// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::collections::BTreeMap;

use crate::{
    ast::{Condition, ConditionKind, Exp, ExpData, Operation, Spec, TempIndex},
    model::GlobalEnv,
    symbol::Symbol,
};

/// Entrypoint of the inline pass
pub(crate) fn run_pass_inline(env: &mut GlobalEnv) -> Result<()> {
    // convert all function specs
    let mut new_specs = BTreeMap::new();
    for menv in env.get_modules() {
        for fenv in menv.get_functions() {
            let spec = inline_all_exp_in_spec(env, fenv.get_spec().clone())?;
            new_specs.insert(fenv.get_qualified_id(), spec);
        }
    }

    // replace all function specs
    for (fid, spec) in new_specs {
        env.override_function_spec(fid, spec);
    }
    Ok(())
}

/// Construct a new spec by inlining all expressions in the given spec
fn inline_all_exp_in_spec(env: &GlobalEnv, spec: Spec) -> Result<Spec> {
    let inliner = ExpInliner { env };

    let Spec {
        loc,
        conditions,
        properties,
        on_impl,
    } = spec;

    // expressions to be substituted when evaluated in a pre-context
    let mut local_vars_pre = BTreeMap::new();
    // expressions to be substituted when evaluated in a post-context
    let mut local_vars_post = BTreeMap::new();

    let mut new_conditions = vec![];
    for cond in conditions {
        let Condition {
            loc,
            kind,
            properties,
            exp,
            additional_exps,
        } = cond;

        match &kind {
            ConditionKind::LetPre(sym) => {
                let var_exp_pre = inliner.inline_exp(&exp, None, Some(&local_vars_pre));
                local_vars_pre.insert(*sym, var_exp_pre);

                let var_exp_post = inliner.inline_exp(&exp, None, Some(&local_vars_post));
                let var_exp_post = if var_exp_post.is_pure(env) {
                    var_exp_post
                } else {
                    let exp_ty = env.get_node_type(var_exp_post.node_id());
                    let node_id = env.new_node(loc, exp_ty);
                    ExpData::Call(node_id, Operation::Old, vec![var_exp_post]).into_exp()
                };
                local_vars_post.insert(*sym, var_exp_post);
            }
            ConditionKind::LetPost(sym) => {
                let var_exp = inliner.inline_exp(&exp, None, Some(&local_vars_post));
                local_vars_post.insert(*sym, var_exp);
            }
            _ => {
                let local_vars = match kind {
                    ConditionKind::AbortsIf
                    | ConditionKind::AbortsWith
                    | ConditionKind::SucceedsIf
                    | ConditionKind::Requires => Some(&local_vars_pre),
                    ConditionKind::Ensures | ConditionKind::Modifies | ConditionKind::Emits => {
                        Some(&local_vars_post)
                    }
                    _ => None,
                };
                let new_exp = inliner.inline_exp(&exp, None, local_vars);
                let new_additional_exps = additional_exps
                    .into_iter()
                    .map(|e| inliner.inline_exp(&e, None, local_vars))
                    .collect();
                let new_cond = Condition {
                    loc,
                    kind,
                    properties,
                    exp: new_exp,
                    additional_exps: new_additional_exps,
                };
                new_conditions.push(new_cond);
            }
        }
    }

    let new_spec = Spec {
        loc,
        conditions: new_conditions,
        properties,
        on_impl,
    };
    Ok(new_spec)
}

/// A struct that capture the inlining logic
struct ExpInliner<'env> {
    env: &'env GlobalEnv,
}

impl ExpInliner<'_> {
    /// Inline expressions in a bottom-up manner. Expressions to be inlined include:
    /// - function calls
    /// - invoke(lambda)
    /// - block expressions (e.g., `{ let x = ..., x + 1 }`)
    fn inline_exp(
        &self,
        exp: &Exp,
        temp_var_repl: Option<&BTreeMap<TempIndex, Exp>>,
        local_var_repl: Option<&BTreeMap<Symbol, Exp>>,
    ) -> Exp {
        use Operation::*;

        let mut rewriter = |e: Exp| match e.as_ref() {
            ExpData::LocalVar(_, sym) => match local_var_repl {
                None => Err(e),
                Some(var_map) => Ok(var_map.get(sym).unwrap().clone()),
            },
            ExpData::Temporary(_, idx) => match temp_var_repl {
                None => Err(e),
                Some(var_map) => Ok(var_map.get(idx).unwrap().clone()),
            },
            ExpData::Call(node_id, Function(mid, fid, _), args) => {
                let callee_menv = self.env.get_module(*mid);
                let callee_decl = callee_menv.get_spec_fun(*fid);
                debug_assert_eq!(args.len(), callee_decl.params.len());
                if callee_decl.is_native || callee_decl.uninterpreted || callee_decl.body.is_none()
                {
                    Err(e)
                } else {
                    let mut callee_local_vars =
                        local_var_repl.cloned().unwrap_or_else(BTreeMap::new);
                    for (arg_exp, (sym, _)) in args
                        .iter()
                        .map(|e| self.inline_exp(e, temp_var_repl, local_var_repl))
                        .zip(callee_decl.params.iter())
                    {
                        callee_local_vars.insert(*sym, arg_exp);
                    }

                    let callee_targs = self.env.get_node_instantiation(*node_id);
                    let callee_body = ExpData::rewrite_node_id(
                        callee_decl.body.as_ref().unwrap().clone(),
                        &mut |id| ExpData::instantiate_node(self.env, id, &callee_targs),
                    );
                    Ok(self.inline_exp(&callee_body, temp_var_repl, Some(&callee_local_vars)))
                }
            }
            ExpData::Invoke(_, lambda, args) => match lambda.as_ref() {
                ExpData::Lambda(_, locals, body) => {
                    debug_assert_eq!(args.len(), locals.len());
                    let mut lambda_local_vars =
                        local_var_repl.cloned().unwrap_or_else(BTreeMap::new);
                    for (arg_exp, decl) in args
                        .iter()
                        .map(|e| self.inline_exp(e, temp_var_repl, local_var_repl))
                        .zip(locals)
                    {
                        lambda_local_vars.insert(decl.name, arg_exp);
                    }
                    Ok(self.inline_exp(body, temp_var_repl, Some(&lambda_local_vars)))
                }
                _ => Err(e),
            },
            ExpData::Lambda(node_id, locals, body) => {
                let mut lambda_local_vars = local_var_repl.cloned().unwrap_or_else(BTreeMap::new);
                for decl in locals {
                    lambda_local_vars
                        .insert(decl.name, ExpData::LocalVar(decl.id, decl.name).into_exp());
                }

                let new_body = self.inline_exp(body, temp_var_repl, Some(&lambda_local_vars));
                Ok(ExpData::Lambda(*node_id, locals.clone(), new_body).into_exp())
            }
            ExpData::Quant(node_id, kind, ranges, triggers, constraint, body) => {
                let mut new_ranges = vec![];
                let mut quant_local_vars = local_var_repl.cloned().unwrap_or_else(BTreeMap::new);
                for (decl, range) in ranges {
                    debug_assert!(decl.binding.is_none());
                    new_ranges.push((
                        decl.clone(),
                        self.inline_exp(range, temp_var_repl, local_var_repl),
                    ));
                    quant_local_vars
                        .insert(decl.name, ExpData::LocalVar(decl.id, decl.name).into_exp());
                }

                let new_triggers = triggers
                    .iter()
                    .map(|t| {
                        t.iter()
                            .map(|e| self.inline_exp(e, temp_var_repl, Some(&quant_local_vars)))
                            .collect()
                    })
                    .collect();
                let new_constraint = constraint
                    .as_ref()
                    .map(|e| self.inline_exp(e, temp_var_repl, Some(&quant_local_vars)));
                let new_body = self.inline_exp(body, temp_var_repl, Some(&quant_local_vars));

                Ok(ExpData::Quant(
                    *node_id,
                    *kind,
                    new_ranges,
                    new_triggers,
                    new_constraint,
                    new_body,
                )
                .into_exp())
            }
            ExpData::Block(_, var_decls, body) => {
                let mut block_local_vars = local_var_repl.cloned().unwrap_or_else(BTreeMap::new);
                for var_decl in var_decls {
                    let var_exp = self.inline_exp(
                        var_decl.binding.as_ref().unwrap(),
                        temp_var_repl,
                        Some(&block_local_vars),
                    );
                    block_local_vars.insert(var_decl.name, var_exp);
                }
                Ok(self.inline_exp(body, temp_var_repl, Some(&block_local_vars)))
            }
            _ => Err(e),
        };
        ExpData::rewrite(exp.clone(), &mut rewriter)
    }
}
