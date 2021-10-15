// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use std::{collections::BTreeMap, str::FromStr};
use structopt::StructOpt;

use bytecode::function_target_pipeline::{FunctionVariant, VerificationFlavor};
use move_model::ast::SpecBlockTarget;

mod ast_print;
mod workflow;

// passes on the move model
mod model_pass;
mod model_pass_inlining;
mod model_simplifier;

// passes on the move prover
mod prove_pass;
mod prove_pass_trimming;

use ast_print::SpecPrinter;
use model_pass::ModelPass;
use prove_pass::ProvePass;
use workflow::WorkflowOptions;

/// Options passed into the specification flattening tool.
#[derive(StructOpt, Clone)]
pub struct FlattenOptions {
    /// Options common and shared by the proving workflow and all passes
    #[structopt(flatten)]
    pub workflow: WorkflowOptions,

    /// Model processing pipeline
    #[structopt(short = "m", long = "model-pipeline")]
    pub model_pipeline: Vec<ModelPass>,

    /// Make sure that the model still verifies after each model processing step
    #[structopt(long = "model-step-prove")]
    pub model_step_check: bool,

    /// Dump the model result *in pretty-printing* after each model processing step
    #[structopt(long = "model-step-dump")]
    pub model_step_dump: bool,

    /// Dump the model result *in raw format* after each model processing step
    #[structopt(long = "model-step-dump-raw", requires = "model-step-dump")]
    pub model_step_dump_raw: bool,

    /// Prove-aided simplification processing pipeline
    #[structopt(short = "p", long = "prove-pipeline")]
    pub prove_pipeline: Vec<ProvePass>,

    /// Make sure that the model still verifies after each prove processing step
    #[structopt(long = "prove-step-check")]
    pub prove_step_check: bool,

    /// Dump the model result *in pretty-printing* after each prove processing step
    #[structopt(long = "prove-step-dump")]
    pub prove_step_dump: bool,

    /// Dump the model result *in raw format* after each prove processing step
    #[structopt(long = "prove-step-dump-raw", requires = "prove-step-dump")]
    pub prove_step_dump_raw: bool,
}

//**************************************************************************************************
// Entrypoint
//**************************************************************************************************

pub fn run(options: &FlattenOptions) -> Result<()> {
    let workflow_options = &options.workflow;
    let (mut env, targets) = workflow::prepare(workflow_options)?;

    // make sure the original verification works
    let proved = workflow::prove(workflow_options, &env, &targets)?;
    if !proved {
        return Err(anyhow!("Original proof is not successful"));
    }

    // flatten spec in target modules
    let mut simplified_specs = BTreeMap::new();
    for (fun_id, variant) in targets.get_funs_and_variants() {
        if !matches!(
            variant,
            FunctionVariant::Verification(VerificationFlavor::Regular)
        ) {
            // only care for functions that have the regular verification variant
            continue;
        }

        let fun_env = env.get_function(fun_id);
        if !fun_env.module_env.is_target() {
            // only run on specs in target module
            continue;
        }
        match &workflow_options.target {
            None => {
                if !fun_env.has_unknown_callers() {
                    // only run on specs for external-facing functions
                    continue;
                }
            }
            Some(target) => {
                if fun_env.get_simple_name_string().as_ref() != target {
                    // only run on matched function name
                    continue;
                }
            }
        }

        // get a copy of the original spec
        let fun_target = targets.get_target(&fun_env, &variant);
        let mut fun_spec = Some(fun_target.get_spec().clone());

        // prepare for stepwise result printing
        let fun_scope = SpecBlockTarget::Function(fun_id.module_id, fun_id.id);
        if options.prove_step_dump || options.model_step_dump {
            println!(
                "================ fun {} ================",
                fun_env.get_full_name_str()
            );
        }

        // pass the spec through the model pipeline
        for (i, pass) in options.model_pipeline.iter().enumerate() {
            let target = fun_target.clone();
            let old_spec = fun_spec.take().unwrap();
            let new_spec = match pass {
                ModelPass::Inline => model_pass_inlining::inline_all_exp_in_spec(target, old_spec),
            }?;

            // dump stepwise results if requested
            if options.model_step_dump {
                let printer = SpecPrinter::new(&env, &fun_scope);

                println!("model step {} - {:?} {{", i, pass);
                for cond in &new_spec.conditions {
                    if options.model_step_dump_raw {
                        println!("\t{:?} {}", cond.kind, cond.exp.display(&env));
                    } else {
                        println!("\t{}", SpecPrinter::convert(printer.print_condition(cond)));
                    }
                }
                println!("}}");
            }

            // override the spec in-place
            let module_data = env
                .module_data
                .iter_mut()
                .find(|m| m.id == fun_id.module_id)
                .ok_or_else(|| {
                    anyhow!(
                        "Unable to find module with id `{}`",
                        fun_id.module_id.to_usize()
                    )
                })?;
            let function_data = module_data
                .function_data
                .get_mut(&fun_id.id)
                .ok_or_else(|| {
                    anyhow!("Unable to find function with id `{:?}`", fun_id.id.symbol())
                })?;
            function_data.spec = new_spec;

            // check the modified spec by testing whether it still verifies (if requested)
            if options.model_step_check {
                let mut spec_override = BTreeMap::new();
                spec_override.insert(fun_id, new_spec.clone());
                let (step_env, step_targets) = workflow::prepare_with_override(
                    workflow_options,
                    &options.model_pipeline,
                    spec_override,
                )?;
                let proved = workflow::prove(workflow_options, &step_env, &step_targets)?;
                if !proved {
                    return Err(anyhow!(
                        "The modified spec for function {} does not verify after prove processing \
                        step {} - {:?}",
                        fun_env.get_full_name_str(),
                        i,
                        pass
                    ));
                }
            }
        }

        // pass the spec through the simplification pipeline
        for (i, pass) in options.prove_pipeline.iter().enumerate() {
            let target = fun_target.clone();
            let old_spec = fun_spec.take().unwrap();
            let new_spec = match pass {
                ProvePass::TrimAbortsIf => prove_pass_trimming::trim_aborts_ifs(
                    workflow_options,
                    &options.model_pipeline,
                    target,
                    old_spec,
                ),
            }?;

            // dump stepwise results if requested
            if options.prove_step_dump {
                println!("prove step {} - {:?} {{", i, pass);
                for cond in &new_spec.conditions {
                    if options.prove_step_dump_raw {
                        println!("\t{:?} {}", cond.kind, cond.exp.display(&env));
                    } else {
                        println!("\t{}", SpecPrinter::convert(printer.print_condition(cond)));
                    }
                }
                println!("}}");
            }

            // check the modified spec by testing whether it still verifies (if requested)
            if options.prove_step_check {
                let mut spec_override = BTreeMap::new();
                spec_override.insert(fun_id, new_spec.clone());
                let (step_env, step_targets) = workflow::prepare_with_override(
                    workflow_options,
                    &options.model_pipeline,
                    spec_override,
                )?;
                let proved = workflow::prove(workflow_options, &step_env, &step_targets)?;
                if !proved {
                    return Err(anyhow!(
                        "The modified spec for function {} does not verify after prove processing \
                        step {} - {:?}",
                        fun_env.get_full_name_str(),
                        i,
                        pass
                    ));
                }
            }

            fun_spec = Some(new_spec);
        }

        simplified_specs.insert(fun_id, fun_spec.unwrap());
    }

    // dump the final result
    for (fun_id, spec) in simplified_specs {
        let fun_env = env.get_function(fun_id);
        let fun_scope = SpecBlockTarget::Function(fun_id.module_id, fun_id.id);
        let printer = SpecPrinter::new(&env, &fun_scope);
        if !spec.conditions.is_empty() {
            println!("fun {}{{", fun_env.get_full_name_str());
            for cond in &spec.conditions {
                println!("\t{}", SpecPrinter::convert(printer.print_condition(cond)));
            }
            println!("}}");
        }
    }

    // everything is OK
    Ok(())
}
