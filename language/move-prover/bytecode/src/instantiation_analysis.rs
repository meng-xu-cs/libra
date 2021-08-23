// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    usage_analysis,
};

use move_binary_format::file_format::TypeParameterIndex;
use move_model::{
    ast::{ConditionKind, GlobalInvariant},
    model::{FunId, FunctionEnv, GlobalEnv, GlobalId, QualifiedId, QualifiedInstId, StructId},
    pragmas::{
        CONDITION_SUSPENDABLE_PROP, DELEGATE_INVARIANTS_TO_CALLER_PRAGMA,
        DISABLE_INVARIANTS_IN_BODY_PRAGMA,
    },
    ty::{Type, TypeDisplayContext, TypeUnificationAdapter, Variance},
};

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt::{self, Formatter},
};

// A named tuple for holding of the invariant relevance information
pub struct InvariantRelevance {
    /// Global invariants covering memories that are used in this function
    pub uses: BTreeSet<GlobalId>,
    /// Global invariants covering memories that are modified in this function
    pub mods: BTreeSet<GlobalId>,
    /// Global invariants covering memories that are directly used in this function
    pub direct_uses: BTreeSet<GlobalId>,
    /// Global invariants covering memories that are directly modified in this function
    pub direct_mods: BTreeSet<GlobalId>,
}

impl InvariantRelevance {
    fn prune_suspendable(&mut self, env: &GlobalEnv) -> Self {
        fn separate(holder: &mut BTreeSet<GlobalId>, env: &GlobalEnv) -> BTreeSet<GlobalId> {
            let mut split = BTreeSet::new();
            holder.retain(|inv_id| {
                if is_invariant_suspendable(env, *inv_id) {
                    split.insert(*inv_id);
                    false
                } else {
                    true
                }
            });
            split
        }

        let uses = separate(&mut self.uses, env);
        let mods = separate(&mut self.mods, env);
        let direct_uses = separate(&mut self.direct_uses, env);
        let direct_mods = separate(&mut self.direct_mods, env);
        Self {
            uses,
            mods,
            direct_uses,
            direct_mods,
        }
    }

    fn subsume_callee(&mut self, suspended: &InvariantRelevance) {
        assert!(self.uses.is_superset(&suspended.uses));
        assert!(self.mods.is_superset(&suspended.mods));
        self.direct_uses.extend(&suspended.uses);
        self.direct_mods.extend(&suspended.mods);
    }
}

// Analysis info to save for global_invariant_instrumentation phase
pub struct InvariantAnalysisData {
    /// Functions which have invariants checked on return instead of in body
    pub fun_set_with_inv_check_on_exit: BTreeSet<QualifiedId<FunId>>,
    /// Functions which invariants checking is turned-off anywhere in the function
    pub fun_set_with_no_inv_check: BTreeSet<QualifiedId<FunId>>,
    /// A mapping from function to the set of global invariants used and modified, respectively
    pub fun_to_inv_map: BTreeMap<QualifiedId<FunId>, InvariantRelevance>,
}

#[derive(Clone)]
pub struct InstantiationAnalysisData {
    /// Instantiations of this function in order to check type-dependent behaviors
    pub type_dependent_checking: BTreeSet<Vec<Type>>,
    /// A mapping that captures: which I[inst] is applicable in F[inst]
    /// - The key in first map is the instantiation of the function + "phantom" types for
    ///   uninstantiated type params appearing in the invariant.
    /// - The value in the second map is the set of invariant instantiations of the global invariant
    ///   identified by its ID that are applicable to this particular instantiation of the function
    pub invariant_applicability:
        BTreeMap<(Vec<Type>, Vec<Type>), BTreeMap<GlobalId, BTreeSet<Vec<Type>>>>,
}

pub fn get_instantiation_analysis<'env>(
    target: &'env FunctionTarget,
) -> &'env InstantiationAnalysisData {
    target
        .get_annotations()
        .get::<InstantiationAnalysisData>()
        .expect("Invariant violation: target not processed for instantiation analysis")
}

// The function target processor
pub struct InstantiationAnalysisProcessor {}

impl InstantiationAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(InstantiationAnalysisProcessor {})
    }
}

impl FunctionTargetProcessor for InstantiationAnalysisProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv<'_>,
        mut data: FunctionData,
    ) -> FunctionData {
        let target = FunctionTarget::new(func_env, &data);

        // see what instantiations for this function are needed by just looking at the move code
        let type_dependent_checking = Self::analyze_instantiation_by_code(&target);

        // see what instantiations for this function are needed to check properties in the spec
        let invariant_applicability = Self::analyze_instantiation_by_spec(&target);

        // save the analysis result to the env
        let result = InstantiationAnalysisData {
            type_dependent_checking,
            invariant_applicability,
        };
        data.annotations.set(result);
        data
    }

    fn name(&self) -> String {
        "instantiation_analysis".to_string()
    }

    fn dump_result(
        &self,
        f: &mut Formatter<'_>,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> fmt::Result {
        writeln!(
            f,
            "\n\n********* Result of instantiation analysis *********\n\n"
        )?;

        let type_display_ctxt = TypeDisplayContext::WithEnv {
            env,
            type_param_names: None,
        };
        let display_type_slice = |tys: &[Type]| -> String {
            let content = tys
                .iter()
                .map(|t| t.display(&type_display_ctxt).to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("<{}>", content)
        };
        let make_indent = |indent: usize| "  ".repeat(indent);

        for (fun_id, fun_variant) in targets.get_funs_and_variants() {
            let fenv = env.get_function(fun_id);
            let target = targets.get_target(&fenv, &fun_variant);
            let result = get_instantiation_analysis(&target);
            writeln!(
                f,
                "function {} [{}] {{",
                fenv.get_full_name_str(),
                target.data.variant
            )?;
            let mut indent = 1;

            writeln!(f, "{}type dependent checking: [", make_indent(indent))?;
            indent += 1;
            for inst in &result.type_dependent_checking {
                writeln!(f, "{}{}", make_indent(indent), display_type_slice(inst))?;
            }
            indent -= 1;
            writeln!(f, "{}]", make_indent(indent))?;

            writeln!(f, "{}invariant applicability: [", make_indent(indent))?;
            indent += 1;
            for ((fun_inst, phantoms), applicability) in &result.invariant_applicability {
                writeln!(
                    f,
                    "{}{} + {} [",
                    make_indent(indent),
                    display_type_slice(fun_inst),
                    display_type_slice(phantoms)
                )?;
                indent += 1;
                for (inv_id, inv_insts) in applicability {
                    writeln!(f, "{}{} => [", make_indent(indent), inv_id)?;
                    indent += 1;
                    for inv_inst in inv_insts {
                        writeln!(f, "{}{}", make_indent(indent), display_type_slice(inv_inst))?;
                    }
                    indent -= 1;
                    writeln!(f, "{}]", make_indent(indent))?;
                }
                indent -= 1;
                writeln!(f, "{}]", make_indent(indent))?;
            }
            indent -= 1;
            writeln!(f, "{}]", make_indent(indent))?;

            writeln!(f, "}}",)?;
        }
        writeln!(f)
    }

    fn initialize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        // probe how global invariants will be evaluated in the functions
        let (fun_set_with_inv_check_on_exit, fun_set_with_no_inv_check) =
            Self::probe_invariant_status_in_functions(env);

        // get a map on how invariants are consumed in functions
        let fun_to_inv_map = Self::build_function_to_invariants_map(env, targets);

        // error checking
        for fun_id in &fun_set_with_no_inv_check {
            let fun_env = env.get_function(*fun_id);
            let mut has_error = false;

            // Rule 1: external-facing functions are not allowed in the N set,
            // UNLESS they don't modify any memory that are checked in any suspendable invariant.
            if fun_env.has_unknown_callers() {
                let relevance = fun_to_inv_map.get(fun_id).unwrap();
                let num_suspendable_inv_modified = relevance
                    .mods
                    .iter()
                    .filter(|inv_id| is_invariant_suspendable(env, **inv_id))
                    .count();
                if num_suspendable_inv_modified != 0 {
                    env.error(
                        &fun_env.get_loc(),
                        "Public or script functions must not be called when invariant checking \
                        is turned-off on this function.",
                    );
                    has_error = true;
                }
            }

            // Rule 2: a function cannot be both on the E set and N set.
            // This is because invariants must hold on entry to any function in the E set, so such
            // a function must not be called from a function in E or N.
            if fun_set_with_inv_check_on_exit.contains(fun_id) {
                env.error(
                    &fun_env.get_loc(),
                    &format!(
                        "Functions must not have `pragma {}` when invariant checking is turned-off \
                        on this function.",
                        DISABLE_INVARIANTS_IN_BODY_PRAGMA
                    ),
                );
                has_error = true;
            }

            if has_error {
                // TODO: port the tracing logic (i.e., why the invariant checking is turned off)
                env.error(
                    &fun_env.get_loc(),
                    &format!(
                        "Invariant checking is turned-off on this function because either \
                        1) a transitive caller of this function has `pragma {}` or \
                        2) `pragma {}` is applied on this function",
                        DISABLE_INVARIANTS_IN_BODY_PRAGMA, DELEGATE_INVARIANTS_TO_CALLER_PRAGMA
                    ),
                );
            }
        }

        // prune the function-to-invariants map with the pragma-magic
        let fun_to_inv_map =
            Self::prune_function_to_invariants_map(env, fun_to_inv_map, &fun_set_with_no_inv_check);

        // save the analysis results in the env
        let result = InvariantAnalysisData {
            fun_set_with_inv_check_on_exit,
            fun_set_with_no_inv_check,
            fun_to_inv_map,
        };
        env.set_extension(result);
    }
}

// This implementation block contains functions on global invariant applicability analysis
impl InstantiationAnalysisProcessor {
    // Build the E set and N set
    //
    // E set: f in E if declared pragma disable_invariant_in_body for f
    // N set: f in N if f is called from a function in E or N
    //        can also put f in N by pragma delegate_invariant_to_caller
    //
    // E set means: a suspendable invariant holds before, after, but NOT during the function body
    // N set means: a suspendable invariant don’t hold at any point in the function
    fn probe_invariant_status_in_functions(
        env: &GlobalEnv,
    ) -> (BTreeSet<QualifiedId<FunId>>, BTreeSet<QualifiedId<FunId>>) {
        let mut disabled_inv_fun_set = BTreeSet::new(); // the E set
        let mut non_inv_fun_set = BTreeSet::new(); // the N set

        // Invariant: if a function is in non_inv_fun_set and not in worklist, then all the
        // functions it calls are also in non_inv_fun_set or in worklist. As a result, when the
        // worklist is empty, all callees of a function in non_inv_fun_set will also be in
        // non_inv_fun_set. Each function is added at most once to the worklist.
        let mut worklist = vec![];
        for module_env in env.get_modules() {
            for fun_env in module_env.get_functions() {
                if is_invariant_checking_disabled(&fun_env) {
                    let fun_id = fun_env.get_qualified_id();
                    disabled_inv_fun_set.insert(fun_id);
                    worklist.push(fun_id);
                }
                if is_invariant_checking_delegated(&fun_env) {
                    let fun_id = fun_env.get_qualified_id();
                    if non_inv_fun_set.insert(fun_id) {
                        // Add to work_list only if fun_id is not in non_inv_fun_set (may have
                        // inferred this from a caller already).
                        worklist.push(fun_id);
                    }
                }
                // Downward closure of non_inv_fun_set
                while let Some(called_fun_id) = worklist.pop() {
                    let called_funs = env.get_function(called_fun_id).get_called_functions();
                    for called_fun_id in called_funs {
                        if non_inv_fun_set.insert(called_fun_id) {
                            // Add to work_list only if fun_id is not in fun_set
                            worklist.push(called_fun_id);
                        }
                    }
                }
            }
        }
        (disabled_inv_fun_set, non_inv_fun_set)
    }

    // Produce a Map[fun_id -> (Set<global_id>, Set<global_id>)] ignoring the relevant pragmas on
    // both function-side (i.e., `disable_invariants_in_body` and `delegate_invariants_to_caller`)
    // and invariant-side (i.e., `suspendable`)
    //
    // The first set contains global invariants that overlaps with the read-write set of the memory,
    // the second set contains global invariants that overlaps with the modified memory set only.
    fn build_function_to_invariants_map(
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> BTreeMap<QualifiedId<FunId>, InvariantRelevance> {
        // collect all global invariants
        let mut global_invariants = vec![];
        for menv in env.get_modules() {
            for inv_id in env.get_global_invariants_by_module(menv.get_id()) {
                global_invariants.push(env.get_global_invariant(inv_id).unwrap());
            }
        }

        // go over each function target and check global invariant applicability
        let mut invariant_relevance = BTreeMap::new();
        for (fun_id, fun_variant) in targets.get_funs_and_variants() {
            assert!(matches!(fun_variant, FunctionVariant::Baseline));
            let fenv = env.get_function(fun_id);
            let target = targets.get_target(&fenv, &fun_variant);
            let related =
                Self::find_relevant_invariants(&target, global_invariants.clone().into_iter());
            invariant_relevance.insert(fun_id, related);
        }

        // return the collected relevance map
        invariant_relevance
    }

    fn find_relevant_invariants<'a>(
        target: &FunctionTarget,
        invariants: impl Iterator<Item = &'a GlobalInvariant>,
    ) -> InvariantRelevance {
        let mem_uses = usage_analysis::get_used_memory_inst(target);
        let mem_mods = usage_analysis::get_modified_memory_inst(target);
        let mem_direct_uses = usage_analysis::get_directly_used_memory_inst(target);
        let mem_direct_mods = usage_analysis::get_directly_modified_memory_inst(target);

        let mut related_rw = BTreeSet::new();
        let mut related_wo = BTreeSet::new();
        let mut related_direct_rw = BTreeSet::new();
        let mut related_direct_wo = BTreeSet::new();
        for inv in invariants {
            for fun_mem in mem_uses.iter() {
                for inv_mem in &inv.mem_usage {
                    if inv_mem.module_id != fun_mem.module_id || inv_mem.id != fun_mem.id {
                        continue;
                    }
                    let adapter =
                        TypeUnificationAdapter::new_vec(&fun_mem.inst, &inv_mem.inst, true, true);
                    let rel = adapter.unify(Variance::Allow, /* shallow_subst */ false);
                    if rel.is_some() {
                        related_rw.insert(inv.id);
                        // this exploits the fact that the `used_memory` set (a read-write set) is
                        // always a superset of the `modified_memory` set.
                        if mem_mods.contains(fun_mem) {
                            related_wo.insert(inv.id);
                        }
                        if mem_direct_uses.contains(fun_mem) {
                            related_direct_rw.insert(inv.id);
                        }
                        if mem_direct_mods.contains(fun_mem) {
                            related_direct_wo.insert(inv.id);
                        }
                    }
                }
            }
        }
        InvariantRelevance {
            uses: related_rw,
            mods: related_wo,
            direct_uses: related_direct_rw,
            direct_mods: related_direct_wo,
        }
    }

    // Prune the Map[fun_id -> (Set<global_id>, Set<global_id>)] returned with
    // `build_function_to_invariants_map` with invariant-checking related pragmas.
    fn prune_function_to_invariants_map(
        env: &GlobalEnv,
        original: BTreeMap<QualifiedId<FunId>, InvariantRelevance>,
        fun_set_with_no_inv_check: &BTreeSet<QualifiedId<FunId>>,
    ) -> BTreeMap<QualifiedId<FunId>, InvariantRelevance> {
        // NOTE: All fields in `InvariantRelevance` are derived based on unification of memory
        // usage/modification of the function and the invariant. In `MemoryUsageAnalysis`, both used
        // memory and modified memory subsumes the set summarized in the called functions.
        //
        // If the called function is NOT a generic function, this means that all the invariants that
        // are applicable to the called function will be applicable to its caller function as well.
        //
        // If the called function IS a generic function, this means that all the invariants that are
        // applicable to this specific instantiation of the called function (which can be another
        // type parameter, i.e., a type parameter from the caller function) will be applicable to
        // this caller function as well.
        //
        // This means that if we disable a suspendable invariant `I` in the called function, for all
        // the callers of this called function, `I` is either
        // - already marked as relevant to the caller (in the `uses/mods` set), or
        // - `I` is not relevant to the caller and we should not insert `I` to the caller.

        // Step 1: remove suspended invariants from the the relevance set. These suspended
        // invariants themselves forms a relevance set which will be directly used/modified in all
        // callers of this function.
        let mut pruned = BTreeMap::new();
        let mut deferred = BTreeMap::new();
        for (fun_id, mut relevance) in original.into_iter() {
            if fun_set_with_no_inv_check.contains(&fun_id) {
                let suspended = relevance.prune_suspendable(env);
                deferred.insert(fun_id, suspended);
            }
            pruned.insert(fun_id, relevance);
        }

        // Step 2: defer the suspended invariants back to the caller, marking them in the directly
        // used/modified sets.
        let mut result = BTreeMap::new();
        for (fun_id, mut relevance) in pruned.into_iter() {
            if !fun_set_with_no_inv_check.contains(&fun_id) {
                let fenv = env.get_function(fun_id);
                for callee in fenv.get_called_functions() {
                    if fun_set_with_no_inv_check.contains(&callee) {
                        // all invariants in the callee side will now be deferred to this function
                        let suspended = deferred.get(&callee).unwrap();
                        relevance.subsume_callee(suspended);
                    }
                }
            }
            result.insert(fun_id, relevance);
        }
        result
    }
}

// This implementation block contains functions on type instantiation collection
impl InstantiationAnalysisProcessor {
    // Find what the instantiations should we have for the target_param_index.
    //
    // the invariant is, forall type parameters whose index < target_param_index, it should either
    // - be assigned with a concrete type and hence, ceases to be a type parameter, or
    // - do not have any matching instantiation and hence, remains a type parameter.
    fn find_instantiations_for_target(
        mem_usage_lhs: &BTreeSet<QualifiedInstId<StructId>>,
        mem_usage_rhs: &BTreeSet<QualifiedInstId<StructId>>,
        treat_lhs_type_param_as_var: bool,
        treat_rhs_type_param_as_var: bool,
        target_param_index: TypeParameterIndex,
        params_on_lhs: bool,
    ) -> BTreeSet<Type> {
        // progressively increase the boundary
        let treat_lhs_type_param_as_var_after_index = if treat_lhs_type_param_as_var {
            Some(target_param_index)
        } else {
            None
        };
        let treat_rhs_type_param_as_var_after_index = if treat_rhs_type_param_as_var {
            Some(target_param_index)
        } else {
            None
        };

        let mut target_param_insts = BTreeSet::new();
        for m1 in mem_usage_lhs.iter() {
            for m2 in mem_usage_rhs.iter() {
                if (m1.module_id != m2.module_id) || (m1.id != m2.id) {
                    continue;
                }

                // Try to unify the instantiations
                let adapter = TypeUnificationAdapter::new_vec_with_boundary(
                    &m1.inst,
                    &m2.inst,
                    treat_lhs_type_param_as_var_after_index,
                    treat_rhs_type_param_as_var_after_index,
                );
                let rel = adapter.unify(Variance::Allow, false);
                if let Some((subst_lhs, subst_rhs)) = rel {
                    let subst = if params_on_lhs { subst_lhs } else { subst_rhs };
                    for (param_idx, inst_ty) in subst.into_iter() {
                        if param_idx != target_param_index {
                            // this parameter will be unified at a later stage.
                            //
                            // NOTE: this code is inefficient when we have multiple type parameters,
                            // but a vast majority of Move code we see so far have at most one type
                            // parameter, so we trade-off efficiency with simplicity in code.
                            assert!(param_idx > target_param_index);
                            continue;
                        }
                        target_param_insts.insert(inst_ty);
                    }
                }
            }
        }
        target_param_insts
    }

    // Find the instantiation combinations for all the type parameters.
    fn progressive_instantiation(
        mem_usage_lhs: &BTreeSet<QualifiedInstId<StructId>>,
        mem_usage_rhs: &BTreeSet<QualifiedInstId<StructId>>,
        treat_lhs_type_param_as_var: bool,
        treat_rhs_type_param_as_var: bool,
        refine_lhs: bool,
        refine_rhs: bool,
        params_arity: usize,
        params_on_lhs: bool,
        mark_irrelevant_param_as_error: bool,
    ) -> BTreeSet<Vec<Type>> {
        let initial_param_insts: Vec<_> = (0..params_arity)
            .map(|idx| Type::TypeParameter(idx as TypeParameterIndex))
            .collect();

        let mut work_queue = VecDeque::new();
        work_queue.push_back(initial_param_insts);
        for target_param_index in 0..params_arity {
            let mut for_next_round = vec![];
            while let Some(param_insts) = work_queue.pop_front() {
                // adapt the memory usage sets with current param instantiations
                let adapted_mem_usage_lhs = mem_usage_lhs
                    .iter()
                    .map(|mem| {
                        if refine_lhs {
                            mem.instantiate_ref(&param_insts)
                        } else {
                            mem.clone()
                        }
                    })
                    .collect();
                let adapted_mem_usage_rhs = mem_usage_rhs
                    .iter()
                    .map(|mem| {
                        if refine_rhs {
                            mem.instantiate_ref(&param_insts)
                        } else {
                            mem.clone()
                        }
                    })
                    .collect();

                // find type instantiations for the target parameter index
                let mut target_param_insts = Self::find_instantiations_for_target(
                    &adapted_mem_usage_lhs,
                    &adapted_mem_usage_rhs,
                    treat_lhs_type_param_as_var,
                    treat_rhs_type_param_as_var,
                    target_param_index as TypeParameterIndex,
                    params_on_lhs,
                );

                // decide what to do with an irrelevant type parameter
                if target_param_insts.is_empty() {
                    let irrelevant_type = if mark_irrelevant_param_as_error {
                        Type::Error
                    } else {
                        Type::TypeParameter(target_param_index as TypeParameterIndex)
                    };
                    target_param_insts.insert(irrelevant_type);
                }

                // instantiate the target type parameter in every possible way
                for inst in target_param_insts {
                    let mut next_insts = param_insts.clone();
                    next_insts[target_param_index] = inst;
                    for_next_round.push(next_insts);
                }
            }
            work_queue.extend(for_next_round);
        }

        // the final workqueue contains possible instantiations for all type parameters
        work_queue.into_iter().collect()
    }

    /// Analyze the bytecode (excluding the specs) to see what instantiations are needed for the
    /// function type parameters. This is needed because Move allows type-dependent behaviors, i.e.,
    /// move_to<R<T>>(..); move_to<R<u64>>(..); leads to a sure abort if T := u64, but the program
    /// might not necessarily abort if T is not instantiated with u64.
    fn analyze_instantiation_by_code(target: &FunctionTarget) -> BTreeSet<Vec<Type>> {
        let mem_usage = usage_analysis::get_used_memory_inst(target)
            .iter()
            .cloned()
            .collect();

        // NOTE: we only treat the type parameters in one side (RHS is arbitrarily chosen here)
        // because we don't want to unify a pair like (S<X, bool>, S<u64, X>). They shouldn't, as
        // there is no assignment X that allows the type pair to unify.
        //
        // But this comes at the cost that we might unify (S<X, Y>, S<X, bool>) with a result
        // [X := X, Y := bool]. We need to additional filter X := X because this just means that the
        // type variable assigns to itself.
        //
        // And we should be able to unify amongst the parameters themselves as well. For example,
        // we can and should unify S<X, Y> with S<Y, X> into [X := Y, Y := X].
        Self::progressive_instantiation(
            &mem_usage,
            &mem_usage,
            false,
            true,
            true,
            true,
            target.get_type_parameters().len(),
            false,
            false,
        )
    }

    /// Analyze the spec to see what instantiations are needed for the function type parameters.
    /// At the same time, this function also derives which invariant needs to be instrumented
    /// on which instantiation of the function, and if an invariant needs to be instrumented, what
    /// are the instantiations of that invariant. So the return result is a
    /// Map[fun_inst -> Map[invariant_id -> Set[invariant_inst]]]
    fn analyze_instantiation_by_spec(
        target: &FunctionTarget,
    ) -> BTreeMap<(Vec<Type>, Vec<Type>), BTreeMap<GlobalId, BTreeSet<Vec<Type>>>> {
        let mut invariant_applicability = BTreeMap::new();

        let env = target.global_env();
        let fun_mem_usage = usage_analysis::get_used_memory_inst(target)
            .iter()
            .cloned()
            .collect();
        let fun_type_params_arity = target.get_type_parameters().len();

        // retrieve relevant global invariants
        let inv_analysis = env.get_extension::<InvariantAnalysisData>().unwrap();
        let relevance = inv_analysis
            .fun_to_inv_map
            .get(&target.func_env.get_qualified_id())
            .unwrap();

        // we only use the `direct_uses` set because this represents the maximum set of invariants
        // that will ever be applicable to this funciton: i.e., we should not assume/assert any
        // invariant outside of this `direct_uses` set in any instantiation of this function.
        for inv_id in &relevance.direct_uses {
            let invariant = env.get_global_invariant(*inv_id).unwrap();
            let inv_type_params = match &invariant.kind {
                ConditionKind::GlobalInvariant(params) => params,
                ConditionKind::GlobalInvariantUpdate(params) => params,
                _ => unreachable!(
                    "A global invariant must have a condition kind of either \
                    `GlobalInvariant` or `GlobalInvariantUpdate`"
                ),
            };

            // find out which instantiations are needed for the function type parameter
            let fun_insts = Self::progressive_instantiation(
                &fun_mem_usage,
                &invariant.mem_usage,
                true,
                true,
                true,
                false,
                fun_type_params_arity,
                true,
                false,
            );

            // per-each instantiation of the function, what are the instantiations of the global
            // invariant in order to make it relevant
            let inv_type_params_arity = inv_type_params.len();
            for fun_param_insts in &fun_insts {
                let inst_fun_mem_usage: BTreeSet<_> = fun_mem_usage
                    .iter()
                    .map(|mem| mem.instantiate_ref(fun_param_insts))
                    .collect();

                // check whether this invariant is still relevant to this particular instantiation
                // of the function
                let mut is_relevant = false;
                for fun_mem in &inst_fun_mem_usage {
                    for inv_mem in &invariant.mem_usage {
                        if inv_mem.module_id != fun_mem.module_id || inv_mem.id != fun_mem.id {
                            continue;
                        }
                        let adapter = TypeUnificationAdapter::new_vec(
                            &fun_mem.inst,
                            &inv_mem.inst,
                            false,
                            true,
                        );
                        let rel = adapter.unify(Variance::Allow, /* shallow_subst */ false);
                        if rel.is_some() {
                            is_relevant = true;
                        }
                    }
                }
                if !is_relevant {
                    // this invariant is no longer applicable to this function instantiation
                    continue;
                }

                // derive the instantiations of the invariant
                let inv_insts = Self::progressive_instantiation(
                    &inst_fun_mem_usage,
                    &invariant.mem_usage,
                    false,
                    true,
                    false,
                    true,
                    inv_type_params_arity,
                    false,
                    true,
                );

                // TODO: if not all type parameters in an invariant can be instantiated, e.g., the
                // invariant talks about some generic memory that is never touched by this function,
                // shall we include the invariant?
                //
                // For a concrete example: we have a function that reads `global<RoleId>` and an
                // invariant I<T>: exists<S<T>>(addr) ==> global<RoleId>(addr).role_id == @DiemRoot;
                // This T in the invariant will not be instantiated to anything. In this case, it
                // might be OK to simply ignore this invariant.
                //
                // But consider the following case: a function modifies `global<RoleId>` and an
                // invariant I<T>: (global<RoleId>(addr).role_id == @DiemRoot) ==>
                //   (exists<S<T>>(addr) ==> global<S<T>>(addr).owner == @Blessed);
                // In this case, is it OK to ignore this invariant?
                //
                // The tentative policy we have for now is to mark an uninstantiated type parameter
                // as a `Type::Error` in the unification process and expand the type parameter list
                // of the function to include the new type parameters in the invariant. These new
                // type parameters behave like "phantom" types: they don't have an effect in the
                // function implementation, but they are needed for spec checking.
                for inv_param_inst in inv_insts {
                    let mut fun_phantom_params = vec![];
                    let adapted_inv_param_inst = inv_param_inst
                        .into_iter()
                        .map(|t| {
                            if matches!(t, Type::Error) {
                                let idx = (fun_type_params_arity + fun_phantom_params.len())
                                    as TypeParameterIndex;
                                let phantom_param = Type::TypeParameter(idx);
                                fun_phantom_params.push(phantom_param.clone());
                                phantom_param
                            } else {
                                t
                            }
                        })
                        .collect();

                    let inserted = invariant_applicability
                        .entry((fun_param_insts.clone(), fun_phantom_params))
                        .or_insert_with(BTreeMap::new)
                        .entry(invariant.id)
                        .or_insert_with(BTreeSet::new)
                        .insert(adapted_inv_param_inst);
                    debug_assert!(inserted);
                }
            }
        }

        invariant_applicability
    }
}

// Utility functions
fn is_invariant_checking_disabled(fun_env: &FunctionEnv) -> bool {
    fun_env.is_pragma_true(DISABLE_INVARIANTS_IN_BODY_PRAGMA, || false)
}

fn is_invariant_checking_delegated(fun_env: &FunctionEnv) -> bool {
    fun_env.is_pragma_true(DELEGATE_INVARIANTS_TO_CALLER_PRAGMA, || false)
}

fn is_invariant_suspendable(env: &GlobalEnv, inv_id: GlobalId) -> bool {
    let inv = env.get_global_invariant(inv_id).unwrap();
    env.is_property_true(&inv.properties, CONDITION_SUSPENDABLE_PROP)
        .unwrap_or(false)
}
