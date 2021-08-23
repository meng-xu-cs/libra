// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

// Transformation which injects global invariants into the bytecode.

use crate::{
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{
        FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant, VerificationFlavor,
    },
    instantiation_analysis::{self, InvariantAnalysisData},
    options::ProverOptions,
    stackless_bytecode::{BorrowNode, Bytecode, Operation, PropKind},
    usage_analysis,
};

use move_model::{
    ast::{ConditionKind, Exp, MemoryLabel},
    exp_generator::ExpGenerator,
    model::{
        FunId, FunctionEnv, GlobalEnv, GlobalId, Loc, QualifiedId, QualifiedInstId, SpecVarId,
        StructId,
    },
    pragmas::CONDITION_ISOLATED_PROP,
    spec_translator::{SpecTranslator, TranslatedSpec},
    ty::Type,
};

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

const GLOBAL_INVARIANT_FAILS_MESSAGE: &str = "global memory invariant does not hold";

// The function target processor
pub struct GlobalInvariantInstrumentationProcessor {}

impl GlobalInvariantInstrumentationProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self {})
    }
}

impl FunctionTargetProcessor for GlobalInvariantInstrumentationProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv<'_>,
        data: FunctionData,
    ) -> FunctionData {
        if fun_env.is_native() || fun_env.is_intrinsic() {
            // Nothing to do.
            return data;
        }
        if !data.variant.is_verified() {
            // Only need to instrument if this is a verification variant
            return data;
        }

        // Retrieve instantiation analysis results
        let target = FunctionTarget::new(fun_env, &data);
        let instantiations = instantiation_analysis::get_instantiation_analysis(&target);

        // Create variants for possible function instantiations
        let env = target.global_env();

        let mut main_context = None;
        let mut variants = vec![];
        for ((fun_inst, fun_phantom), invariants) in &instantiations.invariant_applicability {
            let context = InstrumentationContext::new(fun_env, targets, invariants);

            let is_original = fun_phantom.is_empty()
                && fun_inst
                    .iter()
                    .enumerate()
                    .all(|(i, ty)| matches!(ty, Type::TypeParameter(idx) if *idx as usize == i));
            if is_original {
                main_context = Some(context);
            } else {
                let variant_data = data.fork_with_instantiation(
                    env,
                    fun_inst,
                    fun_phantom,
                    FunctionVariant::Verification(VerificationFlavor::Instantiated(variants.len())),
                );
                variants.push((variant_data, context));
            }
        }

        // Instrument the main variant. It is possible that the `main_context` is None, this means
        // that there are no invariants applicable to this function.
        let main = match main_context {
            None => data,
            Some(context) => Self::instrument(fun_env, data, &context),
        };

        // Instrument the variants representing different instantiations
        for (variant_data, variant_context) in variants {
            let variant_instrumented = Self::instrument(fun_env, variant_data, &variant_context);
            targets.insert_target_data(
                &fun_env.get_qualified_id(),
                variant_instrumented.variant.clone(),
                variant_instrumented,
            );
        }

        // Return the main variant
        main
    }

    fn name(&self) -> String {
        "global_invariant_instrumenter".to_string()
    }
}

// An context helper struct holding immutable information for the instrumenter
struct InstrumentationContext {
    // used for invariants applicability
    entrypoint_invariants: BTreeMap<GlobalId, BTreeSet<Vec<Type>>>,
    related_global_invs_by_mem:
        BTreeMap<QualifiedInstId<StructId>, BTreeMap<GlobalId, BTreeSet<Vec<Type>>>>,
    related_update_invs_by_mem:
        BTreeMap<QualifiedInstId<StructId>, BTreeMap<GlobalId, BTreeSet<Vec<Type>>>>,

    // used for invariants suspension
    function_status: Rc<InvariantAnalysisData>,
    modified_mems_by_callee: BTreeMap<QualifiedId<FunId>, BTreeSet<QualifiedInstId<StructId>>>,
}

impl InstrumentationContext {
    fn new(
        fun_env: &FunctionEnv,
        targets: &FunctionTargetsHolder,
        related_invariants: &BTreeMap<GlobalId, BTreeSet<Vec<Type>>>,
    ) -> Self {
        let env = fun_env.module_env.env;

        // collect entrypoint invariants by filtering out "update" invariants. These invariants
        // will be assumed at the entry of the function.
        let entrypoint_invariants = related_invariants
            .iter()
            .filter_map(|(id, insts)| {
                let inv = env.get_global_invariant(*id).unwrap();
                if matches!(inv.kind, ConditionKind::GlobalInvariant(..)) {
                    Some((*id, insts.clone()))
                } else {
                    None
                }
            })
            .collect();

        // derive a per-mem view of applicable invariants.
        // - for regular invariants,
        //   - they will be checked after the modifying instruction
        // - for update invariants,
        //   - a state snapshot will be saved before the modifying instruction
        //   - the invariant itself will be checked after the modifying instruction
        let mut related_global_invs_by_mem = BTreeMap::new();
        let mut related_update_invs_by_mem = BTreeMap::new();
        for (inv_id, inv_insts) in related_invariants {
            for inv_inst in inv_insts {
                let inv = env.get_global_invariant(*inv_id).unwrap();
                for mem in inv.mem_usage.iter() {
                    let mem_inst = mem.instantiate_ref(inv_inst);
                    let mem_view = match inv.kind {
                        ConditionKind::GlobalInvariant(..) => &mut related_global_invs_by_mem,
                        ConditionKind::GlobalInvariantUpdate(..) => &mut related_update_invs_by_mem,
                        _ => unreachable!(
                            "Unexpected condition type for a global invariant: {}",
                            inv.kind
                        ),
                    };
                    mem_view
                        .entry(mem_inst)
                        .or_insert_with(BTreeMap::new)
                        .entry(*inv_id)
                        .or_insert_with(BTreeSet::new)
                        .insert(inv_inst.clone());
                }
            }
        }

        // retrieve the function status analysis
        // - whether a function evaluates invariant, and
        // - whether an invariant should be evaluated at the return of this function
        let function_status = env.get_extension::<InvariantAnalysisData>().unwrap();

        // pre-collect targets for the called functions
        let modified_mems_by_callee = fun_env
            .get_called_functions()
            .iter()
            .map(|callee_id| {
                let callee_env = env.get_function(*callee_id);
                let callee_target = targets.get_target(&callee_env, &FunctionVariant::Baseline);
                let callee_modified_mems: BTreeSet<_> =
                    usage_analysis::get_modified_memory_inst(&callee_target)
                        .iter()
                        .cloned()
                        .collect();
                (*callee_id, callee_modified_mems)
            })
            .collect();

        // now construct the context
        InstrumentationContext {
            entrypoint_invariants,
            related_global_invs_by_mem,
            related_update_invs_by_mem,
            modified_mems_by_callee,
            function_status,
        }
    }
}

impl GlobalInvariantInstrumentationProcessor {
    // The instrumentation process
    fn instrument(
        fun_env: &FunctionEnv,
        data: FunctionData,
        context: &InstrumentationContext,
    ) -> FunctionData {
        let mut builder = FunctionDataBuilder::new(fun_env, data);

        // Extract and clear current code
        let old_code = std::mem::take(&mut builder.data.code);

        // Emit entrypoint assumptions, i.e., an assume of each invariant over memory directly
        // touched by this function, regardless of where the invariant is defined, as long as the
        // invariant is in the `context.entrypoint_invariants` set.
        let xlated = Self::translate_invariants(&mut builder, &context.entrypoint_invariants);
        Self::assert_or_assume_translated_invariants(
            &mut builder,
            xlated.invariants,
            PropKind::Assume,
        );

        // Generate new instrumented code.
        let mems_modified_in_body = Self::process_bytecode(&mut builder, context, old_code);
        if !mems_modified_in_body.is_empty() {
            // re-instrument the bytecode because this function disables invariant checking in body
            let old_code = std::mem::take(&mut builder.data.code);

            // pre-instrumentation
            let xlated_update_invs = Self::emit_save_mem_for_update_invs(
                &mut builder,
                context,
                mems_modified_in_body.iter(),
            );

            for bc in old_code {
                if let Bytecode::Ret(..) = &bc {
                    // post-instrumentation
                    Self::emit_assert_for_update_and_global_invs(
                        &mut builder,
                        context,
                        xlated_update_invs.clone(),
                        mems_modified_in_body.iter(),
                    );
                }
                builder.emit(bc);
            }
        }

        // Extract the instrumented code
        builder.data
    }

    fn process_bytecode(
        builder: &mut FunctionDataBuilder,
        context: &InstrumentationContext,
        code: Vec<Bytecode>,
    ) -> BTreeSet<QualifiedInstId<StructId>> {
        use BorrowNode::*;
        use Bytecode::*;
        use Operation::*;

        let assert_invariants_at_return = context
            .function_status
            .fun_set_with_inv_check_on_exit
            .contains(&builder.fun_env.get_qualified_id());

        let mut mems_modified_in_body = BTreeSet::new();
        let mut last_opaque_call_info = None;

        for bc in code {
            match &bc {
                Call(_, _, WriteBack(GlobalRoot(mem), ..), ..) => {
                    let modified_mems = vec![mem.clone()];
                    if assert_invariants_at_return {
                        // skip instrumentation if invariant checking is disabled in body
                        mems_modified_in_body.extend(modified_mems);
                        builder.emit(bc);
                    } else {
                        // pre-instrumentation
                        let xlated_update_invs = Self::emit_save_mem_for_update_invs(
                            builder,
                            context,
                            modified_mems.iter(),
                        );

                        builder.emit(bc);

                        // post-instrumentation
                        Self::emit_assert_for_update_and_global_invs(
                            builder,
                            context,
                            xlated_update_invs,
                            modified_mems.iter(),
                        );
                    }
                }
                Call(_, _, MoveTo(mid, sid, inst), ..)
                | Call(_, _, MoveFrom(mid, sid, inst), ..) => {
                    let modified_mems = vec![mid.qualified_inst(*sid, inst.to_owned())];
                    if assert_invariants_at_return {
                        // skip instrumentation if invariant checking is disabled in body
                        mems_modified_in_body.extend(modified_mems);
                        builder.emit(bc);
                    } else {
                        // pre-instrumentation
                        let xlated_update_invs = Self::emit_save_mem_for_update_invs(
                            builder,
                            context,
                            modified_mems.iter(),
                        );

                        builder.emit(bc);

                        // post-instrumentation
                        Self::emit_assert_for_update_and_global_invs(
                            builder,
                            context,
                            xlated_update_invs,
                            modified_mems.iter(),
                        );
                    }
                }
                Call(_, _, OpaqueCallBegin(mid, fid, callee_inst), ..) => {
                    let callee_id = mid.qualified(*fid);

                    // pre-instrument the opaque call if it is in the N set
                    if context
                        .function_status
                        .fun_set_with_no_inv_check
                        .contains(&callee_id)
                    {
                        let callee_modified_mems: BTreeSet<_> = context
                            .modified_mems_by_callee
                            .get(&callee_id)
                            .unwrap()
                            .iter()
                            .map(|mem| mem.instantiate_ref(callee_inst))
                            .collect();

                        if assert_invariants_at_return {
                            // skip instrumentation if invariant checking is disabled in body
                            mems_modified_in_body.extend(callee_modified_mems);
                        } else {
                            // pre-instrumentation of the opaque call
                            let xlated_update_invs = Self::emit_save_mem_for_update_invs(
                                builder,
                                context,
                                callee_modified_mems.iter(),
                            );
                            debug_assert!(last_opaque_call_info.is_none());
                            last_opaque_call_info
                                .insert((callee_modified_mems, xlated_update_invs));
                        }
                    }

                    // emit the opaque call after instrumentation (if there is any)
                    builder.emit(bc);
                }
                Call(_, _, OpaqueCallEnd(mid, fid, _), ..) => {
                    let callee_id = mid.qualified(*fid);

                    // emit the opaque call, with or without instrumentation
                    builder.emit(bc);

                    // post-instrument the opaque call if it is in the N set
                    if context
                        .function_status
                        .fun_set_with_no_inv_check
                        .contains(&callee_id)
                    {
                        // skip instrumentation if invariant checking is disabled in body
                        if !assert_invariants_at_return {
                            debug_assert!(last_opaque_call_info.is_some());
                            let (callee_modified_mems, xlated_update_invs) =
                                last_opaque_call_info.take().unwrap();
                            Self::emit_assert_for_update_and_global_invs(
                                builder,
                                context,
                                xlated_update_invs,
                                callee_modified_mems.iter(),
                            );
                        }
                    }
                }
                Call(_, _, Function(mid, fid, callee_inst), _, _) => {
                    let callee_id = mid.qualified(*fid);

                    // instrument the regular call if it is in the N set
                    if context
                        .function_status
                        .fun_set_with_no_inv_check
                        .contains(&callee_id)
                    {
                        // collect memories modified by the callee
                        let callee_modified_mems: BTreeSet<_> = context
                            .modified_mems_by_callee
                            .get(&callee_id)
                            .unwrap()
                            .iter()
                            .map(|mem| mem.instantiate_ref(callee_inst))
                            .collect();

                        if assert_invariants_at_return {
                            // skip instrumentation if invariant checking is disabled in body
                            mems_modified_in_body.extend(callee_modified_mems);
                            builder.emit(bc);
                        } else {
                            // pre-instrumentation
                            let xlated_update_invs = Self::emit_save_mem_for_update_invs(
                                builder,
                                context,
                                callee_modified_mems.iter(),
                            );

                            builder.emit(bc);

                            // post-instrumentation
                            Self::emit_assert_for_update_and_global_invs(
                                builder,
                                context,
                                xlated_update_invs,
                                callee_modified_mems.iter(),
                            );
                        }
                    } else {
                        // the regular call is not in the N set, emit the call without instrumentation
                        builder.emit(bc);
                    }
                }
                _ => {
                    builder.emit(bc);
                }
            }
        }

        // return the list of memories modified in body if invariant assertion is turned-off in body
        debug_assert!(last_opaque_call_info.is_none());
        mems_modified_in_body
    }

    fn emit_save_mem_for_update_invs<'a>(
        builder: &mut FunctionDataBuilder,
        context: &InstrumentationContext,
        mems: impl Iterator<Item = &'a QualifiedInstId<StructId>>,
    ) -> Vec<(Loc, GlobalId, Exp)> {
        // collect all related update invariants
        let mut update_invs = BTreeMap::new();
        for mem in mems {
            if let Some(invs) = context.related_update_invs_by_mem.get(mem) {
                for (inv_id, inv_inst) in invs {
                    update_invs
                        .entry(*inv_id)
                        .or_insert_with(BTreeSet::new)
                        .extend(inv_inst.iter().cloned());
                }
            }
        }

        // save state snapshots for each of the update invariants
        let xlated = Self::translate_invariants(builder, &update_invs);
        let TranslatedSpec {
            saved_memory,
            saved_spec_vars,
            invariants,
            ..
        } = xlated;
        Self::emit_state_saves_for_update_invs(builder, saved_memory, saved_spec_vars);

        // return the translated invariants
        invariants
    }

    fn emit_assert_for_update_and_global_invs<'a>(
        builder: &mut FunctionDataBuilder,
        context: &InstrumentationContext,
        xlated_update_invs: Vec<(Loc, GlobalId, Exp)>,
        mems: impl Iterator<Item = &'a QualifiedInstId<StructId>>,
    ) {
        // assert update invariants
        Self::assert_or_assume_translated_invariants(builder, xlated_update_invs, PropKind::Assert);

        // collect all related global invariants
        let mut global_invs = BTreeMap::new();
        for mem in mems {
            if let Some(invs) = context.related_global_invs_by_mem.get(mem) {
                for (inv_id, inv_inst) in invs {
                    global_invs
                        .entry(*inv_id)
                        .or_insert_with(BTreeSet::new)
                        .extend(inv_inst.iter().cloned());
                }
            }
        }

        // assert global invariants
        let xlated = Self::translate_invariants(builder, &global_invs);
        Self::assert_or_assume_translated_invariants(builder, xlated.invariants, PropKind::Assert);
    }

    /// Translate the given invariants (with instantiations). This will care for instantiating the
    /// invariants in the function context as well.
    fn translate_invariants(
        builder: &mut FunctionDataBuilder,
        invs_with_insts: &BTreeMap<GlobalId, BTreeSet<Vec<Type>>>,
    ) -> TranslatedSpec {
        let env = builder.global_env();
        let options = ProverOptions::get(env);

        let inst_invs = invs_with_insts
            .iter()
            .map(|(inv_id, inv_insts)| inv_insts.iter().map(move |inst| (*inv_id, inst.clone())))
            .flatten();
        SpecTranslator::translate_invariants_by_id(
            options.auto_trace_level.invariants(),
            builder,
            inst_invs,
        )
    }

    /// Emit an assert or assume for all invariants found in the `TranslatedSpec`
    fn assert_or_assume_translated_invariants(
        builder: &mut FunctionDataBuilder,
        xlated_invariants: Vec<(Loc, GlobalId, Exp)>,
        prop_kind: PropKind,
    ) {
        for (loc, _, cond) in xlated_invariants {
            Self::emit_invariant(builder, loc, cond, prop_kind);
        }
    }

    /// Emit an assert or assume for one invariant, give location and expression for the property
    fn emit_invariant(builder: &mut FunctionDataBuilder, loc: Loc, cond: Exp, prop_kind: PropKind) {
        builder.set_next_debug_comment(format!(
            "global invariant {}",
            loc.display(builder.global_env())
        ));
        // No error messages on assumes
        if matches!(prop_kind, PropKind::Assert) {
            builder.set_loc_and_vc_info(loc, GLOBAL_INVARIANT_FAILS_MESSAGE);
        }
        builder.emit_with(|id| Bytecode::Prop(id, prop_kind, cond));
    }

    /// Update invariants contain "old" expressions, so it is necessary to save any types in the
    /// state that appear in the old expressions.
    fn emit_state_saves_for_update_invs(
        builder: &mut FunctionDataBuilder,
        xlated_saved_memory: BTreeMap<QualifiedInstId<StructId>, MemoryLabel>,
        xlated_saved_spec_var: BTreeMap<QualifiedInstId<SpecVarId>, MemoryLabel>,
    ) {
        // Emit all necessary state saves
        builder.set_next_debug_comment("state save for global update invariants".to_string());
        for (mem, label) in xlated_saved_memory {
            builder.emit_with(|id| Bytecode::SaveMem(id, label, mem));
        }
        for (var, label) in xlated_saved_spec_var {
            builder.emit_with(|id| Bytecode::SaveSpecVar(id, label, var));
        }
        builder.clear_next_debug_comment();
    }
}

// Utility functions
fn _is_invariant_isolated(env: &GlobalEnv, inv_id: GlobalId) -> bool {
    let inv = env.get_global_invariant(inv_id).unwrap();
    env.is_property_true(&inv.properties, CONDITION_ISOLATED_PROP)
        .unwrap_or(false)
}
