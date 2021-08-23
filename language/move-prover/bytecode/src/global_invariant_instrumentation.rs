// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

// Transformation which injects global invariants into the bytecode.

use crate::{
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{
        FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant, VerificationFlavor,
    },
    instantiation_analysis,
    options::ProverOptions,
    stackless_bytecode::{BorrowNode, Bytecode, Operation, PropKind},
    verification_analysis_v2::InvariantAnalysisData,
};

use move_model::{
    ast::{ConditionKind, Exp, GlobalInvariant},
    exp_generator::ExpGenerator,
    model::{FunId, FunctionEnv, GlobalEnv, GlobalId, Loc, QualifiedId, QualifiedInstId, StructId},
    pragmas::CONDITION_ISOLATED_PROP,
    spec_translator::{SpecTranslator, TranslatedSpec},
    ty::{Type, TypeUnificationAdapter, Variance},
};

use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};

const GLOBAL_INVARIANT_FAILS_MESSAGE: &str = "global memory invariant does not hold";

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

        let mut main_invariants = None;
        let mut variants = vec![];
        for ((fun_inst, fun_phantom), invariants) in &instantiations.invariant_applicability {
            let is_original = fun_phantom.is_empty()
                && fun_inst
                    .iter()
                    .enumerate()
                    .all(|(i, ty)| matches!(ty, Type::TypeParameter(idx) if *idx as usize == i));

            if is_original {
                main_invariants = Some(invariants);
            } else {
                let variant_data = data.fork_with_instantiation(
                    env,
                    fun_inst,
                    fun_phantom,
                    FunctionVariant::Verification(VerificationFlavor::Instantiated(variants.len())),
                );
                variants.push((variant_data, invariants));
            }
        }

        // Instrument the main variant
        let main = Instrumenter::run(fun_env, data, main_invariants.unwrap());

        // Instrument the variants representing different instantiations
        for (variant_data, variant_global_invariants) in variants {
            let variant_instrumented =
                Instrumenter::run(fun_env, variant_data, variant_global_invariants);
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

struct Instrumenter<'a> {
    options: &'a ProverOptions,
    builder: FunctionDataBuilder<'a>,
    related_invariants: &'a BTreeMap<GlobalId, BTreeSet<Vec<Type>>>,
    related_invariants_by_mem:
        BTreeMap<QualifiedInstId<StructId>, BTreeMap<GlobalId, BTreeSet<&'a Vec<Type>>>>,
    saved_from_before_instr_or_call: Option<(TranslatedSpec, BTreeSet<GlobalId>)>,
}

impl<'a> Instrumenter<'a> {
    fn run(
        fun_env: &FunctionEnv<'a>,
        data: FunctionData,
        related_invariants: &'a BTreeMap<GlobalId, BTreeSet<Vec<Type>>>,
    ) -> FunctionData {
        let env = fun_env.module_env.env;
        let options = ProverOptions::get(env);
        let builder = FunctionDataBuilder::new(fun_env, data);

        // derive a per-mem view of applicable invariants
        let mut related_invariants_by_mem = BTreeMap::new();
        for (inv_id, inv_insts) in related_invariants.iter() {
            for inv_inst in inv_insts {
                let inv = env.get_global_invariant(*inv_id).unwrap();
                for mem in inv.mem_usage.iter() {
                    let mem_inst = mem.instantiate_ref(inv_inst);
                    related_invariants_by_mem
                        .entry(mem_inst)
                        .or_insert_with(BTreeMap::new)
                        .entry(*inv_id)
                        .or_insert_with(BTreeSet::new)
                        .insert(inv_inst);
                }
            }
        }

        let mut instrumenter = Instrumenter {
            options: options.as_ref(),
            builder,
            related_invariants,
            related_invariants_by_mem,
            saved_from_before_instr_or_call: None,
        };
        instrumenter.instrument();
        instrumenter.builder.data
    }

    fn instrument(&mut self) {
        // Extract and clear current code
        let old_code = std::mem::take(&mut self.builder.data.code);

        // Emit entrypoint assumptions, i.e., an assume of each invariant over memory directly
        // touched by this function, regardless of where the invariant is defined, as long as the
        // invariant is in the `related_invariants` set. But after some filtering.
        let entrypoint_invariants = self.filter_entrypoint_invariants();
        let xlated_spec = self.translate_invariants(&entrypoint_invariants);
        self.assert_or_assume_translated_invariants(
            &xlated_spec.invariants,
            &entrypoint_invariants,
            PropKind::Assume,
        );

        // Generate new instrumented code.
        for bc in old_code {
            self.instrument_bytecode(bc);
        }
    }

    /// Returns list of invariant ids to be assumed at the beginning of the current function.
    fn filter_entrypoint_invariants(&self) -> BTreeSet<GlobalId> {
        // Excludes global invariants that are
        // - "update" invariants, or
        // - marked by the user explicitly as `[isolated]`.

        let env = self.builder.global_env();
        self.related_invariants
            .keys()
            .filter(|id| {
                let inv = env.get_global_invariant(**id).unwrap();
                // excludes "update invariants" and `[isolated]` invariants
                matches!(inv.kind, ConditionKind::GlobalInvariant(..))
                    && !env
                        .is_property_true(&inv.properties, CONDITION_ISOLATED_PROP)
                        .unwrap_or(false)
            })
            .cloned()
            .collect()
    }

    fn instrument_bytecode(&mut self, bc: Bytecode) {
        use BorrowNode::*;
        use Bytecode::*;
        use Operation::*;

        match &bc {
            Call(_, _, WriteBack(GlobalRoot(mem), ..), ..) => {
                self.emit_invariants_for_bytecode(&bc, mem);
            }
            Call(_, _, MoveTo(mid, sid, inst), ..) | Call(_, _, MoveFrom(mid, sid, inst), ..) => {
                let mem = mid.qualified_inst(*sid, inst.to_owned());
                self.emit_invariants_for_bytecode(&bc, &mem);
            }
            // Emit assumes before procedure calls.  This also deals with saves for update invariants.
            Call(_, _, OpaqueCallBegin(module_id, id, _), _, _) => {
                self.assume_invariants_for_opaque_begin(
                    module_id.qualified(*id),
                    entrypoint_invariants,
                    inv_ana_data,
                );
                // Then emit the call instruction.
                self.builder.emit(bc);
            }
            // Emit asserts after procedure calls
            Call(_, _, OpaqueCallEnd(module_id, id, _), _, _) => {
                // First, emit the call instruction.
                self.builder.emit(bc.clone());
                self.assert_invariants_for_opaque_end(module_id.qualified(*id), inv_ana_data)
            }
            // An inline call needs to be treated similarly (but there is just one instruction.
            Call(_, _, Function(module_id, id, _), _, _) => {
                self.assume_invariants_for_opaque_begin(
                    module_id.qualified(*id),
                    entrypoint_invariants,
                    inv_ana_data,
                );
                // Then emit the call instruction.
                self.builder.emit(bc.clone());
                self.assert_invariants_for_opaque_end(module_id.qualified(*id), inv_ana_data)
            }
            // When invariants are disabled in the body of this function but not in its
            // callers, assert them just before a return instruction (the caller will be
            // assuming they hold).
            Ret(_, _) => {
                if disabled_inv_fun_set.contains(&fun_id) {
                    // TODO: It is only necessary to assert invariants that were disabled here.
                    // Asserting more won't hurt, but generates unnecessary work for the prover.
                    let (global_target_invs, _update_target_invs) =
                        self.separate_update_invariants(target_invariants);
                    let xlated_spec = self.translate_invariants(&global_target_invs);
                    self.assert_or_assume_translated_invariants(
                        &xlated_spec.invariants,
                        &global_target_invs,
                        PropKind::Assert,
                    );
                }
                self.builder.emit(bc);
            }
            _ => self.builder.emit(bc),
        }
    }

    /// Emit invariants and saves for call to OpaqueCallBegin in the
    /// special case where the invariants are not checked in the
    /// called function.
    fn assume_invariants_for_opaque_begin(
        &mut self,
        called_fun_id: QualifiedId<FunId>,
        entrypoint_invariants: &BTreeSet<GlobalId>,
        inv_ana_data: &InvariantAnalysisData,
    ) {
        let target_invariants = &inv_ana_data.target_invariants;
        let disabled_inv_fun_set = &inv_ana_data.disabled_inv_fun_set;
        let non_inv_fun_set = &inv_ana_data.non_inv_fun_set;
        let funs_that_modify_inv = &inv_ana_data.funs_that_modify_inv;
        // Normally, invariants would be assumed and asserted in
        // a called function, and so there would be no need to assume
        // the invariant before the call.
        // When invariants are not disabled in the current function
        // but the called function doesn't check them, we are going to
        // need to assert the invariant when the call returns (at the
        // matching OpaqueCallEnd instruction). So, we assume the
        // invariant here, before the OpaqueCallBegin, so that we have
        // a hope of proving it later.
        let fun_id = self.builder.fun_env.get_qualified_id();
        if !disabled_inv_fun_set.contains(&fun_id)
            && !non_inv_fun_set.contains(&fun_id)
            && non_inv_fun_set.contains(&called_fun_id)
        {
            // Do not assume update invs
            // This prevents ASSERTING the updates because emit_assumes_and_saves
            // stores translated invariants for assertion in assume_invariants_for_opaque_end,
            // and we don't want updates to be asserted there.
            // TODO: This should all be refactored to eliminate hacks like the previous
            // sentence.
            let (global_invs, _update_invs) = self.separate_update_invariants(target_invariants);
            // assume the invariants that are modified by the called function
            let modified_invs =
                self.get_invs_modified_by_fun(&global_invs, called_fun_id, funs_that_modify_inv);
            self.emit_assumes_and_saves_before_bytecode(modified_invs, entrypoint_invariants);
        }
    }

    /// Called when invariants need to be checked, but an opaque called function
    /// doesn't check them.
    fn assert_invariants_for_opaque_end(
        &mut self,
        called_fun_id: QualifiedId<FunId>,
        inv_ana_data: &InvariantAnalysisData,
    ) {
        let disabled_inv_fun_set = &inv_ana_data.disabled_inv_fun_set;
        let non_inv_fun_set = &inv_ana_data.non_inv_fun_set;
        // Add invariant assertions after function call when invariant holds in the
        // body of the current function, but the called function does not assert
        // invariants.
        // The asserted invariant ensures the the invariant
        // holds in the body of the current function, as is required.
        let fun_id = self.builder.fun_env.get_qualified_id();
        if !disabled_inv_fun_set.contains(&fun_id)
            && !non_inv_fun_set.contains(&fun_id)
            && non_inv_fun_set.contains(&called_fun_id)
        {
            self.emit_asserts_after_bytecode();
        }
    }

    /// Emit invariant-related assumptions and assertions around a bytecode.
    /// Before instruction, emit assumptions of global update invariants, if necessary,
    /// and emit saves of old state for update invariants.
    fn emit_invariants_for_bytecode(&mut self, bc: &Bytecode, mem: &QualifiedInstId<StructId>) {
        // When invariants are enabled during the body of the current function, add asserts after
        // the operation for each invariant that the operation could modify. Such an operation
        // includes write-backs to a GlobalRoot or MoveTo/MoveFrom a location in the global storage.
        // In these cases, consider only the invariants that are modified by instruction
        let modified_invariants = self.related_invariants_by_mem.get(mem).unwrap();

        self.emit_assumes_and_saves_before_bytecode(modified_invariants);
        // put out the modifying instruction byte code.
        self.builder.emit(bc.clone());
        self.emit_asserts_after_bytecode();
    }

    // emit assumptions for "update" invariants (which are not assumed on entry) and saves for types
    // that are embedded in "old" in the "update" invariants.
    fn emit_assumes_and_saves_before_bytecode(
        &mut self,
        modified_invariants: &BTreeMap<GlobalId, BTreeSet<&Vec<Type>>>,
    ) {
        // translate all the invariants. Some were already translated at the entrypoint, but
        // that's ok because entrypoint invariants are global invariants that don't have "old",
        // so redundant state tags are not going to be a problem.
        let mut xlated_invs = self.translate_invariants_2(modified_invs);

        let (global_invs, _update_invs) = self.separate_update_invariants(&modified_invs);

        // assume the global invariants that weren't assumed at entrypoint
        self.assert_or_assume_translated_invariants(
            &xlated_invs.invariants,
            &modified_assumes,
            PropKind::Assume,
        );
        // emit the instructions to save state in the state tags assigned in the previous step
        self.emit_state_saves_for_update_invs(&mut xlated_invs);
        // Save the translated invariants for use in asserts after instruction or opaque call end
        if self.saved_from_before_instr_or_call.is_none() {
            self.saved_from_before_instr_or_call = Some((xlated_invs, modified_invs));
        } else {
            panic!("self.saved_from_pre should be None");
        }
    }

    fn emit_asserts_after_bytecode(&mut self) {
        // assert the global and update invariants that instruction modifies, regardless of where they
        // were assumed
        if let Some((xlated_invs, modified_invs)) =
            std::mem::take(&mut self.saved_from_before_instr_or_call)
        {
            self.assert_or_assume_translated_invariants(
                &xlated_invs.invariants,
                &modified_invs,
                PropKind::Assert,
            );
        } else {
            // This should never happen
            panic!("saved_from_pre should be Some");
        }
    }

    /// Given a set of invariants, return a pair of sets: global invariants and update invariants
    fn separate_update_invariants(
        &self,
        invariants: &BTreeSet<GlobalId>,
    ) -> (BTreeSet<GlobalId>, BTreeSet<GlobalId>) {
        let global_env = self.builder.fun_env.module_env.env;
        let mut global_invs: BTreeSet<GlobalId> = BTreeSet::new();
        let mut update_invs: BTreeSet<GlobalId> = BTreeSet::new();
        for inv_id in invariants {
            let inv = global_env.get_global_invariant(*inv_id).unwrap();
            if matches!(inv.kind, ConditionKind::GlobalInvariantUpdate(..)) {
                update_invs.insert(*inv_id);
            } else {
                global_invs.insert(*inv_id);
            }
        }
        (global_invs, update_invs)
    }

    /// Returns the set of invariants modified by a function
    fn get_invs_modified_by_fun(
        &self,
        inv_set: &BTreeSet<GlobalId>,
        fun_id: QualifiedId<FunId>,
        funs_that_modify_inv: &BTreeMap<GlobalId, BTreeSet<QualifiedId<FunId>>>,
    ) -> BTreeSet<GlobalId> {
        let mut modified_inv_set: BTreeSet<GlobalId> = BTreeSet::new();
        for inv_id in inv_set {
            if let Some(fun_id_set) = funs_that_modify_inv.get(inv_id) {
                if fun_id_set.contains(&fun_id) {
                    modified_inv_set.insert(*inv_id);
                }
            }
        }
        modified_inv_set
    }

    /// Update invariants contain "old" expressions, so it is necessary to save any types in the
    /// state that appear in the old expressions.  "update_invs" argument must contain only update
    /// invariants (not checked).
    fn emit_state_saves_for_update_invs(&mut self, xlated_spec: &mut TranslatedSpec) {
        // Emit all necessary state saves
        self.builder
            .set_next_debug_comment("state save for global update invariants".to_string());
        for (mem, label) in std::mem::take(&mut xlated_spec.saved_memory) {
            self.builder
                .emit_with(|id| Bytecode::SaveMem(id, label, mem));
        }
        for (var, label) in std::mem::take(&mut xlated_spec.saved_spec_vars) {
            self.builder
                .emit_with(|id| Bytecode::SaveSpecVar(id, label, var));
        }
        self.builder.clear_next_debug_comment();
    }

    /// emit asserts or assumes (depending on prop_kind argument) for the invariants in
    /// xlated_invariants that is also in inv_set at the current location.
    ///
    /// TODO(mengxu) I don't think these checks are necessary, but leaving it here for now just in
    /// case I miss anything
    fn assert_or_assume_translated_invariants(
        &mut self,
        xlated_invariants: &[(Loc, GlobalId, Exp)],
        inv_set: &BTreeSet<GlobalId>,
        prop_kind: PropKind,
    ) {
        let global_env = self.builder.global_env();
        for (loc, mid, cond) in xlated_invariants {
            if inv_set.contains(mid) {
                // Check for hard-to-debug coding error (this is not a user error)
                if inv_set.contains(mid)
                    && matches!(prop_kind, PropKind::Assume)
                    && matches!(
                        global_env.get_global_invariant(*mid).unwrap().kind,
                        ConditionKind::GlobalInvariantUpdate(..)
                    )
                {
                    panic!("Not allowed to assume update invariant");
                }
                self.emit_invariant(loc, cond, prop_kind);
            }
        }
    }

    /// Emit an assert or assume for one invariant, give location and expression for the property
    fn emit_invariant(&mut self, loc: &Loc, cond: &Exp, prop_kind: PropKind) {
        self.builder.set_next_debug_comment(format!(
            "global invariant {}",
            loc.display(self.builder.global_env())
        ));
        // No error messages on assumes
        if matches!(prop_kind, PropKind::Assert) {
            self.builder
                .set_loc_and_vc_info(loc.clone(), GLOBAL_INVARIANT_FAILS_MESSAGE);
        }
        self.builder
            .emit_with(|id| Bytecode::Prop(id, prop_kind, cond.clone()));
    }

    /// Translate the given set of invariants. This will care for instantiating the invariants in
    /// the function context.
    fn translate_invariants(&mut self, invs: &BTreeSet<GlobalId>) -> TranslatedSpec {
        let inst_invs = invs
            .iter()
            .map(|inv_id| {
                let insts = self.related_invariants.get(inv_id).unwrap();
                insts.iter().map(|inst| (*inv_id, inst.clone()))
            })
            .flatten();
        SpecTranslator::translate_invariants_by_id(
            self.options.auto_trace_level.invariants(),
            &mut self.builder,
            inst_invs,
        )
    }

    fn translate_invariants_2(
        &mut self,
        invs_with_insts: &BTreeMap<GlobalId, &BTreeSet<Vec<Type>>>,
    ) -> TranslatedSpec {
        let inst_invs = invs_with_insts
            .iter()
            .map(|(inv_id, inv_insts)| inv_insts.iter().map(|inst| (*inv_id, inst.clone())))
            .flatten();
        SpecTranslator::translate_invariants_by_id(
            self.options.auto_trace_level.invariants(),
            &mut self.builder,
            inst_invs,
        )
    }
}
