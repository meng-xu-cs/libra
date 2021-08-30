// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

// Instrumentation pass which injects global invariants into the bytecode.

use crate::{
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{
        FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant, VerificationFlavor,
    },
    global_invariant_analysis::{self, PerFunctionRelevance},
    options::ProverOptions,
    stackless_bytecode::{Bytecode, Operation, PropKind},
};

use move_binary_format::file_format::CodeOffset;
use move_model::{
    ast::Exp,
    exp_generator::ExpGenerator,
    model::{FunctionEnv, GlobalId, Loc},
    spec_translator::{SpecTranslator, TranslatedSpec},
    ty::Type,
};

use std::collections::{BTreeMap, BTreeSet};

const GLOBAL_INVARIANT_FAILS_MESSAGE: &str = "global memory invariant does not hold";

/// A transposed view of `PerFunctionRelevance` from the point of per function instantiations
#[derive(Default)]
struct InstrumentationPack {
    /// Invariants that needs to be assumed at function entrypoint
    /// - Key: global invariants that needs to be assumed before the first instruction,
    /// - Value: the instantiation information per each related invariant.
    entrypoint_assumptions: BTreeMap<GlobalId, BTreeSet<Vec<Type>>>,

    /// For each bytecode at given code offset, the associated value is a map of
    /// - Key: global invariants that needs to be asserted after the bytecode instruction and
    /// - Value: the instantiation information per each related invariant.
    per_bytecode_assertions: BTreeMap<CodeOffset, BTreeMap<GlobalId, BTreeSet<Vec<Type>>>>,
}

/// A transposed view of `PerFunctionRelevance` grouped by function instantiations
#[derive(Default)]
struct InstrumentationSummary {
    /// A condensed view of the `by_function_instantiation` field. An invariant will show up in the
    /// condensed pack as long as the instantiation of the invariant is applicable to any
    /// instantiation of the function.
    generic_condensation: InstrumentationPack,

    /// For each `inst_fun` (instantiation of function type parameters) in the key set, the
    /// associated value is a set of `inst_inv` (instantiation of invariant type parameters) that
    /// are applicable to the concrete function instance `F<inst_fun>`.
    by_function_instantiation: BTreeMap<Vec<Type>, InstrumentationPack>,
}

impl InstrumentationSummary {
    fn transpose(relevance: &PerFunctionRelevance) -> Self {
        // TODO(mengxu): this is needed here because we haven't finalized the approach to handle
        // uninstantiated type parameters in the invariant yet. An example is:
        // ```
        // invariant<CoinType>
        //   forall cap_owner: address where exists<MintCapability<CoinType>>(cap_owner):
        //      Roles::spec_has_treasury_compliance_role_addr(cap_owner)
        // ```
        // is applicable to function `Roles::grant_role()` (i.e., the invariant should be checked).
        // But the `CoinType` on the invariant side can not be instantiated.
        //
        // Currently, in the analysis pass implemented in `global_invariant_analysis.rs`, an
        // uninstantiated type parameter in the invariant side is marked as `Type::Error`.
        // Therefore, we can easily filter them out.
        //
        // Fortunately, there aren't many of such cases in the Diem Framework code base
        // (5 invariants out of 100+). Therefore, finalizing a solution to handle them is currently
        // in a lower priority. But we do hope to check them in the next iteration.
        fn filter_uninst_params(insts: &BTreeSet<Vec<Type>>) -> BTreeSet<Vec<Type>> {
            insts
                .iter()
                .filter(|inst| inst.iter().all(|t| !matches!(t, Type::Error)))
                .cloned()
                .collect()
        }

        let mut result = Self::default();

        // transpose the `entrypoint_assumptions`
        for (inv_id, inv_rel) in &relevance.entrypoint_assumptions {
            for (fun_inst, inv_insts) in &inv_rel.insts {
                let inv_insts = filter_uninst_params(inv_insts);
                result
                    .by_function_instantiation
                    .entry(fun_inst.clone())
                    .or_default()
                    .entrypoint_assumptions
                    .entry(*inv_id)
                    .or_default()
                    .extend(inv_insts.clone());
                result
                    .generic_condensation
                    .entrypoint_assumptions
                    .entry(*inv_id)
                    .or_default()
                    .extend(inv_insts);
            }
        }

        // transpose the `per_bytecode_assertions`
        for (code_offset, per_code) in &relevance.per_bytecode_assertions {
            for (inv_id, inv_rel) in per_code {
                for (fun_inst, inv_insts) in &inv_rel.insts {
                    let inv_insts = filter_uninst_params(inv_insts);
                    result
                        .by_function_instantiation
                        .entry(fun_inst.clone())
                        .or_default()
                        .per_bytecode_assertions
                        .entry(*code_offset)
                        .or_default()
                        .entry(*inv_id)
                        .or_default()
                        .extend(inv_insts.clone());
                    result
                        .generic_condensation
                        .per_bytecode_assertions
                        .entry(*code_offset)
                        .or_default()
                        .entry(*inv_id)
                        .or_default()
                        .extend(inv_insts);
                }
            }
        }

        result
    }
}

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
            // nothing to do
            return data;
        }
        if !data.variant.is_verified() {
            // only need to instrument if this is a verification variant
            return data;
        }
        debug_assert!(matches!(
            data.variant,
            FunctionVariant::Verification(VerificationFlavor::Regular)
        ));

        let env = fun_env.module_env.env;
        let options = ProverOptions::get(env);

        // retrieve and transpose the analysis result
        let target = FunctionTarget::new(fun_env, &data);
        let analysis_result = global_invariant_analysis::get_info(&target);
        let summary = InstrumentationSummary::transpose(analysis_result);

        // if the backend supports some form of monomorphization, instrument the invariants in
        // the generic version of the function only.
        if options.boogie_poly {
            return Instrumenter::new(fun_env, data).instrument(&summary.generic_condensation);
        }

        // otherwise, specialize the function and instrument corresponding invariants in the
        // specialized function instantiations.
        let mut main_pack = None;
        let mut variants = vec![];
        for (fun_inst, pack) in &summary.by_function_instantiation {
            let is_original = fun_inst
                .iter()
                .enumerate()
                .all(|(i, ty)| matches!(ty, Type::TypeParameter(idx) if *idx as usize == i));
            if is_original {
                main_pack = Some(pack);
            } else {
                let variant_data = data.fork_with_instantiation(
                    env,
                    fun_inst,
                    FunctionVariant::Verification(VerificationFlavor::Instantiated(variants.len())),
                );
                variants.push((variant_data, pack));
            }
        }

        // instrument the main variant.
        //
        // NOTE: it is possible that the `main_pack` is None, this means that there are no
        // invariants applicable to the generic form of the function.
        let main = match main_pack {
            None => data,
            Some(pack) => Instrumenter::new(fun_env, data).instrument(pack),
        };

        // instrument the variants that represent different instantiations
        for (variant_data, variant_pack) in variants {
            let variant_instrumented =
                Instrumenter::new(fun_env, variant_data).instrument(variant_pack);
            targets.insert_target_data(
                &fun_env.get_qualified_id(),
                variant_instrumented.variant.clone(),
                variant_instrumented,
            );
        }

        // return the main variant
        main
    }

    fn name(&self) -> String {
        "global_invariant_instrumentation".to_string()
    }
}

/// A contextualized instrumenter to handle the global invariant instrumentation process.
struct Instrumenter<'env> {
    builder: FunctionDataBuilder<'env>,
}

impl<'env> Instrumenter<'env> {
    fn new(fun_env: &'env FunctionEnv<'env>, data: FunctionData) -> Self {
        let builder = FunctionDataBuilder::new(fun_env, data);
        Self { builder }
    }

    /// The driver function for the overall instrumentation process
    fn instrument(mut self, pack: &InstrumentationPack) -> FunctionData {
        // extract and clear current code
        let old_code = std::mem::take(&mut self.builder.data.code);

        // pre-translate invariants
        //
        // NOTE: here, we need to save a reference to the `TranslatedSpec` for two special types
        // of instructions, OpaqueCallEnd and Return, in order to handle update invariants.
        //
        // - For an OpaqueCallEnd, we need to find the matching OpaqueCallBegin and emit the state
        //   snapshotting instructions there.
        //
        // - For a Return, we need to emit the state snapshotting instructions at the entry point,
        //   after the entry point assumptions.
        let xlated_entrypoint = self.translate_invariants(&pack.entrypoint_assumptions);
        let mut xlated_inlined = BTreeMap::new();
        let mut xlated_for_opaque_begin = BTreeMap::new();
        let mut xlated_for_return_point = None;
        for (&code_offset, related_invs) in &pack.per_bytecode_assertions {
            let xlated = self.translate_invariants(related_invs);
            xlated_inlined.insert(code_offset, xlated);

            match old_code.get(code_offset as usize).unwrap() {
                Bytecode::Call(_, _, Operation::OpaqueCallEnd(..), ..) => {
                    // first the matching OpaqueCallBegin
                    for needle in (0..(code_offset.wrapping_sub(1) as usize)).rev() {
                        if matches!(
                            old_code.get(needle).unwrap(),
                            Bytecode::Call(_, _, Operation::OpaqueCallBegin(..), ..)
                        ) {
                            xlated_for_opaque_begin.insert(needle as CodeOffset, code_offset);
                            break;
                        }
                    }
                }
                Bytecode::Ret(..) => {
                    xlated_for_return_point = Some(code_offset);
                }
                _ => (),
            }
        }

        // Step 1: emit entrypoint assumptions
        self.assert_or_assume_translated_invariants(&xlated_entrypoint, PropKind::Assume);

        // Step 2: emit entrypoint snapshots. This can happen if this function defers invariant
        // checking to the return point and one of the suspended invariant is an update invariant.
        if let Some(offset) = xlated_for_return_point {
            let xlated = xlated_inlined.get(&offset).unwrap();
            self.emit_state_saves_for_update_invs(xlated);
        }

        // Step 3: go over the bytecode and instrument assertions.
        //         For update invariants, instrument state snapshots before the bytecode.
        for (code_offset, bc) in old_code.into_iter().enumerate() {
            let code_offset = code_offset as CodeOffset;

            // pre-instrumentation for state snapshots
            if let Some(xlated) = xlated_for_opaque_begin
                .get(&code_offset)
                .map(|offset| xlated_inlined.get(offset).unwrap())
            {
                self.emit_state_saves_for_update_invs(xlated);
            }

            if let Some(xlated) = xlated_inlined.get(&code_offset) {
                self.emit_state_saves_for_update_invs(xlated);
            }

            // the bytecode itself
            self.builder.emit(bc);

            // post-instrumentation for assertions
            if let Some(xlated) = xlated_inlined.get(&code_offset) {
                self.assert_or_assume_translated_invariants(xlated, PropKind::Assert);
            }
        }

        // Finally, return with the new data accumulated
        self.builder.data
    }

    /// Translate the given invariants (with instantiations). This will care for instantiating the
    /// invariants in the function context as well.
    fn translate_invariants(
        &mut self,
        invs_with_insts: &BTreeMap<GlobalId, BTreeSet<Vec<Type>>>,
    ) -> TranslatedSpec {
        let env = self.builder.global_env();
        let options = ProverOptions::get(env);

        let inst_invs = invs_with_insts
            .iter()
            .map(|(inv_id, inv_insts)| inv_insts.iter().map(move |inst| (*inv_id, inst.clone())))
            .flatten();
        SpecTranslator::translate_invariants_by_id(
            options.auto_trace_level.invariants(),
            &mut self.builder,
            inst_invs,
        )
    }

    /// Emit an assert or assume for all invariants found in the `TranslatedSpec`
    fn assert_or_assume_translated_invariants(
        &mut self,
        xlated: &TranslatedSpec,
        prop_kind: PropKind,
    ) {
        for (loc, _, cond) in &xlated.invariants {
            self.emit_invariant(loc.clone(), cond.clone(), prop_kind);
        }
    }

    /// Emit an assert or assume for one invariant, give location and expression for the property
    fn emit_invariant(&mut self, loc: Loc, cond: Exp, prop_kind: PropKind) {
        self.builder.set_next_debug_comment(format!(
            "global invariant {}",
            loc.display(self.builder.global_env())
        ));
        // No error messages on assumes
        if matches!(prop_kind, PropKind::Assert) {
            self.builder
                .set_loc_and_vc_info(loc, GLOBAL_INVARIANT_FAILS_MESSAGE);
        }
        self.builder
            .emit_with(|id| Bytecode::Prop(id, prop_kind, cond));
    }

    /// Update invariants contain "old" expressions, so it is necessary to save any types in the
    /// state that appear in the old expressions.
    fn emit_state_saves_for_update_invs(&mut self, xlated: &TranslatedSpec) {
        // Emit all necessary state saves
        self.builder
            .set_next_debug_comment("state save for global update invariants".to_string());
        for (mem, label) in &xlated.saved_memory {
            self.builder
                .emit_with(|id| Bytecode::SaveMem(id, *label, mem.clone()));
        }
        for (var, label) in &xlated.saved_spec_vars {
            self.builder
                .emit_with(|id| Bytecode::SaveSpecVar(id, *label, var.clone()));
        }
        self.builder.clear_next_debug_comment();
    }
}
