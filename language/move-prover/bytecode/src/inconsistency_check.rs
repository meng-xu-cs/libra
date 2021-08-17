// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! Instrument `assert false;` in strategic locations in the program such that if proved, signals
//! an inconsistency among the specifications.
//!
//! The presence of inconsistency is a serious issue. If there is an inconsistency in the
//! verification assumptions (perhaps due to a specification mistake or a Prover bug), any false
//! post-condition can be proved vacuously. The `InconsistencyCheckInstrumentationProcessor` adds
//! an `assert false` before
//! - every `return` and
//! - every `abort` (if the `unconditional-abort-as-inconsistency` option is set).
//! In this way, if the instrumented `assert false` can be proved, it means we have an inconsistency
//! in the specifications.
//!
//! A function that unconditionally abort might be considered as some form of inconsistency as well.
//! Consider the function `fun always_abort() { abort 0 }`, it might seem surprising that the prover
//! can prove that `spec always_abort { ensures 1 == 2; }`. If this function aborts unconditionally,
//! any post-condition can be proved. Checking of this behavior is turned-off by default, and can
//! be enabled with the `unconditional-abort-as-inconsistency` flag.

use crate::{
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{
        FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant, InconsistencyCanary,
        VerificationFlavor,
    },
    stackless_bytecode::{Bytecode, Constant, PropKind},
};

use move_model::{
    exp_generator::ExpGenerator,
    model::FunctionEnv,
    ty::{PrimitiveType, Type},
};

// This message is for the boogie wrapper, and not shown to the users.
pub const EXPECTED_TO_FAIL: &str = "expected to fail";

pub struct InconsistencyCheckInstrumenter {}

impl InconsistencyCheckInstrumenter {
    pub fn new() -> Box<Self> {
        Box::new(Self {})
    }
}

impl FunctionTargetProcessor for InconsistencyCheckInstrumenter {
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
        let flavor = match &data.variant {
            FunctionVariant::Baseline
            | FunctionVariant::Verification(VerificationFlavor::Inconsistency(..)) => {
                // instrumentation only applies to non-inconsistency verification variants
                return data;
            }
            FunctionVariant::Verification(flavor) => flavor.clone(),
        };

        // fork and instrumentation
        let new_data = Self::instrument_canary_on_abort(fun_env, &data, flavor.clone());
        targets.insert_target_data(
            &fun_env.get_qualified_id(),
            new_data.variant.clone(),
            new_data,
        );

        let new_data = Self::instrument_canary_on_return(fun_env, &data, flavor);
        targets.insert_target_data(
            &fun_env.get_qualified_id(),
            new_data.variant.clone(),
            new_data,
        );

        // the original function data is unchanged
        data
    }

    fn name(&self) -> String {
        "inconsistency_check_instrumenter".to_string()
    }
}

impl InconsistencyCheckInstrumenter {
    fn instrument_canary_on_abort(
        fun_env: &FunctionEnv,
        data: &FunctionData,
        flavor: VerificationFlavor,
    ) -> FunctionData {
        // create a clone of the data for inconsistency check
        let new_data = data.fork(FunctionVariant::Verification(
            VerificationFlavor::Inconsistency(InconsistencyCanary::OnAbort, Box::new(flavor)),
        ));

        // instrumentation
        let mut builder = FunctionDataBuilder::new(fun_env, new_data);

        // instrument an `assert false` before the return
        let old_code = std::mem::take(&mut builder.data.code);
        for bc in old_code {
            if matches!(bc, Bytecode::Abort(..)) {
                Self::instrument_canary(&mut builder);
            }
            builder.emit(bc);
        }

        builder.data
    }

    fn instrument_canary_on_return(
        fun_env: &FunctionEnv,
        data: &FunctionData,
        flavor: VerificationFlavor,
    ) -> FunctionData {
        // create a clone of the data for inconsistency check
        let new_data = data.fork(FunctionVariant::Verification(
            VerificationFlavor::Inconsistency(InconsistencyCanary::OnReturn, Box::new(flavor)),
        ));

        // instrumentation
        let mut builder = FunctionDataBuilder::new(fun_env, new_data);

        // instrument an `assert false` before the return
        let old_code = std::mem::take(&mut builder.data.code);
        for bc in old_code {
            if matches!(bc, Bytecode::Ret(..)) {
                Self::instrument_canary(&mut builder);
            }
            builder.emit(bc);
        }

        builder.data
    }

    fn instrument_canary(builder: &mut FunctionDataBuilder) {
        builder.set_loc_and_vc_info(builder.fun_env.get_spec_loc(), EXPECTED_TO_FAIL);
        let exp_false = builder.mk_bool_const(false);
        builder.emit_with(|id| Bytecode::Prop(id, PropKind::Assert, exp_false));
    }
}
