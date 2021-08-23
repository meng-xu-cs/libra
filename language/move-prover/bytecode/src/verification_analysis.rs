// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! Analysis which computes an annotation for each function on whether this function should be
//! verified or inlined.

use crate::{
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    instantiation_analysis::InvariantAnalysisData,
    options::ProverOptions,
};

use move_model::{
    model::{FunctionEnv, GlobalEnv, VerificationScope},
    pragmas::VERIFY_PRAGMA,
};

use std::collections::BTreeSet;

/// The annotation for information about verification.
#[derive(Clone, Default)]
pub struct VerificationInfo {
    /// Whether the function is target of verification.
    pub verified: bool,
    /// Whether the function needs to have an inlined variant since it is called from a verified
    /// function and is not opaque.
    pub inlined: bool,
}

/// Get verification information for this function.
pub fn get_info(target: &FunctionTarget<'_>) -> VerificationInfo {
    target
        .get_annotations()
        .get::<VerificationInfo>()
        .cloned()
        .unwrap_or_else(VerificationInfo::default)
}

pub struct VerificationAnalysisProcessor();

impl VerificationAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for VerificationAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv<'_>,
        mut data: FunctionData,
    ) -> FunctionData {
        // This function implements the logic to decide whether to verify this function

        // Rule 1: never verify if "pragma verify = false;"
        if !fun_env.is_pragma_true(VERIFY_PRAGMA, || true) {
            return data;
        }

        // Rule 2: verify the function if it is within the target modules
        let env = fun_env.module_env.env;
        let target_modules = env.get_target_modules();

        let is_in_target_module = target_modules
            .iter()
            .any(|menv| menv.get_id() == fun_env.module_env.get_id());
        if is_in_target_module {
            if Self::within_verification_scope(fun_env) {
                Self::mark_verified(fun_env, &mut data, targets);
            }
            return data;
        }

        // Rule 3: verify the function if it directly uses an invariant that is defined in the
        // target modules
        let inv_analysis = env.get_extension::<InvariantAnalysisData>().unwrap();
        let target_invs: BTreeSet<_> = target_modules
            .iter()
            .map(|menv| env.get_global_invariants_by_module(menv.get_id()))
            .flatten()
            .collect();
        let inv_relevance = inv_analysis
            .fun_to_inv_map
            .get(&fun_env.get_qualified_id())
            .unwrap();
        if !inv_relevance.direct_uses.is_disjoint(&target_invs) {
            if Self::within_verification_scope(fun_env) {
                Self::mark_verified(fun_env, &mut data, targets);
            }
            return data;
        }

        // we don't verify this function
        data
    }

    fn name(&self) -> String {
        "verification_analysis".to_string()
    }

    fn initialize(&self, global_env: &GlobalEnv, _targets: &mut FunctionTargetsHolder) {
        let options = ProverOptions::get(global_env);

        // If we are verifying only one function or module, check that this indeed exists.
        match &options.verify_scope {
            VerificationScope::Only(name) | VerificationScope::OnlyModule(name) => {
                let for_module = matches!(&options.verify_scope, VerificationScope::OnlyModule(_));
                let mut target_exists = false;
                for module in global_env.get_modules() {
                    if module.is_target() {
                        if for_module {
                            target_exists = module.matches_name(name)
                        } else {
                            target_exists = module.get_functions().any(|f| f.matches_name(name));
                        }
                        if target_exists {
                            break;
                        }
                    }
                }
                if !target_exists {
                    global_env.error(
                        &global_env.unknown_loc(),
                        &format!(
                            "{} target {} does not exist in target modules",
                            if for_module { "module" } else { "function" },
                            name
                        ),
                    )
                }
            }
            _ => {}
        }
    }
}

impl VerificationAnalysisProcessor {
    fn within_verification_scope(fun_env: &FunctionEnv) -> bool {
        let env = fun_env.module_env.env;
        let options = ProverOptions::get(env);
        match &options.verify_scope {
            VerificationScope::Public => fun_env.is_exposed(),
            VerificationScope::All => true,
            VerificationScope::Only(name) => fun_env.matches_name(name),
            VerificationScope::OnlyModule(name) => fun_env.module_env.matches_name(name),
            VerificationScope::None => false,
        }
    }

    fn mark_verified(
        fun_env: &FunctionEnv,
        data: &mut FunctionData,
        targets: &mut FunctionTargetsHolder,
    ) {
        let mut info = data.annotations.get_or_default_mut::<VerificationInfo>();
        if !info.verified {
            info.verified = true;
            Self::mark_callees_inlined(fun_env, targets);
        }
    }

    fn mark_inlined(fun_env: &FunctionEnv, targets: &mut FunctionTargetsHolder) {
        if fun_env.is_opaque() || fun_env.is_native() || fun_env.is_intrinsic() {
            return;
        }

        let variant = FunctionVariant::Baseline;
        debug_assert!(
            targets.get_target_variants(fun_env).contains(&variant),
            "`{}` has variant `{:?}`",
            fun_env.get_name().display(fun_env.symbol_pool()),
            variant
        );
        let data = targets
            .get_data_mut(&fun_env.get_qualified_id(), &variant)
            .expect("function data defined");
        let info = data.annotations.get_or_default_mut::<VerificationInfo>();
        if !info.inlined {
            info.inlined = true;
            Self::mark_callees_inlined(fun_env, targets);
        }
    }

    fn mark_callees_inlined(fun_env: &FunctionEnv, targets: &mut FunctionTargetsHolder) {
        for callee in fun_env.get_called_functions() {
            let callee_env = fun_env.module_env.env.get_function(callee);
            Self::mark_inlined(&callee_env, targets);
        }
    }
}
