// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use once_cell::sync::OnceCell;
use std::{
    cmp,
    collections::{BTreeMap, HashMap},
    hash,
};

use bytecode::{
    borrow_analysis::BorrowAnalysisProcessor,
    clean_and_optimize::CleanAndOptimizeProcessor,
    eliminate_imm_refs::EliminateImmRefsProcessor,
    eliminate_mut_refs::EliminateMutRefsProcessor,
    function_target::{FunctionTarget, FunctionTargetData},
    function_target_pipeline::{FunctionTargetPipeline, FunctionTargetsHolder},
    livevar_analysis::LiveVarAnalysisProcessor,
    memory_instrumentation::MemoryInstrumentationProcessor,
    reaching_def_analysis::ReachingDefProcessor,
    stackless_bytecode::{BorrowNode, Bytecode, Operation, TempIndex},
    stackless_bytecode_generator::StacklessBytecodeGenerator,
    stackless_control_flow_graph::StacklessControlFlowGraph,
};
use move_core_types::{
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId as ModuleIdByMove,
};
use spec_lang::env::{
    FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId as ModuleIdBySpec, StructEnv, StructId,
};

use crate::sym_filter::{collect_tracked_functions_and_script, FuncIdMatcher};

/// Lookup id for a `SymFuncInfo` in a `SymOracle`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct SymFuncId(usize);

/// Bridges and extends the `FunctionEnv` in move-prover
pub(crate) struct SymFuncInfo<'env> {
    func_id: SymFuncId,
    pub func_env: FunctionEnv<'env>,
    pub func_data: FunctionTargetData,
    pub func_cfg: StacklessControlFlowGraph,
    func_target: OnceCell<FunctionTarget<'env>>,
}

impl<'env> SymFuncInfo<'env> {
    fn new(func_id: SymFuncId, func_env: FunctionEnv<'env>, func_data: FunctionTargetData) -> Self {
        // generate control-flow graph
        let func_cfg = StacklessControlFlowGraph::new_forward(&func_data.code);
        debug_assert_eq!(func_cfg.entry_blocks().len(), 1);

        // done
        Self {
            func_id,
            func_env,
            func_data,
            func_cfg,
            func_target: OnceCell::new(),
        }
    }

    // getters
    pub fn get_context_string(&self) -> String {
        let module_env = &self.func_env.module_env;
        format!(
            "0x{}::{}::{}",
            if module_env.is_script_module() {
                String::from("X")
            } else {
                module_env.self_address().short_str_lossless()
            },
            module_env.get_identifier(),
            self.func_env.get_identifier()
        )
    }

    pub fn get_instructions(&self) -> &[Bytecode] {
        &self.func_data.code
    }

    pub fn get_target(&'env self) -> &FunctionTarget<'env> {
        self.func_target
            .get_or_init(|| FunctionTarget::new(&self.func_env, &self.func_data))
    }

    pub fn is_script_main(&self) -> bool {
        self.func_env.module_env.is_script_module()
    }
}

impl cmp::PartialEq for SymFuncInfo<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.func_id == other.func_id
    }
}

impl cmp::Eq for SymFuncInfo<'_> {}

/// Lookup id for a `SymStructInfo` in a `SymOracle`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct SymStructId(usize);

/// Bridges and extends the `StructEnv` in move-prover
pub(crate) struct SymStructInfo<'env> {
    pub struct_id: SymStructId,
    pub struct_env: StructEnv<'env>,
}

impl<'env> SymStructInfo<'env> {
    fn new(struct_id: SymStructId, struct_env: StructEnv<'env>) -> Self {
        Self {
            struct_id,
            struct_env,
        }
    }

    // getters
    pub fn get_context_string(&self) -> String {
        let module_env = &self.struct_env.module_env;
        format!(
            "0x{}::{}::{}",
            if module_env.is_script_module() {
                String::from("X")
            } else {
                module_env.self_address().short_str_lossless()
            },
            module_env.get_identifier(),
            self.struct_env.get_identifier()
        )
    }
}

impl cmp::PartialEq for SymStructInfo<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.struct_id == other.struct_id
    }
}

impl cmp::Eq for SymStructInfo<'_> {}

impl hash::Hash for SymStructInfo<'_> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.struct_id.hash(state);
    }
}

/// Bridges to the move-prover internals
pub(crate) struct SymOracle<'env> {
    script_env: ModuleEnv<'env>,
    // tracked functions with two ways to look it up
    tracked_functions: HashMap<SymFuncId, SymFuncInfo<'env>>,
    tracked_functions_by_spec: HashMap<ModuleIdBySpec, HashMap<FunId, SymFuncId>>,
    _tracked_functions_by_move: HashMap<ModuleIdByMove, HashMap<Identifier, SymFuncId>>,
    // defined structs with two ways to look it up
    defined_structs: HashMap<SymStructId, SymStructInfo<'env>>,
    defined_structs_by_spec: HashMap<ModuleIdBySpec, HashMap<StructId, SymStructId>>,
    defined_structs_by_move: HashMap<ModuleIdByMove, HashMap<Identifier, SymStructId>>,
}

impl<'env> SymOracle<'env> {
    pub fn new(
        global_env: &'env GlobalEnv,
        inclusion: Option<&[FuncIdMatcher]>,
        exclusion: &[FuncIdMatcher],
        no_pipeline: bool,
    ) -> Self {
        // collect tracked functions
        let (tracked_function_envs, script_env) =
            collect_tracked_functions_and_script(global_env, inclusion, Some(exclusion));

        // run prover passes
        let mut function_targets = if no_pipeline {
            run_stackless_bytecode_generator(global_env)
        } else {
            run_prover_passes(global_env)
        };

        // build per-function record
        let mut counter = 0;
        let mut tracked_functions = HashMap::new();
        let mut tracked_functions_by_spec = HashMap::new();
        let mut tracked_functions_by_move = HashMap::new();
        for (module_id, module_funcs) in tracked_function_envs {
            let mut module_funcs_by_spec = HashMap::new();
            let mut module_funcs_by_move = HashMap::new();
            for (func_id, func_env) in module_funcs {
                let sym_id = SymFuncId(counter);
                counter += 1;

                module_funcs_by_spec.insert(func_id, sym_id);
                module_funcs_by_move.insert(func_env.get_identifier(), sym_id);

                let func_data = function_targets
                    .targets
                    .remove(&func_env.get_qualified_id())
                    .unwrap();
                tracked_functions.insert(sym_id, SymFuncInfo::new(sym_id, func_env, func_data));
            }
            // checks that each `Idenifier` is unique, should never fail
            debug_assert_eq!(module_funcs_by_spec.len(), module_funcs_by_move.len());

            let module_env = global_env.get_module(module_id);
            tracked_functions_by_spec.insert(module_id, module_funcs_by_spec);
            tracked_functions_by_move.insert(
                ModuleIdByMove::new(*module_env.self_address(), module_env.get_identifier()),
                module_funcs_by_move,
            );
        }
        // checks that each `ModuleIdByMove` is unique, should never fail
        debug_assert_eq!(
            tracked_functions_by_spec.len(),
            tracked_functions_by_move.len()
        );

        // collect all defined structs
        counter = 0;
        let mut defined_structs = HashMap::new();
        let mut defined_structs_by_spec = HashMap::new();
        let mut defined_structs_by_move = HashMap::new();
        for module_env in global_env.get_modules() {
            let module_id_by_spec = module_env.get_id();
            let module_id_by_move =
                ModuleIdByMove::new(*module_env.self_address(), module_env.get_identifier());

            let mut module_structs_by_spec = HashMap::new();
            let mut module_structs_by_move = HashMap::new();
            for struct_env in module_env.into_structs() {
                let sym_id = SymStructId(counter);
                counter += 1;

                module_structs_by_spec.insert(struct_env.get_id(), sym_id);
                module_structs_by_move.insert(struct_env.get_identifier(), sym_id);
                defined_structs.insert(sym_id, SymStructInfo::new(sym_id, struct_env));
            }
            // checks that each `Idenifier` is unique, should never fail
            debug_assert_eq!(module_structs_by_spec.len(), module_structs_by_move.len());

            defined_structs_by_spec.insert(module_id_by_spec, module_structs_by_spec);
            defined_structs_by_move.insert(module_id_by_move, module_structs_by_move);
        }
        // checks that each `ModuleIdByMove` is unique, should never fail
        debug_assert_eq!(defined_structs_by_spec.len(), defined_structs_by_move.len());

        // done
        Self {
            script_env,
            tracked_functions,
            tracked_functions_by_spec,
            _tracked_functions_by_move: tracked_functions_by_move,
            defined_structs,
            defined_structs_by_spec,
            defined_structs_by_move,
        }
    }

    // lookup
    pub fn get_tracked_function_by_spec(
        &self,
        module_id: &ModuleIdBySpec,
        func_id: &FunId,
    ) -> Option<&SymFuncInfo<'env>> {
        self.tracked_functions_by_spec
            .get(module_id)
            .map(|funcs| funcs.get(func_id))
            .flatten()
            .map(|sym_id| self.tracked_functions.get(sym_id).unwrap())
    }

    pub fn _get_tracked_function_by_move(
        &self,
        module_id: &ModuleIdByMove,
        func_id: &IdentStr,
    ) -> Option<&SymFuncInfo<'env>> {
        self._tracked_functions_by_move
            .get(module_id)
            .map(|funcs| funcs.get(func_id))
            .flatten()
            .map(|sym_id| self.tracked_functions.get(sym_id).unwrap())
    }

    pub fn get_defined_struct_by_spec(
        &self,
        module_id: &ModuleIdBySpec,
        struct_id: &StructId,
    ) -> Option<&SymStructInfo<'env>> {
        self.defined_structs_by_spec
            .get(module_id)
            .map(|funcs| funcs.get(struct_id))
            .flatten()
            .map(|sym_id| self.defined_structs.get(sym_id).unwrap())
    }

    pub fn get_defined_struct_by_move(
        &self,
        module_id: &ModuleIdByMove,
        struct_id: &IdentStr,
    ) -> Option<&SymStructInfo<'env>> {
        self.defined_structs_by_move
            .get(module_id)
            .map(|funcs| funcs.get(struct_id))
            .flatten()
            .map(|sym_id| self.defined_structs.get(sym_id).unwrap())
    }

    pub fn get_script_exec_unit(&self) -> &SymFuncInfo<'env> {
        // NOTE: we already checked that the `script_env` has one and only one function and that
        // function is always tracked. So both `unwrap`s are safe here
        self.get_tracked_function_by_spec(
            &self.script_env.get_id(),
            &self.script_env.get_functions().last().unwrap().get_id(),
        )
        .unwrap()
    }

    // misc
    pub fn num_tracked_functions(&self) -> usize {
        self.tracked_functions.len()
    }
}

// prover passes
fn run_prover_passes(global_env: &GlobalEnv) -> FunctionTargetsHolder {
    // build the targets
    let mut targets = FunctionTargetsHolder::default();
    for module_env in global_env.get_modules() {
        for func_env in module_env.get_functions() {
            targets.add_target(&func_env)
        }
    }

    // build the pipeline
    let mut pipeline = FunctionTargetPipeline::default();
    pipeline.add_processor(EliminateImmRefsProcessor::new());
    pipeline.add_processor(EliminateMutRefsProcessor::new());
    pipeline.add_processor(ReachingDefProcessor::new());
    pipeline.add_processor(LiveVarAnalysisProcessor::new());
    pipeline.add_processor(BorrowAnalysisProcessor::new());
    pipeline.add_processor(MemoryInstrumentationProcessor::new());
    pipeline.add_processor(CleanAndOptimizeProcessor::new());

    // run the pipeline
    pipeline.run(global_env, &mut targets, None);

    // done
    targets
}

// no prover passes
fn run_stackless_bytecode_generator(global_env: &GlobalEnv) -> FunctionTargetsHolder {
    let mut targets = BTreeMap::new();
    for module_env in global_env.get_modules() {
        for func_env in module_env.get_functions() {
            let exists = targets.insert(
                func_env.get_qualified_id(),
                StacklessBytecodeGenerator::new(&func_env).generate_function(),
            );
            debug_assert!(exists.is_none());
        }
    }
    FunctionTargetsHolder { targets }
}

// utilities
pub fn get_instruction_defs_and_uses(instruction: &Bytecode) -> (Vec<TempIndex>, Vec<TempIndex>) {
    match instruction {
        Bytecode::Assign(_, dst, src, _) => (vec![*dst], vec![*src]),
        Bytecode::Load(_, dst, _) => (vec![*dst], vec![]),
        Bytecode::Branch(_, _, _, src) => (vec![], vec![*src]),
        Bytecode::Call(_, dsts, op, srcs) => match op {
            Operation::WriteRef => {
                debug_assert_eq!(srcs.len(), 2);
                debug_assert!(dsts.is_empty());
                (vec![srcs[0]], vec![srcs[1]])
            }
            Operation::WriteBack(node) => {
                debug_assert!(dsts.is_empty());
                let uses = srcs.clone();
                match node {
                    BorrowNode::GlobalRoot(..) => (vec![], uses),
                    BorrowNode::LocalRoot(index) | BorrowNode::Reference(index) => {
                        (vec![*index], uses)
                    }
                }
            }
            Operation::Splice(..) => panic!("Unhandled splice case"),
            _ => (dsts.clone(), srcs.clone()),
        },
        Bytecode::Ret(_, srcs) => (vec![], srcs.clone()),
        Bytecode::Abort(_, src) => (vec![], vec![*src]),
        Bytecode::Jump(..) | Bytecode::Label(..) | Bytecode::SpecBlock(..) | Bytecode::Nop(..) => {
            (vec![], vec![])
        }
    }
}
