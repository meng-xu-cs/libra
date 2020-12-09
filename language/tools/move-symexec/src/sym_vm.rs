// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use itertools::Itertools;
use log::{debug, warn};
use std::{collections::HashMap, fmt};

use bytecode::stackless_bytecode::{AssignKind, BorrowNode, Bytecode, Constant, Operation};
use move_core_types::account_address::AccountAddress;
use spec_lang::{
    env::{ModuleId, StructId},
    ty::{PrimitiveType, Type},
};

use crate::{
    sym_exec_graph::{
        ExecBlock, ExecBlockId, ExecFlowType, ExecGraph, ExecSccId, ExecWalker, ExecWalkerStep,
    },
    sym_oracle::{SymFuncInfo, SymOracle},
    sym_smtlib::{SmtCtxt, SmtExpr, SmtKind},
    sym_type_graph::{ExecStructInfo, TypeGraph},
    sym_typing::ExecTypeArg,
    sym_vm_types::{
        SymFrame, SymRefType, SymTransactionArgument, SymValue, ADDRESS_SMT_KIND, SIGNER_SMT_KIND,
    },
};

/// Config: whether to simplify smt expressions upon construction
const CONF_SMT_AUTO_SIMPLIFY: bool = true;

/// An id that uniquely identifies a frame in the VM
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct SymFrameId(usize);

impl fmt::Display for SymFrameId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Holds the states for the VM during the interpretation
struct SymVMState<'smt> {
    /// A collection of all frames created
    frames: HashMap<SymFrameId, SymFrame<'smt>>,
}

impl<'smt> SymVMState<'smt> {
    fn new() -> Self {
        SymVMState {
            frames: HashMap::new(),
        }
    }

    fn add_frame<'env>(&mut self, frame: SymFrame<'smt>) -> SymFrameId {
        let frame_id = SymFrameId(self.frames.len());
        self.frames.insert(frame_id, frame);
        frame_id
    }

    fn get_frame_mut(&mut self, frame_id: SymFrameId) -> &mut SymFrame<'smt> {
        self.frames.get_mut(&frame_id).unwrap()
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct SymIntraSccFlow {
    src_scc_id: ExecSccId,
    src_block_id: ExecBlockId,
    dst_scc_id: ExecSccId,
    dst_block_id: ExecBlockId,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct SymInterSccFlow {
    src_scc_id: ExecSccId,
    src_block_id: ExecBlockId,
    dst_scc_id: ExecSccId,
    dst_block_id: ExecBlockId,
}

#[derive(Clone)]
struct SymFlowInfo<'smt> {
    cond: SmtExpr<'smt>,
    frame_stack: Vec<SymFrameId>,
}

struct SymSccInfo<'smt> {
    /// The scc_id where all scc_ids in the edge_conds resides in
    scc_id: Option<ExecSccId>,
    /// Entry information
    entry_info: SymFlowInfo<'smt>,
    /// Information for flows (i.e., edges) within this scc only
    edge_info: HashMap<SymIntraSccFlow, Option<SymFlowInfo<'smt>>>,
    /// Information for flows (i.e., edges) out of this scc only
    exit_info: HashMap<SymInterSccFlow, Option<SymFlowInfo<'smt>>>,
}

impl<'smt> SymSccInfo<'smt> {
    fn for_base(ctxt: &'smt SmtCtxt, init_frame_id: SymFrameId) -> Self {
        Self {
            scc_id: None,
            entry_info: SymFlowInfo {
                cond: ctxt.bool_const(true),
                frame_stack: vec![init_frame_id],
            },
            edge_info: HashMap::new(),
            exit_info: HashMap::new(),
        }
    }

    fn for_cycle(ctxt: &'smt SmtCtxt, scc_id: ExecSccId) -> Self {
        Self {
            scc_id: Some(scc_id),
            // TODO: this is a fake information
            entry_info: SymFlowInfo {
                cond: ctxt.bool_const(true),
                frame_stack: vec![],
            },
            edge_info: HashMap::new(),
            exit_info: HashMap::new(),
        }
    }

    /// Get the information associated with this intra-scc edge (panic if non-exist)
    fn get_edge_info(
        &self,
        src_scc_id: ExecSccId,
        src_block_id: ExecBlockId,
        dst_scc_id: ExecSccId,
        dst_block_id: ExecBlockId,
    ) -> Option<&SymFlowInfo<'smt>> {
        let key = SymIntraSccFlow {
            src_scc_id,
            src_block_id,
            dst_scc_id,
            dst_block_id,
        };
        self.edge_info.get(&key).unwrap().as_ref()
    }

    /// Put the information associated with this intra-scc edge (panic if exists)
    fn put_edge_info(
        &mut self,
        src_scc_id: ExecSccId,
        src_block_id: ExecBlockId,
        dst_scc_id: ExecSccId,
        dst_block_id: ExecBlockId,
        info: Option<SymFlowInfo<'smt>>,
    ) {
        let key = SymIntraSccFlow {
            src_scc_id,
            src_block_id,
            dst_scc_id,
            dst_block_id,
        };
        let exists = self.edge_info.insert(key, info);
        debug_assert!(exists.is_none());
    }

    /// Put the information associated with this exit edge (panic if exists)
    fn put_exit_info(
        &mut self,
        src_scc_id: ExecSccId,
        src_block_id: ExecBlockId,
        dst_scc_id: ExecSccId,
        dst_block_id: ExecBlockId,
        info: Option<SymFlowInfo<'smt>>,
    ) {
        let key = SymInterSccFlow {
            src_scc_id,
            src_block_id,
            dst_scc_id,
            dst_block_id,
        };
        let exists = self.exit_info.insert(key, info);
        debug_assert!(exists.is_none());
    }

    fn derive_reach_info(
        &self,
        smt_ctxt: &'smt SmtCtxt,
        scc_id: ExecSccId,
        block_id: ExecBlockId,
        incoming_edges: &[(ExecSccId, ExecBlockId)],
    ) -> Option<SymFlowInfo<'smt>> {
        if incoming_edges.is_empty() {
            // this is the entry block of this scc, so just take the scc entry info
            Some(self.entry_info.clone())
        } else {
            let mut derived_cond = smt_ctxt.bool_const(false);
            let mut derived_stack: Option<Vec<_>> = None;
            for (src_scc_id, src_block_id) in incoming_edges.iter() {
                if let Some(edge_info) =
                    self.get_edge_info(*src_scc_id, *src_block_id, scc_id, block_id)
                {
                    // no matter how this block is reached, the frame stack is the same
                    if let Some(stack) = derived_stack.as_ref() {
                        debug_assert_eq!(stack, &edge_info.frame_stack);
                    } else {
                        derived_stack = Some(edge_info.frame_stack.clone());
                    }

                    // unify the reaching conditions
                    derived_cond = derived_cond.or(&edge_info.cond);
                }
            }

            // re-construct the flow info
            derived_stack.map(|frame_stack| SymFlowInfo {
                cond: derived_cond,
                frame_stack,
            })
        }
    }

    fn mark_block_unreachable(
        &mut self,
        scc_id: ExecSccId,
        block_id: ExecBlockId,
        outgoing_edges: &[(ExecSccId, ExecBlockId)],
        scc_exit_edges: &[(ExecSccId, ExecBlockId)],
        _is_a_back_edge: Option<&(ExecSccId, ExecBlockId)>,
    ) {
        for (dst_scc_id, dst_block_id) in outgoing_edges {
            self.put_edge_info(scc_id, block_id, *dst_scc_id, *dst_block_id, None);
        }

        for (dst_scc_id, dst_block_id) in scc_exit_edges {
            self.put_exit_info(scc_id, block_id, *dst_scc_id, *dst_block_id, None);
        }

        // TODO: what about the back edge?
    }
}

/// The reason why this exec block is finished
enum SymBlockTerm<'smt> {
    Normal,
    Ret {
        scc_id: ExecSccId,
        block_id: ExecBlockId,
        call_from_block_id: ExecBlockId,
        return_values: Vec<SymValue<'smt>>,
    },
    Call {
        scc_id: ExecSccId,
        block_id: ExecBlockId,
        frame: SymFrame<'smt>,
    },
}

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM<'env, 'sym> {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
    /// The oracle for environmental information
    oracle: &'env SymOracle<'env>,
    /// The execution graph containing all code
    exec_graph: &'sym ExecGraph<'env>,
    /// Maps all struct types to names of the corresponding smt types
    type_graph: &'sym TypeGraph<'env>,
}

macro_rules! sym_op_unary {
    ($args:ident, $rets:ident, $cond:ident, $frame:ident, $func:tt) => {
        debug_assert_eq!($args.len(), 1);
        debug_assert_eq!($rets.len(), 1);
        debug_assert!(!$frame.is_local_ref($args[0]));
        debug_assert!(!$frame.is_local_ref($rets[0]));
        let sym = $frame.copy_local($args[0], $cond)?;
        $frame.store_local($rets[0], &sym.$func($cond)?, $cond)?;
    };
}

macro_rules! sym_op_binary {
    ($args:ident, $rets:ident, $cond:ident, $frame:ident, $func:tt) => {
        debug_assert_eq!($args.len(), 2);
        debug_assert_eq!($rets.len(), 1);
        debug_assert!(!$frame.is_local_ref($args[0]));
        debug_assert!(!$frame.is_local_ref($args[1]));
        debug_assert!(!$frame.is_local_ref($rets[0]));
        let lhs = $frame.copy_local($args[0], $cond)?;
        let rhs = $frame.copy_local($args[1], $cond)?;
        $frame.store_local($rets[0], &lhs.$func(&rhs, $cond)?, $cond)?;
    };
}

impl<'env, 'sym> SymVM<'env, 'sym> {
    pub fn new(
        oracle: &'env SymOracle<'env>,
        exec_graph: &'sym ExecGraph<'env>,
        type_graph: &'sym TypeGraph<'env>,
    ) -> Self {
        let mut smt_ctxt = SmtCtxt::new(CONF_SMT_AUTO_SIMPLIFY);

        // pre-compute the types for move first class citizens
        smt_ctxt.create_move_type_address();
        smt_ctxt.create_move_type_signer();

        // pre-compute the struct smt types
        for (struct_name, struct_info) in type_graph.reverse_topological_sort() {
            match struct_info {
                ExecStructInfo::Native => {
                    // TODO: we should have a dedicated modeling for native struct types
                    warn!("A native struct type is ignored: {}", struct_name)
                }
                ExecStructInfo::Declared {
                    field_vec,
                    field_map,
                } => {
                    let field_smt_kinds: Vec<(String, SmtKind)> = field_vec
                        .iter()
                        .map(|field_env| {
                            (
                                field_env
                                    .struct_env
                                    .symbol_pool()
                                    .string(field_env.get_name())
                                    .as_str()
                                    .to_owned(),
                                type_arg_to_smt_kind(
                                    field_map.get(&field_env.get_id()).unwrap(),
                                    type_graph,
                                ),
                            )
                        })
                        .collect();
                    smt_ctxt.create_smt_struct(struct_name.to_owned(), field_smt_kinds);
                }
            }
        }

        // done
        Self {
            smt_ctxt,
            oracle,
            exec_graph,
            type_graph,
        }
    }

    fn get_smt_struct_kind(
        &self,
        module_id: &ModuleId,
        struct_id: &StructId,
        type_actuals: &[Type],
        exec_type_args: &[ExecTypeArg<'env>],
    ) -> SmtKind {
        let struct_info = self
            .oracle
            .get_defined_struct_by_spec(module_id, struct_id)
            .unwrap();
        let struct_type_args: Vec<_> = type_actuals
            .iter()
            .map(|type_arg| {
                ExecTypeArg::convert_from_type_actual(type_arg, exec_type_args, self.oracle)
            })
            .collect();

        SmtKind::Struct {
            struct_name: self
                .type_graph
                .get_struct_name(&struct_info.struct_id, &struct_type_args)
                .unwrap()
                .to_owned(),
        }
    }

    fn create_frame<'smt>(
        &'smt self,
        func_info: &'env SymFuncInfo<'env>,
        func_args: &[SymValue<'smt>],
        func_type_args: &[ExecTypeArg<'env>],
        cond: &SmtExpr<'smt>,
    ) -> Result<SymFrame<'smt>> {
        // get information
        let target = func_info.get_target();
        let params = func_info.func_env.get_parameters();
        debug_assert_eq!(func_args.len(), target.get_parameter_count());

        // instantiate local type actuals and collect references
        let local_refs = func_info
            .func_data
            .local_types
            .iter()
            .enumerate()
            .filter_map(|(local_index, local_type)| {
                let exec_type_arg =
                    ExecTypeArg::convert_from_type_actual(local_type, func_type_args, self.oracle);
                if exec_type_arg.is_reference() {
                    Some(local_index)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        // create an empty frame
        let mut frame = SymFrame::new(
            &self.smt_ctxt,
            func_info.func_data.local_types.len(),
            &local_refs,
        );

        // preload args into local slots
        for (i, arg) in func_args.iter().enumerate() {
            debug!("Argument {}", i);
            frame.store_local(
                *target.get_local_index(params.get(i).unwrap().0).unwrap(),
                arg,
                cond,
            )?;
        }

        // done
        Ok(frame)
    }

    pub fn interpret(
        &self,
        sigs_opt: Option<&[AccountAddress]>,
        sym_args: &[SymTransactionArgument],
    ) -> Result<()> {
        // get the script exec unit to kickstart the symbolization
        let script_main = self.oracle.get_script_exec_unit();
        let params = script_main.func_env.get_parameters();

        // turn signers into values
        let mut sym_inputs: Vec<SymValue> = vec![];
        if let Some(signers) = sigs_opt {
            let signer_type =
                Type::Reference(false, Box::new(Type::Primitive(PrimitiveType::Signer)));
            for (i, signer) in signers.iter().enumerate() {
                debug_assert_eq!(params.get(i).unwrap().1, signer_type);
                sym_inputs.push(SymValue::signer_const(
                    &self.smt_ctxt,
                    *signer,
                    &self.smt_ctxt.bool_const(true),
                )?);
            }
        }

        // turn transaction argument into values
        let arg_index_start = sigs_opt.map_or(0, |signers| signers.len());
        for (i, arg) in sym_args.iter().enumerate() {
            sym_inputs.push(SymValue::from_transaction_argument(
                &self.smt_ctxt,
                &params.get(arg_index_start + i).unwrap().1,
                arg,
            )?);
        }

        // create the state
        let mut vm_state = SymVMState::new();

        // prepare the first frame with the input arguments
        let init_frame = self.create_frame(
            script_main,
            &sym_inputs,
            &self.exec_graph.get_entry_block().type_args,
            &self.smt_ctxt.bool_const(true),
        )?;
        let init_frame_id = vm_state.add_frame(init_frame);

        // tracks the sccs that contain cycles only (except the base), and this is by definition,
        // i.e., an scc containing a single block will not be able to form a stack.
        let mut scc_stack = vec![SymSccInfo::for_base(&self.smt_ctxt, init_frame_id)];

        // symbolically walk the exec graph
        let mut walker = ExecWalker::new(self.exec_graph);
        while let Some(walker_step) = walker.next() {
            match walker_step {
                ExecWalkerStep::CycleEntry { scc_id, block_id } => {
                    scc_stack.push(SymSccInfo::for_cycle(&self.smt_ctxt, scc_id));
                }
                ExecWalkerStep::CycleExit { scc_id } => {
                    let exiting_scc_id = scc_stack.pop().unwrap().scc_id.unwrap();
                    debug_assert_eq!(scc_id, exiting_scc_id);
                }
                ExecWalkerStep::Block {
                    scc_id,
                    block_id,
                    incoming_edges,
                    outgoing_edges,
                    scc_exit_edges,
                    is_a_back_edge,
                } => {
                    // log information
                    log_block_info(
                        scc_id,
                        block_id,
                        &incoming_edges,
                        &outgoing_edges,
                        &scc_exit_edges,
                        is_a_back_edge.as_ref(),
                    );

                    // derive the reachability information for this block
                    let mut scc_info = scc_stack.last_mut().unwrap();
                    let reach_info_opt = scc_info.derive_reach_info(
                        &self.smt_ctxt,
                        scc_id,
                        block_id,
                        &incoming_edges,
                    );

                    // if this block is obviously unreachable, shortcut the execution
                    if reach_info_opt.is_none() {
                        debug!("[x] Block is unreachable");
                        scc_info.mark_block_unreachable(
                            scc_id,
                            block_id,
                            &outgoing_edges,
                            &scc_exit_edges,
                            is_a_back_edge.as_ref(),
                        );
                        continue;
                    }

                    let reach_info = reach_info_opt.unwrap();
                    debug!("Reaching condition: {}", reach_info.cond);
                    debug!(
                        "Reaching stack: [{}]",
                        reach_info
                            .frame_stack
                            .iter()
                            .map(|frame_id| frame_id.to_string())
                            .join(", ")
                    );

                    // if this block is not reachable by condition, shortcut the execution
                    if !self
                        .smt_ctxt
                        .is_feasible_assume_solvable(&[&reach_info.cond])?
                    {
                        scc_info.mark_block_unreachable(
                            scc_id,
                            block_id,
                            &outgoing_edges,
                            &scc_exit_edges,
                            is_a_back_edge.as_ref(),
                        );
                        continue;
                    }

                    // now symbolize the block
                    let block = self.exec_graph.get_block_by_block_id(block_id);
                    let current_frame =
                        vm_state.get_frame_mut(*reach_info.frame_stack.last().unwrap());
                    let block_term = self.symbolize_block(
                        scc_id,
                        block,
                        &reach_info,
                        &outgoing_edges,
                        &scc_exit_edges,
                        is_a_back_edge.as_ref(),
                        &mut scc_info,
                        current_frame,
                    )?;

                    // pop the call stack if this is a return block
                    match block_term {
                        SymBlockTerm::Normal => {}
                        SymBlockTerm::Ret {
                            scc_id: dst_scc_id,
                            block_id: dst_block_id,
                            call_from_block_id,
                            return_values,
                        } => {
                            // we guarantee that only function returns show here, script return is
                            // treated as normal. Hence, it must be safe to pop the stack
                            let mut next_frame_stack = reach_info.frame_stack.clone();
                            next_frame_stack.pop().unwrap();

                            // transfer the return value to the parent frame
                            let parent_frame =
                                vm_state.get_frame_mut(*next_frame_stack.last_mut().unwrap());
                            parent_frame.receive_returns(
                                call_from_block_id,
                                &return_values,
                                &reach_info.cond,
                            )?;

                            // tell the dst block that the old frame is gone
                            scc_info.put_edge_info(
                                scc_id,
                                block_id,
                                dst_scc_id,
                                dst_block_id,
                                Some(SymFlowInfo {
                                    cond: reach_info.cond,
                                    frame_stack: next_frame_stack,
                                }),
                            );
                        }
                        SymBlockTerm::Call {
                            scc_id: dst_scc_id,
                            block_id: dst_block_id,
                            frame,
                        } => {
                            let next_frame_id = vm_state.add_frame(frame);
                            let mut next_frame_stack = reach_info.frame_stack.clone();
                            next_frame_stack.push(next_frame_id);

                            // tell the dst block that they have a new frame to use
                            scc_info.put_edge_info(
                                scc_id,
                                block_id,
                                dst_scc_id,
                                dst_block_id,
                                Some(SymFlowInfo {
                                    cond: reach_info.cond,
                                    frame_stack: next_frame_stack,
                                }),
                            );
                        }
                    }
                }
            }
        }

        // we should have nothing left in the stack after execution, except the root scc
        let base_scc = scc_stack.pop().unwrap();
        debug_assert!(base_scc.scc_id.is_none());
        debug_assert!(scc_stack.is_empty());

        // done
        Ok(())
    }

    fn symbolize_block<'smt>(
        &'smt self,
        scc_id: ExecSccId,
        block: &ExecBlock<'env>,
        reach_info: &SymFlowInfo<'smt>,
        outgoing_edges: &[(ExecSccId, ExecBlockId)],
        scc_exit_edges: &[(ExecSccId, ExecBlockId)],
        is_a_back_edge: Option<&(ExecSccId, ExecBlockId)>,
        scc_info: &mut SymSccInfo<'smt>,
        current_frame: &mut SymFrame<'smt>,
    ) -> Result<SymBlockTerm<'smt>> {
        let func_env = block.exec_unit;
        let reach_cond = &reach_info.cond;
        for (pos, instruction) in block.instructions.iter().enumerate() {
            debug!(
                "Instruction {}: {}",
                pos,
                instruction.display(func_env.get_target())
            );
            match instruction {
                Bytecode::Assign(_, dst, src, kind) => {
                    match kind {
                        AssignKind::Move => {
                            debug_assert!(!current_frame.is_local_ref(*src));
                            debug_assert!(!current_frame.is_local_ref(*dst));
                            let sym = current_frame.move_local(*src, reach_cond)?;
                            current_frame.store_local(*dst, &sym, reach_cond)?;
                        }
                        AssignKind::Copy => {
                            debug_assert!(!current_frame.is_local_ref(*src));
                            debug_assert!(!current_frame.is_local_ref(*dst));
                            let sym = current_frame.copy_local(*src, reach_cond)?;
                            current_frame.store_local(*dst, &sym, reach_cond)?;
                        }
                        // TODO: borrow analysis treats Move and Store equally, we did not follow
                        // suite here, the reason can be found in the assign_refs test case
                        AssignKind::Store => {
                            let sym = current_frame.copy_local(*src, reach_cond)?;
                            current_frame.store_local(*dst, &sym, reach_cond)?;

                            // check if we need to transfer the ref as well
                            if current_frame.is_local_ref(*src) {
                                if current_frame.is_local_ref(*dst) {
                                    current_frame.transfer_local_ref(*src, *dst, reach_cond)?;
                                }
                            } else {
                                debug_assert!(!current_frame.is_local_ref(*dst));
                            }
                        }
                    }
                }
                Bytecode::Load(_, dst, val) => {
                    debug_assert!(!current_frame.is_local_ref(*dst));
                    let sym = self.symbolize_constant(val, reach_cond)?;
                    current_frame.store_local(*dst, &sym, reach_cond)?;
                }
                Bytecode::Call(_, rets, op, args) => {
                    match op {
                        // builtins
                        Operation::Destroy => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 0);
                            debug_assert!(!current_frame.is_local_ref(args[0]));
                            current_frame.destroy_local(args[0], reach_cond)?;
                        }
                        // unary
                        Operation::CastU8 => {
                            sym_op_unary!(args, rets, reach_cond, current_frame, cast_u8);
                        }
                        Operation::CastU64 => {
                            sym_op_unary!(args, rets, reach_cond, current_frame, cast_u64);
                        }
                        Operation::CastU128 => {
                            sym_op_unary!(args, rets, reach_cond, current_frame, cast_u128);
                        }
                        Operation::Not => {
                            sym_op_unary!(args, rets, reach_cond, current_frame, not);
                        }
                        // binary
                        Operation::Add => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, add);
                        }
                        Operation::Sub => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, sub);
                        }
                        Operation::Mul => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, mul);
                        }
                        Operation::Div => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, div);
                        }
                        Operation::Mod => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, rem);
                        }
                        Operation::BitOr => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, bit_or);
                        }
                        Operation::BitAnd => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, bit_and);
                        }
                        Operation::Xor => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, bit_xor);
                        }
                        Operation::Shl => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, shl);
                        }
                        Operation::Shr => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, shr);
                        }
                        Operation::Lt => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, lt);
                        }
                        Operation::Gt => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, gt);
                        }
                        Operation::Le => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, le);
                        }
                        Operation::Ge => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, ge);
                        }
                        Operation::Or => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, or);
                        }
                        Operation::And => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, and);
                        }
                        Operation::Eq => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, eq);
                        }
                        Operation::Neq => {
                            sym_op_binary!(args, rets, reach_cond, current_frame, ne);
                        }
                        // struct
                        Operation::Pack(module_id, struct_id, type_actuals) => {
                            debug_assert_eq!(rets.len(), 1);
                            debug_assert!(!args
                                .iter()
                                .any(|index| current_frame.is_local_ref(*index)));
                            debug_assert!(!current_frame.is_local_ref(rets[0]));

                            // get info
                            let struct_kind = self.get_smt_struct_kind(
                                module_id,
                                struct_id,
                                type_actuals,
                                &block.type_args,
                            );
                            let struct_fields = args
                                .iter()
                                .map(|arg_index| current_frame.copy_local(*arg_index, reach_cond))
                                .collect::<Result<Vec<_>>>()?;

                            // build the struct
                            let sym = SymValue::struct_const(
                                &self.smt_ctxt,
                                &struct_kind,
                                &struct_fields.iter().collect::<Vec<_>>(),
                                reach_cond,
                            )?;
                            current_frame.store_local(rets[0], &sym, reach_cond)?;
                        }
                        Operation::Unpack(..) => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert!(!current_frame.is_local_ref(args[0]));
                            debug_assert!(!rets
                                .iter()
                                .any(|index| current_frame.is_local_ref(*index)));

                            // get the struct
                            let sym = current_frame.copy_local(args[0], reach_cond)?;

                            // unpack it
                            let struct_fields = sym.unpack(rets.len(), reach_cond)?;
                            for (dst, field) in rets.iter().zip(struct_fields.iter()) {
                                current_frame.store_local(*dst, field, reach_cond)?;
                            }
                        }
                        Operation::GetField(_, _, _, field_num) => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 1);
                            debug_assert!(!current_frame.is_local_ref(args[0]));
                            debug_assert!(!current_frame.is_local_ref(rets[0]));

                            // get the struct
                            let sym = current_frame.copy_local(args[0], reach_cond)?;

                            // extract the field
                            let field_sym = sym.get_field(*field_num, reach_cond)?;
                            current_frame.store_local(rets[0], &field_sym, reach_cond)?;
                        }
                        // reference
                        Operation::BorrowLoc => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 1);
                            debug_assert!(!current_frame.is_local_ref(args[0]));
                            debug_assert!(current_frame.is_local_ref(rets[0]));

                            // copy the struct as value
                            let sym = current_frame.copy_local(args[0], reach_cond)?;
                            current_frame.store_local(rets[0], &sym, reach_cond)?;

                            // record reference
                            current_frame.record_local_ref(
                                rets[0],
                                &SymRefType::Local {
                                    slot_index: args[0],
                                },
                                reach_cond,
                            )?;
                        }
                        Operation::BorrowField(_, _, _, field_num) => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 1);
                            // TODO: field borrowing must come from a reference?
                            debug_assert!(current_frame.is_local_ref(args[0]));
                            debug_assert!(current_frame.is_local_ref(rets[0]));

                            // copy the field as value
                            let sym = current_frame.copy_local(args[0], reach_cond)?;
                            let field_sym = sym.get_field(*field_num, reach_cond)?;
                            current_frame.store_local(rets[0], &field_sym, reach_cond)?;

                            // record reference
                            current_frame.record_local_ref(
                                rets[0],
                                &SymRefType::Field {
                                    slot_index: args[0],
                                    field_num: *field_num,
                                },
                                reach_cond,
                            )?;
                        }
                        Operation::ReadRef => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 1);
                            debug_assert!(current_frame.is_local_ref(args[0]));
                            debug_assert!(!current_frame.is_local_ref(rets[0]));
                            let sym = current_frame.copy_local(args[0], reach_cond)?;
                            current_frame.store_local(rets[0], &sym, reach_cond)?;
                        }
                        Operation::WriteRef => {
                            debug_assert_eq!(args.len(), 2);
                            debug_assert_eq!(rets.len(), 0);
                            debug_assert!(current_frame.is_local_ref(args[0]));
                            debug_assert!(!current_frame.is_local_ref(args[1]));
                            let sym = current_frame.copy_local(args[1], reach_cond)?;
                            current_frame.store_local(args[0], &sym, reach_cond)?;
                        }
                        Operation::WriteBack(borrow_node) => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 0);
                            debug_assert!(current_frame.is_local_ref(args[0]));
                            match borrow_node {
                                BorrowNode::GlobalRoot(_) => bail!("Globals not supported yet"),
                                BorrowNode::Reference(dst) | BorrowNode::LocalRoot(dst) => {
                                    let guides = current_frame
                                        .select_local_ref(args[0], *dst, reach_cond)?;

                                    let sym = current_frame.copy_local(args[0], reach_cond)?;
                                    for (ref_type, write_cond) in guides {
                                        match ref_type {
                                            SymRefType::Local { slot_index } => current_frame
                                                .store_local(slot_index, &sym, &write_cond)?,
                                            SymRefType::Field {
                                                slot_index,
                                                field_num,
                                            } => {
                                                let struct_old = current_frame
                                                    .copy_local(slot_index, &write_cond)?;
                                                let struct_new = struct_old.put_field(
                                                    &sym,
                                                    field_num,
                                                    &write_cond,
                                                )?;
                                                current_frame.store_local(
                                                    slot_index,
                                                    &struct_new,
                                                    &write_cond,
                                                )?;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        Operation::PackRef => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 0);
                            debug_assert!(current_frame.is_local_ref(args[0]));
                            // TODO: I have no idea what PackRef does..., seems that it always
                            // precedes a WriteBack and does not return anything...
                        }
                        Operation::UnpackRef => {
                            debug_assert_eq!(args.len(), 1);
                            debug_assert_eq!(rets.len(), 0);
                            debug_assert!(current_frame.is_local_ref(args[0]));
                            // TODO: I have no idea what UnpackRef does..., seems that it always
                            // follows a Borrow and does not return anything...
                        }
                        // invoke
                        Operation::Function(module_id, func_id, type_actuals) => {
                            let func_info_opt =
                                self.oracle.get_tracked_function_by_spec(module_id, func_id);

                            // check whether we have the function inlined in the eCFG
                            if let Some(func_info) = func_info_opt {
                                debug_assert_eq!(pos + 1, block.instructions.len());
                                debug_assert_eq!(scc_exit_edges.len(), 0);

                                if let Some((dst_scc_id, dst_block_id)) = is_a_back_edge {
                                    debug_assert_eq!(outgoing_edges.len(), 0);

                                    // check flow type
                                    let flow_type = self
                                        .exec_graph
                                        .get_flow_by_block_ids(block.block_id, *dst_block_id);
                                    debug_assert!(matches!(flow_type, ExecFlowType::CallRecursive));

                                    // TODO: found a back edge
                                    bail!(
                                        "Found a back edge {}::{} -> {}::{}",
                                        scc_id,
                                        block.block_id,
                                        dst_scc_id,
                                        dst_block_id
                                    );
                                } else {
                                    debug_assert_eq!(outgoing_edges.len(), 1);

                                    // check flow type
                                    let (dst_scc_id, dst_block_id) =
                                        outgoing_edges.first().unwrap();
                                    let flow_type = self
                                        .exec_graph
                                        .get_flow_by_block_ids(block.block_id, *dst_block_id);
                                    debug_assert!(matches!(flow_type, ExecFlowType::Call));

                                    // register the return slots
                                    current_frame.set_receive(block.block_id, rets);

                                    // create the frame for this call
                                    let func_sym_args = args
                                        .iter()
                                        .map(|arg_index| {
                                            current_frame.copy_local(*arg_index, reach_cond)
                                        })
                                        .collect::<Result<Vec<_>>>()?;

                                    let func_type_args: Vec<_> = type_actuals
                                        .iter()
                                        .map(|actual| {
                                            ExecTypeArg::convert_from_type_actual(
                                                actual,
                                                &block.type_args,
                                                self.oracle,
                                            )
                                        })
                                        .collect();

                                    let frame = self.create_frame(
                                        func_info,
                                        &func_sym_args,
                                        &func_type_args,
                                        reach_cond,
                                    )?;

                                    // mark that this block is a call block
                                    return Ok(SymBlockTerm::Call {
                                        scc_id: *dst_scc_id,
                                        block_id: *dst_block_id,
                                        frame,
                                    });
                                }
                            } else {
                                // for system functions, this call must not be the lost instruction
                                // of this exec block (in stackless control-flow graph)
                                debug_assert_ne!(pos + 1, block.instructions.len());
                                bail!("System functions not supported yet");
                            }
                        }
                        // others
                        _ => bail!("Operation not supported yet"),
                    }
                }
                Bytecode::Ret(_, rets) => {
                    debug_assert_eq!(pos + 1, block.instructions.len());
                    debug_assert_eq!(scc_exit_edges.len(), 0);
                    debug_assert!(is_a_back_edge.is_none());
                    if block.exec_unit.is_script_main() {
                        debug_assert_eq!(outgoing_edges.len(), 0);

                        // extra assertion since this is the script return
                        debug_assert_eq!(rets.len(), 0);
                        debug_assert_eq!(reach_info.frame_stack.len(), 1);
                        return Ok(SymBlockTerm::Normal);
                    }
                    debug_assert_eq!(outgoing_edges.len(), 1);

                    // check flow type
                    let (dst_scc_id, dst_block_id) = outgoing_edges.first().unwrap();
                    let flow_type = self
                        .exec_graph
                        .get_flow_by_block_ids(block.block_id, *dst_block_id);
                    let call_from_block_id = match flow_type {
                        ExecFlowType::Ret(block_id) => block_id,
                        _ => panic!("Invalid flow type for return instructions"),
                    };

                    // collect return values
                    let sym_rets = rets
                        .iter()
                        .map(|ret_index| current_frame.copy_local(*ret_index, reach_cond))
                        .collect::<Result<Vec<_>>>()?;

                    // mark that this block is a return block
                    return Ok(SymBlockTerm::Ret {
                        scc_id: *dst_scc_id,
                        block_id: *dst_block_id,
                        call_from_block_id,
                        return_values: sym_rets,
                    });
                }
                Bytecode::Branch(_, _, _, idx) => {
                    debug_assert!(!current_frame.is_local_ref(*idx));
                    debug_assert_eq!(pos + 1, block.instructions.len());
                    debug_assert_eq!(outgoing_edges.len() + scc_exit_edges.len(), 2);
                    debug_assert!(is_a_back_edge.is_none());

                    let sym = current_frame.copy_local(*idx, reach_cond)?;
                    let cond_t = sym.flatten_as_predicate(true).and(reach_cond);
                    let cond_f = sym.flatten_as_predicate(false).and(reach_cond);

                    // add conditions for outgoing edges
                    for (dst_scc_id, dst_block_id) in outgoing_edges {
                        let flow_type = self
                            .exec_graph
                            .get_flow_by_block_ids(block.block_id, *dst_block_id);

                        match flow_type {
                            ExecFlowType::Branch(Some(true)) => scc_info.put_edge_info(
                                scc_id,
                                block.block_id,
                                *dst_scc_id,
                                *dst_block_id,
                                Some(SymFlowInfo {
                                    cond: cond_t.clone(),
                                    frame_stack: reach_info.frame_stack.clone(),
                                }),
                            ),
                            ExecFlowType::Branch(Some(false)) => scc_info.put_edge_info(
                                scc_id,
                                block.block_id,
                                *dst_scc_id,
                                *dst_block_id,
                                Some(SymFlowInfo {
                                    cond: cond_f.clone(),
                                    frame_stack: reach_info.frame_stack.clone(),
                                }),
                            ),
                            _ => panic!(
                                "Invalid flow type for outgoing edges with Branch instruction"
                            ),
                        }
                    }

                    // add conditions for scc-exiting edges
                    for (dst_scc_id, dst_block_id) in scc_exit_edges {
                        let flow_type = self
                            .exec_graph
                            .get_flow_by_block_ids(block.block_id, *dst_block_id);

                        match flow_type {
                            ExecFlowType::Branch(Some(true)) => scc_info.put_exit_info(
                                scc_id,
                                block.block_id,
                                *dst_scc_id,
                                *dst_block_id,
                                Some(SymFlowInfo {
                                    cond: cond_f.clone(),
                                    frame_stack: reach_info.frame_stack.clone(),
                                }),
                            ),
                            ExecFlowType::Branch(Some(false)) => scc_info.put_exit_info(
                                scc_id,
                                block.block_id,
                                *dst_scc_id,
                                *dst_block_id,
                                Some(SymFlowInfo {
                                    cond: cond_f.clone(),
                                    frame_stack: reach_info.frame_stack.clone(),
                                }),
                            ),
                            _ => panic!(
                                "Invalid flow type for scc-exit edges with Branch instruction"
                            ),
                        }
                    }
                }
                Bytecode::Jump(..) => {
                    debug_assert_eq!(pos + 1, block.instructions.len());
                    debug_assert_eq!(scc_exit_edges.len(), 0);
                    if let Some((dst_scc_id, dst_block_id)) = is_a_back_edge {
                        // check flow type
                        let flow_type = self
                            .exec_graph
                            .get_flow_by_block_ids(block.block_id, *dst_block_id);
                        debug_assert!(matches!(flow_type, ExecFlowType::Branch(None)));

                        // TODO: found a back edge
                        bail!(
                            "Found a back edge {}::{} -> {}::{}",
                            scc_id,
                            block.block_id,
                            dst_scc_id,
                            dst_block_id
                        );
                    } else {
                        debug_assert_eq!(outgoing_edges.len(), 1);
                        for (dst_scc_id, dst_block_id) in outgoing_edges {
                            // check flow type
                            let flow_type = self
                                .exec_graph
                                .get_flow_by_block_ids(block.block_id, *dst_block_id);
                            debug_assert!(matches!(flow_type, ExecFlowType::Branch(None)));

                            scc_info.put_edge_info(
                                scc_id,
                                block.block_id,
                                *dst_scc_id,
                                *dst_block_id,
                                Some(SymFlowInfo {
                                    cond: reach_cond.clone(),
                                    frame_stack: reach_info.frame_stack.clone(),
                                }),
                            );
                        }
                    }
                }
                Bytecode::Abort(..) => {
                    debug_assert_eq!(pos + 1, block.instructions.len());
                    debug_assert_eq!(outgoing_edges.len(), 0);
                    debug_assert_eq!(scc_exit_edges.len(), 0);
                    // TODO: solve for reachable inputs
                }
                // nop or equivalent
                Bytecode::Label(..) | Bytecode::SpecBlock(..) | Bytecode::Nop(..) => {}
            };
        }

        // the block is not a return block
        Ok(SymBlockTerm::Normal)
    }

    fn symbolize_constant<'smt>(
        &'smt self,
        val: &Constant,
        cond: &SmtExpr<'smt>,
    ) -> Result<SymValue<'smt>> {
        match val {
            Constant::Bool(v) => SymValue::bool_const(&self.smt_ctxt, *v, cond),
            Constant::U8(v) => SymValue::u8_const(&self.smt_ctxt, *v, cond),
            Constant::U64(v) => SymValue::u64_const(&self.smt_ctxt, *v, cond),
            Constant::U128(v) => SymValue::u128_const(&self.smt_ctxt, *v, cond),
            Constant::Address(v) => SymValue::address_const(
                &self.smt_ctxt,
                AccountAddress::from_hex_literal(&format!("{:#X}", v)).unwrap(),
                cond,
            ),
            Constant::ByteArray(v) => SymValue::vector_u8_const(&self.smt_ctxt, v.clone(), cond),
        }
    }
}

// utilities
fn log_block_info(
    scc_id: ExecSccId,
    block_id: ExecBlockId,
    incoming_edges: &[(ExecSccId, ExecBlockId)],
    outgoing_edges: &[(ExecSccId, ExecBlockId)],
    scc_exit_edges: &[(ExecSccId, ExecBlockId)],
    is_a_back_edge: Option<&(ExecSccId, ExecBlockId)>,
) {
    // log information
    debug!("Block: {} (scc: {})", block_id, scc_id);
    debug!(
        "Incoming edges: [{}]",
        incoming_edges
            .iter()
            .map(|(edge_scc_id, edge_block_id)| format!("{}::{}", edge_scc_id, edge_block_id))
            .join("-")
    );
    debug!(
        "Outgoing edges: [{}]",
        outgoing_edges
            .iter()
            .map(|(edge_scc_id, edge_block_id)| format!("{}::{}", edge_scc_id, edge_block_id))
            .join("-")
    );
    debug!(
        "Scc-exit edges: [{}]",
        scc_exit_edges
            .iter()
            .map(|(edge_scc_id, edge_block_id)| format!("{}::{}", edge_scc_id, edge_block_id))
            .join("-")
    );
    debug!(
        "Back edge: {}",
        is_a_back_edge.map_or("X".to_owned(), |(edge_scc_id, edge_block_id)| {
            format!("{}::{}", edge_scc_id, edge_block_id)
        })
    );
}

fn type_arg_to_smt_kind(type_arg: &ExecTypeArg, type_graph: &TypeGraph) -> SmtKind {
    match type_arg {
        ExecTypeArg::Bool => SmtKind::Bool,
        ExecTypeArg::U8 => SmtKind::bitvec_u8(),
        ExecTypeArg::U64 => SmtKind::bitvec_u64(),
        ExecTypeArg::U128 => SmtKind::bitvec_u128(),
        ExecTypeArg::Address => ADDRESS_SMT_KIND.clone(),
        ExecTypeArg::Signer => SIGNER_SMT_KIND.clone(),
        ExecTypeArg::Vector { element_type } => SmtKind::Vector {
            element_kind: Box::new(type_arg_to_smt_kind(element_type.as_ref(), type_graph)),
        },
        ExecTypeArg::Struct {
            struct_info,
            type_args,
        } => SmtKind::Struct {
            struct_name: type_graph
                .get_struct_name(&struct_info.struct_id, type_args)
                .unwrap()
                .to_owned(),
        },
        ExecTypeArg::Reference { referred_type, .. } => SmtKind::Reference {
            referred_kind: Box::new(type_arg_to_smt_kind(referred_type.as_ref(), type_graph)),
        },
        ExecTypeArg::TypeParameter { actual_type, .. } => {
            type_arg_to_smt_kind(actual_type.as_ref(), type_graph)
        }
    }
}
