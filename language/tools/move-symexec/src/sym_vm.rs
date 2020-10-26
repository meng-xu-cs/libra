// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::collections::HashSet;

use move_core_types::account_address::AccountAddress;
use vm::file_format::{Signature, SignatureToken};

use crate::{
    sym_exec_graph::{ExecGraph, ExecWalker},
    sym_smtlib::SmtCtxt,
    sym_vm_types::SymTransactionArgument,
};

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
    /// A map from variable names to exprs
    vars_set: HashSet<String>,
}

impl SymVM {
    pub fn new() -> Self {
        Self {
            smt_ctxt: SmtCtxt::new(),
            vars_set: HashSet::new(),
        }
    }

    pub fn interpret(
        &self,
        exec_graph: &ExecGraph,
        val_arg_sigs: &Signature,
        signers: &[AccountAddress],
        sym_val_args: &[SymTransactionArgument],
    ) {
        // check that we got the correct number of value arguments
        // NOTE: signers must come before value arguments, if present
        // in the signature
        let use_signers = !val_arg_sigs.is_empty()
            && match val_arg_sigs.0.get(0).unwrap() {
                SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                _ => false,
            };

        debug_assert_eq!(
            val_arg_sigs.len(),
            if use_signers { signers.len() } else { 0 } + sym_val_args.len()
        );

        if use_signers {
            let num_signers = signers.len();
            debug_assert_ne!(num_signers, 0);
            debug_assert!(
                (1..num_signers).all(|i| match val_arg_sigs.0.get(i).unwrap() {
                    SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                    _ => false,
                })
            );
        }

        // run the walker
        let mut walker = ExecWalker::new(exec_graph);
        while walker.next().is_some() {}
    }
}
