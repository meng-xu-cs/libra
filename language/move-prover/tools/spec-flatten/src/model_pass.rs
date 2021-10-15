// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::str::FromStr;

/// Available passes to run after tbe movel-model is built, but before the bytecode pipeline is run
#[derive(Clone, Debug)]
pub enum ModelPass {
    Inline,
}

impl FromStr for ModelPass {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let r = match s {
            "inline" => ModelPass::Inline,
            _ => return Err(s.to_string()),
        };
        Ok(r)
    }
}
