// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

use crate::symbolic::ty::{BaseType, Type};

#[repr(u64)]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
enum ExecErrorCode {
    TYPE_ERROR = 1,
}

impl fmt::Display for ExecErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TYPE_ERROR => write!(f, "type error"),
        }
    }
}

pub struct ExecError {
    code: ExecErrorCode,
    message: String,
}

impl ExecError {
    //
    // type errors
    //

    fn type_error<T1: AsRef<str>, T2: AsRef<str>>(expect: T1, actual: T2) -> Self {
        Self {
            code: ExecErrorCode::TYPE_ERROR,
            message: format!("expecting '{}', got '{}'", expect.as_ref(), actual.as_ref()),
        }
    }

    pub fn type_error_expect_vector(ty: &BaseType) -> Self {
        Self::type_error("vector", ty.to_string())
    }

    pub fn type_error_expect_struct(ty: &BaseType) -> Self {
        Self::type_error("struct", ty.to_string())
    }

    pub fn type_error_expect_parameter(ty: &BaseType) -> Self {
        Self::type_error("parameter", ty.to_string())
    }

    pub fn type_error_expect_base(ty: &Type) -> Self {
        Self::type_error("base", ty.to_string())
    }

    pub fn type_error_expect_reference(ty: &Type) -> Self {
        Self::type_error("reference", ty.to_string())
    }
}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} - {}", self.code, self.message)
    }
}

pub type ExecResult<T> = ::std::result::Result<T, ExecError>;
