// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! The type system in move-model is a fat type system designed to cover all cases that can possibly
//! appear in the whole bytecode transformation/instrumentation pipeline. Naturally, this means that
//! some types are no longer applicable when the Move program reaches the end of the transformation.
//!
//! The type system for the interpreter is a strict subset of what is offered in the move-model.
//! In other word, it is slimmed down version of the type system in move-model and a very restricted
//! set of types that are only applicable to the interpreter. Doing so enables us to write code in a
//! more precise way. For example, a type argument can only be a `BaseType` and never a reference.
//! Therefore, `BaseType` is preferred over `Type` for if a struct field/function argument holds
//! a type argument (e.g., `struct FunctionContext {ty_args: Vec<BaseType>, ...}` is preferred over
//! `ty_args: Vec<Type>`, as the former is more descriptive and less error prone).

use std::fmt;

use bytecode::stackless_bytecode::Constant;
use move_binary_format::file_format::{Ability, AbilitySet, CodeOffset, TypeParameterIndex};
use move_core_types::{
    identifier::Identifier,
    language_storage::{StructTag, TypeTag},
    value::{MoveStructLayout, MoveTypeLayout},
};
use move_model::{
    model::{GlobalEnv, ModuleId, StructId},
    ty as MT,
};

use crate::{
    shared::ident::StructIdent,
    symbolic::errors::{ExecError, ExecResult},
};

//**************************************************************************************************
// Type system
//**************************************************************************************************

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum IntType {
    Num,
    U8,
    U64,
    U128,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum PrimitiveType {
    Bool,
    Int(IntType),
    Address,
    Signer,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct StructField {
    pub name: String,
    pub ty: BaseType,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct StructInstantiation {
    pub ident: StructIdent,
    pub insts: Vec<BaseType>,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct ParameterInfo {
    pub index: TypeParameterIndex,
    pub name: String,
    pub abilities: AbilitySet,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum BaseType {
    Primitive(PrimitiveType),
    Vector(Box<BaseType>),
    Struct(StructInstantiation),
    Parameter(ParameterInfo),
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum Type {
    Base(BaseType),
    Reference(BaseType),
}

//**************************************************************************************************
// Display
//**************************************************************************************************

impl fmt::Display for IntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let repr = match self {
            Self::Num => "num",
            Self::U8 => "u8",
            Self::U64 => "u64",
            Self::U128 => "u128",
        };
        f.write_str(repr)
    }
}

impl fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "bool"),
            Self::Int(sub) => sub.fmt(f),
            Self::Address => write!(f, "address"),
            Self::Signer => write!(f, "signer"),
        }
    }
}

impl fmt::Display for StructInstantiation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inst_tokens: Vec<_> = self.insts.iter().map(|t| t.to_string()).collect();
        let field_tokens: Vec<_> = self
            .fields
            .iter()
            .map(|f| format!("{}: {}", f.name, f.ty))
            .collect();
        write!(
            f,
            "struct {}<{}> {{{}}}",
            self.ident,
            inst_tokens.join(", "),
            field_tokens.join(",")
        )
    }
}

impl fmt::Display for ParameterInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut abs = vec![];
        for ab in AbilitySet::ALL {
            if self.abilities.has_ability(ab) {
                let token = match ab {
                    Ability::Copy => "copy",
                    Ability::Drop => "drop",
                    Ability::Store => "store",
                    Ability::Key => "key",
                };
                abs.push(token);
            }
        }
        write!(f, "#{}-{}", self.index, self.name)?;
        if abs.is_empty() {
            Ok(())
        } else {
            write!(f, ": {}", abs.join(", "))
        }
    }
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Primitive(sub) => sub.fmt(f),
            Self::Vector(sub) => write!(f, "vector<{}>", sub),
            Self::Struct(inst) => inst.fmt(f),
            Self::Parameter(param) => param.fmt(f),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Base(sub) => sub.fmt(f),
            Self::Reference(sub) => write!(f, "&mut {}", sub),
        }
    }
}

//**************************************************************************************************
// Implementation
//**************************************************************************************************

impl BaseType {
    //
    // factory
    //

    pub fn mk_bool() -> Self {
        BaseType::Primitive(PrimitiveType::Bool)
    }

    pub fn mk_u8() -> Self {
        BaseType::Primitive(PrimitiveType::Int(IntType::U8))
    }

    pub fn mk_u64() -> Self {
        BaseType::Primitive(PrimitiveType::Int(IntType::U64))
    }

    pub fn mk_u128() -> Self {
        BaseType::Primitive(PrimitiveType::Int(IntType::U128))
    }

    pub fn mk_num() -> Self {
        BaseType::Primitive(PrimitiveType::Int(IntType::Num))
    }

    pub fn mk_address() -> Self {
        BaseType::Primitive(PrimitiveType::Address)
    }

    pub fn mk_signer() -> Self {
        BaseType::Primitive(PrimitiveType::Signer)
    }

    pub fn mk_vector(elem: BaseType) -> Self {
        BaseType::Vector(Box::new(elem))
    }

    pub fn mk_struct(inst: StructInstantiation) -> Self {
        BaseType::Struct(inst)
    }

    pub fn mk_parameter(info: ParameterInfo) -> Self {
        BaseType::Parameter(info)
    }

    pub fn into_ref_type(self) -> Type {
        Type::Reference(self)
    }

    //
    // helpers
    //

    pub fn is_bool(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Bool))
    }

    pub fn is_u8(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Int(IntType::U8)))
    }

    pub fn is_u64(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Int(IntType::U64)))
    }

    pub fn is_u128(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Int(IntType::U128)))
    }

    pub fn is_num(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Int(IntType::Num)))
    }

    pub fn is_int(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Int(_)))
    }

    pub fn is_address(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Address))
    }

    pub fn is_signer(&self) -> bool {
        matches!(self, BaseType::Primitive(PrimitiveType::Signer))
    }

    pub fn is_vector(&self) -> bool {
        matches!(self, BaseType::Vector(_))
    }

    pub fn is_struct(&self) -> bool {
        matches!(self, BaseType::Struct(_))
    }

    pub fn is_parameter(&self) -> bool {
        matches!(self, BaseType::Parameter(_))
    }

    pub fn get_vector_elem(&self) -> ExecResult<&BaseType> {
        match self {
            BaseType::Vector(elem) => Ok(elem.as_ref()),
            _ => Err(ExecError::type_error_expect_vector(self)),
        }
    }

    pub fn get_struct_inst(&self) -> ExecResult<&StructInstantiation> {
        match self {
            BaseType::Struct(inst) => Ok(inst),
            _ => Err(ExecError::type_error_expect_struct(self)),
        }
    }

    pub fn get_parameter_info(&self) -> ExecResult<&ParameterInfo> {
        match self {
            BaseType::Parameter(info) => Ok(info),
            _ => Err(ExecError::type_error_expect_parameter(self)),
        }
    }

    pub fn into_vector_elem(self) -> ExecResult<BaseType> {
        match self {
            BaseType::Vector(elem_ty) => Ok(*elem_ty),
            _ => Err(ExecError::type_error_expect_vector(&self)),
        }
    }

    pub fn into_struct_inst(self) -> ExecResult<StructInstantiation> {
        match self {
            BaseType::Struct(inst) => Ok(inst),
            _ => Err(ExecError::type_error_expect_struct(&self)),
        }
    }

    pub fn into_parameter_info(self) -> ExecResult<ParameterInfo> {
        match self {
            BaseType::Parameter(info) => Ok(info),
            _ => Err(ExecError::type_error_expect_parameter(&self)),
        }
    }

    pub fn is_vector_of(&self, elem: &BaseType) -> bool {
        self.get_vector_elem().map_or(false, |t| t == elem)
    }

    pub fn is_struct_of(&self, inst: &StructInstantiation) -> bool {
        self.get_struct_inst().map_or(false, |t| t == inst)
    }

    pub fn is_parameter_of(&self, info: &ParameterInfo) -> bool {
        self.get_parameter_info().map_or(false, |t| t == info)
    }

    //
    // checking
    //

    pub fn is_compatible_for_assign(&self, other: &BaseType) -> bool {
        match (self, other) {
            (
                BaseType::Primitive(PrimitiveType::Int(IntType::Num)),
                BaseType::Primitive(PrimitiveType::Int(_)),
            ) => true,
            (
                BaseType::Primitive(PrimitiveType::Int(_)),
                BaseType::Primitive(PrimitiveType::Int(IntType::Num)),
            ) => true,
            _ => self == other,
        }
    }

    pub fn is_compatible_for_equality(&self, other: &BaseType) -> bool {
        self.is_compatible_for_assign(other)
    }

    pub fn is_compatible_for_comparison(&self, other: &BaseType) -> bool {
        self.is_int() && self.is_compatible_for_assign(other)
    }

    pub fn is_compatible_for_arithmetic(&self, lhs: &BaseType, rhs: &BaseType) -> bool {
        self.is_int()
            && self.is_compatible_for_assign(lhs)
            && self.is_compatible_for_assign(rhs)
            && lhs.is_compatible_for_assign(rhs)
    }

    pub fn is_compatible_for_bitwise(&self, lhs: &BaseType, rhs: &BaseType) -> bool {
        match (self, lhs, rhs) {
            (BaseType::Primitive(PrimitiveType::Int(IntType::Num)), _, _) => false,
            (
                BaseType::Primitive(PrimitiveType::Int(self_ty)),
                BaseType::Primitive(PrimitiveType::Int(lhs_ty)),
                BaseType::Primitive(PrimitiveType::Int(rhs_ty)),
            ) => self_ty == lhs_ty && self_ty == rhs_ty,
            _ => false,
        }
    }

    pub fn is_compatible_for_bitshift(&self, lhs: &BaseType, rhs: &BaseType) -> bool {
        match (self, lhs, rhs) {
            (BaseType::Primitive(PrimitiveType::Int(IntType::Num)), _, _) => false,
            (
                BaseType::Primitive(PrimitiveType::Int(self_ty)),
                BaseType::Primitive(PrimitiveType::Int(lhs_ty)),
                BaseType::Primitive(PrimitiveType::Int(IntType::U8)),
            ) => self_ty == lhs_ty,
            _ => false,
        }
    }

    pub fn is_compatible_for_constant(&self, value: &Constant) -> bool {
        match (self, value) {
            (BaseType::Primitive(PrimitiveType::Bool), Constant::Bool(_)) => true,
            (BaseType::Primitive(PrimitiveType::Int(IntType::U8)), Constant::U8(_)) => true,
            (BaseType::Primitive(PrimitiveType::Int(IntType::U64)), Constant::U64(_)) => true,
            (BaseType::Primitive(PrimitiveType::Int(IntType::U128)), Constant::U128(_)) => true,
            (BaseType::Primitive(PrimitiveType::Int(IntType::Num)), Constant::U8(_)) => true,
            (BaseType::Primitive(PrimitiveType::Int(IntType::Num)), Constant::U64(_)) => true,
            (BaseType::Primitive(PrimitiveType::Int(IntType::Num)), Constant::U128(_)) => true,
            (BaseType::Primitive(PrimitiveType::Address), Constant::Address(_)) => true,
            (BaseType::Vector(elem_ty), Constant::ByteArray(_)) => elem_ty.is_u8(),
            _ => false,
        }
    }
}

macro_rules! gen {
    (
        $mk_base:ident, $mk_ref:ident,
        $is_base:ident, $is_ref:ident
    ) => {
        pub fn $mk_base() -> Self {
            Self::Base(BaseType::$mk_base())
        }
        pub fn $mk_ref() -> Self {
            Self::Reference(BaseType::$mk_base())
        }

        pub fn $is_base(&self) -> bool {
            self.get_base_type().map_or(false, |t| t.$is_base())
        }
        pub fn $is_ref(&self) -> bool {
            self.get_ref_type().map_or(false, |t| t.$is_base())
        }
    };
    (
        $mk_base:ident, $mk_ref:ident,
        $is_base:ident, $is_ref:ident,
        $p:ident, $t:ty,
        $get_base_p:ident, $get_ref_p:ident,
        $into_base_p:ident, $into_ref_p:ident,
        $is_base_of:ident, $is_ref_of:ident
    ) => {
        pub fn $mk_base($p: $t) -> Self {
            Self::Base(BaseType::$mk_base($p))
        }
        pub fn $mk_ref($p: $t) -> Self {
            Self::Reference(BaseType::$mk_base($p))
        }

        pub fn $is_base(&self) -> bool {
            self.get_base_type().map_or(false, |t| t.$is_base())
        }
        pub fn $is_ref(&self) -> bool {
            self.get_ref_type().map_or(false, |t| t.$is_base())
        }

        pub fn $get_base_p(&self) -> ExecResult<&$t> {
            self.get_base_type()?.$get_base_p()
        }
        pub fn $get_ref_p(&self) -> ExecResult<&$t> {
            self.get_ref_type()?.$get_base_p()
        }

        pub fn $into_base_p(self) -> ExecResult<$t> {
            self.into_base_type()?.$into_base_p()
        }
        pub fn $into_ref_p(self) -> ExecResult<$t> {
            self.into_ref_type()?.$into_base_p()
        }

        pub fn $is_base_of(&self, $p: &$t) -> bool {
            self.get_base_type().map_or(false, |t| t.$is_base_of($p))
        }
        pub fn $is_ref_of(&self, $p: &$t) -> bool {
            self.get_ref_type().map_or(false, |t| t.$is_base_of($p))
        }
    };
}

impl Type {
    //
    // factory
    //

    gen!(mk_bool, mk_ref_bool, is_bool, is_ref_bool);
    gen!(mk_u8, mk_ref_u8, is_u8, is_ref_u8);
    gen!(mk_u64, mk_ref_u64, is_u64, is_ref_u64);
    gen!(mk_u128, mk_ref_u128, is_u128, is_ref_u128);
    gen!(mk_num, mk_ref_num, is_num, is_ref_num);
    gen!(mk_address, mk_ref_address, is_address, is_ref_address);
    gen!(mk_signer, mk_ref_signer, is_signer, is_ref_signer);
    gen!(
        mk_vector,
        mk_ref_vector,
        is_vector,
        is_ref_vector,
        elem,
        BaseType,
        get_vector_elem,
        get_ref_vector_elem,
        into_vector_elem,
        into_ref_vector_elem,
        is_vector_of,
        is_ref_vector_of
    );
    gen!(
        mk_struct,
        mk_ref_struct,
        is_struct,
        is_ref_struct,
        inst,
        StructInstantiation,
        get_struct_inst,
        get_ref_struct_inst,
        into_struct_inst,
        into_ref_struct_inst,
        is_struct_of,
        is_ref_struct_of
    );
    gen!(
        mk_parameter,
        mk_ref_parameter,
        is_parameter,
        is_ref_parameter,
        info,
        ParameterInfo,
        get_parameter_info,
        get_ref_parameter_info,
        into_parameter_info,
        into_ref_parameter_info,
        is_parameter_of,
        is_ref_parameter_of
    );

    //
    // helpers
    //

    pub fn is_base(&self) -> bool {
        matches!(self, Type::Base(_))
    }

    pub fn is_ref(&self) -> bool {
        matches!(self, Type::Reference(_))
    }

    pub fn get_base_type(&self) -> ExecResult<&BaseType> {
        match self {
            Type::Base(base_ty) => Ok(base_ty),
            _ => Err(ExecError::type_error_expect_base(self)),
        }
    }

    pub fn get_ref_type(&self) -> ExecResult<&BaseType> {
        match self {
            Type::Reference(base_ty) => Ok(base_ty),
            _ => Err(ExecError::type_error_expect_reference(self)),
        }
    }

    pub fn into_base_type(self) -> ExecResult<BaseType> {
        match self {
            Type::Base(base_ty) => Ok(base_ty),
            _ => Err(ExecError::type_error_expect_base(&self)),
        }
    }

    pub fn into_ref_type(self) -> ExecResult<BaseType> {
        match self {
            Type::Reference(base_ty) => Ok(base_ty),
            _ => Err(ExecError::type_error_expect_reference(&self)),
        }
    }

    pub fn is_base_of(&self, ty: &BaseType) -> bool {
        self.get_base_type().map_or(false, |t| t == ty)
    }

    pub fn is_ref_of(&self, ty: &BaseType) -> bool {
        self.get_ref_type().map_or(false, |t| t == ty)
    }

    pub fn is_int(&self) -> bool {
        self.get_base_type().map_or(false, |t| t.is_int())
    }

    pub fn is_ref_int(&self) -> bool {
        self.get_ref_type().map_or(false, |t| t.is_int())
    }

    //
    // checking
    //

    pub fn is_compatible_for_assign(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Base(base_ty_1), Type::Base(base_ty_2)) => {
                base_ty_1.is_compatible_for_assign(base_ty_2)
            }
            (Type::Reference(base_ty_1), Type::Reference(base_ty_2)) => {
                base_ty_1.is_compatible_for_assign(base_ty_2)
            }
            _ => false,
        }
    }

    pub fn is_compatible_for_equality(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Base(base_ty_1), Type::Base(base_ty_2)) => {
                base_ty_1.is_compatible_for_equality(base_ty_2)
            }
            (Type::Reference(base_ty_1), Type::Reference(base_ty_2)) => {
                base_ty_1.is_compatible_for_equality(base_ty_2)
            }
            _ => false,
        }
    }

    pub fn is_compatible_for_comparison(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Base(self_ty), Type::Base(other_ty)) => {
                self_ty.is_compatible_for_comparison(other_ty)
            }
            _ => false,
        }
    }

    pub fn is_compatible_for_arithmetic(&self, lhs: &Type, rhs: &Type) -> bool {
        match (self, lhs, rhs) {
            (Type::Base(self_ty), Type::Base(lhs_ty), Type::Base(rhs_ty)) => {
                self_ty.is_compatible_for_arithmetic(lhs_ty, rhs_ty)
            }
            _ => false,
        }
    }

    pub fn is_compatible_for_bitwise(&self, lhs: &Type, rhs: &Type) -> bool {
        match (self, lhs, rhs) {
            (Type::Base(self_ty), Type::Base(lhs_ty), Type::Base(rhs_ty)) => {
                self_ty.is_compatible_for_bitwise(lhs_ty, rhs_ty)
            }
            _ => false,
        }
    }

    pub fn is_compatible_for_bitshift(&self, lhs: &Type, rhs: &Type) -> bool {
        match (self, lhs, rhs) {
            (Type::Base(self_ty), Type::Base(lhs_ty), Type::Base(rhs_ty)) => {
                self_ty.is_compatible_for_bitshift(lhs_ty, rhs_ty)
            }
            _ => false,
        }
    }

    pub fn is_compatible_for_constant(&self, value: &Constant) -> bool {
        match self {
            Type::Base(base_ty) => base_ty.is_compatible_for_constant(value),
            _ => false,
        }
    }

    pub fn is_compatible_for_abort_code(&self) -> bool {
        self.is_u64() || self.is_num()
    }
}
