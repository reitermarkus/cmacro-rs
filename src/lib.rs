//! A library for parsing C macros.
//!
//! This crate allows parsing C macros and converting them to Rust code.
//!
//! Both function-like macros (e.g. `#define FUNC(a, b, c) a + b * c`) as well
//! as variable-like macros (e.g. `#define VAR 4 + 7 * 82`) are supported.
//!
//! See [`FnMacro`] and [`VarMacro`] on how to parse macros.

#![warn(missing_debug_implementations)]
#![warn(missing_docs)]

pub mod ast;
pub use ast::*;
mod error;
pub use error::*;
mod macro_body;
pub use macro_body::*;
mod context;
pub use context::*;

mod var_macro;
pub use var_macro::VarMacro;

mod fn_macro;
pub use fn_macro::FnMacro;

mod macro_set;
pub use macro_set::{ExpansionError, MacroSet};

pub(crate) mod macro_token;
pub use macro_token::MacroToken;

pub(crate) mod codegen;
