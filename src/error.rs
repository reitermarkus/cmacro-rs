use crate::ast::Type;

/// A parsing or codegen error.
#[derive(Debug)]
pub enum Error {
  UnknownVariable,
  InvalidVarMacro,
  ParserError,
  UnsupportedExpression,
  IncompatibleTypes(Option<Type>, Option<Type>),
}
