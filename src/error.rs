use std::fmt;

/// A parsing or codegen error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
  /// Variable is unknown.
  UnknownVariable(String),
  /// Parsing failed.
  ParserError,
  /// Cannot evaluate expression.
  UnsupportedExpression,
  /// Recursive macro definition.
  RecursiveDefinition(String),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::UnknownVariable(var_name) => write!(f, "unknown variable {}", var_name),
      Self::ParserError => write!(f, "parser error"),
      Self::UnsupportedExpression => write!(f, "unsupported expression"),
      Self::RecursiveDefinition(macro_name) => write!(f, "recursive macro definition {}", macro_name),
    }
  }
}
