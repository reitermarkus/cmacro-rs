use std::fmt;

/// An error during parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserError {
  /// Invalid macro name.
  InvalidMacroName,
  /// Invalid macro arguments.
  InvalidMacroArgs,
  /// Invalid macro body.
  InvalidMacroBody,
}

impl fmt::Display for ParserError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidMacroName => write!(f, "invalid macro name"),
      Self::InvalidMacroArgs => write!(f, "invalid macro arguments"),
      Self::InvalidMacroBody => write!(f, "invalid macro body"),
    }
  }
}

impl std::error::Error for ParserError {}

/// An error during code generation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodegenError {
  /// Recursive macro definition.
  RecursiveDefinition(String),
  /// Variable-like macro is not an expression.
  NonExpressionVarMacro,
  /// Expression is not supported in Rust.
  UnsupportedExpression(String),
  /// Type is not supported.
  UnsupportedType(String),
  /// Variable is unknown.
  UnknownVariable(String),
}

impl fmt::Display for CodegenError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::RecursiveDefinition(macro_name) => write!(f, "recursive macro definition {}", macro_name),
      Self::NonExpressionVarMacro => write!(f, "non-expression variable-like macro"),
      Self::UnsupportedExpression(expr) => write!(f, "unsupported expression: {}", expr),
      Self::UnsupportedType(ty) => write!(f, "unsupported type {}", ty),
      Self::UnknownVariable(var_name) => write!(f, "unknown variable {}", var_name),
    }
  }
}

impl std::error::Error for CodegenError {}
