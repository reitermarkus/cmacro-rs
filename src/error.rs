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
