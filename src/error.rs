/// A parsing or codegen error.
#[derive(Debug)]
pub enum Error {
  /// Variable is unknown.
  UnknownVariable,
  /// Parsing failed.
  ParserError,
  /// Cannot evaluate expression.
  UnsupportedExpression,
}
