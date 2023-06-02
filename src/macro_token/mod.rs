use std::borrow::Cow;

use crate::ast::{Comment, Identifier, Lit, MacroArg};

#[cfg(test)]
mod macros;
#[cfg(test)]
pub(crate) use macros::*;

/// A macro token.
#[derive(Debug, Clone, PartialEq)]
pub enum MacroToken<'t> {
  /// A macro parameter for the argument at the given position.
  Arg(MacroArg),
  /// An identifier.
  Identifier(Identifier<'t>),
  /// A literal.
  Lit(Lit<'t>),
  /// Punctuation.
  Punctuation(&'t str),
  /// A comment.
  Comment(Comment<'t>),
  /// An macro token.
  Token(Cow<'t, str>),
}
