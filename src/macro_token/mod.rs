use crate::ast::{Comment, Identifier, IdentifierContinue, Lit, MacroArg, Punctuation};

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
  /// An identifier continuation.
  IdentifierContinue(IdentifierContinue<'t>),
  /// A literal.
  Lit(Lit<'t>),
  /// Punctuation.
  Punctuation(Punctuation<'t>),
  /// A comment.
  Comment(Comment<'t>),
}

impl<'t> From<Identifier<'t>> for MacroToken<'t> {
  fn from(lit: Identifier<'t>) -> Self {
    Self::Identifier(lit)
  }
}

impl<'t> From<IdentifierContinue<'t>> for MacroToken<'t> {
  fn from(lit: IdentifierContinue<'t>) -> Self {
    Self::IdentifierContinue(lit)
  }
}

impl<'t> From<Lit<'t>> for MacroToken<'t> {
  fn from(lit: Lit<'t>) -> Self {
    Self::Lit(lit)
  }
}
