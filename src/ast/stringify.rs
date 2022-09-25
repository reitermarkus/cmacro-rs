use std::{fmt::Debug, ops::RangeFrom};

use nom::{
  combinator::map,
  sequence::{preceded, terminated},
  AsChar, Compare, FindSubstring, IResult, InputIter, InputLength, InputTake, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{
  identifier::identifier,
  tokens::{meta, token},
  Identifier, Type,
};
use crate::{CodegenContext, LocalContext};

/// Stringification of a macro argument.
///
/// ```c
/// #define STRINGIFY(x) #x
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stringify {
  pub(crate) id: Identifier,
}

impl Stringify {
  pub fn parse<I>(tokens: &[I]) -> IResult<&[I], Self>
  where
    I: Debug
      + InputTake
      + InputLength
      + InputIter
      + Slice<RangeFrom<usize>>
      + Compare<&'static str>
      + FindSubstring<&'static str>
      + Clone,
    <I as InputIter>::Item: AsChar,
  {
    map(preceded(terminated(token("#"), meta), identifier), |id| Self { id: Identifier::Literal(id) })(tokens)
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    if let Identifier::Literal(ref id) = self.id {
      if ctx.is_macro_arg(id) {
        ctx.export_as_macro = true;
      }

      // TODO: Should be `*const c_char`.
      Ok(None)
    } else {
      unreachable!()
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let id = self.id.to_token_stream(ctx);

    quote! { ::core::stringify!(#id) }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_stringify() {
    let (_, ty) = Stringify::parse(&["#", "var"]).unwrap();
    assert_eq!(ty, Stringify { id: Identifier::Literal("var".into()) });
  }
}
