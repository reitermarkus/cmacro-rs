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
  BuiltInType, Identifier, Type,
};
use crate::{CodegenContext, LocalContext, MacroArgType};

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
  /// Parse a stringification expression.
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
      if let Some(arg_ty) = ctx.arg_type_mut(id.as_str()) {
        if *arg_ty != MacroArgType::Ident {
          *arg_ty = MacroArgType::Expr;
        }

        return Ok(Some(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)), mutable: false }))
      }
    }

    // Only macro arguments can be stringified.
    Err(crate::Error::UnsupportedExpression)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let id = self.id.to_token_stream(ctx);

    let ffi_prefix = ctx.ffi_prefix();
    let trait_prefix = ctx.num_prefix();

    quote! {
      #trait_prefix concat!(#trait_prefix stringify!(#id), '\0').as_ptr()
        as *const #ffi_prefix c_char
    }
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
