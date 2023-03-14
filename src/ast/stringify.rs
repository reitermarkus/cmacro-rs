use std::{fmt::Debug, ops::RangeFrom};

use nom::{
  combinator::map_opt,
  sequence::{preceded, terminated},
  AsChar, Compare, FindSubstring, IResult, InputIter, InputLength, InputTake, Slice,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{
  identifier::identifier,
  tokens::{meta, token},
  BuiltInType, Identifier, LitIdent, Type,
};
use crate::{CodegenContext, LocalContext, MacroArgType, ParseContext};

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
  pub(crate) fn parse<'i, I>(tokens: &'i [I], ctx: &ParseContext<'_>) -> IResult<&'i [I], Self>
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
    map_opt(preceded(terminated(token("#"), meta), identifier), |id| {
      if ctx.args.contains(&id.as_str()) {
        Some(Self { id: Identifier::Literal(LitIdent { id, macro_arg: true }) })
      } else {
        None
      }
    })(tokens)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
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
    let trait_prefix = ctx.trait_prefix();

    quote! {
      {
        const BYTES: &[u8] = #trait_prefix concat!(#trait_prefix stringify!(#id), '\0').as_bytes();
        BYTES.as_ptr() as *const #ffi_prefix c_char
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::ast::id;

  const CTX: ParseContext = ParseContext::fn_macro("STRINGIFY", &["var"]);

  #[test]
  fn parse_stringify() {
    let (_, ty) = Stringify::parse(&["#", "var"], &CTX).unwrap();
    assert_eq!(ty, Stringify { id: id!(@var) });
  }
}
