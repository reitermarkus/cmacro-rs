use std::fmt::Debug;

use nom::{
  combinator::map,
  sequence::{preceded, terminated},
  IResult,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{
  identifier::identifier_lit,
  tokens::{meta, token},
  BuiltInType, LitIdent, Type,
};
use crate::{CodegenContext, LocalContext, MacroArgType, MacroToken, ParseContext};

/// Stringification of a macro argument.
///
/// ```c
/// #define STRINGIFY(x) #x
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stringify {
  pub(crate) id: LitIdent,
}

impl Stringify {
  /// Parse a stringification expression.
  pub(crate) fn parse<'i, 't>(
    tokens: &'i [MacroToken<'t>],
    _ctx: &ParseContext<'_>,
  ) -> IResult<&'i [MacroToken<'t>], Self> {
    map(preceded(terminated(token("#"), meta), identifier_lit), |id| Self { id })(tokens)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    if let Some(arg_ty) = ctx.arg_type_mut(self.id.as_str()) {
      if *arg_ty != MacroArgType::Ident {
        *arg_ty = MacroArgType::Expr;
      }

      return Ok(Some(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)), mutable: false }))
    }

    // Only macro arguments can be stringified.
    Err(crate::CodegenError::UnsupportedExpression)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let id = Ident::new(self.id.as_str(), Span::call_site());

    let ffi_prefix = ctx.ffi_prefix().into_iter();
    let trait_prefix = ctx.trait_prefix().into_iter();

    let stringify = {
      let trait_prefix = trait_prefix.clone();
      quote! { #(#trait_prefix::)*stringify!($#id) }
    };

    quote! {
      {
        const BYTES: &[u8] = #(#trait_prefix::)*concat!(#stringify, '\0').as_bytes();
        BYTES.as_ptr() as *const #(#ffi_prefix::)*c_char
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::macro_set::tokens;

  const CTX: ParseContext = ParseContext::fn_macro("STRINGIFY", &["var"]);

  #[test]
  fn parse_stringify() {
    let (_, ty) = Stringify::parse(tokens!["#", "$var"], &CTX).unwrap();
    assert_eq!(ty, Stringify { id: LitIdent { id: "var".into() } });
  }
}
