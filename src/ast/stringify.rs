use std::fmt::Debug;

use nom::{
  combinator::map,
  sequence::{preceded, terminated},
  IResult,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{
  tokens::{macro_arg, meta, token},
  BuiltInType, Type,
};
use crate::{token::MacroArg, CodegenContext, LocalContext, MacroArgType, MacroToken};

/// Stringification of a macro argument.
///
/// ```c
/// #define STRINGIFY(x) #x
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stringify {
  pub(crate) arg: MacroArg,
}

impl Stringify {
  /// Parse a stringification expression.
  pub(crate) fn parse<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    map(preceded(terminated(token("#"), meta), macro_arg), |arg| Self { arg })(tokens)
  }

  pub(crate) fn finish<'t, C>(
    &mut self,
    ctx: &mut LocalContext<'_, 't, C>,
  ) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    let arg_ty = ctx.arg_type_mut(self.arg.index());
    if *arg_ty != MacroArgType::Ident {
      *arg_ty = MacroArgType::Expr;
    }

    Ok(Some(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)), mutable: false }))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>) -> TokenStream {
    let id = Ident::new(ctx.arg_name(self.arg.index()), Span::call_site());

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

  use crate::macro_set::{arg as macro_arg, tokens};

  #[test]
  fn parse_stringify() {
    let (_, ty) = Stringify::parse(tokens!["#", macro_arg!(0)]).unwrap();
    assert_eq!(ty, Stringify { arg: MacroArg { index: 0 } });
  }
}
