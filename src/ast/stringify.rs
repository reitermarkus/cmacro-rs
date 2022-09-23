use nom::combinator::map;
use nom::sequence::preceded;
use nom::sequence::terminated;
use nom::IResult;
use proc_macro2::TokenStream;
use quote::quote;
use quote::TokenStreamExt;

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
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    map(preceded(terminated(token("#"), meta), identifier), |id| Self { id: Identifier::Literal(id.to_owned()) })(
      tokens,
    )
  }

  pub(crate) fn finish<'t, 'g, C>(&mut self, ctx: &mut LocalContext<'t, 'g, C>) -> Result<Option<Type>, crate::Error>
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

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>) -> TokenStream {
    let id = self.id.to_token_stream(ctx);

    quote! { ::core::stringify!(#id) }
  }
}
