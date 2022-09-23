use quote::TokenStreamExt;
use quote::quote;
use nom::IResult;
use proc_macro2::TokenStream;
use nom::combinator::map;
use nom::sequence::preceded;
use nom::sequence::terminated;

use crate::LocalContext;
use super::{Identifier, tokens::{meta, token}};
use super::identifier::identifier;

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
    map(
      preceded(terminated(token("#"), meta), identifier),
      |id| Self { id: Identifier::Literal(id.to_owned()) },
    )(tokens)
  }

  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    if let Identifier::Literal(ref id) = self.id {
      if ctx.is_macro_arg(id) {
        ctx.export_as_macro = true;
      }

      Ok(())
    } else {
      unreachable!()
    }
  }

  pub fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream(&self, ctx: &mut LocalContext) -> TokenStream {
    let id = self.id.to_token_stream(ctx);

    quote! { ::core::stringify!(#id) }
  }
}
