use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use crate::{CodegenContext, LocalContext};

/// A macro argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroArg {
  pub(crate) index: usize,
}

impl MacroArg {
  /// Create a new macro argument with the given index.
  pub fn new(index: usize) -> Self {
    Self { index }
  }
}

impl MacroArg {
  pub(crate) fn index(&self) -> usize {
    self.index
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, '_, C>, tokens: &mut TokenStream) {
    tokens.append_all(match ctx.arg_name(self.index()) {
      "..." => quote! { $($__VA_ARGS__),* },
      name => {
        let name = Ident::new(name, Span::call_site());

        if ctx.export_as_macro {
          quote! { $#name }
        } else {
          quote! { #name }
        }
      },
    })
  }
}
