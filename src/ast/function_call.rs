use proc_macro2::TokenStream;
use quote::TokenStreamExt;
use quote::quote;

use crate::LocalContext;
use crate::MacroArgType;
use super::*;

/// A function call.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
  pub name: Identifier,
  pub args: Vec<Expr>,
}

impl FunctionCall {
  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    self.name.finish(ctx)?;

    for arg in self.args.iter_mut() {
      arg.finish(ctx)?;
    }

    if let Identifier::Literal(ref function_name) = self.name {
      if let Some(known_args) = ctx.function(function_name.as_str()).cloned() {
        if known_args.len() == self.args.len() {
          for (arg, known_arg_type) in self.args.iter_mut().zip(known_args.iter()) {
            arg.finish(ctx)?;

            // If the current argument to this function is a macro argument,
            // we can infer the type of the macro argument.
            if let Expr::Variable { name: Identifier::Literal( ref name) } = arg {
              if let Some(arg_type) = ctx.arg_type_mut(name) {
                if *arg_type == MacroArgType::Unknown {
                  *arg_type = MacroArgType::Known(known_arg_type.clone());
                }
              }
            }
          }
        }
      }
    }

    for arg in self.args.iter_mut() {
      arg.finish(ctx)?;
    }

    Ok(())
  }

  pub fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
    let mut name = TokenStream::new();
    self.name.to_tokens(ctx, &mut name);

    let args = self.args.iter().map(|arg| {
      let into = matches!(arg, Expr::Variable { .. }) && !matches!(arg, Expr::Variable { name: Identifier::Literal(id) } if id == "NULL");

      let arg = arg.to_token_stream(ctx);

      if into {
        return quote! { #arg.into() }
      }

      arg
    });

    tokens.append_all(quote! {
      #name(#(#args),*)
    })
  }
}