use std::fmt::Debug;

use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::*;
use crate::{CodegenContext, LocalContext, MacroArgType};

/// A function call.
///
/// ```c
/// #define FUNC f(1, 2, 3)
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
  /// The function name identifier.
  pub(crate) name: Identifier,
  /// The function arguments.
  pub(crate) args: Vec<Expr>,
}

impl FunctionCall {
  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    self.name.finish(ctx)?;

    if let Identifier::Literal(name) = &self.name {
      if let Some(expr) = ctx.arg_value(name.as_str()).or_else(|| ctx.variable_macro_value(name.as_str())) {
        match expr {
          Expr::Variable { name } => {
            let mut name = name.clone();
            name.finish(ctx)?;
            self.name = name;
          },
          _ => return Err(crate::Error::UnsupportedExpression),
        }
      }
    }

    if let Identifier::Literal(name) = &self.name {
      if ctx.function(name.as_str()).is_none() {
        ctx.export_as_macro = true;
      }
    }

    for arg in self.args.iter_mut() {
      arg.finish(ctx)?;
    }

    let mut ty = None;

    if let Identifier::Literal(ref function_name) = self.name {
      if let Some((known_args, known_ret_ty)) = ctx.function(function_name.as_str()) {
        // Cannot call external functions in `const` context.
        if ctx.is_variable_macro() {
          return Err(crate::Error::UnsupportedExpression)
        }

        if known_args.len() == self.args.len() {
          if let Ok(y) = syn::parse_str::<syn::Type>(&known_ret_ty) {
            ty = Some(Type::try_from(y)?);
          }

          for (arg, known_arg_type) in self.args.iter_mut().zip(known_args.iter()) {
            // If the current argument to this function is a macro argument,
            // we can infer the type of the macro argument.
            if let Expr::Variable { name: Identifier::Literal(ref name) } = arg {
              if let Some(arg_type) = ctx.arg_type_mut(name.as_str()) {
                if *arg_type == MacroArgType::Unknown {
                  if let Ok(ty) = syn::parse_str::<syn::Type>(known_arg_type) {
                    *arg_type = MacroArgType::Known(Type::try_from(ty)?);
                  }
                }
              }
            }
          }
        }
      }
    }

    Ok(ty)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    let mut name = TokenStream::new();
    self.name.to_tokens(ctx, &mut name);

    let args = self.args.iter().map(|arg| match arg {
      Expr::Cast { ty: Type::Ptr { mutable, .. }, expr } => match **expr {
        Expr::Literal(Lit::Int(LitInt { value: 0, .. })) => {
          let prefix = ctx.trait_prefix();

          if *mutable {
            quote! { #prefix ptr::null_mut() }
          } else {
            quote! { #prefix ptr::null() }
          }
        },
        _ => {
          let arg = arg.to_token_stream(ctx);
          quote! { (#arg).cast() }
        },
      },
      arg @ Expr::Literal(_) => {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
      // Exporting as a function means we inferred the types of the macro arguments,
      // so no `.into()` is needed in this case.
      arg @ Expr::Variable { name: Identifier::Literal(id) } if !ctx.export_as_macro && id.macro_arg => {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
      _ => {
        let arg = arg.to_token_stream(ctx);
        quote! { (#arg).into() }
      },
    });

    tokens.append_all(quote! {
      #name(#(#args),*)
    })
  }
}
