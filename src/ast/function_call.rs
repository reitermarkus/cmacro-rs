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
  pub(crate) name: Box<Expr>,
  /// The function arguments.
  pub(crate) args: Vec<Expr>,
}

impl FunctionCall {
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    self.name.finish(ctx)?;

    for arg in self.args.iter_mut() {
      arg.finish(ctx)?;
    }

    let mut ty = None;

    if let Expr::Variable { name: Identifier::Literal(ref function_name) } = *self.name {
      if let Some((known_args, known_ret_ty)) = ctx.function(function_name.as_str()) {
        // Cannot call external functions in `const` context.
        if ctx.is_variable_macro() {
          return Err(crate::CodegenError::UnsupportedExpression)
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
      } else {
        ctx.export_as_macro = true;
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
          let prefix = ctx.trait_prefix().into_iter();

          if *mutable {
            quote! { #(#prefix::)*ptr::null_mut() }
          } else {
            quote! { #(#prefix::)*ptr::null() }
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
      arg @ Expr::Arg { name: Identifier::Literal(id) } if id.as_str() == "__VA_ARGS__" => {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
      // Exporting as a function means we inferred the types of the macro arguments,
      // so no `.into()` is needed in this case.
      arg @ Expr::Arg { name: Identifier::Literal(id) } if !ctx.export_as_macro => {
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
