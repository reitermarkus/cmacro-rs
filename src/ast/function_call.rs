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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionCall<'t> {
  /// The function name identifier.
  pub(crate) name: Box<Expr<'t>>,
  /// The function arguments.
  pub(crate) args: Vec<Expr<'t>>,
}

impl<'t> FunctionCall<'t> {
  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    // Cannot call functions in `const` context.
    if ctx.is_variable_macro() {
      return Err(crate::CodegenError::UnsupportedExpression)
    }

    self.name.finish(ctx)?;

    for arg in self.args.iter_mut() {
      arg.finish(ctx)?;
    }

    let mut ty = None;

    if let Expr::Var(Var { ref name }) = *self.name {
      if let Some((known_args, known_ret_ty)) = ctx.function(name.as_str()) {
        if known_args.len() == self.args.len() {
          let ffi_prefix = ctx.ffi_prefix();

          ty = Some(Type::from_rust_ty(&known_ret_ty, ffi_prefix.as_ref())?);

          for (arg, known_arg_type) in self.args.iter_mut().zip(known_args.iter()) {
            // If the current argument to this function is a macro argument,
            // we can infer the type of the macro argument.
            if let Expr::Arg(arg) = arg {
              let arg_type = ctx.arg_type_mut(arg.index());
              if *arg_type == MacroArgType::Unknown {
                *arg_type = MacroArgType::Known(Type::from_rust_ty(known_arg_type, ffi_prefix.as_ref())?);
              }
            }
          }
        }
      } else {
        ctx.export_as_macro = true;

        match name.as_str() {
          "__builtin_offsetof" if self.args.len() == 2 => {
            if let Expr::Arg(arg) = &mut self.args[0] {
              let arg_type = ctx.arg_type_mut(arg.index());
              if *arg_type == MacroArgType::Unknown {
                *arg_type = MacroArgType::Ty;
              }
            }

            if let Expr::Arg(arg) = &mut self.args[1] {
              let arg_type = ctx.arg_type_mut(arg.index());
              if *arg_type == MacroArgType::Unknown {
                *arg_type = MacroArgType::Tt;
              }
            }
          },
          _ => (),
        }
      }
    }

    Ok(ty)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    let (name, args_into) = match &*self.name {
      Expr::Var(Var { ref name }) if name.as_str() == "__builtin_offsetof" && self.args.len() == 2 => {
        let prefix = ctx.trait_prefix().into_iter();
        (quote! { #(#prefix::)*mem::offsetof! }, false)
      },
      name => (name.to_token_stream(ctx), true),
    };

    let args = self.args.iter().map(|arg| match arg {
      // Calling `.into()` on a null-pointer doesn't work.
      arg @ Expr::Cast(Cast { ty, expr })
        if ty.is_ptr() && matches!(&**expr, Expr::Literal(Lit::Int(LitInt { value: 0, .. }))) =>
      {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
      arg @ Expr::Literal(_) => {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
      arg @ Expr::Arg(arg2) if ctx.arg_name(arg2.index()) == "..." => {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
      // Exporting as a function means we inferred the types of the macro arguments,
      // so no `.into()` is needed in this case.
      arg @ Expr::Arg(_) if !ctx.export_as_macro => {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
      arg if args_into => {
        let arg = arg.to_token_stream(ctx);
        quote! { (#arg).into() }
      },
      arg => {
        let arg = arg.to_token_stream(ctx);
        quote! { #arg }
      },
    });

    tokens.append_all(quote! {
      #name(#(#args),*)
    })
  }
}
