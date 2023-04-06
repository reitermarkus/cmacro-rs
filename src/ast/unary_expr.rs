use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{BuiltInType, Type};
use crate::{CodegenContext, Expr, LocalContext};

/// A unary expression operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
  /// `expr++`
  PostInc,
  /// `expr--`
  PostDec,
  /// `++expr`
  Inc,
  /// `--expr`
  Dec,
  /// `+expr`
  Plus,
  /// `-expr`
  Minus,
  /// `!expr`
  Not,
  /// `~expr`
  Comp,
  /// `*expr`
  Deref,
  /// `&expr`
  AddrOf,
}

impl UnaryOp {
  pub(crate) const fn precedence(&self) -> (u8, Option<bool>) {
    match self {
      Self::PostInc | Self::PostDec => (1, Some(true)),
      Self::Inc | Self::Dec | Self::Plus | Self::Minus | Self::Not | Self::Comp | Self::Deref => (2, Some(false)),
      Self::AddrOf => (0, Some(false)),
    }
  }
}

/// A unary expression.
///
/// ```c
/// #define UNARY_EXPR &var
/// #define UNARY_EXPR *ptr
/// #define UNARY_EXPR i++
/// #define UNARY_EXPR !cond
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
  /// Expression operator.
  pub op: UnaryOp,
  /// Expression.
  pub expr: Expr,
}

impl UnaryExpr {
  #[inline]
  pub(crate) const fn precedence(&self) -> (u8, Option<bool>) {
    self.op.precedence()
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    let ty = self.expr.finish(ctx)?;

    match self.op {
      UnaryOp::Not => Ok(Some(Type::BuiltIn(BuiltInType::Bool))),
      UnaryOp::Deref => {
        // Cannot dereference pointers in variable macros, i.e. constants.
        if ctx.is_variable_macro() {
          return Err(crate::Error::UnsupportedExpression)
        }

        if let Some(Type::Ptr { ty, .. }) = ty {
          Ok(Some(*ty))
        } else {
          Ok(ty)
        }
      },
      UnaryOp::AddrOf => Ok(ty.map(|ty| Type::Ptr { ty: Box::new(ty), mutable: true })),
      _ => Ok(ty),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }
  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let (prec, _) = self.precedence();
    let (expr_prec, _) = self.expr.precedence();

    let raw_expr = self.expr.to_token_stream(ctx);

    let expr = if expr_prec > prec {
      quote! { (#raw_expr) }
    } else {
      raw_expr.clone()
    };

    match self.op {
      UnaryOp::Inc => {
        quote! { { #raw_expr += 1; #raw_expr } }
      },
      UnaryOp::Dec => {
        quote! { { #raw_expr -= 1; #raw_expr } }
      },
      UnaryOp::PostInc => {
        quote! { { let prev = #raw_expr; #raw_expr += 1; prev } }
      },
      UnaryOp::PostDec => {
        quote! { { let prev = #raw_expr; #raw_expr -= 1; prev } }
      },
      UnaryOp::Not => {
        quote! { !#expr }
      },
      UnaryOp::Comp => {
        quote! { !#expr }
      },
      UnaryOp::Plus => {
        quote! { +#expr }
      },
      UnaryOp::Minus => {
        quote! { -#expr }
      },
      UnaryOp::Deref => format!("*{}", expr).parse::<TokenStream>().unwrap(),
      UnaryOp::AddrOf => {
        let trait_prefix = ctx.trait_prefix().into_iter();
        quote! { #(#trait_prefix::)*ptr::addr_of_mut!(#raw_expr) }
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::{
    super::{assert_eq_tokens, id, lit, var},
    *,
  };

  #[test]
  fn parentheses_deref_cast() {
    let expr1 = UnaryExpr {
      op: UnaryOp::Deref,
      expr: Expr::Cast {
        ty: Type::Ptr { ty: Box::new(Type::Identifier { name: id!(MyType), is_struct: false }), mutable: true },
        expr: Box::new(lit!(1)),
      },
    };
    assert_eq_tokens!(expr1, "*(1u8 as *mut MyType)");
  }

  #[test]
  fn parentheses_deref_addr_of() {
    let expr1 = UnaryExpr {
      op: UnaryOp::Deref,
      expr: Expr::Unary(Box::new(UnaryExpr { op: UnaryOp::AddrOf, expr: var!(my_var) })),
    };
    assert_eq_tokens!(expr1, "*ptr::addr_of_mut!(my_var)");
  }
}
