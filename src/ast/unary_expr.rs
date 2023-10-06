use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use crate::{CodegenContext, LocalContext};

use super::{Associativity, BinaryExpr, BinaryOp, BuiltInType, Cast, Expr, Type};

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
  pub(crate) const fn precedence(&self) -> (u8, Associativity) {
    match self {
      Self::PostInc | Self::PostDec => (1, Associativity::Left),
      Self::Inc | Self::Dec | Self::Plus | Self::Minus | Self::Not | Self::Comp | Self::Deref => {
        (2, Associativity::Right)
      },
      Self::AddrOf => (0, Associativity::Right),
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnaryExpr<'t> {
  /// Expression operator.
  pub op: UnaryOp,
  /// Expression.
  pub expr: Box<Expr<'t>>,
}

impl<'t> UnaryExpr<'t> {
  #[inline]
  pub(crate) const fn precedence(&self) -> (u8, Associativity) {
    self.op.precedence()
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    let ty = self.expr.finish(ctx)?;

    match self.op {
      UnaryOp::Not => Ok(Some(Type::BuiltIn(BuiltInType::Bool))),
      UnaryOp::Deref => {
        // Cannot dereference pointers in variable macros, i.e. constants.
        if ctx.is_variable_macro() {
          return Err(crate::CodegenError::UnsupportedExpression)
        }

        match ty {
          Some(Type::Ptr { ty, .. }) => Ok(Some(*ty)),
          None => Ok(None),
          // Type can only be either a pointer-type or unknown.
          _ => Err(crate::CodegenError::UnsupportedExpression),
        }
      },
      UnaryOp::AddrOf => Ok(ty.map(|ty| Type::Ptr { ty: Box::new(ty) })),
      _ => Ok(ty),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let (prec, _) = self.precedence();
    let (expr_prec, _) = self.expr.precedence();

    let raw_expr = self.expr.to_token_stream(ctx);

    let expr = if expr_prec > prec {
      quote! { (#raw_expr) }
    } else {
      quote! { #raw_expr }
    };

    match self.op {
      UnaryOp::Inc => {
        if let Expr::Unary(UnaryExpr { op: UnaryOp::Deref, expr }) = &*self.expr {
          if let Expr::Cast(Cast { ty: Type::Ptr { ty }, .. }) = &**expr {
            if matches!(&**ty, Type::Qualified { qualifier, .. } if qualifier.is_volatile()) {
              let lhs_ptr = expr.to_token_stream(ctx);

              let prefix = ctx.trait_prefix().into_iter();
              let value = {
                quote! { #(#prefix::)*ptr::read_volatile(#lhs_ptr) + 1 }
              };

              let prefix = ctx.trait_prefix().into_iter();
              return quote! {
                {
                  let value = #value;
                  #(#prefix::)*ptr::write_volatile(#lhs_ptr, value);
                  value
                }
              }
            }
          }
        }

        quote! { { #raw_expr += 1; #raw_expr } }
      },
      UnaryOp::Dec => {
        if let Expr::Unary(UnaryExpr { op: UnaryOp::Deref, expr }) = &*self.expr {
          if let Expr::Cast(Cast { ty: Type::Ptr { ty }, .. }) = &**expr {
            if matches!(&**ty, Type::Qualified { qualifier, .. } if qualifier.is_volatile()) {
              let lhs_ptr = expr.to_token_stream(ctx);

              let prefix = ctx.trait_prefix().into_iter();
              let value = {
                quote! { #(#prefix::)*ptr::read_volatile(#lhs_ptr) - 1 }
              };

              let prefix = ctx.trait_prefix().into_iter();
              return quote! {
                {
                  let value = #value;
                  #(#prefix::)*ptr::write_volatile(#lhs_ptr, value);
                  value
                }
              }
            }
          }
        }

        quote! { { #raw_expr -= 1; #raw_expr } }
      },
      UnaryOp::PostInc => {
        if let Expr::Unary(UnaryExpr { op: UnaryOp::Deref, expr }) = &*self.expr {
          if let Expr::Cast(Cast { ty: Type::Ptr { ty }, .. }) = &**expr {
            if matches!(&**ty, Type::Qualified { qualifier, .. } if qualifier.is_volatile()) {
              let lhs_ptr = expr.to_token_stream(ctx);

              let prefix = ctx.trait_prefix().into_iter();
              let value = {
                quote! { #(#prefix::)*ptr::read_volatile(#lhs_ptr) }
              };

              let prefix = ctx.trait_prefix().into_iter();
              return quote! {
                {
                  let value = #value;
                  #(#prefix::)*ptr::write_volatile(#lhs_ptr, value + 1);
                  value
                }
              }
            }
          }
        }

        quote! { { let prev = #raw_expr; #raw_expr += 1; prev } }
      },
      UnaryOp::PostDec => {
        if let Expr::Unary(UnaryExpr { op: UnaryOp::Deref, expr }) = &*self.expr {
          if let Expr::Cast(Cast { ty: Type::Ptr { ty }, .. }) = &**expr {
            if matches!(&**ty, Type::Qualified { qualifier, .. } if qualifier.is_volatile()) {
              let lhs_ptr = expr.to_token_stream(ctx);

              let prefix = ctx.trait_prefix().into_iter();
              let value = {
                quote! { #(#prefix::)*ptr::read_volatile(#lhs_ptr) }
              };

              let prefix = ctx.trait_prefix().into_iter();
              return quote! {
                {
                  let value = #value;
                  #(#prefix::)*ptr::write_volatile(#lhs_ptr, value - 1);
                  value
                }
              }
            }
          }
        }

        quote! { { let prev = #raw_expr; #raw_expr -= 1; prev } }
      },
      UnaryOp::Not => format!("!{expr}").parse::<TokenStream>().unwrap(),
      UnaryOp::Comp => format!("!{expr}").parse::<TokenStream>().unwrap(),
      UnaryOp::Plus => format!("+{expr}").parse::<TokenStream>().unwrap(),
      UnaryOp::Minus => format!("-{expr}").parse::<TokenStream>().unwrap(),
      UnaryOp::Deref => {
        match &*self.expr {
          Expr::Cast(Cast { ty: Type::Ptr { ty }, .. }) => {
            if matches!(&**ty, Type::Qualified { qualifier, .. } if qualifier.is_volatile()) {
              let prefix = ctx.trait_prefix().into_iter();
              return quote! { #(#prefix::)*ptr::read_volatile(#raw_expr) }
            }
          },
          Expr::Binary(BinaryExpr { lhs, op, rhs }) => {
            let raw_lhs = lhs.to_token_stream(ctx);
            let raw_rhs = rhs.to_token_stream(ctx);

            let (lhs_prec, _) = lhs.precedence();

            let lhs = if lhs_prec > prec || lhs_prec > 1 {
              quote! { (#raw_lhs) }
            } else {
              raw_lhs
            };

            match op {
              BinaryOp::Add => return quote! { *#lhs.add(#raw_rhs) },
              BinaryOp::Sub => return quote! { *#lhs.sub(#raw_rhs) },
              _ => (),
            }
          },
          Expr::Unary(UnaryExpr { op, expr }) => {
            let raw_expr = expr.to_token_stream(ctx);

            match op {
              UnaryOp::Inc => return quote! { *{ #raw_expr = #raw_expr.add(1); #raw_expr } },
              UnaryOp::Dec => return quote! { *{ #raw_expr = #raw_expr.sub(1); #raw_expr } },
              UnaryOp::PostInc => return quote! { *{ let prev = #raw_expr; #raw_expr = #raw_expr.add(1); prev } },
              UnaryOp::PostDec => return quote! { *{ let prev = #raw_expr; #raw_expr = #raw_expr.sub(1); prev } },
              _ => (),
            }
          },
          _ => (),
        }

        format!("*{expr}").parse::<TokenStream>().unwrap()
      },
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
    super::{assert_eq_tokens, lit, var, Cast},
    *,
  };

  #[test]
  fn parentheses_deref_cast() {
    let expr1 = UnaryExpr {
      op: UnaryOp::Deref,
      expr: Box::new(Expr::Cast(Cast {
        ty: Type::Ptr { ty: Box::new(Type::Identifier { name: Box::new(var!(MyType)), is_struct: false }) },
        expr: Box::new(lit!(1)),
      })),
    };
    assert_eq_tokens!(expr1, "*(1u8 as *mut MyType)");
  }

  #[test]
  fn parentheses_deref_addr_of() {
    let expr1 = UnaryExpr {
      op: UnaryOp::Deref,
      expr: Box::new(Expr::Unary(UnaryExpr { op: UnaryOp::AddrOf, expr: Box::new(var!(my_var)) })),
    };
    assert_eq_tokens!(expr1, "*ptr::addr_of_mut!(my_var)");
  }
}
