use std::fmt::Debug;

use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};

use super::{BuiltInType, Identifier, Lit, LitFloat, LitInt, Type};
use crate::{CodegenContext, Expr, LocalContext};

/// A binary expression operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
  /// `lhs * rhs`
  Mul,
  /// `lhs / rhs`
  Div,
  /// `lhs % rhs`
  Rem,
  /// `lhs + rhs`
  Add,
  /// `lhs - rhs`
  Sub,
  /// `lhs << rhs`
  Shl,
  /// `lhs >> rhs`
  Shr,
  /// `lhs < rhs`
  Lt,
  /// `lhs <= rhs`
  Lte,
  /// `lhs > rhs`
  Gt,
  /// `lhs >= rhs`
  Gte,
  /// `lhs == rhs`
  Eq,
  /// `lhs != rhs`
  Neq,
  /// `lhs & rhs`
  BitAnd,
  /// `lhs ^ rhs`
  BitXor,
  /// `lhs | rhs`
  BitOr,
  /// `lhs && rhs`
  And,
  /// `lhs || rhs`
  Or,
  /// `lhs = rhs`
  Assign,
  /// `lhs += rhs`
  AddAssign,
  /// `lhs -= rhs`
  SubAssign,
  /// `lhs *= rhs`
  MulAssign,
  /// `lhs /= rhs`
  DivAssign,
  /// `lhs %= rhs`
  RemAssign,
  /// `lhs <<= rhs`
  ShlAssign,
  /// `lhs >>= rhs`
  ShrAssign,
  /// `lhs &= rhs`
  BitAndAssign,
  /// `lhs ^= rhs`
  BitXorAssign,
  /// `lhs |= rhs`
  BitOrAssign,
}

impl BinaryOp {
  pub(crate) const fn precedence(&self) -> (u8, Option<bool>) {
    match self {
      Self::Mul | Self::Div | Self::Rem => (5, Some(true)),
      Self::Add | Self::Sub => (6, Some(true)),
      Self::Shl | Self::Shr => (7, Some(true)),

      Self::BitAnd => (8, Some(true)),
      Self::BitXor => (9, Some(true)),
      Self::BitOr => (10, Some(true)),

      Self::Eq | Self::Neq | Self::Lt | Self::Gt | Self::Lte | Self::Gte => (11, None),

      Self::And => (12, Some(true)),
      Self::Or => (13, Some(true)),
      Self::Assign
      | Self::AddAssign
      | Self::SubAssign
      | Self::MulAssign
      | Self::DivAssign
      | Self::RemAssign
      | Self::ShlAssign
      | Self::ShrAssign
      | Self::BitAndAssign
      | Self::BitXorAssign
      | Self::BitOrAssign => (14, Some(false)),
    }
  }
}

impl ToTokens for BinaryOp {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Mul => quote! { * },
      Self::Div => quote! { / },
      Self::Rem => quote! { % },
      Self::Add => quote! { + },
      Self::Sub => quote! { - },
      Self::Shl => quote! { << },
      Self::Shr => quote! { >> },
      Self::Lt => quote! { < },
      Self::Lte => quote! { <= },
      Self::Gt => quote! { > },
      Self::Gte => quote! { >= },
      Self::Eq => quote! { == },
      Self::Neq => quote! { != },
      Self::BitAnd => quote! { & },
      Self::BitXor => quote! { ^ },
      Self::BitOr => quote! { | },
      Self::And => quote! { && },
      Self::Or => quote! { || },
      Self::Assign => quote! { =  },
      Self::AddAssign => quote! { += },
      Self::SubAssign => quote! { -= },
      Self::MulAssign => quote! { *= },
      Self::DivAssign => quote! { /= },
      Self::RemAssign => quote! { %= },
      Self::ShlAssign => quote! { <<= },
      Self::ShrAssign => quote! { >>= },
      Self::BitAndAssign => quote! { &= },
      Self::BitXorAssign => quote! { ^= },
      Self::BitOrAssign => quote! { |= },
    })
  }
}

/// A binary expression.
///
/// ```c
/// #define BINARY_EXPR a + b
/// #define BINARY_EXPR 1 + 2
/// #define BINARY_EXPR 7 % c
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
  /// Left-hand side expression.
  pub lhs: Expr,
  /// Expression operator.
  pub op: BinaryOp,
  /// Right-hand side expression.
  pub rhs: Expr,
}

impl BinaryExpr {
  #[inline]
  pub(crate) const fn precedence(&self) -> (u8, Option<bool>) {
    self.op.precedence()
  }

  pub(crate) fn finish<'g, C>(
    &mut self,
    ctx: &mut LocalContext<'g, C>,
  ) -> Result<(Option<Type>, Option<Type>), crate::Error>
  where
    C: CodegenContext,
  {
    let max_ty_cast = |expr: &Expr| {
      if let Expr::Variable { name: Identifier::Literal(id) } = expr {
        return Some(Type::BuiltIn(match id.as_str() {
          "__SCHAR_MAX__" => BuiltInType::UChar,
          "__SHRT_MAX__" => BuiltInType::UShort,
          "__INT_MAX__" => BuiltInType::UInt,
          "__LONG_MAX__" => BuiltInType::ULong,
          "__LONG_LONG_MAX__" => BuiltInType::ULongLong,
          _ => return None,
        }))
      }

      None
    };

    let mut lhs_ty = self.lhs.finish(ctx)?;
    let mut rhs_ty = self.rhs.finish(ctx)?;

    // Cast mixed float and int expression.
    match (&self.lhs, &self.rhs) {
      (Expr::Literal(Lit::Int(LitInt { value: lhs, suffix: None })), Expr::Literal(Lit::Float(_))) => {
        let f = if *lhs >= f32::MIN as i128 && *lhs <= f32::MAX as i128 {
          LitFloat::Float(*lhs as f32)
        } else {
          LitFloat::Double(*lhs as f64)
        };
        self.lhs = Expr::Literal(Lit::Float(f));
        lhs_ty = self.lhs.finish(ctx)?;
      },
      (Expr::Literal(Lit::Float(_)), Expr::Literal(Lit::Int(LitInt { value: rhs, suffix: None }))) => {
        let f = if *rhs >= f32::MIN as i128 && *rhs <= f32::MAX as i128 {
          LitFloat::Float(*rhs as f32)
        } else {
          LitFloat::Double(*rhs as f64)
        };
        self.rhs = Expr::Literal(Lit::Float(f));
        rhs_ty = self.rhs.finish(ctx)?;
      },
      (lhs, Expr::Literal(Lit::Int(_))) => {
        if let Some(lhs_ty2) = max_ty_cast(lhs) {
          self.lhs = Expr::Cast { ty: lhs_ty2.clone(), expr: Box::new(lhs.clone()) };
          lhs_ty = Some(lhs_ty2);
        }
      },
      (Expr::Literal(Lit::Int(_)), rhs) => {
        if let Some(rhs_ty2) = max_ty_cast(rhs) {
          self.rhs = Expr::Cast { ty: rhs_ty2.clone(), expr: Box::new(rhs.clone()) };
          rhs_ty = Some(rhs_ty2);
        }
      },
      _ => (),
    }

    Ok((lhs_ty, rhs_ty))
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }
  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    let mut lhs = self.lhs.to_token_stream(ctx);
    let op = self.op;
    let mut rhs = self.rhs.to_token_stream(ctx);

    let (lhs_prec, _) = self.lhs.precedence();
    let (prec, assoc) = self.precedence();
    let (rhs_prec, _) = self.rhs.precedence();

    let (lhs_parens, rhs_parens) = match (prec, assoc) {
      (_, None) => (lhs_prec >= prec, rhs_prec >= prec),
      (_, Some(true)) => (lhs_prec > prec, rhs_prec >= prec),
      (_, Some(false)) => (lhs_prec <= prec, rhs_prec < prec),
    };

    match self.op {
      BinaryOp::Assign
      | BinaryOp::AddAssign
      | BinaryOp::SubAssign
      | BinaryOp::BitAndAssign
      | BinaryOp::BitXorAssign
      | BinaryOp::BitOrAssign => {
        quote! { { #lhs #op #rhs; #lhs } }
      },
      op => {
        if lhs_parens {
          lhs = quote! { (#lhs) };
        }
        if rhs_parens {
          rhs = quote! { (#rhs) };
        }

        quote! { #lhs #op #rhs }
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::{
    super::{assert_eq_tokens, lit, var},
    *,
  };

  #[test]
  fn parentheses_add_mul() {
    let expr1 = BinaryExpr { lhs: lit!(1), op: BinaryOp::Add, rhs: lit!(2) };
    assert_eq_tokens!(expr1, "1 + 2");

    let expr2 = BinaryExpr { lhs: Expr::Binary(Box::new(expr1.clone())), op: BinaryOp::Add, rhs: lit!(3) };
    assert_eq_tokens!(expr2, "1 + 2 + 3");

    let expr3 = BinaryExpr { lhs: Expr::Binary(Box::new(expr1.clone())), op: BinaryOp::Mul, rhs: lit!(3) };
    assert_eq_tokens!(expr3, "(1 + 2) * 3");
  }

  #[test]
  fn parentheses_neq() {
    let expr1 = BinaryExpr { lhs: lit!(1), op: BinaryOp::Neq, rhs: lit!(2) };
    assert_eq_tokens!(expr1, "1 != 2");
  }

  #[test]
  fn parentheses_eq() {
    let expr1 = BinaryExpr { lhs: lit!(1), op: BinaryOp::BitAnd, rhs: lit!(2) };
    assert_eq_tokens!(expr1, "1 & 2");

    let expr2 = BinaryExpr { lhs: Expr::Binary(Box::new(expr1)), op: BinaryOp::Eq, rhs: lit!(3) };
    assert_eq_tokens!(expr2, "1 & 2 == 3");
  }

  #[test]
  fn parentheses_rem_div() {
    let expr1 = BinaryExpr { lhs: lit!(6), op: BinaryOp::Rem, rhs: lit!(9) };
    assert_eq_tokens!(expr1, "6 % 9");

    let expr2 = BinaryExpr { lhs: Expr::Binary(Box::new(expr1)), op: BinaryOp::Div, rhs: lit!(3) };
    assert_eq_tokens!(expr2, "6 % 9 / 3");

    let expr3 = BinaryExpr { lhs: lit!(9), op: BinaryOp::Div, rhs: lit!(3) };
    assert_eq_tokens!(expr3, "9 / 3");

    let expr4 = BinaryExpr { lhs: lit!(6), op: BinaryOp::Rem, rhs: Expr::Binary(Box::new(expr3)) };
    assert_eq_tokens!(expr4, "6 % (9 / 3)");
  }

  #[test]
  fn parentheses_assign() {
    let expr1 = BinaryExpr { lhs: var!(a), op: BinaryOp::Assign, rhs: var!(b) };
    assert_eq_tokens!(expr1, "{ a = b; a }");

    let expr2 = BinaryExpr { lhs: var!(c), op: BinaryOp::Assign, rhs: Expr::Binary(Box::new(expr1)) };
    assert_eq_tokens!(expr2, "{ c = { a = b; a }; c }");
  }
}
