use quote::{quote, ToTokens, TokenStreamExt};
use proc_macro2::TokenStream;

use crate::{LocalContext, Expr};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
  /// lhs * rhs
  Mul,
  /// lhs / rhs
  Div,
  /// lhs % rhs
  Rem,
  /// lhs + rhs
  Plus,
  /// lhs - rhs
  Minus,
  /// lhs << rhs
  Shl,
  /// lhs >> rhs
  Shr,
  /// lhs < rhs
  Lt,
  /// lhs <= rhs
  Lte,
  /// lhs > rhs
  Gt,
  /// lhs >= rhs
  Gte,
  /// lhs == rhs
  Eq,
  /// lhs != rhs
  Neq,
  /// lhs & rhs
  BitAnd,
  /// lhs ^ rhs
  BitXor,
  /// lhs | rhs
  BitOr,
  /// lhs && rhs
  And,
  /// lhs || rhs
  Or,
  /// lhs = rhs
  Assign,
  /// lhs += rhs
  AddAssign,
  /// lhs -= rhs
  SubAssign,
  /// lhs *= rhs
  MulAssign,
  /// lhs /= rhs
  DivAssign,
  /// lhs %= rhs
  RemAssign,
  /// lhs <<= rhs
  ShlAssign,
  /// lhs >>= rhs
  ShrAssign,
  /// lhs &= rhs
  BitAndAssign,
  /// lhs ^= rhs
  XorAssign,
  /// lhs |= rhs
  BitOrAssign,
}

impl ToTokens for BinOp {
  fn to_tokens(&self, tokens: &mut TokenStream) {
    tokens.append_all(match self {
      Self::Mul => quote!{ * },
      Self::Div => quote!{ / },
      Self::Rem => quote!{ % },
      Self::Plus => quote!{ + },
      Self::Minus => quote!{ - },
      Self::Shl => quote!{ << },
      Self::Shr => quote!{ >> },
      Self::Lt => quote!{ < },
      Self::Lte => quote!{ <= },
      Self::Gt => quote!{ > },
      Self::Gte => quote!{ >= },
      Self::Eq => quote!{ == },
      Self::Neq => quote!{ != },
      Self::BitAnd => quote!{ & },
      Self::BitXor => quote!{ ^ },
      Self::BitOr => quote!{ | },
      Self::And => quote!{ && },
      Self::Or => quote!{ || },
      Self::Assign => quote!{ =  },
      Self::AddAssign => quote!{ += },
      Self::SubAssign => quote!{ -= },
      Self::MulAssign => quote!{ *= },
      Self::DivAssign => quote!{ /= },
      Self::RemAssign => quote!{ %= },
      Self::ShlAssign => quote!{ <<= },
      Self::ShrAssign => quote!{ >>= },
      Self::BitAndAssign => quote!{ &= },
      Self::XorAssign => quote!{ ^= },
      Self::BitOrAssign => quote!{ |= },
    })
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryOp {
  pub lhs: Expr,
  pub op: BinOp,
  pub rhs: Expr,
}

impl BinaryOp {
  pub fn finish<'t, 'g>(&mut self, ctx: &mut LocalContext<'t, 'g>) -> Result<(), crate::Error> {
    self.lhs.finish(ctx)?;
    self.rhs.finish(ctx)?;

    Ok(())
  }

  pub(crate) fn to_tokens(&self, ctx: &mut LocalContext, tokens: &mut TokenStream) {
    let lhs = self.lhs.to_token_stream(ctx);
    let op = self.op;
    let rhs = self.rhs.to_token_stream(ctx);

    tokens.append_all(match self.op {
      BinOp::Assign | BinOp::AddAssign | BinOp::SubAssign |
      BinOp::BitAndAssign | BinOp::XorAssign | BinOp::BitOrAssign => {
        quote! { { #lhs #op #rhs; #lhs } }
      },
      op => quote!{ ( #lhs #op #rhs ) },
    })
  }
}
