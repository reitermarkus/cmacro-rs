use std::{borrow::Cow, fmt::Debug};

use nom::{
  branch::alt,
  character::complete::char,
  combinator::{map, map_opt, map_res, value},
  multi::{fold_many0, many1, separated_list0},
  sequence::{delimited, pair, preceded, terminated, tuple},
  IResult,
};
use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{tokens::parenthesized, *};
use crate::{
  ast::tokens::{macro_arg, macro_id},
  token::MacroArg,
  CodegenContext, LocalContext, MacroArgType, MacroToken, UnaryOp,
};

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Expr<'t> {
  Arg(MacroArg),
  Variable { name: LitIdent<'t> },
  FunctionCall(FunctionCall<'t>),
  Cast { expr: Box<Self>, ty: Type<'t> },
  Literal(Lit),
  FieldAccess { expr: Box<Self>, field: Box<Self> },
  ArrayAccess { expr: Box<Self>, index: Box<Self> },
  Stringify(Stringify<'t>),
  ConcatIdent(Vec<Self>),
  ConcatString(Vec<Self>),
  Unary(Box<UnaryExpr<'t>>),
  Binary(Box<BinaryExpr<'t>>),
  Ternary(Box<Self>, Box<Self>, Box<Self>),
  Asm(Asm<'t>),
}

impl<'t> Expr<'t> {
  pub(crate) const fn precedence(&self) -> (u8, Option<bool>) {
    match self {
      Self::Asm(_) | Self::Literal(_) | Self::Arg(_) | Self::Variable { .. } | Self::ConcatIdent(_) => (0, None),
      Self::FunctionCall(_) | Self::FieldAccess { .. } => (1, Some(true)),
      Self::Cast { .. } | Self::Stringify(_) | Self::ConcatString(_) => (3, Some(true)),
      Self::Ternary(..) => (0, None),
      // While C array syntax is left associative, Rust precedence is the same as a dereference.
      Self::ArrayAccess { .. } => UnaryOp::Deref.precedence(),
      Self::Unary(expr) => expr.op.precedence(),
      Self::Binary(expr) => expr.op.precedence(),
    }
  }

  /// Parse identifier concatenation, e.g. `arg ## 2`.
  pub(crate) fn parse_concat_ident<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, id) = alt((map(macro_arg, Self::Arg), map(macro_id, |id| Self::Variable { name: id })))(tokens)?;

    fold_many0(
      preceded(
        delimited(meta, token("##"), meta),
        alt((
          map(macro_arg, Self::Arg),
          map(macro_id, |id| Self::Variable { name: id }),
          // Split non-identifiers, e.g. `123def` into integer literals and identifiers.
          map_opt(take_one, |token| {
            fn unsuffixed_int<'e>(input: &str) -> IResult<&str, Expr<'e>> {
              let map_lit_int = |i: u64| Expr::Literal(Lit::Int(LitInt { value: i.into(), suffix: None }));
              alt((
                // Keep leading zeros.
                map(value(0, char('0')), map_lit_int),
                map(nom::character::complete::u64, map_lit_int),
              ))(input)
            }

            let (_, ids) = match token {
              MacroToken::Token(Cow::Borrowed(token2)) => many1(alt((
                unsuffixed_int,
                map_opt(LitIdent::parse_str, |id| Some(Self::Variable { name: id })),
              )))(token2)
              .ok()?,
              MacroToken::Token(Cow::Owned(token2)) => many1(alt((
                unsuffixed_int,
                map_opt(LitIdent::parse_str, |id| Some(Self::Variable { name: id.to_static() })),
              )))(token2.as_ref())
              .ok()?,
              _ => return None,
            };

            Some(Self::ConcatIdent(ids))
          }),
        )),
      ),
      move || id.clone(),
      |acc, item| match (acc, item) {
        (Self::ConcatIdent(mut ids), Self::ConcatIdent(ids2)) => {
          ids.extend(ids2);
          Self::ConcatIdent(ids)
        },
        (Self::ConcatIdent(mut ids), item) => {
          ids.push(item);
          Self::ConcatIdent(ids)
        },
        (expr, item) => match item {
          Self::ConcatIdent(mut ids) => {
            ids.insert(0, expr);
            Self::ConcatIdent(ids)
          },
          item => Self::ConcatIdent(vec![expr, item]),
        },
      },
    )(tokens)
  }

  /// Parse string concatenation, e.g. `arg "333"`.
  fn parse_concat_string<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let parse_var = Self::parse_concat_ident;
    let parse_string =
      alt((map(LitString::parse, |s| Self::Literal(Lit::String(s))), map(Stringify::parse, Self::Stringify)));
    let mut parse_part = alt((parse_string, parse_var));

    let (tokens, s) = parse_part(tokens)?;

    fold_many0(
      preceded(meta, parse_part),
      move || s.clone(),
      |mut acc, expr| match acc {
        Self::ConcatString(ref mut args) => {
          args.push(expr);
          acc
        },
        acc => Self::ConcatString(vec![acc, expr]),
      },
    )(tokens)
  }

  fn parse_factor<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    alt((
      map(LitChar::parse, |c| Self::Literal(Lit::Char(c))),
      Self::parse_concat_string,
      map(Lit::parse, Self::Literal),
      parenthesized(Self::parse),
    ))(tokens)
  }

  fn parse_term_prec1<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, factor) = Self::parse_factor(tokens)?;

    // `__asm ( ... )` or `__asm volatile ( ... )`
    fn is_asm(expr: &Expr) -> bool {
      match expr {
        Expr::Variable { name } => matches!(name.as_str(), "__asm__" | "__asm" | "asm"),
        Expr::ConcatString(exprs) => match exprs.as_slice() {
          [first, second] => {
            is_asm(first)
              && matches!(
                second,
                Expr::Variable { name }
                if matches!(name.as_str(), "volatile" | "inline" | "goto")
              )
          },
          _ => false,
        },
        _ => false,
      }
    }

    match factor {
      ref expr if is_asm(expr) => {
        if let Ok((tokens, asm)) = Asm::parse(tokens) {
          return Ok((tokens, Self::Asm(asm)))
        }
      },
      Self::Arg(_)
      | Self::Variable { .. }
      | Self::FunctionCall(..)
      | Self::FieldAccess { .. }
      | Self::ArrayAccess { .. } => (),
      Self::Unary(ref op) if matches!(&**op, UnaryExpr { op: UnaryOp::AddrOf, .. }) => (),
      _ => return Ok((tokens, factor)),
    }

    enum Access<'t> {
      Fn(Vec<Expr<'t>>),
      Field { field: Box<Expr<'t>>, deref: bool },
      Array { index: Box<Expr<'t>> },
      UnaryOp(UnaryOp),
    }

    map_res(
      fold_many0(
        preceded(
          meta,
          alt((
            map(parenthesized(separated_list0(tuple((meta, token(","), meta)), Self::parse)), Access::Fn),
            map(preceded(terminated(token("."), meta), Self::parse_concat_ident), |field| Access::Field {
              field: Box::new(field),
              deref: false,
            }),
            map(delimited(terminated(token("["), meta), Self::parse, preceded(meta, token("]"))), |index| {
              Access::Array { index: Box::new(index) }
            }),
            map(preceded(terminated(token("->"), meta), Self::parse_concat_ident), |field| Access::Field {
              field: Box::new(field),
              deref: true,
            }),
            map(alt((value(UnaryOp::PostInc, token("++")), value(UnaryOp::PostDec, token("--")))), |op| {
              Access::UnaryOp(op)
            }),
          )),
        ),
        move || Ok((factor.clone(), false)),
        |acc, access| {
          let (expr, was_unary_op) = acc?;
          let is_unary_op = matches!(access, Access::UnaryOp(_));

          Ok((
            match (expr, access) {
              // Postfix `++`/`--` cannot be chained.
              (expr, Access::UnaryOp(op)) if !was_unary_op => Self::Unary(Box::new(UnaryExpr { expr, op })),
              // TODO: Support calling expressions as functions.
              (name @ Self::Arg(_) | name @ Self::Variable { .. }, Access::Fn(args)) => {
                Self::FunctionCall(FunctionCall { name: Box::new(name), args })
              },
              // Field access cannot be chained after postfix `++`/`--`.
              (acc, Access::Field { field, deref }) if !was_unary_op || deref => {
                let acc = if deref { Self::Unary(Box::new(UnaryExpr { op: UnaryOp::Deref, expr: acc })) } else { acc };
                Self::FieldAccess { expr: Box::new(acc), field }
              },
              // Array access cannot be chained after postfix `++`/`--`.
              (acc, Access::Array { index }) if !was_unary_op => Self::ArrayAccess { expr: Box::new(acc), index },
              _ => return Err(()),
            },
            is_unary_op,
          ))
        },
      ),
      |res| res.map(|(expr, _)| expr),
    )(tokens)
  }

  fn parse_term_prec2<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    alt((
      map(pair(parenthesized(Type::parse), Self::parse_term_prec2), |(ty, term)| Self::Cast {
        expr: Box::new(term),
        ty,
      }),
      map(
        pair(
          terminated(
            alt((
              value(UnaryOp::Deref, token("*")),
              value(UnaryOp::AddrOf, token("&")),
              value(UnaryOp::Inc, token("++")),
              value(UnaryOp::Dec, token("--")),
              value(UnaryOp::Plus, token("+")),
              value(UnaryOp::Minus, token("-")),
              value(UnaryOp::Not, token("!")),
              value(UnaryOp::Comp, token("~")),
            )),
            meta,
          ),
          Self::parse_term_prec2,
        ),
        |(op, expr)| Self::Unary(Box::new(UnaryExpr { op, expr })),
      ),
      Self::parse_term_prec1,
    ))(tokens)
  }

  fn parse_term_prec3<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec2(tokens)?;

    fold_many0(
      pair(
        delimited(
          meta,
          alt((value(BinaryOp::Mul, token("*")), value(BinaryOp::Div, token("/")), value(BinaryOp::Rem, token("%")))),
          meta,
        ),
        Self::parse_term_prec2,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec4<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec3(tokens)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Add, token("+")), value(BinaryOp::Sub, token("-")))), meta),
        Self::parse_term_prec3,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec5<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec4(tokens)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Shl, token("<<")), value(BinaryOp::Shr, token(">>")))), meta),
        Self::parse_term_prec4,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec6<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec5(tokens)?;

    fold_many0(
      pair(
        delimited(
          meta,
          alt((
            value(BinaryOp::Lt, token("<")),
            value(BinaryOp::Lte, token("<=")),
            value(BinaryOp::Gt, token(">")),
            value(BinaryOp::Gte, token(">=")),
          )),
          meta,
        ),
        Self::parse_term_prec5,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec7<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec6(tokens)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Eq, token("==")), value(BinaryOp::Neq, token("!=")))), meta),
        Self::parse_term_prec6,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  fn parse_term_prec8<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec7(tokens)?;

    fold_many0(
      preceded(delimited(meta, token("&"), meta), Self::parse_term_prec7),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitAnd, rhs })),
    )(tokens)
  }

  fn parse_term_prec9<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec8(tokens)?;

    fold_many0(
      preceded(delimited(meta, token("^"), meta), Self::parse_term_prec8),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitXor, rhs })),
    )(tokens)
  }

  fn parse_term_prec10<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec9(tokens)?;

    fold_many0(
      preceded(delimited(meta, token("|"), meta), Self::parse_term_prec9),
      move || term.clone(),
      |lhs, rhs| Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::BitOr, rhs })),
    )(tokens)
  }

  fn parse_term_prec13<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec10(tokens)?;

    // Parse ternary.
    if let Ok((tokens, _)) = delimited(meta, token("?"), meta)(tokens) {
      let (tokens, if_branch) = Self::parse_term_prec7(tokens)?;
      let (tokens, _) = delimited(meta, token(":"), meta)(tokens)?;
      let (tokens, else_branch) = Self::parse_term_prec7(tokens)?;
      return Ok((tokens, Self::Ternary(Box::new(term), Box::new(if_branch), Box::new(else_branch))))
    }

    Ok((tokens, term))
  }

  fn parse_term_prec14<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec13(tokens)?;

    fold_many0(
      pair(
        delimited(
          meta,
          alt((
            value(BinaryOp::Assign, token("=")),
            value(BinaryOp::AddAssign, token("+=")),
            value(BinaryOp::SubAssign, token("-=")),
            value(BinaryOp::MulAssign, token("*=")),
            value(BinaryOp::DivAssign, token("/=")),
            value(BinaryOp::RemAssign, token("%=")),
            value(BinaryOp::ShlAssign, token("<<=")),
            value(BinaryOp::ShrAssign, token(">>=")),
            value(BinaryOp::BitAndAssign, token("&=")),
            value(BinaryOp::BitXorAssign, token("^=")),
            value(BinaryOp::BitOrAssign, token("|=")),
          )),
          meta,
        ),
        Self::parse_term_prec14,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(Box::new(BinaryExpr { lhs, op, rhs })),
    )(tokens)
  }

  /// Parse an expression.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    Self::parse_term_prec14(tokens)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match self {
      Self::Cast { expr, ty } => {
        expr.finish(ctx)?;

        // Handle ambiguous cast vs. binary operation, e.g. `(ty)&var` vs `(var1) & var2`.
        if let (Self::Unary(expr), Type::Identifier { name, is_struct: false }) = (&**expr, &ty) {
          let treat_as_binop = match **name {
            Self::Arg(_) => {
              // Arguments cannot be resolved as a type.
              true
            },
            Self::Variable { ref name } => {
              // Cannot resolve type.
              ctx.resolve_ty(name.as_str()).is_none()
            },
            _ => true,
          };

          if treat_as_binop {
            let op = match expr.op {
              UnaryOp::Plus => Some(BinaryOp::Add),
              UnaryOp::Minus => Some(BinaryOp::Sub),
              UnaryOp::Deref => Some(BinaryOp::Mul),
              UnaryOp::AddrOf => Some(BinaryOp::BitAnd),
              _ => None,
            };

            if let Some(op) = op {
              let lhs = (**name).clone();
              let rhs = expr.expr.clone();

              *self = Self::Binary(Box::new(BinaryExpr { lhs, op, rhs }));
              return self.finish(ctx)
            }
          }
        }

        // Remove redundant casts from string literals, e.g. `(char*)"adsf"`.
        if matches!(
          (&**expr, &ty), (Expr::Literal(Lit::String(LitString::Ordinary(_))), Type::Ptr { ty, .. })
          if matches!(**ty, Type::BuiltIn(BuiltInType::Char))
        ) {
          *self = (**expr).clone();
          return self.finish(ctx)
        }

        ty.finish(ctx)?;
        Ok(Some(ty.clone()))
      },
      Self::Arg(arg) => {
        if let MacroArgType::Known(arg_ty) = ctx.arg_type_mut(arg.index()) {
          return Ok(Some(arg_ty.clone()))
        }

        Ok(None)
      },
      Self::Variable { ref mut name } => {
        // Built-in macros.
        match name.as_str() {
          "__LINE__" => {
            ctx.export_as_macro = true;

            *self = Self::Cast {
              ty: Type::BuiltIn(BuiltInType::UInt),
              expr: Box::new(Self::Variable { name: name.clone() }),
            };

            Ok(Some(Type::BuiltIn(BuiltInType::UInt)))
          },
          "__FILE__" => {
            ctx.export_as_macro = true;
            Ok(Some(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)), mutable: false }))
          },
          "__SCHAR_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::SChar))),
          "__SHRT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Short))),
          "__INT_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Int))),
          "__LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::Long))),
          "__LONG_LONG_MAX__" => Ok(Some(Type::BuiltIn(BuiltInType::LongLong))),
          _ => Ok(None),
        }
      },
      Self::FunctionCall(call) => {
        let ty = call.finish(ctx)?;

        match *call.name {
          Self::Variable { ref name } if ctx.function(name.as_str()).is_some() => Ok(ty),
          _ => {
            // Type should only be set if calling an actual function, not a function macro.
            Ok(ty)
          },
        }
      },
      // Convert character literals to casts.
      Self::Literal(lit) if matches!(lit, Lit::Char(..)) => {
        let ty = lit.finish(ctx)?;
        *self = Self::Cast { expr: Box::new(Self::Literal(lit.clone())), ty: ty.clone().unwrap() };
        Ok(ty)
      },
      Self::Literal(lit) => lit.finish(ctx),
      Self::FieldAccess { expr, field } => {
        expr.finish(ctx)?;
        field.finish(ctx)?;

        if let Self::Arg(ref arg) = **field {
          *ctx.arg_type_mut(arg.index()) = MacroArgType::Ident;
        }

        Ok(None)
      },
      Self::ArrayAccess { expr, index } => {
        let expr_ty = expr.finish(ctx)?;
        index.finish(ctx)?;

        match expr_ty {
          Some(Type::Ptr { ty, .. }) => Ok(Some(*ty)),
          None => Ok(None),
          // Type can only be either a pointer-type or unknown.
          _ => Err(crate::CodegenError::UnsupportedExpression),
        }
      },
      Self::Stringify(stringify) => stringify.finish(ctx),
      Self::ConcatIdent(ref mut ids) => {
        for id in ids {
          id.finish(ctx)?;

          match id {
            Self::Arg(arg) => {
              // `concat_idents!` arguments must be `ident`.
              *ctx.arg_type_mut(arg.index()) = MacroArgType::Ident;
            },
            Self::Variable { .. } => (),
            Self::Literal(Lit::Int(LitInt { suffix: None, value })) if *value >= 0 => {
              // NOTE: Not yet supported by the `concat_idents!` macro.
              return Err(crate::CodegenError::UnsupportedExpression)
            },
            _ => {
              // Only `Arg`, `Variable`, and `Literal` are ever added to `ConcatIdent`.
              unreachable!()
            },
          }
        }

        Ok(None)
      },
      Self::ConcatString(names) => {
        let mut new_names = vec![];
        let mut current_name: Option<Vec<u8>> = None;

        for name in &mut *names {
          name.finish(ctx)?;

          if let Self::Literal(Lit::String(lit)) = name {
            if let Some(lit_bytes) = lit.as_bytes() {
              if let Some(ref mut current_name) = current_name {
                current_name.extend_from_slice(lit_bytes);
              } else {
                current_name = Some(lit_bytes.to_vec());
              }
              continue
            } else {
              // FIXME: Cannot concatenate wide strings due to unknown size of `wchar_t`.
              return Err(crate::CodegenError::UnsupportedExpression)
            }
          }

          if let Some(current_name) = current_name.take() {
            new_names.push(Self::Literal(Lit::String(LitString::Ordinary(current_name))));
          }

          new_names.push(name.clone());
        }

        if let Some(current_name) = current_name.take() {
          new_names.push(Self::Literal(Lit::String(LitString::Ordinary(current_name))));
        }

        if new_names.len() == 1 {
          *self = new_names.remove(0);
          self.finish(ctx)
        } else {
          *self = Self::ConcatString(new_names);
          Ok(Some(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)), mutable: false }))
        }
      },
      Self::Unary(op) => {
        let ty = op.finish(ctx)?;

        match (op.op, &op.expr) {
          (UnaryOp::Plus, expr @ Self::Literal(Lit::Int(_)) | expr @ Self::Literal(Lit::Float(_))) => {
            *self = expr.clone();
          },
          (UnaryOp::Minus, Self::Literal(Lit::Int(LitInt { value: i, suffix }))) => {
            let suffix = match suffix {
              Some(BuiltInType::UChar | BuiltInType::SChar) => Some(BuiltInType::SChar),
              Some(BuiltInType::UInt | BuiltInType::Int) => Some(BuiltInType::Int),
              Some(BuiltInType::ULong | BuiltInType::Long) => Some(BuiltInType::Long),
              Some(BuiltInType::ULongLong | BuiltInType::LongLong) => Some(BuiltInType::LongLong),
              _ => None,
            };
            *self = Self::Literal(Lit::Int(LitInt { value: i.wrapping_neg(), suffix }));
          },
          (UnaryOp::Minus, Self::Literal(Lit::Float(f))) => {
            *self = Self::Literal(Lit::Float(match f {
              LitFloat::Float(f) => LitFloat::Float(-f),
              LitFloat::Double(f) => LitFloat::Double(-f),
              LitFloat::LongDouble(f) => LitFloat::LongDouble(-f),
            }));
          },
          (UnaryOp::Not, Self::Literal(Lit::Int(LitInt { value: i, suffix: None }))) => {
            *self = Self::Literal(Lit::Int(LitInt { value: (*i == 0).into(), suffix: None }));
          },
          (UnaryOp::Not, Self::Literal(Lit::Float(f))) => {
            *self = Self::Literal(Lit::Int(LitInt {
              value: match f {
                LitFloat::Float(f) => *f == 0.0,
                LitFloat::Double(f) => *f == 0.0,
                LitFloat::LongDouble(f) => *f == 0.0,
              } as i128,
              suffix: None,
            }));
          },
          (UnaryOp::Not, expr) => {
            if ty != Some(Type::BuiltIn(BuiltInType::Bool)) {
              let lhs = expr.clone();
              let rhs = match ty {
                Some(Type::BuiltIn(BuiltInType::Float)) => Self::Literal(Lit::Float(LitFloat::Float(0.0))),
                Some(Type::BuiltIn(BuiltInType::Double)) => Self::Literal(Lit::Float(LitFloat::Double(0.0))),
                Some(Type::BuiltIn(BuiltInType::LongDouble)) => Self::Literal(Lit::Float(LitFloat::LongDouble(0.0))),
                _ => Self::Literal(Lit::Int(LitInt { value: 0, suffix: None })),
              };

              *self = Self::Binary(Box::new(BinaryExpr { lhs, op: BinaryOp::Eq, rhs }))
            }
          },
          (UnaryOp::Comp, Self::Literal(Lit::Float(_) | Lit::String(_))) => {
            return Err(crate::CodegenError::UnsupportedExpression)
          },
          _ => (),
        }

        Ok(ty)
      },
      Self::Binary(op) => {
        let (lhs_ty, rhs_ty) = op.finish(ctx)?;

        // Calculate numeric expression.
        match (op.op, &op.lhs, &op.rhs) {
          (BinaryOp::Mul, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs * *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Mul, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs * *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Div, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs / *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Div, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs / *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Rem, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs % *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Add, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs + *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Add, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs + *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Sub, Self::Literal(Lit::Float(lhs)), Self::Literal(Lit::Float(rhs))) => {
            *self = Self::Literal(Lit::Float(*lhs - *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Sub, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs - *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Shl, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs << *rhs));
            self.finish(ctx)
          },
          (BinaryOp::Shr, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs >> *rhs));
            self.finish(ctx)
          },
          (BinaryOp::BitAnd, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs & *rhs));
            self.finish(ctx)
          },
          (BinaryOp::BitOr, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs | *rhs));
            self.finish(ctx)
          },
          (BinaryOp::BitXor, Self::Literal(Lit::Int(lhs)), Self::Literal(Lit::Int(rhs))) => {
            *self = Self::Literal(Lit::Int(*lhs ^ *rhs));
            self.finish(ctx)
          },
          (
            BinaryOp::Eq
            | BinaryOp::Neq
            | BinaryOp::And
            | BinaryOp::Or
            | BinaryOp::Lt
            | BinaryOp::Lte
            | BinaryOp::Gt
            | BinaryOp::Gte,
            _,
            _,
          ) => Ok(Some(Type::BuiltIn(BuiltInType::Bool))),
          _ => {
            if lhs_ty == rhs_ty {
              Ok(lhs_ty)
            } else {
              Ok(lhs_ty.xor(rhs_ty))
            }
          },
        }
      },
      Self::Ternary(cond, if_branch, else_branch) => {
        cond.finish(ctx)?;
        let lhs_ty = if_branch.finish(ctx)?;
        let rhs_ty = else_branch.finish(ctx)?;

        if lhs_ty == rhs_ty {
          Ok(lhs_ty)
        } else {
          Ok(lhs_ty.xor(rhs_ty))
        }
      },
      Self::Asm(asm) => asm.finish(ctx),
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    match self {
      Self::Cast { ref expr, ref ty } => tokens.append_all(match (ty, &**expr) {
        (Type::Ptr { mutable, .. }, Expr::Literal(Lit::Int(LitInt { value: 0, .. }))) => {
          let prefix = ctx.trait_prefix().into_iter();

          if *mutable {
            quote! { #(#prefix::)*ptr::null_mut() }
          } else {
            quote! { #(#prefix::)*ptr::null() }
          }
        },
        (ty, expr) => {
          if ty.is_void() {
            let expr = expr.to_token_stream(ctx);
            quote! { { drop(#expr) } }
          } else {
            let (prec, _) = self.precedence();
            let (expr_prec, _) = expr.precedence();

            let expr = match expr {
              // When casting a negative integer, we need to generate it with a suffix, since
              // directly casting to an unsigned integer (i.e. `-1 as u32`) doesn't work.
              // The same is true when casting a big number to a type which is too small,
              // so we output the number with the smallest possible explicit type.
              Expr::Literal(Lit::Int(LitInt { value, .. })) => {
                let expr = if *value < i64::MIN as i128 {
                  Literal::i128_suffixed(*value)
                } else if *value < i32::MIN as i128 {
                  Literal::i64_suffixed(*value as i64)
                } else if *value < i16::MIN as i128 {
                  Literal::i32_suffixed(*value as i32)
                } else if *value < i8::MIN as i128 {
                  Literal::i16_suffixed(*value as i16)
                } else if *value < 0 {
                  Literal::i8_suffixed(*value as i8)
                } else if *value <= u8::MAX as i128 {
                  Literal::u8_suffixed(*value as u8)
                } else if *value <= u16::MAX as i128 {
                  Literal::u16_suffixed(*value as u16)
                } else if *value <= u32::MAX as i128 {
                  Literal::u32_suffixed(*value as u32)
                } else if *value <= u64::MAX as i128 {
                  Literal::u64_suffixed(*value as u64)
                } else {
                  Literal::i128_suffixed(*value)
                };

                quote! { #expr }
              },
              _ => {
                let mut expr = expr.to_token_stream(ctx);
                if expr_prec > prec {
                  expr = quote! { (#expr) };
                }
                expr
              },
            };

            let ty = ty.to_token_stream(ctx);
            quote! { #expr as #ty }
          }
        },
      }),
      Self::Arg(arg) => tokens.append_all(match ctx.arg_name(arg.index()) {
        "..." => quote! { $($__VA_ARGS__),* },
        name => {
          let name = Ident::new(name, Span::call_site());

          if ctx.export_as_macro {
            quote! { $#name }
          } else {
            quote! { #name }
          }
        },
      }),
      Self::Variable { ref name } => {
        let prefix = ctx.ffi_prefix().into_iter();

        tokens.append_all(match name.as_str() {
          "__LINE__" => quote! { line!() },
          "__FILE__" => {
            let ffi_prefix = ctx.ffi_prefix().into_iter();
            let trait_prefix = ctx.trait_prefix().into_iter();

            quote! {
              {
                const BYTES: &[u8] = #(#trait_prefix::)*concat!(file!(), '\0').as_bytes();
                BYTES.as_ptr() as *const #(#ffi_prefix::)*c_char
              }
            }
          },
          "__SCHAR_MAX__" => quote! { #(#prefix::)*c_schar::MAX },
          "__SHRT_MAX__" => quote! { #(#prefix::)*c_short::MAX },
          "__INT_MAX__" => quote! { #(#prefix::)*c_int::MAX },
          "__LONG_MAX__" => quote! { #(#prefix::)*c_long::MAX },
          "__LONG_LONG_MAX__" => quote! { #(#prefix::)*c_longlong::MAX },
          name => {
            let name = Ident::new(name, Span::call_site());
            quote! { #name }
          },
        })
      },
      Self::FunctionCall(ref call) => {
        call.to_tokens(ctx, tokens);
      },
      Self::Literal(ref lit) => lit.to_tokens(ctx, tokens),
      Self::FieldAccess { ref expr, ref field } => {
        let (prec, _) = self.precedence();
        let (expr_prec, _) = expr.precedence();

        let mut expr = expr.to_token_stream(ctx);
        if expr_prec > prec {
          expr = quote! { (#expr) };
        }

        let field = field.to_token_stream(ctx);

        tokens.append_all(format!("{}.{}", expr, field).parse::<TokenStream>().unwrap())
      },
      Self::ArrayAccess { ref expr, ref index } => {
        let (expr_prec, _) = expr.precedence();

        let mut expr = expr.to_token_stream(ctx);
        // `self.precedence()` does not work here since array access is represented
        // as a method call followed by a dereference.
        if expr_prec > 1 {
          expr = quote! { (#expr) };
        }

        let index = index.to_token_stream(ctx);
        tokens.append_all(quote! { *#expr.offset(#index) })
      },
      Self::Stringify(stringify) => {
        stringify.to_tokens(ctx, tokens);
      },
      Self::ConcatIdent(ids) => {
        let trait_prefix = ctx.trait_prefix().into_iter();
        let ids = ids.iter().map(|id| id.to_token_stream(ctx));
        tokens.append_all(quote! { #(#trait_prefix::)*concat_idents!(#(#ids),*) })
      },
      Self::ConcatString(ref names) => {
        let ffi_prefix = ctx.ffi_prefix().into_iter();
        let trait_prefix = ctx.trait_prefix().into_iter();

        let names = names
          .iter()
          .map(|e| match e {
            Self::Variable { name } => match name.as_str() {
              "__FILE__" => quote! { file!() },
              _ => e.to_token_stream(ctx),
            },
            Self::Stringify(stringify) => stringify.to_token_stream_inner(ctx),
            e => e.to_token_stream(ctx),
          })
          .collect::<Vec<_>>();

        tokens.append_all(quote! {
          {
            const BYTES: &[u8] = #(#trait_prefix::)*concat!(#(#names),*, '\0').as_bytes();
            BYTES.as_ptr() as *const #(#ffi_prefix::)*c_char
          }
        })
      },
      Self::Unary(op) => op.to_tokens(ctx, tokens),
      Self::Binary(op) => op.to_tokens(ctx, tokens),
      Self::Ternary(ref cond, ref if_branch, ref else_branch) => {
        let cond = cond.to_token_stream(ctx);
        let if_branch = if_branch.to_token_stream(ctx);
        let else_branch = else_branch.to_token_stream(ctx);

        tokens.append_all(quote! {
          if #cond {
            #if_branch
          } else {
            #else_branch
          }
        })
      },
      Self::Asm(ref asm) => asm.to_tokens(ctx, tokens),
    }
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use crate::macro_set::{arg as macro_arg, id as macro_id, tokens};

  #[test]
  fn parse_literal() {
    let (_, expr) = Expr::parse(tokens![macro_id!(u8), "'a'"]).unwrap();
    assert_eq!(expr, lit!(u8 'a'));

    let (_, expr) = Expr::parse(tokens!["U'🍩'"]).unwrap();
    assert_eq!(expr, lit!(U '🍩'));
  }

  #[test]
  fn parse_stringify() {
    let (_, expr) = Expr::parse(tokens!["#", macro_arg!(0)]).unwrap();
    assert_eq!(expr, Expr::Stringify(Stringify { arg: Box::new(arg!(0)) }));
  }

  #[test]
  fn parse_concat() {
    let (_, expr) = Expr::parse(tokens![r#""abc""#, r#""def""#]).unwrap();
    assert_eq!(expr, Expr::Literal(Lit::String(LitString::Ordinary("abcdef".into()))));

    let (_, expr) = Expr::parse(tokens![r#""def""#, "#", macro_arg!(0)]).unwrap();
    assert_eq!(
      expr,
      Expr::ConcatString(vec![
        Expr::Literal(Lit::String(LitString::Ordinary("def".into()))),
        Expr::Stringify(Stringify { arg: Box::new(arg!(0)) }),
      ])
    );
  }

  #[test]
  fn parse_concat_ident() {
    let (_, id) = Expr::parse(tokens![macro_arg!(0), "##", macro_id!(def)]).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(0), var!(def)]));

    let (_, id) = Expr::parse(tokens![macro_arg!(0), "##", macro_id!(def), "##", macro_id!(ghi)]).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(0), var!(def), var!(ghi)]));

    let (_, id) = Expr::parse(tokens![macro_arg!(0), "##", macro_id!(_def)]).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(0), var!(_def)]));

    let (_, id) = Expr::parse(tokens![macro_arg!(0), "##", "123"]).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(0), lit!(123)]));

    let (_, id) = Expr::parse(tokens![macro_arg!(0), "##", "123def"]).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(0), lit!(123), var!(def)]));

    let (_, id) = Expr::parse(tokens![macro_arg!(0), "##", "123def456ghi"]).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![arg!(0), lit!(123), var!(def456ghi)]));

    let (_, id) = Expr::parse(tokens![macro_id!(__INT), "##", macro_id!(_MAX__)]).unwrap();
    assert_eq!(id, Expr::ConcatIdent(vec![var!(__INT), var!(_MAX__)]));
  }

  #[test]
  fn parse_field_access() {
    let (_, expr) = Expr::parse(tokens![macro_id!(a), ".", macro_id!(b)]).unwrap();
    assert_eq!(expr, Expr::FieldAccess { expr: Box::new(var!(a)), field: Box::new(var!(b)) });
  }

  #[test]
  fn parse_pointer_access() {
    let (_, expr) = Expr::parse(tokens![macro_id!(a), "->", macro_id!(b)]).unwrap();
    assert_eq!(
      expr,
      Expr::FieldAccess {
        expr: Box::new(Expr::Unary(Box::new(UnaryExpr { op: UnaryOp::Deref, expr: var!(a) }))),
        field: Box::new(var!(b))
      }
    );
  }

  #[test]
  fn parse_array_access() {
    let (_, expr) = Expr::parse(tokens![macro_id!(a), "[", "0", "]"]).unwrap();
    assert_eq!(expr, Expr::ArrayAccess { expr: Box::new(var!(a)), index: Box::new(lit!(0)) });

    let (_, expr) = Expr::parse(tokens![macro_id!(a), "[", "0", "]", "[", "1", "]"]).unwrap();
    assert_eq!(
      expr,
      Expr::ArrayAccess {
        expr: Box::new(Expr::ArrayAccess { expr: Box::new(var!(a)), index: Box::new(lit!(0)) }),
        index: Box::new(lit!(1))
      }
    );

    let (_, expr) = Expr::parse(tokens![macro_id!(a), "[", macro_id!(b), "]"]).unwrap();
    assert_eq!(expr, Expr::ArrayAccess { expr: Box::new(var!(a)), index: Box::new(var!(b)) });
  }

  #[test]
  fn parse_assignment() {
    let (_, expr) = Expr::parse(tokens![macro_id!(a), "=", macro_id!(b), "=", macro_id!(c)]).unwrap();
    assert_eq!(
      expr,
      Expr::Binary(Box::new(BinaryExpr {
        lhs: var!(a),
        op: BinaryOp::Assign,
        rhs: Expr::Binary(Box::new(BinaryExpr { lhs: var!(b), op: BinaryOp::Assign, rhs: var!(c) }),),
      }))
    );
  }

  #[test]
  fn parse_function_call() {
    let (_, expr) =
      Expr::parse(tokens![macro_id!(my_function), "(", macro_id!(arg1), ",", macro_id!(arg2), ")"]).unwrap();
    assert_eq!(
      expr,
      Expr::FunctionCall(FunctionCall { name: Box::new(var!(my_function)), args: vec![var!(arg1), var!(arg2)] })
    );
  }

  #[test]
  fn parse_paren() {
    let (_, expr) = Expr::parse(tokens!["(", "-", "123456789012ULL", ")"]).unwrap();
    assert_eq!(
      expr,
      Expr::Unary(Box::new(UnaryExpr {
        op: UnaryOp::Minus,
        expr: Expr::Literal(Lit::Int(LitInt { value: 123456789012, suffix: Some(BuiltInType::ULongLong) }))
      }))
    )
  }
}
