use std::{borrow::Cow, fmt::Debug};

use nom::{
  branch::alt,
  character::complete::char,
  combinator::{map, map_opt, map_res, value},
  multi::{fold_many0, many1, separated_list0},
  sequence::{delimited, pair, preceded, terminated, tuple},
  IResult,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};

use super::{
  tokens::{macro_arg, macro_id, parenthesized},
  *,
};
use crate::{CodegenContext, LocalContext, MacroArgType, MacroToken, UnaryOp};

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Expr<'t> {
  Arg(MacroArg),
  Var(Var<'t>),
  FunctionCall(FunctionCall<'t>),
  Cast(Cast<'t>),
  Literal(Lit<'t>),
  Stringify(Stringify<'t>),
  ConcatIdent(Vec<Self>),
  ConcatString(Vec<Self>),
  SizeOf(Type<'t>),
  Unary(UnaryExpr<'t>),
  Binary(BinaryExpr<'t>),
  Ternary(TernaryExpr<'t>),
}

impl<'t> Expr<'t> {
  pub(crate) const fn precedence(&self) -> (u8, Associativity) {
    match self {
      Self::Literal(_) | Self::Arg(_) | Self::Var(_) | Self::ConcatIdent(_) => (0, Associativity::None),
      Self::FunctionCall(_) => (1, Associativity::Left),
      Self::Stringify(_) | Self::ConcatString(_) => (3, Associativity::Left),
      Self::Cast(cast) => cast.precedence(),
      Self::Unary(expr) => expr.precedence(),
      Self::Binary(expr) => expr.precedence(),
      Self::Ternary(_) => (0, Associativity::None),
      Self::SizeOf(_) => (3, Associativity::Left), // Same as `Cast`.
    }
  }

  /// Parse identifier concatenation, e.g. `arg ## 2`.
  pub(crate) fn parse_concat_ident<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, id) = alt((map(macro_arg, Self::Arg), map(macro_id, |id| Self::Var(Var { name: id }))))(tokens)?;

    fold_many0(
      preceded(
        delimited(meta, punct("##"), meta),
        alt((
          map(macro_arg, Self::Arg),
          map(macro_id, |id| Self::Var(Var { name: id })),
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
              MacroToken::IdentifierContinue(IdentifierContinue { id_cont: Cow::Borrowed(token2) }) => {
                many1(alt((unsuffixed_int, map_opt(Identifier::parse_str, |id| Some(Self::Var(Var { name: id }))))))(
                  token2,
                )
                .ok()?
              },
              MacroToken::IdentifierContinue(IdentifierContinue { id_cont: Cow::Owned(token2) }) => {
                many1(alt((
                  unsuffixed_int,
                  map_opt(Identifier::parse_str, |id| Some(Self::Var(Var { name: id.to_static() }))),
                )))(token2.as_ref())
                .ok()?
              },
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
      map(preceded(keyword("sizeof"), parenthesized(Type::parse)), Self::SizeOf),
      map(LitChar::parse, |c| Self::Literal(Lit::Char(c))),
      Self::parse_concat_string,
      map(Lit::parse, Self::Literal),
      parenthesized(Self::parse),
    ))(tokens)
  }

  fn parse_term_prec1<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, factor) = Self::parse_factor(tokens)?;

    #[derive(Debug)]
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
            map(parenthesized(separated_list0(tuple((meta, punct(","), meta)), Self::parse)), Access::Fn),
            map(preceded(terminated(punct("."), meta), Self::parse_concat_ident), |field| Access::Field {
              field: Box::new(field),
              deref: false,
            }),
            map(delimited(terminated(punct("["), meta), Self::parse, preceded(meta, punct("]"))), |index| {
              Access::Array { index: Box::new(index) }
            }),
            map(preceded(terminated(punct("->"), meta), Self::parse_concat_ident), |field| Access::Field {
              field: Box::new(field),
              deref: true,
            }),
            map(alt((value(UnaryOp::PostInc, punct("++")), value(UnaryOp::PostDec, punct("--")))), |op| {
              Access::UnaryOp(op)
            }),
          )),
        ),
        move || Ok((factor.clone(), false)),
        |acc, access| {
          let (expr, was_unary_postfix_op) = acc?;
          let is_unary_postfix_op = matches!(access, Access::UnaryOp(UnaryOp::PostInc | UnaryOp::PostDec));

          Ok((
            match (expr, access) {
              // Postfix `++`/`--` cannot be chained.
              (expr, Access::UnaryOp(op)) if !was_unary_postfix_op => {
                Self::Unary(UnaryExpr { op, expr: Box::new(expr) })
              },
              // TODO: Support calling expressions as functions.
              (name @ Self::Arg(_) | name @ Self::Var(_), Access::Fn(args)) => {
                Self::FunctionCall(FunctionCall { name: Box::new(name), args })
              },
              // Field access cannot be chained after postfix `++`/`--`.
              (acc, Access::Field { field, deref }) if !was_unary_postfix_op || deref => {
                let acc = if deref { Self::Unary(UnaryExpr { op: UnaryOp::Deref, expr: Box::new(acc) }) } else { acc };
                Self::Binary(BinaryExpr { lhs: Box::new(acc), op: BinaryOp::MemberAccess, rhs: field })
              },
              // Array access cannot be chained after postfix `++`/`--`.
              (acc, Access::Array { index }) if !was_unary_postfix_op => {
                // Array access is an addition followed by dereference.
                Self::Unary(UnaryExpr {
                  op: UnaryOp::Deref,
                  expr: Box::new(Self::Binary(BinaryExpr { lhs: Box::new(acc), op: BinaryOp::Add, rhs: index })),
                })
              },
              _ => return Err(()),
            },
            is_unary_postfix_op,
          ))
        },
      ),
      |res| res.map(|(expr, _)| expr),
    )(tokens)
  }

  fn parse_term_prec2<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    alt((
      map(pair(parenthesized(Type::parse), Self::parse_term_prec2), |(ty, term)| {
        Self::Cast(Cast { ty, expr: Box::new(term) })
      }),
      map(
        pair(
          terminated(
            alt((
              value(UnaryOp::Deref, punct("*")),
              value(UnaryOp::AddrOf, punct("&")),
              value(UnaryOp::Inc, punct("++")),
              value(UnaryOp::Dec, punct("--")),
              value(UnaryOp::Plus, punct("+")),
              value(UnaryOp::Minus, punct("-")),
              value(UnaryOp::Not, punct("!")),
              value(UnaryOp::Comp, punct("~")),
            )),
            meta,
          ),
          Self::parse_term_prec2,
        ),
        |(op, expr)| Self::Unary(UnaryExpr { op, expr: Box::new(expr) }),
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
          alt((value(BinaryOp::Mul, punct("*")), value(BinaryOp::Div, punct("/")), value(BinaryOp::Rem, punct("%")))),
          meta,
        ),
        Self::parse_term_prec2,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec4<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec3(tokens)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Add, punct("+")), value(BinaryOp::Sub, punct("-")))), meta),
        Self::parse_term_prec3,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec5<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec4(tokens)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Shl, punct("<<")), value(BinaryOp::Shr, punct(">>")))), meta),
        Self::parse_term_prec4,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec6<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec5(tokens)?;

    fold_many0(
      pair(
        delimited(
          meta,
          alt((
            value(BinaryOp::Lt, punct("<")),
            value(BinaryOp::Lte, punct("<=")),
            value(BinaryOp::Gt, punct(">")),
            value(BinaryOp::Gte, punct(">=")),
          )),
          meta,
        ),
        Self::parse_term_prec5,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec7<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec6(tokens)?;

    fold_many0(
      pair(
        delimited(meta, alt((value(BinaryOp::Eq, punct("==")), value(BinaryOp::Neq, punct("!=")))), meta),
        Self::parse_term_prec6,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec8<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec7(tokens)?;

    fold_many0(
      preceded(delimited(meta, punct("&"), meta), Self::parse_term_prec7),
      move || term.clone(),
      |lhs, rhs| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op: BinaryOp::BitAnd, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec9<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec8(tokens)?;

    fold_many0(
      preceded(delimited(meta, punct("^"), meta), Self::parse_term_prec8),
      move || term.clone(),
      |lhs, rhs| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op: BinaryOp::BitXor, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec10<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec9(tokens)?;

    fold_many0(
      preceded(delimited(meta, punct("|"), meta), Self::parse_term_prec9),
      move || term.clone(),
      |lhs, rhs| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op: BinaryOp::BitOr, rhs: Box::new(rhs) }),
    )(tokens)
  }

  fn parse_term_prec13<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, term) = Self::parse_term_prec10(tokens)?;

    // Parse ternary.
    if let Ok((tokens, _)) = delimited(meta, punct("?"), meta)(tokens) {
      let (tokens, if_branch) = Self::parse(tokens)?;
      let (tokens, _) = delimited(meta, punct(":"), meta)(tokens)?;
      let (tokens, else_branch) = Self::parse_term_prec13(tokens)?;
      return Ok((
        tokens,
        Self::Ternary(TernaryExpr {
          condition: Box::new(term),
          if_branch: Box::new(if_branch),
          else_branch: Box::new(else_branch),
        }),
      ))
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
            value(BinaryOp::Assign, punct("=")),
            value(BinaryOp::AddAssign, punct("+=")),
            value(BinaryOp::SubAssign, punct("-=")),
            value(BinaryOp::MulAssign, punct("*=")),
            value(BinaryOp::DivAssign, punct("/=")),
            value(BinaryOp::RemAssign, punct("%=")),
            value(BinaryOp::ShlAssign, punct("<<=")),
            value(BinaryOp::ShrAssign, punct(">>=")),
            value(BinaryOp::BitAndAssign, punct("&=")),
            value(BinaryOp::BitXorAssign, punct("^=")),
            value(BinaryOp::BitOrAssign, punct("|=")),
          )),
          meta,
        ),
        Self::parse_term_prec14,
      ),
      move || term.clone(),
      |lhs, (op, rhs)| Self::Binary(BinaryExpr { lhs: Box::new(lhs), op, rhs: Box::new(rhs) }),
    )(tokens)
  }

  /// Parse an expression.
  pub(crate) fn parse<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    Self::parse_term_prec14(tokens)
  }

  pub(crate) fn finish_condition<C>(
    &mut self,
    ctx: &mut LocalContext<'_, 't, C>,
  ) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    let ty = Some(Type::BuiltIn(BuiltInType::Bool));

    if self.finish(ctx)? != ty {
      *self = Expr::Binary(BinaryExpr {
        lhs: Box::new(self.clone()),
        op: BinaryOp::Neq,
        rhs: Box::new(Expr::Literal(Lit::Int(LitInt { value: 0, suffix: None }))),
      });
    }

    Ok(ty)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match self {
      Self::Cast(cast) => {
        let ty = cast.finish(ctx)?;

        // Handle ambiguous cast vs. binary operation, e.g. `(ty)&var` vs `(var1) & var2`.
        if let (Self::Unary(expr), Type::Identifier { name, is_struct: false }) = (&*cast.expr, &cast.ty) {
          let treat_as_binop = match **name {
            Self::Arg(_) => {
              // Arguments cannot be resolved as a type.
              true
            },
            Self::Var(Var { ref name }) => {
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

              *self = Self::Binary(BinaryExpr { lhs: Box::new(lhs), op, rhs });
              return self.finish(ctx)
            }
          }
        }

        // Remove redundant casts from string literals, e.g. `(char*)"adsf"`.
        if matches!(
          (&*cast.expr, &cast.ty), (Expr::Literal(Lit::String(LitString::Ordinary(_))), Type::Qualified { ty, qualifier })
          if matches!(&**ty, Type::Ptr { ty, .. } if matches!(**ty, Type::BuiltIn(BuiltInType::Char))) && qualifier.is_const()
        ) {
          *self = (*cast.expr).clone();
          return self.finish(ctx)
        }

        Ok(ty)
      },
      Self::Arg(arg) => {
        if let MacroArgType::Known(arg_ty) = ctx.arg_type_mut(arg.index()) {
          return Ok(Some(arg_ty.clone()))
        }

        Ok(None)
      },
      Self::Var(var) => var.finish(ctx),
      Self::FunctionCall(call) => call.finish(ctx),
      // Convert character literals to casts.
      Self::Literal(lit) if matches!(lit, Lit::Char(..)) => {
        let ty = lit.finish(ctx)?;
        *self = Self::Cast(Cast { expr: Box::new(Self::Literal(lit.clone())), ty: ty.clone().unwrap() });
        Ok(ty)
      },
      Self::Literal(lit) => lit.finish(ctx),
      Self::Stringify(stringify) => stringify.finish(ctx),
      Self::ConcatIdent(ref mut ids) => {
        for id in ids {
          id.finish(ctx)?;

          match id {
            Self::Arg(arg) => {
              // `concat_idents!` arguments must be `ident`.
              *ctx.arg_type_mut(arg.index()) = MacroArgType::Ident;
            },
            Self::Var(_) => (),
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

          match name {
            Self::Literal(Lit::String(lit)) => {
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
            },
            Self::Var { .. } => {
              // Can only concatenate literals.
              return Err(crate::CodegenError::UnsupportedExpression)
            },
            _ => (),
          }

          if let Some(current_name) = current_name.take() {
            new_names.push(Self::Literal(Lit::String(LitString::Ordinary(Cow::Owned(current_name)))));
          }

          new_names.push(name.clone());
        }

        if let Some(current_name) = current_name.take() {
          new_names.push(Self::Literal(Lit::String(LitString::Ordinary(Cow::Owned(current_name)))));
        }

        if new_names.len() == 1 {
          *self = new_names.remove(0);
          self.finish(ctx)
        } else {
          *self = Self::ConcatString(new_names);
          Ok(Some(Type::Qualified {
            ty: Box::new(Type::Ptr { ty: Box::new(Type::BuiltIn(BuiltInType::Char)) }),
            qualifier: TypeQualifier::Const,
          }))
        }
      },
      Self::Unary(op) => {
        let ty = op.finish(ctx)?;

        match (op.op, &*op.expr) {
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

              *self = Self::Binary(BinaryExpr { lhs: Box::new(lhs), op: BinaryOp::Eq, rhs: Box::new(rhs) })
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
        let ty = op.finish(ctx)?;

        // Calculate numeric expression.
        match (op.op, &*op.lhs, &*op.rhs) {
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
          _ => Ok(ty),
        }
      },
      Self::Ternary(expr) => expr.finish(ctx),
      Self::SizeOf(ty) => {
        ty.finish(ctx)?;
        Ok(Some(Type::BuiltIn(BuiltInType::SizeT)))
      },
    }
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    match self {
      Self::Cast(cast) => cast.to_tokens(ctx, tokens),
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
      Self::Var(var) => {
        var.to_tokens(ctx, tokens);
      },
      Self::FunctionCall(ref call) => {
        call.to_tokens(ctx, tokens);
      },
      Self::Literal(ref lit) => lit.to_tokens(ctx, tokens),
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
            Self::Var(Var { name }) => match name.as_str() {
              "__FILE__" => {
                let trait_prefix = ctx.trait_prefix().into_iter();
                quote! { #(#trait_prefix::)*file!() }
              },
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
      Self::Ternary(ref expr) => expr.to_tokens(ctx, tokens),
      Self::SizeOf(ty) => {
        let trait_prefix = ctx.trait_prefix().into_iter();

        let ty = ty.to_token_stream(ctx);
        let size_t = BuiltInType::SizeT.to_token_stream(ctx);

        tokens.append_all(quote! {
          #(#trait_prefix::)*mem::size_of::<#ty>() as #size_t
        })
      },
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

  #[test]
  fn parse_literal() {
    parse_tokens!(Expr => [id!(u8), lit_char!('a')], Expr::Literal(lit_char!(u8 'a')));
    parse_tokens!(Expr => [lit_char!(U '🍩')], Expr::Literal(lit_char!(U '🍩')));
  }

  #[test]
  fn parse_stringify() {
    parse_tokens!(Expr => [punct!("#"), arg!(0)], Expr::Stringify(Stringify { arg: Box::new(Expr::Arg(arg!(0))) }));
  }

  #[test]
  fn parse_concat() {
    parse_tokens!(
      Expr => [lit_string!("abc"), lit_string!("def")],
      Expr::Literal(Lit::String(LitString::Ordinary("abcdef".as_bytes().into())))
    );

    parse_tokens!(
      Expr => [lit_string!("def"), punct!("#"), arg!(0)],
      Expr::ConcatString(vec![
        Expr::Literal(Lit::String(LitString::Ordinary("def".as_bytes().into()))),
        Expr::Stringify(Stringify { arg: Box::new(Expr::Arg(arg!(0))) }),
      ])
    );
  }

  #[test]
  fn parse_concat_ident() {
    parse_tokens!(Expr => [arg!(0), punct!("##"), id!(def)], Expr::ConcatIdent(vec![Expr::Arg(arg!(0)), var!(def)]));

    parse_tokens!(
      Expr => [arg!(0), punct!("##"), id!(def), punct!("##"), id!(ghi)],
      Expr::ConcatIdent(vec![Expr::Arg(arg!(0)), var!(def), var!(ghi)])
    );

    parse_tokens!(Expr => [arg!(0), punct!("##"), id!(_def)], Expr::ConcatIdent(vec![Expr::Arg(arg!(0)), var!(_def)]));

    parse_tokens!(
      Expr => [arg!(0), punct!("##"), id_cont!("123")],
      Expr::ConcatIdent(vec![Expr::Arg(arg!(0)), lit!(123)])
    );

    parse_tokens!(
      Expr => [arg!(0), punct!("##"), id_cont!("123def")],
      Expr::ConcatIdent(vec![Expr::Arg(arg!(0)), lit!(123), var!(def)])
    );

    parse_tokens!(
      Expr => [arg!(0), punct!("##"), id_cont!("123def456ghi")],
      Expr::ConcatIdent(vec![Expr::Arg(arg!(0)), lit!(123), var!(def456ghi)])
    );

    parse_tokens!(Expr => [id!(__INT), punct!("##"), id!(_MAX__)], Expr::ConcatIdent(vec![var!(__INT), var!(_MAX__)]));
  }

  #[test]
  fn parse_field_access() {
    parse_tokens!(
      Expr => [id!(a), punct!("."), id!(b)],
      Expr::Binary(BinaryExpr { lhs: Box::new(var!(a)), op: BinaryOp::MemberAccess, rhs: Box::new(var!(b)) })
    );
  }

  #[test]
  fn parse_pointer_access() {
    parse_tokens!(
      Expr => [id!(a), punct!("->"), id!(b)],
      Expr::Binary(BinaryExpr {
        lhs: Box::new(Expr::Unary(UnaryExpr { op: UnaryOp::Deref, expr: Box::new(var!(a)) })),
        op: BinaryOp::MemberAccess,
        rhs: Box::new(var!(b))
      })
    );
  }

  #[test]
  fn parse_array_access() {
    parse_tokens!(
      Expr => [id!(a), punct!("["), lit_int!(0), punct!("]")],
      Expr::Unary(UnaryExpr {
        op: UnaryOp::Deref,
        expr: Box::new(Expr::Binary(BinaryExpr { lhs: Box::new(var!(a)), op: BinaryOp::Add, rhs: Box::new(lit!(0)) }))
      })
    );

    parse_tokens!(
      Expr => [id!(a), punct!("["), lit_int!(0), punct!("]"), punct!("["), lit_int!(1), punct!("]")],
      Expr::Unary(UnaryExpr {
        op: UnaryOp::Deref,
        expr: Box::new(Expr::Binary(BinaryExpr {
          lhs: Box::new(Expr::Unary(UnaryExpr {
            op: UnaryOp::Deref,
            expr: Box::new(Expr::Binary(BinaryExpr {
              lhs: Box::new(var!(a)),
              op: BinaryOp::Add,
              rhs: Box::new(lit!(0))
            }))
          })),
          op: BinaryOp::Add,
          rhs: Box::new(Expr::Literal(lit_int!(1)))
        }))
      })
    );

    parse_tokens!(
      Expr => [id!(a), punct!("["), id!(b), punct!("]")],
      Expr::Unary(UnaryExpr {
        op: UnaryOp::Deref,
        expr: Box::new(Expr::Binary(BinaryExpr { lhs: Box::new(var!(a)), op: BinaryOp::Add, rhs: Box::new(var!(b)) }))
      })
    );
  }

  #[test]
  fn parse_assignment() {
    parse_tokens!(
      Expr => [id!(a), punct!("="), id!(b), punct!("="), id!(c)],
      Expr::Binary(BinaryExpr {
        lhs: Box::new(var!(a)),
        op: BinaryOp::Assign,
        rhs: Box::new(Expr::Binary(BinaryExpr {
          lhs: Box::new(var!(b)),
          op: BinaryOp::Assign,
          rhs: Box::new(var!(c))
        })),
      })
    );
  }

  #[test]
  fn parse_function_call() {
    parse_tokens!(
      Expr => [id!(my_function), punct!("("), id!(arg1), punct!(","), id!(arg2), punct!(")")],
      Expr::FunctionCall(FunctionCall { name: Box::new(var!(my_function)), args: vec![var!(arg1), var!(arg2)] })
    );
  }

  #[test]
  fn parse_paren() {
    parse_tokens!(
      Expr => [punct!("("), punct!("-"), lit_int!(ull 123456789012), punct!(")")],
      Expr::Unary(UnaryExpr {
        op: UnaryOp::Minus,
        expr: Box::new(Expr::Literal(Lit::Int(LitInt { value: 123456789012, suffix: Some(BuiltInType::ULongLong) })))
      })
    );
  }
}
