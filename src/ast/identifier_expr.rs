use std::{borrow::Cow, fmt::Debug};

use nom::{
  branch::alt,
  character::complete::char,
  combinator::{map, map_opt, value},
  multi::{fold_many0, many1},
  sequence::{delimited, preceded},
  IResult,
};
use proc_macro2::TokenStream;
use quote::{quote, TokenStreamExt};

use super::{
  tokens::{macro_arg, macro_id},
  *,
};
use crate::{CodegenContext, LocalContext, MacroArgType, MacroToken};

/// An identifier expression.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum IdentifierExpr<'t> {
  /// A macro argument in identifier position.
  Arg(MacroArg),
  /// A plain identifier.
  Plain(Identifier<'t>),
  /// Concatenation of identifiers.
  Concat(Vec<IdentifierContinuationExpr<'t>>),
}

impl<'t> IdentifierExpr<'t> {
  /// Parse identifier concatenation, e.g. `arg ## 2`.
  pub(crate) fn parse_concat_ident<'i>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Self> {
    let (tokens, id) = alt((map(macro_arg, Self::Arg), map(macro_id, Self::Plain)))(tokens)?;

    fold_many0(
      preceded(
        delimited(meta, punct("##"), meta),
        alt((
          map(macro_arg, |arg| vec![IdentifierContinuationExpr::Arg(arg)]),
          map(macro_id, |id| vec![IdentifierContinuationExpr::Plain(id)]),
          // Split non-identifiers, e.g. `123def` into integer literals and identifiers.
          map_opt(take_one, |token| {
            fn unsuffixed_int<'e>(input: &str) -> IResult<&str, IdentifierContinuationExpr<'e>> {
              let map_lit_int = |i: u64| (IdentifierContinuationExpr::Int(LitInt { value: i.into(), suffix: None }));
              alt((
                // Keep leading zeros.
                map(value(0, char('0')), map_lit_int),
                map(nom::character::complete::u64, map_lit_int),
              ))(input)
            }

            let (_, ids) = match token {
              MacroToken::IdentifierContinue(IdentifierContinue { id_cont: Cow::Borrowed(token2) }) => {
                many1(alt((
                  unsuffixed_int,
                  map_opt(Identifier::parse_str, |id| Some(IdentifierContinuationExpr::Plain(id))),
                )))(token2)
                .ok()?
              },
              MacroToken::IdentifierContinue(IdentifierContinue { id_cont: Cow::Owned(token2) }) => {
                many1(alt((
                  unsuffixed_int,
                  map_opt(Identifier::parse_str, |id| Some(IdentifierContinuationExpr::Plain(id.to_static()))),
                )))(token2.as_ref())
                .ok()?
              },
              _ => return None,
            };

            Some(ids)
          }),
        )),
      ),
      move || id.clone(),
      |acc, mut item| match acc {
        Self::Arg(arg) => {
          item.insert(0, IdentifierContinuationExpr::Arg(arg));
          Self::Concat(item)
        },
        Self::Plain(id) => {
          item.insert(0, IdentifierContinuationExpr::Plain(id));
          Self::Concat(item)
        },
        Self::Concat(mut ids) => {
          ids.extend(item);
          Self::Concat(ids)
        },
      },
    )(tokens)
  }

  pub(crate) fn finish<C>(&mut self, ctx: &mut LocalContext<'_, 't, C>) -> Result<Option<Type<'t>>, crate::CodegenError>
  where
    C: CodegenContext,
  {
    match self {
      Self::Arg(_arg) => {
        // *ctx.arg_type_mut(arg.index()) = MacroArgType::Ident;
        Ok(None)
      },
      Self::Plain(_) => Ok(None),
      Self::Concat(ids) => {
        for id in ids {
          match id {
            IdentifierContinuationExpr::Arg(arg) => {
              // `concat_idents!` arguments must be `ident`.
              *ctx.arg_type_mut(arg.index()) = MacroArgType::Ident;
            },
            IdentifierContinuationExpr::Plain(_) => (),
            IdentifierContinuationExpr::Int(LitInt { suffix: None, value }) if *value >= 0 => {
              // NOTE: Not yet supported by the `concat_idents!` macro.
              return Err(crate::CodegenError::UnsupportedExpression(
                "concatenation of identifiers and literals".to_owned(),
              ))
            },
            _ => unreachable!(),
          }
        }

        Ok(None)
      },
    }
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let mut tokens = TokenStream::new();
    self.to_tokens(ctx, &mut tokens);
    tokens
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>, tokens: &mut TokenStream) {
    match self {
      Self::Arg(arg) => arg.to_tokens(ctx, tokens),
      Self::Plain(id) => id.to_tokens(ctx, tokens),
      Self::Concat(ids) => {
        let trait_prefix = ctx.trait_prefix().into_iter();
        let ids = ids.iter().map(|id| id.to_token_stream(ctx));
        tokens.append_all(quote! { #(#trait_prefix::)*concat_idents!(#(#ids),*) })
      },
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum IdentifierContinuationExpr<'t> {
  /// A macro argument in identifier position.
  Arg(MacroArg),
  /// A plain identifier.
  Plain(Identifier<'t>),
  /// An integer.
  Int(LitInt),
}

impl<'t> IdentifierContinuationExpr<'t> {
  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, 't, C>) -> TokenStream {
    let mut tokens = TokenStream::new();

    match self {
      Self::Arg(arg) => arg.to_tokens(ctx, &mut tokens),
      Self::Plain(id) => id.to_tokens(ctx, &mut tokens),
      Self::Int(int) => int.to_tokens(ctx, &mut tokens),
    }
    tokens
  }
}
