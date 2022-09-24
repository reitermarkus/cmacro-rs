use nom::combinator::verify;
use nom::multi::fold_many0;
use nom::sequence::delimited;
use nom::sequence::preceded;
use nom::AsChar;
use nom::Compare;
use nom::FindSubstring;
use nom::IResult;
use nom::InputIter;
use nom::InputLength;
use nom::InputTake;
use proc_macro2::Ident;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::quote;
use quote::TokenStreamExt;

use super::{
  tokens::{meta, take_one, token},
  Type,
};
use crate::{CodegenContext, LocalContext, MacroArgType};

pub(crate) fn identifier<'i, I>(tokens: &'i [I]) -> IResult<&'i [I], String>
where
  I: InputIter + Clone,
  <I as InputIter>::Item: AsChar,
{
  verify(take_one, |token: &I| {
    let mut it = token.iter_elements().map(|i| i.as_char());
    matches!(it.next(), Some('a'..='z' | 'A'..='Z' | '_'))
      && it.all(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'))
  })(tokens)?;

  let s = tokens[0].iter_elements().map(|c| c.as_char()).collect();
  Ok((&tokens[1..], s))
}

fn concat_identifier<'i, I>(tokens: &'i [I]) -> IResult<&'i [I], String>
where
  I: InputIter + Clone,
  <I as InputIter>::Item: AsChar,
{
  verify(take_one, |token: &I| {
    token.iter_elements().all(|c| matches!(c.as_char(), 'a'..='z' | 'A'..='Z' | '_' | '0'..='9'))
  })(tokens)?;

  let s = tokens[0].iter_elements().map(|c| c.as_char()).collect();
  Ok((&tokens[1..], s))
}

/// An identifier.
///
/// ```c
/// #define ID asdf
/// #define ID abc ## def
/// #define ID abc ## 123
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Identifier {
  Literal(String),
  Concat(Vec<String>),
}

impl Identifier {
  pub fn parse<'i, 't, I, T>(tokens: &'i [I]) -> IResult<&'i [I], Self>
  where
    I: InputIter<Item = T> + InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone,
    T: AsChar,
  {
    let (tokens, id) = identifier(tokens)?;

    fold_many0(
      preceded(delimited(meta::<I>, token::<I>("##"), meta::<I>), concat_identifier),
      move || Self::Literal(id.clone()),
      |acc, item| match acc {
        Self::Literal(id) => Self::Concat(vec![id, item]),
        Self::Concat(mut ids) => {
          ids.push(item);
          Self::Concat(ids)
        },
      },
    )(tokens)
  }

  pub(crate) fn finish<'g, C>(&mut self, ctx: &mut LocalContext<'g, C>) -> Result<Option<Type>, crate::Error>
  where
    C: CodegenContext,
  {
    if let Self::Concat(ref mut ids) = self {
      let mut new_ids = vec![];
      let mut non_arg_id: Option<String> = None;

      for id in ids {
        if let Some(arg_ty) = ctx.arg_type_mut(id.as_str()) {
          *arg_ty = MacroArgType::Ident;
          ctx.export_as_macro = true;

          if let Some(non_arg_id) = non_arg_id.take() {
            new_ids.push(non_arg_id);
          }

          new_ids.push(id.to_owned());
        } else if let Some(ref mut non_arg_id) = non_arg_id {
          non_arg_id.push_str(id);
        } else {
          non_arg_id = Some(id.to_owned());
        }
      }

      if new_ids.len() == 1 {
        *self = Self::Literal(new_ids.remove(0));
      } else {
        *self = Self::Concat(new_ids);
      }
    }

    // An identifier does not have a type.
    Ok(None)
  }

  pub(crate) fn to_tokens<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub(crate) fn to_token_stream<C: CodegenContext>(&self, ctx: &mut LocalContext<'_, C>) -> TokenStream {
    match self {
      Self::Literal(ref s) => {
        let id = Ident::new(s, Span::call_site());

        if ctx.is_macro_arg(s) {
          quote! { $#id }
        } else {
          quote! { #id }
        }
      },
      Self::Concat(ids) => {
        let ids = ids.iter().map(|id| Self::Literal(id.to_owned()).to_token_stream(ctx));
        quote! { ::core::concat_idents!(#(#ids),*) }
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_literal() {
    let (_, id) = Identifier::parse(&["asdf"]).unwrap();
    assert_eq!(id, Identifier::Literal("asdf".into()));
  }

  #[test]
  fn parse_concat() {
    let (_, id) = Identifier::parse(&["abc", "##", "def"]).unwrap();
    assert_eq!(id, Identifier::Concat(vec!["abc".into(), "def".into()]));

    let (_, id) = Identifier::parse(&["abc", "##", "123"]).unwrap();
    assert_eq!(id, Identifier::Concat(vec!["abc".into(), "123".into()]));
  }

  #[test]
  fn parse_wrong() {
    let res = Identifier::parse(&["123def"]);
    assert!(res.is_err());

    let res = Identifier::parse(&["123", "##", "def"]);
    assert!(res.is_err());
  }
}
