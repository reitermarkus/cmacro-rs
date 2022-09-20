use quote::TokenStreamExt;

use super::*;

pub(crate) fn identifier<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], &'t str> {
  if let Some(token) = tokens.get(0) {
    let mut it = token.chars();
    if let Some('a'..='z' | 'A'..='Z' | '_') = it.next() {
      if it.all(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9')) {
        return Ok((&tokens[1..], token))
      }
    }
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
}

fn concat_identifier<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], &'t str> {
  if let Some(token) = tokens.get(0) {
    let mut it = token.chars();
    if it.all(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9')) {
      return Ok((&tokens[1..], token))
    }
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
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
  Concat(Vec<String>)
}

impl Identifier {
  pub fn parse<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], Self> {
    let (tokens, id) = identifier(tokens)?;

    fold_many0(
      preceded(
        delimited(meta, token("##"), meta),
        concat_identifier,
      ),
      move || Self::Literal(id.to_owned()),
      |acc, item| {
        match acc {
          Self::Literal(id) => Self::Concat(vec![id.to_owned(), item.to_owned()]),
          Self::Concat(mut ids) => {
            ids.push(item.to_owned());
            Self::Concat(ids)
          }
        }
      }
    )(tokens)
  }

  pub fn visit<'s, 't>(&mut self, ctx: &mut Context<'s, 't>) {
    if let Self::Concat(ref ids) = self {
      for id in ids {
        if let Some(arg_ty) = ctx.args.get_mut(id.as_str()) {
          *arg_ty = MacroArgType::Ident;
          ctx.export_as_macro = true;
        }
      }
    }
  }

  pub fn to_tokens(&self, ctx: &mut Context, tokens: &mut TokenStream) {
    tokens.append_all(self.to_token_stream(ctx))
  }

  pub fn to_token_stream(&self, ctx: &mut Context) -> TokenStream {
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
