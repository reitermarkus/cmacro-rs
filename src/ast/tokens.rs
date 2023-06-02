use nom::{
  combinator::{map_opt, value, verify},
  multi::many0,
  sequence::{delimited, pair},
  IResult, Parser,
};

use crate::MacroToken;

use super::{Comment, Identifier, MacroArg};

pub(crate) fn macro_arg<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], MacroArg> {
  map_opt(take_one, |token| if let MacroToken::Arg(macro_arg) = token { Some(macro_arg.clone()) } else { None })(tokens)
}

pub(crate) fn macro_id<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Identifier<'t>> {
  map_opt(take_one, |token| if let MacroToken::Identifier(id) = token { Some(id.clone()) } else { None })(tokens)
}

pub(crate) fn take_one<I>(tokens: &[I]) -> IResult<&[I], &I>
where
  I: Clone,
{
  if let Some((first, tokens)) = tokens.split_first() {
    return Ok((tokens, first))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn comment<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'i Comment<'t>> {
  map_opt(take_one, |token| match token {
    MacroToken::Comment(comment) => Some(comment),
    _ => None,
  })(tokens)
}

pub(crate) fn meta<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Vec<&'i Comment<'t>>> {
  many0(comment)(input)
}

pub(crate) fn punct<'i, 't>(
  punct: &'static str,
) -> impl Fn(&'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'static str>
where
  't: 'i,
{
  move |tokens| {
    value(
      punct,
      verify(take_one, move |token| if let MacroToken::Punctuation(p) = token { punct == *p } else { false }),
    )(tokens)
  }
}

pub(crate) fn id<'i, 't>(
  id: &'static str,
) -> impl Fn(&'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'static str>
where
  't: 'i,
{
  move |tokens| {
    value(
      id,
      verify(take_one, move |token| {
        if let MacroToken::Identifier(identifier) = token {
          identifier.id.as_ref() == id
        } else {
          false
        }
      }),
    )(tokens)
  }
}

pub(crate) use id as keyword;

pub(crate) fn parenthesized<'i, 't, O, F>(
  f: F,
) -> impl FnMut(&'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], O, nom::error::Error<&'i [MacroToken<'t>]>>
where
  't: 'i,
  F: Parser<&'i [MacroToken<'t>], O, nom::error::Error<&'i [MacroToken<'t>]>>,
{
  delimited(pair(punct("("), meta), f, pair(meta, punct(")")))
}
