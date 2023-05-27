use std::{borrow::Cow, fmt::Debug};

use nom::{
  bytes::complete::{tag, take_until},
  combinator::{all_consuming, map_opt, map_parser, opt, value},
  multi::many0,
  sequence::{delimited, pair, preceded}, IResult, Parser,
};

use crate::MacroToken;

pub(crate) fn macro_arg<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], usize> {
  map_opt(take_one_ref, |token| if let MacroToken::Arg(index) = token { Some(*index) } else { None })(tokens)
}

pub(crate) fn macro_token<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Cow<'t, str>> {
  map_opt(take_one_ref, |token| {
    let token = if let MacroToken::Token(token) = token { token } else { return None };
    Some(token.clone())
  })(tokens)
}

pub(crate) fn take_one_ref<I>(tokens: &[I]) -> IResult<&[I], &I>
where
  I: Clone,
{
  if let Some((first, tokens)) = tokens.split_first() {
    return Ok((tokens, first))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn take_one<I>(tokens: &[I]) -> IResult<&[I], I>
where
  I: Debug + Clone,
{
  if let Some((first, tokens)) = tokens.split_first() {
    return Ok((tokens, first.clone()))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn comment<'i, 't>(tokens: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Cow<'t, str>> {
  map_parser(macro_token, |token: Cow<'t, str>| {
    all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(token.as_ref())
      .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))?;

    Ok((Cow::Borrowed(""), token))
  })(tokens)
}

pub(crate) fn meta<'i, 't>(input: &'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], Vec<Cow<'t, str>>> {
  many0(comment)(input)
}

pub(crate) fn token<'i, 't>(
  token: &'static str,
) -> impl Fn(&'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], &'static str>
where
  't: 'i,
{
  move |tokens| {
    map_parser(macro_token, |token2: Cow<'t, str>| {
      all_consuming(preceded(opt(tag("\\\n")), value(token, tag(token))))(token2.as_ref())
        .map_err(|err: nom::Err<nom::error::Error<&str>>| err.map_input(|_| tokens))?;

      Ok((Cow::Borrowed(""), token))
    })(tokens)
  }
}

pub(crate) use token as keyword;

pub(crate) fn parenthesized<'i, 't, O, F>(
  f: F,
) -> impl FnMut(&'i [MacroToken<'t>]) -> IResult<&'i [MacroToken<'t>], O, nom::error::Error<&'i [MacroToken<'t>]>>
where
  't: 'i,
  F: Parser<&'i [MacroToken<'t>], O, nom::error::Error<&'i [MacroToken<'t>]>>,
{
  delimited(pair(token("("), meta), f, pair(meta, token(")")))
}
