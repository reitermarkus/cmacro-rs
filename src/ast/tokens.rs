use std::fmt::Debug;

use nom::{
  bytes::complete::{tag, take_until},
  combinator::{all_consuming, map_opt},
  multi::many0,
  sequence::{delimited, pair},
  Compare, CompareResult, FindSubstring, IResult, InputLength, InputTake, Parser,
};

pub(crate) fn take_one<I>(tokens: &[I]) -> IResult<&[I], I>
where
  I: Debug + Clone,
{
  if !tokens.is_empty() {
    return Ok((&tokens[1..], tokens[0].clone()))
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Eof)))
}

pub(crate) fn comment<I>(tokens: &[I]) -> IResult<&[I], I>
where
  I: Debug + InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone,
{
  let (tokens, token) = take_one(tokens)?;

  let (_, comment) = all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(token)
    .map_err(|err: nom::Err<nom::error::Error<I>>| err.map_input(|_| tokens))?;

  Ok((tokens, comment))
}

pub(crate) fn meta<I>(input: &[I]) -> IResult<&[I], Vec<I>>
where
  I: Debug + InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone,
{
  many0(comment)(input)
}

pub(crate) fn token<I>(token: &'static str) -> impl Fn(&[I]) -> IResult<&[I], &'static str>
where
  I: Debug + InputTake + InputLength + Compare<&'static str> + Clone,
{
  move |tokens: &[I]| {
    map_opt(take_one, |token2: I| {
      let token2 = if token2.input_len() >= 2 && token2.take(2).compare("\\\n") == CompareResult::Ok {
        // TODO: Fix in tokenizer/lexer.
        let (_, token2) = token2.take_split(2);
        token2
      } else {
        token2
      };

      if token2.compare(token) == CompareResult::Ok {
        Some(token)
      } else {
        None
      }
    })(tokens)
  }
}

pub(crate) use token as keyword;

pub(crate) fn parenthesized<'i, I, O, F>(f: F) -> impl FnMut(&'i [I]) -> IResult<&'i [I], O, nom::error::Error<&'i [I]>>
where
  I: Debug + InputTake + InputLength + Compare<&'static str> + FindSubstring<&'static str> + Clone + 'i,
  F: Parser<&'i [I], O, nom::error::Error<&'i [I]>>,
{
  delimited(pair(token("("), meta), f, pair(meta, token(")")))
}
