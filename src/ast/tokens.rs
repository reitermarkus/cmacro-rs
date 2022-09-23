use nom::multi::many0;
use nom::sequence::delimited;
use nom::IResult;
use nom::bytes::complete::tag;
use nom::combinator::all_consuming;
use nom::bytes::complete::take_until;
use nom::sequence::pair;
use nom::Parser;

pub fn comment<'i, 't>(tokens: &'i [&'t str]) -> IResult<&'i [&'t str], &'t str> {

  if let Some(token) = tokens.first() {
    let token: &str = token;

    let res: IResult<&str, &str> = all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(token);

    if let Ok((_, token)) = res {
      return Ok((&tokens[1..], token))
    }
  }

  Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
}

pub fn meta<'i, 't>(input: &'i [&'t str]) -> IResult<&'i [&'t str], Vec<&'t str>> {
  many0(comment)(input)
}

pub fn token<'i, 't>(token: &'t str) -> impl Fn(&'i [&'t str]) -> IResult<&'i [&'t str], &'t str>
where
  't: 'i,
{
  move |tokens: &[&str]| {
    if let Some(token2) = tokens.first() {
      let token2 = if let Some(token2) = token2.strip_prefix("\\\n") {
        // TODO: Fix in tokenizer/lexer.
        token2
      } else {
        token2
      };

      if token2 == token {
        return Ok((&tokens[1..], token2))
      }
    }

    Err(nom::Err::Error(nom::error::Error::new(tokens, nom::error::ErrorKind::Fail)))
  }
}

pub use token as keyword;

pub fn parenthesized<'i, 't, O, F>(
  f: F,
) -> impl FnMut(&'i [&'t str]) -> IResult<&'i [&'t str], O, nom::error::Error<&'i [&'t str]>>
where
  F: Parser<&'i [&'t str], O, nom::error::Error<&'i [&'t str]>>,
  't: 'i,
{
  delimited(
    pair(token("("), meta),
    f,
    pair(meta, token(")")),
  )
}
