use std::borrow::Cow;

use nom::{
  bytes::complete::{tag, take_until},
  combinator::all_consuming,
  sequence::delimited,
};

/// A comment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment<'t> {
  pub(crate) comment: Cow<'t, str>,
}

impl<'t> TryFrom<&'t str> for Comment<'t> {
  type Error = nom::Err<nom::error::Error<&'t str>>;

  fn try_from(s: &'t str) -> Result<Self, Self::Error> {
    let (_, comment) = all_consuming(delimited(tag("/*"), take_until("*/"), tag("*/")))(s)?;
    Ok(Self { comment: Cow::Borrowed(comment) })
  }
}
