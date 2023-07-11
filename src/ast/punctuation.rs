/// Punctuation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Punctuation<'t> {
  pub(crate) punctuation: &'t str,
}

macro_rules! impl_punct {
  ($($p:expr),* $(,)?) => {
    impl<'t> Punctuation<'t> {
      pub(crate) fn as_str(&self) -> &'t str {
        &self.punctuation
      }

      pub(crate) fn concat(&self, other: &Self) -> Option<Self> {
        Some(Self {
          punctuation: match (self.punctuation, other.punctuation) {
            ("-", ">") => "->",
            ("+", "+") => "++",
            ("-", "-") => "--",
            ("<", "<") => "<<",
            (">", ">") => ">>",
            ("<", "=") => "<=",
            (">", "=") => ">=",
            ("=", "=") => "==",
            ("!", "=") => "!=",
            ("&", "&") => "&&",
            ("|", "|") => "||",
            ("*", "=") => "*=",
            ("/", "=") => "/=",
            ("%", "=") => "%=",
            ("+", "=") => "+=",
            ("-", "=") => "-=",
            ("<<", "=") | ("<", "<=") => "<<=",
            (">>", "=") | (">", ">=") => ">>=",
            ("&", "=") => "&=",
            ("^", "=") => "^=",
            ("|", "=") => "|=",
            ("#", "#") => "##",
            ("<", ":") => "<:",
            (":", ">") => ":>",
            ("<", "%") => "<%",
            ("%", ">") => "%>",
            ("%", ":") => "%:",
            ("%:", "%:") => "%:%:",
            _ => return None,
          }
        })
      }
    }

    impl<'t> TryFrom<&'t str> for Punctuation<'t> {
      type Error = &'t str;

      fn try_from(s: &'t str) -> Result<Self, Self::Error> {
        if matches!(s, $($p)|*) {
          Ok(Self { punctuation: s })
        } else if s == "\\\n{" {
          Ok(Self { punctuation: "{" })
        } else if s == "\\\n}" {
          Ok(Self { punctuation: "}" })
        } else {
          Err(s)
        }
      }
    }
  };
}

impl PartialEq<str> for Punctuation<'_> {
  fn eq(&self, other: &str) -> bool {
    *self.punctuation == *other
  }
}

impl PartialEq<&str> for Punctuation<'_> {
  fn eq(&self, other: &&str) -> bool {
    *self.punctuation == **other
  }
}

impl PartialEq<Punctuation<'_>> for &str {
  fn eq(&self, other: &Punctuation<'_>) -> bool {
    *self == other.punctuation
  }
}

impl_punct![
  "[", "]", "(", ")", "{", "}", ".", "->", "++", "--", "&", "*", "+", "-", "~", "!", "/", "%", "<<", ">>", "<", ">",
  "<=", ">=", "==", "!=", "^", "|", "&&", "||", "?", ":", ";", "...", "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=",
  "&=", "^=", "|=", ",", "#", "##", "<:", ":>", "<%", "%>", "%:", "%:%:",
];
