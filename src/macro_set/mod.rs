use std::{
  borrow::Cow,
  collections::{HashMap, HashSet},
  error::Error,
  fmt,
  iter::IntoIterator,
  mem,
};

use crate::{
  ast::{Comment, Identifier, IdentifierContinue, Lit, LitChar, LitString, MacroArg, Punctuation},
  MacroToken,
};

#[cfg(test)]
pub(crate) mod test_macros;

/// A set of macros.
///
/// C macros can only be fully expanded once all macros are defined.
/// This struct is a container for collecting all defined variable-like and
/// function-like macros.
///
/// After all macros have been defined [`MacroSet::expand_var_macro`] and
/// [`MacroSet::expand_fn_macro`] can be used to properly tokenize and
/// fully expand nested macros. This also includes expanding stringification (`#`)
/// and concatenation (`##`), except when their respective operands are macro
/// arguments.
///
/// # Example
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use cmacro::{MacroArg, MacroSet, MacroToken, Identifier, Lit, Punctuation};
///
/// let mut macro_set = MacroSet::new();
///
/// macro_set.define_var_macro("PI", &["3.14"]);
/// macro_set.define_fn_macro("TIMES_PI", &["n"], &["n", "*", "PI"]);
///
/// let (args, body) = macro_set.expand_fn_macro("TIMES_PI")?;
/// assert_eq!(args, vec![MacroToken::Identifier(Identifier::try_from("n")?)]);
/// assert_eq!(body, vec![
///   MacroToken::Arg(MacroArg::new(0)),
///   MacroToken::Punctuation(Punctuation::try_from("*")?),
///   MacroToken::Lit(Lit::try_from("3.14")?),
/// ]);
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, Default)]
pub struct MacroSet {
  var_macros: HashMap<String, Vec<String>>,
  fn_macros: HashMap<String, (Vec<String>, Vec<String>)>,
}

/// An error during macro expansion.
#[derive(Debug, PartialEq)]
pub enum ExpansionError {
  /// Macro not found.
  MacroNotFound,
  /// Invalid token.
  InvalidToken,
  /// Function-like macro called with wrong number of arguments.
  FnMacroArgumentError {
    /// The macro name.
    name: String,
    /// The required number of arguments.
    required: usize,
    /// The given number of arguments.
    given: usize,
  },
  /// Macro starts with `##`.
  ConcatBegin,
  /// Macro ends with `##`.
  ConcatEnd,
  /// `__VA_ARGS__` used in non-variadic macro.
  NonVariadicVarArgs,
  /// Function-like macro argument is not unique.
  NonUniqueArgument(String),
  /// `#` in function-like macro is not followed by an argument.
  StringifyNonArgument,
  /// Concatenation does not produce a valid pre-processing token.
  InvalidConcat,
  /// Invalid token used in argument
  InvalidArgumentName,
}

impl fmt::Display for ExpansionError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::MacroNotFound => "macro not found".fmt(f),
      Self::InvalidToken => "macro contains an invalid token".fmt(f),
      Self::FnMacroArgumentError { name, required, given } => {
        write!(f, "macro {name} requires {required} arguments, {given} given")
      },
      Self::ConcatBegin => "macro starts with `##`".fmt(f),
      Self::ConcatEnd => "macro ends with `##`".fmt(f),
      Self::NonVariadicVarArgs => "`__VA_ARGS__` found in non-variadic macro".fmt(f),
      Self::NonUniqueArgument(arg) => write!(f, "macro argument {arg} is not unique"),
      Self::StringifyNonArgument => "`#` is not followed by a macro argument".fmt(f),
      Self::InvalidConcat => "concatenation does not produce a valid pre-processing token".fmt(f),
      Self::InvalidArgumentName => "argument name is not an identifier".fmt(f),
    }
  }
}

impl Error for ExpansionError {}

fn is_comment(s: &str) -> bool {
  (s.starts_with("/*") && s.ends_with("*/")) || s.starts_with("//")
}

fn is_whitespace(s: &str) -> bool {
  let s = s.trim();
  s.is_empty() || is_comment(s)
}

fn tokenize_arg_names<'s, 't, T>(arg_names: &'s [T]) -> Result<Vec<Token<'t>>, ExpansionError>
where
  's: 't,
  T: AsRef<str> + 't,
{
  let it = arg_names.iter();
  let mut arg_names = vec![];

  let mut is_variadic = false;

  for token in it {
    let token = Token::from_str(token.as_ref());

    match token {
      Token::Identifier(ref id) => {
        if is_variadic {
          return Err(ExpansionError::InvalidArgumentName)
        }

        if arg_names.contains(&token) {
          return Err(ExpansionError::NonUniqueArgument(id.as_str().to_owned()))
        }
      },
      Token::Punctuation(ref p) if p.as_str() == "..." => {
        if is_variadic {
          return Err(ExpansionError::NonUniqueArgument("...".into()))
        }

        is_variadic = true;
      },
      Token::Comment(_) => (),
      _ => return Err(ExpansionError::InvalidArgumentName),
    };

    arg_names.push(token)
  }

  Ok(arg_names)
}

fn tokenize<'t, T>(arg_names: &[Token<'t>], tokens: &'t [T]) -> Vec<Token<'t>>
where
  T: AsRef<str> + 't,
{
  tokens
    .iter()
    .map(|t| {
      let t = t.as_ref();
      if let Some(arg_index) = arg_names
        .iter()
        .filter(|t| matches!(t, Token::Punctuation(_) | Token::Identifier(_)))
        .position(|arg| if let Token::Identifier(id) = arg { id.as_str() == t } else { false })
      {
        Token::MacroArg(arg_index)
      } else {
        Token::from_str(t)
      }
    })
    .collect()
}

enum StringifyAction<'s> {
  /// Keep the token and the preceding `#`.
  Keep,
  /// Skip the token.
  Skip,
  /// Append the given string.
  Append(&'s str),
}

impl<'t> Token<'t> {
  pub fn from_str(token: &'t str) -> Self {
    if token == "__VA_ARGS__" {
      Token::VarArgs
    } else if let Ok(identifier) = Identifier::try_from(token) {
      Self::Identifier(identifier)
    } else if let Ok(literal) = Lit::try_from(token) {
      Self::Literal(literal, Cow::Borrowed(token))
    } else if let Ok(id_cont) = IdentifierContinue::try_from(token) {
      Self::IdentifierContinue(id_cont)
    } else if let Ok(p) = Punctuation::try_from(token) {
      Self::Punctuation(p)
    } else if let Ok(comment) = Comment::try_from(token) {
      Self::Comment(comment)
    } else {
      Self::Plain(Cow::Borrowed(token))
    }
  }

  pub fn stringify(&self, nested: bool) -> StringifyAction<'_> {
    use StringifyAction::*;

    match self {
      Self::MacroArg(_) => Keep,
      Self::VarArgs => {
        if nested {
          Keep
        } else {
          Append("__VA_ARGS__")
        }
      },
      Self::Identifier(id) => match id.id.as_ref() {
        "__LINE__" | "__FILE__" if nested => Keep,
        t => Append(t),
      },
      Self::IdentifierContinue(t) => Append(t.as_str()),
      Self::NonReplacable(t) => t.stringify(nested),
      Self::Literal(_, t) => Append(t.as_ref()),
      Self::Plain(t) => Append(t.as_ref()),
      Self::Punctuation(t) => Append(t.as_str()),
      Self::Comment(_) => Skip,
      Self::Placemarker => Skip,
    }
  }

  pub fn detokenize(self, arg_names: &[Token<'t>]) -> Result<Option<MacroToken<'t>>, ExpansionError> {
    Ok(Some(match self {
      Self::MacroArg(arg_index) => MacroToken::Arg(MacroArg { index: arg_index }),
      Self::VarArgs => MacroToken::Arg(MacroArg { index: arg_names.len() - 1 }),
      Self::Identifier(id) => MacroToken::Identifier(id),
      Self::IdentifierContinue(id_cont) => MacroToken::IdentifierContinue(id_cont),
      Self::Literal(lit, _) => MacroToken::Lit(lit),
      Self::Plain(_) => return Err(ExpansionError::InvalidToken),
      Self::Punctuation(t) => MacroToken::Punctuation(t),
      Self::Comment(t) => MacroToken::Comment(t),
      Self::NonReplacable(t) => return t.detokenize(arg_names),
      Self::Placemarker => return Ok(None),
    }))
  }

  pub fn concat(self, other: Self) -> Result<Self, ExpansionError> {
    let new_token = match (self, other) {
      (Token::NonReplacable(lhs), rhs) => return lhs.concat(rhs),
      (lhs, Token::NonReplacable(rhs)) => return lhs.concat(*rhs),
      (Self::Placemarker, rhs) => return Ok(rhs),
      (lhs, Self::Placemarker) => return Ok(lhs),
      (
        Self::Identifier(mut lhs),
        Self::Identifier(Identifier { id: rhs }) | Self::IdentifierContinue(IdentifierContinue { id_cont: rhs }),
      ) => {
        lhs.id.to_mut().push_str(rhs.as_ref());
        return Ok(Self::Identifier(lhs))
      },
      (Self::Punctuation(lhs), Self::Punctuation(ref rhs)) => {
        return Ok(Self::NonReplacable(Box::new(Self::Punctuation(
          lhs.concat(rhs).ok_or(ExpansionError::InvalidConcat)?,
        ))))
      },
      (Self::Literal(Lit::String(_) | Lit::Char(_), _), _) => {
        // Cannot concatenate anything to a string or char literal.
        return Err(ExpansionError::InvalidConcat)
      },
      (Self::Punctuation(lhs), Self::Literal(lit, rhs)) => {
        if lhs == "." {
          match lit {
            Lit::String(_) | Lit::Char(_) => return Err(ExpansionError::InvalidConcat),
            Lit::Int(_) | Lit::Float(_) => {
              let token = format!("{}{rhs}", lhs.as_str());
              if let Ok(literal) = Lit::try_from(token.as_str()) {
                return Ok(Self::Literal(literal.into_static(), Cow::Owned(token)))
              }
            },
          }
        }

        return Err(ExpansionError::InvalidConcat)
      },
      (Self::Identifier(mut lhs), Self::Literal(lit, rhs)) => {
        match lit {
          Lit::String(LitString::Ordinary(_)) | Lit::Char(LitChar::Ordinary(_))
            if matches!(lhs.id.as_ref(), "u8" | "u" | "U" | "L") =>
          {
            lhs.id.to_mut().push_str(rhs.as_ref());
            return Ok(Self::Literal(
              Lit::try_from(lhs.id.as_ref()).unwrap().into_static(),
              Cow::Owned(lhs.id.into_owned()),
            ))
          },
          // Strings cannot be prefixed with anything else.
          Lit::String(_) | Lit::Char(_) => (),
          Lit::Int(_) => {
            lhs.id.to_mut().push_str(rhs.as_ref());
            return Ok(Self::Identifier(lhs))
          },
          Lit::Float(_) => {
            // Appending a float only works for scientific notation
            if rhs.as_ref().chars().all(unicode_ident::is_xid_continue) {
              lhs.id.to_mut().push_str(rhs.as_ref());
              return Ok(Self::Identifier(Identifier::try_from(lhs.id.as_ref()).unwrap().to_static()))
            }
          },
        }

        return Err(ExpansionError::InvalidConcat)
      },
      (
        Self::Identifier(Identifier { id: mut lhs })
        | Self::IdentifierContinue(IdentifierContinue { id_cont: mut lhs })
        | Self::Literal(_, mut lhs)
        | Self::Plain(mut lhs),
        Self::Identifier(Identifier { id: ref rhs })
        | Self::IdentifierContinue(IdentifierContinue { id_cont: ref rhs })
        | Self::Literal(_, ref rhs)
        | Self::Plain(ref rhs),
      ) => {
        lhs.to_mut().push_str(rhs.as_ref());
        lhs.into_owned()
      },
      (Self::Punctuation(_lhs), _) => return Err(ExpansionError::InvalidConcat),
      (_, Self::Punctuation(_rhs)) => return Err(ExpansionError::InvalidConcat),
      (Self::MacroArg(_) | Self::VarArgs | Self::Comment(_), _)
      | (_, Self::MacroArg(_) | Self::VarArgs | Self::Comment(_)) => unreachable!(),
    };

    Ok(if let Ok(identifier) = Identifier::try_from(new_token.as_ref()) {
      Self::Identifier(identifier.to_static())
    } else if let Ok(literal) = Lit::try_from(new_token.as_ref()) {
      Self::Literal(literal.into_static(), Cow::Owned(new_token))
    } else if let Ok(id_cont) = IdentifierContinue::try_from(new_token.as_ref()) {
      Self::IdentifierContinue(id_cont.into_static())
    } else {
      Self::Plain(Cow::Owned(new_token))
    })
  }
}

fn stringify(tokens: Vec<Token<'_>>, nested: bool) -> Vec<Token<'_>> {
  let it = tokens.into_iter().peekable();
  let mut tokens = vec![];

  let mut space_before_next = false;

  let mut current_string = None;

  for token in it {
    let token = match token.stringify(nested) {
      StringifyAction::Keep => {
        tokens.push(Token::Punctuation(Punctuation { punctuation: "#" }));
        tokens.push(token);
        continue
      },
      StringifyAction::Skip => continue,
      StringifyAction::Append(s) => s,
    };

    let s = current_string.get_or_insert(String::new());

    if token != ")" && token != "]" && token != "}" && token != "." && token != "," && token != "(" && space_before_next
    {
      s.push(' ');
    }

    space_before_next = !(token == "(" || token == "[" || token == "{" || token == ".");

    s.push_str(token)
  }

  tokens.extend(current_string.take().map(|s| {
    Token::Literal(Lit::String(LitString::Ordinary(Cow::Owned(s.clone().into_bytes()))), Cow::Owned(format!("{s:?}")))
  }));

  if tokens.is_empty() {
    return vec![Token::Literal(Lit::String(LitString::Ordinary(Cow::Borrowed(&[]))), Cow::Borrowed("\"\""))]
  }

  tokens
}

fn detokenize<'t>(arg_names: &[Token<'t>], tokens: Vec<Token<'t>>) -> Result<Vec<MacroToken<'t>>, ExpansionError> {
  tokens.into_iter().filter_map(|t| t.detokenize(arg_names).transpose()).collect()
}

enum CollectArgsError {
  /// Open parenthesis not found.
  MissingOpenParenthesis(char),
  /// Unclosed parenthesis.
  UnclosedParenthesis(char),
}

#[derive(Debug, Clone, PartialEq)]
enum Token<'t> {
  /// A token that will not be considered for replacement again.
  NonReplacable(Box<Self>),
  /// A macro argument.
  MacroArg(usize),
  /// Variable macro arguments.
  VarArgs,
  /// Punctuation.
  Punctuation(Punctuation<'t>),
  /// An identifier.
  Identifier(Identifier<'t>),
  /// An identifier continuation.
  IdentifierContinue(IdentifierContinue<'t>),
  /// A literal.
  Literal(Lit<'t>, Cow<'t, str>),
  /// An intermediary token which cannot be parsed yet.
  Plain(Cow<'t, str>),
  /// A comment token.
  Comment(Comment<'t>),
  /// A placeholder token.
  Placemarker,
}

impl MacroSet {
  /// Create a new macro set.
  pub fn new() -> Self {
    Self::default()
  }

  fn contains_var_args(body: &[Token<'_>]) -> bool {
    body.iter().any(|t| *t == Token::VarArgs)
  }

  fn expand_macro_body<'s, 't>(
    &'s self,
    non_replaced_names: HashSet<&str>,
    body: &[Token<'t>],
  ) -> Result<Vec<Token<'t>>, ExpansionError>
  where
    's: 't,
  {
    let mut tokens = vec![];
    let mut it = body.iter().cloned().peekable();

    while let Some(token) = it.next() {
      match token {
        Token::Identifier(ref id) => {
          if non_replaced_names.contains(id.id.as_ref()) {
            tokens.push(Token::NonReplacable(Box::new(token)));
          } else {
            // Treat as function-like macro call if immediately followed by `(`.
            if it.peek() == Some(&Token::Punctuation(Punctuation { punctuation: "(" })) {
              if let Some((arg_names, body)) = self.fn_macros.get(id.id.as_ref()) {
                if let Ok(args) = self.collect_args(&mut it) {
                  let arg_names = tokenize_arg_names(arg_names)?;
                  let body = tokenize(&arg_names, body);
                  let expanded_tokens = self.expand_fn_macro_body(
                    non_replaced_names.clone(),
                    id.id.as_ref(),
                    &arg_names,
                    Some(&args),
                    &body,
                  )?;
                  tokens.extend(expanded_tokens);
                  tokens.extend(it);
                  return self.expand_macro_body(non_replaced_names, &tokens)
                }
              }
            }

            // If it's not a macro call, check if it is a variable-like macro.
            if let Some(body) = self.var_macros.get(id.id.as_ref()) {
              let body = tokenize(&[], body);
              tokens.extend(self.expand_var_macro_body(non_replaced_names.clone(), id.id.as_ref(), &body)?);
              tokens.extend(it);
              return self.expand_macro_body(non_replaced_names, &tokens)
            }

            tokens.push(token)
          }
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  fn expand_var_macro_body<'s, 't, 'n>(
    &'s self,
    mut non_replaced_names: HashSet<&'n str>,
    name: &'n str,
    body: &[Token<'t>],
  ) -> Result<Vec<Token<'t>>, ExpansionError>
  where
    's: 't,
  {
    // A variable-like macro shall not contain `__VA_ARGS__`.
    if Self::contains_var_args(body) {
      return Err(ExpansionError::NonVariadicVarArgs)
    }

    let mut body = Self::expand_concat(body.to_vec())?;
    Self::remove_placemarkers(&mut body);

    non_replaced_names.insert(name);

    self.expand_macro_body(non_replaced_names, &body)
  }

  fn expand_fn_macro_body<'s, 't, 'n>(
    &'s self,
    mut non_replaced_names: HashSet<&'n str>,
    name: &'n str,
    arg_names: &[Token<'t>],
    args: Option<&[Vec<Token<'t>>]>,
    body: &[Token<'t>],
  ) -> Result<Vec<Token<'t>>, ExpansionError>
  where
    's: 't,
  {
    let arg_names: Vec<_> = arg_names.iter().filter(|t| !matches!(t, Token::Comment(_))).cloned().collect();

    let is_variadic = matches!(arg_names.last(), Some(Token::Punctuation(p)) if p == "...");

    if !is_variadic {
      // A function-like macro shall only contain `__VA_ARGS__` if it uses ellipsis notation in the parameters.
      if Self::contains_var_args(body) {
        return Err(ExpansionError::NonVariadicVarArgs)
      }

      if let Some(args) = args {
        if arg_names.len() != args.len()
          // Allow passing an empty argument for arity 0.
          && !(arg_names.is_empty() && args.first().map(|arg| arg.is_empty()).unwrap_or(true))
        {
          return Err(ExpansionError::FnMacroArgumentError {
            name: name.to_owned(),
            required: arg_names.len(),
            given: args.len(),
          })
        }
      }
    }

    // Parameter names must be unique.
    {
      let arg_names = arg_names.iter().filter_map(|t| -> Option<&str> {
        match t {
          Token::Punctuation(p) => Some(p.as_str()),
          Token::Identifier(id) => Some(id.as_str()),
          _ => None,
        }
      });
      if let Some((_, duplicate_parameter)) = arg_names
        .clone()
        .enumerate()
        .find(|(i, arg_name)| arg_names.clone().skip(i + 1).any(|arg_name2| *arg_name == arg_name2))
      {
        return Err(ExpansionError::NonUniqueArgument(duplicate_parameter.to_owned()))
      }
    }

    let body = if let Some(args) = args {
      self.expand_arguments(non_replaced_names.clone(), &arg_names, args, body)?
    } else {
      body.to_vec()
    };

    let mut body = Self::expand_concat(body)?;
    Self::remove_placemarkers(&mut body);

    non_replaced_names.insert(name);

    self.expand_macro_body(non_replaced_names, &body)
  }

  fn collect_args<'s, 't, I>(&'s self, it: &mut I) -> Result<Vec<Vec<Token<'t>>>, CollectArgsError>
  where
    's: 't,
    I: Iterator<Item = Token<'t>> + Clone,
  {
    let mut parentheses = vec![]; // Keep track of parenthesis pairs.
    let mut args = vec![];
    let mut current_arg = vec![];

    let mut it2 = it.clone();

    match it2.next() {
      Some(Token::Punctuation(p)) if p == "(" => (),
      _ => return Err(CollectArgsError::MissingOpenParenthesis('(')),
    }

    while let Some(token) = it2.next() {
      match token {
        Token::Punctuation(p) => {
          let pop = |parentheses: &mut Vec<char>, open, close| match parentheses.pop() {
            Some(p) => {
              if p == open {
                Ok(())
              } else {
                Err(CollectArgsError::UnclosedParenthesis(p))
              }
            },
            None => Err(CollectArgsError::MissingOpenParenthesis(close)),
          };

          match p.as_str() {
            "(" => parentheses.push('('),
            ")" => {
              if parentheses.is_empty() {
                args.push(mem::take(&mut current_arg));

                *it = it2;
                return Ok(args)
              } else {
                pop(&mut parentheses, '(', ')')?
              }
            },
            "[" => parentheses.push('['),
            "]" => pop(&mut parentheses, '[', ']')?,
            "{" => parentheses.push('{'),
            "}" => pop(&mut parentheses, '{', '}')?,
            "," => {
              if parentheses.is_empty() {
                args.push(mem::take(&mut current_arg));
                continue
              }
            },
            _ => (),
          }

          current_arg.push(Token::Punctuation(p));
        },
        token => current_arg.push(token),
      }
    }

    Err(CollectArgsError::UnclosedParenthesis('('))
  }

  fn expand_arguments<'s, 't>(
    &'s self,
    non_replaced_names: HashSet<&str>,
    arg_names: &[Token<'t>],
    args: &[Vec<Token<'t>>],
    tokens: &[Token<'t>],
  ) -> Result<Vec<Token<'t>>, ExpansionError>
  where
    's: 't,
  {
    let mut it = tokens.iter().cloned().peekable();
    let mut tokens = vec![];

    while let Some(token) = it.next() {
      match token {
        Token::Punctuation(ref p) if p == "#" => match it.peek() {
          Some(Token::MacroArg(_) | Token::VarArgs) => {
            tokens.push(token.clone());
          },
          _ => return Err(ExpansionError::StringifyNonArgument),
        },
        Token::MacroArg(_) | Token::VarArgs => {
          let arg = if let Token::MacroArg(arg_index) = token {
            args[arg_index].clone()
          } else {
            let mut var_args = vec![];

            for (i, arg) in args[(arg_names.len() - 1)..].iter().enumerate() {
              if i > 0 {
                var_args.push(Token::Punctuation(Punctuation { punctuation: "," }));
              }
              var_args.extend(arg.clone());
            }

            var_args
          };

          match tokens.last() {
            Some(Token::Punctuation(Punctuation { punctuation: "#" })) => {
              tokens.pop();
              tokens.extend(stringify(arg, non_replaced_names.len() > 1));
            },
            Some(Token::Punctuation(Punctuation { punctuation: "##" })) => {
              let arg = self.expand_macro_body(non_replaced_names.clone(), &arg)?;

              if arg.is_empty() {
                tokens.push(Token::Placemarker);
              } else {
                tokens.extend(arg);
              }
            },
            _ if it.peek() == Some(&Token::Punctuation(Punctuation { punctuation: "##" })) => {
              let arg = self.expand_macro_body(non_replaced_names.clone(), &arg)?;

              if arg.is_empty() {
                tokens.push(Token::Placemarker);
              } else {
                tokens.extend(arg);
              }
            },
            _ => tokens.extend(self.expand_macro_body(non_replaced_names.clone(), &arg)?),
          }
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  fn expand_concat(tokens: Vec<Token<'_>>) -> Result<Vec<Token<'_>>, ExpansionError> {
    let mut it = tokens.into_iter().peekable();
    let mut tokens = vec![];

    while let Some(token) = it.next() {
      match token {
        Token::Punctuation(Punctuation { punctuation: "##" })
          if !matches!(tokens.last(), Some(&Token::MacroArg(_) | &Token::VarArgs))
            && !matches!(it.peek(), Some(&Token::MacroArg(_) | &Token::VarArgs)) =>
        {
          macro_rules! until_no_whitespace {
            ($expr:expr, $error:ident) => {{
              loop {
                match $expr {
                  Some(Token::Comment(_)) => continue,
                  Some(token) => break token,
                  // Macros may not start or and with `##`.
                  None => return Err(ExpansionError::$error),
                }
              }
            }};
          }

          // Ignore whitespace between the last non-whitespace token and this `##`.
          let lhs = until_no_whitespace!(tokens.pop(), ConcatBegin);
          let rhs = if it.peek() == Some(&Token::Punctuation(Punctuation { punctuation: "##" })) {
            // Treat consecutive `##` as one.
            Token::Placemarker
          } else {
            // Ignore whitespace between this `##` and the next non-whitespace token.
            until_no_whitespace!(it.next(), ConcatEnd)
          };
          tokens.push(lhs.concat(rhs)?)
        },
        token => tokens.push(token),
      }
    }

    Ok(tokens)
  }

  fn remove_placemarkers(tokens: &mut Vec<Token<'_>>) {
    tokens.retain(|t| *t != Token::Placemarker);
  }

  /// Define a variable-like macro.
  ///
  /// Returns true if the macro was redefined.
  pub fn define_var_macro<N, B>(&mut self, name: N, body: B) -> bool
  where
    N: AsRef<str>,
    B: IntoIterator,
    B::Item: AsRef<str>,
  {
    let name = name.as_ref().to_owned();
    let body = body.into_iter().map(|t| t.as_ref().to_owned()).collect::<Vec<_>>();

    let redefined = if let Some(old_body) = self.var_macros.remove(&name) {
      let old_tokens = old_body.iter().filter(|t| !is_whitespace(t));
      let new_tokens = body.iter().filter(|t| !is_whitespace(t));

      !old_tokens.zip(new_tokens).all(|(t1, t2)| t1 == t2)
    } else {
      self.fn_macros.remove(&name).is_some()
    };

    self.var_macros.insert(name, body);

    redefined
  }

  /// Expand a variable-like macro.
  pub fn expand_var_macro<'s, 't>(&'s self, name: &str) -> Result<Vec<MacroToken<'t>>, ExpansionError>
  where
    's: 't,
  {
    let body = self.var_macros.get(name).ok_or(ExpansionError::MacroNotFound)?;
    let body = tokenize(&[], body);
    let tokens = self.expand_var_macro_body(HashSet::new(), name, &body)?;
    detokenize(&[], tokens)
  }

  /// Undefine a variable-like macro with the given name.
  ///
  /// Returns true if the macro was undefined.
  pub fn undefine_var_macro(&mut self, name: &str) -> bool {
    self.var_macros.remove(name).is_some()
  }

  /// Define a function-like macro.
  ///
  /// Returns true if the macro was redefined.
  pub fn define_fn_macro<N, A, B>(&mut self, name: N, args: A, body: B) -> bool
  where
    N: AsRef<str>,
    A: IntoIterator,
    A::Item: AsRef<str>,
    B: IntoIterator,
    B::Item: AsRef<str>,
  {
    let name = name.as_ref().to_owned();
    let args = args.into_iter().map(|a| a.as_ref().to_owned()).collect::<Vec<_>>();
    let body = body.into_iter().map(|a| a.as_ref().to_owned()).collect::<Vec<_>>();

    let redefined = if let Some((old_args, old_body)) = self.fn_macros.remove(&name) {
      let old_args = old_args.iter().filter(|t| !is_whitespace(t));
      let new_args = args.iter().filter(|t| !is_whitespace(t));
      let args_equal = old_args.zip(new_args).all(|(old_arg, arg)| old_arg == arg);

      let old_tokens = old_body.iter().filter(|t| !is_whitespace(t));
      let new_tokens = body.iter().filter(|t| !is_whitespace(t));
      let tokens_equal = old_tokens.zip(new_tokens).all(|(t1, t2)| t1 == t2);

      !(args_equal && tokens_equal)
    } else {
      self.var_macros.remove(&name).is_some()
    };

    self.fn_macros.insert(name, (args, body));

    redefined
  }

  /// Expand a function-like macro.
  pub fn expand_fn_macro<'s, 't>(
    &'s self,
    name: &str,
  ) -> Result<(Vec<MacroToken<'t>>, Vec<MacroToken<'t>>), ExpansionError>
  where
    's: 't,
  {
    let (arg_names, body) = self.fn_macros.get(name).ok_or(ExpansionError::MacroNotFound)?;

    let arg_names = tokenize_arg_names(arg_names)?;
    let body = tokenize(&arg_names, body);
    let tokens = self.expand_fn_macro_body(HashSet::new(), name, &arg_names, None, &body)?;

    let tokens = detokenize(&arg_names, tokens)?;
    let arg_names = detokenize(&[], arg_names)?;

    Ok((arg_names, tokens))
  }

  /// Undefine a function-like macro with the given name.
  ///
  /// Returns true if the macro was undefined.
  pub fn undefine_fn_macro(&mut self, name: &str) -> bool {
    self.fn_macros.remove(name).is_some()
  }

  /// Expand a macro expression using the macros defined in the set.
  pub fn expand<'s, 'b, 't, T>(&'s self, body: &'b [T]) -> Result<Vec<MacroToken<'t>>, ExpansionError>
  where
    's: 't,
    'b: 't,
    T: AsRef<str> + 't,
  {
    let body = tokenize(&[], body);
    let tokens: Vec<Token<'t>> = self.expand_var_macro_body(HashSet::new(), "", &body)?;
    detokenize(&[], tokens)
  }
}

#[cfg(test)]
macro_rules! token_vec {
  ($($token:expr),*) => {{
    vec![
      $(
        MacroToken::from($token)
      ),*
    ]
  }};
}

#[cfg(test)]
mod tests {
  use crate::{
    ast::{arg, comment, id, lit_int, lit_string, punct},
    macro_token::*,
  };

  use super::*;

  #[test]
  fn macro_set() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("VAR", ["A", "+", "B"]);
    macro_set.define_var_macro("A", ["2"]);
    macro_set.define_var_macro("B", ["3"]);
    macro_set.define_fn_macro("PLUS", ["A", "B"], ["A", "+", "B"]);
    macro_set.define_fn_macro("F1", ["A", "B"], ["A", "+", "VAR", "+", "B"]);
    macro_set.define_var_macro("PLUS_VAR", ["PLUS", "(", "7", ",", "8", ")"]);
    macro_set.define_var_macro("PLUS_PLUS_VAR", ["PLUS", "(", "PLUS", "(", "3", ",", "1", ")", ",", "8", ")"]);
    macro_set.define_var_macro("PLUS_VAR_VAR", ["PLUS", "(", "7", ",", "VAR", ")"]);

    assert_eq!(macro_set.expand_var_macro("VAR"), Ok(token_vec![lit_int!(2), punct!("+"), lit_int!(3)]));
    assert_eq!(
      macro_set.expand_fn_macro("F1"),
      Ok((
        token_vec![id!(A), id!(B)],
        token_vec![arg!(0), punct!("+"), lit_int!(2), punct!("+"), lit_int!(3), punct!("+"), arg!(1)]
      ))
    );
    assert_eq!(macro_set.expand_var_macro("PLUS_VAR"), Ok(token_vec![lit_int!(7), punct!("+"), lit_int!(8)]));
    assert_eq!(
      macro_set.expand_var_macro("PLUS_PLUS_VAR"),
      Ok(token_vec![lit_int!(3), punct!("+"), lit_int!(1), punct!("+"), lit_int!(8)])
    );
    assert_eq!(
      macro_set.expand_var_macro("PLUS_VAR_VAR"),
      Ok(token_vec![lit_int!(7), punct!("+"), lit_int!(2), punct!("+"), lit_int!(3)])
    );
  }

  #[test]
  fn non_unique_arg_name() {
    let mut macro_set = MacroSet::new();
    macro_set.define_fn_macro("X", ["x", "x"], ["x", "*", "x"]);
    assert_eq!(macro_set.expand_fn_macro("X"), Err(ExpansionError::NonUniqueArgument("x".into())));
  }

  #[test]
  fn parse_args_whitespace() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("TIMES", ["x", "/* X coordinate */", "y", "/* Y coordinate */"], ["x", "*", "y"]);
    assert_eq!(
      macro_set.expand_fn_macro("TIMES"),
      Ok((
        token_vec![id!(x), comment!("/* X coordinate */"), id!(y), comment!("/* Y coordinate */")],
        token_vec![arg!(0), punct!("*"), arg!(1)]
      ))
    );
  }

  #[test]
  fn parse_concat_var_args() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("CONCAT_VAR_ARGS", ["..."], ["__VA_", "##", "ARGS__"]);
    macro_set.define_var_macro("CALL_CONCAT_VAR_ARGS", ["CONCAT_VAR_ARGS", "(", ")"]);
    assert_eq!(
      macro_set.expand_fn_macro("CONCAT_VAR_ARGS"),
      Ok((token_vec![punct!("...")], token_vec![id!(__VA_ARGS__)]))
    );
    assert_eq!(macro_set.expand_var_macro("CALL_CONCAT_VAR_ARGS"), Ok(token_vec![id!(__VA_ARGS__)]));
  }

  #[test]
  fn concat_begin_end() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT_BEGIN", ["##", "b"]);
    macro_set.define_var_macro("CONCAT_END", ["a", "##"]);
    macro_set.define_var_macro("CONCAT_BEGIN_END", ["##"]);
    macro_set.define_var_macro("CONCAT_COMMENT_BEGIN", ["/* a */", "##", "b"]);
    macro_set.define_var_macro("CONCAT_COMMENT_END", ["a", "##", "/* b */"]);
    macro_set.define_var_macro("CONCAT_COMMENT_BEGIN_END", ["/* a */", "##", "/* b */"]);

    assert_eq!(macro_set.expand_var_macro("CONCAT_BEGIN"), Err(ExpansionError::ConcatBegin));
    assert_eq!(macro_set.expand_var_macro("CONCAT_END"), Err(ExpansionError::ConcatEnd));
    assert_eq!(macro_set.expand_var_macro("CONCAT_BEGIN_END"), Err(ExpansionError::ConcatBegin));

    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT_BEGIN"), Err(ExpansionError::ConcatBegin));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT_END"), Err(ExpansionError::ConcatEnd));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT_BEGIN_END"), Err(ExpansionError::ConcatBegin));
  }

  #[test]
  fn parse_disjunct() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("THREE_PLUS", ["3", "+"]);
    macro_set.define_var_macro("FOUR", ["4"]);
    macro_set.define_var_macro("THREE_PLUS_FOUR", ["THREE_PLUS", "FOUR"]);

    assert_eq!(macro_set.expand_var_macro("THREE_PLUS_FOUR"), Ok(token_vec![lit_int!(3), punct!("+"), lit_int!(4)]));
  }

  #[test]
  fn parse_fn_no_args() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("FUNC", [] as [String; 0], ["123"]);
    macro_set.define_var_macro("ONE_TWO_THREE", ["FUNC", "(", ")"]);
    assert_eq!(macro_set.expand_var_macro("ONE_TWO_THREE"), Ok(token_vec![lit_int!(123)]));
  }

  #[test]
  fn parse_disjunct_fn() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("FUNC1", ["a", "b"], ["a", "+", "b"]);
    macro_set.define_var_macro("FUNC1_PARTIAL", ["FUNC1", "(", "1", ","]);
    macro_set.define_fn_macro("FUNC2", [] as [String; 0], ["FUNC1_PARTIAL", "2", ")"]);

    assert_eq!(
      macro_set.expand_fn_macro("FUNC2"),
      Ok((token_vec![], token_vec![lit_int!(1), punct!("+"), lit_int!(2)]))
    );
  }

  #[test]
  fn parse_disjunct_fn_call() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("BAR", ["a", "b"], ["a", "+", "b"]);
    macro_set.define_fn_macro("FOO", [] as [String; 0], ["BAR"]);
    macro_set.define_var_macro("APLUSB", ["FOO", "(", ")", "(", "3", ",", "1", ")"]);

    assert_eq!(macro_set.expand_var_macro("APLUSB"), Ok(token_vec![lit_int!(3), punct!("+"), lit_int!(1)]));
  }

  #[test]
  fn parse_recursive() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("FUNC1", ["arg"], ["FUNC2", "(", "arg", ")"]);
    macro_set.define_fn_macro("FUNC2", ["arg"], ["FUNC1", "(", "arg", ")"]);
    macro_set.define_var_macro("VAR1", ["1", "+", "VAR1"]);
    assert_eq!(
      macro_set.expand_fn_macro("FUNC1"),
      Ok((token_vec![id!(arg)], token_vec![id!(FUNC1), punct!("("), arg!(0), punct!(")")]))
    );
    assert_eq!(
      macro_set.expand_fn_macro("FUNC2"),
      Ok((token_vec![id!(arg)], token_vec![id!(FUNC2), punct!("("), arg!(0), punct!(")")]))
    );
    assert_eq!(macro_set.expand_var_macro("VAR1"), Ok(token_vec![lit_int!(1), punct!("+"), id!(VAR1)]));
  }

  #[test]
  fn parse_stringify() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("s", ["377"]);
    macro_set.define_fn_macro("STRINGIFY", ["s"], ["#", "s"]);
    assert_eq!(macro_set.expand_fn_macro("STRINGIFY"), Ok((token_vec![id!(s)], token_vec![punct!("#"), arg!(0)])));
  }

  #[test]
  fn parse_stringify_nested() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("STRINGIFY", ["s"], ["#", "s"]);
    macro_set.define_var_macro("s", ["STRINGIFY", "(", "asdf", ")"]);
    macro_set.define_var_macro("e", ["STRINGIFY", "(", "a", "+", "b", ")"]);
    assert_eq!(macro_set.expand_var_macro("s"), Ok(token_vec![lit_string!("asdf")]));
    assert_eq!(macro_set.expand_var_macro("e"), Ok(token_vec![lit_string!("a + b")]));
  }

  #[test]
  fn parse_stringify_double_nested() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("STRINGIFY1", ["s"], ["#", "s"]);
    macro_set.define_fn_macro("STRINGIFY2", ["s"], ["STRINGIFY1", "(", "s", ")"]);
    macro_set.define_var_macro("LINE_STRING1", ["STRINGIFY1", "(", "__LINE__", ")"]);
    macro_set.define_var_macro("LINE_STRING2", ["STRINGIFY2", "(", "__LINE__", ")"]);
    assert_eq!(macro_set.expand_fn_macro("STRINGIFY1"), Ok((token_vec![id!(s)], token_vec![punct!("#"), arg!(0)])));
    assert_eq!(macro_set.expand_fn_macro("STRINGIFY2"), Ok((token_vec![id!(s)], token_vec![punct!("#"), arg!(0)])));
    assert_eq!(macro_set.expand_var_macro("LINE_STRING1"), Ok(token_vec![lit_string!("__LINE__")]));
    assert_eq!(macro_set.expand_var_macro("LINE_STRING2"), Ok(token_vec![punct!("#"), id!(__LINE__)]));
  }

  #[test]
  fn parse_stringify_var_args() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("STRINGIFY", ["..."], ["#", "__VA_ARGS__"]);
    macro_set.define_var_macro("ZERO", ["STRINGIFY", "(", ")"]);
    macro_set.define_var_macro("ONE", ["STRINGIFY", "(", "asdf", ")"]);
    macro_set.define_var_macro("TWO", ["STRINGIFY", "(", "a", ",", "b", ")"]);
    assert_eq!(macro_set.expand_var_macro("ZERO"), Ok(token_vec![lit_string!("")]));
    assert_eq!(macro_set.expand_var_macro("ONE"), Ok(token_vec![lit_string!("asdf")]));
    assert_eq!(macro_set.expand_var_macro("TWO"), Ok(token_vec![lit_string!("a, b")]));
  }

  #[test]
  fn parse_wrong_arity() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("func", ["x"], ["func", "(", "x", ",", "3", ")"]);
    macro_set.define_fn_macro("wrapper_func", ["x"], ["func", "(", "x", ",", "3", ")"]);

    assert_eq!(
      macro_set.expand_fn_macro("wrapper_func"),
      Err(ExpansionError::FnMacroArgumentError { name: "func".into(), required: 1, given: 2 })
    );
  }

  #[test]
  fn parse_concat() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("A", ["1"]);
    macro_set.define_var_macro("B", ["2"]);
    macro_set.define_var_macro("CONCAT", ["A", "##", "B"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT"), Ok(token_vec![id!(AB)]));
  }

  #[test]
  fn parse_concat_comment() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT_COMMENT1", ["A", "/* 1 */", "##", "B"]);
    macro_set.define_var_macro("CONCAT_COMMENT2", ["A", "##", "/* 2 */", "B"]);
    macro_set.define_var_macro("CONCAT_COMMENT3", ["A", "/* 1 */", "##", "/* 2 */", "B"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT1"), Ok(token_vec![id!(AB)]));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT2"), Ok(token_vec![id!(AB)]));
    assert_eq!(macro_set.expand_var_macro("CONCAT_COMMENT3"), Ok(token_vec![id!(AB)]));
  }

  #[test]
  fn parse_concat_string() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("A", ["1"]);
    macro_set.define_var_macro("B", ["2"]);
    macro_set.define_var_macro("C", ["\", world!\""]);
    macro_set.define_var_macro("AB", ["\"Hello\""]);
    macro_set.define_fn_macro("CONCAT_STRING", ["A", "B"], ["A", "##", "B", "C"]);
    assert_eq!(
      macro_set.expand_fn_macro("CONCAT_STRING"),
      Ok((token_vec![id!(A), id!(B)], token_vec![arg!(0), punct!("##"), arg!(1), lit_string!(", world!")]))
    );
  }

  #[test]
  fn parse_concat_string_prefix() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("A", ["u8", "##", "\"abc\""]);
    macro_set.define_var_macro("B", ["u8", "\"abc\""]);
    macro_set.define_fn_macro("PREFIX", ["prefix"], ["prefix", "##", "\"abc\""]);
    macro_set.define_var_macro("C", ["PREFIX", "(", "u8", ")"]);
    macro_set.define_fn_macro("PREFIX_STRINGIFY", ["prefix"], ["prefix", "##", "#", "prefix"]);
    macro_set.define_var_macro("D", ["PREFIX_STRINGIFY", "(", "u8", ")"]);
    macro_set.define_fn_macro("PREFIX_HASH", ["prefix"], ["prefix", "##", "#"]);
    macro_set.define_var_macro("E", ["PREFIX_HASH", "(", "u8", ")"]);
    assert_eq!(macro_set.expand_var_macro("A"), Ok(token_vec![lit_string!(u8 "abc")]));
    assert_eq!(macro_set.expand_var_macro("B"), Ok(token_vec![id!(u8), lit_string!("abc")]));
    assert_eq!(macro_set.expand_var_macro("C"), Ok(token_vec![lit_string!(u8 "abc")]));
    assert_eq!(macro_set.expand_var_macro("D"), Ok(token_vec![lit_string!(u8 "u8")]));
    assert_eq!(macro_set.expand_var_macro("E"), Err(ExpansionError::StringifyNonArgument));
  }

  #[test]
  fn parse_concat_ident_int() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT", ["FUNC", "##", "123"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT"), Ok(token_vec![id!(FUNC123)]));
  }

  #[test]
  fn parse_concat_ident_float() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT", ["FUNC", "##", "123e4"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT"), Ok(token_vec![id!(FUNC123e4)]));
  }

  #[test]
  fn parse_concat_dot_float() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT", [".", "##", "123e4"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT"), Ok(token_vec![double!(0.123e4)]));
  }

  #[test]
  fn parse_concat_dot_int() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("CONCAT", [".", "##", "01234"]);
    assert_eq!(macro_set.expand_var_macro("CONCAT"), Ok(token_vec![double!(0.01234)]));
  }

  #[test]
  fn parse_concat_empty() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("CONCAT", ["a", "b"], ["a", "##", "b"]);
    macro_set.define_var_macro("EMPTY", ["CONCAT", "(", ",", ")"]);
    assert_eq!(macro_set.expand_var_macro("EMPTY"), Ok(token_vec![]));
  }

  #[test]
  fn parse_c_std_6_10_3_3_example() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("hash_hash", ["#", "##", "#"]);
    macro_set.define_fn_macro("mkstr", ["a"], ["#", "a"]);
    macro_set.define_fn_macro("in_between", ["a"], ["mkstr", "(", "a", ")"]);
    macro_set.define_fn_macro("join", ["c", "d"], ["in_between", "(", "c", "hash_hash", "d", ")"]);
    macro_set.define_var_macro("join_x_y", ["join", "(", "x", ",", "y", ")"]);
    assert_eq!(macro_set.expand_var_macro("join_x_y"), Ok(token_vec![lit_string!("x ## y")]));
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_3() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("x", ["3"]);
    macro_set.define_fn_macro("f", ["a"], ["f", "(", "x", "*", "(", "a", ")", ")"]);
    macro_set.define_var_macro("x", ["2"]);
    macro_set.define_var_macro("g", ["f"]);
    macro_set.define_var_macro("z", ["z", "[", "0", "]"]);
    macro_set.define_var_macro("h", ["g", "(", "~"]);
    macro_set.define_fn_macro("m", ["a"], ["a", "(", "w", ")"]);
    macro_set.define_var_macro("w", ["0", ",", "1"]);
    macro_set.define_fn_macro("t", ["a"], ["a"]);
    macro_set.define_fn_macro("p", [] as [String; 0], ["int"]);
    macro_set.define_fn_macro("q", ["x"], ["x"]);
    macro_set.define_fn_macro("r", ["x", "y"], ["x", "##", "y"]);
    macro_set.define_fn_macro("str", ["x"], ["#", "x"]);

    assert_eq!(
      macro_set.expand(&[
        "f", "(", "y", "+", "1", ")", "+", "f", "(", "f", "(", "z", ")", ")", "%", "t", "(", "t", "(", "g", ")", "(",
        "0", ")", "+", "t", ")", "(", "1", ")", ";",
      ]),
      Ok(token_vec![
        id!(f),
        punct!("("),
        lit_int!(2),
        punct!("*"),
        punct!("("),
        id!(y),
        punct!("+"),
        lit_int!(1),
        punct!(")"),
        punct!(")"),
        punct!("+"),
        id!(f),
        punct!("("),
        lit_int!(2),
        punct!("*"),
        punct!("("),
        id!(f),
        punct!("("),
        lit_int!(2),
        punct!("*"),
        punct!("("),
        id!(z),
        punct!("["),
        lit_int!(0),
        punct!("]"),
        punct!(")"),
        punct!(")"),
        punct!(")"),
        punct!(")"),
        punct!("%"),
        id!(f),
        punct!("("),
        lit_int!(2),
        punct!("*"),
        punct!("("),
        lit_int!(0),
        punct!(")"),
        punct!(")"),
        punct!("+"),
        id!(t),
        punct!("("),
        lit_int!(1),
        punct!(")"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&[
        "g", "(", "x", "+", "(", "3", ",", "4", ")", "-", "w", ")", "|", "h", "5", ")", "&", "m", "(", "f", ")", "^",
        "m", "(", "m", ")", ";",
      ]),
      Ok(token_vec![
        id!(f),
        punct!("("),
        lit_int!(2),
        punct!("*"),
        punct!("("),
        lit_int!(2),
        punct!("+"),
        punct!("("),
        lit_int!(3),
        punct!(","),
        lit_int!(4),
        punct!(")"),
        punct!("-"),
        lit_int!(0),
        punct!(","),
        lit_int!(1),
        punct!(")"),
        punct!(")"),
        punct!("|"),
        id!(f),
        punct!("("),
        lit_int!(2),
        punct!("*"),
        punct!("("),
        punct!("~"),
        lit_int!(5),
        punct!(")"),
        punct!(")"),
        punct!("&"),
        id!(f),
        punct!("("),
        lit_int!(2),
        punct!("*"),
        punct!("("),
        lit_int!(0),
        punct!(","),
        lit_int!(1),
        punct!(")"),
        punct!(")"),
        punct!("^"),
        id!(m),
        punct!("("),
        lit_int!(0),
        punct!(","),
        lit_int!(1),
        punct!(")"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&[
        "p", "(", ")", "i", "[", "q", "(", ")", "]", "=", "{", "q", "(", "1", ")", ",", "r", "(", "2", ",", "3", ")",
        ",", "r", "(", "4", ",", ")", ",", "r", "(", ",", "5", ")", ",", "r", "(", ",", ")", "}", ";",
      ]),
      Ok(token_vec![
        id!(int),
        id!(i),
        punct!("["),
        punct!("]"),
        punct!("="),
        punct!("{"),
        lit_int!(1),
        punct!(","),
        lit_int!(23),
        punct!(","),
        lit_int!(4),
        punct!(","),
        lit_int!(5),
        punct!(","),
        punct!("}"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&[
        "char", "c", "[", "2", "]", "[", "6", "]", "=", "{", "str", "(", "hello", ")", ",", "str", "(", ")", "}", ";"
      ]),
      Ok(token_vec![
        id!(char),
        id!(c),
        punct!("["),
        lit_int!(2),
        punct!("]"),
        punct!("["),
        lit_int!(6),
        punct!("]"),
        punct!("="),
        punct!("{"),
        lit_string!("hello"),
        punct!(","),
        lit_string!(""),
        punct!("}"),
        punct!(";")
      ])
    );
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_4() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("str", ["s"], ["#", "s"]);
    macro_set.define_fn_macro("xstr", ["s"], ["str", "(", "s", ")"]);
    macro_set.define_fn_macro(
      "debug",
      ["s", "t"],
      [
        "printf",
        "(",
        "\"x\"",
        "#",
        "s",
        "\"= %d, x\"",
        "#",
        "t",
        "\"= %s\"",
        ",",
        "x",
        "##",
        "s",
        ",",
        "x",
        "##",
        "t",
        ")",
      ],
    );
    macro_set.define_fn_macro("INCFILE", ["n"], ["vers", "##", "n"]);
    macro_set.define_fn_macro("glue", ["a", "b"], ["a", "##", "b"]);
    macro_set.define_fn_macro("xglue", ["a", "b"], ["glue", "(", "a", ",", "b", ")"]);
    macro_set.define_var_macro("HIGHLOW", ["\"hello\""]);
    macro_set.define_var_macro("LOW", ["LOW", "\", world\""]);

    assert_eq!(
      macro_set.expand(&["debug", "(", "1", ",", "2", ")", ";"]),
      Ok(token_vec![
        id!(printf),
        punct!("("),
        lit_string!("x"),
        lit_string!("1"),
        lit_string!("= %d, x"),
        lit_string!("2"),
        lit_string!("= %s"),
        punct!(","),
        id!(x1),
        punct!(","),
        id!(x2),
        punct!(")"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&[
        "fputs",
        "(",
        "str",
        "(",
        "strncmp",
        "(",
        "\"abc\\0d\"",
        ",",
        "\"abc\"",
        ",",
        "'\\4'",
        ")", // this goes away
        "==",
        "0",
        ")",
        "str",
        "(",
        ":",
        "@",
        "\\n",
        ")",
        ",",
        "s",
        ")",
        ";",
      ]),
      Ok(token_vec![
        id!(fputs),
        punct!("("),
        lit_string!("strncmp(\"abc\\0d\", \"abc\", '\\4') == 0"),
        lit_string!(": @ \\n"),
        punct!(","),
        id!(s),
        punct!(")"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&["xstr", "(", "INCFILE", "(", "2", ")", ".", "h", ")"]),
      Ok(token_vec![lit_string!("vers2.h")])
    );
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_5() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("t", ["x", "y", "z"], ["x", "##", "y", "##", "z"]);
    assert_eq!(
      macro_set.expand(&[
        "int", "j", "[", "]", "=", "{", //
        "t", "(", "1", ",", "2", ",", "3", ")", ",", //
        "t", "(", ",", "4", ",", "5", ")", ",", //
        "t", "(", "6", ",", ",", "7", ")", ",", //
        "t", "(", "8", ",", "9", ",", ")", ",", //
        "t", "(", "10", ",", ",", ")", ",", //
        "t", "(", ",", "11", ",", ")", ",", //
        "t", "(", ",", ",", "12", ")", ",", //
        "t", "(", ",", ",", ")", //
        "}", ";",
      ]),
      Ok(token_vec![
        id!(int),
        id!(j),
        punct!("["),
        punct!("]"),
        punct!("="),
        punct!("{"),
        lit_int!(123),
        punct!(","),
        lit_int!(45),
        punct!(","),
        lit_int!(67),
        punct!(","),
        lit_int!(89),
        punct!(","),
        lit_int!(10),
        punct!(","),
        lit_int!(11),
        punct!(","),
        lit_int!(12),
        punct!(","),
        punct!("}"),
        punct!(";")
      ])
    );
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_6() {
    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("OBJ_LIKE", ["/* whie space */", "(", "1", "-", "1", ")", "/* other */"]);
    assert!(!macro_set.define_var_macro("OBJ_LIKE", ["(", "1", "-", "1", ")"]));

    assert!(!macro_set.define_fn_macro("FUNC_LIKE", ["a"], ["(", "a", ")"]));
    assert!(!macro_set.define_fn_macro(
      "FUNC_LIKE",
      ["a"],
      ["(", "/* note the white space */", "a", "/* other stuff on this line \n */", ")"]
    ));

    let mut macro_set = MacroSet::new();

    macro_set.define_var_macro("OBJ_LIKE", ["(", "0", ")"]);
    assert!(macro_set.define_var_macro("OBJ_LIKE", ["(", "1", "-", "1", ")"]));

    macro_set.define_fn_macro("FUNC_LIKE", ["b"], ["(", "a", ")"]);
    assert!(macro_set.define_fn_macro("FUNC_LIKE", ["b"], ["(", "b", ")"]));
  }

  #[test]
  fn parse_c_std_6_10_3_5_example_7() {
    let mut macro_set = MacroSet::new();

    macro_set.define_fn_macro("debug", ["..."], ["fprintf", "(", "stderr", ",", "__VA_ARGS__", ")"]);
    macro_set.define_fn_macro("showlist", ["..."], ["puts", "(", "#", "__VA_ARGS__", ")"]);
    macro_set.define_fn_macro(
      "report",
      ["test", "..."],
      ["(", "(", "test", ")", "?", "puts", "(", "#", "test", ")", ":", "printf", "(", "__VA_ARGS__", ")", ")"],
    );

    assert_eq!(
      macro_set.expand(&["debug", "(", "\"Flag\"", ")", ";"]),
      Ok(token_vec![
        id!(fprintf),
        punct!("("),
        id!(stderr),
        punct!(","),
        lit_string!("Flag"),
        punct!(")"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&["debug", "(", "\"X = %d\\n\"", ",", "x", ")", ";"]),
      Ok(token_vec![
        id!(fprintf),
        punct!("("),
        id!(stderr),
        punct!(","),
        lit_string!("X = %d\n"),
        punct!(","),
        id!(x),
        punct!(")"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&["showlist", "(", "The", "first", ",", "second", ",", "and", "third", "items", ".", ")", ";"]),
      Ok(token_vec![
        id!(puts),
        punct!("("),
        lit_string!("The first, second, and third items."),
        punct!(")"),
        punct!(";")
      ])
    );
    assert_eq!(
      macro_set.expand(&["report", "(", "x", ">", "y", ",", "\"x is %d but y is %d\"", ",", "x", ",", "y", ")", ";"]),
      Ok(token_vec![
        punct!("("),
        punct!("("),
        id!(x),
        punct!(">"),
        id!(y),
        punct!(")"),
        punct!("?"),
        id!(puts),
        punct!("("),
        lit_string!("x > y"),
        punct!(")"),
        punct!(":"),
        id!(printf),
        punct!("("),
        lit_string!("x is %d but y is %d"),
        punct!(","),
        id!(x),
        punct!(","),
        id!(y),
        punct!(")"),
        punct!(")"),
        punct!(";")
      ])
    );
  }
}
