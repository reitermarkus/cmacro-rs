pub fn tokenize_name<'t>(input: &'t [u8]) -> Vec<&'t [u8]> {
  let mut tokens = vec![];

  let mut i = 0;

  loop {
    match input.get(i) {
      Some(b'a'..=b'z' | b'A'..=b'Z' | b'_') => {
        let start = i;
        i += 1;

        while let Some(b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'0'..=b'9') = input.get(i) {
          i += 1;
        }

        tokens.push(&input[start..i]);
      },
      Some(b'(' | b')' | b',') => {
        tokens.push(&input[i..(i + 1)]);
        i += 1;
      },
      Some(b'/') if matches!(input.get(i + 1), Some(b'*')) => {
        let start = i;
        i += 2;

        while let Some(c) = input.get(i) {
          i += 1;

          if *c == b'*' {
            if let Some(b'/') = input.get(i) {
              i += 1;
              tokens.push(&input[start..i]);
              break
            }
          }
        }
      },
      Some(b'.') if matches!(input.get(i..(i + 3)), Some(b"...")) => {
        tokens.push(&input[i..(i + 3)]);
        i += 3;
      },
      Some(b' ') => {
        i += 1;
      },
      Some(c) => unreachable!("{}", *c as char),
      None => break,
    }
  }

  tokens
}
