use std::{collections::HashMap, env, fs, process::exit};

use clang::{source::SourceRange, Clang, EntityKind, EntityVisitResult, Index};
use glob::glob;
use pretty_assertions::StrComparison;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, TokenStreamExt};
use yansi::{
  Color::{Green, Red},
  Style,
};

use cmacro::{CodegenContext, ExpansionError, FnMacro, MacroSet, VarMacro};

fn location_in_scope(r: &SourceRange) -> bool {
  let start = r.get_start();
  let location = start.get_spelling_location();
  start.is_in_main_file() && !start.is_in_system_header() && location.file.is_some()
}

fn file_visit_macros<F: FnMut(EntityKind, String, Option<Vec<String>>, Vec<String>)>(file: &str, mut visitor: F) {
  let clang = Clang::new().unwrap();

  let index = Index::new(&clang, false, true);

  let tu = index
    .parser(file)
    .arguments(&["-std=c11"])
    .detailed_preprocessing_record(true)
    .skip_function_bodies(true)
    .parse()
    .unwrap();

  let entity = tu.get_entity();
  entity.visit_children(|cur, _parent| {
    let range = cur.get_range().unwrap();
    if !location_in_scope(&range) {
      return EntityVisitResult::Continue
    }

    match cur.get_kind() {
      kind @ EntityKind::FunctionDecl => {
        let mut tokens = range.tokenize().into_iter().map(|token| token.get_spelling());

        let return_type = tokens.next().unwrap();
        let name = tokens.next().unwrap();
        tokens.next();

        let mut args = vec![];

        let mut it = tokens.take_while(|token| token != ")");
        while let Some(token) = it.next() {
          if token == "," {
            args.push(it.next().unwrap());
            continue
          }

          if let Some(last_arg) = args.last_mut() {
            last_arg.push(' ');
            last_arg.push_str(&token);
          } else {
            args.push(token);
          }
        }

        visitor(kind, name, Some(args), vec![return_type])
      },
      kind @ EntityKind::MacroDefinition => {
        let range = cur.get_range().unwrap();
        if !location_in_scope(&range) {
          return EntityVisitResult::Continue
        }

        let mut tokens: Vec<_> = range.tokenize().into_iter().map(|token| token.get_spelling()).collect();

        let name = tokens.remove(0);

        let args = if cur.is_function_like_macro() {
          let n = tokens.iter().position(|t| t == ")").unwrap();

          let args = tokens.drain(0..(n + 1)).skip(1).take(n - 1).filter(|t| t != ",").collect::<Vec<_>>();

          Some(args)
        } else {
          None
        };

        visitor(kind, name, args, tokens)
      },
      _ => (),
    }

    EntityVisitResult::Continue
  });
}

#[derive(Debug, Default)]
struct TestContext {
  pub macros: Vec<String>,
  pub functions: HashMap<String, (Vec<String>, String)>,
  pub macro_set: MacroSet,
}

impl CodegenContext for TestContext {
  fn resolve_ty(&self, name: &str) -> Option<syn::Type> {
    if name == "size_t" {
      return None
    }

    let ty = proc_macro2::Ident::new(name, proc_macro2::Span::call_site());
    Some(syn::parse_quote! { #ty })
  }

  fn function(&self, name: &str) -> Option<(Vec<syn::Type>, syn::Type)> {
    let (arg_tys, ret_ty) = self.functions.get(name)?;

    let parse_type = |ty: &str| {
      let ty = ty.parse::<cmacro::Type>().ok()?;
      let ty = ty.to_rust_ty(self)?;
      Some(ty)
    };

    let arg_tys = arg_tys.iter().map(|ty| parse_type(ty.as_str())).collect::<Option<Vec<_>>>()?;

    Some((arg_tys, parse_type(ret_ty.as_str())?))
  }
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
  let test_name: Option<String> = env::args().nth(1);

  let mut errors = HashMap::new();

  for entry in glob("./tests/fixtures/*.h").unwrap() {
    let entry = entry?;
    let header_name = entry.as_path().file_stem().and_then(|s| s.to_str()).unwrap();
    let header_path = entry.as_path().display().to_string();
    let output_path = entry.as_path().with_extension("rs");

    if let Some(ref test_name) = test_name {
      if !test_name.starts_with('-') && !header_name.contains(test_name) {
        continue
      }
    }

    print!("test {} ... ", header_name);

    let mut context = TestContext::default();

    file_visit_macros(&header_path, |kind, name, args, mut value| match kind {
      EntityKind::FunctionDecl => {
        context.functions.insert(name, (args.unwrap(), value.remove(0)));
      },
      EntityKind::MacroDefinition => {
        if let Some(args) = args {
          context.macro_set.define_fn_macro(name.clone(), args, value);
        } else {
          context.macro_set.define_var_macro(name.clone(), value);
        }

        context.macros.push(name);
      },
      _ => (),
    });

    let mut generated_code = TokenStream::new();

    for name in &context.macros {
      match context.macro_set.expand_fn_macro(name) {
        Ok((arg_names, fn_macro)) => match FnMacro::parse(name.as_str(), &arg_names, &fn_macro) {
          Ok(mut fn_macro) => match fn_macro.generate(&context) {
            Ok(tokens) => generated_code.append_all(tokens),
            Err(err) => eprintln!("Error generating function-like macro `{name}`: {err}"),
          },
          Err(err) => eprintln!("Error parsing function-like macro `{name}`: {err}"),
        },
        Err(ExpansionError::MacroNotFound) => (),
        Err(err) => eprintln!("Error for `{name}`: {err:?}"),
      }

      match context.macro_set.expand_var_macro(name) {
        Ok(var_macro) => match VarMacro::parse(name.as_str(), &var_macro) {
          Ok(mut var_macro) => match var_macro.generate(&context) {
            Ok((value, ty)) => {
              let name = Ident::new(name, Span::call_site());
              let ty = ty.unwrap_or(quote! { _ });
              generated_code.append_all(quote! {
                pub const #name: #ty = #value;
              })
            },
            Err(err) => eprintln!("Error generating variable-like macro `{name}`: {err}"),
          },
          Err(err) => eprintln!("Error parsing variable-like macro `{name}`: {err}"),
        },
        Err(ExpansionError::MacroNotFound) => (),
        Err(err) => eprintln!("Error for `{name}`: {err:?}"),
      }
    }

    let expected = prettyplease::unparse(&syn::parse_str::<syn::File>(&fs::read_to_string(output_path)?)?);

    let f = match syn::parse2::<syn::File>(generated_code.clone()) {
      Ok(f) => f,
      Err(err) => {
        use annotate_snippets::snippet::*;

        let span = err.span();

        let source = generated_code.to_string();

        let err_string = err.to_string();
        let snippet = Snippet {
          title: Some(Annotation { label: Some(&err_string), id: None, annotation_type: AnnotationType::Error }),
          footer: vec![],
          slices: vec![Slice {
            source: &source,
            line_start: span.start().line,
            origin: None,
            fold: false,
            annotations: vec![],
          }],
          opt: Default::default(),
        };

        let snippet = annotate_snippets::display_list::DisplayList::from(snippet).to_string();

        println!(" {}", Style::new(Red).paint("FAILED"));
        errors.insert(header_name.to_owned(), (String::new(), expected, Some(snippet)));
        continue;
      },
    };

    let actual = prettyplease::unparse(&f);

    if actual == expected {
      println!(" {}", Style::new(Green).paint("ok"));
    } else {
      println!(" {}", Style::new(Red).paint("FAILED"));
      errors.insert(header_name.to_owned(), (actual, expected, None));
    }
  }

  if !errors.is_empty() {
    println!("\nfailures:\n");

    for (header_name, (actual, expected, snippet)) in &errors {
      let diff = StrComparison::new(expected, actual);
      print!("---- {} diff ----\n{}", header_name, diff);

      if let Some(snippet) = snippet {
        print!("---- {} parse ----\n{}", header_name, snippet);
      }
    }

    println!("\nfailures:");

    for header_name in errors.keys() {
      println!("    {}", header_name);
    }

    println!();
    exit(1);
  }

  Ok(())
}
