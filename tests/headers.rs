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

use cmacro::{CodegenContext, FnMacro, VarMacro};

fn location_in_scope(r: &SourceRange) -> bool {
  let start = r.get_start();
  let location = start.get_spelling_location();
  start.is_in_main_file() && !start.is_in_system_header() && location.file.is_some()
}

fn file_visit_macros<F: FnMut(EntityKind, &str, Option<&[&str]>, &[&str])>(file: &str, mut visitor: F) {
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
        let args = tokens.take_while(|token| token != ")").collect::<Vec<_>>();
        let args = args.iter().map(|t| t.as_str()).collect::<Vec<&str>>();

        visitor(kind, &name, Some(args).as_deref(), &[&return_type])
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

        let args = args.as_ref().map(|args| args.iter().map(|t| t.as_str()).collect::<Vec<&str>>());
        let tokens = tokens.iter().map(|t| t.as_str()).collect::<Vec<&str>>();

        visitor(kind, &name, args.as_deref(), &tokens)
      },
      _ => (),
    }

    EntityVisitResult::Continue
  });
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

    #[derive(Debug, Clone, Default)]
    struct Context {
      pub macros: Vec<String>,
      pub functions: HashMap<String, (Vec<String>, String)>,
      pub fn_macros: HashMap<String, FnMacro>,
      pub var_macros: HashMap<String, VarMacro>,
    }

    impl CodegenContext for Context {
      fn function(&self, name: &str) -> Option<(Vec<String>, String)> {
        self.functions.get(name).cloned()
      }

      fn function_macro(&self, name: &str) -> Option<&FnMacro> {
        self.fn_macros.get(name)
      }

      fn variable_macro(&self, name: &str) -> Option<&VarMacro> {
        self.var_macros.get(name)
      }
    }

    let mut context = Context::default();

    file_visit_macros(&header_path, |kind, name, args, value| match kind {
      EntityKind::FunctionDecl => {
        context.functions.insert(
          name.to_owned(),
          (args.unwrap().iter().map(|&token| token.to_owned()).collect(), value[0].to_owned()),
        );
      },
      EntityKind::MacroDefinition => {
        if let Some(args) = args {
          match FnMacro::parse(name, args, value) {
            Ok(fn_macro) => {
              context.fn_macros.insert(name.to_owned(), fn_macro);
            },
            Err(err) => {
              eprintln!("Failed to parse macro {}({}): {}", name, format!("({})", args.join(", ")), err);
            },
          }
        } else {
          match VarMacro::parse(name, value) {
            Ok(var_macro) => {
              context.var_macros.insert(name.to_owned(), var_macro);
            },
            Err(err) => {
              eprintln!("Failed to parse macro {}: {}", name, err)
            },
          }
        }

        context.macros.push(name.to_owned());
      },
      _ => (),
    });

    let mut f = TokenStream::new();

    for name in &context.macros {
      if let Some(fn_macro) = context.function_macro(name) {
        let mut fn_macro = fn_macro.clone();
        if let Ok(tokens) = fn_macro.generate(&context) {
          f.append_all(tokens);
        }
      }

      if let Some(var_macro) = context.variable_macro(name) {
        let mut var_macro = var_macro.clone();
        if let Ok((value, ty)) = var_macro.generate(&context) {
          let name = Ident::new(name, Span::call_site());
          let ty = ty.unwrap_or(quote! { _ });
          f.append_all(quote! {
            pub const #name: #ty = #value;
          })
        }
      }
    }

    let expected = prettyplease::unparse(&syn::parse2::<syn::File>(f)?);
    let actual = prettyplease::unparse(&syn::parse_str::<syn::File>(&fs::read_to_string(output_path)?)?);

    if actual == expected {
      println!(" {}", Style::new(Green).paint("ok"));
    } else {
      println!(" {}", Style::new(Red).paint("FAILED"));
      errors.insert(header_name.to_owned(), (actual, expected));
    }
  }

  if !errors.is_empty() {
    println!("\nfailures:\n");

    for (header_name, (actual, expected)) in &errors {
      let diff = StrComparison::new(expected, actual);
      print!("---- {} diff ----\n{}", header_name, diff);
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
