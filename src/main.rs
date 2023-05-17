use color_eyre::eyre::Result;
use ivm::parser::ast::Ast;
use std::{env, fs};

fn main() -> Result<()> {
  if env::var("RUST_LIB_BACKTRACE").is_err() {
    // Don't print backtrace for user program errors
    env::set_var("RUST_LIB_BACKTRACE", "0");
  }
  color_eyre::install()?;

  let args: Vec<String> = env::args().collect();
  if args.len() != 2 {
    eprintln!("Usage: ivm <filename>");
    std::process::exit(1);
  }
  let src = &fs::read_to_string(&args[1])?;
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.to_inet_program();
  program.reduce();
  let result = program.read_back();
  println!("{result}");
  Ok(())
}
