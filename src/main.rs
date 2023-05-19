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
  let mut program = ast.into_inet_program();

  /* println!("{}", program.read_back());
  let mut reduction_count = 0;
  let mut prev_states = HashSet::new();
  while program.reduce_step() {
    let result = program.read_back();
    println!("[{reduction_count}] {result}");
    reduction_count += 1;
  } */

  let reduction_count = program.reduce();
  println!("[{reduction_count}] {}", program.read_back());
  Ok(())
}
