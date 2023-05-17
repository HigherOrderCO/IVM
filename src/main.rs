use color_eyre::eyre::Result;
use ivm::parser::{ast::Ast, display::fmt_nested_connections, flatten::unflatten_connections};
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
  let rule_book = ast.build_rule_book(src)?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  net.reduce_full(&rule_book);
  let connections = net.read_back();
  let connections = unflatten_connections(connections);
  let connections = fmt_nested_connections(&connections);
  println!("{connections}");
  Ok(())
}
