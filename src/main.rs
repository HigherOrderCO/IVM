use color_eyre::eyre::Result;
use ivm::parser::ast::Ast;
use std::{env, fs, time::Instant};

// TODO: Use clap when parsing more complex arguments

fn main() -> Result<()> {
  if env::var("RUST_LIB_BACKTRACE").is_err() {
    // Don't print backtrace for user program errors
    env::set_var("RUST_LIB_BACKTRACE", "0");
  }
  color_eyre::install()?; // Pretty printed errors

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
  while program.scan_active_pairs_and_reduce_step() {
    let result = program.read_back();
    println!("[{reduction_count}] {result}");
    reduction_count += 1;
  } */

  let time = Instant::now();
  let reduction_count = program.reduce();
  let elapsed_s = time.elapsed().as_secs_f64();

  let rps = reduction_count as f64 / elapsed_s;
  println!("[{reduction_count} R][{elapsed_s:.3} s][{rps:.3} RPS]\n{}", program.read_back());
  Ok(())
}
