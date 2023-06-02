use clap::Parser;
use color_eyre::eyre::Result;
use ivm::parser::ast::Ast;
use std::{env, fs, path::PathBuf, time::Instant};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
  /// Don't print final reduced net
  #[arg(short, long)]
  ignore_final_reduced_net: bool,

  /// Print elapsed time, rewrites, rewrites-per-second
  #[arg(short, long)]
  stats: bool,

  /// Print net after every reduction step
  #[arg(short, long)]
  debug: bool,

  /// File containing the source code of the program
  file_path: PathBuf,
}

fn main() -> Result<()> {
  if env::var("RUST_LIB_BACKTRACE").is_err() {
    // Don't print backtrace for user program errors
    env::set_var("RUST_LIB_BACKTRACE", "0");
  }
  color_eyre::install()?; // Pretty printed errors

  let args = Args::parse();

  let src = &fs::read_to_string(&args.file_path)?;
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let pre_preduce = false;
  let mut program = ast.into_inet_program(pre_preduce);

  let time = Instant::now();
  let reduction_count = if args.debug {
    println!("{}", program.read_back());
    let mut reduction_count = 0;
    while program.scan_active_pairs_and_reduce_step() {
      println!("[{reduction_count}] {}", program.read_back());
      reduction_count += 1;
    }
    reduction_count
  } else {
    program.reduce()
  };
  let elapsed_s = time.elapsed().as_secs_f64();

  if !args.ignore_final_reduced_net {
    println!("{}", program.read_back());
  }
  if !args.ignore_final_reduced_net && args.stats {
    println!();
  }
  if args.stats {
    let rps_m = reduction_count as f64 / elapsed_s / 1_000_000.0;
    println!("[TIME: {elapsed_s:.3}s | COST: {reduction_count} | RPS: {rps_m:.3}m]");
  }

  Ok(())
}
