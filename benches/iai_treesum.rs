use iai::black_box;
use ivm::{inet_program::INetProgram, parser::ast::Ast};

fn nat(n: usize) -> String {
  if n == 0 { "Zero".to_string() } else { format!("Succ({})", nat(n - 1)) }
}

fn setup(n: usize) -> INetProgram {
  let src = include_str!("treesum_generic.ivm");
  let src = &src.replace("{n}", &nat(n));
  let ast = Ast::parse(src).unwrap();
  let ast = ast.validate(src).unwrap();
  let pre_preduce = false;
  ast.into_inet_program(pre_preduce)
}

fn run(n: usize) {
  let mut program = setup(n);
  program.reduce();
  /* let result = program.read_back();
  let res = nat(1 << n);
  assert_eq!(result, format!("root ~ {res}")); */
}

const SHORT_N: usize = 3;
const LONG_N: usize = 18;

fn iai_benchmark_setup_short() {
  setup(SHORT_N);
}

fn iai_benchmark_setup_long() {
  setup(LONG_N);
}

fn iai_benchmark_short() {
  run(black_box(SHORT_N))
}

fn iai_benchmark_long() {
  run(black_box(LONG_N))
}

iai::main!(iai_benchmark_setup_short, iai_benchmark_setup_long, iai_benchmark_short, iai_benchmark_long);
