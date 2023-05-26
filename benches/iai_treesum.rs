use iai::black_box;
use ivm::parser::ast::Ast;

fn run(n: usize) {
  fn nat(n: usize) -> String {
    if n == 0 { "Zero".to_string() } else { format!("Succ({})", nat(n - 1)) }
  }

  let src = include_str!("treesum.ivm");
  let src = &src.replace("{n}", &nat(n));
  let ast = Ast::parse(src).unwrap();
  let ast = ast.validate(src).unwrap();
  let mut program = ast.into_inet_program(false);
  program.reduce();
  /* let result = program.read_back();
  let res = nat(1 << n);
  assert_eq!(result, format!("root ~ {res}")); */
}

fn iai_benchmark_short() {
  run(black_box(3))
}

fn iai_benchmark_long() {
  run(black_box(23))
}

iai::main!(iai_benchmark_short, iai_benchmark_long);
