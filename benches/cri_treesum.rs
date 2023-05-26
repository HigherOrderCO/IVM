use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ivm::{inet_program::INetProgram, parser::ast::Ast};

fn nat(n: usize) -> String {
  if n == 0 { "Zero".to_string() } else { format!("Succ({})", nat(n - 1)) }
}

fn setup(n: usize) -> INetProgram {
  // let src = include_str!("treesum.ivm");
  let src = &std::fs::read_to_string("./benches/treesum.ivm").unwrap();
  let src = &src.replace("{n}", &nat(n));
  let ast = Ast::parse(src).unwrap();
  let ast = ast.validate(src).unwrap();
  let reduce_rule_rhs_subnets = true;
  ast.into_inet_program(reduce_rule_rhs_subnets)
}

fn run(mut program: INetProgram) {
  program.reduce();
  /* let result = program.read_back();
  let res = nat(1 << n);
  assert_eq!(result, format!("root ~ {res}")); */
}

const SHORT_N: usize = 3;
const LONG_N: usize = 18;

fn cri_benchmark_short(c: &mut Criterion) {
  let n = SHORT_N;
  let program = setup(black_box(n));
  c.bench_function(&format!("treesum {n}"), |b| b.iter(|| run(black_box(program.clone()))));
}

fn cri_benchmark_long(c: &mut Criterion) {
  let n = LONG_N;
  let program = setup(black_box(n));
  c.bench_function(&format!("treesum {n}"), |b| b.iter(|| run(black_box(program.clone()))));
}

criterion_group!(benches, cri_benchmark_short, cri_benchmark_long);
criterion_main!(benches);
