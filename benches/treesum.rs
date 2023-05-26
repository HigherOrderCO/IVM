use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ivm::parser::ast::Ast;

fn criterion_benchmark(c: &mut Criterion) {
  fn nat(n: usize) -> String {
    if n == 0 { "Zero".to_string() } else { format!("Succ({})", nat(n - 1)) }
  }

  let n = 4;
  // let src = include_str!("treesum.ivm");
  let src = &std::fs::read_to_string("./benches/treesum.ivm").unwrap();
  let src = &src.replace("{n}", &nat(n));
  let ast = Ast::parse(src).unwrap();
  let ast = ast.validate(src).unwrap();
  let program = ast.into_inet_program(true);
  c.bench_function(&format!("treesum {n}"), |b| {
    b.iter(|| {
      let mut program = black_box(program.clone());
      program.reduce();
      /* let result = program.read_back();
      let res = nat(1 << n);
      assert_eq!(result, format!("root ~ {res}")); */
    })
  });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
