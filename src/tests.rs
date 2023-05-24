use crate::{
  error::IvmResult,
  lexer::*,
  parser::{ast::*, display::fmt_connections},
};
use chumsky::span::SimpleSpan;
use itertools::Itertools;
use logos::Logos;

#[test]
fn test_lexer() {
  use Token::*;

  assert_eq!(Token::lexer(
    "//
    agent rule init()/**/,=~/*:<-_*/ /* loads and loads of senseless drivel /* --ahem, useful documentation */ featuring nested comments */
    // single line comment"
  ).collect::<Vec<_>>(),
  vec![
    KeywordAgent, KeywordRule, KeywordInit, LParen, RParen, Comma, Equals, Tilde,
  ]);
}

#[test]
fn test_parser() -> IvmResult<()> {
  assert_eq!(
    Ast::parse(
      "// Nat
      agent Zero
      agent Succ(pred)
      rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
      rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

      init root ~ Succ(Succ(Zero))
    "
    )?,
    Ast {
      agents: vec![
        Spanned { span: SimpleSpan::new(13, 23), val: Agent { agent: "Zero".to_string(), ports: vec![] } },
        Spanned {
          span: SimpleSpan::new(30, 46),
          val: Agent { agent: "Succ".to_string(), ports: vec!["pred".to_string()] }
        },
      ],
      rules: vec![
        Rule {
          lhs: ActivePair {
            lhs: Agent { agent: "Succ".to_string(), ports: vec!["ret".to_string()] },
            rhs: Agent { agent: "Zero".to_string(), ports: vec![] },
          },
          rhs: vec![
            Connection {
              lhs: Connector::Port("ret".to_string()),
              rhs: Connector::Agent(Agent { agent: "Succ".to_string(), ports: vec!["_0".to_string()] })
            },
            Connection {
              lhs: Connector::Port("_0".to_string()),
              rhs: Connector::Agent(Agent { agent: "Zero".to_string(), ports: vec![] })
            }
          ],
          span: SimpleSpan::new(53, 93),
        },
        Rule {
          lhs: ActivePair {
            lhs: Agent { agent: "Succ".to_string(), ports: vec!["ret".to_string()] },
            rhs: Agent { agent: "Succ".to_string(), ports: vec!["p".to_string()] }
          },
          rhs: vec![
            Connection {
              lhs: Connector::Port("ret".to_string()),
              rhs: Connector::Agent(Agent { agent: "Succ".to_string(), ports: vec!["_0".to_string()] })
            },
            Connection {
              lhs: Connector::Port("_0".to_string()),
              rhs: Connector::Agent(Agent { agent: "Succ".to_string(), ports: vec!["p".to_string()] })
            }
          ],
          span: SimpleSpan::new(100, 146),
        }
      ],
      init: Spanned {
        span: SimpleSpan::new(154, 182),
        val: vec![
          Connection {
            lhs: Connector::Port(ROOT_PORT_NAME.to_string()),
            rhs: Connector::Agent(Agent { agent: "Succ".to_string(), ports: vec!["_0".to_string()] })
          },
          Connection {
            lhs: Connector::Port("_0".to_string()),
            rhs: Connector::Agent(Agent { agent: "Succ".to_string(), ports: vec!["_1".to_string()] })
          },
          Connection {
            lhs: Connector::Port("_1".to_string()),
            rhs: Connector::Agent(Agent { agent: "Zero".to_string(), ports: vec![] })
          }
        ],
      },
    }
  );
  Ok(())
}

#[test]
fn test_add_one_three() -> IvmResult<()> {
  let src = "
    agent Zero
    agent Succ(pred)
    rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
    rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

    agent Add(ret, a)
    rule Add(ret, a) ~ Zero = ret ~ a
    rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

    init a ~ Succ(Zero), Add(root, a) ~ Succ(Succ(Succ(Zero)))
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  program.reduce();
  assert_eq!(program.read_back(), "root ~ Succ(Succ(Succ(Succ(Zero))))");
  Ok(())
}

#[test]
fn test_add_zero_zero() -> IvmResult<()> {
  let src = "
    agent Zero()
    agent Succ(pred)
    rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
    rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

    agent Add(a, b)
    rule Add(ret, a) ~ Zero = ret ~ a
    rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

    init Add(root, Zero) ~ Zero
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  eprintln!("{:#?}", program.net);
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  program.reduce();
  eprintln!("program.net.active_pairs(): {:#?}", program.net.scan_active_pairs());
  assert_eq!(program.net.scan_active_pairs(), vec![], "{}\n{:#?}", program.ast, program.net);
  assert_eq!(program.read_back(), "root ~ Zero");
  Ok(())
}

#[test]
fn test_reduce_inet_basic() -> IvmResult<()> {
  let src = "
    agent A(a)
    agent B
    rule A(a) ~ B = a ~ B
    init A(root) ~ B
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  eprintln!("program.net.active_pairs(): {:#?}", program.net.scan_active_pairs());
  assert_eq!(program.read_back(), "root ~ B");
  Ok(())
}

#[test]
fn test_reduce_inet_ctor_era() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent B(a, b)
    agent Era
    agent R
    rule A(e, f) ~ B(g, h) = e ~ g, f ~ h
    rule Era ~ Era =
    init A(root, i) ~ B(j, h), i ~ Era, j ~ R, h ~ Era
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  eprintln!("program.net.active_pairs(): {:#?}", program.net.scan_active_pairs());
  assert_eq!(program.net.scan_active_pairs(), vec![], "{}\n{:#?}", program.ast, program.net);
  program.reduce();
  let result = program.read_back();
  assert_eq!(result, "root ~ R");
  Ok(())
}

#[test]
fn test_reduce_inet_ctor_res_direct() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent B(a, b)
    agent Res
    rule A(e, f) ~ B(g, h) = e ~ g, f ~ h
    init A(root, i) ~ B(j, h), i ~ h, j ~ Res
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  for step in 0 .. {
    let result = program.read_back();
    eprintln!("{step:2}: {result}");
    if !program.net.scan_active_pairs_and_reduce_step(&program.rule_book) {
      assert_eq!(result, "root ~ Res");
      break;
    }
  }
  Ok(())
}

#[test]
fn test_subnet_root_node_self_links() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent B(a, b)
    agent Res
    agent SubnetPort1
    agent SubnetPort3

    // The subnet root node will have self-links: [(0, 2), (0, 3), (0, 0), (0, 1)]
    rule A(e, f) ~ B(g, h) = e ~ g, f ~ h

    init A(root, SubnetPort1) ~ B(j, SubnetPort3), j ~ Res
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  for step in 0 .. {
    let result = program.read_back();
    eprintln!("{step:2}: {result}");
    if !program.net.scan_active_pairs_and_reduce_step(&program.rule_book) {
      assert_eq!(result, "root ~ Res, SubnetPort1 ~ SubnetPort3");
      break;
    }
  }
  Ok(())
}

#[test]
fn test_reduce_inet_link_pair_intermediary() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent B(a, b)
    agent Tmp(a)
    agent Res
    rule A(e, f) ~ B(g, h) = Tmp(e) ~ g, f ~ h
    rule Tmp(a) ~ Res = a ~ Res
    init A(root, i) ~ B(j, h), i ~ h, j ~ Res
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  for step in 0 .. {
    let result = program.read_back();
    eprintln!("{step:2}: {result}");
    if !program.net.scan_active_pairs_and_reduce_step(&program.rule_book) {
      assert_eq!(result, "root ~ Res");
      break;
    }
  }
  Ok(())
}

#[test]
fn test_reduce_inet_link_self_principal() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    init A(root, i) ~ i
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 0, "{}\n{:#?}", program.ast, program.net);
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert_eq!(program.read_back(), "A(root, _1) ~ _1");
  Ok(())
}

#[test]
fn test_prevent_self_inlining() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent B(a, b, c)
    init A(root, B(a, a, i)) ~ i
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 0, "{}\n{:#?}", program.ast, program.net);
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert_eq!(program.read_back(), "A(root, B(_2, _2, _4)) ~ _4");
  Ok(())
}

#[test]
fn test_reduce_inet_link_self_aux() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent E
    rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
    init A(root, i) ~ A(j, j), i ~ E
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert_eq!(program.read_back(), "root ~ E");
  Ok(())
}

#[test]
fn test_reduce_inet_link_self_double() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent E
    rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
    init A(a, a) ~ A(b, b), root ~ E
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert_eq!(program.net.scan_active_pairs(), vec![], "{}\n{:#?}", program.ast, program.net);
  assert_eq!(program.read_back(), "root ~ E");
  Ok(())
}

#[test]
fn test_reduce_inet_link_pair_single() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent E
    rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
    init A(root, j) ~ A(j, i), i ~ E
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert_eq!(program.read_back(), "root ~ E");
  Ok(())
}

#[test]
fn test_reduce_inet_link_pair_double() -> IvmResult<()> {
  let src = "
    agent A(a, b)
    agent E
    rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
    init A(a, b) ~ A(a, b), root ~ E
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  assert_eq!(program.net.scan_active_pairs().len(), 1, "{}\n{:#?}", program.ast, program.net);
  assert!(program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert!(!program.net.scan_active_pairs_and_reduce_step(&program.rule_book));
  assert_eq!(program.read_back(), "root ~ E");
  Ok(())
}

#[test]
fn test_inet_validate_basic() -> IvmResult<()> {
  let src = "
    agent A
    init root ~ a, a ~ A
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  program.reduce();
  assert_eq!(program.read_back(), "root ~ A");
  Ok(())
}

#[test]
fn test_inet_validate() -> IvmResult<()> {
  let src = "
    agent A
    agent B(a, b)
    init root ~ r, r ~ A, B(a, a) ~ b, b ~ c, c ~ B(d, d), B(e, f) ~ g, g ~ B(f, e)
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  program.reduce();
  assert_eq!(program.read_back(), "root ~ A, B(_0, _0) ~ B(_2, _2), B(_4, _5) ~ B(_5, _4)");
  Ok(())
}

#[test]
fn test_inet_validate_transitive_connections() -> IvmResult<()> {
  let src = "
    agent A
    agent B
    agent C
    // init root ~ a, b ~ c, a ~ b, c ~ A
    // init root ~ a, b ~ c, a ~ b, c ~ A, d ~ B, d ~ C
    init root ~ B, C ~ a, b ~ c, a ~ b, c ~ A
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  program.reduce();
  assert_eq!(program.read_back(), "root ~ B, C ~ A");
  Ok(())
}

#[test]
fn test_inet_validate_transitive_connections_generated() -> IvmResult<()> {
  use rand::{seq::SliceRandom, thread_rng};

  let last = 'd';
  let mut connections = ('a' ..= last)
    .tuple_windows()
    .map(|(l, r)| Connection::new(Connector::Port(l.to_string()), Connector::Port(r.to_string())))
    .collect_vec();

  for _ in 0 .. 50 {
    connections.shuffle(&mut thread_rng());
    let connections = fmt_connections(&connections);
    let src = &format!(
      "
      agent A
      init root ~ a, {connections}, {last} ~ A
    "
    );
    let ast = Ast::parse(src)?;
    let ast = ast.validate(src)?;
    let mut program = ast.into_inet_program();
    program.reduce();
    assert_eq!(program.read_back(), "root ~ A");
  }
  Ok(())
}

#[test]
fn test_duplicate_rule() -> IvmResult<()> {
  let src = "
    agent A
    agent B
    rule A ~ B =
    rule B ~ A =
    init root ~ A
  ";
  let ast = Ast::parse(src)?;
  assert!(ast.validate(src).is_err());
  Ok(())
}

#[test]
fn test_read_back() -> IvmResult<()> {
  let src = "
    agent Zero
    agent Succ(pred)
    rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
    rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

    agent Add(a, b)
    rule Add(ret, a) ~ Zero = ret ~ a
    rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

    init a ~ Succ(Zero), Add(root, a) ~ Succ(Succ(Succ(Zero)))
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  program.reduce();
  assert_eq!(program.read_back(), "root ~ Succ(Succ(Succ(Succ(Zero))))");
  Ok(())
}

#[test]
fn test_unary_arith() -> IvmResult<()> {
  let src = "
    agent Zero
    agent Succ(pred)
    rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
    rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

    agent Add(a, b)
    rule Add(ret, a) ~ Zero = ret ~ a
    rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

    agent Era
    rule Era ~ Zero =
    rule Era ~ Succ(p) = Era ~ p

    agent Dup(a, b)
    rule Dup(a, b) ~ Zero = a ~ Zero, b ~ Zero
    rule Dup(a, b) ~ Succ(p) = a ~ Succ(a2), b ~ Succ(b2), Dup(a2, b2) ~ p

    agent Mul(a, b)
    rule Mul(ret, a) ~ Zero = ret ~ Zero, a ~ Era
    rule Mul(ret, a) ~ Succ(b) = Dup(a2, a3) ~ a, Add(ret, cnt) ~ a2, Mul(cnt, a3) ~ b

    agent T
    agent F

    rule Era ~ T =
    rule Era ~ F =

    agent IsZero(ret)
    rule IsZero(ret) ~ Zero = ret ~ T
    rule IsZero(ret) ~ Succ(a) = ret ~ F, a ~ Era

    agent Pred(ret)
    rule Pred(ret) ~ Zero = ret ~ Zero
    rule Pred(ret) ~ Succ(p) = ret ~ p

    agent Sub(ret, a)
    rule Sub(ret, a) ~ Zero = ret ~ a
    rule Sub(ret, a) ~ Succ(b) = Pred(pa) ~ a, Sub(ret, pa) ~ b,

    agent AbsDiff(ret, a)
    // rule AbsDiff(ret, a) ~ b = Add(ret, x) ~ y, Sub(x, a2) ~ Succ(b2), Sub(y, Succ(b3)) ~ a3, Dup(a2, a3) ~ a, Dup(b2, b3) ~ b
    rule AbsDiff(ret, a) ~ Zero = Add(ret, x) ~ y, Sub(x, a2) ~ Zero, Sub(y, Zero) ~ a3, Dup(a2, a3) ~ a
    rule AbsDiff(ret, a) ~ Succ(b) = Add(ret, x) ~ y, Sub(x, a2) ~ Succ(b2), Sub(y, Succ(b3)) ~ a3, Dup(a2, a3) ~ a, Dup(b2, b3) ~ b

    agent Eq(ret, a)
    // rule Eq(ret, a) ~ b = IsZero(ret) ~ d, AbsDiff(d, a) ~ b
    rule Eq(ret, a) ~ Zero = IsZero(ret) ~ d, AbsDiff(d, a) ~ Zero
    rule Eq(ret, a) ~ Succ(b) = IsZero(ret) ~ d, AbsDiff(d, a) ~ Succ(b)

    agent Ne(ret, a)
    // rule Ne(ret, a) ~ b = Not(ret) ~ cnt, Eq(cnt, a) ~ b
    rule Ne(ret, a) ~ Zero = Not(ret) ~ cnt, Eq(cnt, a) ~ Zero
    rule Ne(ret, a) ~ Succ(p) = Not(ret) ~ cnt, Eq(cnt, a) ~ Succ(p)

    agent And(ret, a)
    rule And(ret, a) ~ T = ret ~ a
    rule And(ret, a) ~ F = ret ~ F, a ~ Era

    // agent Or(ret, a)
    // rule Or(ret, a) ~ T = ret ~ T, a ~ Era
    // rule Or(ret, a) ~ F = ret ~ a

    agent Not(ret)
    rule Not(ret) ~ T = ret ~ F
    rule Not(ret) ~ F = ret ~ T

    init
      And(And(And(root, a), b), c) ~ d,
      Eq(a, Succ(Zero)) ~ Succ(Zero),
      Ne(b, Succ(Zero)) ~ Succ(Succ(Zero)),
      Ne(c, Succ(Succ(Zero))) ~ Succ(Zero),
      Eq(d, n5) ~ a5, Add(a5, Succ(Succ(Zero))) ~ Succ(Succ(Succ(Zero))),
        Sub(n5, n6) ~ Succ(Zero),
        Mul(n6, Succ(Succ(Zero))) ~ Succ(Succ(Succ(Zero)))
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  program.reduce();
  let result = program.read_back();
  assert_eq!(result, "root ~ T");
  Ok(())
}

#[test]
fn test_lambda() -> IvmResult<()> {
  let src = "
    agent Era
    agent Dup(a, b)
    agent Sup(a, b)
    agent Lam(var, body)
    agent App(arg, ret)

    rule Era ~ Era =
    rule Era ~ Dup(a, b) = Era ~ a, Era ~ b
    rule Era ~ Sup(a, b) = Era ~ a, Era ~ b
    rule Era ~ Lam(var, body) = Era ~ var, Era ~ body
    rule Era ~ App(arg, ret) = Era ~ arg, Era ~ ret

    // App-Lam
    rule App(arg, ret) ~ Lam(var, body) = ret ~ body, arg ~ var

    // Dup-Lam
    rule Dup(a, b) ~ Lam(var, body) =
      Sup(var1, var2) ~ var,
      Dup(body1, body2) ~ body,
      Lam(var1, body1) ~ a,
      Lam(var2, body2) ~ b

    // Dup-Sup 1
    rule Dup(a, b) ~ Sup(c, d) = a ~ c, b ~ d

    // Dup-Sup 2, can't have both Dup-Sup rules until we have labels
    // rule Dup(x, y) ~ Sup(a, b) =
    // 	Sup(xa, xb) ~ x,
    // 	Sup(ya, yb) ~ y,
    // 	Dup(xa, ya) ~ a,
    // 	Dup(xb, yb) ~ b

    // App-Sup
    rule App(arg, ret) ~ Sup(a, b) =
      Dup(arg1, arg2) ~ arg,
      App(arg1, ret1) ~ a, App(arg2, ret2) ~ b,
      Sup(ret1, ret2) ~ ret

    init
      two ~ Lam(f, Lam(x, body)),
        Dup(f1, f2) ~ f,
        App(x, c) ~ f1,
        App(c, body) ~ f2,

      id ~ Lam(y, y),

      fn ~ id, Era ~ two,
      // fn ~ two, Era ~ id,
      Dup(fn1, fn2) ~ fn,
      Dup(fn1, fn2) ~ root,
  ";
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  for step in 0 .. {
    let result = program.read_back();
    eprintln!("{step:2}: {result}");
    if !program.net.scan_active_pairs_and_reduce_step(&program.rule_book) {
      assert_eq!(result, "root ~ Dup(Lam(_4, _4), Lam(_2, _2))");
      break;
    }
  }
  Ok(())
}

#[test]
fn test_sum() -> IvmResult<()> {
  let src = include_str!("../examples/sum.ivm");
  let ast = Ast::parse(src)?;
  let ast = ast.validate(src)?;
  let mut program = ast.into_inet_program();
  program.reduce();
  let result = program.read_back();

  assert_eq!(result, "root ~ T");
  Ok(())
}

#[test]
fn test_treesum() -> IvmResult<()> {
  fn nat(n: usize) -> String {
    if n == 0 { "Zero".to_string() } else { format!("Succ({})", nat(n - 1)) }
  }

  let n = 4;
  let src = &std::fs::read_to_string("./benches/treesum.ivm").unwrap();
  let src = &src.replace("{n}", &nat(n));
  let ast = Ast::parse(src).unwrap();
  let ast = ast.validate(src).unwrap();
  let mut program = ast.into_inet_program();
  program.reduce();
  let result = program.read_back();
  let res = nat(1 << n);
  assert_eq!(result, format!("root ~ {res}"));
  Ok(())
}

#[test]
fn test_rule_rhs_reduction_doesnt_terminate() -> IvmResult<()> {
  let src = "
    agent A
    agent B
    rule A ~ B = A ~ B
    init root ~ A
  ";
  let ast = Ast::parse(src)?;
  assert!(ast.validate(src).is_ok());
  Ok(())
}
