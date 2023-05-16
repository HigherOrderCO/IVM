use crate::{
  lexer::*,
  parser::{
    ast::*,
    display::{fmt_connections, fmt_nested_connections},
    flatten::unflatten_connections,
  },
  Error,
};
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
fn test_parser() {
  assert_eq!(
    Ast::parse(
      "
		// Nat
		agent Zero
		agent Succ(pred)
		rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
		rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

		init root ~ Succ(Succ(Zero))
		"
    ),
    Some(Ast {
      agents: vec![Agent { agent: "Zero".to_string(), ports: vec![] }, Agent {
        agent: "Succ".to_string(),
        ports: vec!["pred".to_string()]
      }],
      rules: vec![
        Rule {
          lhs: ActivePair {
            lhs: Agent { agent: "Succ".to_string(), ports: vec!["ret".to_string()] },
            rhs: Agent { agent: "Zero".to_string(), ports: vec![] }
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
          ]
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
          ]
        }
      ],
      init: vec![
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
      ]
    })
  );
}

#[test]
fn test_ast_validation() {
  assert!(
    Ast::parse(
      "
		agent Zero()
		agent Succ(pred)
		rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
		rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

		agent Add(a, b)
		rule Add(ret, a) ~ Zero = ret ~ a
		rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

		init a ~ Succ(Zero), Add(root, a) ~ Succ(Succ(Succ(Zero)))
		"
    )
    .unwrap()
    .build_rule_book()
    .is_ok()
  );
}

#[test]
fn test_to_inet() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent Zero()
		agent Succ(pred)
		rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
		rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

		agent Add(a, b)
		rule Add(ret, a) ~ Zero = ret ~ a
		rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

		init a ~ Succ(Zero), Add(root, a) ~ Succ(Succ(Succ(Zero)))
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  eprintln!("{:#?}", net);
  assert_eq!(net.active_pairs().len(), 1, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  Ok(())
}

#[test]
fn test_reduce_inet() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent Zero()
		agent Succ(pred)
		rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
		rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

		agent Add(a, b)
		rule Add(ret, a) ~ Zero = ret ~ a
		rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

		init Add(root, Zero) ~ Zero
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  eprintln!("{:#?}", net);
  assert_eq!(net.active_pairs().len(), 1, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  net.reduce_full(&rule_book);
  eprintln!("{:#?}", net);
  eprintln!("net.active_pairs(): {:#?}", net.active_pairs());
  assert_eq!(net.active_pairs(), vec![(0, 3)], "{}\n{:#?}", ast, net);
  Ok(())
}

#[test]
fn test_reduce_inet_basic() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A(a)
		agent B
		rule A(a) ~ B = a ~ B
		init A(root) ~ B
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  eprintln!("{:#?}", net);
  assert_eq!(net.active_pairs().len(), 1, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  assert!(!net.reduce_step(&rule_book));
  eprintln!("{:#?}", net);
  eprintln!("net.active_pairs(): {:#?}", net.active_pairs());
  Ok(())
}

#[test]
fn test_reduce_inet_ctor_era() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A(a, b)
		agent B(c, d)
		agent Era
		rule A(e, f) ~ B(g, h) = e ~ g, f ~ h
		rule Era ~ Era =
		init A(root, i) ~ B(j, h), i ~ Era, j ~ Era, h ~ Era
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  eprintln!("{:#?}", net);
  assert_eq!(net.active_pairs().len(), 1, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  assert!(net.reduce_step(&rule_book));
  assert!(!net.reduce_step(&rule_book));
  eprintln!("{:#?}", net);
  eprintln!("net.active_pairs(): {:#?}", net.active_pairs());
  assert_eq!(net.active_pairs(), vec![(0, 4)], "{}\n{:#?}", ast, net);
  Ok(())
}

#[test]
fn test_reduce_inet_link_self_principal() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A(a, b)
		init A(root, i) ~ i
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  eprintln!("{:#?}", net);
  assert_eq!(net.active_pairs().len(), 0, "{}\n{:#?}", ast, net);
  assert!(!net.reduce_step(&rule_book));
  Ok(())
}

#[test]
fn test_reduce_inet_link_self_aux() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A(a, b)
		agent E
		rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
		init A(root, i) ~ A(j, j), i ~ E
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  assert_eq!(net.active_pairs().len(), 1, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  assert!(!net.reduce_step(&rule_book));
  eprintln!("{:#?}", net);
  Ok(())
}

#[test]
fn test_reduce_inet_link_self_double() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A(a, b)
		agent E
		rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
		init A(a, a) ~ A(b, b), root ~ E
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  assert_eq!(net.active_pairs().len(), 2, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  assert!(!net.reduce_step(&rule_book));
  eprintln!("{:#?}", net);
  assert_eq!(net.active_pairs(), vec![(0, 3)], "{}\n{:#?}", ast, net);
  Ok(())
}

#[test]
fn test_reduce_inet_link_pair_single() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A(a, b)
		agent E
		rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
		init A(root, j) ~ A(j, i), i ~ E
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  assert_eq!(net.active_pairs().len(), 1, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  assert!(!net.reduce_step(&rule_book));
  eprintln!("{:#?}", net);
  Ok(())
}

#[test]
fn test_reduce_inet_link_pair_double() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A(a, b)
		agent E
		rule A(e, f) ~ A(g, h) = e ~ g, f ~ h
		init A(a, b) ~ A(a, b), root ~ E
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  assert_eq!(net.active_pairs().len(), 2, "{}\n{:#?}", ast, net);
  assert!(net.reduce_step(&rule_book));
  assert!(!net.reduce_step(&rule_book));
  eprintln!("{:#?}", net);
  Ok(())
}

#[test]
fn test_inet_validate_basic() -> Result<(), Error> {
  let ast = Ast::parse(&format!(
    "
		agent A
		init root ~ a, a ~ A
		",
  ))
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let net = ast.to_inet(&rule_book.agent_name_to_id);
  eprintln!("{:#?}", net);
  net.validate();
  Ok(())
}

#[test]
fn test_inet_validate() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent A
		agent B(a, b)
		init root ~ r, r ~ A, B(a, a) ~ b, b ~ c, c ~ B(d, d), B(e, f) ~ g, g ~ B(f, e)
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  Ok(())
}

#[test]
fn test_inet_validate_transitive_connections() -> Result<(), Error> {
  let ast = Ast::parse(&format!(
    "
		agent A
		agent B
		agent C
		// init root ~ a, b ~ c, a ~ b, c ~ A
		// init root ~ a, b ~ c, a ~ b, c ~ A, d ~ B, d ~ C
		init root ~ B, C ~ a, b ~ c, a ~ b, c ~ A
		",
  ))
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let net = ast.to_inet(&rule_book.agent_name_to_id);
  eprintln!("{:#?}", net);
  net.validate();
  Ok(())
}

#[test]
fn test_inet_validate_transitive_connections_generated() -> Result<(), Error> {
  use rand::{seq::SliceRandom, thread_rng};

  let last = 'd';
  let mut connections = ('a' ..= last)
    .tuple_windows()
    .map(|(l, r)| Connection::new(Connector::Port(l.to_string()), Connector::Port(r.to_string())))
    .collect_vec();

  for _ in 0 .. 50 {
    connections.shuffle(&mut thread_rng());
    let connections = fmt_connections(&connections);
    let ast = Ast::parse(&format!(
      "
			agent A
			init root ~ a, {connections}, {last} ~ A
			",
    ))
    .unwrap();
    let rule_book = ast.build_rule_book()?;
    let net = ast.to_inet(&rule_book.agent_name_to_id);
    net.validate();
  }
  Ok(())
}

#[test]
fn test_duplicate_rule() {
  let ast = Ast::parse(&format!(
    "
		agent A
		agent B
		rule A ~ B = A ~ B
		rule B ~ A = A ~ B
		init root ~ A
		",
  ))
  .unwrap();
  assert!(ast.build_rule_book().is_err());
}

#[test]
fn test_read_back() -> Result<(), Error> {
  let ast = Ast::parse(
    "
		agent Zero
		agent Succ(pred)
		rule Succ(ret) ~ Zero = ret ~ Succ(Zero)
		rule Succ(ret) ~ Succ(p) = ret ~ Succ(Succ(p))

		agent Add(a, b)
		rule Add(ret, a) ~ Zero = ret ~ a
		rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b

		init a ~ Succ(Zero), Add(root, a) ~ Succ(Succ(Succ(Zero)))
		",
  )
  .unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  net.reduce_full(&rule_book);
  eprintln!("{:#?}", net);
  let connections = net.read_back();
  eprintln!("{}", fmt_connections(&connections));
  let connections = unflatten_connections(connections);
  let connections = fmt_nested_connections(&connections);
  eprintln!("{}", connections);
  assert_eq!(connections, "root ~ Succ(Succ(Succ(Succ(Zero))))");
  Ok(())
}

#[test]
fn test_unary_arith() -> Result<(), Error> {
  let ast = Ast::parse(
		"
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
		// rule AbsDiff(ret, a) ~ b = Add(ret, x) ~ y, Sub(x, a) ~ b, Sub(y, b) ~ a
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

		agent Or(ret, a)
		rule Or(ret, a) ~ T = ret ~ T, a ~ Era
		rule Or(ret, a) ~ F = ret ~ a

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
		",
	)
	.unwrap();
  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  net.reduce_full(&rule_book);
  let connections = net.read_back();
  let connections = unflatten_connections(connections);
  let connections = fmt_nested_connections(&connections);
  assert_eq!(connections, "root ~ T");
  Ok(())
}

#[test]
fn test_lambda() -> Result<(), Error> {
  let ast = Ast::parse(
    "
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
			",
  )
  .unwrap();

  let rule_book = ast.build_rule_book()?;
  let mut net = ast.to_inet(&rule_book.agent_name_to_id);
  net.validate();
  for step in 0 .. {
    let connections = net.read_back();
    let connections = unflatten_connections(connections);
    let connections = fmt_nested_connections(&connections);
    eprintln!("{step:2}: {connections}");
    if !net.reduce_step(&rule_book) {
      assert_eq!(connections, "root ~ Dup(Lam(_4, _4), Lam(_2, _2))");
      break;
    }
  }
  Ok(())
}
