/* Syntax:

<agent_name> = [A-Z][_a-zA-Z0-9]*
<port_name> = [a-z][_a-zA-Z0-9]*
<agent> = <agent_name> ( $(<port_name>),* )
<agent_def> = agent <agent>
<nested_agent> = <agent_name> ( $(<port_name> | <nested_agent>),* )
<connector> = <nested_agent> | <port_name>
<connection> = <connector> ~ <connector>
<connections> = $(<connection>),+
<active_pair> = <agent> ~ <agent>
<rule_def> = rule <active_pair> = <connections>
<definition> = <agent_def> | <rule_def>
<init> = init <connections>
<ast> = $(<definition>)+ <init>

Note: Whitespace and comments are ignored.
Single-line comments start with `//` and end with a newline.
Multi-line comments start with `/*` and end with `*/`, and can be nested.
*/

pub mod ast;
pub mod display;
pub mod flatten;

use crate::{
  error::{print_program_errors, IvmResult},
  lexer::Token,
  parser::{ast::*, display::fmt_connections, flatten::flatten_connections},
};
use chumsky::{
  input::{Stream, ValueInput},
  prelude::*,
};
use itertools::{Either, Itertools};
use logos::Logos;

impl Ast {
  // Constructs parser and returns it
  fn parser<'a, I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>>()
  -> impl Parser<'a, I, Ast, extra::Err<Rich<'a, Token<'a>>>> {
    let agent_name = select! { Token::Agent(s) => s.to_string() }.labelled("agent");

    let port_name = select! { Token::Port(s) => s.to_string() }.labelled("port");

    let agent = agent_name
      .then(
        port_name
          .separated_by(just(Token::Comma))
          .allow_trailing()
          .collect()
          .delimited_by(just(Token::LParen), just(Token::RParen))
          .or_not(),
      )
      .map(|(agent, ports)| Agent { agent, ports: ports.unwrap_or_default() })
      .labelled("agent");

    let nested_agent = recursive(|nested_agent| {
      agent_name
        .then(
          port_name
            .map(NestedConnector::Port)
            .or(nested_agent.map(NestedConnector::Agent))
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .or_not(),
        )
        .map(|(agent, ports)| NestedAgent { agent, ports: ports.unwrap_or_default() })
        .labelled("agent")
    });

    // Agent and rule definitions can be interleaved, but are separated before storing in Ast
    enum Definition {
      Agent(Spanned<Agent>),
      Rule(Rule),
    }

    let agent_def = just(Token::KeywordAgent)
      .ignore_then(agent)
      .map_with_span(|agent, span| Definition::Agent(Spanned::new(span, agent)));

    let connector = nested_agent.map(NestedConnector::Agent).or(port_name.map(NestedConnector::Port));

    let connection = connector
      .clone()
      .then_ignore(just(Token::Tilde))
      .then(connector)
      .map(|(lhs, rhs)| NestedConnection { lhs, rhs });

    let connections = connection.separated_by(just(Token::Comma)).allow_trailing().collect::<Vec<_>>();

    let rule_def = just(Token::KeywordRule)
      .ignore_then(connections.clone())
      .then_ignore(just(Token::Equals))
      .then(connections.clone())
      .try_map(|(rule_lhs, rule_rhs), span| {
        if let [NestedConnection { lhs: NestedConnector::Agent(lhs), rhs: NestedConnector::Agent(rhs) }] =
          rule_lhs.as_slice()
        {
          let mut next_port_idx = 0;
          let (lhs, lhs_connections) = lhs.clone().flatten(&mut next_port_idx);
          let (rhs, rhs_connections) = rhs.clone().flatten(&mut next_port_idx);

          if !lhs_connections.is_empty() || !rhs_connections.is_empty() {
            Err(Rich::custom(span, format!("Rule LHS cannot match deeper than active pair, {}", span)))
          } else {
            let lhs = ActivePair { lhs, rhs };
            Ok(Definition::Rule(Rule { lhs, rhs: flatten_connections(rule_rhs), span }))
          }
        } else {
          Err(Rich::custom(span, format!("Rule LHS must be an active pair, not {}", span)))
        }
      });

    // TODO: For showing better errors to user, allow parsing repeated `init` statements and reject during validation
    let init = just(Token::KeywordInit).ignore_then(connections);

    let definition = agent_def.or(rule_def);

    let ast = definition
      .repeated()
      .at_least(1)
      .collect::<Vec<_>>()
      .then(init.map_with_span(|init, init_span| (init, init_span)))
      .validate(|(definitions, (init_connections, init_span)), span, emitter| {
        // Separate the interleaved agent and rule definitions
        let (agents, rules) = definitions.into_iter().partition_map(|def| match def {
          Definition::Agent(agent) => Either::Left(agent),
          Definition::Rule(rule) => Either::Right(rule),
        });

        // Nesting is syntactic sugar, flatten all connections for further processing
        let init_connections = flatten_connections(init_connections);

        // Root port must be referenced exactly once
        let refs_to_root_port = init_connections
          .iter()
          .flat_map(|conn| conn.port_names_iter())
          .filter(|port| *port == ROOT_PORT_NAME)
          .count();
        if refs_to_root_port != 1 {
          emitter.emit(Rich::custom(
            span,
            format!(
              "`{INIT_CONNECTIONS}` connections must connect exactly one port to `{ROOT_PORT_NAME}`:\n{}",
              fmt_connections(&init_connections)
            ),
          ));
        }

        Ast { agents, rules, init: Spanned { span: init_span, val: init_connections } }
      });

    ast
  }

  pub fn parse(src: &str) -> IvmResult<Self> {
    let token_iter = Token::lexer(src).spanned().map(|(tok, span)| (tok, span.into()));
    let token_stream = Stream::from_iter(token_iter).spanned((src.len() .. src.len()).into());
    Self::parser().parse(token_stream).into_result().map_err(|e| print_program_errors(e, src))
  }
}
