pub mod ast;
pub mod display;
pub mod flatten;

use crate::{
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
	fn parser<'a, I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>>()
	-> impl Parser<'a, I, Ast, extra::Err<Rich<'a, Token<'a>>>> {
		#[derive(Debug, Clone)]
		pub enum Definition {
			Agent(Agent),
			Rule(Rule),
		}

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

		let agent_def = just(Token::KeywordAgent).ignore_then(agent).map(Definition::Agent);

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
				if let [
					NestedConnection { lhs: NestedConnector::Agent(lhs), rhs: NestedConnector::Agent(rhs) },
				] = rule_lhs.as_slice()
				{
					let mut next_port_idx = 0;
					let (lhs, lhs_connections) = lhs.clone().flatten(&mut next_port_idx);
					let (rhs, rhs_connections) = rhs.clone().flatten(&mut next_port_idx);
					if !lhs_connections.is_empty() || !rhs_connections.is_empty() {
						Err(Rich::custom(
							span,
							format!("Rule LHS cannot match deeper than active pair, {}", span),
						))
					} else {
						let lhs = ActivePair { lhs, rhs };
						Ok(Definition::Rule(Rule { lhs, rhs: flatten_connections(rule_rhs) }))
					}
				} else {
					Err(Rich::custom(span, format!("Rule LHS must be an active pair, not {}", span)))
				}
			});

		// TODO: For showing better errors to user, allow parsing repeated `init` statements and reject during validation
		let init = just(Token::KeywordInit).ignore_then(connections);

		let definition = agent_def.or(rule_def);
		definition.repeated().collect::<Vec<_>>().then(init).validate(
			|(definitions, init_connections), span, emitter| {
				let (agents, rules) = definitions.into_iter().partition_map(|def| match def {
					Definition::Agent(agent) => Either::Left(agent),
					Definition::Rule(rule) => Either::Right(rule),
				});

				let init_connections = flatten_connections(init_connections);

				let mut root_refs = 0;
				init_connections.iter().for_each(|conn| {
					fn visit_ports(obj: &Connector, cb: &mut impl FnMut(&str)) {
						match obj {
							Connector::Agent(Agent { agent: _, ports }) => {
								for port in ports {
									cb(port)
								}
							}
							Connector::Port(port) => cb(port),
						}
					}
					let mut cb = |port: &str| {
						if port == ROOT_PORT_NAME {
							root_refs += 1;
						}
					};
					visit_ports(&conn.lhs, &mut cb);
					visit_ports(&conn.rhs, &mut cb);
				});
				if root_refs != 1 {
					emitter.emit(Rich::custom(
						span,
						format!(
							"`{INIT_CONNECTIONS}` connections must connect exactly one port to `{ROOT_PORT_NAME}`:\n{}",
							fmt_connections(&init_connections)
						),
					));
				}

				Ast { agents, rules, init: init_connections }
			},
		)
	}

	// TODO: Return Result
	pub fn parse(src: &str) -> Option<Self> {
		use ariadne::{Color, Label, Report, ReportKind, Source};

		let token_iter = Token::lexer(src).spanned().map(|(tok, span)| (tok, span.into()));
		let token_stream = Stream::from_iter(token_iter).spanned((src.len() .. src.len()).into());
		match Self::parser().parse(token_stream).into_result() {
			Ok(ast) => Some(ast),
			Err(errs) => {
				errs.into_iter().for_each(|e| {
					Report::build(ReportKind::Error, (), e.span().start)
						.with_code(3)
						.with_message(e.to_string())
						.with_label(
							Label::new(e.span().into_range())
								.with_message(e.reason().to_string())
								.with_color(Color::Red),
						)
						.finish()
						.write(Source::from(src), std::io::stderr().lock())
						.unwrap()
				});
				None
			}
		}
	}
}
