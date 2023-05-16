use crate::{
  error::{construct_result, IvmErrors, IvmResult},
  inet::{port, INet, NodeIdx, NodePort},
  rule_book::{AgentId, RuleBook, ROOT_AGENT_ID},
};
use chumsky::{prelude::Rich, span::SimpleSpan};
use color_eyre::eyre::eyre;
use derive_new::new;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;

/// The first node in a net is the root node
pub const ROOT_NODE_IDX: NodeIdx = 0;

pub const ROOT_PORT_NAME: &str = "root";

/// Matches Token::KeywordInit
pub const INIT_CONNECTIONS: &str = "init";

/// Starts with uppercase letter (Token::Agent)
pub type AgentName = String;

/// Starts with lowercase letter (Token::Port)
pub type PortName = String;

pub type PortNameRef<'a> = &'a str;

// The syntax allows writing nested agents for convenience, this gets flattened during parsing.
// Also see flatten.rs

// Nested types

/// E.g. A(a, B(b, c))
#[derive(Debug, Clone, PartialEq)]
pub struct NestedAgent {
  pub agent: AgentName,
  pub ports: Vec<NestedConnector>, // Auxiliary ports
}

/// Like `Connector`, but can contain nested agents
/// E.g. A(a, B(b, c))
#[derive(Debug, Clone, PartialEq)]
pub enum NestedConnector {
  Agent(NestedAgent),
  Port(PortName),
}

/// E.g. A(a, B(b, c)) ~ C(D(d, e), f)
#[derive(new, Debug, Clone, PartialEq)]
pub struct NestedConnection {
  pub lhs: NestedConnector,
  pub rhs: NestedConnector,
}

// Flat types

/// E.g. A(b, c)
#[derive(Debug, Clone, PartialEq)]
pub struct Agent {
  pub agent: AgentName,
  pub ports: Vec<PortName>, // Auxiliary ports
}

/// One end of a connection, can be either agent or port
#[derive(Debug, Clone, PartialEq)]
pub enum Connector {
  Agent(Agent),
  Port(PortName),
}

/// E.g. A(a, b) ~ c
#[derive(new, Debug, Clone, PartialEq)]
pub struct Connection {
  pub lhs: Connector,
  pub rhs: Connector,
}

impl Connection {
  pub fn port_names_iter(&self) -> impl Iterator<Item = &PortName> {
    [&self.lhs, &self.rhs].into_iter().flat_map(|connector| match connector {
      Connector::Agent(Agent { agent: _, ports }) => ports,
      Connector::Port(port) => std::slice::from_ref(port),
    })
  }
}

// Rule types

/// E.g. A(a, b) ~ B(c, d)
#[derive(Debug, Clone, PartialEq)]
pub struct ActivePair {
  pub lhs: Agent,
  pub rhs: Agent,
}

/// A rule has a LHS and RHS, and the LHS of a rule is an active pair that has its own LHS and RHS
/// E.g. rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b
#[derive(Debug, Clone, PartialEq)]
pub struct Rule {
  pub lhs: ActivePair,
  pub rhs: Vec<Connection>,
  pub span: SimpleSpan, // Used for showing in error messages
}

/// AST of source file
#[derive(Debug, Clone, PartialEq)]
pub struct Ast {
  pub agents: Vec<Agent>,
  pub rules: Vec<Rule>,
  pub init: Vec<Connection>,
  pub init_span: SimpleSpan, // Used for showing in error messages
}

impl Ast {
  /// Validate AST and build rule book from it
  /// The `src` parameter is used for resolving spans for error messages
  pub fn build_rule_book(&self, src: &str) -> IvmResult<RuleBook> {
    /// Check that agent usage has correct number of ports matching its declaration
    fn check_agent_arity(
      errors: &mut IvmErrors,
      span: SimpleSpan,
      Agent { agent, ports }: &Agent,
      agent_arity: &HashMap<&PortName, usize>,
    ) {
      let port_count = agent_arity[agent];
      if ports.len() != port_count {
        errors.push(Rich::custom(
          span,
          format!("Agent `{}` has {} ports, but {} ports are linked to it", agent, port_count, ports.len()),
        ));
      }
    }

    /// Validate connections, either in a rule's RHS or in the initial net:
    /// Check linearity restriction (each port must be referenced exactly twice)
    /// Check that each agent usage has correct number of ports matching its declaration
    /// `rule_src` is used for error messages, pass `None` when validating `init` connections
    fn validate_connections(
      errors: &mut IvmErrors,
      span: SimpleSpan,
      rule_src: Option<&str>,
      connections: &[Connection],
      mut port_name_occurrences: HashMap<PortName, usize>,
      agent_arity: &HashMap<&PortName, usize>,
    ) {
      // Check agent arity and count port occurrences
      process_agents_and_ports(
        connections,
        |agent| check_agent_arity(errors, span, agent, &agent_arity),
        |port_name: &PortName| {
          let occurrences = port_name_occurrences.entry(port_name.to_owned()).or_insert(0);
          *occurrences += 1;
        },
      );

      // Check linearity restriction (each port must be referenced exactly twice)
      // Except for root port, which must be referenced exactly once, but only in `init` connections
      for (port_name, occurrences) in port_name_occurrences {
        if port_name == ROOT_PORT_NAME {
          match rule_src {
            None => {
              // Rule `init`
              if occurrences != 1 {
                errors.push(Rich::custom(span, format!(
                  "Port name `{ROOT_PORT_NAME}` occurs {occurrences} != 1 times in `{INIT_CONNECTIONS}` connections",
                )));
              }
            }
            Some(rule_src) => {
              errors.push(Rich::custom(span, format!(
                "Reserved port name `{ROOT_PORT_NAME}` not allowed in rule `{rule_src}`, only in `{INIT_CONNECTIONS}` connections",
              )));
            }
          }
        } else {
          if occurrences != 2 {
            let rule_src = rule_src.unwrap_or(INIT_CONNECTIONS);
            errors.push(Rich::custom(
              span,
              format!("Port name `{port_name}` occurs {occurrences} != 2 times in `{rule_src}`"),
            ));
          }
        }
      }
    }

    let mut errors = IvmErrors::new();

    // Build agent arity map and check for duplicate agent definitions
    let mut agent_arity = HashMap::new();
    for Agent { agent, ports } in &self.agents {
      if agent_arity.insert(agent, ports.len()).is_some() {
        return Err(eyre!("Duplicate definition of agent `{}`", agent));
      }
    }

    // Rule book uses agent IDs instead of names for faster lookup, so build map from names to IDs
    // Sort agents by name to ensure deterministic order of IDs for reproducible results
    // Agent IDs start from 1, 0 is reserved for the root node's agent_id
    let agent_name_to_id = agent_arity
      .keys()
      .sorted()
      .enumerate()
      .map(|(i, &agent)| (agent.to_owned(), 1 + i))
      .collect::<HashMap<AgentName, AgentId>>();

    // Validate rules and build rule book
    let mut rule_book = RuleBook::new(agent_name_to_id);
    for rule in &self.rules {
      /// Reject duplicate port names in agents of active pair
      /// E.g. A(a, a) ~ B is invalid, port names in active pair must be distinct
      /// Returns set of port names in agent
      fn validate_agent_port_references(
        errors: &mut IvmErrors,
        span: SimpleSpan,
        side: &str,
        agent: &Agent,
        rule_src: &str,
      ) -> HashSet<PortName> {
        let port_names = agent.ports.iter().cloned().collect::<HashSet<_>>();
        if port_names.len() < agent.ports.len() {
          let duplicate_port_names = agent.ports.iter().duplicates().join(", ");
          errors.push(Rich::custom(
            span ,format!(
            "Duplicate port names ({duplicate_port_names}) in agent `{}` in {side} of active pair in rule `{rule_src}`",
            agent.agent,
          )));
        }
        port_names
      }

      let Rule { lhs: active_pair, rhs: rule_rhs, span } = rule;
      let rule_src = &src[span.into_range()];
      let span = *span;

      // Validate LHS
      let ActivePair { lhs, rhs } = active_pair;
      check_agent_arity(&mut errors, span, lhs, &agent_arity);
      check_agent_arity(&mut errors, span, rhs, &agent_arity);

      // Ensure that sets of port names in LHS and RHS of active pair are disjoint
      let port_names_in_lhs = validate_agent_port_references(&mut errors, span, "LHS", &lhs, rule_src);
      let port_names_in_rhs = validate_agent_port_references(&mut errors, span, "RHS", &rhs, rule_src);

      // Reject duplicate port names in active pair
      // E.g. A(c) ~ B(c) is invalid, port names in active pair must be distinct
      if !port_names_in_lhs.is_disjoint(&port_names_in_rhs) {
        let intersection = port_names_in_lhs.intersection(&port_names_in_rhs).join(", ");
        errors.push(Rich::custom(
          span,
          format!(
          "Cannot use the same port names ({intersection}) on both sides of active pair in LHS of rule `{rule_src}`",
        )));
      }

      // Port names in active pair are external links in a rule's RHS net
      // E.g. if we have: rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b
      // then {ret, a, b} are external links in the RHS net `ret ~ Succ(cnt), Add(cnt, a) ~ b`
      let port_names_in_active_pair = port_names_in_lhs.into_iter().chain(port_names_in_rhs);
      // Each external port occurs once in the active pair, so pre-populate the map with 1
      let port_name_occurrences = port_names_in_active_pair.map(|port| (port, 1)).collect::<HashMap<_, _>>();

      // Validate RHS
      validate_connections(&mut errors, span, Some(rule_src), rule_rhs, port_name_occurrences, &agent_arity);

      // Rule is valid
      rule_book.add_rule(rule, rule_src, &mut errors);
    }

    // We validated the connections of all rules' RHS, now we validate the `init` connections
    validate_connections(&mut errors, self.init_span, None, &self.init, HashMap::new(), &agent_arity);

    construct_result(src, Some(rule_book), errors)
  }

  // AST needs to be validated
  // `agent_name_to_id` must come from the `RuleBook` returned by `build_rule_book`
  pub fn to_inet(&self, agent_name_to_id: &HashMap<AgentName, AgentId>) -> INet {
    let mut net = INet::default();

    // Create root node with one port
    let root_node_idx = net.new_node(ROOT_AGENT_ID, 1);
    debug_assert_eq!(root_node_idx, ROOT_NODE_IDX);
    net[root_node_idx].agent_name = ROOT_PORT_NAME.to_string();
    let root_port = port(root_node_idx, 0);

    // The root node is the only external link ("free variable") in the `init` connections
    let mut external_links = HashMap::<PortNameRef, NodePort>::new();
    external_links.insert(ROOT_PORT_NAME, root_port);

    net.add_connections(&self.init, external_links, agent_name_to_id);
    net
  }
}

/// Iterate over connections and process agents and ports with the given functions
pub fn process_agents_and_ports(
  connections: &[Connection],
  mut process_agent: impl FnMut(&Agent),
  mut process_port: impl FnMut(&PortName),
) {
  let mut process_connector = |connector: &Connector| match connector {
    Connector::Agent(agent) => {
      process_agent(agent);
      for port in &agent.ports {
        process_port(port);
      }
    }
    Connector::Port(port) => process_port(port),
  };

  for Connection { lhs, rhs } in connections {
    process_connector(lhs);
    process_connector(rhs);
  }
}
