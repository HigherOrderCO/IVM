use crate::{
  error::{pass_output_and_errors_to_result, IvmResult, ProgramErrors},
  inet::{port, INet, NodeIdx},
  inet_program::INetProgram,
  rule_book::{AgentId, RuleBook, INET_MAX_PRE_REDUCTION_STEPS, ROOT_AGENT_ID},
};
use chumsky::{prelude::Rich, span::SimpleSpan};
use derive_new::new;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;

/// The first node in a net is the root node
pub const ROOT_NODE_IDX: NodeIdx = 0;

/// Port name of the root node in `init` connections
pub const ROOT_PORT_NAME: &str = "root";

/// Matches `Token::KeywordInit`
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

/// Wrapper for a value with a span
#[derive(new, Debug, Clone, PartialEq)]
pub struct Spanned<T> {
  pub span: SimpleSpan, // Used for showing in error messages
  pub val: T,
}

/// AST of source file
#[derive(Debug, Clone, PartialEq)]
pub struct Ast {
  pub agents: Vec<Spanned<Agent>>,
  pub rules: Vec<Rule>,
  pub init: Spanned<Vec<Connection>>,
}

impl Ast {
  /// Validate AST and build rule book from it
  /// The `src` parameter is used for resolving spans for error messages
  pub fn validate(self, src: &str) -> IvmResult<ValidatedAst> {
    /// Validate agent usage, returns false if agent is undeclared
    fn validate_agent_usage(
      errors: &mut ProgramErrors,
      span: SimpleSpan,
      Agent { agent, ports }: &Agent,
      agent_arity: &HashMap<&AgentName, usize>,
      agent_usages: &mut HashMap<&AgentName, usize>,
    ) -> bool {
      // Increase usage count for agent so that we can warn about unused agents
      if let Some(usage_count) = agent_usages.get_mut(agent) {
        *usage_count += 1;
      } else {
        errors.push(Rich::custom(span, format!("Agent `{}` is used, but not declared", agent)));
        return false;
      }

      // Check that agent usage has correct number of ports matching its declaration
      let port_count = agent_arity[agent];
      if ports.len() != port_count {
        errors.push(Rich::custom(
          span,
          format!("Agent `{}` has {} ports, but {} ports are linked to it", agent, port_count, ports.len()),
        ));
      }
      true
    }

    /// Validate connections, either in a rule's RHS or in the initial net:
    /// Check linearity restriction (each port must be referenced exactly twice)
    /// Check that each agent usage has correct number of ports matching its declaration
    /// `rule_src` is used for error messages, pass `None` when validating `init` connections
    /// Returns false if the connections reference non-existing agents
    fn validate_connections(
      errors: &mut ProgramErrors,
      span: SimpleSpan,
      rule_connections: bool,
      connections: &[Connection],
      mut port_name_occurrences: HashMap<PortName, usize>,
      agent_arity: &HashMap<&AgentName, usize>,
      agent_usages: &mut HashMap<&AgentName, usize>,
    ) -> bool {
      let mut all_referenced_agents_exist = true;
      // Check agent arity and count port occurrences
      process_agents_and_ports(
        connections,
        |agent| {
          all_referenced_agents_exist &= validate_agent_usage(errors, span, agent, agent_arity, agent_usages);
        },
        |port_name: &PortName| {
          let occurrences = port_name_occurrences.entry(port_name.to_owned()).or_insert(0);
          *occurrences += 1;
        },
      );

      // Check linearity restriction (each port must be referenced exactly twice)
      // Except for root port, which must be referenced exactly once, but only in `init` connections
      for (port_name, occurrences) in port_name_occurrences {
        if port_name == ROOT_PORT_NAME {
          if rule_connections {
            errors.push(Rich::custom(span, format!(
              "Reserved port name `{ROOT_PORT_NAME}` not allowed in rule, only in `{INIT_CONNECTIONS}` connections",
            )));
          } else {
            // `init` connections
            if occurrences != 1 {
              errors.push(Rich::custom(span, format!(
                  "Port name `{ROOT_PORT_NAME}` occurs {occurrences} != 1 times in `{INIT_CONNECTIONS}` connections",
                )));
            }
          }
        } else {
          if occurrences != 2 {
            errors
              .push(Rich::custom(span, format!("Port name `{port_name}` occurs {occurrences} != 2 times",)));
          }
        }
      }

      all_referenced_agents_exist
    }

    let mut errors = ProgramErrors::new();

    // Build agent arity map and check for duplicate agent definitions
    let mut agent_arity = HashMap::new();
    for Spanned { span, val: Agent { agent, ports } } in &self.agents {
      if agent_arity.insert(agent, ports.len()).is_some() {
        errors.push(Rich::custom(*span, format!("Duplicate definition of agent `{}`", agent)));
      }
    }

    // Count references to declared agents so we can show warnings for unused agents
    let mut agent_usages = agent_arity.iter().map(|(&agent, _)| (agent, 0)).collect::<HashMap<_, _>>();
    // Count agent usages in rule active pairs separately
    let mut agent_usages_in_rule_active_pairs = agent_usages.clone();

    // Rule book uses agent IDs instead of names for faster lookup, so build map from names to IDs
    // Sort agents by name to ensure deterministic order of IDs for reproducible results
    // Agent IDs start from 1, 0 is reserved for the root node's agent_id
    let agent_name_to_id = agent_arity
      .keys()
      .sorted()
      .enumerate()
      .map(|(i, &agent)| (agent.to_owned(), (1 + i) as AgentId))
      .collect::<HashMap<AgentName, AgentId>>();

    // Validate rules and build rule book
    let mut rule_book = RuleBook::new(agent_name_to_id.len());
    for rule in &self.rules {
      /// Reject duplicate port names in agents of active pair
      /// E.g. A(a, a) ~ B is invalid, port names in active pair must be distinct
      /// Returns set of port names in agent
      fn validate_agent_port_references(
        errors: &mut ProgramErrors,
        span: SimpleSpan,
        side: &str,
        agent: &Agent,
      ) -> HashSet<PortName> {
        let port_names = agent.ports.iter().cloned().collect::<HashSet<_>>();
        if port_names.len() < agent.ports.len() {
          let duplicate_port_names = agent.ports.iter().duplicates().join(", ");
          errors.push(Rich::custom(
            span,
            format!(
              "Duplicate port names ({duplicate_port_names}) in agent `{}` in {side} of active pair in rule",
              agent.agent,
            ),
          ));
        }
        port_names
      }

      let Rule { lhs: active_pair, rhs: rule_rhs, span } = rule;
      let rule_src = &src[span.into_range()];
      let span = *span;

      // Validate LHS
      let ActivePair { lhs, rhs } = active_pair;
      let mut all_agents_referenced_in_rule_exist =
        validate_agent_usage(&mut errors, span, lhs, &agent_arity, &mut agent_usages_in_rule_active_pairs)
          && validate_agent_usage(
            &mut errors,
            span,
            rhs,
            &agent_arity,
            &mut agent_usages_in_rule_active_pairs,
          );

      // Ensure that sets of port names in LHS and RHS of active pair are disjoint
      let port_names_in_lhs = validate_agent_port_references(&mut errors, span, "LHS", lhs);
      let port_names_in_rhs = validate_agent_port_references(&mut errors, span, "RHS", rhs);

      // Reject duplicate port names in active pair
      // E.g. A(c) ~ B(c) is invalid, port names in active pair must be distinct
      if !port_names_in_lhs.is_disjoint(&port_names_in_rhs) {
        let intersection = port_names_in_lhs.intersection(&port_names_in_rhs).join(", ");
        errors.push(Rich::custom(
          span,
          format!(
            "Cannot use the same port names ({intersection}) on both sides of active pair in LHS of rule",
          ),
        ));
      }

      // Port names in active pair are external links in a rule's RHS net
      // E.g. if we have: rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b
      // then {ret, a, b} are external links in the RHS net `ret ~ Succ(cnt), Add(cnt, a) ~ b`
      let port_names_in_active_pair = port_names_in_lhs.into_iter().chain(port_names_in_rhs);
      // Each external port occurs once in the active pair, so pre-populate the map with 1
      let port_name_occurrences = port_names_in_active_pair.map(|port| (port, 1)).collect::<HashMap<_, _>>();

      // Validate RHS
      all_agents_referenced_in_rule_exist &= validate_connections(
        &mut errors,
        span,
        true,
        rule_rhs,
        port_name_occurrences,
        &agent_arity,
        &mut agent_usages,
      );

      // Add rule to rule book
      if all_agents_referenced_in_rule_exist {
        rule_book.insert_rule(rule, rule_src, &agent_name_to_id, &mut errors);
      }
    }
    let agent_id_to_name = agent_name_to_id.iter().map(|(name, id)| (*id, name.clone())).collect();

    // We validated the connections of all rules' RHS, now we validate the `init` connections
    validate_connections(
      &mut errors,
      self.init.span,
      false,
      &self.init.val,
      HashMap::new(),
      &agent_arity,
      &mut agent_usages,
    );

    // Check for unused agents
    for (agent_name, usage_count) in agent_usages {
      if usage_count == 0 {
        let span = self
          .agents
          .iter()
          .find_map(|Spanned { span, val: Agent { agent, ports: _ } }| (agent == agent_name).then_some(*span))
          .unwrap();
        errors.push(Rich::custom(span, format!("Unused agent `{agent_name}`")));
      }
    }

    // Drop these so that self can be moved
    drop(agent_arity);
    drop(agent_usages_in_rule_active_pairs);

    pass_output_and_errors_to_result(
      src,
      Some(ValidatedAst { ast: self, rule_book, agent_name_to_id, agent_id_to_name }),
      errors,
    )
  }
}

/// A validated AST and its corresponding `RuleBook`
pub struct ValidatedAst {
  pub ast: Ast,
  pub rule_book: RuleBook,
  pub agent_name_to_id: HashMap<AgentName, AgentId>,
  pub agent_id_to_name: HashMap<AgentId, AgentName>,
}

impl ValidatedAst {
  /// Generate an `INetProgram` from a `ValidatedAst`
  pub fn into_inet_program(self, pre_preduce: bool) -> INetProgram {
    let Self { ast, mut rule_book, agent_name_to_id, agent_id_to_name } = self;

    let mut net = INet::default();

    // Create root node with one port which points to itself (by default)
    let root_node_idx = net.new_node(ROOT_AGENT_ID, 1);
    debug_assert_eq!(root_node_idx, ROOT_NODE_IDX);
    let root_port = port(root_node_idx, 0);

    // The root node is the only external port ("free variable") in the `init` connections
    let external_ports = vec![[Err(ROOT_PORT_NAME), Ok(root_port)]];

    net.add_connections(&ast.init.val, external_ports, &agent_name_to_id);

    if cfg!(debug_assertions) {
      net.validate(false);
    }

    rule_book.finalize(&agent_id_to_name, pre_preduce);

    if pre_preduce {
      let mut reduced_net = net.clone();
      if let Some(reduction_count) =
        reduced_net.reduce_in_max_steps::<INET_MAX_PRE_REDUCTION_STEPS>(&rule_book)
      {
        if reduction_count > 0 {
          // There were active pairs that were reduced
          reduced_net.remove_unused_nodes();
          if cfg!(debug_assertions) {
            reduced_net.validate(false);
          }
          net = reduced_net;
        }
      }
    }

    INetProgram::new(ast, net, rule_book, agent_id_to_name)
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
