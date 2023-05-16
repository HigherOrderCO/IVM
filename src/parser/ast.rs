use crate::{
  inet::{port, INet, NodeIdx, NodePort},
  rule_book::{AgentId, RuleBook, ROOT_AGENT_ID},
  Error,
};
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
}

/// AST of source file
#[derive(Debug, Clone, PartialEq)]
pub struct Ast {
  pub(crate) agents: Vec<Agent>,
  pub(crate) rules: Vec<Rule>,
  pub(crate) init: Vec<Connection>,
}

impl Ast {
  /// Validate AST and build rule book from it
  pub fn build_rule_book(&self) -> Result<RuleBook, Error> {
    /// Check that agent usage has correct number of ports matching its declaration
    fn check_agent_arity(
      Agent { agent, ports }: &Agent,
      agent_arity: &HashMap<&PortName, usize>,
    ) -> Result<(), Error> {
      let port_count = agent_arity[agent];
      if ports.len() != port_count {
        return Err(format!(
          "Agent `{}` has {} ports, but {} ports are linked to it",
          agent,
          port_count,
          ports.len()
        ));
      }
      Ok(())
    }

    /// Validate connections, either in a rule's RHS or in the initial net:
    /// Check linearity restriction (each port must be referenced exactly twice)
    /// Check that each agent usage has correct number of ports matching its declaration
    fn validate_connections(
      rule: Option<&dyn Fn() -> String>,
      connections: &[Connection],
      mut port_name_occurrences: HashMap<PortName, usize>,
      agent_arity: &HashMap<&PortName, usize>,
    ) -> Result<(), Error> {
      // Check agent arity and count port occurrences
      process_agents_and_ports(
        connections,
        |agent| check_agent_arity(agent, &agent_arity),
        |port_name: &PortName| {
          let occurrences = port_name_occurrences.entry(port_name.to_owned()).or_insert(0);
          *occurrences += 1;
          Ok(())
        },
      )?;

      // Check linearity restriction (each port must be referenced exactly twice)
      // Except for root port, which must be referenced exactly once, but only in `init` connections
      for (port_name, occurrences) in port_name_occurrences {
        if port_name == ROOT_PORT_NAME {
          match rule {
            None => {
              // Rule `init`
              if occurrences != 1 {
                return Err(format!(
                  "Port name `{ROOT_PORT_NAME}` occurs {} != 1 times in `{INIT_CONNECTIONS}` connections",
                  occurrences
                ));
              }
            }
            Some(rule) => {
              return Err(format!(
                "Reserved port name `{ROOT_PORT_NAME}` not allowed in rule `{}`, only in `{INIT_CONNECTIONS}` connections",
                rule()
              ));
            }
          }
        } else {
          if occurrences != 2 {
            let rule = match rule {
              None => INIT_CONNECTIONS.to_string(),
              Some(rule) => rule(),
            };
            return Err(format!("Port name `{}` occurs {} != 2 times in `{}`", port_name, occurrences, rule));
          }
        }
      }
      Ok(())
    }

    // Build agent arity map and check for duplicate agent definitions
    let mut agent_arity = HashMap::new();
    for Agent { agent, ports } in &self.agents {
      if agent_arity.insert(agent, ports.len()).is_some() {
        return Err(format!("Duplicate definition of agent `{}`", agent));
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
        side: &str,
        agent: &Agent,
        rule: &Rule,
      ) -> Result<HashSet<PortName>, Error> {
        let port_names = agent.ports.iter().cloned().collect::<HashSet<_>>();
        if port_names.len() < agent.ports.len() {
          let duplicate_port_names = agent.ports.iter().duplicates().collect_vec();
          return Err(format!(
            "Duplicate port names {duplicate_port_names:?} in agent `{}` in {side} of active pair in rule `{rule}`",
            agent.agent,
          ));
        }
        Ok(port_names)
      }

      let Rule { lhs: active_pair, rhs: rule_rhs } = rule;

      // Validate LHS
      let ActivePair { lhs, rhs } = active_pair;
      check_agent_arity(lhs, &agent_arity)?;
      check_agent_arity(rhs, &agent_arity)?;

      // Ensure that sets of port names in LHS and RHS of active pair are disjoint
      let port_names_in_lhs = validate_agent_port_references("LHS", &lhs, &rule)?;
      let port_names_in_rhs = validate_agent_port_references("RHS", &rhs, &rule)?;

      // Reject duplicate port names in active pair
      // E.g. A(c) ~ B(c) is invalid, port names in active pair must be distinct
      if !port_names_in_lhs.is_disjoint(&port_names_in_rhs) {
        let intersection = port_names_in_lhs.intersection(&port_names_in_rhs).collect_vec();
        return Err(format!(
          "Cannot use the same port names ({:?}) on both sides of active pair in LHS of rule `{}`",
          intersection, rule
        ));
      }

      // Port names in active pair are external links in a rule's RHS net
      // E.g. if we have: rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b
      // then {ret, a, b} are external links in the RHS net `ret ~ Succ(cnt), Add(cnt, a) ~ b`
      let port_names_in_active_pair = port_names_in_lhs.into_iter().chain(port_names_in_rhs);
      // Each external port occurs once in the active pair, so pre-populate the map with 1
      let port_name_occurrences = port_names_in_active_pair.map(|port| (port, 1)).collect::<HashMap<_, _>>();

      // Validate RHS
      validate_connections(Some(&|| rule.to_string()), rule_rhs, port_name_occurrences, &agent_arity)?;

      // Rule is valid
      rule_book.add_rule(rule)?;
    }

    // We validated the connections of all rules' RHS, now we validate the `init` connections
    validate_connections(None, &self.init, HashMap::new(), &agent_arity)?;

    Ok(rule_book)
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
  mut process_agent: impl FnMut(&Agent) -> Result<(), Error>,
  mut process_port: impl FnMut(&PortName) -> Result<(), Error>,
) -> Result<(), Error> {
  let mut process_connector = |connector: &Connector| -> Result<(), Error> {
    match connector {
      Connector::Agent(agent) => {
        process_agent(agent)?;
        for port in &agent.ports {
          process_port(port)?;
        }
      }
      Connector::Port(port) => process_port(port)?,
    }
    Ok(())
  };

  for Connection { lhs, rhs } in connections {
    process_connector(lhs)?;
    process_connector(rhs)?;
  }
  Ok(())
}
