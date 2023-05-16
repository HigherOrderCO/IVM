use crate::{
  inet::{port, INet, NodeIdx, NodePort},
  rule_book::{AgentId, RuleBook, ROOT_AGENT_ID},
  Error,
};
use derive_new::new;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;

pub const ROOT_NODE_IDX: NodeIdx = 0;
pub const ROOT_PORT_NAME: &str = "root";
pub const INIT_CONNECTIONS: &str = "init";

pub type AgentName = String; // Starts with uppercase letter
pub type PortName = String; // Starts with lowercase letter
pub type PortNameRef<'a> = &'a str;

// The syntax allows writing nested agents for convenience, e.g. A(a, B(b, c))
// This gets flattened during parsing into A(a, _0), _0 ~ B(b, c)

// Nested types

// E.g. A(a, B(b, c))
#[derive(Debug, Clone, PartialEq)]
pub struct NestedAgent {
  pub agent: AgentName,
  pub ports: Vec<NestedConnector>, // Auxiliary ports
}

#[derive(Debug, Clone, PartialEq)]
pub enum NestedConnector {
  Agent(NestedAgent),
  Port(PortName),
}

// E.g. A(a, B(b, c)) ~ C(D(d, e), f)
#[derive(new, Debug, Clone, PartialEq)]
pub struct NestedConnection {
  pub lhs: NestedConnector,
  pub rhs: NestedConnector,
}

// Flat types

#[derive(Debug, Clone, PartialEq)]
pub struct Agent {
  pub agent: AgentName,
  pub ports: Vec<PortName>, // Auxiliary ports
}

#[derive(Debug, Clone, PartialEq)]
pub enum Connector {
  Agent(Agent),
  Port(PortName),
}

#[derive(new, Debug, Clone, PartialEq)]
pub struct Connection {
  pub lhs: Connector,
  pub rhs: Connector,
}

impl Connection {
  pub fn port_names(&self) -> impl Iterator<Item = &PortName> {
    [&self.lhs, &self.rhs].into_iter().flat_map(|connector| match connector {
      Connector::Agent(Agent { agent: _, ports }) => ports,
      Connector::Port(port) => std::slice::from_ref(port),
    })
  }
}

// Rule types

// E.g. A(a, b) ~ B(c, d)
#[derive(Debug, Clone, PartialEq)]
pub struct ActivePair {
  pub lhs: Agent,
  pub rhs: Agent,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Rule {
  pub lhs: ActivePair,
  pub rhs: Vec<Connection>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ast {
  pub(crate) agents: Vec<Agent>,
  pub(crate) rules: Vec<Rule>,
  pub(crate) init: Vec<Connection>,
}

impl Ast {
  pub fn build_rulebook(&self) -> Result<RuleBook, Error> {
    let mut agent_arity = HashMap::new();

    for Agent { agent, ports } in &self.agents {
      if agent_arity.insert(agent, ports.len()).is_some() {
        return Err(format!("Duplicate definition of agent `{}`", agent));
      }
    }

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

    fn validate_connections(
      rule: Option<&dyn Fn() -> String>,
      connections: &[Connection],
      mut port_name_occurrences: HashMap<PortName, usize>,
      agent_arity: &HashMap<&PortName, usize>,
    ) -> Result<(), Error> {
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

    // Validate rules and build rule book
    let agent_name_to_id = agent_arity
			.keys()
			.sorted()
			.enumerate()
			.map(|(i, &agent)| (agent.to_owned(), 1 + i)) // +1 because 0 is reserved for the root agent
			.collect::<HashMap<AgentName, AgentId>>();
    let mut rule_book = RuleBook::new(agent_name_to_id);
    for rule in &self.rules {
      fn validate_agent_port_references(
        side: &str,
        agent: &Agent,
        rule: &Rule,
      ) -> Result<HashSet<PortName>, Error> {
        let port_names = agent.ports.iter().cloned().collect::<HashSet<_>>();
        if port_names.len() < agent.ports.len() {
          return Err(format!(
            "Duplicate port names in agent `{}` in {} of active pair in rule `{}`",
            agent.agent, side, rule
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
      if !port_names_in_lhs.is_disjoint(&port_names_in_rhs) {
        let intersection = port_names_in_lhs.intersection(&port_names_in_rhs).collect_vec();
        return Err(format!(
          "Cannot use the same port names ({:?}) on both sides of active pair in LHS of rule `{}`",
          intersection, rule
        ));
      }

      // Port names in active pair are external links in a rule's RHS net
      let port_name_occurrences = port_names_in_lhs
        .into_iter()
        .chain(port_names_in_rhs)
        .map(|port| (port, 1))
        .collect::<HashMap<_, _>>();

      // Validate RHS
      validate_connections(Some(&|| rule.to_string()), rule_rhs, port_name_occurrences, &agent_arity)?;

      rule_book.add_rule(rule)?;
    }

    validate_connections(None, &self.init, HashMap::new(), &agent_arity)?;

    Ok(rule_book)
  }

  // AST needs to be validated
  pub fn to_inet(&self, agent_name_to_id: &HashMap<AgentName, AgentId>) -> INet {
    let mut net = INet::default();
    let agent_id = ROOT_AGENT_ID;
    let root_node_idx = net.new_node(agent_id, 1);
    debug_assert_eq!(root_node_idx, ROOT_NODE_IDX);
    net[root_node_idx].agent_name = ROOT_PORT_NAME.to_string();
    let root_port = port(root_node_idx, 0);

    let mut external_links = HashMap::<PortNameRef, NodePort>::new();
    external_links.insert(ROOT_PORT_NAME, root_port);
    net.add_connections(&self.init, external_links, agent_name_to_id);
    net
  }
}

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
