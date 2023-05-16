use crate::parser::ast::*;
use itertools::Itertools;

// The syntax allows writing nested agents for convenience, this gets flattened during parsing.
// E.g. A(a, B(b, c)) => A(a, _0), _0 ~ B(b, c)
// E.g. A(a, B(C(b, c), D(d, e))) => A(a, _0), _0 ~ B(_1, _2), _1 ~ C(b, c), _2 ~ D(d, e)

impl NestedAgent {
  pub(super) fn flatten(self, next_port_idx: &mut usize) -> (Agent, Vec<Connection>) {
    let Self { agent, ports } = self;
    let mut connections = vec![];
    (
      Agent {
        agent,
        ports: ports
          .into_iter()
          .map(|nested_connector| match nested_connector {
            NestedConnector::Agent(agent) => {
              let new_port_name = format!("_{}", next_port_idx);
              *next_port_idx += 1;

              let port = Connector::Port(new_port_name.clone());

              let (flattened_agent, nested_connections) = agent.flatten(next_port_idx);
              connections.push(Connection::new(port, Connector::Agent(flattened_agent)));
              connections.extend(nested_connections);

              new_port_name
            }
            NestedConnector::Port(port) => port,
          })
          .collect(),
      },
      connections,
    )
  }
}

impl NestedConnector {
  pub(super) fn flatten(self, next_port_idx: &mut usize) -> (Connector, Vec<Connection>) {
    let mut connections = vec![];
    match self {
      NestedConnector::Agent(agent) => {
        let (flattened_agent, nested_connections) = agent.flatten(next_port_idx);
        connections.extend(nested_connections);
        (Connector::Agent(flattened_agent), connections)
      }
      NestedConnector::Port(port) => (Connector::Port(port), connections),
    }
  }
}

impl NestedConnection {
  pub(super) fn flatten(self, next_port_idx: &mut usize) -> Vec<Connection> {
    let (lhs, lhs_connections) = self.lhs.flatten(next_port_idx);
    let (rhs, rhs_connections) = self.rhs.flatten(next_port_idx);
    let mut connections = vec![];
    connections.push(Connection::new(lhs, rhs));
    connections.extend(lhs_connections);
    connections.extend(rhs_connections);
    connections
  }
}

pub(super) fn flatten_connections(connections: Vec<NestedConnection>) -> Vec<Connection> {
  let mut next_port_idx = 0;
  connections.into_iter().flat_map(|connection| connection.flatten(&mut next_port_idx)).collect()
}

// Unflatten connections, used for reading back computed nets into readable textual form
// E.g. root ~ Succ(_0), Succ(_1) ~ _2, _1 ~ Zero, Succ(_3) ~ _0, _3 ~ Succ(_2) => root ~ Succ(Succ(Succ(Succ(Zero))))
// E.g. root ~ Lam(_0, _1), _0 ~ _1 => root ~ Lam(_0, _0)
pub fn unflatten_connections(connections: Vec<Connection>) -> Vec<NestedConnection> {
  let mut connections = connections
    .into_iter()
    .map(|connection| {
      let Connection { lhs, rhs } = connection;
      let unflatten_connector = |connector| match connector {
        Connector::Agent(Agent { agent, ports }) => NestedConnector::Agent(NestedAgent {
          agent,
          ports: ports.into_iter().map(|port| NestedConnector::Port(port)).collect(),
        }),
        Connector::Port(port) => NestedConnector::Port(port),
      };
      let lhs = unflatten_connector(lhs);
      let rhs = unflatten_connector(rhs);
      NestedConnection { lhs, rhs }
    })
    .collect_vec();

  // Inline nestable agents
  // root ~ Succ(_0), Succ(_1) ~ _2, _1 ~ Zero, Succ(_3) ~ _0, _3 ~ Succ(_2)
  // => root ~ Succ(Succ(Succ(Succ(Zero))))

  // Inline one candidate per iteration
  while {
    let mut made_progress = false;

    // Find link candidates that can be inlined: X ~ A(wire), wire ~ B(..)
    let inline_candidates = connections
      .iter()
      .enumerate()
      .filter_map(|(i, NestedConnection { lhs, rhs })| match (lhs, rhs) {
        (NestedConnector::Agent(agent), NestedConnector::Port(port))
        | (NestedConnector::Port(port), NestedConnector::Agent(agent)) => {
          Some((i, agent.clone(), port.clone()))
        }
        _ => None,
      })
      .collect_vec();

    // Inline link candidates, remove in reverse order to avoid index invalidation
    for (i, candidate, wire) in inline_candidates.into_iter().rev() {
      // NOTE: Could cause stack overflow due to recursion
      fn inline_agent(agent: &mut NestedAgent, candidate: &NestedAgent, wire: &PortName) -> bool {
        let NestedAgent { agent: _, ports } = agent;
        for connector in ports {
          match connector {
            NestedConnector::Agent(agent) => {
              if inline_agent(agent, candidate, wire) {
                return true;
              }
            }
            NestedConnector::Port(port) => {
              if port == wire {
                *connector = NestedConnector::Agent(candidate.clone());
                return true;
              }
            }
          }
        }
        false
      }

      let mut inlined = false;
      for NestedConnection { lhs, rhs } in &mut connections {
        for connector in [lhs, rhs] {
          match connector {
            NestedConnector::Agent(agent) => {
              if inline_agent(agent, &candidate, &wire) {
                inlined = true;
                break;
              }
            }
            NestedConnector::Port(_port) => {}
          }
        }
      }
      if inlined {
        connections.remove(i);
        made_progress = true;
        break;
      }
    }
    made_progress
  } {}

  // Merge wire names
  // root ~ Lam(_0, _1), _0 ~ _1 => root ~ Lam(_0, _0)

  let merge_candidates = connections
    .iter()
    .enumerate()
    .filter_map(|(i, NestedConnection { lhs, rhs })| match (lhs, rhs) {
      (NestedConnector::Port(a), NestedConnector::Port(b)) => {
        let (a, b) = (a.min(b), a.max(b));
        (b != ROOT_PORT_NAME).then(|| (i, a.clone(), b.clone()))
      }
      _ => None,
    })
    .collect_vec();

  // Inline link candidates, remove in reverse order to avoid index invalidation
  for (i, wire_to_use, wire_to_replace) in merge_candidates.into_iter().rev() {
    // NOTE: Could cause stack overflow due to recursion
    fn replace_port(
      connector: &mut NestedConnector,
      wire_to_use: &PortName,
      wire_to_replace: &PortName,
    ) -> bool {
      match connector {
        NestedConnector::Agent(NestedAgent { agent: _, ports }) => {
          for connector in ports {
            if replace_port(connector, wire_to_use, wire_to_replace) {
              return true;
            }
          }
        }
        NestedConnector::Port(port) => {
          if port == wire_to_replace {
            *port = wire_to_use.clone();
            return true;
          }
        }
      }
      false
    }

    let mut replaced = false;
    for NestedConnection { lhs, rhs } in &mut connections {
      for connector in [lhs, rhs] {
        if replace_port(connector, &wire_to_use, &wire_to_replace) {
          replaced = true;
          break;
        }
      }
    }
    if replaced {
      connections.remove(i);
    }
  }

  connections
}
