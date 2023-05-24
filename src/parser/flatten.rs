use crate::{inet::EXTERNAL_PORT_PREFIX, parser::ast::*, util::sort_tuple};
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
      fn unflatten_connector(connector: Connector) -> NestedConnector {
        match connector {
          Connector::Agent(Agent { agent, ports }) => NestedConnector::Agent(NestedAgent {
            agent,
            ports: ports.into_iter().map(|port| NestedConnector::Port(port)).collect(),
          }),
          Connector::Port(port) => NestedConnector::Port(port),
        }
      }

      let Connection { lhs, rhs } = connection;
      let lhs = unflatten_connector(lhs);
      let rhs = unflatten_connector(rhs);
      NestedConnection { lhs, rhs }
    })
    .collect_vec();

  // Inline nestable agents
  // E.g. `root ~ Succ(_0), Succ(_1) ~ _2, _1 ~ Zero, Succ(_3) ~ _0, _3 ~ Succ(_2)`
  // becomes `root ~ Succ(Succ(Succ(Succ(Zero))))`

  // Inline one candidate per iteration
  while {
    // Find link candidates that can be inlined:
    // All port-to-agent connections like `wire ~ B(..)` are candidates, but they
    // can only be inlined if `wire` is connected to an aux port, e.g. `X ~ A(wire)`
    let mut inline_candidates = connections
      .iter()
      .enumerate()
      .filter_map(|(i, NestedConnection { lhs, rhs })| match (lhs, rhs) {
        (NestedConnector::Agent(agent), NestedConnector::Port(port)) => {
          Some((i, 0, agent.clone(), port.clone()))
        }
        (NestedConnector::Port(port), NestedConnector::Agent(agent)) => {
          Some((i, 1, agent.clone(), port.clone()))
        }
        _ => None,
      })
      .collect_vec();

    let mut made_progress = false; // Whether any candidate was inlined

    // Try to inline candidates, iterate reversed to avoid index invalidation when removing from `connections`
    while let Some((connection_idx, connector_idx, candidate, wire)) = inline_candidates.pop() {
      // If `agent` contains `wire`, replace `wire` with `candidate` and return true, which
      // means that the connection corresponding to this candidate can be removed from `connections`.
      // Otherwise, return false.
      fn inline_agent(agent: &mut NestedAgent, candidate: &NestedAgent, wire: &PortName) -> bool {
        let NestedAgent { agent: _, ports } = agent;
        for connector in ports {
          match connector {
            NestedConnector::Agent(agent) => {
              // Visit nested agents recursively
              if inline_agent(agent, candidate, wire) {
                return true;
              }
            }
            NestedConnector::Port(port) => {
              // Eliminate `wire` by inlining `candidate`
              if port == wire {
                *connector = NestedConnector::Agent(candidate.clone());
                return true;
              }
            }
          }
        }
        false
      }

      // Iterate over all connectors and replace `wire` with `candidate`
      let mut inlined = false;
      for (i, NestedConnection { lhs, rhs }) in connections.iter_mut().enumerate() {
        for (j, connector) in [lhs, rhs].into_iter().enumerate() {
          if i == connection_idx && j == connector_idx {
            // If an agent's principal port is connected to one of its auxilliary ports,
            // it would be inlined into itself, which is not allowed!
            // E.g. A(_0, _1) ~ _1
            continue;
          }
          match connector {
            NestedConnector::Agent(agent) => {
              if inline_agent(agent, &candidate, &wire) {
                inlined = true;

                // There is exactly one connector that contains `wire`, e.g. `X ~ A(wire)`
                // apart from the candidate connection itself (e.g. `wire ~ B(..)`), which is removed below.
                break;
              }
            }
            NestedConnector::Port(_port) => {}
          }
        }
      }
      if inlined {
        // If an `Agent` connector (e.g. `B(..)`) was inlined into another
        // (e.g. into `A(..)`, resulting in `X ~ A(B(..))`),
        // then remove the `wire ~ B(..)` connection.
        connections.remove(connection_idx);

        // Keep iterating as long as we make progress
        made_progress = true;

        // By inlining one candidate, other candidates may become invalidated.
        // Break here, so that we recompute `inline_candidates` in the next iteration.
        break;
      }
    }
    made_progress
  } {}

  // Now merge wire names
  // E.g. `root ~ Lam(_0, _1), _0 ~ _1` becomes `root ~ Lam(_0, _0)`

  // All port-to-port connections that don't involve `root` are merge candidates
  let mut merge_candidates = connections
    .iter()
    .enumerate()
    .filter_map(|(i, NestedConnection { lhs, rhs })| match (lhs, rhs) {
      (NestedConnector::Port(a), NestedConnector::Port(b)) => {
        // Sort, so that `wire_to_use` is always the lower one,
        // e.g. `root ~ Lam(_0, _1), _0 ~ _1` becomes `root ~ Lam(_0, _0)`, not `root ~ Lam(_1, _1)`
        let (wire_to_use, wire_to_replace) = sort_tuple((a.clone(), b.clone()));

        // If `wire_to_replace` has a protected name, keep it and replace `wire_to_use` with it.
        // E.g. `root ~ _0` or `ep_0 ~ _0`
        Some(if wire_to_replace == ROOT_PORT_NAME || wire_to_replace.starts_with(EXTERNAL_PORT_PREFIX) {
          (i, wire_to_replace, wire_to_use)
        } else {
          (i, wire_to_use, wire_to_replace)
        })
      }
      _ => None,
    })
    .collect_vec();

  // Inline candidates, iterate reversed to avoid index invalidation when removing from `connections`
  while let Some((i, wire_to_use, wire_to_replace)) = merge_candidates.pop() {
    // Replaces `wire_to_replace` with `wire_to_use` in `connector` if it's found.
    // Returns true if it was found and replaced, which means that the connection
    // corresponding to this candidate can be removed from `connections`.
    fn replace_port(
      connector: &mut NestedConnector,
      wire_to_use: &PortName,
      wire_to_replace: &PortName,
    ) -> bool {
      match connector {
        NestedConnector::Agent(NestedAgent { agent: _, ports }) => {
          // Visit ports of nested agents recursively
          for connector in ports {
            if replace_port(connector, wire_to_use, wire_to_replace) {
              return true;
            }
          }
        }
        NestedConnector::Port(port) => {
          // E.g. if we have `root ~ Lam(_0, _1), _0 ~ _1` and the candidate
          // is represented by `wire_to_use` == "_0" and `wire_to_replace` == "_1"
          // and we are at the `port` named "_1", then we replace it with "_0".
          // That's how `Lam(_0, _1)` becomes `Lam(_0, _0)`.
          if port == wire_to_replace {
            *port = wire_to_use.clone();
            return true;
          }
        }
      }
      false
    }

    // Iterate over all connectors and replace `wire_to_replace` with `wire_to_use`
    let mut replaced = false;
    for NestedConnection { lhs, rhs } in &mut connections {
      for connector in [lhs, rhs] {
        if replace_port(connector, &wire_to_use, &wire_to_replace) {
          replaced = true;

          // There is exactly one connector that contains `wire_to_replace`,
          // apart from the candidate connection itself (e.g. `_0 ~ _1`), which is removed below.
          break;
        }
      }
    }
    if replaced {
      // If one end of a port-to-port connection (e.g. "_1") was replaced with the other end (e.g. "_0"),
      // remove the connection from `connections` (e.g. `_0 ~ _1` in this example)
      connections.remove(i);
    }
  }

  connections
}
