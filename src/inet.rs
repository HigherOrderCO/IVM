use crate::{
  parser::ast::{
    Agent, AgentName, Connection, Connector, PortName, PortNameRef, ROOT_NODE_IDX, ROOT_PORT_NAME,
  },
  rule_book::{AgentId, RuleBook},
};
use hashbrown::{hash_map::Entry, HashMap};
use itertools::Itertools;
use std::fmt;

pub type NodeIdx = usize;
pub type PortIdx = usize;

#[derive(Debug, Clone, Default)]
pub struct Node {
  used: bool,
  pub agent_id: AgentId,     // Note: Has value ROOT_AGENT_ID by default
  pub ports: Vec<NodePort>,  // 0: principal port
  pub agent_name: AgentName, // TODO: Remove, map agent_id to agent_name for readback
}

// Note: (0, 0) is default
#[derive(Default, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodePort {
  pub node_idx: NodeIdx,
  pub port_idx: PortIdx,
}

impl fmt::Display for NodePort {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}", (self.node_idx, self.port_idx))
  }
}

pub fn port(node_idx: NodeIdx, port_idx: PortIdx) -> NodePort {
  NodePort { node_idx, port_idx }
}

#[derive(Default, Debug, Clone)]
pub struct INet {
  pub nodes: Vec<Node>,
  free_nodes: Vec<NodeIdx>,
}

impl INet {
  pub fn new_node(&mut self, agent_id: AgentId, port_count: usize) -> NodeIdx {
    let node_idx = match self.free_nodes.pop() {
      Some(node_idx) => node_idx,
      None => {
        let node_idx = self.nodes.len();
        self.nodes.push(Default::default());
        node_idx
      }
    };
    let node = &mut self[node_idx];
    node.used = true;
    node.agent_id = agent_id;
    node.ports = vec![Default::default(); port_count];
    node_idx
  }

  pub fn free_node(&mut self, node_idx: NodeIdx) {
    self[node_idx] = Default::default();
    self.free_nodes.push(node_idx);
  }

  // Mutually link port
  pub fn link(&mut self, a: NodePort, b: NodePort) {
    self[a] = b;
    self[b] = a;
  }

  // TODO: Consume self, return validated type / error instead of assert
  pub fn validate(&self) {
    let mut used_node_count = 0;
    for (node_idx, node) in self.nodes.iter().enumerate() {
      if node.used {
        used_node_count += 1;

        for port_idx in 0 .. node.ports.len() {
          let src = port(node_idx, port_idx);
          let dst = self[src];

          assert_eq!(self[dst], src, "\nNon-bidirectional link {:?}:\n{self:#?}", (src, dst));

          assert!(self[dst.node_idx].used, "\nUsed node linked to unused node {:?}:\n{self:#?}", (src, dst));
        }
      } else {
        assert_eq!(node.ports, vec![]);
        assert!(self.free_nodes.contains(&node_idx), "\n{self:#?}");
      }
    }
    assert!(used_node_count >= 2, "Interaction net has {used_node_count} < 2 nodes:\n{self:#?}");
  }

  pub fn active_pairs(&self) -> Vec<(NodeIdx, NodeIdx)> {
    let mut active_pairs = vec![];
    for (node_idx, node) in self.nodes.iter().enumerate() {
      if !node.used {
        continue;
      }
      let dst = self[port(node_idx, 0)];
      // After validation, we can assume that dst.node_idx == node_idx
      if node_idx < dst.node_idx && dst.port_idx == 0 {
        active_pairs.push((node_idx, dst.node_idx));
      }
    }
    active_pairs
  }

  // Rewrite active pair using rule book
  fn rewrite(&mut self, (a, b): (NodeIdx, NodeIdx), rule_book: &RuleBook) -> bool {
    debug_assert!(
      self[port(a, 0)] == port(b, 0) && self[port(b, 0)] == port(a, 0),
      "Expected active pair: {:?}\n{self:#?}",
      (a, b),
    );

    // If active pair contains two references to the same wire, we have to link
    // the target of both references afterwards, so that the nodes can be freed
    // Case A(a, b) ~ B(c, c) -> link(self[port(b, 1)], self[port(b, 2)])
    // Case A(a, b) ~ B(b, c) -> link(self[port(a, 2)], self[port(b, 0)])
    // Case A(a, b) ~ B(a, b) -> link(self[port(a, 1)], self[port(b, 1)])
    //                       and link(self[port(a, 2)], self[port(b, 2)])
    // Case A(a, a) ~ B(b, b) -> link(self[port(a, 1)], self[port(a, 2)])
    //                       and link(self[port(b, 1)], self[port(b, 2)])
    // If any port of A or B is linked to any port of A or B, we temporarily
    // break the link by adding an intermediary node (with 2 ports because it
    // represents a wire going through it). After doing the rewrite, we link
    // both target ports of the intermediary node together and free it.

    const INTERMEDIARY_AGENT_ID: AgentId = usize::MAX;
    let mut intermediary_nodes = vec![];
    for node_idx in [a, b] {
      for port_idx in 0 .. self[node_idx].ports.len() {
        let dst = self[node_idx][port_idx];
        if dst.node_idx == a || dst.node_idx == b {
          // Create intermediary node temporarily until after rewrite
          // E.g. A(a, a) ~ B => A(a, b) ~ B, a ~ TMP(b)
          // E.g. A(a) ~ B(a) => A(a) ~ B(b), a ~ TMP(b)
          let intermediary = self.new_node(INTERMEDIARY_AGENT_ID, 2);
          let src = port(node_idx, port_idx);
          self.link(src, port(intermediary, 0));
          self.link(dst, port(intermediary, 1));
          intermediary_nodes.push(intermediary);
        }
      }
    }

    let rewritten = rule_book.apply(self, (a, b));
    for node_idx in intermediary_nodes {
      let node = &self[node_idx];
      let src = node[0];
      let dst = node[1];
      self.link(src, dst);
      self.free_node(node_idx);
    }
    if rewritten {
      self.free_node(a);
      self.free_node(b);
    }

    if cfg!(debug_assertions) {
      self.validate();
    }
    rewritten
  }

  // Perform one reduction step
  pub fn reduce_step(&mut self, rule_book: &RuleBook) -> bool {
    for active_pair in self.active_pairs() {
      if self.rewrite(active_pair, rule_book) {
        return true;
      }
    }
    false
  }

  pub fn reduce_full(&mut self, rule_book: &RuleBook) {
    while {
      let mut made_progress = false;
      for active_pair in self.active_pairs() {
        if self.rewrite(active_pair, rule_book) {
          made_progress = true;
        }
      }
      made_progress
    } {}
  }

  pub fn read_back(&self) -> Vec<Connection> {
    let mut connections = vec![];

    let mut node_idx_to_agent_port_names = HashMap::<NodeIdx, Vec<PortName>>::new();

    let mut new_port_name = {
      let mut next_port_idx = 0;
      move || {
        let r = format!("_{}", next_port_idx);
        next_port_idx += 1;
        r
      }
    };

    for (node_idx, node) in self.nodes.iter().enumerate() {
      if !node.used {
        continue;
      }

      for port_idx in 0 .. node.ports.len() {
        let src = port(node_idx, port_idx);
        let dst = self[src];
        if src < dst {
          let mut connector = |node_port: NodePort| {
            let node = &self[node_port.node_idx];
            let agent_port_names = node_idx_to_agent_port_names
              .entry(node_port.node_idx)
              .or_insert_with(|| (0 .. node.ports.len() - 1).map(|_| new_port_name()).collect());
            if node_port.port_idx == 0 {
              if node_port.node_idx == ROOT_NODE_IDX {
                Connector::Port(ROOT_PORT_NAME.to_string())
              } else {
                Connector::Agent(Agent {
                  agent: node.agent_name.clone(), // TODO: Map agent_id to agent_name
                  ports: agent_port_names.clone(),
                })
              }
            } else {
              Connector::Port(agent_port_names[node_port.port_idx - 1].clone())
            }
          };

          let src = connector(src);
          let dst = connector(dst);
          connections.push(Connection::new(src, dst));
        }
      }
    }
    connections
  }

  pub fn add_connections<'a>(
    &mut self,
    connections: &'a [Connection],
    mut external_links: HashMap<PortNameRef<'a>, NodePort>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
  ) {
    type MaybeLinkedPort<'a> = Result<NodePort, PortNameRef<'a>>;
    let mut ports_to_link_later = Vec::<[MaybeLinkedPort; 2]>::new();
    {
      for Connection { lhs, rhs } in connections {
        fn encode_connector<'a>(
          connector: &'a Connector,
          net: &mut INet,
          external_links: &mut HashMap<PortNameRef<'a>, NodePort>,
          agent_name_to_id: &HashMap<AgentName, AgentId>,
        ) -> MaybeLinkedPort<'a> {
          match connector {
            Connector::Agent(agent) => {
              let agent_name = agent.agent.clone();
              let Agent { agent, ports } = agent;
              let agent_id = agent_name_to_id[agent];
              let node_idx = net.new_node(agent_id, 1 + ports.len());
              net[node_idx].agent_name = agent_name;
              for (i, port_name) in ports.iter().enumerate() {
                let port = port(node_idx, 1 + i);
                match external_links.entry(port_name) {
                  Entry::Occupied(entry) => {
                    net.link(port, entry.remove());
                  }
                  Entry::Vacant(entry) => {
                    entry.insert(port);
                  }
                }
              }
              Ok(port(node_idx, 0))
            }
            Connector::Port(port) => Err(port),
          }
        }

        let lhs = encode_connector(&lhs, self, &mut external_links, agent_name_to_id);
        let rhs = encode_connector(&rhs, self, &mut external_links, agent_name_to_id);
        match (lhs, rhs) {
          (Ok(lhs), Ok(rhs)) => self.link(lhs, rhs),
          _ => {
            ports_to_link_later.push([lhs, rhs]);
          }
        }
      }
      ports_to_link_later
        .extend(external_links.into_iter().map(|(port_name, node_port)| [Err(port_name), Ok(node_port)]));
    }

    fn follow_links_until_port<'a>(
      port_name: PortNameRef<'a>,
      mut prev: MaybeLinkedPort<'a>,
      ports_to_link_later: &[[MaybeLinkedPort<'a>; 2]],
    ) -> Result<NodePort, PortNameRef<'a>> {
      let mut port_to_find = Err(port_name);
      while let Some(connector) = ports_to_link_later.iter().find_map(|[lhs, rhs]| {
        // There are two matches in the list, one connection where we
        // came from, and the other one is the one we want to visit
        if lhs == &port_to_find {
          (rhs != &prev).then_some(rhs)
        } else if rhs == &port_to_find {
          (lhs != &prev).then_some(lhs)
        } else {
          None
        }
      }) {
        match connector {
          Ok(node_port) => return Ok(*node_port),
          _ => {
            prev = port_to_find;
            port_to_find = *connector;
          }
        }
      }
      port_to_find
    }

    fn lookup_port_name(
      port_name: PortNameRef,
      prev: MaybeLinkedPort,
      ports_to_link_later: &[[MaybeLinkedPort; 2]],
    ) -> Result<NodePort, String> {
      follow_links_until_port(port_name, prev, &ports_to_link_later)
        .map_err(|_| format!("Port not found: `{}`", port_name))
    }
    let target = |port: MaybeLinkedPort, prev: MaybeLinkedPort, ports_to_link_later| {
      port.or_else(|port_name| lookup_port_name(port_name, prev, ports_to_link_later))
    };

    for [lhs, rhs] in &ports_to_link_later {
      match (lhs, rhs) {
        (&Ok(lhs), &Ok(rhs)) => self.link(lhs, rhs),
        (Err(_), Err(_)) => {} // Skip
        (&Ok(node_port), &Err(port_name)) | (&Err(port_name), &Ok(node_port)) => {
          let port_to_find: MaybeLinkedPort = Err(port_name);
          let mut connections = ports_to_link_later
            .iter()
            .filter_map(|[lhs, rhs]| {
              if lhs == &port_to_find {
                Some(rhs)
              } else if rhs == &port_to_find {
                Some(lhs)
              } else {
                None
              }
            })
            .copied()
            .collect_vec();
          let port = if connections.len() == 2 {
            // If we have Ok(port) ~ Err(a), Err(a) ~ X, `connections` is [Ok(port), X] or [X, Ok(port)]
            // We want to link Ok(port) ~ target(X), so we must follow X
            connections.remove((connections[0] == Ok(node_port)) as usize)
          } else {
            // Every link occurs as two connections, so we can't have a single connection
            unreachable!("{:?}", (lhs, rhs))
          };
          let prev = port_to_find; // Don't go to Err(a) after X
          let target = target(port, prev, &ports_to_link_later).unwrap_or_else(|_| {
            panic!("\nTarget not found for port: `{port_name}`\nports_to_link_later: {ports_to_link_later:?}")
          });
          self.link(node_port, target);
        }
      }
    }
  }
}

use std::ops::{Index, IndexMut};

impl Index<NodeIdx> for INet {
  type Output = Node;

  fn index(&self, idx: NodeIdx) -> &Self::Output {
    &self.nodes[idx]
  }
}

impl IndexMut<NodeIdx> for INet {
  fn index_mut(&mut self, idx: NodeIdx) -> &mut Self::Output {
    &mut self.nodes[idx]
  }
}

impl Index<PortIdx> for Node {
  type Output = NodePort;

  fn index(&self, idx: PortIdx) -> &Self::Output {
    &self.ports[idx]
  }
}

impl IndexMut<PortIdx> for Node {
  fn index_mut(&mut self, idx: PortIdx) -> &mut Self::Output {
    &mut self.ports[idx]
  }
}

impl Index<NodePort> for INet {
  type Output = NodePort;

  fn index(&self, idx: NodePort) -> &Self::Output {
    &self[idx.node_idx][idx.port_idx]
  }
}

impl IndexMut<NodePort> for INet {
  fn index_mut(&mut self, idx: NodePort) -> &mut Self::Output {
    &mut self[idx.node_idx][idx.port_idx]
  }
}
