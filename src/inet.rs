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

/// A node in the INet
#[derive(Debug, Clone, Default)]
pub struct Node {
  /// Unused nodes are available for reuse
  used: bool,

  /// Note: Has value ROOT_AGENT_ID by default
  pub agent_id: AgentId,

  /// 0: principal port
  pub ports: Vec<NodePort>, // TODO: Use smallvec for reducing heap allocations

  pub agent_name: AgentName, // TODO: Remove. Map agent_id to agent_name for readback
}

/// A port in the INet
/// Note: (0, 0) is default
#[derive(Default, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
  /// Allocate a new node
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

  /// Make node available for reuse
  pub fn free_node(&mut self, node_idx: NodeIdx) {
    self[node_idx] = Default::default();
    self.free_nodes.push(node_idx);
  }

  /// Mutually link port
  pub fn link(&mut self, a: NodePort, b: NodePort) {
    self[a] = b;
    self[b] = a;
  }

  /// Validate inet, panics if invalid, useful for debugging/tests
  /// If an INet generated from a valid AST fails validation, it's a bug
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

  /// Determine active pairs that can potentially be rewritten if there is a matching rule
  pub fn active_pairs(&self) -> ActivePairs {
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

  /// Rewrite active pair using rule book
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
    let mut intermediary_nodes = vec![]; // TODO: Reuse between rewrites
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

  /// Perform one reduction step
  pub fn reduce_step(&mut self, rule_book: &RuleBook) -> bool {
    for active_pair in self.active_pairs() {
      if self.rewrite(active_pair, rule_book) {
        return true;
      }
    }
    false
  }

  /// Reduce net until no more reductions are possible
  // TODO: Only scan all active pairs in the beginning, check neighbors adjacent to rewritten sub-net for new active pairs
  pub fn reduce_full(&mut self, rule_book: &RuleBook) -> usize {
    let mut reduction_count = 0;
    while {
      let mut made_progress = false;
      for active_pair in self.active_pairs() {
        if self.rewrite(active_pair, rule_book) {
          made_progress = true;
          reduction_count += 1;
        }
      }
      made_progress
    } {}
    reduction_count
  }

  /*/// Reduce net until no more reductions are possible, without rescanning for active pairs after each rewrite
  pub fn reduce_full_opt(&mut self, rule_book: &RuleBook) {
    let mut active_pairs = self.active_pairs();
    let mut new_active_pairs = vec![];
    while !active_pairs.is_empty() {
      for active_pair in active_pairs.drain(..) {
        if self.rewrite(active_pair, rule_book) {
          // Add newly created active pairs to the list.
          // New active pairs can appear within the inserted sub-net
          // or at the links between the sub-net and the rest of the net
        }
      }
      active_pairs.extend(new_active_pairs.drain(..));
    }
  }*/

  /// Read back reduced net into textual form
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

  /// Add a `Connector` to the net
  /// Returns Ok(port) if it was added (agent) or linked (via lookup in `ports_to_link`)
  /// Modifies `ports_to_link` such that looked up (found & linked) ports are removed and
  /// auxiliary ports of newly added agents are inserted, so that future lookups can find them.
  fn add_connector<'a>(
    &mut self,
    connector: &'a Connector,
    ports_to_link: &mut HashMap<PortNameRef<'a>, NodePort>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
  ) -> MaybeLinkedPort<'a> {
    match connector {
      Connector::Agent(agent) => {
        // Insert agent node
        let agent_name = agent.agent.clone();
        let Agent { agent, ports } = agent;
        let agent_id = agent_name_to_id[agent];
        let node_idx = self.new_node(agent_id, 1 + ports.len());
        self[node_idx].agent_name = agent_name;

        // Link ports
        for (i, port_name) in ports.iter().enumerate() {
          let port = port(node_idx, 1 + i); // +1 to skip principal port
          match ports_to_link.entry(port_name) {
            Entry::Occupied(entry) => {
              // Link the port to the external port
              self.link(port, entry.remove());
            }
            Entry::Vacant(entry) => {
              // Other end of the link is not external but somewhere in `connections`
              // so it can only be linked later
              entry.insert(port);
            }
          }
        }

        // An agent node has no deps so it can always be created.
        // Return principal port of the created agent node in this net
        Ok(port(node_idx, 0))
      }
      Connector::Port(port) => Err(port), // Can only be linked later
    }
  }

  /// Add connections to the net, either when creating a net from scratch or inserting a sub-net during a rewrite
  /// `ports_to_link` is a map from port names to ports in the parent net
  /// When creating a net from scratch, `ports_to_link` only contains the root port
  pub fn add_connections<'a>(
    &mut self,
    connections: &'a [Connection],
    mut ports_to_link: HashMap<PortNameRef<'a>, NodePort>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
  ) {
    // Unordered pairs of ports that could not be linked yet, at least one of them is not linked yet
    // Unliked ports are represented by Err(name), linked ports by Ok(port)
    // (This won't contain fully linked pairs, so at least one of each is Err.)
    // E.g. when this function is called with [ A(a, a) ~ b, b ~ C(root) ],
    // `ports_to_link_later` will contain [(Ok(A.ports[0]), Err("b")), (Err("b"), Ok(C.ports[0]))]
    // What happens with A.ports[1] and A.ports[2]:
    // During the call of `add_connector` for A, A.ports[1] is inserted into `ports_to_link` and
    // when processing A.ports[2], it will find ("a", A.ports[1]) in `ports_to_link`, remove it
    // and link A.ports[1] to A.ports[2].
    // During the call of `add_connector` for C, when processing C.ports[1], it will find ("root", (0, 0))
    // in `ports_to_link`, remove it and link (0, 0) to C.ports[1].
    let mut ports_to_link_later = Vec::<[MaybeLinkedPort; 2]>::new();

    // Try to link all connectors of all connections
    for Connection { lhs, rhs } in connections {
      let lhs = self.add_connector(&lhs, &mut ports_to_link, agent_name_to_id);
      let rhs = self.add_connector(&rhs, &mut ports_to_link, agent_name_to_id);
      match (lhs, rhs) {
        (Ok(lhs), Ok(rhs)) => {
          // Both connectors could be linked to existing (or created) ports
          self.link(lhs, rhs);
        }
        _ => {
          // At least one of the connectors is not linked yet, so remember to link this pair later
          ports_to_link_later.push([lhs, rhs]);
        }
      }
    }

    // Also remember to link all external ports that were not linked yet
    ports_to_link_later
      .extend(ports_to_link.into_iter().map(|(port_name, node_port)| [Err(port_name), Ok(node_port)]));
    // At this point, `ports_to_link_later` contains all pairs of ports that still need to be linked, these are linked below

    type LinkGraph<'a> = HashMap<&'a MaybeLinkedPort<'a>, Vec<&'a MaybeLinkedPort<'a>>>; // Value Vec has len 2
    let link_graph = ports_to_link_later
      .iter()
      .map(|[a, b]| (a, b))
      .chain(ports_to_link_later.iter().map(|[a, b]| (b, a)))
      .sorted()
      .group_by(|(key, _values)| *key)
      .into_iter()
      .map(|(key, group)| (key, group.map(|(_key, value)| value).collect_vec()))
      .collect::<LinkGraph>();

    /// Find target of `port`. If it's Ok(port), return port.
    /// If it's Err(name), do transitive lookup of name in `ports_to_link_later` and return the port.
    fn target(
      port: MaybeLinkedPort,
      prev: MaybeLinkedPort,
      link_graph: &LinkGraph,
    ) -> Result<NodePort, String> {
      fn lookup_port_name(
        port_name: PortNameRef,
        prev: MaybeLinkedPort,
        link_graph: &LinkGraph,
      ) -> Result<NodePort, String> {
        /// Follows links in `link_graph` until it finds a port with the given name.
        /// `prev` is the port we came from, so we don't follow links back to it.
        /// This functions is used to find the other end of a connection.
        /// E.g. when `link_graph` is [Ok(port) ~ Err(a), Err(a) ~ X, X ~ ...] and we call
        /// `follow_links_until_port("a", Ok(port), link_graph)`, it will lookup the target of "a":
        /// It won't follow the link Ok(port) ~ Err(a) but Err(a) ~ X
        /// to find the other end of the connection that "a" transitsively connects to.
        /// Then we can link `port` with the other end we found.
        fn follow_links_until_port<'a>(
          port_name: PortNameRef<'a>,
          mut prev: MaybeLinkedPort<'a>,
          link_graph: &'a LinkGraph,
        ) -> Result<NodePort, PortNameRef<'a>> {
          let mut port_to_find = Err(port_name);
          while let Some(connector) = link_graph.get(&port_to_find).and_then(|connectors| {
            connectors.iter().find(|connector| {
              // There are two matches, one connection where we
              // came from, and the other one is the one we want to visit
              ***connector != prev
            })
          }) {
            match connector {
              Ok(node_port) => return Ok(*node_port),
              _ => {
                prev = port_to_find;
                port_to_find = **connector;
              }
            }
          }
          port_to_find
        }

        follow_links_until_port(port_name, prev, &link_graph)
          .map_err(|_| format!("Port not found: `{}`", port_name))
      }

      port.or_else(|port_name| lookup_port_name(port_name, prev, link_graph))
    }

    // Link remaining ports that were not linked yet
    for [lhs, rhs] in &ports_to_link_later {
      match (lhs, rhs) {
        (&Ok(_), &Ok(_)) => unreachable!("Both ports were already linked"),
        (Err(_), Err(_)) => {} // Skip, we only process ends of links (Ok(port) values)
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
          let target = target(port, prev, &link_graph).unwrap_or_else(|_| {
            panic!("\nTarget not found for port: `{port_name}`\nlink_graph: {link_graph:#?}");
          });
          self.link(node_port, target);
        }
      }
    }
  }
}

type MaybeLinkedPort<'a> = Result<NodePort, PortNameRef<'a>>;

type ActivePairs = Vec<(NodeIdx, NodeIdx)>;

// Indexing utils to allow indexing an INet with a NodeIdx and NodePort

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
