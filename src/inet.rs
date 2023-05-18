use crate::{
  parser::ast::{
    Agent, AgentName, Connection, Connector, PortName, PortNameRef, ROOT_NODE_IDX, ROOT_PORT_NAME,
  },
  rule_book::{AgentId, RuleBook},
  util::sort_tuple,
};
use hashbrown::{hash_map::Entry, HashMap};
use itertools::Itertools;
use std::{fmt, vec};

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

  fn node_is_part_of_active_pair(&self, node_idx: NodeIdx) -> Option<NodeIdx> {
    let dst = self[port(node_idx, 0)];
    // After validation, we can assume that dst.node_idx == node_idx
    (dst.port_idx == 0).then_some(dst.node_idx)
  }

  /// Determine active pairs that can potentially be rewritten if there is a matching rule
  pub fn active_pairs(&self) -> ActivePairs {
    let mut active_pairs = vec![];
    for (node_idx, node) in self.nodes.iter().enumerate() {
      if !node.used {
        continue;
      }

      if let Some(dst_node_idx) = self.node_is_part_of_active_pair(node_idx) {
        if node_idx < dst_node_idx {
          active_pairs.push((node_idx, dst_node_idx));
        }
      }
    }
    active_pairs
  }

  /// Rewrite active pair using rule book
  /// Returns new active pairs that were created during the rewrite
  /// Returns None if active pair could not be rewritten because there was no matching rule
  fn rewrite(&mut self, (a, b): (NodeIdx, NodeIdx), rule_book: &RuleBook) -> Option<ActivePairs> {
    debug_assert!(
      self[port(a, 0)] == port(b, 0) && self[port(b, 0)] == port(a, 0),
      "Expected active pair: {:?}\n{self:#?}",
      (a, b),
    );

    // New active pairs can appear within the inserted sub-net or at the links between the sub-net and
    // the rest of the net. Of the pre-existing nodes, only the nodes whose principal port was linked
    // to an aux port of the active pair before the rewrite can become active pairs after the rewrite.

    // We need to determine which local nodes could form active pairs after this rewrite
    // The rewrite could connect aux ports of both A and B which could form an active pair
    // So initially we add those nodes as candidates whose principal port is connected to
    // an aux port of A or B. (Note that it's impossible that we accidentally add A or B
    // as candidates, because their principal ports are already connected to each other's.)
    // (Also note that we don't have to dedup A's and B's candidates, because each node
    // can only be a candidate once because it only has one principal port.)
    // After the rewrite, we add nodes as candidates that were created during the rewrite
    let active_pair_candidate_nodes = self[a]
      .ports
      .iter()
      .skip(1)
      .chain(self[b].ports.iter().skip(1))
      .filter(|port| port.port_idx == 0)
      .map(|port| port.node_idx)
      .collect::<Vec<_>>();

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

    let rule_application_result = rule_book.apply(self, (a, b));
    for node_idx in intermediary_nodes {
      let node = &self[node_idx];
      let src = node[0];
      let dst = node[1];
      self.link(src, dst);
      self.free_node(node_idx);
    }
    let new_active_pairs = if let Some(created_nodes) = rule_application_result {
      self.free_node(a);
      self.free_node(b);

      // Add nodes created by rewrite as candidates for active pairs
      // There are no duplicates in this chained iter, because these sets are disjoint
      // let created_nodes = dbg!(created_nodes);
      let active_pair_candidate_nodes = active_pair_candidate_nodes.into_iter().chain(created_nodes);

      // Check which of the candidates actually form active pairs.
      // Sort each pair of node indices so that we can dedup them.
      // Sort the list of pairs so that we can dedup them.
      // TODO: Optimize, don't allocate memory
      let new_active_pairs = active_pair_candidate_nodes
        .filter_map(|node_idx| {
          debug_assert!(self[node_idx].used, "Node {node_idx} is not used: {:#?}", self[node_idx]);
          self.node_is_part_of_active_pair(node_idx).map(|dst_node_idx| {
            debug_assert!(
              self[dst_node_idx].used,
              "Node {dst_node_idx} is not used: {:#?}",
              self[dst_node_idx]
            );
            sort_tuple((node_idx, dst_node_idx))
          })
        })
        .sorted()
        .dedup()
        .collect_vec();
      Some(new_active_pairs)
    } else {
      None // No rewrite happened, so no new active pairs came into existence
    };

    if cfg!(debug_assertions) {
      self.validate();
    }
    new_active_pairs
  }

  /// Perform one reduction step
  pub fn reduce_step(&mut self, rule_book: &RuleBook) -> bool {
    for active_pair in self.active_pairs() {
      if self.rewrite(active_pair, rule_book).is_some() {
        return true;
      }
    }
    false
  }

  /// Reduce net until no more reductions are possible, without rescanning for active pairs after each rewrite.
  /// Only scans the net for active pairs in the beginning. After each rewrite, new active pairs are found by
  /// checking the nodes involved in and adjacent to the rewritten sub-net.
  pub fn reduce_full(&mut self, rule_book: &RuleBook) -> usize {
    let mut active_pairs = self.active_pairs();
    let mut new_active_pairs = vec![];
    let mut reduction_count = 0;
    while !active_pairs.is_empty() {
      // At this point, `new_active_pairs` is empty and `active_pairs` contains all currently active pairs
      for active_pair in active_pairs.drain(..) {
        if let Some(new_active_pairs_created_by_rewrite) = self.rewrite(active_pair, rule_book) {
          new_active_pairs.extend(new_active_pairs_created_by_rewrite);
          reduction_count += 1;
        }
      }
      // At this point, `active_pairs` is empty and `new_active_pairs` contains all new active pairs
      active_pairs.extend(new_active_pairs.drain(..)); // Reusing Vecs between iterations
    }
    reduction_count
  }

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
  fn add_connector<'a, 'b: 'a>(
    &mut self,
    connector: &'b Connector,
    ports_to_link: &'a mut Vec<[MaybeLinkedPort<'b>; 2]>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
    created_nodes: &mut CreatedNodes,
  ) -> MaybeLinkedPort<'b> {
    match connector {
      Connector::Agent(agent) => {
        // Insert agent node
        let agent_name = agent.agent.clone();
        let Agent { agent, ports } = agent;
        let agent_id = agent_name_to_id[agent];
        let node_idx = self.new_node(agent_id, 1 + ports.len());
        self[node_idx].agent_name = agent_name;

        for (i, port_name) in ports.iter().enumerate() {
          let port = port(node_idx, 1 + i); // +1 to skip principal port

          // Queue up connection to link it later
          ports_to_link.push([Ok(port), Err(port_name)]);
        }

        // Keep track of created nodes so that we can determine active pairs created by this rewrite
        created_nodes.push(node_idx);

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
    ports_to_link: HashMap<PortNameRef<'a>, NodePort>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
  ) -> CreatedNodes {
    fn port_target<'a, 'b: 'a>(
      ports_to_link_later: &'a mut Vec<[MaybeLinkedPort<'b>; 2]>,
      port_name: PortNameRef<'b>,
    ) -> MaybeLinkedPort<'b> {
      let mut target: MaybeLinkedPort = Err(port_name);
      while let Some((i, connector)) = ports_to_link_later.iter().enumerate().find_map(|(i, [lhs, rhs])| {
        if lhs == &target {
          Some((i, *rhs))
        } else if rhs == &target {
          Some((i, *lhs))
        } else {
          None
        }
      }) {
        // Found connection target of `port_name`, remove the connection
        let _ = ports_to_link_later.swap_remove(i);

        target = connector;
        if target.is_ok() {
          break;
          // If the connector is a port name, follow the connection further
        }
      }
      target
    }

    // We keep track of connections that are not linked together yet, as unordered pairs of ports.
    // Unlinked ports are represented by Err(name), linked ports by Ok(port)
    // E.g. when this function is called with [ A(a, a) ~ b, b ~ C(root) ],
    // `ports_to_link_later` will contain [(Ok(A.ports[0]), Err("b")), (Err("b"), Ok(C.ports[0]))]
    // What happens with A.ports[1] and A.ports[2]:
    // During the call of `add_connector` for A, A.ports[1] is inserted into `ports_to_link` and
    // when processing A.ports[2], it will find ("a", A.ports[1]) in `ports_to_link`, remove it
    // and link A.ports[1] to A.ports[2].
    // During the call of `add_connector` for C, when processing C.ports[1], it will find ("root", (0, 0))
    // in `ports_to_link`, remove it and link (0, 0) to C.ports[1].
    // We pre-populate `ports_to_link_later` with external ports:
    let mut ports_to_link_later =
      ports_to_link.into_iter().map(|(port_name, node_port)| [Ok(node_port), Err(port_name)]).collect_vec();

    let mut created_nodes = vec![];

    // Add all connectors of all connections to `ports_to_link_later`
    for Connection { lhs, rhs } in connections {
      let lhs = self.add_connector(&lhs, &mut ports_to_link_later, agent_name_to_id, &mut created_nodes);
      let rhs = self.add_connector(&rhs, &mut ports_to_link_later, agent_name_to_id, &mut created_nodes);
      ports_to_link_later.push([lhs, rhs]);
    }
    // At this point, `ports_to_link_later` contains all pairs of ports that still need to be linked

    // Link all pairs of ports that could not be linked yet
    while let Some([lhs, rhs]) = ports_to_link_later.pop() {
      match (lhs, rhs) {
        (Ok(lhs), Ok(rhs)) => {
          // Both connectors are ready to be linked
          self.link(lhs, rhs);
        }
        (Ok(node_port), Err(port_name)) | (Err(port_name), Ok(node_port)) => {
          // Look up the connection target of `port_name` and queue the connection for later linking
          let target = port_target(&mut ports_to_link_later, port_name);
          ports_to_link_later.push([Ok(node_port), target]);
        }
        (Err(lhs), Err(rhs)) => {
          // Look up the connection target of both connectors, and queue the connection for later linking
          let lhs = port_target(&mut ports_to_link_later, lhs);
          let rhs = port_target(&mut ports_to_link_later, rhs);
          ports_to_link_later.push([lhs, rhs]);
        }
      }
    }

    created_nodes
  }
}

pub type CreatedNodes = Vec<NodeIdx>;

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
