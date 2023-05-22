use crate::{
  parser::ast::{
    Agent, AgentName, Connection, Connector, PortName, PortNameRef, ROOT_NODE_IDX, ROOT_PORT_NAME,
  },
  rule_book::{AgentId, RuleBook, EXTERNAL_NODE_IDX},
  util::sort_tuple,
};
use hashbrown::HashMap;
use itertools::Itertools;
use smallvec::SmallVec;
use std::{
  collections::VecDeque,
  fmt,
  ops::{Index, IndexMut},
  vec,
};

pub type NodeIdx = usize;
pub type PortIdx = usize;

type PortVec = SmallVec<[NodePort; 4]>; // SmallVec to avoid heap allocation for small port counts

/// A node in the INet
#[derive(Debug, Clone, Default)]
pub struct Node {
  /// Unused nodes are available for reuse
  used: bool,

  /// Note: Has value ROOT_AGENT_ID by default
  pub agent_id: AgentId,

  /// 0: principal port
  pub ports: PortVec,

  pub agent_name: AgentName,
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

/// Construct a NodePort that can be used to index into INet
pub fn port(node_idx: NodeIdx, port_idx: PortIdx) -> NodePort {
  NodePort { node_idx, port_idx }
}

/// This represents the interaction net
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

    // TODO: Optimize mem allocs, clear instead of overwrite
    node.ports = vec![Default::default(); port_count].into();
    // node.ports.clear();
    // node.ports.resize(port_count, Default::default());

    node_idx
  }

  /// Make node available for reuse
  pub fn free_node(&mut self, node_idx: NodeIdx) {
    self[node_idx] = Default::default(); // TODO: Optimize mem allocs, clear instead of overwrite
    self.free_nodes.push(node_idx);
  }

  /// Mutually link ports
  pub fn link(&mut self, a: NodePort, b: NodePort) {
    if a.node_idx != EXTERNAL_NODE_IDX && b.node_idx != EXTERNAL_NODE_IDX {
      self[a] = b;
      self[b] = a;
    }
  }

  /// Like `link`, except it doesn't link to external nodes.
  /// Returns true if the link was successful, false otherwise
  pub fn link_external(&mut self, a: NodePort, b: NodePort) {
    if a.node_idx != EXTERNAL_NODE_IDX {
      self[a] = b;
    }
    if b.node_idx != EXTERNAL_NODE_IDX {
      self[b] = a;
    }
  }

  /// Validate the inet, panics if invalid, useful for debugging/tests
  /// If an INet generated from a valid AST fails validation, it'd be a bug
  pub fn validate(&self) {
    let mut used_node_count = 0;
    for (node_idx, node) in self.nodes.iter().enumerate() {
      if node.used {
        used_node_count += 1;

        assert_ne!(node.ports.len(), 0, "Nodes must have at least one port:\n{node:#?}");
        for port_idx in 0 .. node.ports.len() {
          let src = port(node_idx, port_idx);
          let dst = self[src];

          assert_eq!(self[dst], src, "\nNon-bidirectional link {:?}:\n{self:#?}", (src, dst));

          assert!(self[dst.node_idx].used, "\nUsed node linked to unused node {:?}:\n{self:#?}", (src, dst));
        }
      } else {
        assert_eq!(node.ports, PortVec::default());
        assert!(self.free_nodes.contains(&node_idx), "\n{self:#?}");
      }
    }
    assert!(used_node_count >= 2, "Interaction net has {used_node_count} < 2 nodes:\n{self:#?}");
  }

  /// Add a `Connector` to the net, only called by `INet::add_connections`.
  /// If the connector is a port, `Err(port_name)` is returned so that it can be linked later.
  /// If the connector is an agent, it is added as a new node and its principal port is returned as `Ok(port)`.
  /// Connections to auxiliary ports are added to `deferred_port_links` so that they can be linked later.
  fn add_connector<'a, 'b: 'a>(
    &mut self,
    connector: &'b Connector,
    deferred_port_links: &'a mut MaybeLinkedPorts<'b>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
    created_nodes: &mut CreatedNodes,
  ) -> MaybeLinkedPort<'b> {
    match connector {
      Connector::Agent(agent) => {
        // Create agent node
        let agent_name = agent.agent.clone();
        let Agent { agent, ports } = agent;
        let agent_id = agent_name_to_id[agent];
        let node_idx = self.new_node(agent_id, 1 + ports.len());
        self[node_idx].agent_name = agent_name;

        for (i, port_name) in ports.iter().enumerate() {
          let port = port(node_idx, 1 + i); // +1 to skip principal port

          // Queue up connection to link it later
          deferred_port_links.push([Err(port_name), Ok(port)]);
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

  /// Add connections to the net, either when creating a net from scratch or inserting a sub-net
  /// during a rewrite. `external_ports` is a map from port names to ports in the parent net.
  /// When creating a net from scratch (in `ValidatedAst::into_inet_program`),
  /// `external_ports` only contains the `root` port.
  /// When called by `RuleBook::apply`, `external_ports` contains the ports of the parent net that
  /// the rule's RHS sub-net is connected to, based on which INet ports the rule's LHS (active pair)
  /// aux port names map to, in that context of the local rewrite.
  pub fn add_connections<'a>(
    &mut self,
    connections: &'a [Connection],
    external_ports: MaybeLinkedPorts<'a>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
  ) -> CreatedNodes {
    /// Follow connections to find the target of a `port_name` that it resolves to.
    /// Returns `Ok(port)` if the target port could be found, `Err(port_name)` otherwise.
    /// Connections are removed (consumed) from `deferred_port_links` as they are followed.
    /// E.g. if `deferred_port_links` is `[Err("x") ~ Err("y"), Err("y") ~ port]` and `port_name` is "x",
    /// `Ok(port)` is returned and `deferred_port_links` is updated to `[]` as the followed links were consumed.
    /// As long as `deferred_port_links` is not empty, there are still unresolved ports to be linked.
    fn port_target<'a, 'b: 'a>(
      deferred_port_links: &'a mut MaybeLinkedPorts<'b>,
      port_name: PortNameRef<'b>,
    ) -> MaybeLinkedPort<'b> {
      let mut target: MaybeLinkedPort = Err(port_name);
      while let Some((i, connector)) = deferred_port_links.iter().enumerate().find_map(|(i, [lhs, rhs])| {
        if lhs == &target {
          Some((i, *rhs))
        } else if rhs == &target {
          Some((i, *lhs))
        } else {
          None
        }
      }) {
        // Found connection target of `port_name`, remove the connection
        let _ = deferred_port_links.swap_remove(i);

        target = connector;
        if target.is_ok() {
          break;
          // If the connector is `Err(port_name)`, continue looking up further
        }
      }
      target
    }

    // We keep track of connections that are not linked together yet, as unordered pairs of ports.
    // Unlinked ports are represented by Err(name), linked ports by Ok(port).
    // We pre-populate `deferred_port_links` with `external_ports`:
    let mut deferred_port_links = external_ports;

    let mut created_nodes = vec![];

    // Add all connectors of all connections to `deferred_port_links`
    for Connection { lhs, rhs } in connections {
      let lhs = self.add_connector(&lhs, &mut deferred_port_links, agent_name_to_id, &mut created_nodes);
      let rhs = self.add_connector(&rhs, &mut deferred_port_links, agent_name_to_id, &mut created_nodes);
      deferred_port_links.push([lhs, rhs]);
    }

    // At this point, `deferred_port_links` contains all pairs of ports that need to be linked

    // Link all pairs of ports that could not be linked yet
    while let Some([lhs, rhs]) = deferred_port_links.pop() {
      eprintln!("deferred_port_links: {deferred_port_links:#?}, {lhs:?} ~ {rhs:?}");
      match (lhs, rhs) {
        (Ok(lhs), Ok(rhs)) => {
          // Both connectors are resolved to ports, thus ready to be linked
          self.link_external(lhs, rhs);
          eprintln!("Linked {lhs} ~ {rhs}");
        }
        (Ok(node_port), Err(port_name)) | (Err(port_name), Ok(node_port)) => {
          // Look up the connection target of `port_name` and queue the connection for later linking
          let target = port_target(&mut deferred_port_links, port_name);
          deferred_port_links.push([target, Ok(node_port)]);
        }
        (Err(lhs_name), Err(rhs_name)) => {
          // Look up the connection target of both connectors, and queue the connection for later linking
          let lhs = port_target(&mut deferred_port_links, lhs_name);
          let rhs = port_target(&mut deferred_port_links, rhs_name);
          if lhs == Err(lhs_name) && rhs == Err(rhs_name) {
            // Both connectors are unresolved, so we can't link them
          } else {
            deferred_port_links.push([lhs, rhs]);
          }
        }
      }
    }

    created_nodes
  }

  // Inserts a rule's RHS sub-net into the net, called by `RuleBook::apply`.
  // `external_ports` is a map from external port indices to ports in the `self` net.
  // External port indices refer to auxiliary ports in the active pair of the rule LHS:
  // E.g. if the rule LHS is `X(a, b) ~ Y(c, d)`, then `external_ports` contains the ports of `self`
  // that map to `[a, b, c, d]` (in that order) in the context of the local rewrite.
  // In other words, the ports are indexed left-to-right, after ordering both active pair agent IDs:
  // So the external ports would be the same if the rule LHS was written as `Y(c, d) ~ X(a, b)`.
  // (Assuming X's AgentId < Y's AgentId in this example.)
  pub fn insert_rule_rhs_subnet(&mut self, subnet: &INet, external_ports: &[NodePort]) -> CreatedNodes {
    // TODO: Use reuseable Vec, since subnet indices start at 0
    // Copy all fields other than `ports` from `subnet` to `self` and keep track of new node indices
    let subnet_node_idx_to_self_node_idx = subnet
      .nodes
      .iter()
      .map(|node| {
        debug_assert!(node.used); // Rule RHS subnets should have all unused nodes removed

        // Create a new node in `self` for each node in `subnet`
        let node_idx = self.new_node(node.agent_id, node.ports.len());
        self[node_idx].agent_name = node.agent_name.clone();

        node_idx
      })
      .collect_vec();

    // Copy mapped ports using new node indices
    for (subnet_node, self_node_idx) in subnet.nodes.iter().zip(&subnet_node_idx_to_self_node_idx) {
      // TODO: get_unchecked_mut
      let self_node = &mut self[*self_node_idx];
      for (subnet_port, self_port) in subnet_node.ports.iter().zip(self_node.ports.iter_mut()) {
        let NodePort { node_idx: subnet_node_idx, port_idx } = *subnet_port;
        *self_port = if subnet_node_idx == EXTERNAL_NODE_IDX {
          // Map `port_idx` to external port in `self`
          // TODO: get_unchecked
          external_ports[port_idx]
          // TODO: Start external port indices at 1 to avoid confusion with principal port?
        } else {
          // Map `node_idx` from `subnet` to `self`
          // TODO: get_unchecked
          NodePort { node_idx: subnet_node_idx_to_self_node_idx[subnet_node_idx], port_idx }
        };
      }
    }

    subnet_node_idx_to_self_node_idx
  }

  /// Remove all unused nodes
  pub fn remove_unused_nodes(&mut self) {
    for unused_node_idx in self.free_nodes.drain(..) {
      // Remove node
      let _unused_node = self.nodes.remove(unused_node_idx);
      for node in &mut self.nodes {
        // Update node indices in links
        for port in &mut node.ports {
          if port.node_idx > unused_node_idx {
            port.node_idx -= 1;
          }
        }
      }
    }
  }

  /// Determines if a given node is part of an active pair and returns the other node in the pair
  fn node_is_part_of_active_pair(&self, node_idx: NodeIdx) -> Option<NodeIdx> {
    let dst = self[port(node_idx, 0)];
    // After validation, we can assume that dst.node_idx == node_idx
    (dst.port_idx == 0).then_some(dst.node_idx)
  }

  /// Determine active pairs that can potentially be rewritten if there is a matching rule
  pub fn scan_active_pairs(&self) -> ActivePairs {
    let mut active_pairs = vec![];
    for (node_idx, node) in self.nodes.iter().enumerate() {
      if !node.used {
        continue;
      }

      if let Some(dst_node_idx) = self.node_is_part_of_active_pair(node_idx) {
        // Only process each bidirectional link once, to prevent duplicates
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
    // After the rewrite, we add the nodes as candidates that were created during the rewrite.
    let active_pair_candidate_nodes = self[a]
      .ports
      .iter()
      .skip(1)
      .chain(self[b].ports.iter().skip(1))
      .filter(|port| port.port_idx == 0)
      .map(|port| port.node_idx)
      .collect::<Vec<_>>();

    /*
    The rewrite mechanism assumes that all wires between aux ports of the active pair
    and the rest of the net are unique. E.g. `A(a, a) ~ B` or `A(a) ~ B(a)` would be a problem.
    Our workaround: If the active pair contains two references to the same wire,
    we split the wire into two, by inserting a temporary intermediary node:
    E.g. `A(a, a) ~ B` becomes `A(a, b) ~ B, a ~ TMP(b)`
    E.g. `A(a) ~ B(a)` becomes `A(a) ~ B(b), a ~ TMP(b)`
    This is done by adding an intermediary node with two ports, one of which is linked to each
    of the two aux ports that were previously using the same wire (like a wire going through it).
    Then the rewrite is performed as usual, and afterwards the two ports of the intermediary
    node are linked together and the intermediary node is removed.
    */
    const INTERMEDIARY_AGENT_ID: AgentId = usize::MAX;
    let mut intermediary_nodes = vec![];
    for node_idx in [a, b] {
      for port_idx in 0 .. self[node_idx].ports.len() {
        let dst = self[node_idx][port_idx];
        if dst.node_idx == a || dst.node_idx == b {
          // Create intermediary node that will be removed after rewrite. It temporarily converts
          // the problematic self-link of the active pair into a link to another node,
          // which allows us to rewrite the active pair by assuming there are no self-links.
          // We link port 0 of TMP to src and port 1 of TMP to dst, to split the shared wire.
          let intermediary = self.new_node(INTERMEDIARY_AGENT_ID, 2);
          let src = port(node_idx, port_idx);
          self.link(src, port(intermediary, 0));
          self.link(dst, port(intermediary, 1));
          intermediary_nodes.push(intermediary);
        }
      }
    }

    // Apply rewrite rule to active pair if there is a matching rule
    let rule_application_result = rule_book.apply(self, (a, b));

    // Now that the rewrite is done (or no rewrite happened if there was no applicable rule),
    // we can remove the intermediary nodes and link their two wires together into one again.
    for node_idx in intermediary_nodes {
      let node = &self[node_idx];
      let src = node[0];
      let dst = node[1];
      self.link(src, dst);
      self.free_node(node_idx);
    }

    let new_active_pairs = if let Some(created_nodes) = rule_application_result {
      // Remove the nodes of the active pair that was rewritten
      self.free_node(a);
      self.free_node(b);

      // Add nodes created by rewrite as candidates for new active pairs.
      // There are no duplicates in this chained iter, because these sets are disjoint
      let active_pair_candidate_nodes = active_pair_candidate_nodes.into_iter().chain(created_nodes);

      // Check which of the candidates actually form active pairs.
      // Sort each pair of node indices so that we can dedup them.
      // Sort the list of pairs so that we can dedup them.
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

  /// Perform one reduction step:
  /// Scan for active pairs and rewrite the first one for which a rule exists.
  /// Returns true if a rewrite happened, false otherwise (either because
  /// there are no active pairs or because no rule applies to any of them).
  /// Not efficient because of the rescan for active pairs, but useful for debugging.
  pub fn scan_active_pairs_and_reduce_step(&mut self, rule_book: &RuleBook) -> bool {
    for active_pair in self.scan_active_pairs() {
      if self.rewrite(active_pair, rule_book).is_some() {
        return true;
      }
    }
    false
  }

  /// Reduce net until no more reductions are possible, without rescanning for active pairs after each rewrite.
  /// Only scans the net for active pairs in the beginning. After each rewrite, new active pairs are found by
  /// checking the nodes involved in and adjacent to the rewritten sub-net.
  pub fn reduce(&mut self, rule_book: &RuleBook) -> usize {
    let mut reduction_count = 0;
    let mut active_pairs = VecDeque::from(self.scan_active_pairs());
    // `active_pairs` is a queue, we process active pairs in the order they were found:
    // Pop from the front while the queue is not empty, and push new active pairs to the back.
    while let Some(active_pair) = active_pairs.pop_front() {
      if let Some(new_active_pairs_created_by_rewrite) = self.rewrite(active_pair, rule_book) {
        active_pairs.extend(new_active_pairs_created_by_rewrite);
        reduction_count += 1;
      }
    }
    reduction_count
  }

  /// Read back reduced net into textual form
  pub fn read_back(&self) -> Vec<Connection> {
    // Helper function to generate new unique port names
    let mut new_port_name = {
      let mut next_port_idx = 0;
      move || {
        let r = format!("_{}", next_port_idx);
        next_port_idx += 1;
        r
      }
    };

    // We use this to keep track of the names we give to agent aux ports
    let mut nodes_aux_port_names = HashMap::<NodeIdx, Vec<PortName>>::new();

    // Keep track of connections between ports
    let mut connections = vec![];

    // Iterate over all active links
    for (node_idx, node) in self.nodes.iter().enumerate() {
      if !node.used {
        continue;
      }

      for port_idx in 0 .. node.ports.len() {
        // src ~ dst
        let src = port(node_idx, port_idx);
        let dst = self[src];

        // Only process each bidirectional link once, to prevent duplicates
        if src < dst {
          /// Build a `Connector` from a port. If the port is a principal port, the connector is an `Agent`.
          /// If the port is an aux port, the connector is a `Port`.
          fn build_connector_from_port(
            net: &INet,
            node_idx_to_agent_port_names: &mut HashMap<NodeIdx, Vec<PortName>>,
            mut new_port_name: impl FnMut() -> String,
            node_port: NodePort,
          ) -> Connector {
            let node = &net[node_port.node_idx];
            // Whenever we encounter a node we haven't seen before, we generate new unique aux port names for it.
            // When we encounter the same node again, we read the previously generated aux port names.
            // This ensures that all references to the same node use the same aux port names.
            let agent_aux_port_names = node_idx_to_agent_port_names
              .entry(node_port.node_idx)
              .or_insert_with(|| (1 .. node.ports.len()).map(|_| new_port_name()).collect());

            if node_port.port_idx == 0 {
              // Connected to a principal port, either `x ~ root` or `x ~ Agent(...)`
              if node_port.node_idx == ROOT_NODE_IDX {
                Connector::Port(ROOT_PORT_NAME.to_string())
              } else {
                Connector::Agent(Agent {
                  agent: node.agent_name.clone(),
                  ports: agent_aux_port_names.clone(),
                })
              }
            } else {
              // Connected to auxiliary port of agent: `x ~ aux, Agent(..., aux, ...) ~ y`
              Connector::Port(agent_aux_port_names[node_port.port_idx - 1].clone())
            }
          }

          // For each link src ~ dst, we create a `Connection`
          let src = build_connector_from_port(self, &mut nodes_aux_port_names, &mut new_port_name, src);
          let dst = build_connector_from_port(self, &mut nodes_aux_port_names, &mut new_port_name, dst);
          connections.push(Connection::new(src, dst));
        }
      }
    }
    connections
  }
}

/// Represents the nodes created by a rewrite (when `RuleBook::apply` calls `INet::add_connections`)
pub type CreatedNodes = Vec<NodeIdx>;

/// Represents a connection between two ports for deferred linking
/// Either Ok(port) or Err(port_name) which needs to be looked up later
type MaybeLinkedPort<'a> = Result<NodePort, PortNameRef<'a>>;
type MaybeLinkedPorts<'a> = Vec<[MaybeLinkedPort<'a>; 2]>;

/// Represents active pairs of nodes in a net
type ActivePairs = Vec<(NodeIdx, NodeIdx)>;

// Indexing utils to allow indexing an INet with a NodeIdx and NodePort

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
