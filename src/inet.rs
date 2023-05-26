use crate::{
  parser::{
    ast::{Agent, AgentName, Connection, Connector, PortName, PortNameRef, ROOT_NODE_IDX, ROOT_PORT_NAME},
    display::fmt_nested_connections,
    flatten::unflatten_connections,
  },
  rule_book::{AgentId, RuleBook, ROOT_AGENT_ID},
  util::sort_tuple,
};
use hashbrown::HashMap;
use std::{
  cmp::Reverse,
  collections::VecDeque,
  fmt,
  ops::{Index, IndexMut},
  vec,
};

pub type NodeIdx = usize;
pub type PortIdx = usize;

type PortVec = Vec<NodePort>;

/// A node in the INet
#[derive(Debug, Clone, Default)]
pub struct Node {
  /// Unused nodes are available for reuse
  used: bool,

  /// Note: Has value ROOT_AGENT_ID by default
  pub agent_id: AgentId,

  /// 0: principal port
  pub ports: PortVec,
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
#[inline(always)]
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
  #[inline(always)]
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
    node.ports.resize(port_count, Default::default());

    node_idx
  }

  /// Make node available for reuse
  #[inline(always)]
  pub fn free_node(&mut self, node_idx: NodeIdx) {
    let node = &mut self[node_idx];
    node.used = false;
    node.ports.clear();

    self.free_nodes.push(node_idx);
  }

  /// Mutually link ports
  #[inline(always)]
  fn link(&mut self, a: NodePort, b: NodePort) {
    self[a] = b;
    self[b] = a;
  }

  /// Validate the inet, panics if invalid, useful for debugging/tests
  /// If an INet generated from a valid AST fails validation, it'd be a bug
  pub fn validate(&self, allow_unused_nodes: bool) {
    /* if cfg!(test) {
      eprintln!("validate: {self:#?}");
    } */

    let mut contains_unused_nodes = false;
    let mut root_node_count = 0;
    for (node_idx, node) in self.nodes.iter().enumerate() {
      if node.used {
        assert_ne!(node.agent_id, Self::INTERMEDIARY_AGENT_ID);

        if node_idx == ROOT_NODE_IDX {
          root_node_count += 1;
        } else {
          assert_ne!(
            node.agent_id, ROOT_AGENT_ID,
            "Non-root nodes must have a non-root agent id:\n{node:#?}"
          );
          assert_ne!(node.ports.len(), 0, "Non-root nodes must have at least one port:\n{node:#?}");
        }

        for port_idx in 0 .. node.ports.len() {
          let src = port(node_idx, port_idx);
          let dst = self[src];

          /* if cfg!(test) {
            eprintln!("{src} ~ {dst}");
          } */
          assert!(self[dst.node_idx].used, "\nUsed node linked to unused node {:?}:\n{self:#?}", (src, dst));

          assert_eq!(self[dst], src, "\nNon-bidirectional link {:?}:\n{self:#?}", (src, dst));
        }
        assert!(!self.free_nodes.contains(&node_idx), "\n{self:#?}");
      } else {
        contains_unused_nodes = true;
        // assert_eq!(node.ports, PortVec::default());
        assert!(self.free_nodes.contains(&node_idx), "\n{self:#?}");
      }
    }
    if !self.nodes.is_empty() {
      let node = &self[ROOT_NODE_IDX];
      assert!(node.used, "Root node must be used");
      assert_eq!(node.agent_id, ROOT_AGENT_ID);
      assert_eq!(root_node_count, 1, "There must be exactly one root node");
    }
    assert!(
      allow_unused_nodes || !contains_unused_nodes,
      "INet is not allowed to have unused nodes:\n{self:#?}"
    );
  }

  /// Add a `Connector` to the net, only called by `INet::add_connections`.
  /// If the connector is a port, `Err(port_name)` is returned so that it can be linked later.
  /// If the connector is an agent, it is added as a new node and its principal port is returned as `Ok(port)`.
  /// Connections to auxiliary ports are added to `deferred_port_links` so that they can be linked later.
  /// This function is only called by `INet::add_connections`
  fn add_connector<'a, 'b: 'a>(
    &mut self,
    connector: &'b Connector,
    deferred_port_links: &'a mut MaybeLinkedPorts<'b>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
    created_nodes: &mut NodeIndices,
  ) -> MaybeLinkedPort<'b> {
    match connector {
      Connector::Agent(agent) => {
        // Create agent node
        let Agent { agent, ports } = agent;
        let agent_id = agent_name_to_id[agent];
        let node_idx = self.new_node(agent_id, 1 + ports.len());

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
  /// When called by `RuleBook::apply_rewrite_rule`, `external_ports` contains the ports of the parent net
  /// that the rule's RHS sub-net is connected to, based on which INet ports the rule's LHS (active pair)
  /// aux port names map to, in that context of the local rewrite.
  /// Returns the indices of the created nodes.
  pub fn add_connections<'a>(
    &mut self,
    connections: &'a [Connection],
    external_ports: MaybeLinkedPorts<'a>,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
  ) -> NodeIndices {
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
      let lhs = self.add_connector(lhs, &mut deferred_port_links, agent_name_to_id, &mut created_nodes);
      let rhs = self.add_connector(rhs, &mut deferred_port_links, agent_name_to_id, &mut created_nodes);
      deferred_port_links.push([lhs, rhs]);
    }

    // At this point, `deferred_port_links` contains all pairs of ports that need to be linked

    // Link all pairs of ports that could not be linked yet
    while let Some([lhs, rhs]) = deferred_port_links.pop() {
      // eprintln!("deferred_port_links: {deferred_port_links:#?}, {lhs:?} ~ {rhs:?}");
      match (lhs, rhs) {
        (Ok(lhs), Ok(rhs)) => {
          // Both connectors are resolved to ports, thus ready to be linked
          self.link(lhs, rhs);
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

  /// Remove all unused nodes, called by `RuleBook::reduce_rule_rhs_subnets`
  pub fn remove_unused_nodes(&mut self) {
    self.free_nodes.sort_by_key(|&node_idx| Reverse(node_idx));
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

  // The rewrite mechanism assumes that all wires between aux ports of the active pair
  // and the rest of the net are unique. E.g. `A(a, a) ~ B` or `A(a) ~ B(a)` would be a problem.
  // Our workaround: If the active pair contains two references to the same wire,
  // we split the wire into two, by inserting a temporary intermediary node:
  // E.g. `A(a, a) ~ B` becomes `A(a, b) ~ B, a ~ TMP(b)`
  // E.g. `A(a) ~ B(a)` becomes `A(a) ~ B(b), a ~ TMP(b)`
  // This is done by adding an intermediary node with two ports, one of which is linked to each
  // of the two aux ports that were previously using the same wire (like a wire going through it).
  // Then the rewrite is performed as usual, and afterwards the two ports of the intermediary
  // node are linked together and the intermediary node is removed.
  const INTERMEDIARY_AGENT_ID: AgentId = usize::MAX;

  /// Rewrite active pair using rule book.
  /// Assumes that reuse buffers are empty.
  /// Returns `false` if active pair could not be rewritten because there was no matching rule
  /// Returns `true` when a rule matched and a rewrite happened, in that case
  /// `reuse.inet_new_active_pairs_created_by_rewrite` contains the new active pairs.
  fn rewrite_active_pair(
    &mut self,
    (a, b): ActiveNodePair,
    rule_book: &RuleBook,
    reuse: &mut ReuseableRewriteData,
  ) -> bool {
    debug_assert!(a < b, "Expected active pair to be ordered: {:?}", (a, b));
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
    let active_pair_candidate_nodes_whose_principal_port_points_into_subnet =
      &mut reuse.inet_active_pair_candidate_nodes;
    debug_assert_eq!(*active_pair_candidate_nodes_whose_principal_port_points_into_subnet, vec![]);
    active_pair_candidate_nodes_whose_principal_port_points_into_subnet.extend(
      self[a]
        .ports
        .iter()
        .skip(1)
        .chain(self[b].ports.iter().skip(1))
        .filter(|port| port.port_idx == 0)
        .map(|port| port.node_idx),
    );

    let intermediary_nodes = &mut reuse.inet_intermediary_nodes;
    for node_idx in [a, b] {
      // Skip principal port
      for port_idx in 1 .. self[node_idx].ports.len() {
        let src = port(node_idx, port_idx);
        let dst = self[src];
        if dst.node_idx == a || dst.node_idx == b {
          // Create intermediary node that will be removed after rewrite. It temporarily converts
          // the problematic self-link of the active pair into a link to another node,
          // which allows us to rewrite the active pair by assuming there are no self-links.
          // We link port 0 of TMP to src and port 1 of TMP to dst, to split the shared wire.
          let intermediary = self.new_node(Self::INTERMEDIARY_AGENT_ID, 2);
          let src = port(node_idx, port_idx);
          self.link(src, port(intermediary, 0));
          self.link(dst, port(intermediary, 1));
          intermediary_nodes.push(intermediary);
        }
      }
    }

    // Apply rewrite rule to active pair if there is a matching rule
    let active_pair_candidates = rule_book.apply_rewrite_rule(self, (a, b), &mut reuse.subnet);

    // Now that the rewrite is done (or no rewrite happened if there was no applicable rule),
    // we can remove the intermediary nodes and link their two wires together into one again.
    for &node_idx in &*intermediary_nodes {
      let node = &self[node_idx];
      self.link(node[0], node[1]);
      self.free_node(node_idx);
    }

    let rewrite_happened = if let Some(active_pair_candidates) = active_pair_candidates {
      // Remove the nodes of the active pair that was rewritten
      self.free_node(a);
      self.free_node(b);

      // Now we compute the new active pairs that came into existence by this rewrite

      let subnet = &reuse.subnet;
      let new_active_pairs = &mut reuse.inet_new_active_pairs_created_by_rewrite;
      debug_assert_eq!(*new_active_pairs, vec![]);

      // These are nodes whose principal port points through the subnet boundary, they could form
      // an active pair, depending on whether they connect to the other node's principal port.
      // Note: There are no duplicates in this chained iter, because these sets are disjoint.
      let active_pair_candidate_nodes =
        active_pair_candidate_nodes_whose_principal_port_points_into_subnet.iter().copied().chain(
          active_pair_candidates.nodes_whose_principal_port_points_outside_subnet.iter().map(|&node_idx| {
            // The node_idx is relative to the subnet, we need to map it to an index in `self`
            subnet.map_node_idx_to_outer_net(node_idx)
          }),
        );

      // Add active pairs between nodes of the inserted subnet and nodes that already existed in `self`.
      // Check which of the candidates actually form active pairs.
      // This can create duplicates, e.g.
      // if `active_pair_candidate_nodes_whose_principal_port_points_into_subnet` contains (1, 2) and
      // `nodes_whose_principal_port_points_outside_subnet` contains (2, 1), we dedup the sorted tuples below.
      new_active_pairs.extend(active_pair_candidate_nodes.filter_map(|node_idx| {
        debug_assert!(self[node_idx].used, "Node {node_idx} is not used: {:#?}", self[node_idx]);
        self.node_is_part_of_active_pair(node_idx).map(|dst_node_idx| {
          debug_assert!(
            self[dst_node_idx].used,
            "Node {dst_node_idx} is not used: {:#?}",
            self[dst_node_idx]
          );
          sort_tuple((node_idx, dst_node_idx))
        })
      }));

      // Each pair of node indices was sorted so that we can dedup them after sorting
      new_active_pairs.sort_unstable();
      new_active_pairs.dedup();

      // Add active pairs between nodes of the inserted subnet
      // These active pairs were already confirmed to exist between nodes of the inserted subnet.
      // These exist when a rule's RHS subnet could not be reduced within the max number of rewrites.
      // Note: This cannot add duplicates because `active_pairs_inside_subnet`
      // and `active_pair_candidate_nodes` are disjoint.
      if !active_pair_candidates.active_pairs_inside_subnet.is_empty() {
        new_active_pairs.extend(active_pair_candidates.active_pairs_inside_subnet.iter().map(
          |&(lhs_node_idx, rhs_node_idx)| {
            // The node indices are relative to the subnet, we need to map them to an index in `self`
            let (lhs_node_idx, rhs_node_idx) = (
              subnet.map_node_idx_to_outer_net(lhs_node_idx),
              subnet.map_node_idx_to_outer_net(rhs_node_idx),
            );
            debug_assert!(
              self[lhs_node_idx].used,
              "Node {lhs_node_idx} is not used: {:#?}",
              self[lhs_node_idx]
            );
            debug_assert!(
              self[rhs_node_idx].used,
              "Node {rhs_node_idx} is not used: {:#?}",
              self[rhs_node_idx]
            );
            debug_assert_eq!(
              self.node_is_part_of_active_pair(lhs_node_idx),
              Some(rhs_node_idx),
              "Expected active pair: {:?}\n{self:#?}",
              (lhs_node_idx, rhs_node_idx)
            );
            let node_indices = (lhs_node_idx, rhs_node_idx);
            debug_assert_eq!(
              node_indices,
              sort_tuple(node_indices),
              "Expected sorted tuple: {:?}",
              node_indices
            );
            node_indices
          },
        ));
        if cfg!(debug_assertions) {
          let len_before_dedup = new_active_pairs.len();
          new_active_pairs.sort_unstable();
          new_active_pairs.dedup();
          assert_eq!(
            len_before_dedup,
            new_active_pairs.len(),
            "`active_pair_candidate_nodes` and `active_pairs_inside_subnet` must be disjoint"
          );
        }
      }
      true
    } else {
      false
    };

    if cfg!(debug_assertions) {
      self.validate(true);
    }
    rewrite_happened
  }

  /// Inserts a rule's RHS sub-net into the net, called by `RuleBook::apply_rewrite_rule`.
  /// It works by:
  /// - Creating nodes in `self` for the `subnet` nodes, to get new node indices
  /// - Copying ports of `subnet` nodes to the new nodes, translating links using new node indices
  /// - Pass-through-linking the subnet root node's ports to the corresponding ports in `self`
  /// - Removing the subnet root node from `self`
  /// The aux ports of the two active pair nodes are mapped to the subnet's root node ports:
  /// `external_ports` maps subnet root node port indices to ports in the `self` net.
  /// External (subnet root node) port indices refer to auxiliary ports in the active pair of the rule LHS:
  /// E.g. if the rule LHS is `X(a, b) ~ Y(c, d)`, then `external_ports` contains the ports of `self`
  /// that map to `[a, b, c, d]` (in that order) in the context of the local rewrite.
  /// In other words, the ports are indexed left-to-right, after ordering both active pair agent IDs:
  /// So the external ports would be the same if the rule LHS was written as `Y(c, d) ~ X(a, b)`.
  /// (Assuming X's AgentId < Y's AgentId in this example.)
  /// This function assumes that `reuse.subnet_node_idx_to_main_node_idx` is empty
  /// and that `reuse.rule_book_external_ports` contains the external ports of the subnet.
  /// When this function returns, `reuse.inet_subnet_node_idx_to_main_node_idx` contains the node indices
  /// of the inserted subnet nodes, to enable `rewrite_active_pair` to determine new active pairs.
  /// (`reuse.inet_subnet_node_idx_to_main_node_idx[0]` will be the index of the removed subnet root node.)
  pub fn insert_rule_rhs_subnet(&mut self, subnet: &INet, reuse: &mut ReuseableSubnetData) {
    let external_ports = &reuse.rule_book_external_ports;
    let subnet_node_idx_to_main_node_idx = &mut reuse.inet_subnet_node_idx_to_main_node_idx;
    debug_assert_eq!(*subnet_node_idx_to_main_node_idx, vec![]);

    // Copy fields except `ports` from `subnet` node to `self` node and store new node indices
    subnet_node_idx_to_main_node_idx.extend(subnet.nodes.iter().map(|node| {
      debug_assert!(node.used); // Rule RHS subnet must have all unused nodes removed

      // Create a new node in `self` for each node in `subnet` and return its index
      self.new_node(node.agent_id, node.ports.len())
    }));

    // Copy mapped ports using new node indices
    for (subnet_node, self_node_idx) in subnet.nodes.iter().zip(&*subnet_node_idx_to_main_node_idx) {
      let self_node = &mut self[*self_node_idx];
      for (subnet_port, self_port) in subnet_node.ports.iter().zip(self_node.ports.iter_mut()) {
        let NodePort { node_idx: subnet_node_idx, port_idx } = *subnet_port;
        // Copy `port_idx` unchanged but map `node_idx` from `subnet` to `self`
        *self_port = NodePort {
          node_idx: unsafe { *subnet_node_idx_to_main_node_idx.get_unchecked(subnet_node_idx) },
          port_idx,
        };
      }
    }

    // Pass-through link subnet root node's ports and then remove it, like temporary nodes in `rewrite_active_pair`
    // Remove subnet root node from list of created nodes
    let subnet_root_node_idx_in_self = reuse.map_node_idx_to_outer_net(ROOT_NODE_IDX);
    let subnet_root_node: &Node = &self[subnet_root_node_idx_in_self];
    debug_assert_eq!(subnet_root_node.agent_id, ROOT_AGENT_ID);
    debug_assert_eq!(subnet_root_node.ports.len(), external_ports.len());
    for (port_idx, &ext_port) in external_ports.iter().enumerate() {
      // Note: `target_port` doesn't necessary point to a former `subnet` node,
      // if subnet root node contains self-links. See `test_subnet_root_node_self_links`
      let target_port = self[port(subnet_root_node_idx_in_self, port_idx)];
      self.link(ext_port, target_port);
    }

    // Remove subnet root node, now that we pass-through-linked all its ports to external ports
    self.free_node(subnet_root_node_idx_in_self);
  }

  /// Determines if a given node is part of an active pair and returns the other node in the pair
  #[inline(always)]
  fn node_is_part_of_active_pair(&self, node_idx: NodeIdx) -> Option<NodeIdx> {
    // The only node that can have no ports is the subnet root node, e.g. in `rule Era ~ Zero =`
    let node = &self[node_idx];
    if node.agent_id != ROOT_AGENT_ID {
      let dst = self[port(node_idx, 0)];
      // After validation, we can assume that dst.node_idx == node_idx
      (dst.port_idx == 0).then_some(dst.node_idx)
    } else {
      // Never consider the root node to be part of an active pair
      None
    }
  }

  /// Determine active pairs that can potentially be rewritten if there is a matching rule
  pub fn scan_active_pairs(&self) -> ActiveNodePairs {
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

  /// Returns the active pairs that can come into existence after inserting a subnet,
  /// pass-through-linking through its root node and removing it.
  /// In other words, returns indices of nodes whose principal port points to a root node port.
  fn nodes_whose_principal_port_points_outside_subnet(&self) -> NodeIndices {
    let mut nodes_whose_principal_port_points_outside_subnet = vec![];
    for &target in &self[ROOT_NODE_IDX].ports {
      if target.node_idx != ROOT_NODE_IDX && target.port_idx == 0 {
        nodes_whose_principal_port_points_outside_subnet.push(target.node_idx);
      }
    }
    nodes_whose_principal_port_points_outside_subnet
  }

  /// Returns the active pairs that can come into existence after inserting a subnet:
  /// - Field `active_pairs_inside_subnet` contains the active pairs that already exist in the subnet,
  ///   which will definitely exist after inserting the subnet (and for which a rule exists)
  /// - Field `nodes_whose_principal_port_points_outside_subnet` contains the indices of nodes
  ///   whose principal port points to a root node port, which can form active pairs with other nodes
  ///   whose principal port points to aux ports of an active pair that gets rewritten.
  ///   So these are not definitive active pair nodes, but they could form active pairs after a rewrite.
  pub fn active_pair_candidates_after_inserting_subnet(&self, rule_book: &RuleBook) -> ActivePairCandidates {
    let mut active_pairs_inside_subnet = self.scan_active_pairs();
    let mut nodes_whose_principal_port_points_outside_subnet =
      self.nodes_whose_principal_port_points_outside_subnet();

    if cfg!(debug_assertions) {
      let mut set = hashbrown::HashSet::new();
      for node_idx in active_pairs_inside_subnet
        .iter()
        .flat_map(|(lhs, rhs)| [lhs, rhs])
        .chain(&nodes_whose_principal_port_points_outside_subnet)
      {
        assert!(set.insert(node_idx), "Duplicate node in active_pairs: {set:#?}");
      }
    }

    active_pairs_inside_subnet.retain_mut(|active_pair| {
      if let Some(ordered_active_pair) = rule_book.rule_exists_for_active_pair(self, *active_pair) {
        *active_pair = ordered_active_pair;
        true
      } else {
        false
      }
    });

    nodes_whose_principal_port_points_outside_subnet
      .retain(|&node_idx| rule_book.rule_exists_for_agent_id(self[node_idx].agent_id));

    ActivePairCandidates { active_pairs_inside_subnet, nodes_whose_principal_port_points_outside_subnet }
  }

  /// Perform one reduction step:
  /// Scan for active pairs and rewrite the first one for which a rule exists.
  /// Returns `true` if a rewrite happened, false otherwise (either because
  /// there are no active pairs or because no rule applies to any of them).
  /// Not efficient because of the rescan for active pairs, but useful for debugging.
  pub fn scan_active_pairs_and_reduce_step(&mut self, rule_book: &RuleBook) -> bool {
    let mut reuse = ReuseableRewriteData::default();
    for active_pair in self.scan_active_pairs() {
      if self.rewrite_active_pair(active_pair, rule_book, &mut reuse) {
        return true;
      }
    }
    false
  }

  /// Reduce net until no more reductions are possible, without rescanning for active pairs after each rewrite.
  /// Only scans the net for active pairs in the beginning. After each rewrite, new active pairs are found by
  /// checking the nodes involved in and adjacent to the rewritten sub-net.
  pub fn reduce(&mut self, rule_book: &RuleBook) -> usize {
    let reduction_count = self.reduce_in_max_steps::<{ usize::MAX }>(rule_book);
    unsafe { reduction_count.unwrap_unchecked() }
  }

  /// Like `reduce` but performs maximum `max_reductions` reduction steps.
  /// Returns the number of reductions actually performed, None if limit was reached.
  pub fn reduce_in_max_steps<const MAX_REDUCTIONS: usize>(&mut self, rule_book: &RuleBook) -> Option<usize> {
    let mut reuse = ReuseableRewriteData::default();
    let mut reduction_count = 0;
    let mut active_pairs = VecDeque::from(self.scan_active_pairs());
    // `active_pairs` is a queue, we process active pairs in the order they were found:
    // Pop from the front while the queue is not empty, and push new active pairs to the back.
    while let Some(active_pair) = active_pairs.pop_front() {
      if self.rewrite_active_pair(active_pair, rule_book, &mut reuse) {
        active_pairs.extend(&reuse.inet_new_active_pairs_created_by_rewrite);
        reduction_count += 1;
        if reduction_count > MAX_REDUCTIONS {
          return None;
        }
        reuse.clear_when_rule_matched();
      } else {
        reuse.clear_when_no_rule_matched();
      }
    }
    Some(reduction_count)
  }

  /// Read back reduced net into textual form raw (unchanged)
  pub fn read_back_raw(
    &self,
    agent_id_to_name: &HashMap<AgentId, AgentName>,
    root_port_names: &[PortName],
  ) -> Vec<Connection> {
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
            agent_id_to_name: &HashMap<AgentId, AgentName>,
            node_idx_to_agent_port_names: &mut HashMap<NodeIdx, Vec<PortName>>,
            root_port_names: &[PortName],
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

            if node.agent_id == ROOT_AGENT_ID {
              // Connected to a port of the root node
              Connector::Port(root_port_names[node_port.port_idx].clone())
            } else {
              if node_port.port_idx == 0 {
                // Connected to a principal port, either `x ~ root` or `x ~ Agent(...)`
                if node_port.node_idx == ROOT_NODE_IDX {
                  Connector::Port(ROOT_PORT_NAME.to_string())
                } else {
                  Connector::Agent(Agent {
                    agent: agent_id_to_name[&node.agent_id].clone(),
                    ports: agent_aux_port_names.clone(),
                  })
                }
              } else {
                // Connected to auxiliary port of agent: `x ~ aux, Agent(..., aux, ...) ~ y`
                Connector::Port(agent_aux_port_names[node_port.port_idx - 1].clone())
              }
            }
          }

          // For each link src ~ dst, we create a `Connection`
          let src = build_connector_from_port(
            self,
            agent_id_to_name,
            &mut nodes_aux_port_names,
            root_port_names,
            &mut new_port_name,
            src,
          );
          let dst = build_connector_from_port(
            self,
            agent_id_to_name,
            &mut nodes_aux_port_names,
            root_port_names,
            &mut new_port_name,
            dst,
          );
          connections.push(Connection::new(src, dst));
        }
      }
    }
    connections
  }

  /// Read back reduced net into readable (nested) textual form
  pub fn read_back(
    &self,
    agent_id_to_name: &HashMap<AgentId, AgentName>,
    root_port_names: &[PortName],
  ) -> String {
    let connections = self.read_back_raw(agent_id_to_name, root_port_names);
    let connections = unflatten_connections(connections, root_port_names);
    fmt_nested_connections(&connections)
  }
}

/// Reuseable memory between rewrites, to avoid unnecessary allocations
#[derive(Default)]
struct ReuseableRewriteData {
  inet_active_pair_candidate_nodes: NodeIndices,
  inet_intermediary_nodes: NodeIndices,
  subnet: ReuseableSubnetData,
  inet_new_active_pairs_created_by_rewrite: ActiveNodePairs,
}

/// Separate sub-borrowable struct to pass to `RuleBook::apply_rewrite_rule`
#[derive(Default)]
pub struct ReuseableSubnetData {
  pub rule_book_external_ports: Vec<NodePort>,
  inet_subnet_node_idx_to_main_node_idx: NodeIndices,
}

impl ReuseableSubnetData {
  /// Map a node index in the subnet to a node index in the outer net.
  /// Used after inserting a rule's RHS subnet during rewrite,
  /// to determine node indices of new active pairs.
  fn map_node_idx_to_outer_net(&self, node_idx: NodeIdx) -> NodeIdx {
    unsafe { *self.inet_subnet_node_idx_to_main_node_idx.get_unchecked(node_idx) }
  }
}

impl ReuseableRewriteData {
  /// When no rule matched, only the first two fields were populated
  fn clear_when_no_rule_matched(&mut self) {
    self.inet_active_pair_candidate_nodes.clear();
    self.inet_intermediary_nodes.clear();
  }

  /// When a rule matched, all fields were populated
  fn clear_when_rule_matched(&mut self) {
    self.inet_active_pair_candidate_nodes.clear();
    self.inet_intermediary_nodes.clear();
    self.subnet.rule_book_external_ports.clear();
    self.subnet.inet_subnet_node_idx_to_main_node_idx.clear();
    self.inet_new_active_pairs_created_by_rewrite.clear();
  }
}

/// Represents a connection between two ports for deferred linking
/// Either Ok(port) or Err(port_name) which needs to be looked up later
type MaybeLinkedPort<'a> = Result<NodePort, PortNameRef<'a>>;
type MaybeLinkedPorts<'a> = Vec<[MaybeLinkedPort<'a>; 2]>;

/// Represents active pair of nodes in a net, meaning that their principal ports are connected.
/// Not necessarily that a rewrite rule exists for this pair.
pub type ActiveNodePair = (NodeIdx, NodeIdx);

pub type ActiveNodePairs = Vec<ActiveNodePair>;

pub type NodeIndices = Vec<NodeIdx>;

/// When building the rule book, we keep track of which subnet nodes can form active pairs after a rewrite
#[derive(Clone, Debug, PartialEq, Default)]
pub struct ActivePairCandidates {
  /// Definitive active pairs inside subnet whose principal ports are connected
  pub active_pairs_inside_subnet: ActiveNodePairs,

  /// Nodes inside subnet whose principal port points to a root node port such that
  /// it can form an active pair after a rewrite
  pub nodes_whose_principal_port_points_outside_subnet: NodeIndices,
}

// Indexing utils to allow indexing an INet with a NodeIdx and NodePort

impl Index<NodeIdx> for INet {
  type Output = Node;

  fn index(&self, idx: NodeIdx) -> &Self::Output {
    if cfg!(debug_assertions) { &self.nodes[idx] } else { unsafe { self.nodes.get_unchecked(idx) } }
  }
}

impl IndexMut<NodeIdx> for INet {
  fn index_mut(&mut self, idx: NodeIdx) -> &mut Self::Output {
    if cfg!(debug_assertions) { &mut self.nodes[idx] } else { unsafe { self.nodes.get_unchecked_mut(idx) } }
  }
}

impl Index<PortIdx> for Node {
  type Output = NodePort;

  fn index(&self, idx: PortIdx) -> &Self::Output {
    if cfg!(debug_assertions) { &self.ports[idx] } else { unsafe { self.ports.get_unchecked(idx) } }
  }
}

impl IndexMut<PortIdx> for Node {
  fn index_mut(&mut self, idx: PortIdx) -> &mut Self::Output {
    if cfg!(debug_assertions) { &mut self.ports[idx] } else { unsafe { self.ports.get_unchecked_mut(idx) } }
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
