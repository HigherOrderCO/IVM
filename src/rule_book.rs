use crate::{
  error::ProgramErrors,
  inet::{INet, NodeIdx, NodePort, ReuseableSubnetData},
  parser::ast::{ActivePair, AgentName, PortName, Rule, ROOT_NODE_IDX},
  rule_map::RuleMap,
  util::sort_tuples_by_fst,
};
use chumsky::prelude::Rich;
use hashbrown::HashMap;
use itertools::Itertools;

/// Agent IDs start from 1, 0 is reserved for the root node's agent_id
pub type AgentId = usize;

/// Agent ID 0 is reserved for the root
pub const ROOT_AGENT_ID: AgentId = 0;

/// Ordered pair of AgentIds represents active pair
/// So that we only have to store one mapping to cover A ~ B and B ~ A
pub type RuleLhs = (AgentId, AgentId);

/// RHS of a rule, contains the rule's RHS sub-net
#[derive(Clone)]
pub struct RuleRhs {
  /// Active pair of the rule, only used for logging
  active_pair: ActivePair,

  /// Names of the rule's RHS sub-net root node's ports == aux port names of the
  /// rule's active pair after ordering them by agent id. Used for read back.
  root_port_names: Vec<PortName>,

  /// The rule's RHS sub-net, with the root node's ports representing links to the rule's
  /// active pair aux ports. E.g. in `rule Eq(ret, a) ~ Zero = IsZero(ret) ~ a`
  /// (assuming the agent id of `Eq` is less than the agent id of `IsZero`)
  /// the root node has 2 ports since the total number of active pair aux ports is 2.
  /// `root_port_names` is `["ret", "a"]`, and the sub-net is `IsZero((0, 0)) ~ (0, 1)`.
  /// The sub-net's root node is removed during rule application after its ports have been
  /// pass-through-linked to bridge the boundary between the main net and the sub-net.
  subnet: INet,
}

/// The rule book is a mapping from active pair to a rule's RHS connections.
/// E.g. if we have: rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b
/// then the rule book maps (Add, Succ) to [ret ~ Succ(cnt), Add(cnt, a) ~ b]
/// which is a sub-net in which the ports that are named in the active pair
/// appear as external links (i.e. not connected to any other ports in the sub-net).
/// During rule application, the rule RHS sub-net is constructed and external links
/// are connected to the corresponding ports in the active pair of the net.
/// Currently the ports are linked by name, but this could be changed to use port ids.
#[derive(Clone)]
pub struct RuleBook {
  rules: RuleMap,
}

impl RuleBook {
  pub fn new(_agent_count: usize) -> Self {
    Self { rules: RuleMap::new() }
    // Self { rules: RuleMap::new(agent_count) }
  }

  /// Insert into rule book and check for duplicate rules
  pub fn insert_rule(
    &mut self,
    rule: &Rule,
    _rule_src: &str,
    agent_name_to_id: &HashMap<AgentName, AgentId>,
    errors: &mut ProgramErrors,
  ) {
    let Rule { lhs: active_pair, rhs: rule_rhs, span } = rule;

    let ActivePair { lhs: lhs_agent, rhs: rhs_agent } = active_pair;
    let lhs_id = agent_name_to_id[&lhs_agent.agent];
    let rhs_id = agent_name_to_id[&rhs_agent.agent];

    // Construct RuleLhs, ordered pair of AgentIDs. Order agents along with AgentIDs
    let ((lhs_id, lhs_agent), (rhs_id, rhs_agent)) =
      sort_tuples_by_fst(((lhs_id, lhs_agent), (rhs_id, rhs_agent)));
    let key = (lhs_id, rhs_id); // Ordered pair

    let value = RuleRhs {
      active_pair: active_pair.clone(),
      root_port_names: [lhs_agent, rhs_agent]
        .into_iter()
        .flat_map(|agent| &agent.ports)
        .map(|port| port.to_owned())
        .collect_vec(),
      subnet: {
        let external_ports = [lhs_agent, rhs_agent]
          .into_iter()
          .flat_map(|agent| &agent.ports)
          .enumerate()
          .map(|(external_port_idx, port_name)| {
            [Err(port_name.as_str()), Ok(NodePort { node_idx: ROOT_NODE_IDX, port_idx: external_port_idx })]
          })
          .collect_vec();

        // This inet represents the rule's RHS sub-net
        let mut subnet = INet::default();

        // Create root node with as many ports as there are external ports in the rule's RHS sub-net
        // (== the number of aux ports in the active pair)
        // Set each port to point to itself.
        let root_node_idx = subnet.new_node(ROOT_AGENT_ID, external_ports.len());
        debug_assert_eq!(root_node_idx, ROOT_NODE_IDX);
        subnet[root_node_idx].ports = (0 .. external_ports.len())
          .map(|port_idx| NodePort { node_idx: ROOT_NODE_IDX, port_idx })
          .collect_vec()
          .into();

        let _created_nodes = subnet.add_connections(rule_rhs, external_ports, agent_name_to_id);
        if cfg!(debug_assertions) {
          subnet.validate(false);
        }
        subnet
      },
    };
    if let Some(_) = self.rules.insert(key, value) {
      errors.push(Rich::custom(*span, format!("Duplicate rule for active pair `{active_pair}`")));
    }
  }

  /// Pre-reduce the rule book's RHS sub-nets as an optimization step before running the program.
  /// This must be done after all rules have been inserted.
  pub fn reduce_rule_rhs_subnets(&mut self, agent_id_to_name: &HashMap<AgentId, AgentName>) {
    /// Maximum number of reduction steps to perform on each rule's RHS sub-net.
    /// If it cannot be reduced in this many steps, the original sub-net is kept.
    /// Because rules' RHS sub-nets are not guaranteed to terminate.
    const RULE_BOOK_MAX_PRE_REDUCTION_STEPS: usize = 100;

    let reduced_rules = self
      .rules
      .iter()
      .filter_map(|(key, RuleRhs { active_pair, root_port_names, subnet })| {
        let mut subnet: INet = subnet.clone();
        subnet.reduce_in_max_reductions::<RULE_BOOK_MAX_PRE_REDUCTION_STEPS>(self).and_then(
          |reduction_count| {
            (reduction_count > 0).then(|| {
              subnet.remove_unused_nodes();
              if cfg!(debug_assertions) {
                subnet.validate(false);
              }
              (*key, RuleRhs {
                active_pair: active_pair.clone(),
                root_port_names: root_port_names.clone(),
                subnet,
              })
            })
          },
        )
      })
      .collect_vec();

    if cfg!(test) {
      // Print reduced rule subnets
      let mut reduced_rules = reduced_rules
        .iter()
        .map(|(_, RuleRhs { active_pair, root_port_names, subnet })| {
          format!("rule {active_pair} = {}", subnet.read_back(agent_id_to_name, root_port_names))
        })
        .collect_vec();
      reduced_rules.sort();
      if !reduced_rules.is_empty() {
        println!("Reduced rules: {{\n{}\n}}", reduced_rules.join("\n"));
      }
    }

    // Overwrite rules with reduced rules
    self.rules.extend(reduced_rules);
  }

  /// Apply rule to active pair if such a rule exists.
  /// Assumes that `reuse.rule_book_external_ports` is empty.
  /// Returns `true` if a rule was applied, in that case `reuse.inet_subnet_node_idx_to_self_node_idx`
  /// contains the node indices of the inserted subnet nodes.
  pub fn apply_rewrite_rule(
    &self,
    net: &mut INet,
    active_pair: (NodeIdx, NodeIdx),
    reuse: &mut ReuseableSubnetData,
  ) -> bool {
    let (node_idx_lhs, node_idx_rhs) = active_pair;
    let (lhs_node, rhs_node) = (&net[node_idx_lhs], &net[node_idx_rhs]);
    let (lhs_id, rhs_id) = (lhs_node.agent_id, rhs_node.agent_id);

    // Construct RuleLhs, ordered pair of AgentIDs. Order nodes along with AgentIDs
    let ((lhs_id, lhs_node), (rhs_id, rhs_node)) =
      sort_tuples_by_fst(((lhs_id, lhs_node), (rhs_id, rhs_node)));
    let key = (lhs_id, rhs_id); // Ordered pair

    if let Some(RuleRhs { active_pair: _, root_port_names: _, subnet }) = self.rules.get(&key) {
      // Construct external ports for the rule's RHS sub-net
      reuse.rule_book_external_ports.extend([lhs_node, rhs_node].into_iter().flat_map(|node| {
        node.ports.iter().skip(1).copied() // Skip principal port
      }));
      net.insert_rule_rhs_subnet(subnet, reuse);
      true
    } else {
      false
    }
  }
}
