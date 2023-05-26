use crate::{
  error::ProgramErrors,
  inet::{ActiveNodePair, ActivePairCandidates, INet, NodePort, ReuseableSubnetData},
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
  pub(crate) subnet: INet,

  pub(crate) active_pair_candidates_after_inserting_subnet: ActivePairCandidates,
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
  pub fn new(agent_count: usize) -> Self {
    // Self { rules: RuleMap::new() }
    Self { rules: RuleMap::new(agent_count) }
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

    let (root_port_names, root_node_ports): (Vec<_>, Vec<_>) = [lhs_agent, rhs_agent]
      .into_iter()
      .flat_map(|agent| &agent.ports)
      .enumerate()
      .map(|(external_port_idx, port_name)| {
        (port_name.to_owned(), NodePort { node_idx: ROOT_NODE_IDX, port_idx: external_port_idx })
      })
      .unzip();

    let subnet = {
      let external_ports = root_port_names
        .iter()
        .zip(&root_node_ports)
        .map(|(port_name, node_port)| [Err(port_name.as_str()), Ok(*node_port)])
        .collect_vec();

      // This inet represents the rule's RHS sub-net
      let mut subnet = INet::default();

      // Create root node with as many ports as there are external ports in the rule's RHS sub-net
      // (== the number of aux ports in the active pair)
      // Set each port to point to itself.
      let root_node_idx = subnet.new_node(ROOT_AGENT_ID, external_ports.len());
      debug_assert_eq!(root_node_idx, ROOT_NODE_IDX);
      subnet[root_node_idx].ports = root_node_ports.into();

      let _created_nodes = subnet.add_connections(rule_rhs, external_ports, agent_name_to_id);
      if cfg!(debug_assertions) {
        subnet.validate(false);
      }
      subnet
    };

    // let active_pair_candidates_after_inserting_subnet =
    //   subnet.active_pair_candidates_after_inserting_subnet(self);

    let active_pair_candidates_after_inserting_subnet = ActivePairCandidates::default();

    let value = RuleRhs {
      active_pair: active_pair.clone(),
      root_port_names,
      subnet,
      active_pair_candidates_after_inserting_subnet,
    };
    if self.rules.insert(key, value).is_some() {
      errors.push(Rich::custom(*span, format!("Duplicate rule for active pair `{active_pair}`")));
    }
  }

  /// Finalize the rule book after all rules have been inserted. Must be called before doing rewrites.
  /// Precompute and store the active pair candidates for each rule's RHS subnet.
  /// Optionally optimize the rule book by reducing the RHS sub-nets of each rule.
  pub fn finalize(&mut self, agent_id_to_name: &HashMap<AgentId, AgentName>, reduce_rule_rhs_subnets: bool) {
    self.precompute_active_pair_candidates();

    if reduce_rule_rhs_subnets {
      self.reduce_rule_rhs_subnets(agent_id_to_name);
    }
  }

  /// Precompute and store the active pair candidates for each rule's RHS subnet.
  fn precompute_active_pair_candidates(&mut self) {
    self.rules = RuleMap::from_iter(
      self.rules.agent_count,
      self.rules.clone().into_iter().map(|(lhs, mut rhs)| {
        rhs.active_pair_candidates_after_inserting_subnet =
          rhs.subnet.active_pair_candidates_after_inserting_subnet(self);
        (lhs, rhs)
      }),
    );
  }

  /// Pre-reduce the rule book's RHS sub-nets as an optimization step before running the program.
  /// This must be done after all rules have been inserted.
  fn reduce_rule_rhs_subnets(&mut self, _agent_id_to_name: &HashMap<AgentId, AgentName>) {
    /// Maximum number of reduction steps to perform on each rule's RHS sub-net.
    /// If it cannot be reduced in this many steps, the original sub-net is kept.
    /// Because rules' RHS sub-nets are not guaranteed to terminate.
    const RULE_BOOK_MAX_PRE_REDUCTION_STEPS: usize = 100;

    let reduced_rules = self
      .rules
      .iter()
      .filter_map(
        |(
          key,
          RuleRhs { active_pair, root_port_names, subnet, active_pair_candidates_after_inserting_subnet },
        )| {
          // We can reduce if there are active pairs in the rule's RHS sub-net.
          // It doesn't guarantee that the reduction terminates though.
          let can_reduce =
            !active_pair_candidates_after_inserting_subnet.active_pairs_inside_subnet.is_empty();
          if can_reduce {
            let mut subnet: INet = subnet.clone();
            subnet.reduce_in_max_steps::<RULE_BOOK_MAX_PRE_REDUCTION_STEPS>(self).and_then(
              |reduction_count| {
                (reduction_count > 0).then(|| {
                  subnet.remove_unused_nodes();
                  if cfg!(debug_assertions) {
                    subnet.validate(false);
                  }

                  let active_pair_candidates_after_inserting_subnet =
                    subnet.active_pair_candidates_after_inserting_subnet(self);
                  debug_assert_eq!(
                    active_pair_candidates_after_inserting_subnet.active_pairs_inside_subnet,
                    vec![],
                    "Subnet must not have any active pairs after being reduced"
                  );

                  (key, RuleRhs {
                    active_pair: active_pair.clone(),
                    root_port_names: root_port_names.clone(),
                    subnet,
                    active_pair_candidates_after_inserting_subnet,
                  })
                })
              },
            )
          } else {
            None
          }
        },
      )
      .collect_vec();

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
    active_pair: ActiveNodePair,
    reuse: &mut ReuseableSubnetData,
  ) -> Option<&ActivePairCandidates> {
    let (node_idx_lhs, node_idx_rhs) = active_pair;
    let (lhs_node, rhs_node) = (&net[node_idx_lhs], &net[node_idx_rhs]);
    let (lhs_id, rhs_id) = (lhs_node.agent_id, rhs_node.agent_id);

    // Construct RuleLhs, ordered pair of AgentIDs. Order nodes along with AgentIDs
    let ((lhs_id, lhs_node), (rhs_id, rhs_node)) =
      sort_tuples_by_fst(((lhs_id, lhs_node), (rhs_id, rhs_node)));
    let key = (lhs_id, rhs_id); // Ordered pair

    if let Some(&RuleRhs {
      active_pair: _,
      root_port_names: _,
      ref subnet,
      ref active_pair_candidates_after_inserting_subnet,
    }) = self.rules.get(&key)
    {
      let external_ports = &mut reuse.rule_book_external_ports;
      debug_assert_eq!(*external_ports, vec![]);

      // Construct external ports for the rule's RHS sub-net:
      // The aux ports of the two active pair nodes are mapped to the subnet's root node ports
      external_ports.extend([lhs_node, rhs_node].into_iter().flat_map(|node| {
        node.ports.iter().skip(1).copied() // Skip principal port
      }));

      net.insert_rule_rhs_subnet(subnet, reuse);
      Some(active_pair_candidates_after_inserting_subnet)
    } else {
      None
    }
  }

  /// Checks if a rule exists for the given active pair, returns the node indices ordered by agent IDs
  pub fn rule_exists_for_active_pair(
    &self,
    net: &INet,
    active_pair: ActiveNodePair,
  ) -> Option<ActiveNodePair> {
    let (node_idx_lhs, node_idx_rhs) = active_pair;
    let (lhs_node, rhs_node) = (&net[node_idx_lhs], &net[node_idx_rhs]);
    let (lhs_id, rhs_id) = (lhs_node.agent_id, rhs_node.agent_id);

    // Order node indices along with AgentIDs
    let ((lhs_id, node_idx_lhs), (rhs_id, node_idx_rhs)) =
      sort_tuples_by_fst(((lhs_id, node_idx_lhs), (rhs_id, node_idx_rhs)));
    let key = (lhs_id, rhs_id); // Ordered pair

    self.rules.contains_key(&key).then_some((node_idx_lhs, node_idx_rhs))
  }

  /// Returns `true` if a rule exists for the given agent ID on either side of the active pair
  pub fn rule_exists_for_agent_id(&self, agent_id: AgentId) -> bool {
    self.rules.keys().flat_map(|(lhs_id, rhs_id)| [lhs_id, rhs_id]).any(|id| id == agent_id)
  }

  #[cfg(test)]
  pub(crate) fn get_rule_for_agents(&self, agent_ids: RuleLhs) -> Option<&RuleRhs> {
    use crate::util::sort_tuple;

    self.rules.get(&sort_tuple(agent_ids))
  }
}
