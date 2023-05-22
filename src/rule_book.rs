use crate::{
  error::ProgramErrors,
  inet::{CreatedNodes, INet, NodeIdx},
  parser::ast::{ActivePair, AgentName, Connection, PortName, Rule},
  util::sort_tuples_by_fst,
};
use chumsky::prelude::Rich;
use derive_new::new;
use hashbrown::HashMap;
use itertools::Itertools;

/// Agent IDs start from 1, 0 is reserved for the root node's agent_id
pub type AgentId = usize;

/// Agent ID 0 is reserved for the root
pub const ROOT_AGENT_ID: AgentId = 0;

/// Ordered pair of AgentIds represents active pair
/// So that we only have to store one mapping to cover A ~ B and B ~ A
type RuleLhs = (AgentId, AgentId);

#[derive(Clone)]
struct RuleRhs {
  rule_src: String, // Rule's source code, used for showing in error messages
  port_idx_to_name: [Vec<PortName>; 2],
  connections: Vec<Connection>,
}

/**
The rule book is a mapping from active pair to a rule's RHS connections.
E.g. if we have: rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b
then the rule book maps (Add, Succ) to [ret ~ Succ(cnt), Add(cnt, a) ~ b]
which is a sub-net in which the ports that are named in the active pair
appear as external links (i.e. not connected to any other ports in the sub-net).
During rule application, the rule RHS sub-net is constructed and external links
are connected to the corresponding ports in the active pair of the net.
Currently the ports are linked by name, but this could be changed to use port ids.
*/
#[derive(new, Clone)]
pub struct RuleBook {
  pub agent_name_to_id: HashMap<AgentName, AgentId>,
  #[new(default)]
  rules: HashMap<RuleLhs, RuleRhs>,
}

impl RuleBook {
  /// Insert into rule book and check for duplicate rules
  pub fn add_rule(&mut self, rule: &Rule, rule_src: &str, errors: &mut ProgramErrors) {
    let Rule { lhs: active_pair, rhs: rule_rhs, span } = rule;

    let ActivePair { lhs: lhs_agent, rhs: rhs_agent } = active_pair;
    let lhs_id = self.agent_name_to_id[&lhs_agent.agent];
    let rhs_id = self.agent_name_to_id[&rhs_agent.agent];

    // Construct RuleLhs, ordered pair of AgentIDs. Order agents along with AgentIDs
    let ((lhs_id, lhs_agent), (rhs_id, rhs_agent)) =
      sort_tuples_by_fst(((lhs_id, lhs_agent), (rhs_id, rhs_agent)));
    let key = (lhs_id, rhs_id); // Ordered pair

    let value = RuleRhs {
      rule_src: rule_src.to_owned(),
      port_idx_to_name: [
        lhs_agent.ports.iter().map(|port_name| port_name.to_owned()).collect_vec(),
        rhs_agent.ports.iter().map(|port_name| port_name.to_owned()).collect_vec(),
      ],
      connections: rule_rhs.clone(),
    };
    if let Some(_) = self.rules.insert(key, value) {
      errors.push(Rich::custom(*span, format!("Duplicate rule for active pair `{active_pair}`")));
    }
  }

  /// Apply rule to active pair if such a rule exists
  /// Returns indices of created nodes if a rule was applied, None otherwise
  pub fn apply(&self, net: &mut INet, active_pair: (NodeIdx, NodeIdx)) -> Option<CreatedNodes> {
    let (node_idx_lhs, node_idx_rhs) = active_pair;
    let (lhs_node, rhs_node) = (&net[node_idx_lhs], &net[node_idx_rhs]);
    let (lhs_id, rhs_id) = (lhs_node.agent_id, rhs_node.agent_id);

    // Construct RuleLhs, ordered pair of AgentIDs. Order nodes along with AgentIDs
    let ((lhs_id, lhs_node), (rhs_id, rhs_node)) =
      sort_tuples_by_fst(((lhs_id, lhs_node), (rhs_id, rhs_node)));
    let key = (lhs_id, rhs_id); // Ordered pair

    if let Some(RuleRhs { rule_src, port_idx_to_name, connections }) = self.rules.get(&key) {
      // Build `external_links` (pairs of port name and NodePort)
      // based on all auxiliary ports in the active pair, e.g. if the rule LHS
      // is Add(ret, a) ~ Succ(b), the ports {ret, a, b} are external links, then
      // `INet::add_connections` looks up ports when adding the connections of the RHS sub-net
      let external_links = [lhs_node, rhs_node]
        .into_iter()
        .zip(port_idx_to_name)
        .flat_map(|(node, port_idx_to_name)| {
          debug_assert_eq!(
            node.ports.len(),
            port_idx_to_name.len() + 1,
            "\n{net:#?}\n{rule_src}\n{node:?}, {port_idx_to_name:?}"
          );

          // Skip principal port, only auxiliary ports have names
          node
            .ports
            .iter()
            .skip(1)
            .zip(port_idx_to_name)
            .map(|(&node_port, port_name)| [Err(port_name.as_str()), Ok(node_port)])
        })
        .collect();
      Some(net.add_connections(connections, external_links, &self.agent_name_to_id))
    } else {
      None
    }
  }
}
