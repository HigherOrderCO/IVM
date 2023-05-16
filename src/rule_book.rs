use crate::{
  inet::{INet, NodeIdx},
  parser::ast::{ActivePair, AgentName, Connection, PortName, Rule},
  Error,
};
use derive_new::new;
use hashbrown::HashMap;
use itertools::Itertools;

/// Agent IDs start from 1, 0 is reserved for the root node's agent_id
pub type AgentId = usize;

/// Agent ID 0 is reserved for the root
pub const ROOT_AGENT_ID: AgentId = 0;

/// Ordered pair of AgentIds represents active pair
/// So that we only have to store one mapping to cover A~B and B~A
type RuleLhs = (AgentId, AgentId);

struct RuleRhs {
  rule_src: String, // Rule's source code, used for showing in error messages
  port_idx_to_name: [Vec<PortName>; 2],
  connections: Vec<Connection>, // TODO: Use agent/port id in connections
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
#[derive(new)]
pub struct RuleBook {
  pub agent_name_to_id: HashMap<AgentName, AgentId>, // TODO: read-only getter
  #[new(default)]
  rules: HashMap<RuleLhs, RuleRhs>,
}

impl RuleBook {
  /// Insert into rule book and check for duplicate rules
  pub fn add_rule(&mut self, rule: &Rule) -> Result<(), Error> {
    let Rule { lhs: active_pair, rhs: rule_rhs } = rule;
    let ActivePair { lhs, rhs } = active_pair;
    let lhs_id = *self.agent_name_to_id.get(&lhs.agent).unwrap();
    let rhs_id = *self.agent_name_to_id.get(&rhs.agent).unwrap();
    let ((lhs, rhs), (lhs_id, rhs_id)) =
      if lhs_id <= rhs_id { ((lhs, rhs), (lhs_id, rhs_id)) } else { ((rhs, lhs), (rhs_id, lhs_id)) };
    let key = (lhs_id, rhs_id); // Ordered pair
    let value = RuleRhs {
      rule_src: rule.to_string(),
      port_idx_to_name: [
        lhs.ports.iter().map(|port_name| port_name.to_owned()).collect_vec(),
        rhs.ports.iter().map(|port_name| port_name.to_owned()).collect_vec(),
      ],
      connections: rule_rhs.clone(),
    };
    if let Some(_) = self.rules.insert(key, value) {
      return Err(format!("Duplicate rule for active pair `{active_pair}`: {rule}"));
    }
    Ok(())
  }

  /// Apply rule to active pair if such a rule exists
  /// Returns true if a rule was applied
  pub fn apply(&self, net: &mut INet, active_pair: (NodeIdx, NodeIdx)) -> bool {
    let (node_idx_lhs, node_idx_rhs) = active_pair;
    let (lhs_node, rhs_node) = (&net[node_idx_lhs], &net[node_idx_rhs]);
    let (lhs_id, rhs_id) = (lhs_node.agent_id, rhs_node.agent_id);
    let ((lhs_node, rhs_node), (lhs_id, rhs_id)) = if lhs_id <= rhs_id {
      ((lhs_node, rhs_node), (lhs_id, rhs_id))
    } else {
      ((rhs_node, lhs_node), (rhs_id, lhs_id))
    };
    let key = (lhs_id, rhs_id); // Ordered pair
    if let Some(RuleRhs { rule_src: rule, port_idx_to_name, connections }) = self.rules.get(&key) {
      // eprintln!("Applying rule for active pair `{active_pair:?}`: {rule}");

      // Build external_links map from port name to NodePort in this net
      // based on all auxiliary ports in the active pair, e.g. if the rule RHS
      // is Add(ret, a) ~ Succ(b), the ports {ret, a, b} will be mapped, then
      // INet::add_connections looks up ports when adding the connections of the RHS sub-net

      // TODO: Optimize, don't do port lookup by name
      let external_links = [lhs_node, rhs_node]
        .into_iter()
        .zip(port_idx_to_name)
        .flat_map(|(node, port_idx_to_name)| {
          debug_assert_eq!(
            node.ports.len(),
            port_idx_to_name.len() + 1,
            "\n{net:#?}\n{rule}\n{node:?}, {port_idx_to_name:?}"
          );
          // Skip principal port, we only have names for auxiliary ports
          node
            .ports
            .iter()
            .skip(1)
            .zip(port_idx_to_name)
            .map(|(&node_port, port_name)| (port_name.as_str(), node_port))
        })
        .collect();
      net.add_connections(connections, external_links, &self.agent_name_to_id);
      true
    } else {
      false
    }
  }
}
