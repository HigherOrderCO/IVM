use crate::{
  inet::INet,
  parser::{
    ast::{AgentName, Ast},
    display::fmt_nested_connections,
    flatten::unflatten_connections,
  },
  rule_book::{AgentId, RuleBook},
};
use derive_new::new;
use hashbrown::HashMap;

/// `INetProgram` contains all context necessary to reduce the net
#[derive(new, Clone)]
pub struct INetProgram {
  pub ast: Ast, // Not necessary for reduction, but useful for debugging
  pub net: INet,
  pub rule_book: RuleBook,
  agent_name_to_id: HashMap<AgentName, AgentId>,
  #[new(default)]
  agent_id_to_name: Option<HashMap<AgentId, AgentName>>,
}

impl INetProgram {
  /// Perform one reduction step
  pub fn scan_active_pairs_and_reduce_step(&mut self) -> bool {
    self.net.scan_active_pairs_and_reduce_step(&self.rule_book)
  }

  /// Reduce the net using the rule book
  pub fn reduce(&mut self) -> usize {
    self.net.reduce(&self.rule_book)
  }

  /// Read back reduced net into readable (nested) textual form
  pub fn read_back(&mut self) -> String {
    // Compute `agent_id_to_name` only if needed and then cache it
    let agent_id_to_name = self
      .agent_id_to_name
      .get_or_insert_with(|| self.agent_name_to_id.iter().map(|(name, id)| (*id, name.clone())).collect());

    let connections = self.net.read_back(agent_id_to_name);
    let connections = unflatten_connections(connections);
    fmt_nested_connections(&connections)
  }
}
