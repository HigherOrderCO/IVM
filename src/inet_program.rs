use crate::{
  inet::INet,
  parser::ast::{AgentName, Ast, ROOT_PORT_NAME},
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
  pub(crate) agent_id_to_name: HashMap<AgentId, AgentName>,
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
    let root_port_names = &[ROOT_PORT_NAME.to_owned()];
    self.net.read_back(&self.agent_id_to_name, root_port_names)
  }
}
