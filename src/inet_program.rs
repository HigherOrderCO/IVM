use crate::{
  inet::INet,
  parser::{
    ast::{AgentName, Ast},
    display::fmt_nested_connections,
    flatten::unflatten_connections,
  },
  rule_book::{AgentId, RuleBook},
};
use hashbrown::HashMap;

/// `INetProgram` contains all context necessary to reduce the net
#[derive(Clone)]
pub struct INetProgram {
  pub ast: Ast, // Not necessary for reduction, but useful for debugging
  pub net: INet,
  pub rule_book: RuleBook,
  pub agent_name_to_id: HashMap<AgentName, AgentId>,
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
  pub fn read_back(&self) -> String {
    let connections = self.net.read_back();
    let connections = unflatten_connections(connections);
    fmt_nested_connections(&connections)
  }
}
