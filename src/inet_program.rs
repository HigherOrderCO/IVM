use crate::{
  inet::INet,
  parser::{ast::Ast, display::fmt_nested_connections, flatten::unflatten_connections},
  rule_book::RuleBook,
};

/// INet program contains all context necessary to reduce the net
pub struct INetProgram {
  pub ast: Ast, // Not necessary for reduction, but useful for debugging
  pub net: INet,
  pub rule_book: RuleBook,
}

impl INetProgram {
  /// Reduce the net using the rule book
  pub fn reduce(&mut self) -> usize {
    self.net.reduce_full(&self.rule_book)
  }

  /// Perform one reduction step
  pub fn reduce_step(&mut self) -> bool {
    self.net.reduce_step(&self.rule_book)
  }

  /// Read back reduced net into readable (nested) textual form
  pub fn read_back(&self) -> String {
    let connections = self.net.read_back();
    let connections = unflatten_connections(connections);
    fmt_nested_connections(&connections)
  }
}
