use crate::parser::ast::*;
use itertools::Itertools;
use std::fmt;

// Display impls for nested types

impl fmt::Display for NestedAgent {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let Self { agent, ports } = self;
    write!(f, "{agent}")?;
    if !ports.is_empty() {
      write!(f, "({})", ports.iter().map(|port| format!("{}", port)).join(", "))?;
    }
    Ok(())
  }
}

impl fmt::Display for NestedConnector {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      NestedConnector::Agent(agent) => write!(f, "{}", agent),
      NestedConnector::Port(port) => write!(f, "{}", port),
    }
  }
}

impl fmt::Display for NestedConnection {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} ~ {}", self.lhs, self.rhs)
  }
}

pub fn fmt_nested_connections(connections: &[NestedConnection]) -> String {
  connections.iter().map(|conn| format!("{}", conn)).join(", ")
}

// Display impls for flat types

impl fmt::Display for Agent {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let Self { agent, ports } = self;
    write!(f, "{agent}")?;
    if !ports.is_empty() {
      write!(f, "({})", ports.iter().map(|port| format!("{}", port)).join(", "))?;
    }
    Ok(())
  }
}

impl fmt::Display for Connector {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Connector::Agent(agent) => write!(f, "{}", agent),
      Connector::Port(port) => write!(f, "{}", port),
    }
  }
}

impl fmt::Display for Connection {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} ~ {}", self.lhs, self.rhs)
  }
}

pub fn fmt_connections(connections: &[Connection]) -> String {
  connections.iter().map(|conn| format!("{}", conn)).join(", ")
}

// Display impls for rule types

impl fmt::Display for ActivePair {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    impl ActivePair {
      fn to_connection(self) -> Connection {
        let Self { lhs, rhs } = self;
        Connection::new(Connector::Agent(lhs), Connector::Agent(rhs))
      }
    }

    write!(f, "{}", self.clone().to_connection())
  }
}

impl fmt::Display for Rule {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} = {}", self.lhs, fmt_connections(&self.rhs))
  }
}

impl fmt::Display for Ast {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let indent = "  ";
    write!(
      f,
      "AST {{\n{indent}agents: [\n{}\n{indent}],\n{indent}rules: [\n{}\n{indent}],\n{indent}init: {}\n}}",
      self.agents.iter().map(|agent| format!("{indent}{indent}{}", agent.val)).join("\n"),
      self.rules.iter().map(|rule| format!("{indent}{indent}{}", rule)).join("\n"),
      fmt_connections(&self.init.val)
    )
  }
}
