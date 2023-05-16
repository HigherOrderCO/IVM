#![allow(dead_code)]

mod inet;
mod lexer;
mod parser;
mod rule_book;
#[cfg(test)]
mod tests;

type Error = String; // TODO: Use stronger type
