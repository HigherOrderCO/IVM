#![allow(dead_code)]

mod inet;
mod lexer;
mod parser;
mod rule_book;
#[cfg(test)]
mod tests;

// TODO: Use stronger type like extra::Err<Rich<'a, Token<'a>>> with Rich::custom()
type Error = String;
