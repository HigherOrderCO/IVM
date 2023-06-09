pub mod error;
pub mod inet;
pub mod inet_program;
pub mod lexer;
pub mod parser;
pub mod rule_book;
pub mod rule_map;
pub mod util;

#[cfg(test)]
mod tests;

use mimalloc_rust::GlobalMiMalloc;

#[global_allocator]
static GLOBAL_ALLOC: GlobalMiMalloc = GlobalMiMalloc;
