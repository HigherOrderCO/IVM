use logos::{FilterResult, Lexer, Logos};
use std::fmt;

#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Token<'a> {
	// Keywords
	#[token("agent")]
	KeywordAgent,

	#[token("rule")]
	KeywordRule,

	#[token("init")]
	KeywordInit,

	// Symbols
	#[token("(")]
	LParen,

	#[token(")")]
	RParen,

	#[token(",")]
	Comma,

	#[regex("=")]
	Equals,

	#[token("~")]
	Tilde,

	#[regex("[A-Z][_a-zA-Z0-9]*")]
	Agent(&'a str),

	#[regex("[a-z][_a-zA-Z0-9]*")]
	Port(&'a str),

	#[regex("//.*", logos::skip)]
	SingleLineComment,

	#[token("/*", comment)]
	MultiLineComment,

	#[regex(r"[ \t\f\n]+", logos::skip)]
	Whitespace,

	#[error]
	Error,
}

// Lexer for nested multi-line comments
#[derive(Logos)]
pub enum MultiLineComment {
	#[token("/*")]
	Open,

	#[token("*/")]
	Close,

	#[regex("(?s).")]
	Other,

	#[error]
	Error,
}

fn comment<'a>(lexer: &mut Lexer<'a, Token<'a>>) -> FilterResult<()> {
	let start = lexer.remainder();
	let mut comment = MultiLineComment::lexer(start);
	let mut depth = 1; // Already matched an Open token, so count it
	while {
		if let Some(token) = comment.next() {
			match token {
				MultiLineComment::Open => depth += 1,
				MultiLineComment::Close => depth -= 1,
				MultiLineComment::Other => {}
				MultiLineComment::Error => return FilterResult::Error,
			}
		} else {
			// Unclosed comment
			return FilterResult::Error;
		}
		depth > 0
	} {}
	let end = comment.remainder();
	let span = end as *const str as *const () as usize - start as *const str as *const () as usize;
	lexer.bump(span);
	FilterResult::Skip
}

impl<'a> fmt::Display for Token<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::KeywordAgent => write!(f, "agent"),
			Self::KeywordRule => write!(f, "rule"),
			Self::KeywordInit => write!(f, "init"),
			Self::LParen => write!(f, "("),
			Self::RParen => write!(f, ")"),
			Self::Comma => write!(f, ","),
			Self::Equals => write!(f, "="),
			Self::Tilde => write!(f, "~"),
			Self::Agent(s) => write!(f, "{}", s),
			Self::Port(s) => write!(f, "{}", s),
			Self::SingleLineComment => write!(f, "<SingleLineComment>"),
			Self::MultiLineComment => write!(f, "<MultiLineComment>"),
			Self::Whitespace => write!(f, "<whitespace>"),
			Self::Error => write!(f, "<error>"),
		}
	}
}
