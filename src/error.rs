use crate::lexer::Token;
use chumsky::prelude::Rich;
use color_eyre::{eyre::eyre, Report};
use itertools::Itertools;

pub type ProgramError<'a> = Rich<'a, Token<'a>>;
pub type ProgramErrors<'a> = Vec<ProgramError<'a>>;
pub type IvmResult<T> = color_eyre::eyre::Result<T>;

/// Print program errors and convert to eyre error, to be used in map_err
pub fn print_program_errors<'a>(errs: ProgramErrors<'a>, src: &'a str) -> Report {
  use ariadne::{Color, Label, Report, ReportKind, Source};

  errs.into_iter().sorted_by_key(|e| e.span().start).for_each(|e| {
    Report::build(ReportKind::Error, (), e.span().start)
    // .with_code(1)
    .with_message(e.to_string())
    .with_label(
      Label::new(e.span().into_range()).with_message(e.reason().to_string()).with_color(Color::Red),
    )
    .finish()
    .write(Source::from(src), std::io::stderr().lock())
    .unwrap()
  });
  eyre!("Execution aborted due to errors")
}

/// Each static analysis / transformation pass can produce an output, or multiple errors
/// found in the program. This function takes the output and program errors, and returns a Result
/// for easy chaining of passes. If the program contains errors, they are printed to stderr.
pub fn pass_output_and_errors_to_result<'a, T>(
  src: &'a str,
  output: Option<T>,
  errors: ProgramErrors<'a>,
) -> IvmResult<T> {
  type OutputResult<'a, T> = Result<T, Vec<ProgramError<'a>>>;

  fn output_result<T>(output: Option<T>, errors: ProgramErrors<'_>) -> OutputResult<'_, T> {
    if errors.is_empty() { output.ok_or(errors) } else { Err(errors) }
  }

  output_result(output, errors).map_err(|e| print_program_errors(e, src))
}
