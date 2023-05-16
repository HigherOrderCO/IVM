use crate::lexer::Token;
use chumsky::prelude::Rich;
use color_eyre::{eyre::eyre, Report};

pub type IvmError<'a> = Rich<'a, Token<'a>>;
pub type IvmErrors<'a> = Vec<IvmError<'a>>;
pub type IvmResult<T> = color_eyre::eyre::Result<T>;

pub fn convert_errors<'a>(errs: IvmErrors<'a>, src: &'a str) -> Report {
  use ariadne::{Color, Label, Report, ReportKind, Source};

  errs.into_iter().for_each(|e| {
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

pub fn construct_result<'a, T>(src: &'a str, output: Option<T>, errors: IvmErrors<'a>) -> IvmResult<T> {
  type TmpResult<'a, T> = Result<T, Vec<IvmError<'a>>>;

  fn construct_result<'a, T>(output: Option<T>, errors: IvmErrors<'a>) -> TmpResult<'a, T> {
    if errors.is_empty() { output.ok_or(errors) } else { Err(errors) }
  }

  construct_result(output, errors).map_err(|e| convert_errors(e, src))
}
