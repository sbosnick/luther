#[deny(missing_docs)]

#[macro_use]
extern crate failure;

mod error;
mod span;

pub use error::{LexError, Result};
pub use span::{Span, Location};
