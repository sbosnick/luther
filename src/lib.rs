//! A library for creating a lexer for a token type.
//!
//! The motivating case for this crate is a token enum that has the `Lexer` trait implemented on
//! it. The `lexer` method of this trait will return a token iterator when given a `char` iterator.
//!
//! The `Lexer` trait would normally be derived through the (yet to be written) luther-derive
//! crate.
//!
//! The input to the `lexer` method is a falible iterator (i.e. an iterator with a Result item
//! type) over a `Span` of `char`. The output is a falible iterator over a `Span` of the token
//! type.

#![deny(missing_docs)]

#[macro_use]
extern crate failure;

mod error;
mod span;
pub mod dfa;

pub use error::{LexError, Result};
pub use span::{Span, Location};

use std::result::Result as StdResult;

/// An interface for creating a lexer for a `char` iterator for the type on which it is
/// implemented.
///
/// This trait would normally be derived through the (yet to be written) luther-derive crate.
pub trait Lexer: Sized {
    /// Creates a lexer from the supplied `char` iterator.
    ///
    /// The return type is an iterator over `Self` (or rather `Result<Span<Self>>`).
    fn lexer<I,F>(input: I) -> dfa::Lexer<Self>
        where I: IntoIterator<Item=StdResult<Span<char>, F>>,
              F: failure::Fail;
}
