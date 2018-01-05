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

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

#[cfg(test)]
#[macro_use]
extern crate lazy_static;

#[cfg(test)]
extern crate regex;

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
    /// The deterministic finite automaton for the lexer.
    type Dfa: dfa::Dfa<Self>;

    /// Creates a lexer from the supplied `char` iterator.
    ///
    /// # Type Parameters
    /// - F: the failure type for the input falible iterator
    /// - I: a type convertable to a falible iterator over `Span<char>`
    ///
    /// # Returns
    /// An fallible iterator over `Span<Self>`.
    fn lexer<F,I>(input: I) -> dfa::Lexer<Self, F, <I as IntoIterator>::IntoIter, Self::Dfa>
        where I: IntoIterator<Item=StdResult<Span<char>, F>>,
              F: failure::Fail
    {
        dfa::Lexer::new(input.into_iter())
    }
}
