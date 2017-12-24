#[macro_use]
extern crate failure;

#[cfg(test)]
mod test;

use std::{ops, result};

#[deny(missing_docs)]

/// Wraps a value with start and end `Location`'s.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Span<T> {
    start: Location,
    end: Location,
    value: T
}

impl<T> Span<T> {
    /// Create a new `Span` for a given start and end `Location` and value.
    pub fn new(start: Location, end: Location, value: T) -> Span<T> {
        Span{start, end, value}
    }

    /// Gets the start `Location` of the `Span`.
    pub fn start(&self) -> Location {
        self.start
    }

    /// Gets the end `Location` of the `Span`.
    pub fn end(&self) -> Location {
        self.end
    }

    /// Gets a reference to the value of the `Span`.
    pub fn value_ref(&self) -> &T {
        &self.value
    }

    /// Extends the current `Span` to a new end `Location`.
    pub fn extend(&mut self, end: Location) {
        self.end = end;
    }
}

impl From<(usize, char)> for Span<char> {
    /// Converts from a (pos, value) to a `Span`.
    ///
    /// This conversion is designed to support the Item type of the iterator returned from the
    /// `str::char_indicies()` method. It assumes the pos is the starting position and that the value
    /// is encoded in utf8.
    fn from((pos, value): (usize, char) ) -> Self {
        Self::new(pos.into(), (pos + value.len_utf8()).into(), value)
    }
}

/// An abstract location within a stream of tokens or characters.
///
/// Note that `Location`'s are not orderable (that is, `Location` does not impl `Ord` or `PartialOrd`).
/// The value of a `Location` cannot tell you whether it comes before or after some other
/// `Location` in the same stream, just whether its equal or not equal to some other `Location`.
/// It is possible to create a new `Location` from a `usize` or by adding a `usize` to an exising `Location`.
///
/// # Panics
///
/// Adding a usize to a `Location` will panic if the resulting `Location` value is greater than
/// `usize::max_value()`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Default)]
pub struct Location (usize);

impl Location {
    /// Create a new `Location` for a given starting point.
    pub fn new(location: usize) -> Location {
        Location(location)
    }
}

impl ops::AddAssign<usize> for Location {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl ops::Add<usize> for Location {
    type Output = Location;

    fn add(mut self, rhs: usize) -> Location {
        self += rhs;
        self
    }
}

impl From<usize> for Location {
    fn from(value: usize) -> Self {
        Self::new(value)
    }
}

/// The error type for the lexers produced by Lexer implementations.
#[derive(Debug, Fail)]
pub enum LexError {
    /// The lexer encountered an invalid chararter in the input. This error occurs
    /// when the invalid character would be the first character of a new token.
    #[fail(display = "The lexer encountered an invalid character in the input: {}.", _0)]
    InvalidCharacter(char),
}

/// A specialized Result type for lexer operations.
pub type Result<T> = result::Result<T, LexError>;
