//! Defines the `Lexer` iterator that lexes a `char` iterator using a supplied deterministic
//! finite automoton.

use super::{Span, Result};

/// The iterator that lexes a `char` iterator into a token iterator.
///
/// The generic type `T` is the token type.
///
/// The iterator is a falible iterator over `Span<T>` where the span runs from the start of the
/// first `char` that is part of the token to the end of the last `char`. `Lexer` performs a
/// maximal-munch lex of a falible `Span<char>` iterator using a supplied deterministic finite
/// automoton ("dfa").
pub struct Lexer<T> {
    _t: T
}

impl<T> Iterator for Lexer<T> {
    type Item = Result<Span<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!();
    }
}
