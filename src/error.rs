// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::result;
use failure::Fail;

/// The error type for the lexers produced by Lexer implementations.
#[derive(Debug, Fail)]
pub enum LexError<F: Fail> {
    /// The lexer encountered an invalid chararter in the input. This error occurs
    /// when the invalid character would be the first character of a new token.
    #[fail(display = "The lexer encountered an invalid character in the input: {}.", _0)]
    InvalidCharacter(char),

    /// The lexer encountered an invalid token in the input. This error occurs
    /// when the lexer has consumed some valid characters but cannot make further
    /// progress and the consumed characters do not form a valid token.
    #[fail(display = "The lexer encountered an invalid token: {}.", _0)]
    InvalidToken(String),

    /// The lexer encountered an error in the input stream.
    #[fail(display = "The lexer encountered an input error.")]
    InputError(#[cause] F)
}

impl<F: Fail> From<F> for LexError<F> {
    fn from(f: F) -> LexError<F> {
        LexError::InputError(f)
    }
}

/// A specialized Result type for lexer operations.
pub type Result<T, F> = result::Result<T, LexError<F>>;
