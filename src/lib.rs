#[macro_use]
extern crate failure;

/// The error type for the lexers produced by Lexer implementations.
#[derive(Debug, Fail)]
pub enum LexError {
    /// The lexer encountered an invalid chararter in the input. This error occurs
    /// when the invalid character would be the first character of a new token.
    #[fail(display = "The lexer encountered an invalid character in the input: {}.", _0)]
    InvalidCharacter(char),
}
