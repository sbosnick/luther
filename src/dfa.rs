//! Defines the `Lexer` iterator that lexes a `char` iterator using a supplied deterministic
//! finite automaton.

use std::result::Result as StdResult;
use std::marker::PhantomData;
use failure::Fail;
use super::{Span, Result};

/// The iterator that lexes a `char` iterator into a token iterator.
///
/// The generic type `T` is the token type.
///
/// The iterator is a falible iterator over `Span<T>` where the span runs from the start of the
/// first `char` that is part of the token to the end of the last `char`. `Lexer` performs a
/// maximal-munch lex of a falible `Span<char>` iterator using a supplied deterministic finite
/// automaton ("dfa").
///
/// # Type Parameters
/// - T: the token type
/// - F: the failure type for the falible input iterator
/// - I: the falible input iterator type over `Span<char>`
/// - D: the deterministic finite automaton that return `T` tokens in accepting states
pub struct Lexer<T, F, I, D>
where I: Iterator<Item=StdResult<Span<char>,F>>,
      F: Fail,
      D: Dfa<T>
{
    _input: I,
    _current: D,
    _t: PhantomData<T>
}

impl<T,F,I,D> Lexer<T,F,I,D>
where I: Iterator<Item=StdResult<Span<char>,F>>,
      F: Fail,
      D: Dfa<T>
{
    /// Create a new `Lexer` from the supplied iterator.
    pub fn new(_: I) -> Lexer<T,F,I,D> {
        unimplemented!();
    }
}

impl<T,F,I,D> Iterator for Lexer<T,F,I,D>
where I: Iterator<Item=StdResult<Span<char>,F>>,
      F: Fail,
      D: Dfa<T>
{
    type Item = Result<Span<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!();
    }
}

/// Interface to describe a deterministic finite atomaton.
///
/// Mathematically a dfa is a 5-tuple: (Q, q₀, Σ, δ, A) where
///
/// - Q: a set of states
/// - q₀: the start state (q₀ ∈ Q)
/// - Σ: the alphabet over which the dfa operates
/// - δ: a function Q x Σ → Q (the transition function)
/// - A: the accepting states (A ⊆ Q)
///
/// The `Dfa` trait corresponds to this defintion as follows:
///
/// - `Self`: the set of states
/// - `Default::default()`: the start state
/// - `char`: the alphabet over which `Dfa` operates
/// - `transition()`: the transition function
/// - `accept()`: a function to test if a given state is an accepting state
///
/// In addition to the mathematical elements of a dfa, `Dfa` has the `error_state()`
/// method which identifies one of the states as a special error state.
///
/// # Type Parameters
/// - `T`: the token type returned for accepting states
pub trait Dfa<T>: Default {
    /// Identifies the error state for the `Dfa`.
    ///
    /// The error state is used by `Lexer` to implement maximal-munch lexing.
    fn error_state() -> Self;

    /// The transition function for the the `Dfa`.
    ///
    /// The function identifes the target state when trasitioning from the current
    /// state using the transition identifed by `c`.
    ///
    /// # Parameters
    /// - c: the `char` that names the transition to follow
    ///
    /// # Returns
    /// The new state after following the transition.
    fn transition(&self, c: char) -> Self;

    /// Tests for being in an accepting state.
    ///
    /// # Parameters
    /// - matched: the `str` of matched characters for the transtions from the start state to the
    /// current state
    ///
    /// # Returns
    /// - `None`: the current state is not an accepting state
    /// - `Some(t)`: the current state is an aceepting state and `t` is the corresponding token
    fn accept(&self, matched: &str) -> Option<T>;
}
