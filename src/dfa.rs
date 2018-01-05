//! Defines the `Lexer` iterator that lexes a `char` iterator using a supplied deterministic
//! finite automaton.

use std::iter;
use std::result::Result as StdResult;
use std::marker::PhantomData;
use failure::Fail;
use super::{Span, Result, LexError, Location};

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
    input: iter::Peekable<I>,
    _d: PhantomData<D>,
    _t: PhantomData<T>
}

impl<T,F,I,D> Lexer<T,F,I,D>
where I: Iterator<Item=StdResult<Span<char>,F>>,
      F: Fail,
      D: Dfa<T>
{
    /// Create a new `Lexer` from the supplied iterator.
    pub fn new(input: I) -> Lexer<T,F,I,D> {
        Lexer{ input: input.peekable(), _d: PhantomData, _t: PhantomData }
    }

    // The Ok return is what is needed to drive the Iterator::next() loop. The Err
    // return is the return type from Iterator::next() when the pre-conditions for
    // loop aren't there.
    //
    // Errors that occur during the Iterator::next() loop end the loop and cause
    // next() to attempt to return a Span<T> based on what has been processed so far.
    // The error itself is left to the next call to Iterator::next() to be returned.
    //
    // That is where this function comes in. This function detects the errors that
    // occured at the end of the last Iterator::next() call and return them on this call
    // (though it will also detect errors at the start of the first Iterator::next() call
    // as well).
    fn init_dfa(&mut self) -> StdResult<(Location, Location, D), Option<Result<Span<T>, F>>> {
        let state = D::default();

        // The Ok() case peeks but does not read
        if let Some(&Ok(ref span)) = self.input.peek() {
            if !(state.transition(*span.value_ref()).is_error()) {
                return Ok((span.start(), span.end(), state));
            }
        }

        // The Err() case reads and consumes the input
        match self.input.next() {
            None => Err(None),
            Some(Err(err)) => Err(Some(Err(err.into()))),
            Some(Ok(span)) => Err(Some(Err(LexError::InvalidCharacter(*span.value_ref()))))
        }
    }
}

impl<T,F,I,D> Iterator for Lexer<T,F,I,D>
where I: Iterator<Item=StdResult<Span<char>,F>>,
      F: Fail,
      D: Dfa<T>
{
    type Item = Result<Span<T>, F>;

    fn next(&mut self) -> Option<Self::Item> {
        // Initialize the dfa and tracking state
        let (start, mut end, mut state) = match self.init_dfa() {
            Ok(ok) => ok,
            Err(err) => return err
        };

        let mut tok_str = String::new();

        // Loop while there is more input that does not cause
        // an error transition.
        loop {
            match self.input.peek() {
                Some(&Ok(ref span)) => {
                    let next_state = state.transition(*span.value_ref());
                    if next_state.is_error() {
                        break;
                    }

                    state = next_state;
                    end = span.end();
                    tok_str.push(*span.value_ref());
                },
                _ => break,
            }

            self.input.next();
        }

        // Return the accepted token or InvalidToken
        Some(state.accept(&tok_str)
                        .map(|t| Span::new(start, end, t))
                        .ok_or(LexError::InvalidToken(tok_str)))
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
    /// Test for an error state for the `Dfa`.
    ///
    /// Error states are used by `Lexer` to implement maximal-munch lexing.
    fn is_error(&self) -> bool;

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

#[cfg(test)]
mod test {
    use super::*;
    use std::str;
    use quickcheck;
    use regex::Regex;

    #[derive(PartialEq, Eq, Debug)]
    enum Tokens {
        Token1(String),
    }

    // This dfa corresponds to the re "a(b|c)c*"
    #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
    enum DfaStates { State0, State1, State2, State3 }

    impl Default for DfaStates {
        fn default() -> Self {
            DfaStates::State0
        }
    }

    impl Dfa<Tokens> for DfaStates {
        fn is_error(&self) -> bool {
            *self == DfaStates::State2
        }

        fn transition(&self, c: char) -> Self {
            use self::DfaStates::*;

            match (self, c) {
                (&State0, 'a') => State1,
                (&State1, 'b') => State3,
                (&State1, 'c') => State3,
                (&State3, 'c') => State3,
                (_, _) => State2,
            }
        }

        fn accept(&self, input: &str) -> Option<Tokens> {
            if *self == DfaStates::State3 {
                Some(Tokens::Token1(input.to_string()))
            } else {
                None
            }
        }
    }

    #[derive(Debug,Fail)]
    #[fail(display = "The impossible has happend: NoFail has failed.")]
    struct NoFail {}

    type DfaLexer<I> = Lexer<Tokens, NoFail, I, DfaStates>;

    #[derive(Debug,Fail,Clone)]
    enum FakeError{ 
        #[fail(display = "An input error has occured.")]
        InputError 
    }

    impl quickcheck::Arbitrary for FakeError {
        fn arbitrary<G: quickcheck::Gen>(_: &mut G) -> Self {
            // There is only 1 FakeError value so return it
            FakeError::InputError
        }
    }

    type FakeLexer<I> = Lexer<Tokens, FakeError, I, DfaStates>;

    #[test]
    fn lexer_is_some_ok_for_accepted_input() {
        let input = "ab".char_indices().map(|i| Ok(i.into()));

        let mut sut = DfaLexer::new(input)
            .map(|r| r.map(|s| s.into_inner()));
        let result = sut.next();

        assert_matches!(result, Some(Ok((s, Tokens::Token1(_), e)))
                                if s == 0.into() && e == 1.into());
    }

    #[test]
    fn lexer_is_none_for_empty_input() {
        let input = "".char_indices().map(|i| Ok(i.into()));

        let mut sut = DfaLexer::new(input)
            .map(|r| r.map(|s| s.into_inner()));
        let result = sut.next();

        assert_matches!(result, None);
    }

    #[test]
    fn lexer_is_some_err_invalid_token_for_rejected_input() {
        let input = "a".char_indices().map(|i| Ok(i.into()));

        let mut sut = DfaLexer::new(input)
            .map(|r| r.map(|s| s.into_inner()));
        let result = sut.next();

        assert_matches!(result, Some(Err(LexError::InvalidToken(ref s)))
                                if *s == "a".to_string());
    }

    #[test]
    fn lexer_is_some_err_invalid_character_for_invalid_initial_character() {
        let input = "b".char_indices().map(|i| Ok(i.into()));

        let mut sut = DfaLexer::new(input)
            .map(|r| r.map(|s| s.into_inner()));
        let result = sut.next();

        assert_matches!(result, Some(Err(LexError::InvalidCharacter('b'))));
    }

    #[test]
    fn lexer_is_some_err_input_error_for_initial_input_error() {
        let input = vec![Err(FakeError::InputError)];

        let mut sut = FakeLexer::new(input.into_iter())
            .map(|r| r.map(|s| s.into_inner()));
        let result = sut.next();

        assert_matches!(result, Some(Err(LexError::InputError(FakeError::InputError))));
    }

    #[test]
    fn lexer_matches_consecutive_tokens_in_input() {
        let input = "abacabccc".char_indices().map(|i| Ok(i.into()));

        let sut = DfaLexer::new(input)
            .map(|r| r.map(|s| s.into_inner().1));
        let result: StdResult<Vec<_>,_> = sut.collect();
        let strings: Vec<_> = result.expect("DfaLexer had an unexpected error.").into_iter()
            .map(|tok| match tok { Tokens::Token1(s) => s })
            .collect();

        assert_eq!(strings, vec!["ab", "ac", "abccc"])
    }

    #[test]
    fn lexer_is_invalid_character_for_invalid_second_token_in_input() {
        let input = "abb".char_indices().map(|i| Ok(i.into()));

        let sut = DfaLexer::new(input)
            .map(|r| r.map(|s| s.into_inner().1));
        let result: StdResult<Vec<_>,_> = sut.collect();

        assert_matches!(result, Err(LexError::InvalidCharacter('b')));
    }

    #[test]
    fn lexer_is_invalid_token_for_invalid_second_token_in_input() {
        let input = "aba".char_indices().map(|i| Ok(i.into()));

        let sut = DfaLexer::new(input)
            .map(|r| r.map(|s| s.into_inner().1));
        let result: StdResult<Vec<_>,_> = sut.collect();

        assert_matches!(result, Err(LexError::InvalidToken(_)));
    }

    #[test]
    fn lexer_is_input_error_for_subsequent_input_error() {
        let input = vec![Ok((0, 'a').into()), Ok((1,'b').into()), Err(FakeError::InputError)];

        let sut = FakeLexer::new(input.into_iter())
            .map(|r| r.map(|s| s.into_inner()));
        let result: StdResult<Vec<_>,_> = sut.collect();

        assert_matches!(result, Err(LexError::InputError(FakeError::InputError)));
    }

    quickcheck! {
        fn prop_lexer_matches_regex(input: Vec<StdResult<char,FakeError>>) -> bool {
            use LexError::*;
            lazy_static! {
                static ref RE: Regex = Regex::new("^a(b|c)c*$").unwrap();
            }
            let input = input.into_iter().map(|r| r.map(|c| Span::new(0.into(), 0.into(), c)));

            let sut = FakeLexer::new(input)
                .map(|r| r.map(|s| s.into_inner().1));
            let result: StdResult<Vec<_>,_> = sut.collect();

            match result {
                Err(InputError(_)) => true,
                Err(InvalidCharacter(c)) => c != 'a',
                Err(InvalidToken(s)) => !RE.is_match(&s),
                Ok(vec) => vec.into_iter().all(|Tokens::Token1(s)| RE.is_match(&s))
            }
        }
    }
}
