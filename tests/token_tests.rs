// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

#[macro_use]
extern crate failure;
extern crate luther;

use std::default;
use luther::Lexer;

#[derive(Debug, PartialEq)]
enum Tokens {
    Ab,
    Acc(String),
}

// Start luther-derive exemplar

// dfa matches ["ab", "acc*"]
#[derive(PartialEq, Debug, Clone, Copy)]
enum TokensDfa {
    State0, // ["ab", "acc*"]
    State1, // [ null, null ]
    State2, // ["b", "cc*"]
    State3, // ["", null]
    State4, // [null, "c*"]
}

impl default::Default for TokensDfa {
    fn default() -> Self {
        TokensDfa::State0
    }
}

impl luther::dfa::Dfa<Tokens> for TokensDfa {
    fn is_error(&self) -> bool {
        *self == TokensDfa::State1
    }

    fn transition(&self, c: char) -> Self {
        use TokensDfa::*;

        match (*self, c) {
            (State0, 'a') => State2,
            (State2, 'b') => State3,
            (State2, 'c') => State4,
            (State4, 'c') => State4,
            (_, _) => State1,
        }
    }

    fn accept(&self, matched: &str) -> Option<Tokens> {
        use TokensDfa::*;

        match *self {
            State3 => Some(Tokens::Ab),
            State4 => Some(Tokens::Acc(matched.parse().unwrap_or_default())),
            _ => None,
        }
    }
}

impl luther::Lexer for Tokens {
    type Dfa = TokensDfa;
}

// End luther-dervie exemplar

#[derive(Fail, Debug)]
enum NoError {}

impl std::fmt::Display for NoError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "The impossible has occured.")
    }
}

struct SpanedStrIter<I>
where
    I: Iterator<Item = (usize, char)>,
{
    inner: I,
}

impl<'a> SpanedStrIter<std::str::CharIndices<'a>> {
    fn new(input: &'a str) -> Self {
        SpanedStrIter {
            inner: input.char_indices(),
        }
    }
}

impl<I> Iterator for SpanedStrIter<I>
where
    I: Iterator<Item = (usize, char)>,
{
    type Item = Result<luther::Span<char>, NoError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(i) => Some(Ok(i.into())),
        }
    }
}

#[test]
fn luther_matches_for_tokens_ab_and_accc() {
    let input = SpanedStrIter::new("abaccc");

    let sut = Tokens::lexer(input).map(|r| r.map(|s| s.into_inner().1));
    let result: Result<Vec<_>, _> = sut.collect();
    let result = result.expect("unexpected lexer error");

    assert_eq!(result, vec![Tokens::Ab, Tokens::Acc("accc".to_string())]);
}
