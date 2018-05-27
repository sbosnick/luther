// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

extern crate luther;

use std::default;
use luther::Lexer;
use luther::spanned::StrExt;

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
            _ => None, // COV_EXCL_LINE
        }
    }
}

impl luther::Lexer for Tokens {
    type Dfa = TokensDfa;
}

// End luther-dervie exemplar

#[test]
fn luther_matches_for_tokens_ab_and_accc() {
    let input = "abaccc".spanned_chars();

    let sut = Tokens::lexer(input).map(|r| r.map(|s| s.into_inner().1));
    let result: Result<Vec<_>, _> = sut.collect();
    let result = result.expect("unexpected lexer error");

    assert_eq!(result, vec![Tokens::Ab, Tokens::Acc("accc".to_string())]);
}
