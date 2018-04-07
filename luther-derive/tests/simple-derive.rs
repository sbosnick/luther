// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

extern crate luther;

#[macro_use]
extern crate luther_derive;

#[macro_use]
extern crate assert_matches;

use luther::Lexer;
use luther::spanned::StrExt;

#[derive(Lexer, Debug)]
enum Token {
    #[luther(regex = "ab")] Ab,
    #[luther(regex = "acc*")] Acc,
    #[luther(regex = "a(bc|de)")] Abcde(String),
}

#[test]
fn token_lexes_ab() {
    let input = "ab".spanned_chars();

    let mut sut = Token::lexer(input).map(|r| r.map(|s| s.into_inner().1));
    let result = sut.next();

    assert_matches!(result, Some(Ok(Token::Ab)));
}

#[test]
fn token_lexes_ade() {
    let input = "ade".spanned_chars();

    let mut sut = Token::lexer(input).map(|r| r.map(|s| s.into_inner().1));
    let result = sut.next();

    assert_matches!(result, Some(Ok(Token::Abcde(ref s))) if s == "ade");
}
