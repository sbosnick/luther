// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

#![crate_type = "lib"]

extern crate luther;

#[macro_use]
extern crate luther_derive;

#[derive(Lexer, Debug)]
pub enum Token {
    #[luther(regex = "ab")] Ab,
    #[luther(regex = "acc*", priority_group = "2")] Acc,
    #[luther(regex = "a(bc|de)")] Abcde(String),
}
