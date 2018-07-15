// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! A library for creating a deterministic finite automaton from a regular
//! expression or from a regular vector.
//!
//! This library implements the dfa construction technique described in
//! Scott Owens et al., _Regular Expression Derivatives Reexamined_. The
//! motivating use for this library is the [luther-derive] crate, but it
//! may have additional uses.
//!
//! [luther-derive]: https://crates.io/crates/luther-derive

#![deny(missing_docs)]

#[cfg(test)]
#[macro_use]
extern crate proptest;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

pub mod alphabet;

mod partition;
mod range;
