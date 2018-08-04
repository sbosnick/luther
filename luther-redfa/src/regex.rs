// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

pub struct RegexContext {}

impl RegexContext {
    pub fn new() -> RegexContext {
        unimplemented!()
    }

    pub fn empty() -> Regex {
        unimplemented!()
    }

    pub fn class() -> Regex {
        unimplemented!()
    }

    pub fn concat() -> Regex {
        unimplemented!()
    }

    pub fn repetition() -> Regex {
        unimplemented!()
    }

    pub fn alteration() -> Regex {
        unimplemented!()
    }

    pub fn and() -> Regex {
        unimplemented!()
    }

    pub fn complement() -> Regex {
        unimplemented!()
    }
}

pub struct Regex {}

impl Regex {
    pub fn kind(&self) -> RegexKind {
        unimplemented!()
    }
}

pub enum RegexKind {
    Empty,
    Class,
    Concat,
    Repetition,
    Alteration,
    And,
    Complement,
}
