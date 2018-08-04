// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use typed_arena::Arena;

/// A context for creating regular expressions.
///
/// The factory methods in `RegexContext` create different kinds of `Regex` but
/// also maintain those `Regex` in `≈-cannonical` form as this is defined in section
/// 4.1 of Owens et al. The need to maintain the regular expressions in cannonical form
/// is why there is no means of creating a `Regex` from a `RegexKind`.
pub struct RegexContext {
    arena: Arena<RegexKind>,
}

impl RegexContext {
    /// Create a new `RegexContext`.
    pub fn new() -> RegexContext {
        RegexContext {
            arena: Arena::new(),
        }
    }

    /// Create an empty `Regex`.
    ///
    /// The empty regular expressions matches everything, including the empty
    /// string.
    pub fn empty(&self) -> Regex {
        Regex {
            kind: self.arena.alloc(RegexKind::Empty),
        }
    }

    pub fn class(&self) -> Regex {
        unimplemented!()
    }

    pub fn concat(&self) -> Regex {
        unimplemented!()
    }

    pub fn repetition(&self) -> Regex {
        unimplemented!()
    }

    pub fn alteration(&self) -> Regex {
        unimplemented!()
    }

    pub fn and(&self) -> Regex {
        unimplemented!()
    }

    pub fn complement(&self) -> Regex {
        unimplemented!()
    }
}

/// A regular expression.
///
/// A `Regex` is created by the factory methods in `RegexContext` and is
/// associated with that context. It is not possible to create a `Regex`
/// directly. It is also not possible to create a `Regex` from a `RegexKind` in
/// order to allow `RegexContext` to maintain certain regular expressions in
/// cannonical form.
pub struct Regex<'a> {
    kind: &'a RegexKind,
}

impl<'a> Regex<'a> {
    /// Get the kind of the regular expression.
    pub fn kind(&self) -> &RegexKind {
        &self.kind
    }
}

/// The kind of a regular expressions.
#[derive(Debug, PartialEq)]
pub enum RegexKind {
    /// The empty regular expressions which matches everything, including the
    /// empty string.
    Empty,
    Class,
    Concat,
    Repetition,
    Alteration,
    And,
    Complement,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty_regex_has_kind_empty() {
        let ctx = RegexContext::new();

        let sut = ctx.empty();

        assert_eq!(sut.kind(), &RegexKind::Empty);
    }
}
