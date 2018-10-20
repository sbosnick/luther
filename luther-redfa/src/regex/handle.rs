// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use alphabet::Alphabet;
use regex::RegexKind;

/// A regular expression.
///
/// A `Regex` is created by the factory methods in `RegexContext` and is
/// associated with that context. It is not possible to create a `Regex`
/// directly. It is also not possible to create a `Regex` from a `RegexKind` in
/// order to allow `RegexContext` to maintain certain regular expressions in
/// cannonical form.
#[derive(Debug, PartialEq, Clone, Copy, Hash, Eq)]
pub struct Regex<'a, A: 'a + Alphabet> {
    kind: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Regex<'a, A> {
    pub(super) fn new(kind: &'a RegexKind<'a, A>) -> Self {
        Regex{ kind }
    }

    /// Get the kind of the regular expression.
    pub fn kind(&self) -> &'a RegexKind<'a, A> {
        &self.kind
    }
}
