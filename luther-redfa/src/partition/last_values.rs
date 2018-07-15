// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

pub struct UnionLastVals(Option<(bool, bool)>);

impl UnionLastVals {
    pub fn new() -> Self {
        UnionLastVals(None)
    }

    pub fn next_value(&mut self, left: Option<bool>, right: Option<bool>) -> Option<bool> {
        // These predicates are the heart of the UnionIntervalIter implementation. They
        // decide whether `value` is a new value in the context of `first` and `second`.
        // UnionIntervalIter::next() will skip values for which these predicates are
        // false (assuming there is already some `first` and `second` context). There
        // may be a way to combine these two predicates, but we should wait until there is
        // more tests of PartitionMap (or UnionIntervalIter) before trying to do so.
        fn is_new_value(value: bool, first: bool, second: bool) -> bool {
            (value && !(first || second)) || (!value && !second)
        }
        fn is_new_value_dual(value: bool, first: bool, second: bool) -> bool {
            (value != first && second) || (!value && !second)
        }

        let result = match (left, right, self.0) {
            (Some(nl), Some(nr), None) => Some(nl || nr),
            (Some(nl), None, None) => Some(nl),
            (None, Some(nr), None) => Some(nr),
            (Some(nl), None, Some((ol, or))) if is_new_value(nl, ol, or) => Some(nl),
            (None, Some(nr), Some((ol, or))) if is_new_value(nr, or, ol) => Some(nr),
            (Some(nl), Some(nr), Some((ol, or))) if is_new_value_dual(nl || nr, ol, ol == or) => {
                Some(nl || nr)
            }
            _ => None,
        };

        self.0 = match (left, right) {
            (Some(left), Some(right)) => Some((left, right)),
            (None, None) => None,
            (Some(left), None) => Some((left, self.0.map_or(left, |(_, right)| right))),
            (None, Some(right)) => Some((self.0.map_or(right, |(left, _)| left), right)),
        };

        result
    }
}
