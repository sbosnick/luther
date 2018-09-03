// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use alphabet::Alphabet;
use label::TransitionLabel;
use partition::PartitionMap;

/// The DerivativeClasses are a partition of the `Alphabet` into subsets whose
/// Brzozowski derivatives for a specified regular expression (or regular vector)
/// are equivalant for each member of the subset.
pub struct DerivativeClasses<A: Alphabet> {
    map: PartitionMap<A, TransitionLabel>,
}

impl<A: Alphabet> DerivativeClasses<A> {
    pub(crate) fn new(map: PartitionMap<A, TransitionLabel>) -> DerivativeClasses<A> {
        DerivativeClasses { map }
    }

    /// Iterate over the half-open ranges that comprise the DerivativeClasses.
    ///
    /// The half-open ranges are represented by the (inclusive) lower bound of the
    /// range. The (exclusive) upper bound of a range is represented by the lower
    /// bound of the next range. Since the `DerivativeClasses` form a partition of
    /// the `Alphabet` this is well defined.
    ///
    /// The lower bound of the range is paired with the `TransitionLabel` applicable
    /// the subset to which this range belongs. In the general case, there will be
    /// multiple ranges that belong to the same subset and, hence, have the same
    /// `TransitionLabel`.
    pub fn ranges<'a>(&'a self) -> impl Iterator<Item = (A, TransitionLabel)> + 'a {
        self.map.ranges().map(|(a, label)| (a.clone(), *label))
    }
}
