// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::fmt::Debug;
use std::iter::FromIterator;

use alphabet::Alphabet;
use partition::{PartitionMap, PartitionMapRangeIter};
use regex::Range;

/// A `PartitionSet` is a set of `U`.
///
/// # Type Parameter
/// | U | The universe to partition to determine set membership |
///
/// U must be `Clone` but the `clone` implementation should be an efficient one. It is
/// likely that most useful types for U are `Copy`. U must also be an `Alphabet`.
#[derive(Clone, Debug, PartialEq, PartialOrd, Hash, Eq)]
pub struct PartitionSet<U> {
    map: PartitionMap<U, bool>,
}

impl<U: Alphabet> PartitionSet<U> {
    pub fn full_singleton() -> PartitionSet<U> {
        PartitionSet {
            map: PartitionMap::new(.., true, false),
        }
    }

    pub fn contains(&self, u: &U) -> bool {
        self.map.get(u).clone()
    }

    pub fn is_complement_empty(&self) -> bool {
        self.map.is_complement_empty()
    }

    pub fn union(&self, other: &PartitionSet<U>) -> PartitionSet<U> {
        PartitionSet {
            map: self.map.union(&other.map),
        }
    }

    pub fn complement(&self) -> PartitionSet<U> {
        PartitionSet {
            map: self.map.complement(),
        }
    }

    pub fn into_map<V>(&self, in_value: V, out_value: V) -> PartitionMap<U, V>
    where
        V: Debug + Clone + PartialEq,
    {
        use self::ElementStatus::*;

        PartitionMap::from_lower_bound_iter(
                self.lower_bound_iter()
                .map(|(u, status)| {
                    (
                        u, 
                        match status {
                            Included => in_value.clone(),
                            Excluded => out_value.clone(),
                        },
                    )
                })
        )

    }

    pub fn lower_bound_iter<'a>(&'a self) -> impl Iterator<Item=(U, ElementStatus)> + 'a {
        self.map.ranges()
            .map(|(u,v)| (u.clone(), if *v { ElementStatus::Included } else { ElementStatus::Excluded}))
    }
}

impl<U: Alphabet> FromIterator<Range<U>> for PartitionSet<U> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Range<U>>,
    {
        PartitionSet {
            map: iter.into_iter().collect(),
        }
    }
}

impl<'a, U: Alphabet> IntoIterator for &'a PartitionSet<U> {
    type Item = Range<U>;
    type IntoIter = PartitionSetRangeIter<'a, U>;

    fn into_iter(self) -> Self::IntoIter {
        PartitionSetRangeIter {
            inner: self.map.range_iter(),
        }
    }
}

pub enum ElementStatus {
    Included,
    Excluded,
}

pub struct PartitionSetRangeIter<'a, U: 'a + Alphabet> {
    inner: PartitionMapRangeIter<'a, U>,
}

impl<'a, U: Alphabet> Iterator for PartitionSetRangeIter<'a, U> {
    type Item = Range<U>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}
