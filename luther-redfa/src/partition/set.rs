// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::fmt::Debug;
use std::iter::{self, FromIterator};
use std::slice;

use arrayvec::ArrayVec;
use itertools::{self, Itertools};

use alphabet::Alphabet;
use partition::PartitionMap;
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
    ranges: Vec<U>,
}

// The implementation uses a vector of U to represent the included and excluded
// ranges in the set (hence why the vector is called 'ranges'). The elements of the
// vector are the inclusive lower bound of the range where the exclusive upper bound
// is the lower bound of the next range (or one past U::max_value() for the last element
// of the vector). The vector is sorted in increasing order and each lower bound appears
// at most once.
//
// The even numbered indexes of 'ranges' are the included ranges and the odd numbered
// indexes are the excluded ranges. If 'ranges.len() == 0' or if 'ranges[0] != U::min_value()'
// then there is an implicit first range starting at U::min_value() that is excluded.
impl<U: Alphabet> PartitionSet<U> {
    pub fn full_singleton() -> PartitionSet<U> {
        PartitionSet {
            ranges: vec![U::min_value()],
        }
    }

    pub fn contains(&self, u: &U) -> bool {
        match self.ranges.binary_search(u) {
            Ok(idx) => idx %2 == 0,
            Err(idx) => idx %2 == 1,
        }
    }

    pub fn is_complement_empty(&self) -> bool {
        self.ranges.len() == 1 && self.ranges.contains(&U::min_value())
    }

    pub fn union(&self, other: &PartitionSet<U>) -> PartitionSet<U> {
        use itertools::EitherOrBoth::{Left, Right, Both};
        use self::ElementStatus::{Included, Excluded};

        let mut left = Excluded;
        let mut right = Excluded;

        PartitionSet {
            ranges: itertools::merge_join_by(
                        self.ranges.iter().enumerate(),
                        other.ranges.iter().enumerate(), 
                        |(_, l), (_, r)| l.cmp(r))
                .filter_map(|item| match item {
                    Left((i,v)) if is_even(i) => {
                        left = Included;
                        emit(right, v)
                    }
                    Right((i,v)) if is_even(i) => {
                        right = Included;
                        emit(left, v)
                    }
                    Left((_,v)) => {
                        left = Excluded;
                        emit(right, v)
                    }
                    Right((_,v)) => {
                        right = Excluded;
                        emit(left, v)
                    }
                    Both((i,v), (j,_)) if is_even(i) && is_even(j) => {
                        let result = emit_both(left, right, v);
                        left = Included;
                        right = Included;
                        result
                    }
                    Both((i,v), (j,_)) if !is_even(i) && is_even(j) => {
                        let result = emit_both(left, right, v);
                        left = Excluded;
                        right = Included;
                        result
                    }
                    Both((i,v), (j,_)) if is_even(i) && !is_even(j) => {
                        let result = emit_both(left, right, v);
                        left = Included;
                        right = Excluded;
                        result
                    }
                    Both((_,v), (_,_)) => {
                        let result = emit_included(left, right, v);
                        left = Excluded;
                        right = Excluded;
                        result
                    }
                })
                .cloned()
                .collect(),
        }
    }

    pub fn complement(&self) -> PartitionSet<U> {
        PartitionSet {
            ranges: if self.ranges.contains(&U::min_value()) {
                self.ranges.iter().skip(1).cloned().collect()
            } else {
                iter::once(U::min_value()).chain(self.ranges.iter().cloned()).collect()
            }
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
        use self::ElementStatus::*;

        let pre = if self.ranges.len() == 0 || !self.ranges.contains(&U::min_value()) {
            Some((U::min_value(), Excluded))
        } else {
            None
        };

        pre.into_iter().chain(
            self.ranges.iter().enumerate().map(|(i, val)| {
                (val.clone(), if i % 2 == 0 { Included } else { Excluded})
            })
        )

    }
}

impl<U: Alphabet> FromIterator<Range<U>> for PartitionSet<U> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Range<U>>,
    {
        PartitionSet {
            ranges: iter.into_iter()
                .sorted_by_key(|range| range.start())
                .into_iter()
                .coalesce(|prev, curr| prev.coalesce(&curr))
                .flat_map(|item| {
                    let mut array = ArrayVec::<[_;2]>::new();
                    array.push(item.start());
                    item.end().increment().map(|end| array.push(end));
                    array
                })
                .collect(),
        }
    }
}

impl<'a, U: Alphabet> IntoIterator for &'a PartitionSet<U> {
    type Item = Range<U>;
    type IntoIter = PartitionSetRangeIter<'a, U>;

    fn into_iter(self) -> Self::IntoIter {
        PartitionSetRangeIter {
            inner: self.ranges.iter(),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum ElementStatus {
    Included,
    Excluded,
}

pub struct PartitionSetRangeIter<'a, U: 'a + Alphabet> {
    inner: slice::Iter<'a, U>,
}

impl<'a, U: Alphabet> Iterator for PartitionSetRangeIter<'a, U> {
    type Item = Range<U>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
            .map(|start| {
                let end = self.inner.next().map_or(U::max_value(), |end| {
                    end.decrement()
                        .expect("U::min_value() found in locaiton other than the first one")
                });
                Range::new(start.clone(), end)
            })
    }
}

fn is_even(i: usize) -> bool {
    i%2 == 0
}

fn emit<T>(status: ElementStatus, value: T) -> Option<T> {
    if status == ElementStatus::Excluded {
        Some(value)
    } else {
        None
    }
}

fn emit_both<T>(left : ElementStatus, right: ElementStatus, value: T) -> Option<T> {
    if left == ElementStatus::Excluded && right == ElementStatus::Excluded {
        Some(value)
    } else {
        None
    }
}

fn emit_included<T>(left: ElementStatus, right: ElementStatus, value: T) -> Option<T> {
    if left == ElementStatus::Included || right == ElementStatus::Included {
        Some(value)
    } else {
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::iter;
    use testutils;
    use proptest::prelude::*;
    use proptest::collection;
    use partition::map_get;

    #[test]
    fn partition_set_into_map_gets_expected_values() {
        use testutils::TestAlpha::*;

        let sut = PartitionSet::from_iter(vec![Range::new(B, C)]);
        let map = sut.into_map(0, 1);

        assert_eq!(*map_get(&map, &A), 1);
        assert_eq!(*map_get(&map, &B), 0);
        assert_eq!(*map_get(&map, &C), 0);
        assert_eq!(*map_get(&map, &D), 1);
        assert_eq!(*map_get(&map, &E), 1);
    }

    #[test]
    fn partition_set_contains_expected_values() {
        use testutils::TestAlpha::*;
        let range = vec![Range::new(B, C)];

        let sut = PartitionSet::from_iter(range);

        assert!(!sut.contains(&A));
        assert!(sut.contains(&B));
        assert!(sut.contains(&C));
        assert!(!sut.contains(&D));
        assert!(!sut.contains(&E));
    }

    #[test]
    fn partition_set_from_empty_ranges_is_empty() {
        let range = iter::empty::<Range<u8>>();

        let sut: PartitionSet<_> = range.collect();

        assert_eq!(sut.into_iter().count(), 0);
    }

    #[test]
    fn partition_set_full_singleton_contains_all_values() {
        use testutils::TestAlpha::*;

        let sut = PartitionSet::full_singleton();

        assert!(sut.contains(&A));
        assert!(sut.contains(&B));
        assert!(sut.contains(&C));
        assert!(sut.contains(&D));
        assert!(sut.contains(&E));
    }

    #[test]
    fn partition_set_complement_of_empty_is_complement_empty() {
        let range = iter::empty::<Range<testutils::TestAlpha>>();

        let sut: PartitionSet<_> = range.collect();
        let complement = sut.complement();

        assert!(complement.is_complement_empty());
    }

    #[test]
    fn partition_set_union_iterates_expected_values() {
        use testutils::TestAlpha::*;
        let set1 = PartitionSet::from_iter(vec![Range::new(B, C)]);
        let set2 = PartitionSet::from_iter(vec![Range::new(C, D)]);

        let sut = set1.union(&set2);
        let results: Vec<_> = sut.into_iter().collect();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0], Range::new(B, D));
    }

    #[test]
    fn partition_set_union_with_adjacent_ranges_contains_expected_values() {
        use testutils::TestAlpha::*;
        let set1 = PartitionSet::from_iter(iter::once(Range::new(C,C)));
        let set2 = PartitionSet::from_iter(iter::once(Range::new(D,D)));

        let sut = set1.union(&set2);

        assert!(!sut.contains(&A));
        assert!(!sut.contains(&B));
        assert!(sut.contains(&C));
        assert!(sut.contains(&D));
        assert!(!sut.contains(&E));
    }

    // Strategy defintions for property tests

    prop_compose!{
        fn arb_range()(lower in any::<u8>())
            (lower in Just(lower), upper in lower..)
            -> Range<u8> 
            {
                Range::new(lower, upper)
            }
    }

    prop_compose!{
        fn arb_partiton_set()
            (ranges in collection::vec(arb_range(), collection::size_range(..10)))
            -> PartitionSet<u8>
            {
                PartitionSet::from_iter(ranges)
            }
    }

    // Property tests

    proptest! {
        #[test]
        fn prop_partition_set_union_contains_values_from_sources(
            set1 in arb_partiton_set(),
            set2 in arb_partiton_set(),
            )
        {
            let union = set1.union(&set2);

            for i in (0..256).map(|x| x as u8) {
                prop_assert_eq!(
                    union.contains(&i),
                    set1.contains(&i) || set2.contains(&i),
                    "union is {:?}; i is {}",
                    union, i);
            }
        }

        #[test]
        fn prop_partition_set_from_ranges_has_ascenting_inner_ranges(
            ranges in collection::vec(arb_range(), collection::size_range(..10)))
        {
            let sut = PartitionSet::from_iter(ranges);

            for (first, second) in sut.ranges.iter().tuple_windows() {
                prop_assert!( first < second, "set is {:?}", sut);
            }
        }
    }
}
