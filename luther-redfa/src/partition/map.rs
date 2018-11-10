// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::collections::{btree_map, BTreeMap, Bound};
use std::fmt::Debug;

use alphabet::Alphabet;
use range::RangeArgument;

use super::{merge_iter, MergeValue};

/// A `PartitionMap` is an effecient map from all elements of `U` to a value
/// from `V`.
///
/// # Type Parameters
/// | U | The universe to map to values                       |
/// | V | The values to which to map elements of the universe |
///
/// Both U and V must be `Clone`, but the `clone` implemtation should be an effecient
/// one. It is likely that most useful types for U are `Copy`, but there may be a useful
/// type for V that is not `Copy` but has an inexpensive `Clone` implementation (i.e.
/// `Arc`). U must also be and `Alphabet`.
#[derive(Clone, Debug, PartialEq, PartialOrd, Hash, Eq)]
pub struct PartitionMap<U, V> {
    map: BTreeMap<U, V>,
}

// PartitionMap is implemented by storing the lower bound of the half open interval
// [a, b), where a ∈ U and b ∈ U ∪ U::max_value() + 1. That is, b is either an element
// of U or is 1 past the last element of U. Since we are just storing the lower bound
// of the interval, the upper bound (the half open end) can remain implicit.
//
// A PartitionMap is intented to partition U and then map each subset in the partition
// to some value from V. The implementaiton must ensure that every value from U is mapped to
// some value from V. This is done with by mataining the following invarient:
//
//  1.  Every PartitionMap must contain an interval [U::min_value(), b) for some b.
//
// Since we store intervals by storing the lower bound of the interval, this means that we
// must store U::min_value() in every PartitionMap.
//
// We also want to minimize the number of intervals the we explicitly store so we also maintain
// the following invarient:
//
//  2.  No PartitionMap will contain two intervals [a, b) and [b, c) that both map to
//      the same element of V.
//
//  We store the mapping from an interval to its value as a BTreeMap from the lower
//  bound to the value and also storing the upper bound (assuming it is not U::max_value() + 1)
//  as a map to some different value. invarient 2 then translates into the requiment that
//  successive values in the BTreeMap be distinct when iterated in order by key (i.e.
//  when you use BTreeMap::values()).
impl<U, V> PartitionMap<U, V>
where
    U: Alphabet,
    V: Clone + Debug + PartialEq,
{
    /// Creates a new `PartitionMap` where the elements in `range` have `in_value` and all other
    /// elements have `out_value`.
    ///
    /// # Panics
    /// `new` will panic if the range start is greater than the range end, or if the start and end
    /// are equal and both ends of the range are exclusive. It will also panic if `in_value` and
    /// `out_value` are equal.
    pub fn new<R: RangeArgument<U>>(range: R, in_value: V, out_value: V) -> PartitionMap<U, V> {
        let (s, e, v) = map_range(range.start(), range.end(), &in_value, &out_value);
        if s > e && e.is_some() {
            panic!("Cannot create a PartionMap: range start is greater than range end.");
        }

        assert_ne!(
            in_value, out_value,
            "in_value and out_value cannot be the same in PartionMap::new()"
        );

        let mut map = BTreeMap::new();
        map.insert(U::min_value(), v);
        s.map(|s| map.insert(s, in_value));
        e.map(|e| map.insert(e, out_value));

        PartitionMap { map }
    }

    pub fn ranges(&self) -> impl Iterator<Item = (&U, &V)> {
        self.map.range(..)
    }
}

impl<U, V> PartitionMap<U, V>
where
    U: Alphabet,
    V: Clone,
{
    /// Creates a new `PartitionMap` from the ranges identifed by the consectutive lower bound,
    /// value pairs.
    pub fn from_lower_bound_iter<I>(iter: I) -> PartitionMap<U,V> 
        where I: IntoIterator<Item=(U,V)>,
    {
        PartitionMap {
            map: iter.into_iter().collect(),
        }
    }

    pub fn from_merge<I, J, M>(left: I, right: J, merge: &mut M) -> PartitionMap<U, V>
    where
        I: IntoIterator<Item = (U, V)>,
        J: IntoIterator<Item = (U, V)>,
        M: MergeValue<V>,
    {
        PartitionMap::from_lower_bound_iter(merge_iter(left, right, merge))
    }

}

impl<U, V> IntoIterator for PartitionMap<U, V>
where
    U: Alphabet,
    V: Clone,
{
    type Item = (U, V);
    type IntoIter = btree_map::IntoIter<U, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

fn map_range<U, V>(
    start: Bound<&U>,
    end: Bound<&U>,
    in_value: &V,
    out_value: &V,
) -> (Option<U>, Option<U>, V)
where
    U: Alphabet,
    V: Clone,
{
    use std::collections::Bound::*;

    match (start, end) {
        (Unbounded, Unbounded) => (None, None, in_value.clone()),
        (Unbounded, Included(e)) => (None, e.clone().increment(), in_value.clone()),
        (Unbounded, Excluded(e)) => {
            let (e, v) = check_min_value(e, out_value, in_value);
            (None, e, v)
        }
        (Included(s), Unbounded) => {
            let (s, v) = check_min_value(s, in_value, out_value);
            (s, None, v)
        }
        (Included(s), Included(e)) => {
            let (s, v) = check_min_value(s, in_value, out_value);
            let e = e.clone().increment();
            (s, e, v)
        }
        (Included(s), Excluded(e)) if s == e => (None, None, out_value.clone()),
        (Included(s), Excluded(e)) => {
            let (s, v) = check_min_value(s, in_value, out_value);
            let e = e.clone();
            (s, Some(e), v)
        }
        (Excluded(s), Unbounded) => (s.clone().increment(), None, out_value.clone()),
        (Excluded(s), Included(e)) if s == e => (None, None, out_value.clone()),
        (Excluded(s), Included(e)) => (
            s.clone().increment(),
            e.clone().increment(),
            out_value.clone(),
        ),
        (Excluded(s), Excluded(e)) => (s.clone().increment(), Some(e.clone()), out_value.clone()),
    }
}

fn check_min_value<U: Alphabet, V: Clone>(u: &U, v_min: &V, v_not_min: &V) -> (Option<U>, V) {
    if *u == U::min_value() {
        (None, v_min.clone())
    } else {
        (Some(u.clone()), v_not_min.clone())
    }
}

#[cfg(test)]
pub fn map_get<'a, U: Ord, V>(map: &'a PartitionMap<U,V>, u: &U) -> &'a V 
{
    map.map
        .range((Bound::Unbounded, Bound::Included(u)))
        .next_back()
        .expect("Invalid PartionMap: unable to get element.")
        .1
}

#[cfg(test)]
mod test {
    use super::*;
    use testutils::*;

    // Simple types for use in unit tests

    type TestPM<V> = PartitionMap<TestAlpha, V>;

    // Unit tests

    #[test]
    fn full_range_partition_map_includes_just_min_value() {
        let pm = TestPM::new(.., true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(pm.map[&TestAlpha::A]);
    }

    #[test]
    fn lower_bounded_range_partition_map_includes_two_values() {
        let pm = TestPM::new(TestAlpha::B.., true, false);

        assert_eq!(pm.map.len(), 2);
        assert!(!pm.map[&TestAlpha::A]);
        assert!(pm.map[&TestAlpha::B]);
    }

    #[test]
    fn upper_bounded_range_partition_map_includes_two_values() {
        let pm = TestPM::new(..TestAlpha::C, true, false);

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&TestAlpha::A]);
        assert!(!pm.map[&TestAlpha::C]);
    }

    #[test]
    fn bounded_range_partition_map_includes_three_values() {
        let pm = TestPM::new(TestAlpha::B..TestAlpha::D, true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&TestAlpha::A]);
        assert!(pm.map[&TestAlpha::B]);
        assert!(!pm.map[&TestAlpha::D]);
    }

    #[test]
    fn empty_bounded_range_partition_map_includes_one_value() {
        use testutils::TestAlpha::*;

        let pm = TestPM::new(C..C, true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(!pm.map[&TestAlpha::A]);
    }

    #[test]
    fn empty_lower_bounded_range_paratition_map_includes_one_value() {
        use testutils::TestAlpha::*;

        let pm = TestPM::new(..A, true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(!pm.map[&TestAlpha::A]);
    }

    #[test]
    fn included_upper_bounded_range_partition_map_includes_two_values() {
        use std::collections::Bound::*;

        let pm = TestPM::new((Unbounded, Included(TestAlpha::C)), true, false);

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&TestAlpha::A]);
        assert!(!pm.map[&TestAlpha::D]);
    }

    #[test]
    fn included_both_bounded_range_partition_map_includes_three_values() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        let pm = TestPM::new((Included(B), Included(C)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&B]);
        assert!(!pm.map[&D]);
    }

    #[test]
    fn excluded_lower_bounded_range_partition_map_includes_two_values() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        let pm = TestPM::new((Excluded(C), Unbounded), true, false);

        assert_eq!(pm.map.len(), 2);
        assert!(!pm.map[&A]);
        assert!(pm.map[&D]);
    }

    #[test]
    fn empty_excluded_lower_bounded_range_partiton_map_includes_one_value() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        let pm = TestPM::new((Excluded(E), Unbounded), true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(!pm.map[&A]);
    }

    #[test]
    fn excluded_lower_include_upper_bounded_range_partition_map_includes_three_values() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        let pm = TestPM::new((Excluded(B), Included(D)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&C]);
        assert!(!pm.map[&E]);
    }

    #[test]
    fn empty_excluded_lower_included_upper_bounded_range_partition_map_includes_one_value() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        let pm = TestPM::new((Excluded(D), Included(D)), true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(!pm.map[&A]);
    }

    #[test]
    fn excluded_both_bounded_range_partition_map_includes_three_values() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        let pm = TestPM::new((Excluded(B), Excluded(D)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&C]);
        assert!(!pm.map[&D]);
    }
}
