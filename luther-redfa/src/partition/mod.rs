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
use itertools;
use range::RangeArgument;

pub use self::set::PartitionSet;
pub use self::set::PartitionSetRangeIter;

mod set;

/// A `PartitionMap` is an effecient map from all elements of `U` to a value
/// from `V`.
///
/// The mapping is achived by mapping an interval of of elements of the universe
/// to the same value. This provides an implementation of a simplified version
/// of the union-split-find problem. More specifically this (attepts to) implement
/// the "Interval Union-Split-Find Problem" described in [_Complexity of
/// Union-Split-Find Problems_][Lai].
///
/// # Type Parameters
/// | U | The universe to map to values                       |
/// | V | The values to which to map elements of the universe |
///
/// Both U and V must be `Clone`, but the `clone` implemtation should be an effecient
/// one. It is likely that most useful types for U are `Copy`, but there may be a useful
/// type for V that is not `Copy` but has an inexpensive `Clone` implementation (i.e.
/// `Arc`). U must also be and `Alphabet`.
///
/// [Lai]: http://hdl.handle.net/1721.1/45638
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

    /// Creates a new `PartitionMap` from the ranges identifed by the consectutive lower bound,
    /// value pairs.
    pub fn from_lower_bound_iter<I>(iter: I) -> PartitionMap<U,V> 
        where I: IntoIterator<Item=(U,V)>,
    {
        PartitionMap {
            map: iter.into_iter().collect(),
        }
    }

    /// Gets the value associated with an element of U.
    pub fn get(&self, u: &U) -> &V {
        self.map
            .range((Bound::Unbounded, Bound::Included(u)))
            .next_back()
            .expect("Invalid PartionMap: unable to get element.")
            .1
    }

    /// Splits the partition at `u` using `f` to map the resulting values.
    ///
    /// The interval that `u` is in is split at `u`. That is, assuming that
    /// `u` falls in the interval [a, b) then the patition is split to include
    /// intervals [a,u) and [u, b). The value mapping function `f` maps the
    /// current value of the elements of the interval to a pair of values,
    /// one for each side of the split.
    ///
    /// # Panics
    /// `split` will panic if `f` produces two identical values.
    pub fn split<F>(&mut self, u: U, f: F)
    where
        F: Fn(V) -> (V, V),
    {
        let (delete_left, insert_right, check_right) = {
            let ((key, value), prior) = get_current_and_prior_intervals(u.clone(), &mut self.map);
            let (l, r) = get_values(value.clone(), f);

            // adjust the value of the current interval, if it is the
            // first interval or if the prior interval value matches
            // the new left value
            prior
                .clone()
                .filter(|(_, ref v)| *v == l.clone())
                .or_else(|| {
                    *value = if key == u {
                        r.clone()
                    } else {
                        l.clone()
                    };
                    None
                });

            // select the insertions and deletions to the left and right
            match prior {
                // split point was already present in the map and is not the first entry
                Some((_, ref v)) if key == u && *v != r => (None, None, Some(r)),
                Some((_, ref v)) if key == u && *v == r => (Some(key), None, Some(r)),

                // split point not present in map and its interval is not the first entry
                Some((_, ref v)) if *v == l => (Some(key), Some(r), None),
                Some(_) => (None, Some(r), None),

                // split point already present in the map as the first entry
                None if key == u => (None, None, Some(r)),

                // interval of split point is the first entry
                None => (None, Some(r), None),
            }
        };

        // insert and delete to the right
        insert_right
            .map(|value| self.insert_value(u.clone(), value))
            .or(check_right)
            .and_then(|value| get_next_interval_key_if_value(u, value, &self.map))
            .map(|key| self.delete_key(key));

        // delete to the left
        delete_left.map(|key| self.delete_key(key));
    }

    fn insert_value(&mut self, u: U, v: V) -> V {
        self.map.insert(u, v.clone());
        v
    }

    fn delete_key(&mut self, u: U) {
        self.map.remove(&u);
    }

    pub fn ranges(&self) -> impl Iterator<Item = (&U, &V)> {
        self.map.range(..)
    }
}

impl<'a, 'b, U, V> PartitionMap<U, V>
where
    U: Alphabet + 'a + 'b,
    V: Clone + 'a + 'b,
{
    pub fn from_merge<I, J, M>(left: I, right: J, merge: &mut M) -> PartitionMap<U, V>
    where
        I: IntoIterator<Item = (U, V)>,
        J: IntoIterator<Item = (U, V)>,
        M: MergeValue<V>,
    {
        use itertools::EitherOrBoth::*;

        PartitionMap {
            map: itertools::merge_join_by(left, right, |(l, _), (r, _)| l.cmp(r))
                .map(|value| match value {
                    Left((u, v)) => (u, merge.next_left(v)),
                    Right((u, v)) => (u, merge.next_right(v)),
                    Both((u, vl), (_, vr)) => (u, merge.next_both(vl, vr)),
                })
                .collect(),
        }
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

pub trait MergeValue<V> {
    fn next_left(&mut self, v: V) -> V;
    fn next_right(&mut self, v: V) -> V;
    fn next_both(&mut self, left: V, right: V) -> V;
}

fn get_values<V, F>(v: V, f: F) -> (V, V)
where
    V: PartialEq + Debug,
    F: Fn(V) -> (V, V),
{
    let (l, r) = f(v);
    assert_ne!(
        l, r,
        "Function passed to PartitionMap::split() produced idential values."
    );
    (l, r)
}

fn get_current_and_prior_intervals<U: Ord + Clone, V: Clone>(
    u: U,
    map: &mut BTreeMap<U, V>,
) -> ((U, &mut V), Option<(U, V)>) {
    let mut range = map.range_mut((Bound::Unbounded, Bound::Included(&u)));
    let (key, value) = range
        .next_back()
        .expect("Invalid PartionMap: unable to get element.");
    (
        (key.clone(), value),
        range.next_back().map(|(k, v)| (k.clone(), v.clone())),
    )
}

fn get_next_interval_key_if_value<U: Ord + Clone, V: PartialEq>(
    u: U,
    value: V,
    map: &BTreeMap<U, V>,
) -> Option<U> {
    map.range((Bound::Excluded(&u), Bound::Unbounded))
        .next()
        .and_then(|(k, v)| if *v == value { Some(k.clone()) } else { None })
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
mod test {
    use super::*;
    use itertools::Itertools;
    use proptest::collection;
    use proptest::prelude::*;
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

    #[test]
    #[should_panic]
    fn lower_bound_greater_than_upper_bound_panics() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        TestPM::new((Included(C), Excluded(B)), true, false);
    }

    #[test]
    #[should_panic]
    fn lower_exclusive_bound_equal_upper_exlusive_bound_panics() {
        use std::collections::Bound::*;
        use testutils::TestAlpha::*;

        TestPM::new((Excluded(C), Excluded(C)), true, false);
    }

    #[test]
    fn partion_map_gets_expected_values() {
        use testutils::TestAlpha::*;

        let pm = TestPM::new(B..D, true, false);

        assert!(!pm.get(&A));
        assert!(pm.get(&B));
        assert!(pm.get(&C));
        assert!(!pm.get(&D));
        assert!(!pm.get(&E));
    }

    #[test]
    fn partion_map_min_lower_bound_gets_all_true() {
        use testutils::TestAlpha::*;

        let pm = TestPM::new(A.., true, false);

        assert!(pm.get(&A));
        assert!(pm.get(&B));
        assert!(pm.get(&C));
        assert!(pm.get(&D));
        assert!(pm.get(&E));
    }

    struct Value(u8);

    impl MergeValue<u8> for Value {
        fn next_left(&mut self, _: u8) -> u8 {
            self.0 += 1;
            self.0
        }

        fn next_right(&mut self, _: u8) -> u8 {
            self.0 += 1;
            self.0
        }

        fn next_both(&mut self, _: u8, _: u8) -> u8 {
            self.0 += 1;
            self.0
        }
    }

    #[test]
    fn patition_map_from_merge_get_expected_values() {
        use testutils::TestAlpha::*;
        let left = TestPM::new(B..C, 0, 1);
        let right = TestPM::new(C..D, 3, 5);
        let mut merge = Value(0);

        let sut = TestPM::from_merge(left, right, &mut merge);

        assert_eq!(*sut.get(&A), 1);
        assert_eq!(*sut.get(&B), 2);
        assert_eq!(*sut.get(&C), 3);
        assert_eq!(*sut.get(&D), 4);
        assert_eq!(*sut.get(&E), 4);
    }

    #[test]
    fn split_partion_map_gets_expected_values() {
        use testutils::TestAlpha::*;

        let mut pm = TestPM::new(B..E, 1, 0);
        pm.split(D, |v| (v, 5));

        assert_eq!(*pm.get(&A), 0);
        assert_eq!(*pm.get(&B), 1);
        assert_eq!(*pm.get(&C), 1);
        assert_eq!(*pm.get(&D), 5);
        assert_eq!(*pm.get(&E), 0);
    }

    #[test]
    fn split_partition_map_maintains_non_consectutive_values_to_left() {
        use testutils::TestAlpha::*;

        let mut pm = TestPM::new(B.., 1, 0);
        pm.split(C, |_| (0, 1));

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&A] == 0);
        assert!(pm.map[&C] == 1);
    }

    #[test]
    fn split_partition_map_maintains_non_consectutive_values_to_right() {
        use testutils::TestAlpha::*;

        let mut pm = TestPM::new(..D, 0, 1);
        pm.split(C, |_| (0, 1));

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&A] == 0);
        assert!(pm.map[&C] == 1);
    }

    #[test]
    fn split_partition_map_maintains_non_consecutive_values_at_initial_divide() {
        use testutils::TestAlpha::*;

        let mut pm = TestPM::new(C.., true, false);
        pm.split(C, |_| (true, false));

        assert_eq!(pm.map.len(), 1);
        assert!(pm.map[&A] == false);
    }

    // Types and Strategy defintions for property tests

    prop_compose!{
        fn arb_u8_range()(lower in any::<u8>())
            (lower in Just(lower), upper in lower.., kind in 0u8..4)
            -> (Bound<u8>, Bound<u8>) {
                use std::collections::Bound::*;
                match kind {
                    0 => (Unbounded, Unbounded),
                    1 => (Included(lower), Unbounded),
                    2 => (Unbounded, Excluded(upper)),
                    _ => (Included(lower), Excluded(upper)),
                }
            }
    }

    prop_compose!{
        fn arb_partition_map()(range in arb_u8_range())
            -> PartitionMap<u8, bool> {
                PartitionMap::new(range, true, false)
        }
    }

    #[derive(Clone, Debug)]
    enum PMOp {
        Split(u8),
    }

    impl PMOp {
        fn run(&self, arg: &PartitionMap<u8, bool>) -> PartitionMap<u8, bool> {
            use self::PMOp::*;

            match self {
                Split(point) => {
                    let mut arg = arg.clone();
                    arg.split(*point, |_| (true, false));
                    arg
                }
            }
        }
    }

    fn arb_pm_op_vector() -> collection::VecStrategy<BoxedStrategy<PMOp>> {
        let pmop_strategy = prop_oneof![
            2 => any::<u8>().prop_map(PMOp::Split),
        ];

        collection::vec(pmop_strategy.boxed(), ..10)
    }

    // Property tests and supporting functions

    proptest! {
        #[test]
        fn prop_partition_map_contains_min_value(
            pm in arb_partition_map(),
            ops in arb_pm_op_vector()
            )
        {
            let mut pm: PartitionMap<u8,bool> = pm.clone();
            for op in ops {
                pm = op.run(&pm);
            }

            prop_assert!(pm.map.contains_key(&0));
        }

        #[test]
        fn prop_partition_map_values_alternate(
            pm in arb_partition_map(),
            ops in arb_pm_op_vector())
        {
            let mut pm: PartitionMap<u8,bool> = pm.clone();
            for op in ops {
                pm = op.run(&pm);
            }

            for (first, second) in pm.map.values().tuple_windows() {
                prop_assert_ne!(first, second);
            }
        }
    }
}
