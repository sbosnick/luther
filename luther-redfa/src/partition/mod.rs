// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::collections::{BTreeMap, Bound};
use std::fmt::Debug;
use std::iter::Peekable;

use alphabet::Alphabet;
use range::RangeArgument;

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
/// `Arc`).
///
/// [Lai]: http://hdl.handle.net/1721.1/45638
#[derive(Clone, Debug)]
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
    U: Alphabet + Debug,
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
            panic!(
                "Cannot create a PartionMap: range start is greater than range end: [{:?}, {:?}).",
                s, e
            );
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
        let right: Option<V>;
        let delete_left: Option<U>;
        let mut delete_right: Option<U> = None;
        let mut check_value: Option<V> = None;
        {
            let mut range = self.map.range_mut((Bound::Unbounded, Bound::Included(&u)));
            let (key, value) = range
                .next_back()
                .expect("Invalid PartitionMap: unable to get element.");

            let (l, r) = f(value.clone());
            assert_ne!(
                l, r,
                "Function passed to PartionMap::split() produced identical values."
            );

            let (l1, r1) = if *key == u && *value == r {
                (None, None)
            } else {
                match range.next_back() {
                    Some((_, ref v)) if **v != l && *key != u => {
                        *value = l;
                        (None, Some(r))
                    }
                    Some((_, ref v)) if **v != l => {
                        check_value = Some(r.clone());
                        *value = r;
                        (None, None)
                    }
                    Some((_, ref v)) if **v == l => (Some(key.clone()), Some(r)),
                    None if *value == r => (None, None),
                    _ => (None, Some(r)),
                }
            };
            delete_left = l1;
            right = r1;
        }

        if let Some(right) = right {
            self.map.insert(u.clone(), right.clone());
            delete_right = self.map
                .range((Bound::Excluded(&u), Bound::Unbounded))
                .next()
                .and_then(|(k, v)| if *v == right { Some(k.clone()) } else { None })
        } else if let Some(check_value) = check_value {
            delete_right = self.map
                .range((Bound::Excluded(&u), Bound::Unbounded))
                .next()
                .and_then(|(k, v)| {
                    if *v == check_value {
                        Some(k.clone())
                    } else {
                        None
                    }
                })
        }
        if let Some(delete_left) = delete_left {
            self.map.remove(&delete_left);
        }
        if let Some(delete_right) = delete_right {
            self.map.remove(&delete_right);
        }
    }
}

impl<U> PartitionMap<U, bool>
where
    U: Alphabet + Debug,
{
    /// Produce the union of the current `PartitionMap` and another one.
    ///
    /// An element in the resulting `PartitionMap` is true if it was true
    /// in either the orginal `PartitionMap` or in `other`. That is the result
    /// of `union` is `{self[u] or other [u] | ∀ u ∈ U}` where `or` is logical
    /// or.
    pub fn union(&self, other: &Self) -> Self {
        PartitionMap {
            map: UnionIntervalIter::new(self.map.range(..), other.map.range(..)).collect(),
        }
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

struct UnionIntervalIter<'a, U: 'a, L, R>
where
    L: Iterator<Item = (&'a U, &'a bool)>,
    R: Iterator<Item = (&'a U, &'a bool)>,
{
    left: Peekable<L>,
    right: Peekable<R>,
    last_vals: last_values::UnionLastVals,
}

impl<'a, U: 'a, L, R> UnionIntervalIter<'a, U, L, R>
where
    L: Iterator<Item = (&'a U, &'a bool)>,
    R: Iterator<Item = (&'a U, &'a bool)>,
{
    fn new(left: L, right: R) -> Self {
        UnionIntervalIter {
            left: left.peekable(),
            right: right.peekable(),
            last_vals: last_values::UnionLastVals::new(),
        }
    }
}

impl<'a, U: 'a, L, R> Iterator for UnionIntervalIter<'a, U, L, R>
where
    L: Iterator<Item = (&'a U, &'a bool)>,
    R: Iterator<Item = (&'a U, &'a bool)>,
    U: Ord + Clone + Debug,
{
    type Item = (U, bool);

    fn next(&mut self) -> Option<Self::Item> {
        #[derive(Debug)]
        enum Adv {
            Left,
            Right,
            Both,
            None,
        };
        
        let mut value = None;
        let mut key = None;

        while value.is_none() {
            let (k, v, adv) = match (self.left.peek(), self.right.peek()) {
                (Some(&(ul, vl)), Some(&(ur, _))) if ul < ur => {
                    let next_val = self.last_vals.next_value(Some(*vl), None);
                    (Some(ul.clone()), next_val, Adv::Left)
                }
                (Some(&(ul, _)), Some(&(ur, vr))) if ul > ur => {
                    let next_val = self.last_vals.next_value(None, Some(*vr));
                    (Some(ur.clone()), next_val, Adv::Right)
                }
                (Some(&(ul, vl)), Some(&(_ur, vr))) => {
                    // ul == ur
                    let next_val = self.last_vals.next_value(Some(*vl), Some(*vr));
                    (Some(ul.clone()), next_val, Adv::Both)
                }
                (Some(&(ul, vl)), None) => {
                    let next_val = self.last_vals.next_value(Some(*vl), None);
                    (Some(ul.clone()), next_val, Adv::Left)
                }
                (None, Some(&(ur, vr))) => {
                    let next_val = self.last_vals.next_value(None, Some(*vr));
                    (Some(ur.clone()), next_val, Adv::Right)
                }
                (None, None) => {
                    self.last_vals.next_value(None, None);
                    (None, None, Adv::None)
                }
            };

            key = k;
            value = v;

            match adv {
                Adv::Left => {
                    self.left.next();
                }
                Adv::Right => {
                    self.right.next();
                }
                Adv::Both => {
                    self.left.next();
                    self.right.next();
                }
                Adv::None => {
                    break;
                }
            }
        }

        match (key, value) {
            (Some(k), Some(v)) => Some((k, v)),
            (None, None) => None,
            kv => panic!(
                "Unexpect return value for UnionIntervalIter::next(): {:?}",
                kv
            ),
        }
    }
}

mod last_values;

#[cfg(test)]
mod test {
    use super::*;
    use itertools::Itertools;
    use proptest::collection;
    use proptest::prelude::*;

    // Simple types for use in unit tests

    #[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
    enum TestAlpha {
        A,
        B,
        C,
        D,
        E,
    }

    impl Alphabet for TestAlpha {
        fn min_value() -> Self {
            TestAlpha::A
        }

        fn max_value() -> Self {
            TestAlpha::E
        }

        fn increment(&self) -> Option<Self> {
            use self::TestAlpha::*;

            match self {
                &A => Some(B),
                &B => Some(C),
                &C => Some(D),
                &D => Some(E),
                &E => None,
            }
        }

        fn decrement(&self) -> Option<Self> {
            use self::TestAlpha::*;

            match self {
                &A => None,
                &B => Some(A),
                &C => Some(B),
                &D => Some(C),
                &E => Some(D),
            }
        }
    }

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
        use self::TestAlpha::*;

        let pm = TestPM::new(C..C, true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(!pm.map[&TestAlpha::A]);
    }

    #[test]
    fn empty_lower_bounded_range_paratition_map_includes_one_value() {
        use self::TestAlpha::*;

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
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        let pm = TestPM::new((Included(B), Included(C)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&B]);
        assert!(!pm.map[&D]);
    }

    #[test]
    fn excluded_lower_bounded_range_partition_map_includes_two_values() {
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        let pm = TestPM::new((Excluded(C), Unbounded), true, false);

        assert_eq!(pm.map.len(), 2);
        assert!(!pm.map[&A]);
        assert!(pm.map[&D]);
    }

    #[test]
    fn empty_excluded_lower_bounded_range_partiton_map_includes_one_value() {
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        let pm = TestPM::new((Excluded(E), Unbounded), true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(!pm.map[&A]);
    }

    #[test]
    fn excluded_lower_include_upper_bounded_range_partition_map_includes_three_values() {
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        let pm = TestPM::new((Excluded(B), Included(D)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&C]);
        assert!(!pm.map[&E]);
    }

    #[test]
    fn empty_excluded_lower_included_upper_bounded_range_partition_map_includes_one_value() {
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        let pm = TestPM::new((Excluded(D), Included(D)), true, false);

        assert_eq!(pm.map.len(), 1);
        assert!(!pm.map[&A]);
    }

    #[test]
    fn excluded_both_bounded_range_partition_map_includes_three_values() {
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        let pm = TestPM::new((Excluded(B), Excluded(D)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&C]);
        assert!(!pm.map[&D]);
    }

    #[test]
    #[should_panic]
    fn lower_bound_greater_than_upper_bound_panics() {
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        TestPM::new((Included(C), Excluded(B)), true, false);
    }

    #[test]
    #[should_panic]
    fn lower_exclusive_bound_equal_upper_exlusive_bound_panics() {
        use self::TestAlpha::*;
        use std::collections::Bound::*;

        TestPM::new((Excluded(C), Excluded(C)), true, false);
    }

    #[test]
    fn partion_map_gets_expected_values() {
        use self::TestAlpha::*;

        let pm = TestPM::new(B..D, true, false);

        assert!(!pm.get(&A));
        assert!(pm.get(&B));
        assert!(pm.get(&C));
        assert!(!pm.get(&D));
        assert!(!pm.get(&E));
    }

    #[test]
    fn partion_map_min_lower_bound_gets_all_true() {
        use self::TestAlpha::*;

        let pm = TestPM::new(A.., true, false);

        assert!(pm.get(&A));
        assert!(pm.get(&B));
        assert!(pm.get(&C));
        assert!(pm.get(&D));
        assert!(pm.get(&E));
    }

    #[test]
    fn split_partion_map_gets_expected_values() {
        use self::TestAlpha::*;

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
        use self::TestAlpha::*;

        let mut pm = TestPM::new(B.., 1, 0);
        pm.split(C, |_| (0, 1));

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&A] == 0);
        assert!(pm.map[&C] == 1);
    }

    #[test]
    fn split_partition_map_maintains_non_consectutive_values_to_right() {
        use self::TestAlpha::*;

        let mut pm = TestPM::new(..D, 0, 1);
        pm.split(C, |_| (0, 1));

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&A] == 0);
        assert!(pm.map[&C] == 1);
    }

    #[test]
    fn split_partition_map_maintains_non_consecutive_values_at_min_value() {
        use self::TestAlpha::*;

        let pm = TestPM::new(..C, true, false);
        let mut pm = pm.union(&TestPM::new(D.., true, false));
        pm.split(A, |_| (true, false));

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&A] == false);
        assert!(pm.map[&D] == true);
    }

    #[test]
    fn split_partition_map_maintains_non_consecutive_values_after_union() {
        use self::TestAlpha::*;

        let pm = TestPM::new(..C, true, false);
        let mut pm = pm.union(&TestPM::new(D.., true, false));
        pm.split(C, |_| (true, false));

        assert_eq!(pm.map.len(), 3);
        assert!(pm.map[&A] == true);
        assert!(pm.map[&C] == false);
        assert!(pm.map[&D] == true);
    }

    #[test]
    fn union_partition_map_gets_expected_values() {
        use self::TestAlpha::*;
        let other = TestPM::new(B..D, true, false);

        let sut = TestPM::new(C..E, true, false);
        let result = sut.union(&other);

        assert!(!*result.get(&A));
        assert!(*result.get(&B));
        assert!(*result.get(&C));
        assert!(*result.get(&D));
        assert!(!*result.get(&E));
    }

    #[test]
    fn union_interval_iter_has_sticky_true() {
        use self::TestAlpha::*;
        let left = vec![(&A, &true), (&B, &false)].into_iter();
        let right = vec![(&A, &true), (&C, &false)].into_iter();

        let mut sut = UnionIntervalIter::new(left, right.into_iter());
        sut.next();
        let result = sut.next();

        assert_matches!(result, Some((C, false)));
    }

    #[test]
    fn union_interval_iter_pairwise_has_sticky_true() {
        use self::TestAlpha::*;
        let left = vec![(&A, &true), (&B, &false), (&C, &false)].into_iter();
        let right = vec![(&A, &true), (&B, &true), (&C, &false)].into_iter();

        let mut sut = UnionIntervalIter::new(left, right.into_iter());
        sut.next();
        let result = sut.next();

        assert_matches!(result, Some((C, false)));
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
        Union((Bound<u8>, Bound<u8>)),
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
                Union(range) => arg.union(&PartitionMap::new(*range, true, false)),
            }
        }
    }

    fn arb_pm_op_vector() -> collection::VecStrategy<BoxedStrategy<PMOp>> {
        let pmop_strategy = prop_oneof![
            2 => any::<u8>().prop_map(PMOp::Split),
            1 => arb_u8_range().prop_map(PMOp::Union),
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
