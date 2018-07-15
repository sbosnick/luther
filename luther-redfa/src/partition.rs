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

use range::RangeArgument;
use alphabet::Alphabet;

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
#[derive(Debug)]
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
            in_value,
            out_value,
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
        let right;
        {
            let (key, value) = self.map
                .range_mut((Bound::Unbounded, Bound::Included(&u)))
                .next_back()
                .expect("Invalid PartitionMap: unable to get element.");

            let (l, r) = f(value.clone());
            assert_ne!(
                l,
                r,
                "Function passed to PartionMap::split() produced identical values."
            );

            if *key != u {
                *value = l;
            }
            right = r;
        }
        self.map.insert(u, right);
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
        (Included(s), Excluded(e)) => {
            let (s, v) = check_min_value(s, in_value, out_value);
            let e = e.clone();
            (s, Some(e), v)
        }
        (Excluded(s), Unbounded) => (s.clone().increment(), None, out_value.clone()),
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
    last_vals: Option<(bool, bool)>,
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
            last_vals: None,
        }
    }

    fn set_both_last_vals(&mut self, left: bool, right: bool) {
        self.last_vals = Some((left, right));
    }

    fn set_left_last_val(&mut self, left: bool) {
        let (_, right) = self.last_vals
            .expect("set_left_last_val() called before set_both_last_vals()");
        self.last_vals = Some((left, right));
    }

    fn set_right_last_val(&mut self, right: bool) {
        let (left, _) = self.last_vals
            .expect("set_right_last_val() called before set_both_last_vals()");
        self.last_vals = Some((left, right));
    }

    fn set_none_last_vals(&mut self) {
        self.last_vals = None;
    }

    fn next_left_value(&mut self, value: bool) -> Option<bool> {
        let result = self.last_vals.map_or(Some(value), |(left, right)| {
            if !(left || right) && value {
                Some(value)
            } else if !right && !value {
                Some(value)
            } else {
                None
            }
        });

        self.set_left_last_val(value);
        result
    }

    fn next_right_value(&mut self, value: bool) -> Option<bool> {
        let result = self.last_vals.map_or(Some(value), |(left, right)| {
            if !(left || right) && value {
                Some(value)
            } else if !left && !value {
                Some(value)
            } else {
                None
            }
        });

        self.set_right_last_val(value);
        result
    }

    fn next_both_value(&mut self, newleft: bool, newright: bool) -> Option<bool> {
        let result = self.last_vals
            .map_or(Some(newleft || newright), |(left, right)| {
                if !(left || right) && (newleft || newright) {
                    Some(newleft || newright)
                } else if !left && !newright {
                    Some(newright)
                } else if !right && !newleft {
                    Some(newleft)
                } else {
                    None
                }
            });

        self.set_both_last_vals(newleft, newright);
        result
    }
}

impl<'a, U: 'a, L, R> Iterator for UnionIntervalIter<'a, U, L, R>
where
    L: Iterator<Item = (&'a U, &'a bool)>,
    R: Iterator<Item = (&'a U, &'a bool)>,
    U: Ord + Clone,
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
                    let next_val = self.next_left_value(*vl);
                    (Some(ul.clone()), next_val, Adv::Left)
                }
                (Some(&(ul, _)), Some(&(ur, vr))) if ul > ur => {
                    let next_val = self.next_right_value(*vr);
                    (Some(ur.clone()), next_val, Adv::Right)
                }
                (Some(&(ul, vl)), Some(&(_ur, vr))) => {
                    // ul == ur
                    let next_val = self.next_both_value(*vl, *vr);
                    (Some(ul.clone()), next_val, Adv::Both)
                }
                (Some(&(ul, vl)), None) => {
                    let next_val = self.next_left_value(*vl);
                    (Some(ul.clone()), next_val, Adv::Left)
                }
                (None, Some(&(ur, vr))) => {
                    let next_val = self.next_right_value(*vr);
                    (Some(ur.clone()), next_val, Adv::Right)
                }
                (None, None) => {
                    self.set_none_last_vals();
                    (None, None, Adv::None)
                }
            };

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
            key = k;
            value = v;
        }

        match (key, value) {
            (Some(k), Some(v)) => Some((k, v)),
            (None, None) => None,
            _ => panic!("Unexpect return value for UnionIntervalIter::next()"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

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
    fn bounded_range_partition_map_includes_three_valued() {
        let pm = TestPM::new(TestAlpha::B..TestAlpha::D, true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&TestAlpha::A]);
        assert!(pm.map[&TestAlpha::B]);
        assert!(!pm.map[&TestAlpha::D]);
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
        use self::TestAlpha::*;

        let pm = TestPM::new((Included(B), Included(C)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&B]);
        assert!(!pm.map[&D]);
    }

    #[test]
    fn excluded_lower_bounded_range_partition_map_includes_two_values() {
        use std::collections::Bound::*;
        use self::TestAlpha::*;

        let pm = TestPM::new((Excluded(C), Unbounded), true, false);

        assert_eq!(pm.map.len(), 2);
        assert!(!pm.map[&A]);
        assert!(pm.map[&D]);
    }

    #[test]
    fn excluded_lower_include_upper_bounded_range_partition_map_includes_three_values() {
        use std::collections::Bound::*;
        use self::TestAlpha::*;

        let pm = TestPM::new((Excluded(B), Included(D)), true, false);

        assert_eq!(pm.map.len(), 3);
        assert!(!pm.map[&A]);
        assert!(pm.map[&C]);
        assert!(!pm.map[&E]);
    }

    #[test]
    fn excluded_both_bounded_range_partition_map_includes_three_values() {
        use std::collections::Bound::*;
        use self::TestAlpha::*;

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
        use self::TestAlpha::*;

        TestPM::new((Included(C), Excluded(B)), true, false);
    }

    #[test]
    #[should_panic]
    fn lower_exclusive_bound_equal_upper_exlusive_bound_panics() {
        use std::collections::Bound::*;
        use self::TestAlpha::*;

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
}
