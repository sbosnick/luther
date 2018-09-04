// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

mod last_values;

use std::collections::{btree_map, BTreeMap, Bound};
use std::fmt::Debug;
use std::iter::{FromIterator, Peekable};

use alphabet::Alphabet;
use arrayvec::ArrayVec;
use itertools::{self, Itertools};
use range::RangeArgument;
use regex::Range;

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
#[derive(Clone, Debug, PartialEq, PartialOrd, Hash)]
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

    fn from_partition_map_to_bool(
        source: &PartitionMap<U, bool>,
        in_value: V,
        out_value: V,
    ) -> PartitionMap<U, V> {
        PartitionMap {
            map: source
                .ranges()
                .map(|(u, v)| {
                    (
                        u.clone(),
                        if *v {
                            in_value.clone()
                        } else {
                            out_value.clone()
                        },
                    )
                })
                .collect(),
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

impl<U> PartitionMap<U, bool>
where
    U: Alphabet,
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

    pub fn complement(&self) -> Self {
        PartitionMap {
            map: self.map
                .iter()
                .map(|(k, v)| (k.clone(), (!v).clone()))
                .collect(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.map.len() == 1 && !self.map[&U::min_value()]
    }

    pub fn is_complement_empty(&self) -> bool {
        self.map.len() == 1 && self.map[&U::min_value()]
    }

    fn range_iter<'a>(&'a self) -> PartitionMapRangeIter<'a, U> {
        PartitionMapRangeIter {
            inner: (&self.map).into_iter(),
            first: true,
        }
    }
}

impl<U: Alphabet> FromIterator<Range<U>> for PartitionMap<U, bool> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Range<U>>,
    {
        use itertools::Position::*;

        let mut map: BTreeMap<U, bool> = iter.into_iter()
            .sorted_by_key(|range| range.start())
            .into_iter()
            .coalesce(|prev, curr| prev.coalesce(&curr))
            .with_position()
            .flat_map(|item| {
                let mut array = ArrayVec::<[_; 3]>::new();

                let (start, end) = match item {
                    First(item) | Only(item) => {
                        if item.start() != U::min_value() {
                            array.push((U::min_value(), false));
                        }
                        (item.start(), item.end())
                    }
                    Middle(item) | Last(item) => (item.start(), item.end()),
                };
                array.push((start, true));
                end.increment().map(|end| array.push((end, false)));

                array
            })
            .collect();

        if map.is_empty() {
            map.insert(U::min_value(), false);
        }

        PartitionMap { map }
    }
}

pub struct PartitionMapRangeIter<'a, U: 'a + Alphabet> {
    inner: btree_map::Iter<'a, U, bool>,
    first: bool,
}

impl<'a, U: Alphabet> Iterator for PartitionMapRangeIter<'a, U> {
    type Item = Range<U>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .and_then(|(k, v)| {
                let start = if self.first && !v {
                    self.inner.next()
                } else {
                    Some((k, v))
                };
                self.first = false;
                start
            })
            .map(|(start, _)| {
                let end = self.inner.next().map_or(U::max_value(), |(end, _)| {
                    end.decrement()
                        .expect("U::min_value() found in location other than the first one")
                });
                Range::new(start.clone(), end)
            })
    }
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
    U: Ord + Clone,
{
    type Item = (U, bool);

    fn next(&mut self) -> Option<Self::Item> {
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
            _ => panic!("Unexpect return value for UnionIntervalIter::next()"),
        }
    }
}

/// A `PartitionSet` is a set of `U` implemented in terms of a `PartitionMap` to
/// `bool`.
///
/// # Type Parameter
/// | U | The universe to partition to determine set membership |
///
/// U must be `Clone` but the `clone` implementation should be an efficient one. It is
/// likely that most useful types for U are `Copy`. U must also be an `Alphabet`.
#[derive(Clone, Debug, PartialEq, PartialOrd, Hash)]
pub struct PartitionSet<U> {
    map: PartitionMap<U, bool>,
}

impl<U: Alphabet> PartitionSet<U> {
    pub fn new<R: RangeArgument<U>>(range: R) -> PartitionSet<U> {
        PartitionSet {
            map: PartitionMap::new(range, true, false),
        }
    }

    pub fn contains(&self, u: &U) -> bool {
        self.map.get(u).clone()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
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
        PartitionMap::from_partition_map_to_bool(&self.map, in_value, out_value)
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

pub struct PartitionSetRangeIter<'a, U: 'a + Alphabet> {
    inner: PartitionMapRangeIter<'a, U>,
}

impl<'a, U: Alphabet> Iterator for PartitionSetRangeIter<'a, U> {
    type Item = Range<U>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use itertools::Itertools;
    use proptest::collection;
    use proptest::prelude::*;
    use std::iter;
    use testutils::*;

    // Simple types for use in unit tests

    type TestPM<V> = PartitionMap<TestAlpha, V>;
    type TestPS = PartitionSet<TestAlpha>;

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
    fn split_partition_map_maintains_non_consecutive_values_at_min_value() {
        use testutils::TestAlpha::*;

        let pm = TestPM::new(..C, true, false);
        let mut pm = pm.union(&TestPM::new(D.., true, false));
        pm.split(A, |_| (true, false));

        assert_eq!(pm.map.len(), 2);
        assert!(pm.map[&A] == false);
        assert!(pm.map[&D] == true);
    }

    #[test]
    fn split_partition_map_maintains_non_consecutive_values_at_initial_divide() {
        use testutils::TestAlpha::*;

        let mut pm = TestPM::new(C.., true, false);
        pm.split(C, |_| (true, false));

        assert_eq!(pm.map.len(), 1);
        assert!(pm.map[&A] == false);
    }

    #[test]
    fn split_partition_map_maintains_non_consecutive_values_after_union() {
        use testutils::TestAlpha::*;

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
        use testutils::TestAlpha::*;
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
    fn partition_map_from_map_to_bool_get_expected_values() {
        use testutils::TestAlpha::*;
        let source = TestPM::new(B..D, true, false);

        let sut = TestPM::from_partition_map_to_bool(&source, 0, 1);

        assert_eq!(*sut.get(&A), 1);
        assert_eq!(*sut.get(&B), 0);
        assert_eq!(*sut.get(&C), 0);
        assert_eq!(*sut.get(&D), 1);
        assert_eq!(*sut.get(&E), 1);
    }

    #[test]
    fn union_interval_iter_has_sticky_true() {
        use testutils::TestAlpha::*;
        let left = vec![(&A, &true), (&B, &false)].into_iter();
        let right = vec![(&A, &true), (&C, &false)].into_iter();

        let mut sut = UnionIntervalIter::new(left, right.into_iter());
        sut.next();
        let result = sut.next();

        assert_matches!(result, Some((C, false)));
    }

    #[test]
    fn union_interval_iter_pairwise_has_sticky_true() {
        use testutils::TestAlpha::*;
        let left = vec![(&A, &true), (&B, &false), (&C, &false)].into_iter();
        let right = vec![(&A, &true), (&B, &true), (&C, &false)].into_iter();

        let mut sut = UnionIntervalIter::new(left, right.into_iter());
        sut.next();
        let result = sut.next();

        assert_matches!(result, Some((C, false)));
    }

    #[test]
    fn complement_partition_map_gets_expected_values() {
        use testutils::TestAlpha::*;

        let sut = TestPM::new(B..D, true, false);
        let result = sut.complement();

        assert!(*result.get(&A));
        assert!(!*result.get(&B));
        assert!(!*result.get(&C));
        assert!(*result.get(&D));
        assert!(*result.get(&E));
    }

    #[test]
    fn partion_map_from_ranges_has_expected_values() {
        let ranges = vec![
            Range::new(15u8, 25),
            Range::new(30, 35),
            Range::new(36, 40),
            Range::new(50, 60),
            Range::new(55, 65),
            Range::new(5, 8),
        ];

        let sut: PartitionMap<_, _> = ranges.into_iter().collect();

        assert!(!sut.map[&0]);
        assert!(sut.map[&5]);
        assert!(!sut.map[&9]);
        assert!(sut.map[&15]);
        assert!(!sut.map[&26]);
        assert!(sut.map[&30]);
        assert!(!sut.map[&41]);
        assert!(sut.map[&50]);
        assert!(!sut.map[&66]);
    }

    #[test]
    fn partition_map_from_empty_ranges_have_expected_value() {
        let ranges = Vec::<Range<u8>>::new();

        let sut: PartitionMap<_, _> = ranges.into_iter().collect();

        assert!(!sut.map[&0]);
    }

    #[test]
    fn partition_map_iterates_expected_ranges() {
        let ranges = vec![Range::new(5u8, 8), Range::new(15, 25), Range::new(50, 60)];

        let sut = PartitionMap::from_iter(ranges.clone());
        let result: Vec<_> = sut.range_iter().collect();

        assert_eq!(result, ranges);
    }

    #[test]
    fn patition_set_contains_expected_values() {
        use testutils::TestAlpha::*;

        let sut = TestPS::new(B..D);

        assert!(!sut.contains(&A));
        assert!(sut.contains(&B));
        assert!(sut.contains(&C));
        assert!(!sut.contains(&D));
        assert!(!sut.contains(&E));
    }

    #[test]
    fn patition_set_from_empty_ranges_is_empty() {
        let range = iter::empty::<Range<u8>>();

        let sut: PartitionSet<_> = range.collect();

        assert!(sut.is_empty());
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
        Complement,
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
                Complement => arg.complement(),
            }
        }
    }

    fn arb_pm_op_vector() -> collection::VecStrategy<BoxedStrategy<PMOp>> {
        let pmop_strategy = prop_oneof![
            2 => any::<u8>().prop_map(PMOp::Split),
            1 => arb_u8_range().prop_map(PMOp::Union),
            1 => Just(PMOp::Complement),
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

        #[test]
        fn prop_merged_partition_map_contains_min_value(
            pm_left in arb_partition_map(),
            ops_left in arb_pm_op_vector(),
            pm_right in arb_partition_map(),
            ops_right in arb_pm_op_vector()
            )
        {
            let mut pm_left = pm_left.clone();
            for op in ops_left {
                pm_left = op.run(&pm_left);
            }

            let mut pm_right = pm_right.clone();
            for op in ops_right {
                pm_right = op.run(&pm_right);
            }

            let mut merge = Value(0);
            let pm = PartitionMap::from_merge(
                PartitionMap::from_partition_map_to_bool(&pm_left, 0, 1),
                PartitionMap::from_partition_map_to_bool(&pm_right, 0, 1), &mut merge);

            prop_assert!(pm.map.contains_key(&0));
        }

        #[test]
        fn prop_merged_partition_map_values_alternate(
            pm_left in arb_partition_map(),
            ops_left in arb_pm_op_vector(),
            pm_right in arb_partition_map(),
            ops_right in arb_pm_op_vector()
            )
        {
            let mut pm_left = pm_left.clone();
            for op in ops_left {
                pm_left = op.run(&pm_left);
            }

            let mut pm_right = pm_right.clone();
            for op in ops_right {
                pm_right = op.run(&pm_right);
            }

            let mut merge = Value(0);
            let pm = PartitionMap::from_merge(
                PartitionMap::from_partition_map_to_bool(&pm_left, 0, 1),
                PartitionMap::from_partition_map_to_bool(&pm_right, 0, 1), &mut merge);

            for (first, second) in pm.map.values().tuple_windows() {
                prop_assert_ne!(first, second);
            }
        }
    }
}
