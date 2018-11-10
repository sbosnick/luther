// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::fmt::Debug;
use std::iter::FromIterator;
use std::rc::Rc;

use alphabet::Alphabet;
use partition::{PartitionMap, PartitionSet, PartitionSetRangeIter};

/// A (possibly empty) subset of the alphabet `A`.
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
pub struct Class<A: Alphabet> {
    set: Option<Rc<PartitionSet<A>>>,
}

/// An iterator over the closed ranges of a class.
///
/// This is the return type of the `Class<A>::ranges()` method.
pub struct Ranges<'a, A: 'a + Alphabet> {
    inner: Option<PartitionSetRangeIter<'a, A>>,
}

/// An inclusive range of charaters from the alphabet `A`.
#[derive(Debug, PartialEq, Clone)]
pub struct Range<A: Alphabet> {
    start: A,
    end: A,
}

impl<A: Alphabet> Class<A> {
    /// Get an iterator over the closed ranges that make up the `Class`.
    ///
    /// The ranges returned by the iterator will be non-overlapping ranges
    /// and will be in increasing order. Adjacent ranges will also be combined.
    pub fn ranges<'a>(&'a self) -> Ranges<'a, A> {
        Ranges {
            inner: match self.set {
                Some(ref set) => Some(set.into_iter()),
                None => None,
            }
        }
    }

    /// Check if the subset of `A` is empty.
    pub fn is_empty(&self) -> bool {
        self.set.is_none()
    }

    /// Check if the subset of `A` is the complement of the empty set
    /// (i.e. it is every element in `A`).
    pub fn is_complement_empty(&self) -> bool {
        self.set.as_ref().map_or(false, |set| set.is_complement_empty())
    }

    /// Check if the class contains the character `c`.
    pub fn contains(&self, c: &A) -> bool {
        self.set.as_ref().map_or(false, |set| set.contains(c))
    }

    pub(super) fn union(&self, other: &Class<A>) -> Class<A> {
        let set = match (self.set.as_ref(), other.set.as_ref()) {
            (Some(selfset), Some(otherset)) => Some(Rc::new(selfset.union(&otherset))),
            (None, Some(set)) => Some(set.clone()),
            (Some(set), None) => Some(set.clone()),
            (None, None) => None,
        };

        Class{ set }
    }

    pub(super) fn complement(&self) -> Class<A> {
        Class {
            set: self.set.as_ref().map_or_else(
                     || Some( Rc::new( PartitionSet::full_singleton())),
                     |set| Some( Rc::new(set.complement())),
                 )
        }
    }

    pub(crate) fn into_partition_map<V>(&self, in_value: V, out_value: V) -> PartitionMap<A, V>
    where
        V: Debug + Clone + PartialEq,
    {
        match self.set.as_ref() {
            Some(set) => set.into_map(in_value, out_value),
            None => PartitionMap::new(.., out_value, in_value),
        }
    }
}

impl<A: Alphabet> FromIterator<Range<A>> for Class<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Range<A>>,
    {
        let mut iter = iter.into_iter().peekable();
        Class {
            set: if iter.peek().is_none() {
                None
            } else {
                Some(Rc::new(iter.into_iter().collect()))
            }
        }
    }
}

impl<'a, A: Alphabet> Iterator for Ranges<'a, A> {
    type Item = Range<A>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.as_mut().and_then(|inner| inner.next())
    }
}

impl<A: Alphabet> Range<A> {
    /// Creates a new range of characters.
    ///
    /// If `end` is less than the `start` then they will be reversed.
    pub fn new(start: A, end: A) -> Range<A> {
        if end < start {
            Range {
                start: end,
                end: start,
            }
        } else {
            Range { start, end }
        }
    }

    /// The start of the range of characters.
    ///
    /// The start is included in the range.
    pub fn start(&self) -> A {
        self.start.clone()
    }

    /// The end of the range of characters.
    ///
    /// The end is included in the range.
    pub fn end(&self) -> A {
        self.end.clone()
    }

    pub(crate) fn coalesce(&self, other: &Self) -> Result<Self, (Self, Self)> {
        let maxstart = self.start.clone().max(other.start.clone());
        let minend = self.end.clone().min(other.end.clone());

        if maxstart.decrement().map_or(true, |start| start <= minend) {
            let start = self.start.clone().min(other.start.clone());
            let end = self.end.clone().max(other.end.clone());
            Ok(Range::new(start, end))
        } else {
            Err((self.clone(), other.clone()))
        }
    }
}

impl<'a, A: Alphabet> PartialEq<Range<A>> for &'a Range<A> {
    fn eq(&self, other: &Range<A>) -> bool {
        self.start == other.start && self.end == other.end
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use testutils::TestAlpha::*;

    #[test]
    fn range_coalesce_min_value_ranges() {
        let other = Range::new(A, A);

        let sut = Range::new(A, A);
        let result = sut.coalesce(&other);

        assert_matches!(result, Ok(r) => {
            assert_eq!(r.start(), A);
            assert_eq!(r.end(), A);
        });
    }

    #[test]
    fn range_coalesce_ajacent_ranges() {
        let other = Range::new(A, B);

        let sut = Range::new(C, D);
        let result = sut.coalesce(&other);

        assert_matches!(result, Ok(r) => {
            assert_eq!(r.start(), A);
            assert_eq!(r.end(), D);
        });
    }

    #[test]
    fn range_coalesce_overlapping_ranges() {
        let other = Range::new(A, C);

        let sut = Range::new(B, D);
        let result = sut.coalesce(&other);

        assert_matches!(result, Ok(r) => {
            assert_eq!(r.start(), A);
            assert_eq!(r.end(), D);
        });
    }

    #[test]
    fn range_coalesce_non_overlapping_ranges() {
        let other = Range::new(A, B);

        let sut = Range::new(D, D);
        let result = sut.coalesce(&other);

        assert_matches!(result, Err((r, s)) => {
            assert_eq!(r.start(), D);
            assert_eq!(r.end(), D);
            assert_eq!(s.start(), A);
            assert_eq!(s.end(), B);
        });
    }

    #[test]
    fn range_coalesce_contained_ranges() {
        let other = Range::new(C, C);

        let sut = Range::new(A, D);
        let result = sut.coalesce(&other);

        assert_matches!(result, Ok(r) => {
            assert_eq!(r.start(), A);
            assert_eq!(r.end(), D);
        });
    }
}
