// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use itertools;

pub use self::map::Partition;
pub use self::set::Set;
pub use self::set::SetRangeIter;

mod set;
mod map ;

pub trait MergeValue<V> {
    fn next_left(&mut self, v: V) -> V;
    fn next_right(&mut self, v: V) -> V;
    fn next_both(&mut self, left: V, right: V) -> V;
}

pub fn merge_iter<'a, I, J, M, U, V>(left: I, right: J, merge: &'a mut M) -> impl Iterator<Item=(U,V)> + 'a
where
    I: IntoIterator<Item=(U,V)> + 'a,
    J: IntoIterator<Item=(U,V)> + 'a,
    M: MergeValue<V>,
    U: Ord,
{
    use itertools::EitherOrBoth::*;

    itertools::merge_join_by(left, right, |(l, _), (r, _)| l.cmp(r))
        .map(move |value| match value {
            Left((u, v)) => (u, merge.next_left(v)),
            Right((u, v)) => (u, merge.next_right(v)),
            Both((u, vl), (_, vr)) => (u, merge.next_both(vl, vr)),
        })
}

#[cfg(test)]
use self::map::map_get;

#[cfg(test)]
mod test {
    use super::*;
    use testutils::*;

    // Simple types for use in unit tests

    type TestPM<V> = Partition<TestAlpha, V>;

    // Unit tests

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

        assert!(!map_get(&pm, &A));
        assert!(map_get(&pm, &B));
        assert!(map_get(&pm, &C));
        assert!(!map_get(&pm, &D));
        assert!(!map_get(&pm, &E));
    }

    #[test]
    fn partion_map_min_lower_bound_gets_all_true() {
        use testutils::TestAlpha::*;

        let pm = TestPM::new(A.., true, false);

        assert!(map_get(&pm, &A));
        assert!(map_get(&pm, &B));
        assert!(map_get(&pm, &C));
        assert!(map_get(&pm, &D));
        assert!(map_get(&pm, &E));
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

        assert_eq!(*map_get(&sut, &A), 1);
        assert_eq!(*map_get(&sut, &B), 2);
        assert_eq!(*map_get(&sut, &C), 3);
        assert_eq!(*map_get(&sut, &D), 4);
        assert_eq!(*map_get(&sut, &E), 4);
    }
}
