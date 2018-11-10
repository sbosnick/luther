// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

pub use self::map::PartitionMap;
pub use self::set::PartitionSet;
pub use self::set::PartitionSetRangeIter;

mod set;
mod map ;

pub trait MergeValue<V> {
    fn next_left(&mut self, v: V) -> V;
    fn next_right(&mut self, v: V) -> V;
    fn next_both(&mut self, left: V, right: V) -> V;
}

#[cfg(test)]
mod test {
    use super::*;
    use testutils::*;

    // Simple types for use in unit tests

    type TestPM<V> = PartitionMap<TestAlpha, V>;

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

}
