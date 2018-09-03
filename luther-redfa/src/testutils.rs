// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

// The utility types in this module are used to support tests in more than
// one other module.

use alphabet::Alphabet;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum TestAlpha {
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
