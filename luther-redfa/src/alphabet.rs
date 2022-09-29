// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! Trait to define alphabets for regular expressions and dfa's.

use std::{char, hash::Hash, mem};

/// Required functionality for all alphabets that `luther-redfa` can use when
/// building a dfa from a regular expresson (or a regular vector).
///
/// The alphabet is required to have a total order, maximum and minimum
/// elements, and the ability to increment and decrement elements.
pub trait Alphabet: Ord + Clone + Hash {
    /// The minimum value in the alphabet.
    fn min_value() -> Self;

    /// The maximum value in the alphabet.
    fn max_value() -> Self;

    /// Return the next element (None if this is already max_value()).
    fn increment(&self) -> Option<Self>;

    /// Return the previous element (None if this is already min_value()).
    fn decrement(&self) -> Option<Self>;
}

impl Alphabet for u8 {
    fn min_value() -> Self {
        u8::min_value()
    }

    fn max_value() -> Self {
        u8::max_value()
    }

    fn increment(&self) -> Option<Self> {
        self.checked_add(1)
    }

    fn decrement(&self) -> Option<Self> {
        self.checked_sub(1)
    }
}

const LAST_BEFORE_SUROGATE: char = '\u{D7FF}';
const FIRST_AFTER_SUROGATE: char = '\u{E000}';
const ZERO_CHAR: char = '\u{0000}';

impl Alphabet for char {
    fn min_value() -> Self {
        ZERO_CHAR
    }

    fn max_value() -> Self {
        char::MAX
    }

    fn increment(&self) -> Option<Self> {
        // A char outside of the ranges [0x0, 0xD7FF] and [0xE000, 0x10FFFF]
        // is undefined behaviour. The special cases procted the
        // mem::transmute() call from producing such a value.
        match self {
            &char::MAX => None,
            &LAST_BEFORE_SUROGATE => Some(FIRST_AFTER_SUROGATE),
            _ => unsafe { mem::transmute((*self as u32) + 1) },
        }
    }

    fn decrement(&self) -> Option<Self> {
        // A char outside of the ranges [0x0, 0xD7FF] and [0xE000, 0x10FFFF]
        // is undefined behaviour. The special cases procted the
        // mem::transmute() call from producing such a value.
        match self {
            &ZERO_CHAR => None,
            &FIRST_AFTER_SUROGATE => Some(LAST_BEFORE_SUROGATE),
            _ => unsafe { mem::transmute((*self as u32) - 1) },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn increment_max_char_is_none() {
        let result = char::max_value().increment();

        assert!(result.is_none());
    }

    #[test]
    fn decrement_min_char_is_none() {
        let result = char::min_value().decrement();

        assert!(result.is_none());
    }

    #[test]
    fn increment_decrement_is_orginal() {
        let start = 'a';

        let result = start
            .increment()
            .expect("Unexpected None value.")
            .decrement()
            .expect("Unexpected None value.");

        assert_eq!(result, start);
    }

    #[test]
    fn increment_decrement_last_before_surrogate_is_original() {
        let start = LAST_BEFORE_SUROGATE;

        let result = start
            .increment()
            .expect("Unexpected None value.")
            .decrement()
            .expect("Unexpected None value.");

        assert_eq!(result, start);
    }

    proptest! {
        #[test]
        fn prop_char_alphabet_increment_decrement(a in any::<char>()) {
            let result = a.increment()
                .and_then(|b| b.decrement());

            prop_assert!( result.is_none() || result.unwrap() == a);
        }
    }
}
