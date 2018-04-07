// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! Defines iterators and other utilities for working with `Span<T>`.

use std::{fmt, str};

/// A failure that cannot occur.
///
/// This type is used as the error type in a `Result<T,E>` when no errors
/// are possible.
#[derive(Fail, Debug)]
pub enum Never {}

impl fmt::Display for Never {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "The impossible has occured. Never has occured as a failure."
        )
    }
}

/// An iterator over the spanned `char`'s of an `str`
pub struct SpannedStrIter<I>
where
    I: Iterator<Item = (usize, char)>,
{
    inner: I,
}

impl<'a> SpannedStrIter<str::CharIndices<'a>> {
    /// Create a new `SpannedStrIter` for the given `str`.
    pub fn new(input: &'a str) -> Self {
        SpannedStrIter {
            inner: input.char_indices(),
        }
    }
}

impl<I> Iterator for SpannedStrIter<I>
where
    I: Iterator<Item = (usize, char)>,
{
    type Item = Result<super::Span<char>, Never>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(i) => Some(Ok(i.into())),
        }
    }
}

/// Extention trait for `str` to provide the `spanned_chars` method.
pub trait StrExt {
    /// Iterate over the spanned `char`'s of the string.
    fn spanned_chars<'a>(&'a self) -> SpannedStrIter<str::CharIndices<'a>>;
}

impl StrExt for str {
    fn spanned_chars<'a>(&'a self) -> SpannedStrIter<str::CharIndices<'a>> {
        SpannedStrIter::new(self)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use Span;

    #[test]
    fn string_iterates_expected_spans() {
        let results: Result<Vec<_>, _> = "abc℞①".spanned_chars().collect();

        assert_eq!(
            results.expect("Unexpected error in the spanned_chars() iterator."),
            vec![
                Span::new(0.into(), 0.into(), 'a'),
                Span::new(1.into(), 1.into(), 'b'),
                Span::new(2.into(), 2.into(), 'c'),
                Span::new(3.into(), 5.into(), '℞'),
                Span::new(6.into(), 8.into(), '①'),
            ]
        )
    }
}
