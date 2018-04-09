// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! Defines iterators and other utilities for working with `Span<T>`.

use std::{fmt, io, str};
use super::{Location, Span};
use encode_unicode::{U8UtfExt, Utf8Char};
use std::io::prelude::*;

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
    type Item = Result<Span<char>, Never>;

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

/// An iterator that converts bytes to spanned utf8 `chars`.
///
/// # Errors
/// The iterator will produce an Err(e) item when ever the underlying
/// iterator does so. It will also produce the following errors as a part
/// of converting from bytes to utf8 encoded `char`s:
///
/// - `ErrorKind::UnexpectedEof`: the underlying iterator ended in the middle of a
/// multibyte utf8 `char`
/// - `ErrorKind::InvalidData`: a byte or byte sequence from the underlying iterator
/// was not a valid utf8 encoded `char`
pub struct SpannedUtf8Iter<I>
where
    I: Iterator<Item = io::Result<u8>>,
{
    inner: I,
    current: Location,
}

impl<I> SpannedUtf8Iter<I>
where
    I: Iterator<Item = io::Result<u8>>,
{
    /// Create a new `SpannedUtf8Iter` over the given bytes iterator.
    ///
    /// The `Location`'s for the `Span<char>`'s that are produced
    /// will start at `start`.
    pub fn new(start: Location, iter: I) -> SpannedUtf8Iter<I> {
        SpannedUtf8Iter {
            inner: iter,
            current: start,
        }
    }

    fn make_span(&mut self, c: char) -> Span<char> {
        let start = self.current;
        let len = c.len_utf8();

        self.current += len;
        Span::new(start, start + (len - 1), c)
    }
}

impl<I> Iterator for SpannedUtf8Iter<I>
where
    I: Iterator<Item = io::Result<u8>>,
{
    type Item = io::Result<Span<char>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(Err(e)) => Some(Err(e)),
            Some(Ok(first)) => {
                Some(extract_utf8_char(first, &mut self.inner).map(|c| self.make_span(c)))
            }
        }
    }
}

fn extract_utf8_char<I>(first: u8, iter: &mut I) -> io::Result<char>
where
    I: Iterator<Item = io::Result<u8>>,
{
    let count = first.extra_utf8_bytes().map_err(map_invalid_data)?;

    let mut buffer = [first, 0, 0, 0];
    for index in 1..(count + 1) {
        buffer[index] = extract_utf8_continutaion_byte(iter)?;
    }

    Utf8Char::from_array(buffer)
        .map_err(map_invalid_data)
        .map(|c| c.to_char())
}

fn map_invalid_data<E>(error: E) -> io::Error
where
    E: Into<Box<::std::error::Error + Send + Sync>>,
{
    io::Error::new(io::ErrorKind::InvalidData, error)
}

fn extract_utf8_continutaion_byte<I>(iter: &mut I) -> io::Result<u8>
where
    I: Iterator<Item = io::Result<u8>>,
{
    use std::io::{Error, ErrorKind};

    match iter.next() {
        None => Err(Error::new(
            ErrorKind::UnexpectedEof,
            "Too few bytes for utf8 character.",
        )),
        Some(Err(e)) => Err(e),
        Some(Ok(byte)) => Ok(byte),
    }
}

/// Extention trait for a reader to allow it to prodcue a spanned `char`s iterator.
///
/// Although there is a default implementation for every reader, there will likely
/// be bad performance on any unbuffered readers because the iterator will use many
/// single-byte reads.
pub trait Utf8SpannedChars: Read + Sized {
    /// Iterate over the spanned utf8 encoded `char`s for this reader.
    fn spanned_chars(self, start: Location) -> SpannedUtf8Iter<io::Bytes<Self>>;
}

impl<R: Read> Utf8SpannedChars for R {
    fn spanned_chars(self, start: Location) -> SpannedUtf8Iter<io::Bytes<Self>> {
        SpannedUtf8Iter::new(start, self.bytes())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::ErrorKind;

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

    #[test]
    fn extract_invalid_first_byte_is_error() {
        use std::iter;
        let continuation_byte: u8 = 0x80;

        let result = extract_utf8_char(continuation_byte, &mut iter::empty::<io::Result<u8>>());

        assert_matches!(result, Err(ref e) if e.kind() == ErrorKind::InvalidData);
    }

    #[test]
    fn extract_with_too_few_bytes_is_error() {
        let first: u8 = 0xe1; // first byte of 3 byte sequence
        let rest: Vec<io::Result<u8>> = vec![Ok(90)]; // 1 following byte

        let result = extract_utf8_char(first, &mut rest.into_iter());

        assert_matches!(result, Err(ref e) if e.kind() == ErrorKind::UnexpectedEof);
    }

    #[test]
    fn extract_with_invalid_continuation_is_error() {
        let first: u8 = 0xc2; // first byte of 2 byte sequence
        let rest: Vec<io::Result<u8>> = vec![Ok(0xc2)]; // not continuation byte

        let result = extract_utf8_char(first, &mut rest.into_iter());

        assert_matches!(result, Err(ref e) if e.kind() == ErrorKind::InvalidData);
    }

    #[test]
    fn extract_with_valid_bytes_is_expected_char() {
        let first: u8 = 0xe1; // first byte of 3 byte sequence
        let rest: Vec<io::Result<u8>> = vec![Ok(0x90), Ok(0x81)];

        let result = extract_utf8_char(first, &mut rest.into_iter());

        assert_matches!(result, Ok(c) if c == 'ᐁ');
    }

    #[test]
    fn spanned_utf8_decodes_expected_chars() {
        let bytes = vec![0x41, 0x42, 0xc2, 0xa2, 0xe1, 0x90, 0x81];
        let iter = bytes.into_iter().map(|b| Ok(b));

        let results: Result<Vec<_>, _> = SpannedUtf8Iter::new(0.into(), iter).collect();

        assert_eq!(
            results.expect("Unexpected error in the SpannedUtf8Iter."),
            vec![
                Span::new(0.into(), 0.into(), 'A'),
                Span::new(1.into(), 1.into(), 'B'),
                Span::new(2.into(), 3.into(), '¢'),
                Span::new(4.into(), 6.into(), 'ᐁ'),
            ]
        );
    }

    #[test]
    fn utf8_spanned_chars_decodes_expected_chars() {
        let bytes = vec![0x41, 0x42, 0xc2, 0xa2, 0xe1, 0x90, 0x81];

        let results: Result<Vec<_>, _> = bytes.spanned_chars(0.into()).collect();

        assert_eq!(
            results.expect("Unexpected error in the SpannedUtf8Iter."),
            vec![
                Span::new(0.into(), 0.into(), 'A'),
                Span::new(1.into(), 1.into(), 'B'),
                Span::new(2.into(), 3.into(), '¢'),
                Span::new(4.into(), 6.into(), 'ᐁ'),
            ]
        );
    }
}
