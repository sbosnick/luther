// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This is copied from the standard library because the RangeArgument
// trait is not yet stable.

//! Range syntax.

use std::collections::Bound::{self, Excluded, Included, Unbounded};
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};

/// `RangeArgument` is implemented by Rust's built-in range types, produced
/// by range syntax like `..`, `a..`, `..b` or `c..d`.
pub trait RangeArgument<T: ?Sized> {
    /// Start index bound.
    ///
    /// Returns the start value as a `Bound`.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// #![feature(alloc)]
    /// #![feature(collections_range)]
    ///
    /// extern crate alloc;
    ///
    /// # fn main() {
    /// use alloc::range::RangeArgument;
    /// use alloc::Bound::*;
    ///
    /// assert_eq!((..10).start(), Unbounded);
    /// assert_eq!((3..10).start(), Included(&3));
    /// # }
    /// ```
    fn start(&self) -> Bound<&T>;

    /// End index bound.
    ///
    /// Returns the end value as a `Bound`.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// #![feature(alloc)]
    /// #![feature(collections_range)]
    ///
    /// extern crate alloc;
    ///
    /// # fn main() {
    /// use alloc::range::RangeArgument;
    /// use alloc::Bound::*;
    ///
    /// assert_eq!((3..).end(), Unbounded);
    /// assert_eq!((3..10).end(), Excluded(&10));
    /// # }
    /// ```
    fn end(&self) -> Bound<&T>;
}

// FIXME add inclusive ranges to RangeArgument

impl<T: ?Sized> RangeArgument<T> for RangeFull {
    fn start(&self) -> Bound<&T> {
        Unbounded
    }
    fn end(&self) -> Bound<&T> {
        Unbounded
    }
}

impl<T> RangeArgument<T> for RangeFrom<T> {
    fn start(&self) -> Bound<&T> {
        Included(&self.start)
    }
    fn end(&self) -> Bound<&T> {
        Unbounded
    }
}

impl<T> RangeArgument<T> for RangeTo<T> {
    fn start(&self) -> Bound<&T> {
        Unbounded
    }
    fn end(&self) -> Bound<&T> {
        Excluded(&self.end)
    }
}

impl<T> RangeArgument<T> for Range<T> {
    fn start(&self) -> Bound<&T> {
        Included(&self.start)
    }
    fn end(&self) -> Bound<&T> {
        Excluded(&self.end)
    }
}

impl<T> RangeArgument<T> for (Bound<T>, Bound<T>) {
    fn start(&self) -> Bound<&T> {
        match *self {
            (Included(ref start), _) => Included(start),
            (Excluded(ref start), _) => Excluded(start),
            (Unbounded, _) => Unbounded,
        }
    }

    fn end(&self) -> Bound<&T> {
        match *self {
            (_, Included(ref end)) => Included(end),
            (_, Excluded(ref end)) => Excluded(end),
            (_, Unbounded) => Unbounded,
        }
    }
}

impl<'a, T: ?Sized + 'a> RangeArgument<T> for (Bound<&'a T>, Bound<&'a T>) {
    fn start(&self) -> Bound<&T> {
        self.0
    }

    fn end(&self) -> Bound<&T> {
        self.1
    }
}
