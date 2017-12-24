use std::ops;

/// Wraps a value with start and end `Location`'s.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Span<T> {
    start: Location,
    end: Location,
    value: T
}

impl<T> Span<T> {
    /// Create a new `Span` for a given start and end `Location` and value.
    pub fn new(start: Location, end: Location, value: T) -> Span<T> {
        Span{start, end, value}
    }

    /// Gets the start `Location` of the `Span`.
    pub fn start(&self) -> Location {
        self.start
    }

    /// Gets the end `Location` of the `Span`.
    pub fn end(&self) -> Location {
        self.end
    }

    /// Gets a reference to the value of the `Span`.
    pub fn value_ref(&self) -> &T {
        &self.value
    }

    /// Extends the current `Span` to a new end `Location`.
    pub fn extend(&mut self, end: Location) {
        self.end = end;
    }
}

impl From<(usize, char)> for Span<char> {
    /// Converts from a (pos, value) to a `Span`.
    ///
    /// This conversion is designed to support the Item type of the iterator returned from the
    /// `str::char_indicies()` method. It assumes the pos is the starting position and that the value
    /// is encoded in utf8.
    fn from((pos, value): (usize, char) ) -> Self {
        Self::new(pos.into(), (pos + value.len_utf8()).into(), value)
    }
}

/// An abstract location within a stream of tokens or characters.
///
/// Note that `Location`'s are not orderable (that is, `Location` does not impl `Ord` or `PartialOrd`).
/// The value of a `Location` cannot tell you whether it comes before or after some other
/// `Location` in the same stream, just whether its equal or not equal to some other `Location`.
/// It is possible to create a new `Location` from a `usize` or by adding a `usize` to an exising `Location`.
///
/// # Panics
///
/// Adding a usize to a `Location` will panic if the resulting `Location` value is greater than
/// `usize::max_value()`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Default)]
pub struct Location (usize);

impl Location {
    /// Create a new `Location` for a given starting point.
    pub fn new(location: usize) -> Location {
        Location(location)
    }
}

impl ops::AddAssign<usize> for Location {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl ops::Add<usize> for Location {
    type Output = Location;

    fn add(mut self, rhs: usize) -> Location {
        self += rhs;
        self
    }
}

impl From<usize> for Location {
    fn from(value: usize) -> Self {
        Self::new(value)
    }
}

#[cfg(test)]
mod test {
    use std::usize;
    use super::*;

    #[test]
    fn location_default_eq_location_0() {
        let sut: Location = Default::default();

        assert_eq!(sut, Location::new(0));
    }

    #[test]
    fn location_add_eq_usize_add() {
        let base = 5;
        let inc = 3;

        let sut = Location::new(base);

        assert_eq!(sut + inc, Location::new(base + inc));
    }

    #[test]
    #[should_panic]
    fn location_add_overflow_panics() {
        Location::new(usize::max_value()) + 3;
    }

    #[test]
    fn span_from_usize_char_gives_expected_result() {
        let value = '€';
        let pos = 5;

        let sut: Span<char> = (pos, value).into();

        assert_eq!(sut, Span::new(pos.into(), (pos+ 3).into(), value));
    }
}
