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
