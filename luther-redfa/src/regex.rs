// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! Regular expression types.
//!
//! The types in this module provide a representation of the extended regular
//! expressions supported by `luther_redfa`. The key types are `RegexContext<A>`,
//! `Regex<A>` and `RegexKind<A>`.
//!
//! Most of the regular expression types are generic over the alphabet that they
//! are designed to match. The alphabet is identifed by the `Alphabet` trait, for
//! which the `luther_redfa` crate provides `u8` and `char` implementations.
//!
//! `RegexContext<A>` is a factory for creating `Regex<A>` and has factory methods
//! for each variant of `RegexKind<A>`. There is no means of creating a `Regex<A>`
//! directly from a `RegexKind<A>`. The required use of factory methods allows for
//! mataining the regular expressons in cannonical form.

use std::fmt::{self, Debug, Display};
use std::iter::FromIterator;

use alphabet::Alphabet;
use partition::{PartitionSet, PartitionSetRangeIter};
use typed_arena::Arena;

/// A context for creating regular expressions.
///
/// The factory methods in `RegexContext` create different kinds of `Regex` but
/// also maintain those `Regex` in `≈-cannonical` form as this is defined in section
/// 4.1 of Owens et al. The need to maintain the regular expressions in cannonical form
/// is why there is no means of creating a `Regex` from a `RegexKind`.
///
/// # Type Parameter
/// - A: the alphabet over which the regular expression operates
pub struct RegexContext<'a, A: 'a + Alphabet> {
    arena: Arena<RegexKind<'a, A>>,
}

impl<'a, A: Alphabet + Debug> RegexContext<'a, A> {
    /// Create a new `RegexContext`.
    pub fn new() -> RegexContext<'a, A> {
        RegexContext {
            arena: Arena::new(),
        }
    }

    /// Create an empty `Regex`.
    ///
    /// The empty regular expressions matches everything, including the empty
    /// string.
    pub fn empty(&'a self) -> Regex<'a, A> {
        Regex {
            kind: self.arena.alloc(RegexKind::Empty),
        }
    }

    /// Create a character class `Regex`.
    ///
    /// The class regular expression matches a single character from one of the
    /// ranges specified by `ranges`. This factory can also create the empty set
    /// by passing in an empty iterator for `ranges`. The empty set does not
    /// match anything.
    pub fn class<I>(&'a self, ranges: I) -> Regex<A>
    where
        I: IntoIterator<Item = Range<A>>,
    {
        let class = ranges.into_iter().collect();
        Regex {
            kind: self.arena.alloc(RegexKind::Class(class)),
        }
    }

    /// Not yet implemented.
    pub fn concat(&self) -> Regex<A> {
        unimplemented!()
    }

    /// Create a repetition `Regex`.
    ///
    /// The repetition regular expression matches 0 or more occurances of of
    /// the `other` regular expression. The only kind of repetition directly
    /// supported by `RegexContext` is kleene star.
    pub fn repetition(&self, other: Regex<'a, A>) -> Regex<A> {
        let kind = match other.kind {
            RegexKind::Repetition(_) | RegexKind::Empty => other.kind,
            RegexKind::Class(class) if class.is_empty() => self.arena.alloc(RegexKind::Empty),
            _ => self.arena
                .alloc(RegexKind::Repetition(Repetition { inner: other.kind })),
        };
        Regex { kind }
    }

    /// Create an alteration (or logical-or) `Regex`.
    ///
    /// The alteration regular expression matches either the `lhs` regular
    /// expression or the `rhs` regular expression.
    pub fn alteration(&'a self, lhs: Regex<'a, A>, rhs: Regex<'a, A>) -> Regex<A> {
        if lhs.kind.is_null() || rhs.kind.is_complement_null() {
            return rhs;
        }
        if rhs.kind.is_null() || lhs.kind.is_complement_null() {
            return lhs;
        }
        if lhs.kind == rhs.kind {
            return lhs;
        }

        let (first, second) = order_operands(lhs.kind, rhs.kind, |first, second| {
            self.arena
                .alloc(RegexKind::Alteration(Alteration { first, second }))
        });

        let kind = self.arena
            .alloc(RegexKind::Alteration(Alteration { first, second }));

        Regex { kind }
    }

    /// Create a logical-and `Regex`.
    ///
    /// The and regular expression matches if both the `lhs` regular
    /// expression and the `rhs` regular expressions match.
    pub fn and(&'a self, lhs: Regex<'a, A>, rhs: Regex<'a, A>) -> Regex<A> {
        if lhs.kind.is_null() || rhs.kind.is_complement_null() {
            return lhs;
        }
        if rhs.kind.is_null() || lhs.kind.is_complement_null() {
            return rhs;
        }
        if lhs.kind == rhs.kind {
            return lhs;
        }

        let (first, second) = order_operands(lhs.kind, rhs.kind, |first, second| {
            self.arena.alloc(RegexKind::And(And { first, second }))
        });

        let kind = self.arena.alloc(RegexKind::And(And { first, second }));

        Regex { kind }
    }

    /// Create a complement (or negation) `Regex`.
    ///
    /// The complement regular expression matches everything that the supplied
    /// `other` regular expression does not match.
    pub fn complement(&self, other: Regex<'a, A>) -> Regex<A> {
        let kind = if let RegexKind::Complement(complement) = other.kind {
            complement.inner
        } else {
            self.arena
                .alloc(RegexKind::Complement(Complement { inner: other.kind }))
        };
        Regex { kind }
    }
}

/// A regular expression.
///
/// A `Regex` is created by the factory methods in `RegexContext` and is
/// associated with that context. It is not possible to create a `Regex`
/// directly. It is also not possible to create a `Regex` from a `RegexKind` in
/// order to allow `RegexContext` to maintain certain regular expressions in
/// cannonical form.
#[derive(Debug, PartialEq, Clone)]
pub struct Regex<'a, A: 'a + Alphabet> {
    kind: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Regex<'a, A> {
    /// Get the kind of the regular expression.
    pub fn kind(&self) -> &RegexKind<'a, A> {
        &self.kind
    }
}

/// The kind of a regular expression.
///
/// # Type Parameter
/// - A: the alphabet over which the regular expression operates
#[derive(Debug, PartialEq, PartialOrd)]
pub enum RegexKind<'a, A: 'a + Alphabet> {
    /// The empty regular expressions which matches everything, including the
    /// empty string.
    Empty,

    /// A regular expressions which matches one character from a (possibly empty)
    /// subset of the alphabet `A`.
    ///
    /// If the subset is empty then the resulting regular expression will match
    /// nothing.
    Class(Class<A>),

    /// Not yet implemented.
    Concat,

    /// A regular expression which matches 0 or more instances of a different
    /// regular expression.
    ///
    /// Note: The only kind of repetition that is directly supported is kleene star.
    Repetition(Repetition<'a, A>),

    /// A regular expression which matches either of two different regular
    /// expressions.
    Alteration(Alteration<'a, A>),

    /// A regular expression which matches both of two different regular
    /// expressions.
    And(And<'a, A>),

    /// A regular expression which matches the complement (or negation) of a different
    /// regular expression.
    Complement(Complement<'a, A>),
}

impl<'a, A: Alphabet + Debug> RegexKind<'a, A> {
    fn is_null(&self) -> bool {
        use self::RegexKind::*;

        match self {
            Class(class) if class.is_empty() => true,
            _ => false,
        }
    }

    fn is_complement_null(&self) -> bool {
        use self::RegexKind::*;

        if let Complement(complement) = self {
            complement.inner.is_null()
        } else {
            false
        }
    }

    fn binary_operands(&self) -> Option<(&'a RegexKind<'a, A>, &'a RegexKind<'a, A>)> {
        use self::RegexKind::*;

        match self {
            Alteration(alt) => Some((alt.first, alt.second)),
            And(and) => Some((and.first, and.second)),
            _ => None,
        }
    }
}

impl<'a, A: Alphabet> Display for RegexKind<'a, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::RegexKind::*;

        match self {
            Empty => write!(f, "Empty"),
            Class(_) => write!(f, "Class{{...}}"),
            Concat => write!(f, "Concat(not yet implemented)"),
            Repetition(rep) => write!(f, "Repetition({})", rep.inner),
            Alteration(alt) => write!(f, "Alteration({}, {})", alt.first, alt.second),
            And(and) => write!(f, "And({}, {})", and.first, and.second),
            Complement(comp) => write!(f, "Complement({})", comp.inner),
        }
    }
}

/// A (possibly empty) subset of the alphabet `A`.
#[derive(Debug, PartialEq, PartialOrd)]
pub struct Class<A: Alphabet> {
    set: PartitionSet<A>,
}

impl<A: Alphabet + Debug> Class<A> {
    /// Get an iterator over the closed ranges that make up the `Class`.
    ///
    /// The ranges returned by the iterator will be non-overlapping ranges
    /// and will be in increasing order. Adjacent ranges will also be combined.
    pub fn ranges<'a>(&'a self) -> Ranges<'a, A> {
        Ranges {
            inner: self.set.into_iter(),
        }
    }

    /// Check if the subset of `A` is empty.
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

impl<A: Alphabet> FromIterator<Range<A>> for Class<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Range<A>>,
    {
        Class {
            set: iter.into_iter().collect(),
        }
    }
}

/// A regular expression holder for which the complement (or negation) has been
/// taken.
#[derive(Debug, PartialEq, PartialOrd)]
pub struct Complement<'a, A: 'a + Alphabet> {
    inner: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Complement<'a, A> {
    /// Get the inner regular expression that is being complemented.
    pub fn inner(&'a self) -> Regex<'a, A> {
        Regex { kind: self.inner }
    }
}

/// A regular expression holder for which repetition has been applied.
#[derive(Debug, PartialEq, PartialOrd)]
pub struct Repetition<'a, A: 'a + Alphabet> {
    inner: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Repetition<'a, A> {
    /// Get the inner regular expression that is being repeated.
    pub fn inner(&'a self) -> Regex<'a, A> {
        Regex { kind: self.inner }
    }
}

/// A regular expression holder for regular expressions used as
/// alternatives (through alteration).
#[derive(Debug, PartialEq, PartialOrd)]
pub struct Alteration<'a, A: 'a + Alphabet> {
    first: &'a RegexKind<'a, A>,
    second: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Alteration<'a, A> {
    /// Get the first of the regular expression alternative.
    pub fn first(&'a self) -> Regex<'a, A> {
        Regex { kind: self.first }
    }

    /// Get the second of the regular expression alternative.
    pub fn second(&'a self) -> Regex<'a, A> {
        Regex { kind: self.second }
    }
}

/// A regular expressions holder for regular expressions used as
/// arguments to the `and` operation.
#[derive(Debug, PartialEq, PartialOrd)]
pub struct And<'a, A: 'a + Alphabet> {
    first: &'a RegexKind<'a, A>,
    second: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> And<'a, A> {
    /// Get the first of the regular expressions being anded.
    pub fn first(&'a self) -> Regex<'a, A> {
        Regex { kind: self.first }
    }

    /// Get the second of the regular expressions being anded.
    pub fn second(&'a self) -> Regex<'a, A> {
        Regex { kind: self.second }
    }
}

/// An iterator over the closed ranges of a class.
///
/// This is the return type of the `Class<A>::ranges()` method.
pub struct Ranges<'a, A: 'a + Alphabet> {
    inner: PartitionSetRangeIter<'a, A>,
}

impl<'a, A: Alphabet> Iterator for Ranges<'a, A> {
    type Item = Range<A>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

/// An inclusive range of charaters from the alphabet `A`.
#[derive(Debug, PartialEq, Clone)]
pub struct Range<A: Alphabet> {
    start: A,
    end: A,
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
        let (anchor, comp) = if self.start <= other.start {
            (self, other)
        } else {
            (other, self)
        };

        comp.start
            .decrement()
            .and_then(|start| {
                if start <= anchor.end {
                    Some(Range::new(anchor.start.clone(), comp.end.clone()))
                } else {
                    None
                }
            })
            .ok_or_else(|| (self.clone(), other.clone()))
    }
}

impl<'a, A: Alphabet> PartialEq<Range<A>> for &'a Range<A> {
    fn eq(&self, other: &Range<A>) -> bool {
        self.start == other.start && self.end == other.end
    }
}

// This function is responsible for ordering the operands to a communtiative and
// associative binary operation into a cannonical, lexographical order.
fn order_operands<'a, A, F>(
    lhs: &'a RegexKind<'a, A>,
    rhs: &'a RegexKind<'a, A>,
    factory: F,
) -> (&'a RegexKind<'a, A>, &'a RegexKind<'a, A>)
where
    A: Alphabet + Debug,
    F: Fn(&'a RegexKind<'a, A>, &'a RegexKind<'a, A>) -> &'a RegexKind<'a, A>,
{
    if let Some((inner_first, inner_second)) = lhs.binary_operands() {
        let (first, second, third) = if rhs < inner_first {
            (rhs, inner_first, inner_second)
        } else if rhs < inner_second {
            (inner_first, rhs, inner_second)
        } else {
            (inner_first, inner_second, rhs)
        };

        (first, factory(second, third))
    } else if lhs < rhs {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::iter;

    #[test]
    fn empty_regex_has_kind_empty() {
        let ctx = RegexContext::<char>::new();

        let sut = ctx.empty();

        assert_eq!(sut.kind(), &RegexKind::Empty);
    }

    #[test]
    fn class_regex_has_kind_class() {
        let ctx = RegexContext::new();
        let ranges = vec![Range::new('a', 'c'), Range::new('g', 'h')];

        let sut = ctx.class(ranges);

        assert_matches!(sut.kind(), &RegexKind::Class(_));
    }

    #[test]
    fn class_regex_round_trips_simple_ranges() {
        let ctx = RegexContext::new();
        let expected = vec![Range::new('a', 'c'), Range::new('g', 'h')];

        let sut = ctx.class(expected.clone());

        assert_matches!(sut.kind(), &RegexKind::Class(ref class) => {
            let ranges: Vec<Range<_>> = class.ranges().collect();
            assert_eq!(ranges, expected);
        });
    }

    #[test]
    fn simple_complement_regex_has_kind_complement() {
        let ctx = RegexContext::new();
        let class = ctx.class(vec![Range::new('a', 'c')]);

        let sut = ctx.complement(class);

        assert_matches!(sut.kind(), &RegexKind::Complement(_));
    }

    #[test]
    fn simple_complement_regex_round_trips_original_kind() {
        let ctx = RegexContext::new();
        let class = ctx.class(vec![Range::new('a', 'c')]);

        let sut = ctx.complement(class);

        assert_matches!(sut.kind(), &RegexKind::Complement(ref complement) => {
            assert_matches!(complement.inner().kind(), &RegexKind::Class(_));
        });
    }

    #[test]
    fn double_complement_regex_has_orginal_kind() {
        let ctx = RegexContext::new();
        let class = ctx.class(vec![Range::new('a', 'c')]);
        let complement = ctx.complement(class);

        let sut = ctx.complement(complement);

        assert_matches!(sut.kind(), &RegexKind::Class(_));
    }

    #[test]
    fn simple_repetition_regex_has_kind_repetition() {
        let ctx = RegexContext::new();
        let class = ctx.class(vec![Range::new('a', 'c')]);

        let sut = ctx.repetition(class);

        assert_matches!(sut.kind(), &RegexKind::Repetition(_));
    }

    #[test]
    fn simple_repetition_regex_round_trips_original_kind() {
        let ctx = RegexContext::new();
        let class = ctx.class(vec![Range::new('a', 'c')]);

        let sut = ctx.repetition(class);

        assert_matches!(sut.kind(), &RegexKind::Repetition(ref repetition) => {
            assert_matches!(repetition.inner().kind(), &RegexKind::Class(_));
        });
    }

    #[test]
    fn double_repetition_does_not_apply_twice() {
        let ctx = RegexContext::new();
        let class = ctx.class(vec![Range::new('a', 'c')]);
        let repetition = ctx.repetition(class);

        let sut = ctx.repetition(repetition);

        assert_matches!(sut.kind(), &RegexKind::Repetition(ref repetition) => {
            assert_matches!(repetition.inner().kind(), &RegexKind::Class(_));
        });
    }

    #[test]
    fn empty_repetition_is_still_emtpy() {
        let ctx = RegexContext::<char>::new();
        let empty = ctx.empty();

        let sut = ctx.repetition(empty);

        assert_matches!(sut.kind(), &RegexKind::Empty);
    }

    #[test]
    fn null_repetition_is_empty() {
        let ctx = RegexContext::<char>::new();
        let class = ctx.class(Vec::new());

        let sut = ctx.repetition(class);

        assert_matches!(sut.kind(), &RegexKind::Empty);
    }

    #[test]
    fn alteration_with_empty_class_is_other_value() {
        let ctx = RegexContext::<char>::new();
        let empty_class = ctx.class(Vec::new());
        let empty = ctx.empty();
        let neg_empty = ctx.complement(empty);

        let sut = ctx.alteration(empty_class, neg_empty);

        assert_matches!(sut.kind(), RegexKind::Complement(_));
    }

    #[test]
    fn alteration_with_complement_of_empty_class_is_complement_of_empty_class() {
        let ctx = RegexContext::<char>::new();
        let empty_class = ctx.class(Vec::new());
        let empty = ctx.empty();
        let neg_empty = ctx.complement(empty_class);

        let sut = ctx.alteration(empty, neg_empty);

        assert_matches!(sut.kind(), RegexKind::Complement(complement) => {
            assert_matches!(complement.inner, RegexKind::Class(class) => {
                assert!(class.is_empty());
            })
        });
    }

    #[test]
    fn alteration_with_equal_terms_is_that_term() {
        let ctx = RegexContext::new();
        let expected = vec![Range::new('a', 'c')];
        let class1 = ctx.class(expected.clone());
        let class2 = ctx.class(expected.clone());

        let sut = ctx.alteration(class1, class2);

        assert_matches!(sut.kind(), RegexKind::Class(class) => {
            let ranges: Vec<Range<_>> = class.ranges().collect();
            assert_eq!(ranges, expected);
        });
    }

    #[test]
    fn alteration_is_commutative() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        let neg_class = ctx.complement(ctx.class(iter::once(Range::new('f', 'z'))));

        let sut1 = ctx.alteration(class.clone(), neg_class.clone());
        let sut2 = ctx.alteration(neg_class, class);

        assert_eq!(sut1, sut2);
    }

    #[test]
    fn alteration_is_associative() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        let neg_class = ctx.complement(ctx.class(iter::once(Range::new('f', 'z'))));
        let rep_class = ctx.repetition(ctx.class(iter::once(Range::new('A', 'Z'))));

        let sut1 = ctx.alteration(
            ctx.alteration(class.clone(), neg_class.clone()),
            rep_class.clone(),
        );
        let sut2 = ctx.alteration(class, ctx.alteration(neg_class, rep_class));

        assert_eq!(sut1, sut2);
    }

    #[test]
    fn and_with_empty_class_is_empty_class() {
        let ctx = RegexContext::<char>::new();
        let empty_class = ctx.class(Vec::new());
        let empty = ctx.empty();
        let neg_empty = ctx.complement(empty);

        let sut = ctx.and(empty_class, neg_empty);

        assert_matches!(sut.kind(), RegexKind::Class(class)=> {
            assert!(class.is_empty())
        });
    }

    #[test]
    fn and_with_complement_of_empty_class_is_other_value() {
        let ctx = RegexContext::<char>::new();
        let empty_class = ctx.class(Vec::new());
        let empty = ctx.empty();
        let neg_empty = ctx.complement(empty_class);

        let sut = ctx.and(empty, neg_empty);

        assert_matches!(sut.kind(), RegexKind::Empty);
    }

    #[test]
    fn and_with_equal_terms_is_that_term() {
        let ctx = RegexContext::new();
        let expected = vec![Range::new('a', 'c')];
        let class1 = ctx.class(expected.clone());
        let class2 = ctx.class(expected.clone());

        let sut = ctx.and(class1, class2);

        assert_matches!(sut.kind(), RegexKind::Class(class) => {
            let ranges: Vec<Range<_>> = class.ranges().collect();
            assert_eq!(ranges, expected);
        });
    }

    #[test]
    fn and_is_commutative() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        let neg_class = ctx.complement(ctx.class(iter::once(Range::new('f', 'z'))));

        let sut1 = ctx.and(class.clone(), neg_class.clone());
        let sut2 = ctx.and(neg_class, class);

        assert_eq!(sut1, sut2);
    }

    #[test]
    fn and_is_associative() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        let neg_class = ctx.complement(ctx.class(iter::once(Range::new('f', 'z'))));
        let rep_class = ctx.repetition(ctx.class(iter::once(Range::new('A', 'Z'))));

        let sut1 = ctx.and(ctx.and(class.clone(), neg_class.clone()), rep_class.clone());
        let sut2 = ctx.and(class, ctx.and(neg_class, rep_class));

        assert_eq!(sut1, sut2);
    }
}
