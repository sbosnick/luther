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
use std::ops::Index;
use std::rc::Rc;

use alphabet::Alphabet;
use partition::{PartitionMap, PartitionSet, PartitionSetRangeIter};
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

impl<'a, A: Alphabet> RegexContext<'a, A> {
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
            kind: self.make_class(class),
        }
    }

    fn make_class(&'a self, class: Class<A>) -> &'a RegexKind<'a, A> {
        self.arena.alloc(RegexKind::Class(class))
    }

    /// Create a concatination `Regex`.
    ///
    /// The concatination regular expression matches the `lhs` regular
    /// expression followed by the `rhs` regular expression.
    pub fn concat(&'a self, lhs: Regex<'a, A>, rhs: Regex<'a, A>) -> Regex<A> {
        if lhs.kind.is_null() || rhs.kind.is_empty_string() {
            return lhs;
        };
        if rhs.kind.is_null() || lhs.kind.is_empty_string() {
            return rhs;
        };

        let (first, second) = match lhs.kind {
            RegexKind::Concat(concat) => (concat.first, self.make_concat(concat.second, rhs.kind)),
            _ => (lhs.kind, rhs.kind),
        };

        Regex {
            kind: self.make_concat(first, second),
        }
    }

    fn make_concat(
        &'a self,
        first: &'a RegexKind<'a, A>,
        second: &'a RegexKind<'a, A>,
    ) -> &'a RegexKind<'a, A> {
        self.arena
            .alloc(RegexKind::Concat(Concat { first, second }))
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

    /// Create an alternation (or logical-or) `Regex`.
    ///
    /// The alternation regular expression matches either the `lhs` regular
    /// expression or the `rhs` regular expression.
    pub fn alternation(&'a self, lhs: Regex<'a, A>, rhs: Regex<'a, A>) -> Regex<A> {
        if lhs.kind.is_null() || rhs.kind.is_complement_null() {
            return rhs;
        }
        if rhs.kind.is_null() || lhs.kind.is_complement_null() {
            return lhs;
        }
        if lhs.kind == rhs.kind {
            return lhs;
        }
        if let (RegexKind::Class(left), RegexKind::Class(right)) = (lhs.kind, rhs.kind) {
            return Regex {
                kind: self.make_class(left.union(right)),
            };
        }

        let (first, second) = order_operands(
            lhs.kind,
            rhs.kind,
            |f, s| self.make_alternation(f, s),
            get_alternation_operands,
        );

        Regex {
            kind: self.make_alternation(first, second),
        }
    }

    fn make_alternation(
        &'a self,
        first: &'a RegexKind<'a, A>,
        second: &'a RegexKind<'a, A>,
    ) -> &'a RegexKind<'a, A> {
        self.arena
            .alloc(RegexKind::Alternation(Alternation { first, second }))
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

        let (first, second) = order_operands(
            lhs.kind,
            rhs.kind,
            |first, second| self.make_and(first, second),
            get_and_operands,
        );

        Regex {
            kind: self.make_and(first, second),
        }
    }

    fn make_and(
        &'a self,
        first: &'a RegexKind<'a, A>,
        second: &'a RegexKind<'a, A>,
    ) -> &'a RegexKind<'a, A> {
        self.arena.alloc(RegexKind::And(And { first, second }))
    }

    /// Create a complement (or negation) `Regex`.
    ///
    /// The complement regular expression matches everything that the supplied
    /// `other` regular expression does not match.
    pub fn complement(&'a self, other: Regex<'a, A>) -> Regex<A> {
        let kind = match other.kind {
            RegexKind::Complement(complement) => complement.inner,
            RegexKind::Class(class) => self.make_class(class.complement()),
            _ => self.make_complement(other.kind),
        };

        Regex { kind }
    }

    fn make_complement(&'a self, inner: &'a RegexKind<'a, A>) -> &'a RegexKind<'a, A> {
        self.arena
            .alloc(RegexKind::Complement(Complement { inner }))
    }

    /// Create a `RegexVec` from an iterator of `Regex`'s.
    pub fn vec<I>(&'a self, iter: I) -> RegexVec<'a, A>
    where
        I: Iterator<Item = Regex<'a, A>>,
    {
        RegexVec {
            vec: self.arena.alloc_extend(iter.map(|r| (*r.kind).clone())),
        }
    }
}

/// A regular expression.
///
/// A `Regex` is created by the factory methods in `RegexContext` and is
/// associated with that context. It is not possible to create a `Regex`
/// directly. It is also not possible to create a `Regex` from a `RegexKind` in
/// order to allow `RegexContext` to maintain certain regular expressions in
/// cannonical form.
#[derive(Debug, PartialEq, Clone, Copy, Hash, Eq)]
pub struct Regex<'a, A: 'a + Alphabet> {
    kind: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Regex<'a, A> {
    /// Get the kind of the regular expression.
    pub fn kind(&self) -> &'a RegexKind<'a, A> {
        &self.kind
    }
}

/// The kind of a regular expression.
///
/// # Type Parameter
/// - A: the alphabet over which the regular expression operates
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
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

    /// A regular expression that matches two other regular expressions in sequence.
    Concat(Concat<'a, A>),

    /// A regular expression which matches 0 or more instances of a different
    /// regular expression.
    ///
    /// Note: The only kind of repetition that is directly supported is kleene star.
    Repetition(Repetition<'a, A>),

    /// A regular expression which matches either of two different regular
    /// expressions.
    Alternation(Alternation<'a, A>),

    /// A regular expression which matches both of two different regular
    /// expressions.
    And(And<'a, A>),

    /// A regular expression which matches the complement (or negation) of a different
    /// regular expression.
    Complement(Complement<'a, A>),
}

impl<'a, A: Alphabet> RegexKind<'a, A> {
    fn is_null(&self) -> bool {
        use self::RegexKind::*;

        match self {
            Class(class) if class.is_empty() => true,
            _ => false,
        }
    }

    fn is_complement_null(&self) -> bool {
        use self::RegexKind::*;

        match self {
            Class(class) if class.is_complement_empty() => true,
            _ => false,
        }
    }

    fn is_empty_string(&self) -> bool {
        use self::RegexKind::*;

        if let Empty = self {
            true
        } else {
            false
        }
    }
}

impl<'a, A: Alphabet> Display for RegexKind<'a, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::RegexKind::*;

        match self {
            Empty => write!(f, "Empty"),
            Class(_) => write!(f, "Class{{...}}"),
            Concat(concat) => write!(f, "Concat({}, {})", concat.first, concat.second),
            Repetition(rep) => write!(f, "Repetition({})", rep.inner),
            Alternation(alt) => write!(f, "Alternation({}, {})", alt.first, alt.second),
            And(and) => write!(f, "And({}, {})", and.first, and.second),
            Complement(comp) => write!(f, "Complement({})", comp.inner),
        }
    }
}

/// A regular vector.
///
/// A `RegexVec` is created by a factory method in `RegexContext` and is assocatied
/// with that context. It is not possible to create a `RegexVec` directly.
#[derive(Debug, PartialEq, Clone, Copy, Hash, Eq)]
pub struct RegexVec<'a, A: 'a + Alphabet> {
    vec: &'a [RegexKind<'a, A>],
}

impl<'a, A: Alphabet> RegexVec<'a, A> {
    /// Get the length of the `RegexVec`.
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Get the element of the `RegexVec` at `index`.
    ///
    /// Returns `None` if `index` is greater than `self.len()`.
    pub fn get(&self, index: usize) -> Option<&RegexKind<'a, A>> {
        self.vec.get(index)
    }
}

impl<'a, A: Alphabet> Index<usize> for RegexVec<'a, A> {
    type Output = RegexKind<'a, A>;

    fn index(&self, index: usize) -> &Self::Output {
        self.vec.index(index)
    }
}

/// A (possibly empty) subset of the alphabet `A`.
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
pub struct Class<A: Alphabet> {
    set: Rc<PartitionSet<A>>,
}

impl<A: Alphabet> Class<A> {
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

    /// Check if the subset of `A` is the complement of the empty set
    /// (i.e. it is every element in `A`).
    pub fn is_complement_empty(&self) -> bool {
        self.set.is_complement_empty()
    }

    /// Check if the class contains the character `c`.
    pub fn contains(&self, c: &A) -> bool {
        self.set.contains(c)
    }

    fn union(&self, other: &Class<A>) -> Class<A> {
        Class {
            set: Rc::new(self.set.union(&other.set)),
        }
    }

    fn complement(&self) -> Class<A> {
        Class {
            set: Rc::new(self.set.complement()),
        }
    }

    pub(crate) fn into_partition_map<V>(&self, in_value: V, out_value: V) -> PartitionMap<A, V>
    where
        V: Debug + Clone + PartialEq,
    {
        self.set.into_map(in_value, out_value)
    }
}

impl<A: Alphabet> FromIterator<Range<A>> for Class<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Range<A>>,
    {
        Class {
            set: Rc::new(iter.into_iter().collect()),
        }
    }
}

/// A regular expression holder for which the complement (or negation) has been
/// taken.
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
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
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
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
/// alternatives (through alternation).
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
pub struct Alternation<'a, A: 'a + Alphabet> {
    first: &'a RegexKind<'a, A>,
    second: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Alternation<'a, A> {
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
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
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

/// A regular expression holder for regular expressions being
/// concatenated.
#[derive(Debug, PartialEq, PartialOrd, Hash, Eq, Clone)]
pub struct Concat<'a, A: 'a + Alphabet> {
    first: &'a RegexKind<'a, A>,
    second: &'a RegexKind<'a, A>,
}

impl<'a, A: Alphabet> Concat<'a, A> {
    /// Gets the first of the regular expressons being concatenated.
    pub fn first(&'a self) -> Regex<'a, A> {
        Regex { kind: self.first }
    }

    /// Get the second of the regular expressions being concatenated.
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
fn order_operands<'a, A, F, G>(
    lhs: &'a RegexKind<'a, A>,
    rhs: &'a RegexKind<'a, A>,
    factory: F,
    get_operands: G,
) -> (&'a RegexKind<'a, A>, &'a RegexKind<'a, A>)
where
    A: Alphabet,
    F: Fn(&'a RegexKind<'a, A>, &'a RegexKind<'a, A>) -> &'a RegexKind<'a, A>,
    G: Fn(&'a RegexKind<'a, A>) -> Option<(&'a RegexKind<'a, A>, &'a RegexKind<'a, A>)>,
{
    if let Some((inner_first, inner_second)) = get_operands(lhs) {
        let (first, second, third) = order_third_operand(inner_first, inner_second, rhs);

        (first, factory(second, third))
    } else if let Some((inner_first, inner_second)) = get_operands(rhs) {
        let (first, second, third) = order_third_operand(inner_first, inner_second, lhs);

        (first, factory(second, third))
    } else if lhs < rhs {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}

// This function orders 'third' with respect to 'first' and 'second' assuming
// that 'first' and 'second' are already ordered with respect to each other.
fn order_third_operand<'a, A: Alphabet>(
    first: &'a RegexKind<'a, A>,
    second: &'a RegexKind<'a, A>,
    third: &'a RegexKind<'a, A>,
) -> (
    &'a RegexKind<'a, A>,
    &'a RegexKind<'a, A>,
    &'a RegexKind<'a, A>,
) {
    if third < first {
        (third, first, second)
    } else if third < second {
        (first, third, second)
    } else {
        (first, second, third)
    }
}

fn get_alternation_operands<'a, A: Alphabet>(
    kind: &'a RegexKind<'a, A>,
) -> Option<(&'a RegexKind<'a, A>, &'a RegexKind<'a, A>)> {
    if let RegexKind::Alternation(alt) = kind {
        Some((alt.first, alt.second))
    } else {
        None
    }
}

fn get_and_operands<'a, A: Alphabet>(
    kind: &'a RegexKind<'a, A>,
) -> Option<(&'a RegexKind<'a, A>, &'a RegexKind<'a, A>)> {
    if let RegexKind::And(and) = kind {
        Some((and.first, and.second))
    } else {
        None
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
    fn double_complement_regex_has_orginal_kind() {
        let ctx = RegexContext::new();
        let class = ctx.class(vec![Range::new('a', 'c')]);
        let complement = ctx.complement(class);

        let sut = ctx.complement(complement);

        assert_matches!(sut.kind(), &RegexKind::Class(_));
    }

    #[test]
    fn complement_of_class_is_class_of_complement() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('b', 'd')));
        let expected = ctx.class(vec![
            Range::new('\u{0}', 'a'),
            Range::new('e', ::std::char::MAX),
        ]);

        let sut = ctx.complement(class);

        assert_eq!(sut, expected);
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
    fn alternation_with_empty_class_is_other_value() {
        let ctx = RegexContext::<char>::new();
        let empty_class = ctx.class(Vec::new());
        let empty = ctx.empty();
        let neg_empty = ctx.complement(empty);

        let sut = ctx.alternation(empty_class, neg_empty);

        assert_matches!(sut.kind(), RegexKind::Complement(_));
    }

    #[test]
    fn alternation_with_complement_of_empty_class_is_complement_of_empty_class() {
        let ctx = RegexContext::<char>::new();
        let empty_class = ctx.class(Vec::new());
        let empty = ctx.empty();
        let neg_empty = ctx.complement(empty_class);

        let sut = ctx.alternation(empty, neg_empty);

        assert_matches!(sut.kind(), RegexKind::Class(class) => {
                assert!(class.is_complement_empty());
        });
    }

    #[test]
    fn alternation_with_equal_terms_is_that_term() {
        let ctx = RegexContext::new();
        let expected = vec![Range::new('a', 'c')];
        let class1 = ctx.class(expected.clone());
        let class2 = ctx.class(expected.clone());

        let sut = ctx.alternation(class1, class2);

        assert_matches!(sut.kind(), RegexKind::Class(class) => {
            let ranges: Vec<Range<_>> = class.ranges().collect();
            assert_eq!(ranges, expected);
        });
    }

    #[test]
    fn alternation_is_commutative() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        let neg_class = ctx.complement(ctx.class(iter::once(Range::new('f', 'z'))));

        let sut1 = ctx.alternation(class.clone(), neg_class.clone());
        let sut2 = ctx.alternation(neg_class, class);

        assert_eq!(sut1, sut2);
    }

    #[test]
    fn alternation_is_associative() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        // this forced formulation avoids simplifications that are not the sut
        let neg_class = Regex {
            kind: ctx.make_complement(ctx.class(iter::once(Range::new('f', 'z'))).kind),
        };
        let rep_class = ctx.repetition(ctx.class(iter::once(Range::new('A', 'Z'))));

        let sut1 = ctx.alternation(
            ctx.alternation(class.clone(), neg_class.clone()),
            rep_class.clone(),
        );
        let sut2 = ctx.alternation(class, ctx.alternation(neg_class, rep_class));

        assert_eq!(sut1, sut2);
    }

    #[test]
    fn alternation_re_orders_terms_for_associative_simplification() {
        let ctx = RegexContext::new();
        let first = ctx.class(iter::once(Range::new('a', 'c')));
        let second = ctx.empty();
        let third = ctx.repetition(ctx.class(iter::once(Range::new('d', 'f'))));

        let sut1 = ctx.alternation(
            first.clone(),
            ctx.alternation(second.clone(), third.clone()),
        );
        let sut2 = ctx.alternation(ctx.alternation(first, second), third);

        assert_eq!(sut1, sut2);
    }

    #[test]
    fn alternation_of_classes_is_union_of_class_elements() {
        let ctx = RegexContext::new();
        let class1 = ctx.class(iter::once(Range::new('a', 'c')));
        let class2 = ctx.class(iter::once(Range::new('f', 'm')));
        let expected = ctx.class(vec![Range::new('a', 'c'), Range::new('f', 'm')]);

        let sut = ctx.alternation(class1, class2);

        assert_eq!(sut, expected);
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

    #[test]
    fn and_with_alternation_does_not_associate() {
        let ctx = RegexContext::new();
        let class1 = ctx.class(iter::once(Range::new('a', 'c')));
        let class2 = ctx.repetition(ctx.class(iter::once(Range::new('f', 'm'))));
        let class3 = ctx.repetition(ctx.class(iter::once(Range::new('o', 'z'))));

        let sut = ctx.and(ctx.alternation(class1, class2), class3);

        assert_matches!(sut.kind(), RegexKind::And(and) => {
            assert_matches!(and.second().kind(), RegexKind::Alternation(_));
        });
    }

    #[test]
    fn concat_with_empty_class_is_empty_class() {
        let ctx = RegexContext::<char>::new();
        let empty_class = ctx.class(Vec::new());
        let neg_empty = ctx.complement(ctx.empty());

        let sut = ctx.concat(empty_class, neg_empty);

        assert_matches!(sut.kind(), RegexKind::Class(class)=> {
            assert!(class.is_empty())
        });
    }

    #[test]
    fn concat_with_empty_string_is_other_value() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        let empty = ctx.empty();

        let sut = ctx.concat(empty, class);

        assert_matches!(sut.kind(), RegexKind::Class(_));
    }

    #[test]
    fn concat_is_associative() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));
        let neg_class = ctx.complement(ctx.class(iter::once(Range::new('f', 'z'))));
        let rep_class = ctx.repetition(ctx.class(iter::once(Range::new('A', 'Z'))));

        let sut1 = ctx.concat(
            ctx.concat(class.clone(), neg_class.clone()),
            rep_class.clone(),
        );
        let sut2 = ctx.concat(class, ctx.concat(neg_class, rep_class));

        assert_eq!(sut1, sut2);
    }

    #[test]
    fn vec_has_expected_length() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));

        let sut = ctx.vec(iter::once(class));

        assert_eq!(sut.len(), 1);
    }

    #[test]
    fn vec_has_expected_item() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));

        let sut = ctx.vec(iter::once(class));

        assert_eq!(sut.get(0).unwrap(), class.kind())
    }

    #[test]
    fn vec_index_has_expected_item() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new('a', 'c')));

        let sut = ctx.vec(iter::once(class));

        assert_eq!(&sut[0], class.kind())
    }
}
