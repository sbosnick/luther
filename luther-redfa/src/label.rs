// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter;

use alphabet::Alphabet;
use dfa::DerivativeClasses;
use itertools::Itertools;
use partition::{MergeValue, Partition};
use regex::{Regex, RegexContext, RegexKind, RegexVec};

/// StateLabel describes types that can be used to generate a deterministic
/// finite automaton (DFA).
///
/// The types that implement StateLabel can be used to label the states of
/// the generated DFA.
///
/// This trait is sealed and cannot be implemented for types outside of
/// `luther-redfa`.
pub trait StateLabel<'a, A: Alphabet>: Hash + Eq + private::Sealed {
    /// Calculate the Brzozowski derivative of a `StateLabel` with respect to
    /// the characther `c` from the `Alphabet` `A`.
    fn derivative(self, c: &A, ctx: &'a RegexContext<'a, A>) -> Self;

    /// Predicate to determine if a state in the DFA labeled with `self`
    /// is an accepting state.
    fn is_accepting(self, ctx: &'a RegexContext<'a, A>) -> bool;

    /// Create the label for the error state in a generated DFA.
    fn error(&self, ctx: &'a RegexContext<'a, A>) -> Self;

    /// Create the derivative classes for the state labeled by self.
    fn derivative_classes(&self, ctx: &'a RegexContext<'a, A>) -> DerivativeClasses<A>;
}

/// Labels the transitions in a deterministic finite automaton.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct TransitionLabel(u32);

impl TransitionLabel {
    fn first() -> TransitionLabel {
        TransitionLabel(0)
    }

    fn second() -> TransitionLabel {
        TransitionLabel(1)
    }
}

struct TransitionLabelMerger {
    current: Option<(TransitionLabel, TransitionLabel)>,
    map: HashMap<(TransitionLabel, TransitionLabel), TransitionLabel>,
    next: u32,
}

impl TransitionLabelMerger {
    fn new() -> TransitionLabelMerger {
        TransitionLabelMerger {
            current: None,
            map: HashMap::new(),
            next: 0,
        }
    }

    // This is an internal methond designed to be called from the next_* methods
    // and not called directly.
    fn next(&mut self, current: (TransitionLabel, TransitionLabel)) -> TransitionLabel {
        self.current = Some(current);
        let next = &mut self.next;

        *self.map.entry(current).or_insert_with(|| {
            let value = *next;
            *next += 1;
            TransitionLabel(value)
        })
    }
}

impl MergeValue<TransitionLabel> for TransitionLabelMerger {
    fn next_left(&mut self, l: TransitionLabel) -> TransitionLabel {
        match self.current {
            None => panic!("TransitionLabelMerger: next_left() called before next_both()."),
            Some((_, r)) => self.next((l, r)),
        }
    }

    fn next_right(&mut self, r: TransitionLabel) -> TransitionLabel {
        match self.current {
            None => panic!("TransitionLabelMerger: next_right() called before next_both()."),
            Some((l, _)) => self.next((l, r)),
        }
    }

    fn next_both(&mut self, left: TransitionLabel, right: TransitionLabel) -> TransitionLabel {
        self.next((left, right))
    }
}

trait Nullable<'a, A: Alphabet> {
    fn nullable(&self, ctx: &'a RegexContext<'a, A>) -> Self;
}

impl<'a, A: Alphabet> Nullable<'a, A> for Regex<'a, A> {
    fn nullable(&self, ctx: &'a RegexContext<'a, A>) -> Self {
        use self::RegexKind::*;

        // this is the from the defintion of ν(r) in section 3.1 and 4.2 of Owen et al.
        match self.kind() {
            Empty => ctx.empty(),
            Class(_) => ctx.class(iter::empty()),
            Concat(concat) => ctx.and(concat.first().nullable(ctx), concat.second().nullable(ctx)),
            Alternation(alt) => {
                ctx.alternation(alt.first().nullable(ctx), alt.second().nullable(ctx))
            }
            Repetition(_) => ctx.empty(),
            And(and) => ctx.and(and.first().nullable(ctx), and.second().nullable(ctx)),
            Complement(comp) if is_nullable(comp.inner(), ctx) => ctx.class(iter::empty()),
            Complement(_) => ctx.empty(),
        }
    }
}

impl<'a, A: Alphabet> StateLabel<'a, A> for Regex<'a, A> {
    fn derivative(self, c: &A, ctx: &'a RegexContext<'a, A>) -> Self {
        use self::RegexKind::*;

        // this is from the rules for computing ∂ for a regular expression in
        // sections 3.1 and 4.2 of Owen et al.
        match self.kind() {
            Empty => ctx.class(iter::empty()),
            Class(class) if class.contains(c) => ctx.empty(),
            Class(_) => ctx.class(iter::empty()),
            Concat(concat) => ctx.alternation(
                ctx.concat(concat.first().derivative(c, ctx), concat.second()),
                ctx.concat(
                    concat.first().nullable(ctx),
                    concat.second().derivative(c, ctx),
                ),
            ),
            Repetition(rep) => {
                ctx.concat(rep.inner().derivative(c, ctx), ctx.repetition(rep.inner()))
            }
            Alternation(alt) => ctx.alternation(
                alt.first().derivative(c, ctx),
                alt.second().derivative(c, ctx),
            ),
            And(and) => ctx.and(
                and.first().derivative(c, ctx),
                and.second().derivative(c, ctx),
            ),
            Complement(comp) => ctx.complement(comp.inner().derivative(c, ctx)),
        }
    }

    fn is_accepting(self, ctx: &'a RegexContext<'a, A>) -> bool {
        is_nullable(self.clone(), ctx)
    }

    fn error(&self, ctx: &'a RegexContext<'a, A>) -> Self {
        ctx.class(iter::empty())
    }

    fn derivative_classes(&self, ctx: &'a RegexContext<'a, A>) -> DerivativeClasses<A> {
        DerivativeClasses::new(regex_to_partition_map(self.clone(), ctx))
    }
}

impl<'a, A: Alphabet + Debug> StateLabel<'a, A> for RegexVec<'a, A> {
    fn derivative(self, c: &A, ctx: &'a RegexContext<'a, A>) -> Self {
        self.map(ctx, |re| re.derivative(c, ctx))
    }

    fn is_accepting(self, ctx: &'a RegexContext<'a, A>) -> bool {
        self.any(|re| re.is_accepting(ctx))
    }

    fn error(&self, ctx: &'a RegexContext<'a, A>) -> Self {
        ctx.vec(iter::repeat(ctx.class(iter::empty())).take(self.len()))
    }

    fn derivative_classes(&self, ctx: &'a RegexContext<'a, A>) -> DerivativeClasses<A> {
        DerivativeClasses::new(
            self.map_elements(move |re| regex_to_partition_map(re, ctx))
                .into_iter()
                .fold1(|left, right| {
                    Partition::from_merge(left, right, &mut TransitionLabelMerger::new())
                })
                .unwrap_or_else(|| {
                    Partition::new(.., TransitionLabel::first(), TransitionLabel::second())
                }),
        )
    }
}

fn regex_to_partition_map<'a, A: Alphabet>(
    regex: Regex<'a, A>,
    ctx: &'a RegexContext<'a, A>,
) -> Partition<A, TransitionLabel> {
    use self::RegexKind::*;

    let first = TransitionLabel::first();
    let second = TransitionLabel::second();

    match regex.kind() {
        Empty => Partition::new(.., first, second),
        Class(class) => class.into_partition_map(first, second),
        Repetition(rep) => regex_to_partition_map(rep.inner(), ctx),
        Complement(comp) => regex_to_partition_map(comp.inner(), ctx),
        Concat(concat) if !is_nullable(concat.first(), ctx) => {
            regex_to_partition_map(concat.first(), ctx)
        }
        Concat(concat) => pm_from_merge(concat.first(), concat.second(), ctx),
        Alternation(alt) => pm_from_merge(alt.first(), alt.second(), ctx),
        And(and) => pm_from_merge(and.first(), and.second(), ctx),
    }
}

fn is_nullable<'a, A: Alphabet>(regex: Regex<'a, A>, ctx: &'a RegexContext<'a, A>) -> bool {
    regex.nullable(ctx) == ctx.empty()
}

fn pm_from_merge<'a, A: Alphabet>(
    first: Regex<'a, A>,
    second: Regex<'a, A>,
    ctx: &'a RegexContext<'a, A>,
) -> Partition<A, TransitionLabel> {
    Partition::from_merge(
        regex_to_partition_map(first, ctx),
        regex_to_partition_map(second, ctx),
        &mut TransitionLabelMerger::new(),
    )
}

#[cfg(test)]
pub(crate) use self::test::FakeLabel;

mod private {
    pub trait Sealed {}

    impl<'a, A: super::Alphabet> Sealed for super::Regex<'a, A> {}

    impl<'a, A: super::Alphabet> Sealed for super::RegexVec<'a, A> {}

    #[cfg(test)]
    impl Sealed for super::FakeLabel {}
}

#[cfg(test)]
mod test {
    use super::*;
    use regex::Range;
    use std::collections::HashSet;
    use std::hash::{Hash, Hasher};
    use testutils::TestAlpha;

    // FakeLabel is a test double used to test dfa::State. It is in
    // this module StateLabel is a sealed trait and to be able
    // to access the private constructors of TransitionLabel.
    #[derive(Debug, Clone)]
    pub struct FakeLabel {
        pub id: u32,
        pub classes: (::testutils::TestAlpha, ::testutils::TestAlpha),
        pub is_accepting_called: ::std::cell::Cell<bool>,
    }

    impl Default for FakeLabel {
        fn default() -> Self {
            FakeLabel {
                id: 0,
                classes: (::testutils::TestAlpha::A, ::testutils::TestAlpha::E),
                is_accepting_called: ::std::cell::Cell::new(false),
            }
        }
    }

    impl Hash for FakeLabel {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.id.hash(state);
        }
    }

    impl PartialEq for FakeLabel {
        fn eq(&self, other: &FakeLabel) -> bool {
            self.id.eq(&other.id)
        }
    }

    impl Eq for FakeLabel {}

    impl<'a> StateLabel<'a, ::testutils::TestAlpha> for FakeLabel {
        fn derivative(
            self,
            _c: &::testutils::TestAlpha,
            _ctx: &'a RegexContext<'a, ::testutils::TestAlpha>,
        ) -> Self {
            unimplemented!()
        }

        fn is_accepting(self, _ctx: &'a RegexContext<'a, ::testutils::TestAlpha>) -> bool {
            self.is_accepting_called.set(true);
            true
        }

        fn error(&self, _ctx: &'a RegexContext<'a, ::testutils::TestAlpha>) -> Self {
            unimplemented!()
        }

        fn derivative_classes(
            &self,
            _ctx: &'a RegexContext<'a, ::testutils::TestAlpha>,
        ) -> DerivativeClasses<::testutils::TestAlpha> {
            DerivativeClasses::new(Partition::new(
                self.classes.0..self.classes.1,
                TransitionLabel::first(),
                TransitionLabel::second(),
            ))
        }
    }

    type TestCtx<'a> = RegexContext<'a, TestAlpha>;

    #[test]
    fn transition_label_merger_next_both_remembers_result() {
        let left = TransitionLabel::first();
        let right = TransitionLabel::second();

        let mut sut = TransitionLabelMerger::new();
        let first = sut.next_both(left, right);
        let second = sut.next_both(left, right);

        assert_eq!(first, second);
    }

    #[test]
    fn transistion_label_merger_next_both_does_not_duplicate_different_result() {
        let left = TransitionLabel::first();
        let right = TransitionLabel::second();

        let mut sut = TransitionLabelMerger::new();
        let first = sut.next_both(left, left);
        let second = sut.next_both(left, right);

        assert_ne!(first, second);
    }

    #[test]
    fn transition_label_merger_next_left_remembers_result() {
        let left = TransitionLabel::first();
        let right = TransitionLabel::second();

        let mut sut = TransitionLabelMerger::new();
        let first = sut.next_both(left, right);
        let second = sut.next_left(left);

        assert_eq!(first, second);
    }

    #[test]
    #[should_panic]
    fn transisiton_label_merger_initial_next_left_panics() {
        let left = TransitionLabel::first();

        let mut sut = TransitionLabelMerger::new();
        sut.next_left(left);
    }

    #[test]
    fn transition_label_merger_next_right_remembers_result() {
        let left = TransitionLabel::first();
        let right = TransitionLabel::second();

        let mut sut = TransitionLabelMerger::new();
        let first = sut.next_both(left, right);
        let second = sut.next_right(right);

        assert_eq!(first, second);
    }

    #[test]
    #[should_panic]
    fn transisiton_label_merger_initial_next_right_panics() {
        let right = TransitionLabel::first();

        let mut sut = TransitionLabelMerger::new();
        sut.next_right(right);
    }

    #[test]
    fn derivative_classes_of_empty_regex_have_one_subset() {
        let ctx = TestCtx::new();

        let sut = ctx.empty();
        let classes = sut.derivative_classes(&ctx);
        let ranges: Vec<_> = classes.ranges().collect();

        assert_eq!(ranges.len(), 1);
        assert_eq!(ranges[0].0, TestAlpha::A);
    }

    #[test]
    fn derivative_classes_of_class_regex_have_two_subsets() {
        use testutils::TestAlpha::*;
        let ctx = TestCtx::new();

        let sut = ctx.class(iter::once(Range::new(B, D)));
        let classes = sut.derivative_classes(&ctx);
        let ranges: HashSet<_> = classes.ranges().map(|(_, v)| v).collect();

        assert_eq!(ranges.len(), 2);
    }

    #[test]
    fn derivative_classes_of_complement_is_same_as_original() {
        use testutils::TestAlpha::*;
        let ctx = TestCtx::new();

        let sut = ctx.complement(ctx.repetition(ctx.class(iter::once(Range::new(B, D)))));
        let classes = sut.derivative_classes(&ctx);
        let ranges: HashSet<_> = classes.ranges().map(|(_, v)| v).collect();

        assert_eq!(ranges.len(), 2);
    }

    #[test]
    fn derivative_classes_of_and_is_intersecting_subsets() {
        use testutils::TestAlpha::*;
        let ctx = TestCtx::new();

        let sut = ctx.and(
            ctx.repetition(ctx.class(iter::once(Range::new(B, D)))),
            ctx.class(iter::once(Range::new(C, E))),
        );
        let classes = sut.derivative_classes(&ctx);
        let ranges: HashSet<_> = classes.ranges().map(|(_, v)| v).collect();

        assert_eq!(ranges.len(), 4);
    }

    #[test]
    fn derivative_classes_of_alternation_is_intersecting_subsets() {
        use testutils::TestAlpha::*;
        let ctx = TestCtx::new();

        let sut = ctx.alternation(
            ctx.repetition(ctx.class(iter::once(Range::new(B, D)))),
            ctx.class(iter::once(Range::new(C, E))),
        );
        let classes = sut.derivative_classes(&ctx);
        let ranges: HashSet<_> = classes.ranges().map(|(_, v)| v).collect();

        assert_eq!(ranges.len(), 4);
    }

    #[test]
    fn derivative_classes_of_nullable_concat_is_intersecting_subsets() {
        use testutils::TestAlpha::*;
        let ctx = TestCtx::new();

        let sut = ctx.concat(
            ctx.repetition(ctx.class(iter::once(Range::new(B, D)))),
            ctx.class(iter::once(Range::new(C, E))),
        );
        let classes = sut.derivative_classes(&ctx);
        let ranges: HashSet<_> = classes.ranges().map(|(_, v)| v).collect();

        assert_eq!(ranges.len(), 4);
    }

    #[test]
    fn derivative_classes_of_regex_vec_is_intersecting_subsets() {
        let ctx = RegexContext::new();
        let re1 = ctx.concat(
            ctx.class(iter::once(Range::new('a', 'a'))),
            ctx.class(iter::once(Range::new('b', 'b'))),
        );
        let re2 = ctx.concat(
            ctx.class(iter::once(Range::new('b', 'b'))),
            ctx.class(iter::once(Range::new('c', 'c'))),
        );

        let sut = ctx.vec(vec![re1, re2].into_iter());
        let classes = sut.derivative_classes(&ctx);
        let ranges: HashSet<_> = classes.ranges().map(|(_, v)| v).collect();

        assert_eq!(ranges.len(), 3);
    }
}
