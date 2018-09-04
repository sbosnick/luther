// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

//! The types that define a deterministic finite automaton that can be generated
//! from either a regular expression or a regular vector.
//!
//! A `Dfa` over an `Alphabet` is a set of `State's`, one of which is the start
//! state and, optionally, one of which is the error state. Some of the states
//! may also be identified as accepting states. The states have transisitons to
//! other states.
//!
//! The states are labeled with either a `Regex` or (in future) a regular vector. The types that
//! can act as state labels implement StateLabel. Each state also has `DerivativeClasses` which
//! are a partition of the `Alphabet` into subsets which require a single transition for all of
//! the elements in a particular subset.
//!
//! The `DerivativeClasses` associated with a state map elements of the `Alphabet` to
//! `TransitionLabel's`, which in turn map a transition from one state to the next.
//!
//! The primary `Alphabet's` over which you can construct a `Dfa` are `char` (for Unicode) and
//! `u8` (for ASCII).

use std::collections::HashMap;
use std::iter;
use std::marker::PhantomData;
use std::ops::Index;

use alphabet::Alphabet;
use label::{StateLabel, TransitionLabel};
use partition::PartitionMap;
use regex::RegexContext;

/// A deterministic finite automaton generated from a regular expression or
/// a regular vector.
///
/// Dfa is generic over its `Alphabet` and over its `StateLabel`. The primary
/// types that implement `Alphabet` are `char` (for Unicode) and `u8` (for ASCII).
/// The primary types that implement `StateLabel` are `Regex` and (in future) a
/// type that represents regular vectors.
pub struct Dfa<'a, A, S>
where
    A: Alphabet + 'a,
    S: StateLabel<'a, A>,
{
    _phantom: PhantomData<&'a A>,
    _label: PhantomData<S>,
}

/// A state in a `Dfa`.
///
/// Each state has a label (of a type that implements `StateLabel`), a set
/// of DerivativeClasses that map elements of the `Alphabet` to a transitions
/// (using a TransitionLabel), and the transisitions themselves that identify
/// the state to which the transition when for a particular subset of the `Alphabet`
/// identifed by a particular `TransitionLabel`.
pub struct State<'a, A, S>
where
    A: Alphabet + 'a,
    S: StateLabel<'a, A>,
{
    label: S,
    classes: DerivativeClasses<A>,
    ctx: &'a RegexContext<'a, A>,
    transitions: HashMap<TransitionLabel, StateIdx>,
}

/// The index of a particular state in a `Dfa`.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct StateIdx(u32);

/// The DerivativeClasses are a partition of the `Alphabet` into subsets whose
/// Brzozowski derivatives for a specified regular expression (or regular vector)
/// are equivalant for each member of the subset.
#[derive(Debug, PartialEq, Clone)]
pub struct DerivativeClasses<A: Alphabet> {
    map: PartitionMap<A, TransitionLabel>,
}

impl<'a, A, S> Dfa<'a, A, S>
where
    A: Alphabet,
    S: StateLabel<'a, A>,
{
    /// Generate a new `Dfa` for the `start` regular expression or regular vector.
    ///
    /// The `Dfa` will take ownership of `ctx`.
    pub fn new(_start: S, _ctx: RegexContext<'a, A>) -> Dfa<A, S> {
        unimplemented!()
    }

    /// Iterator over the states of the `Dfa`.
    pub fn states(&self) -> impl Iterator<Item = &State<'a, A, S>> {
        iter::empty()
    }

    /// Iterator over the indexes of the states of the `Dfa`.
    pub fn state_idx(&self) -> impl Iterator<Item = StateIdx> {
        iter::empty()
    }

    /// Get the index of the start state of the `Dfa`.
    pub fn start(&self) -> StateIdx {
        unimplemented!()
    }

    /// Get the index of the error state of the `Dfa` (if any).
    pub fn error(&self) -> Option<StateIdx> {
        unimplemented!()
    }
}

impl<'a, A, S> Index<StateIdx> for Dfa<'a, A, S>
where
    A: Alphabet,
    S: StateLabel<'a, A>,
{
    type Output = State<'a, A, S>;

    /// Get a `State` in the `Dfa` given its `StateIdx`.
    fn index(&self, _index: StateIdx) -> &Self::Output {
        unimplemented!()
    }
}

impl<'a, A, S> State<'a, A, S>
where
    A: Alphabet,
    S: StateLabel<'a, A>,
{
    fn new(label: S, ctx: &'a RegexContext<'a, A>) -> State<'a, A, S> {
        let classes = label.derivative_classes(ctx);
        State {
            label,
            classes,
            ctx,
            transitions: HashMap::new(),
        }
    }

    fn add_transition(&mut self, label: TransitionLabel, state: StateIdx) {
        self.transitions.insert(label, state);
    }

    /// Get the `DerivativeClasses` for this `State`.
    pub fn classes(&self) -> &DerivativeClasses<A> {
        &self.classes
    }

    /// Get the label (regular expression or regular vector) for this `State`.
    pub fn label(&self) -> &S {
        &self.label
    }

    /// Get the index of the state to which to transition for a particular label.
    ///
    /// The relevant `TransitionLabel`'s for this `State` are part of the state's
    /// `DerivativeClasses` returned by classes().
    pub fn transition(&self, label: TransitionLabel) -> Option<StateIdx> {
        self.transitions.get(&label).map(|&idx| idx)
    }

    /// Predicate to check if this `State` is an accepting state.
    pub fn is_accepting(&self) -> bool {
        self.label.is_accepting(self.ctx)
    }
}

impl<A: Alphabet> DerivativeClasses<A> {
    pub(crate) fn new(map: PartitionMap<A, TransitionLabel>) -> DerivativeClasses<A> {
        DerivativeClasses { map }
    }

    /// Iterate over the half-open ranges that comprise the DerivativeClasses.
    ///
    /// The half-open ranges are represented by the (inclusive) lower bound of the
    /// range. The (exclusive) upper bound of a range is represented by the lower
    /// bound of the next range. Since the `DerivativeClasses` form a partition of
    /// the `Alphabet` this is well defined.
    ///
    /// The lower bound of the range is paired with the `TransitionLabel` applicable
    /// the subset to which this range belongs. In the general case, there will be
    /// multiple ranges that belong to the same subset and, hence, have the same
    /// `TransitionLabel`.
    pub fn ranges<'a>(&'a self) -> impl Iterator<Item = (A, TransitionLabel)> + 'a {
        self.map.ranges().map(|(a, label)| (a.clone(), *label))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use itertools::Itertools;
    use label::FakeLabel;
    use testutils::TestAlpha;

    #[test]
    fn new_state_has_provided_label() {
        let ctx = RegexContext::new();
        let label = FakeLabel {
            id: 2,
            ..Default::default()
        };

        let sut = State::new(label.clone(), &ctx);

        assert_eq!(sut.label(), &label);
    }

    #[test]
    fn new_state_has_expected_classes() {
        use self::TestAlpha::*;
        let ctx = RegexContext::new();
        let label = FakeLabel {
            id: 2,
            classes: (B, C),
            ..Default::default()
        };

        let sut = State::new(label, &ctx);
        let transitions = sut.classes().ranges().map(|(k, _)| k).collect_vec();

        assert_eq!(transitions, vec![A, B, C]);
    }

    #[test]
    fn state_is_accepting_delegates_to_label() {
        let ctx = RegexContext::new();
        let label = FakeLabel::default();

        let sut = State::new(label, &ctx);
        sut.is_accepting();

        assert!(sut.label().is_accepting_called.get());
    }

    #[test]
    fn state_added_transition_appears_as_a_transition() {
        let ctx = RegexContext::new();
        let label = FakeLabel::default();
        let idx = StateIdx(3);

        let mut sut = State::new(label, &ctx);
        let tr = sut.classes().ranges().map(|(_, tr)| tr).next().unwrap();
        sut.add_transition(tr, idx);

        assert_eq!(sut.transition(tr), Some(idx));
    }
}
