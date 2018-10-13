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
use std::fmt::{self, Debug};

use std::ops::Index;

use alphabet::Alphabet;
use itertools::Itertools;
use label::{StateLabel, TransitionLabel};
use partition::PartitionMap;
use regex::RegexContext;
use typed_arena::Arena;

/// A deterministic finite automaton generated from a regular expression or
/// a regular vector.
///
/// Dfa is generic over its `Alphabet` and over its `StateLabel`. The primary
/// types that implement `Alphabet` are `char` (for Unicode) and `u8` (for ASCII).
/// The primary types that implement `StateLabel` are `Regex` and (in future) a
/// type that represents regular vectors.
#[derive(Debug)]
pub struct Dfa<'a, A, S>
where
    A: Alphabet + 'a,
    S: StateLabel<'a, A>,
{
    states: Vec<RegexState<'a, A, S>>,
    start: StateIdx,
    error: Option<StateIdx>,
}

/// A state in a `Dfa`.
pub trait State<A: Alphabet, T> {
    /// Get the `DerivativeClasses` for this state.
    fn classes(&self) -> &DerivativeClasses<A>;

    /// Get the label for this state.
    fn label(&self) -> &T;

    /// Get the index of the state to which to transisiton for a particular label.
    ///
    /// The relevant `TransitionLabel`'s for this state are part of the states's
    /// `DerivativeClasses` returned by classes().
    fn transition(&self, label: TransitionLabel) -> Option<StateIdx>;

    /// Predicate to check if this state is an accepting state.
    fn is_accepting(&self) -> bool;
}

/// A state in a `Dfa` associated with a regular expression.
///
/// Each state has a label (of a type that implements `StateLabel`), a set
/// of DerivativeClasses that map elements of the `Alphabet` to a transitions
/// (using a TransitionLabel), and the transisitions themselves that identify
/// the state to which the transition when for a particular subset of the `Alphabet`
/// identifed by a particular `TransitionLabel`.
pub struct RegexState<'a, A, S>
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
    S: StateLabel<'a, A> + Clone,
{
    /// Generate a new `Dfa` for the `start` regular expression or regular vector.
    pub fn new(start: S, ctx: &'a RegexContext<'a, A>) -> Dfa<A, S> {
        // This is an iterative implementation of the recursive DFA construction
        // algorithm using RE derivatives and character classes given in Figure 3
        // of Owens et al.
        use std::collections::hash_map::Entry::*;

        let arena = Arena::new(); // manage lifetimes of the derivative class ranges
        let mut states = Vec::new(); // the states in the DFA
        let mut map = HashMap::new(); // implementation of "∃q' ∈ Q such that q' ≈ q"
        let mut stack = Vec::new(); // the (index, iterator) stack for "recursion"

        // add the start state
        let mut curr = states.len();
        states.push(RegexState::new(start.clone(), ctx));
        map.insert(start.clone(), curr);

        // the explore() function from Figure 3
        'explore: loop {
            // - the argument to alloc_extend() is C(q) where states[curr] is q
            // - iterating over 'iter' in goto() is fold(goto q) except that the
            //   items in the iteration are both the TransitionLabel ("S") and the
            //   representative character ("c ∈ S") for that derivative class subset.
            let mut iter = arena
                .alloc_extend(
                    states[curr]
                        .classes()
                        .ranges()
                        .unique_by(|&(_, trans)| trans),
                )
                .iter();

            // the goto() function from Figure 3
            'goto: loop {
                match iter.next() {
                    Some((a, trans)) => {
                        let derivative = states[curr].label().clone().derivative(&a, ctx);

                        // "if ∃q' ∈ Q such that q' ≈ q"
                        match map.entry(derivative.clone()) {
                            Occupied(occ) => {
                                // add a transition to an existing state
                                states[curr].add_transition(*trans, StateIdx(*occ.get() as u32));
                            }

                            Vacant(vac) => {
                                // add a new state for "derivative"
                                let new_idx = states.len();
                                states.push(RegexState::new(derivative, ctx));
                                vac.insert(new_idx);

                                // add a transition to the new state
                                states[curr].add_transition(*trans, StateIdx(new_idx as u32));

                                // "recurse" into explore()
                                stack.push((curr, iter));
                                curr = new_idx;
                                continue 'explore;
                            }
                        }
                    }

                    None => match stack.pop() {
                        // "recurse" out of the current explore()
                        Some((c, i)) => {
                            curr = c;
                            iter = i;
                        }

                        // no more derivative class subsets for the current state and
                        // no more states on the stack so we are done
                        None => break 'explore,
                    },
                }
            }
        }

        Dfa {
            states,
            start: map.get(&start.clone())
                .map(|&idx| StateIdx(idx as u32))
                .unwrap(),
            error: map.get(&S::error(&start, ctx))
                .map(|&idx| StateIdx(idx as u32)),
        }
    }

    /// Iterator over the states of the `Dfa`.
    pub fn states(&self) -> impl Iterator<Item = &RegexState<'a, A, S>> {
        (&self.states).into_iter()
    }

    /// Iterator over the indexes of the states of the `Dfa`.
    pub fn state_idx(&'a self) -> impl Iterator<Item = StateIdx> + 'a {
        (&self.states)
            .into_iter()
            .enumerate()
            .map(|(i, _)| StateIdx(i as u32))
    }

    /// Get the index of the start state of the `Dfa`.
    pub fn start(&self) -> StateIdx {
        self.start
    }

    /// Get the index of the error state of the `Dfa` (if any).
    pub fn error(&self) -> Option<StateIdx> {
        self.error
    }
}

impl<'a, A, S> Index<StateIdx> for Dfa<'a, A, S>
where
    A: Alphabet,
    S: StateLabel<'a, A>,
{
    type Output = RegexState<'a, A, S>;

    /// Get a `State` in the `Dfa` given its `StateIdx`.
    fn index(&self, index: StateIdx) -> &Self::Output {
        &self.states[index.0 as usize]
    }
}

impl<'a, A, S> RegexState<'a, A, S>
where
    A: Alphabet,
    S: StateLabel<'a, A> + Clone,
{
    fn new(label: S, ctx: &'a RegexContext<'a, A>) -> RegexState<'a, A, S> {
        let classes = label.derivative_classes(ctx);
        RegexState {
            label,
            classes,
            ctx,
            transitions: HashMap::new(),
        }
    }

    fn add_transition(&mut self, label: TransitionLabel, state: StateIdx) {
        self.transitions.insert(label, state);
    }
}

impl<'a, A, S> State<A, S> for RegexState<'a, A, S>
where
    A: Alphabet,
    S: StateLabel<'a, A> + Clone,
{
    /// Get the `DerivativeClasses` for this `RegexState`.
    fn classes(&self) -> &DerivativeClasses<A> {
        &self.classes
    }

    /// Get the label (regular expression or regular vector) for this `RegexState`.
    fn label(&self) -> &S {
        &self.label
    }

    /// Get the index of the state to which to transition for a particular label.
    ///
    /// The relevant `TransitionLabel`'s for this `RegexState` are part of the state's
    /// `DerivativeClasses` returned by classes().
    fn transition(&self, label: TransitionLabel) -> Option<StateIdx> {
        self.transitions.get(&label).map(|&idx| idx)
    }

    /// Predicate to check if this `RegexState` is an accepting state.
    fn is_accepting(&self) -> bool {
        self.label.clone().is_accepting(self.ctx)
    }
}

impl<'a, A, S> Debug for RegexState<'a, A, S>
where
    A: Alphabet + Debug + 'a,
    S: StateLabel<'a, A> + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("RegexState")
            .field("label", &self.label)
            .field("classes", &self.classes)
            .field("transisitons", &self.transitions)
            .finish()
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
    use regex::Range;
    use std::iter;
    use testutils::TestAlpha;

    #[test]
    fn new_state_has_provided_label() {
        let ctx = RegexContext::new();
        let label = FakeLabel {
            id: 2,
            ..Default::default()
        };

        let sut = RegexState::new(label.clone(), &ctx);

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

        let sut = RegexState::new(label, &ctx);
        let transitions = sut.classes().ranges().map(|(k, _)| k).collect_vec();

        assert_eq!(transitions, vec![A, B, C]);
    }

    #[test]
    fn state_added_transition_appears_as_a_transition() {
        let ctx = RegexContext::new();
        let label = FakeLabel::default();
        let idx = StateIdx(3);

        let mut sut = RegexState::new(label, &ctx);
        let tr = sut.classes().ranges().map(|(_, tr)| tr).next().unwrap();
        sut.add_transition(tr, idx);

        assert_eq!(sut.transition(tr), Some(idx));
    }

    #[test]
    fn simple_new_dfa_contains_expected_states() {
        let ctx = RegexContext::new();
        let regex = ctx.class(iter::once(Range::new('a', 'a')));
        let empty = ctx.empty();
        let error = ctx.class(iter::empty());

        let sut = Dfa::new(regex, &ctx);
        let states: Vec<_> = sut.states().collect();

        assert_eq!(states.len(), 3);
        for state in states {
            assert!(state.label() == &regex || state.label() == &empty || state.label() == &error);
        }
    }

    #[test]
    fn owens_new_dfa_has_expect_number_of_state() {
        // this test the dfa from Figure 2 of Owens et al.; the regex is "ab|ac"
        let ctx = RegexContext::new();
        let regex = ctx.alternation(
            ctx.concat(
                ctx.class(iter::once(Range::new('a', 'a'))),
                ctx.class(iter::once(Range::new('b', 'b'))),
            ),
            ctx.concat(
                ctx.class(iter::once(Range::new('a', 'a'))),
                ctx.class(iter::once(Range::new('c', 'c'))),
            ),
        );

        let sut = Dfa::new(regex, &ctx);

        assert_eq!(sut.states().count(), 4);
    }

    #[test]
    fn simple_new_dfa_for_regular_vector_has_expect_number_of_state() {
        let ctx = RegexContext::new();
        let vec = ctx.vec(
            vec![
                ctx.concat(
                    ctx.class(iter::once(Range::new('a', 'a'))),
                    ctx.class(iter::once(Range::new('b', 'b'))),
                ),
                ctx.concat(
                    ctx.class(iter::once(Range::new('a', 'a'))),
                    ctx.class(iter::once(Range::new('c', 'c'))),
                ),
            ].into_iter(),
        );

        let sut = Dfa::new(vec, &ctx);

        assert_eq!(sut.states().count(), 5);
    }
}
