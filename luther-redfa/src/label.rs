// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::iter;

use alphabet::Alphabet;
use regex::{Regex, RegexContext, RegexKind};

/// Label describes types that can be used to generate a deterministic
/// finite automaton (DFA).
///
/// The types that implement Label can be used to label the states of
/// the generated DFA.
///
/// This trait is sealed and cannot be implemented for types outside of
/// `luther-redfa`.
pub trait Label<'a, A: Alphabet>: private::Sealed {
    /// Calculate the Brzozowski derivative of a `Label` with respect to
    /// the characther `c` from the `Alphabet` `A`.
    fn derivative(&self, c: &A, ctx: &'a RegexContext<'a, A>) -> Self;

    /// Predicate to determine if a state in the DFA labeled with `self`
    /// is an accepting state.
    fn is_accepting(&self, ctx: &'a RegexContext<'a, A>) -> bool;

    /// Create the label for the error state in a generated DFA.
    fn error(ctx: &'a RegexContext<'a, A>) -> Self;
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
            Complement(comp) if comp.inner().nullable(ctx) == ctx.empty() => {
                ctx.class(iter::empty())
            }
            Complement(_) => ctx.empty(),
        }
    }
}

impl<'a, A: Alphabet> Label<'a, A> for Regex<'a, A> {
    fn derivative(&self, c: &A, ctx: &'a RegexContext<'a, A>) -> Self {
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

    fn is_accepting(&self, ctx: &'a RegexContext<'a, A>) -> bool {
        self.nullable(ctx) == ctx.empty()
    }

    fn error(ctx: &'a RegexContext<'a, A>) -> Self {
        ctx.class(iter::empty())
    }
}

mod private {
    pub trait Sealed {}

    impl<'a, A: super::Alphabet> Sealed for super::Regex<'a, A> {}
}
