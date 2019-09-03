// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use alphabet::Alphabet;
use regex::{Regex, RegexKind, RegexVec, RegexVecIter};

/// Interface to allow a traversal of another type.
///
/// This is designed to allow a post-order, depth-first search
/// of a recursive type.
pub trait Traverse<'a, A: 'a + Alphabet> {

    /// The type of iterator that will conduct the traversal.
    type Iterator: Iterator<Item=Regex<'a, A>>;

    /// Conduct the traveral.
    fn traverse(self) -> Self::Iterator;
}

/// Iterator to visit the terms of a regular expression.
///
/// The resulting traveral of the regular expression is a
/// post-order, depth-first search.
pub struct RegexDfsIter<'a, A: 'a + Alphabet> {
    stack: Vec<Regex<'a, A>>,
    node: Option<Regex<'a,A>>,
    last_node: Option<Regex<'a, A>>,
}

/// Iterator to visit the terms of a regular vector.
///
/// The resulting traversal is a post-order, depth first
/// search of each of the regular expressions that make up
/// the regular vector in turn.
pub struct RegexVecDfsIter<'a, A: 'a + Alphabet> {
    inner: RegexVecIter<'a, A>,
    current: Option<RegexDfsIter<'a, A>>,
}

impl<'a, A: Alphabet> Traverse<'a, A> for Regex<'a, A> {
    type Iterator = RegexDfsIter<'a, A>;

    fn traverse(self) -> Self::Iterator {
        RegexDfsIter { stack: Vec::new(), node: Some(self), last_node: None }
    }
}

impl<'a, A: Alphabet> RegexDfsIter<'a, A> {
    fn push(&mut self, node: &Regex<'a, A>) {
        self.stack.push(node.clone());
    }

    fn pop(&mut self) -> Option<Regex<'a, A>> {
        self.last_node = self.stack.pop();
        self.last_node.clone()
    }

    fn is_last(&self, node: Regex<'a, A>) -> bool {
        match self.last_node {
            None => false,
            Some(ref n) => *n == node,
        }
    }
}

impl<'a, A: Alphabet> Iterator for RegexDfsIter<'a, A> {
    type Item = Regex<'a, A>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::RegexKind::*;

        // Handle the right children on the way up
        if let (None, Some(node)) = (self.node.clone(), self.stack.last()) {
            match node.kind() {
                And(and) if !self.is_last(and.second()) => {
                    self.node = Some(and.second());
                }
                Alternation(alt) if !self.is_last(alt.second()) => {
                    self.node = Some(alt.second());
                }
                Concat(cat) if !self.is_last(cat.second()) => {
                    self.node = Some(cat.second());
                }
                _ => {}
            };
        }

        // Handle the left children
        while let Some(node) = self.node.clone() {
            self.push(&node);
            match node.kind() {
                And(and) => self.node = Some(and.first()),
                Alternation(alt) => self.node = Some(alt.first()),
                Concat(cat) => self.node = Some(cat.first()),
                Complement(comp) => self.node = Some(comp.inner()),
                Repetition(rep) => self.node = Some(rep.inner()),
                _ => self.node = None,
            }
        }

        self.pop()
    }
}

impl<'a, A: Alphabet> Traverse<'a, A> for RegexVec<'a, A> {
    type Iterator = RegexVecDfsIter<'a, A>;

    fn traverse(self) -> Self::Iterator {
        let mut inner = self.iter();
        let current = next_dfs_iter(&mut inner);
        RegexVecDfsIter{ inner, current }
    }
}

impl<'a, A: Alphabet> Iterator for RegexVecDfsIter<'a, A> {
    type Item = Regex<'a, A>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let result = match self.current.as_mut() {
                Some(iter) => iter.next(),
                None => return None
            };

            match result {
                Some(re) => return Some(re),
                None => self.current = next_dfs_iter(&mut self.inner),
            };
        }
    }
}

fn next_dfs_iter<'a, A, I>(iter: &mut I) -> Option<RegexDfsIter<'a, A>>
where
    A: Alphabet,
    I: Iterator<Item = Regex<'a,A>>,
{
    iter.next().map(|re| re.traverse())
}

#[cfg(test)]
mod test {
    use super::*;
    use std::iter;
    use regex::{RegexContext, Range};
    use testutils::TestAlpha;

    #[test]
    fn traverse_empty_regex_has_empty_regex_term() {
        let ctx = RegexContext::<TestAlpha>::new();

        let sut = ctx.empty();
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![sut]);
    }

    #[test]
    fn traverse_class_regex_has_class_regext_term() {
        let ctx = RegexContext::new();

        let sut = ctx.class(iter::once(Range::new(TestAlpha::A, TestAlpha::B)));
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![sut]);
    }

    #[test]
    fn traverse_repetition_regex_has_two_terms() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new(TestAlpha::A, TestAlpha::B)));

        let sut = ctx.repetition(class);
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![class, sut]);
    }

    #[test]
    fn traverse_complement_repetition_has_three_terms() {
        let ctx = RegexContext::new();
        let class = ctx.class(iter::once(Range::new(TestAlpha::A, TestAlpha::B)));
        let rep = ctx.repetition(class);

        let sut = ctx.complement(rep);
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![class, rep, sut]);
    }

    #[test]
    fn traverse_concat_two_classes_has_three_terms() {
        let ctx = RegexContext::new();
        let class1 = ctx.class(iter::once(Range::new(TestAlpha::A, TestAlpha::B)));
        let class2 = ctx.class(iter::once(Range::new(TestAlpha::C, TestAlpha::D)));

        let sut = ctx.concat(class1, class2);
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![class1, class2, sut]);
    }

    #[test]
    fn traverse_alternation_repetition_has_five_terms() {
        let ctx = RegexContext::new();
        let class1 = ctx.class(iter::once(Range::new(TestAlpha::A, TestAlpha::B)));
        let class2 = ctx.class(iter::once(Range::new(TestAlpha::C, TestAlpha::D)));
        let rep1 = ctx.repetition(class1);
        let rep2 = ctx.repetition(class2);

        let sut = ctx.alternation(rep1, rep2);
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![class1, rep1, class2, rep2, sut]);
    }

    #[test]
    fn traverse_and_alternation_repetition_has_seven_terms() {
        let ctx = RegexContext::new();
        let class1 = ctx.class(iter::once(Range::new(TestAlpha::A, TestAlpha::B)));
        let class2 = ctx.class(iter::once(Range::new(TestAlpha::C, TestAlpha::D)));
        let class3 = ctx.class(iter::once(Range::new(TestAlpha::E, TestAlpha::E)));
        let rep1 = ctx.repetition(class1);
        let rep2 = ctx.repetition(class2);
        let alt = ctx.alternation(rep1, rep2);

        let sut = ctx.and(class3, alt);
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![class3, class1, rep1, class2, rep2, alt, sut]);
    }

    #[test]
    fn traverse_simple_regex_vec_has_three_terms() {
        let ctx = RegexContext::new();
        let class1 = ctx.class(iter::once(Range::new(TestAlpha::A, TestAlpha::B)));
        let class2 = ctx.class(iter::once(Range::new(TestAlpha::C, TestAlpha::D)));
        let rep = ctx.repetition(class1);

        let sut = ctx.vec(vec![rep, class2].into_iter());
        let result: Vec<_> = sut.traverse().collect();

        assert_eq!(result, vec![class1, rep, class2]);
    }
}
