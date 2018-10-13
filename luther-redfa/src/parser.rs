// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::fmt::{self, Display};
use std::iter;

use dfa::Dfa;
use failure::Fail;
use regex::{Range, Regex, RegexContext, RegexVec};
use regex_syntax::{
    self, hir::{self, visit, ClassUnicode, Hir, Visitor}, Parser,
};

/// The context for generating a deterministic finite automaton from either
/// a single regular expression or from a sequence of regular expressions.
pub struct DfaContext<'a> {
    ctx: RegexContext<'a, char>,
}

impl<'a> DfaContext<'a> {
    /// Create a new `DfaContext`.
    pub fn new() -> DfaContext<'a> {
        DfaContext {
            ctx: RegexContext::new(),
        }
    }

    /// Generate a `Dfa` from the regular expression given by `regex`.
    pub fn from_regex(&'a self, regex: &str) -> Result<Dfa<'a, char, Regex<'a, char>>> {
        let regex = parse_regex(regex, &self.ctx)?;
        Ok(Dfa::new(regex, &self.ctx))
    }

    /// Generate a `Dfa` from the regular vector formed by the regular expressions given
    /// by `regexes`.
    pub fn from_regex_vec<'b, I>(&'a self, regexes: I) -> Result<Dfa<'a, char, RegexVec<'a, char>>>
    where
        I: IntoIterator<Item = &'b str>,
    {
        let regexes = self.ctx.vec(
            regexes
                .into_iter()
                .map(|r| parse_regex(r, &self.ctx))
                .collect::<Result<Vec<_>>>()?
                .into_iter(),
        );
        Ok(Dfa::new(regexes, &self.ctx))
    }
}

/// The error type for parsing regular expressions while generating
/// a `Dfa`.
#[derive(Debug)]
pub struct Error {
    regex: String,
    message: &'static str,
    cause: Option<regex_syntax::Error>,
}

impl Error {
    fn parse(regex: &str, cause: regex_syntax::Error) -> Error {
        Error {
            regex: regex.to_string(),
            message: "unable to parse",
            cause: Some(cause),
        }
    }

    fn invalid_unicode(regex: &str) -> Error {
        Error {
            regex: regex.to_string(),
            message: "regex can match invalid unicode char's",
            cause: None,
        }
    }

    fn unexpected_end(regex: &str) -> Error {
        Error {
            regex: regex.to_string(),
            message: "parser unexpected reached the end of the regex",
            cause: None,
        }
    }

    fn anchor_unsupported(regex: &str) -> Error {
        Error {
            regex: regex.to_string(),
            message: "anchored regular expressions are not supported",
            cause: None,
        }
    }

    fn word_boundry_unsupported(regex: &str) -> Error {
        Error {
            regex: regex.to_string(),
            message: "regular expressions with word boudries are not supported",
            cause: None,
        }
    }

    fn non_greedy_unsupported(regex: &str) -> Error {
        Error {
            regex: regex.to_string(),
            message: "regular expressions with non-greedy repetition are not supported",
            cause: None,
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Invalid regular expressions (\"{}\"): {}",
            self.regex, self.message
        )
    }
}

impl Fail for Error {
    fn cause(&self) -> Option<&Fail> {
        match self.cause {
            Some(ref cause) => Some(cause),
            None => None,
        }
    }
}

/// A specilized `Result` type for creating `Dfa`'s
pub type Result<T> = ::std::result::Result<T, Error>;

fn parse_regex_to_hir(regex: &str) -> Result<Hir> {
    Parser::new()
        .parse(regex)
        .map_err(|err| Error::parse(regex, err))
}

fn parse_regex<'a>(regex: &str, ctx: &'a RegexContext<'a, char>) -> Result<Regex<'a, char>> {
    let hir = parse_regex_to_hir(regex)?;
    visit(&hir, RegexVisitor::new(regex, ctx))
}

struct RegexVisitor<'a, 'b> {
    regex: &'b str,
    ctx: &'a RegexContext<'a, char>,
    stack: Vec<Regex<'a, char>>,
}

impl<'a, 'b> RegexVisitor<'a, 'b> {
    fn new(regex: &'b str, ctx: &'a RegexContext<'a, char>) -> RegexVisitor<'a, 'b> {
        RegexVisitor {
            regex,
            ctx,
            stack: Vec::new(),
        }
    }

    fn push<F: Fn(&'a RegexContext<'a, char>) -> Regex<'a, char>>(&mut self, f: F) {
        self.stack.push(f(self.ctx))
    }

    fn pop(&mut self) -> Result<Regex<'a, char>> {
        self.stack
            .pop()
            .ok_or_else(|| Error::unexpected_end(self.regex))
    }

    fn fold_right<F>(&mut self, f: F, count: usize) -> Result<()>
    where
        F: Fn(&'a RegexContext<'a, char>, Regex<'a, char>, Regex<'a, char>) -> Regex<'a, char>,
    {
        let mut tail = self.pop()?;
        for _ in 0..(count - 1) {
            let head = self.pop()?;
            tail = f(self.ctx, head, tail);
        }
        self.stack.push(tail);
        Ok(())
    }

    fn make_repetition(&mut self, kind: &hir::RepetitionKind) -> Result<()> {
        use self::hir::RepetitionKind::*;
        use self::hir::RepetitionRange::*;

        // utility to handle an exact number of repeats
        fn exactly<'a>(
            ctx: &'a RegexContext<'a, char>,
            body: Regex<'a, char>,
            count: u32,
        ) -> Regex<'a, char> {
            iter::repeat(body)
                .take(count as usize)
                .fold(ctx.empty(), |l, r| ctx.concat(l, r))
        }

        // utility to handle a minimum number of repeats
        fn at_least<'a>(
            ctx: &'a RegexContext<'a, char>,
            body: Regex<'a, char>,
            count: u32,
        ) -> Regex<'a, char> {
            ctx.concat(exactly(ctx, body, count), ctx.repetition(body))
        }

        // Translate the different kinds of repetition into this library's
        // types of regular expressions. This does involve repeated concatinations
        // to deal with "AtLeast", "Exactly", or "Bounded" types of repetition.
        let body = self.pop()?;
        self.push(|c| match kind {
            ZeroOrOne => c.alternation(c.empty(), body),
            ZeroOrMore => c.repetition(body),
            OneOrMore => c.concat(body, c.repetition(body)),
            Range(AtLeast(x)) => at_least(c, body, *x),
            Range(Exactly(x)) => exactly(c, body, *x),
            Range(Bounded(x, y)) => c.and(
                at_least(c, body, *x),
                c.complement(at_least(c, body, *y + 1)),
            ),
        });

        Ok(())
    }
}

impl<'a, 'b> Visitor for RegexVisitor<'a, 'b> {
    type Output = Regex<'a, char>;
    type Err = Error;

    fn finish(mut self) -> Result<Regex<'a, char>> {
        self.pop()
    }

    fn visit_post(&mut self, hir: &Hir) -> Result<()> {
        use self::hir::Class;
        use self::hir::HirKind::*;
        use self::hir::Literal;
        use self::hir::Repetition;

        match hir.kind() {
            Empty => self.push(|c| c.empty()),
            Literal(Literal::Byte(_)) => return Err(Error::invalid_unicode(self.regex)),
            Literal(Literal::Unicode(ch)) => self.push(|c| c.class(literal_ranges(*ch))),
            Class(Class::Bytes(_)) => return Err(Error::invalid_unicode(self.regex)),
            Class(Class::Unicode(class)) => self.push(|c| c.class(class_ranges(class))),
            Anchor(_) => return Err(Error::anchor_unsupported(self.regex)),
            WordBoundary(_) => return Err(Error::word_boundry_unsupported(self.regex)),
            Repetition(Repetition { greedy: false, .. }) => {
                return Err(Error::non_greedy_unsupported(self.regex))
            }
            Repetition(Repetition { kind, .. }) => self.make_repetition(kind)?,
            Group(_) => {} // treats all GroupKind's the same
            Concat(elt) => self.fold_right(|c, l, r| c.concat(l, r), elt.len())?,
            Alternation(elt) => self.fold_right(|c, l, r| c.alternation(l, r), elt.len())?,
        }

        Ok(())
    }
}

fn literal_ranges(ch: char) -> impl Iterator<Item = Range<char>> {
    iter::once(Range::new(ch, ch))
}

fn class_ranges<'a>(class: &'a ClassUnicode) -> impl Iterator<Item = Range<char>> + 'a {
    class
        .iter()
        .map(|range| Range::new(range.start(), range.end()))
}

#[cfg(test)]
mod test {
    use super::*;
    use regex::RegexKind;

    #[test]
    fn parse_regex_gives_class_regex_for_single_char_regex() {
        let ctx = RegexContext::new();

        let result = parse_regex("a", &ctx);

        assert_matches!(
            result, Ok(regex) => {
                assert_matches!(regex.kind(), RegexKind::Class(class) => {
                    assert_eq!(class.ranges().count(), 1);
                    assert!(class.contains(&'a'));
        })});
    }

    #[test]
    fn parse_regex_gives_empty_regex_for_empty_string_regex() {
        let ctx = RegexContext::new();

        let result = parse_regex("", &ctx);

        assert_matches!( result, Ok(regex) => {
            assert_matches!(regex.kind(), RegexKind::Empty);
        });
    }

    #[test]
    fn parse_regex_gives_class_for_range_regex() {
        let ctx = RegexContext::new();

        let result = parse_regex("[a-c]", &ctx);

        assert_matches!(
            result, Ok(regex) => {
                assert_matches!(regex.kind(), RegexKind::Class(class) => {
                    assert_eq!(class.ranges().count(), 1);
                    assert!(class.contains(&'a'));
                    assert!(class.contains(&'b'));
                    assert!(class.contains(&'c'));
        })});
    }

    #[test]
    fn parse_regex_gives_error_for_anchored_regex() {
        let ctx = RegexContext::new();

        let result = parse_regex("^a", &ctx);

        assert_matches!(result, Err(_));
    }

    #[test]
    fn parse_regex_gives_error_for_word_boundry() {
        let ctx = RegexContext::new();

        let result = parse_regex("\\ba", &ctx);

        assert_matches!(result, Err(_));
    }

    #[test]
    fn parse_regex_gives_error_for_non_greedy_repetition() {
        let ctx = RegexContext::new();

        let result = parse_regex("a*?", &ctx);

        assert_matches!(result, Err(_));
    }

    #[test]
    fn parse_regex_give_repetition_for_kleen_star() {
        let ctx = RegexContext::new();

        let result = parse_regex("a*", &ctx);

        assert_matches!(
            result, Ok(regex) => {
                assert_matches!(regex.kind(), RegexKind::Repetition(rep) => {
                    assert_matches!(rep.inner().kind(), RegexKind::Class(_))
                })
            });
    }

    #[test]
    fn parse_regex_is_transparent_to_groups() {
        let ctx = RegexContext::new();

        let result1 = parse_regex("a*", &ctx).unwrap();
        let result2 = parse_regex("(a*)", &ctx).unwrap();

        assert_eq!(result1, result2);
    }

    #[test]
    fn parse_regex_concat_gives_expected_concat_regex() {
        let ctx = RegexContext::new();

        let result = parse_regex("ab", &ctx);

        assert_matches!(
            result, Ok(regex) => {
                assert_matches!(regex.kind(), RegexKind::Concat(concat) => {
                    assert_matches!(concat.first().kind(), RegexKind::Class(class)=> {
                        assert_eq!(class.ranges().count(), 1);
                        assert!(class.contains(&'a'));
                    });
                    assert_matches!(concat.second().kind(), RegexKind::Class(class)=> {
                        assert_eq!(class.ranges().count(), 1);
                        assert!(class.contains(&'b'));
                    });
                })
            });
    }

    #[test]
    fn parse_regex_alternation_give_exected_alternation_regex() {
        let ctx = RegexContext::new();

        let result = parse_regex("c*|a*|b*", &ctx);

        assert_matches!(
            result, Ok(regex) => {
                assert_matches!(regex.kind(), RegexKind::Alternation(alt) => {
                    assert_matches!(alt.first().kind(), RegexKind::Repetition(_) );
                    assert_matches!(alt.second().kind(), RegexKind::Alternation(alt) => {
                        assert_matches!(alt.first().kind(), RegexKind::Repetition(_));
                        assert_matches!(alt.second().kind(), RegexKind::Repetition(_) )
                    })
                })
            });
    }

    #[test]
    fn dfa_context_from_regex_for_owens_regex_has_expected_number_of_states() {
        // this tests the dfa from Figure 2 of Owens et al.
        let sut = DfaContext::new();
        let dfa = sut.from_regex("ab|ac")
            .expect("Unexpected error parsing regex");

        assert_eq!(dfa.states().count(), 4);
    }

    #[test]
    fn dfa_context_from_regex_vec_has_expected_number_of_states() {
        let sut = DfaContext::new();
        let dfa = sut.from_regex_vec(vec!["ab", "ac"])
            .expect("Unexpected error parsing regexs");

        assert_eq!(dfa.states().count(), 5);
    }
}
