// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::cmp::Ordering;

use enum_info::{EnumInfo, VariantInfo};
use super::Dfa;
use redfa::{self, Regex};
use redfa::dfa::Normalize;

/// build_dfa builds a Dfa from the information contained in the EnumInfo passed in.
///
/// The return type is the Dfa and the index of the error state in that Dfa. The value
/// attached to each state of the Dfa is an Option<VariantInfo>. It is None for non-accepting
/// states and Some(vi) for accepting states where vi is the VariantInfo that corresponds
/// to the variant matched by this state.
///
/// If more than one variant can be matched in a given accepting states the one in the lowest
/// priority group is selected. If more than one variant in the same priority group can be
/// matched then the tie is broken by preferring simple strings (i.e. without repetition, or
/// alteration, etc.) over more complicated regular expressions. If there is still a tie then
/// this is an error.
///
/// It is also an error if any of the regular expresions corresponding to one of variants matches
/// the empty string since this would prevent the generated lexer from making progress.
pub fn build_dfa<'info, 'ast: 'info>(info: &'info EnumInfo<'ast>) -> (Dfa<'info, 'ast>, usize) {
    // parse the regex for the variants
    let regexs: Result<Vec<Regex<char>>, _> = info.variants
        .iter()
        .map(|vi| vi.regex.parse().or_else(|e| Err((&vi.regex, e))))
        .collect();
    let regexs = regexs
        .unwrap_or_else(|(re, e)| panic!("luther: invalid regex \"{}\":{}", re, e))
        .normalize();

    // check for nullable regex
    match regexs
        .iter()
        .position(|re| re.nullable())
        .map(|i| &info.variants[i].regex)
    {
        Some(re) => panic!("luther: regex \"{}\" matches the empty string", re),
        _ => {}
    }

    // find all the simple strings
    let simple_strings: Vec<_> = regexs.iter().map(|re| is_simple_string(re)).collect();

    // create the error state
    let error = vec![Regex::Null; regexs.len()];

    // create the dfa
    let (dfa, map) = redfa::Dfa::from_derivatives(vec![regexs, error.clone()]);

    // find the error state
    let error_state = map[&error] as usize;

    // map the states to accepting states
    let dfa = dfa.map(|re| {
        map_accepting_state(re.as_ref(), info.variants.as_ref(), simple_strings.as_ref())
    });

    (dfa, error_state)
}

fn map_accepting_state<'re, 'info, 'ast: 'info>(
    regexs: &'re Vec<Regex<char>>,
    vis: &'info Vec<VariantInfo<'ast>>,
    simple: &'re Vec<bool>,
) -> Option<&'info VariantInfo<'ast>> {
    let min = izip!(regexs, vis, simple).fold(RegexAccumulator::new(), RegexAccumulator::combine);

    if min.count > 1 {
        let (_, vi, _) = min.regex_vi.unwrap();
        panic!(
            "luther: accepting state matches more than one regex including \"{}\"",
            vi.regex
        );
    }

    min.regex_vi.map(|(_, vi, _)| vi)
}

type RegexVariant<'re, 'info, 'ast: 'info> =
    (&'re Regex<char>, &'info VariantInfo<'ast>, &'re bool);

struct RegexAccumulator<'re, 'info, 'ast: 'info> {
    regex_vi: Option<RegexVariant<'re, 'info, 'ast>>,
    count: u32,
}

impl<'re, 'info, 'ast: 'info> RegexAccumulator<'re, 'info, 'ast> {
    fn new() -> Self {
        RegexAccumulator {
            regex_vi: None,
            count: 0,
        }
    }

    fn combine(self, new: RegexVariant<'re, 'info, 'ast>) -> Self {
        let (regex, _, _) = new;
        if regex.nullable() {
            let (regex_vi, count) = self.regex_vi.map_or((new, 1), |old| {
                match compare_by_priority_group(new, old) {
                    Ordering::Less => (new, 1),
                    Ordering::Equal => (old, self.count + 1),
                    Ordering::Greater => (old, self.count),
                }
            }); // COV_EXCL_LINE
            RegexAccumulator {
                regex_vi: Some(regex_vi),
                count,
            }
        } else {
            self
        }
    }
}

fn compare_by_priority_group(
    (_, l_vi, l_simple): RegexVariant,
    (_, r_vi, r_simple): RegexVariant,
) -> Ordering {
    match l_vi.priority_group.cmp(&r_vi.priority_group) {
        Ordering::Equal => compare_for_simple_string(l_simple, r_simple),
        ord => ord,
    }
}

fn compare_for_simple_string(lhs: &bool, rhs: &bool) -> Ordering {
    match (lhs, rhs) {
        (&true, &false) => Ordering::Less,
        (&false, &true) => Ordering::Greater,
        _ => Ordering::Equal,
    }
}

fn is_simple_string(regex: &Regex<char>) -> bool {
    match regex {
        &Regex::Cat(ref regexs) => regexs.iter().all(|re| match re {
            &Regex::Alt(ref ts, ref res) => ts.len() == 1 && res.len() == 0,
            _ => false,
        }),
        _ => false,
    }
}
