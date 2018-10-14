// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

extern crate luther_redfa;

#[macro_use]
extern crate criterion;

use criterion::Criterion;
use luther_redfa::Context;

static DECIMAL_CONST_REGEX: &str =
    r"([1-9][0-9]*|0[0-7]*|0[xX][0-9a-fA-F]+)(([uU]([lL]|ll|LL)?)|(([lL]|ll|LL)[uU]?))?";

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("two_keywords", |b| {
        b.iter(|| {
            let ctx = Context::new();
            ctx.from_regex_vec(vec!["auto", "for"])
                .expect("parse error");
        })
    });

    c.bench_function("decimal_const", |b| {
        b.iter(|| {
            let ctx = Context::new();
            ctx.from_regex(DECIMAL_CONST_REGEX).expect("parse error");
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
