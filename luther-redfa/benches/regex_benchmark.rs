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

use std::alloc::System;
use std::iter;

use criterion::Criterion;
use luther_redfa::regex::RegexContext;


#[global_allocator]
static A: System = System;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("empty_regex", |b| {
        b.iter( || {
            let ctx = RegexContext::<char>::new();
            ctx.empty();
        })
    });

    c.bench_function("null_regex", |b| {
        b.iter( || {
            let ctx = RegexContext::<char>::new();
            ctx.class(iter::empty());
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
