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

use criterion::{Criterion, ParameterizedBenchmark};
use luther_redfa::Context;

use std::alloc::System;

#[global_allocator]
static A: System = System;

static DECIMAL_CONST_REGEX: &str =
    r"([1-9][0-9]*|0[0-7]*|0[xX][0-9a-fA-F]+)(([uU]([lL]|ll|LL)?)|(([lL]|ll|LL)[uU]?))?";

fn simple_benchmarks(c: &mut Criterion) {
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

fn scaling_keyword_benchmark(c: &mut Criterion) {
    c.bench(
        "multiple_keywords", 
        ParameterizedBenchmark::new(
            "keywords",
            |b, count| b.iter_with_setup(
                || get_keywords().into_iter().take(*count),
                |keywords| {
                    let c = Context::new();
                    c.from_regex_vec(keywords)
                        .expect("parse error");
                },
            ),
            vec![1usize, 2, 4, 8, 16, 32],
        )
    );
}

criterion_group!(benches, simple_benchmarks, scaling_keyword_benchmark);
criterion_main!(benches);

fn get_keywords() -> Vec<&'static str> {
    vec![
        "auto",
        "break",
        "case",
        "char",
        "const",
        "continue",
        "default",
        "do",
        "double",
        "else",
        "enum",
        "extern",
        "float",
        "for",
        "goto",
        "if",
        "inline",
        "int",
        "long",
        "register",
        "restrict",
        "return",
        "short",
        "signed",
        "sizeof",
        "static",
        "struct",
        "switch",
        "typeof",
        "union",
        "unsigned",
        "void",
        "volitile",
        "while",
        "_Alignas",
        "_Alignof",
        "_Atomic",
        "_Bool",
        "_Complex",
        "_Generic",
        "_Imaginary",
        "_Noreturn",
        "_Static_assert",
        "_Thread_local",
        "__func__",
    ]
}
