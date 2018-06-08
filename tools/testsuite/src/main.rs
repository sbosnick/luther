// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

#[macro_use]
extern crate quicli;

extern crate itertools;

mod args;
mod project;
mod runner;

use std::path::{Path, PathBuf};
use quicli::prelude::*;
use quicli::fs;
use runner::Outcome;
use itertools::Itertools;

/// Run the luther-derive test suite.
#[derive(Debug, StructOpt)]
struct Cli {
    /// Name of the single test to run, run all tests if not present.
    #[structopt(parse(from_os_str))]
    test_name: Option<PathBuf>,

    /// Directory into which to output kcov files, run without kcov if not present.
    #[structopt(short = "k", long = "kcov-out", parse(from_os_str))]
    kcov_out: Option<PathBuf>,

    /// Pass many times for more log output.
    #[structopt(long = "verbose", short = "v", parse(from_occurrences))]
    verbosity: u8,
}

impl Cli {
    fn kcov_out_dir(&self) -> Option<&Path> {
        self.kcov_out.as_ref().map(|path| path.as_ref())
    }
}

main!(|args: Cli, log_level: verbosity| {
    let proj = project::Project::new();
    proj.ensure_dirs()?;
    let runner = runner::Runner::new(args.kcov_out_dir(), &proj);

    if let Some(test_name) = args.test_name.as_ref() {
        let outcome = runner.run_test(
            proj.test_suite_dir().join(test_name),
            test_name.starts_with("succ"),
        )?;

        if outcome == Outcome::Fail {
            bail!("test {} failed", test_name.display());
        }
    } else {
        let succ_pattern = make_pattern(proj.test_suite_dir(), "succ")?;
        let fail_pattern = make_pattern(proj.test_suite_dir(), "fail")?;

        debug!("success pattern: {}", succ_pattern);
        debug!("fail pattern: {}", fail_pattern);

        let results = fs::glob(&succ_pattern)?
            .into_iter()
            .map(|path| runner.run_test(path, true))
            .fold_results(TestResults::new(), TestResults::accumulate)?;

        let results = fs::glob(&fail_pattern)?
            .into_iter()
            .map(|path| runner.run_test(path, false))
            .fold_results(results, TestResults::accumulate)?;

        info!(
            "test suite results: {} passes and {} failures",
            results.passes, results.failures
        );
    }
});

struct TestResults {
    passes: u8,
    failures: u8,
}

impl TestResults {
    fn new() -> TestResults {
        TestResults {
            passes: 0,
            failures: 0,
        }
    }

    fn accumulate(mut self, outcome: runner::Outcome) -> Self {
        use runner::Outcome::*;
        match outcome {
            Pass => self.passes += 1,
            Fail => self.failures += 1,
        }
        self
    }
}

fn make_pattern<P: AsRef<Path>>(test_suite: P, stem_base: &str) -> Result<String> {
    let test_suite = test_suite.as_ref();

    let mut filename = stem_base.to_owned();
    filename.push_str("*.rs");

    test_suite
        .join(filename)
        .to_str()
        .ok_or_else(|| format_err!("Unable to make glob pattern for {}", test_suite.display()))
        .map(|s| s.to_owned())
}
