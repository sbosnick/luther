// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::path::Path;
use std::process::{Command, Output};
use args;
use project;
use quicli::prelude::*;
use quicli::fs;

#[derive(Debug)]
pub struct Runner<'proj> {
    out_dir_base: &'proj Path,
    rustc_args: args::Args,
    kcov_args: Option<args::Args>,
}

impl<'proj> Runner<'proj> {
    pub fn new(kcov_out_dir: Option<&Path>, project: &'proj project::Project) -> Runner<'proj> {
        let dep_dir = project.lib_dir().join("deps");
        let libluther = project.lib_dir().join("libluther.rlib");
        let libluther_derive = project.lib_dir().join("libluther_derive.so");

        let rustc_args = args::Args::new()
            .add_arg("-L")
            .add_equal_arg("dependency", dep_dir)
            .add_arg("--extern")
            .add_equal_arg("luther", libluther)
            .add_arg("--extern")
            .add_equal_arg("luther_derive", libluther_derive);

        let kcov_args = kcov_out_dir.map(|out_dir| {
            args::Args::new()
                .add_equal_arg("--include-path", &project.root_dir())
                .add_equal_arg("--exclude-line", "COV_EXCL_LINE")
                .add_equal_arg("--exclude-region", "COV_EXCL_START:COV_EXCL_END")
                .add_arg(out_dir)
        });

        Runner {
            rustc_args,
            kcov_args,
            out_dir_base: project.out_dir(),
        }
    }

    pub fn run_test<P: AsRef<Path>>(&self, test_file: P, expect_success: bool) -> Result<Outcome> {
        let test_file = test_file.as_ref();
        let test_stem = test_file.file_stem().ok_or_else(|| {
            format_err!(
                "Unable to extract file stem for test file {}",
                test_file.display()
            )
        })?;

        let out_dir = &self.out_dir_base.join(test_stem);
        fs::create_dir(out_dir)?;

        let mut command = self.kcov_args.as_ref().map_or_else(
            || Command::new("rustc"),
            |kcov_args| {
                let mut command = Command::new("kcov");
                command.args(kcov_args).arg("rustc");
                command
            },
        );

        command
            .args(&self.rustc_args)
            .arg("--out-dir")
            .arg(out_dir)
            .arg(test_file);

        debug!("running: {:?}", command);

        let output = command.output()?;

        if output.status.success() == expect_success {
            info!("test {} ok", test_stem.to_string_lossy());
            log_output(&output, Level::Debug);
            Ok(Outcome::Pass)
        } else {
            warn!("test {} failed", test_stem.to_string_lossy());
            log_output(&output, Level::Info);
            Ok(Outcome::Fail)
        }
    }
}

fn log_output(output: &Output, level: Level) {
    output.status.code().map_or_else(
        || debug!("no output status code"),
        |code| debug!("output status code was: {}", code),
    );

    if log_enabled!(level) {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        log!(level, "stdout is: {}", stdout);
        log!(level, "stderr is: {}", stderr);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Pass,
    Fail,
}
