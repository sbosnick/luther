// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::path::{Path, PathBuf};
use std::fs;
use quicli::prelude::*;
use quicli::fs as quickfs;

#[derive(Debug)]
pub struct Project {
    test_suite: PathBuf,
    out: PathBuf,
    lib: PathBuf,
    root: PathBuf,
}

impl Project {
    pub fn new() -> Project {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        debug!("manifest dir is: {}", path.display());

        path.pop();
        path.pop();
        debug!("root dir is: {}", path.display());

        Project {
            test_suite: path.join("luther-derive/testsuite"),
            out: path.join("target/testsuite"),
            lib: path.join("target/debug"),
            root: path,
        }
    }

    pub fn ensure_dirs(&self) -> Result<()> {
        if !self.test_suite.is_dir() {
            bail!(
                "Unable to locate test suite at: {}",
                self.test_suite.display()
            );
        }

        if !self.lib.is_dir() {
            bail!(
                "Unable to locate libraries directory at: {}",
                self.lib.display()
            );
        }

        if self.out.exists() {
            debug!("deleting existing output directory");
            fs::remove_dir_all(&self.out)?;
        }
        debug!("creating output root at: {}", self.out.display());
        quickfs::create_dir(&self.out)?;

        Ok(())
    }

    pub fn test_suite_dir(&self) -> &Path {
        self.test_suite.as_ref()
    }

    pub fn out_dir(&self) -> &Path {
        self.out.as_ref()
    }

    pub fn lib_dir(&self) -> &Path {
        self.lib.as_ref()
    }

    pub fn root_dir(&self) -> &Path {
        self.root.as_ref()
    }
}
