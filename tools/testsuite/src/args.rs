// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::ffi::{OsStr, OsString};
use std::iter::IntoIterator;

#[derive(Debug)]
pub struct Args(Vec<OsString>);

impl Args {
    pub fn new() -> Self {
        Args(Vec::new())
    }

    pub fn add_arg<T: AsRef<OsStr>>(mut self, arg: T) -> Self {
        self.0.push(arg.as_ref().to_os_string());
        self
    }

    pub fn add_equal_arg<L, R>(mut self, arg_l: L, arg_r: R) -> Self
    where
        L: AsRef<OsStr>,
        R: AsRef<OsStr>,
    {
        let mut arg = arg_l.as_ref().to_os_string();
        arg.push("=");
        arg.push(arg_r);

        self.0.push(arg);
        self
    }
}

impl<'a> IntoIterator for &'a Args {
    type Item = <&'a Vec<OsString> as IntoIterator>::Item;
    type IntoIter = <&'a Vec<OsString> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}
