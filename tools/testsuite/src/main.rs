// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

#[macro_use]
extern crate quicli;

use quicli::prelude::*;

/// Run the luther-derive test suite.
#[derive(Debug, StructOpt)]
struct Cli {
    /// Pass many times for more log output.
    #[structopt(long = "verbose", short = "v", parse(from_occurrences))]
    verbosity: u8,
}

main!(|args: Cli, log_level: verbosity| {
    info!("Hello World!");
    println!("verbosity is: {}", args.verbosity);
    warn!("Not yet implemented.");
    debug!("Aren't you nosey!");
});
