// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting the file time to Unix time.

// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

use clap::Parser;
use nt_time::FileTime;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// File time to convert.
    time: FileTime,
}

fn main() {
    let opt = Opt::parse();

    let ut = opt.time.to_unix_time();
    println!("{ut:?}");
}
