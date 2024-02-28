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

use clap::{Parser, ValueEnum};
use nt_time::FileTime;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// Unit of Unix time to print.
    #[arg(short, long, value_enum, default_value_t, ignore_case(true))]
    unit: Unit,

    /// File time to convert.
    time: FileTime,
}

#[derive(Clone, Debug, Default, ValueEnum)]
enum Unit {
    /// Seconds.
    #[default]
    Seconds,

    /// Nanoseconds.
    Nanoseconds,
}

fn main() {
    let opt = Opt::parse();

    let ut = match opt.unit {
        Unit::Seconds => opt.time.to_unix_time().into(),
        Unit::Nanoseconds => opt.time.to_unix_time_nanos(),
    };
    println!("{ut}");
}
