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

#[cfg(feature = "std")]
use clap::Parser;

#[cfg(feature = "std")]
#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// Unit of Unix time to print.
    #[arg(short, long, value_enum, default_value_t, ignore_case(true))]
    unit: Unit,

    /// File time to convert.
    time: u64,
}

#[cfg(feature = "std")]
#[derive(Clone, Debug, Default, clap::ValueEnum)]
enum Unit {
    /// Seconds.
    #[default]
    Seconds,

    /// Nanoseconds.
    Nanoseconds,
}

#[cfg(feature = "std")]
fn main() {
    use nt_time::FileTime;

    let opt = Opt::parse();

    let ft = FileTime::new(opt.time);
    let ut = match opt.unit {
        Unit::Seconds => ft.to_unix_time().into(),
        Unit::Nanoseconds => ft.to_unix_time_nanos(),
    };
    println!("{ut}");
}

#[cfg(not(feature = "std"))]
fn main() -> anyhow::Result<()> {
    anyhow::bail!("`std` feature is required");
}
