//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! An example of converting the Windows NT system time to Unix time.

// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

#[cfg(feature = "std")]
use anyhow::Context;
#[cfg(feature = "std")]
use clap::Parser;

#[cfg(feature = "std")]
#[derive(Debug, Parser)]
#[clap(version, about)]
struct Opt {
    /// Unit of Unix time to print.
    #[clap(short, long, value_enum, default_value_t, ignore_case(true))]
    unit: Unit,

    /// Windows NT system time to convert.
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
fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ft = nt_time::FileTime::new(opt.time);
    let ut = time::OffsetDateTime::try_from(ft)
        .map(|dt| match opt.unit {
            Unit::Seconds => time::OffsetDateTime::unix_timestamp(dt).into(),
            Unit::Nanoseconds => time::OffsetDateTime::unix_timestamp_nanos(dt),
        })
        .context("could not convert time")?;
    println!("{ut}");
    Ok(())
}

#[cfg(not(feature = "std"))]
fn main() -> anyhow::Result<()> {
    anyhow::bail!("`std` feature is required");
}
