//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! An example of converting Unix time to the file time.

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
#[clap(version, about, group(clap::ArgGroup::new("time").required(true)))]
struct Opt {
    /// Unix time in seconds to convert.
    #[clap(
        short,
        long,
        value_name("TIME"),
        allow_hyphen_values(true),
        group("time")
    )]
    secs: Option<i64>,

    /// Unix time in nanoseconds to convert.
    #[clap(
        short,
        long,
        value_name("TIME"),
        allow_hyphen_values(true),
        group("time")
    )]
    nanos: Option<i128>,
}

#[cfg(feature = "std")]
fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ut = match (opt.secs, opt.nanos) {
        (Some(time), None) => time::OffsetDateTime::from_unix_timestamp(time),
        (None, Some(time)) => time::OffsetDateTime::from_unix_timestamp_nanos(time),
        _ => unreachable!(),
    }
    .context("could not read time")?;
    let ft = nt_time::FileTime::try_from(ut).context("could not convert time")?;
    println!("{ft}");
    Ok(())
}

#[cfg(not(feature = "std"))]
fn main() -> anyhow::Result<()> {
    anyhow::bail!("`std` feature is required");
}
