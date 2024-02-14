// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting Unix time to the file time.

// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

use anyhow::Context;
use clap::{ArgGroup, Parser};
use nt_time::FileTime;

#[derive(Debug, Parser)]
#[command(version, about, group(ArgGroup::new("time").required(true)))]
struct Opt {
    /// Unix time in seconds to convert.
    #[arg(
        short,
        long,
        value_name("TIME"),
        allow_hyphen_values(true),
        group("time")
    )]
    secs: Option<i64>,

    /// Unix time in nanoseconds to convert.
    #[arg(
        short,
        long,
        value_name("TIME"),
        allow_hyphen_values(true),
        group("time")
    )]
    nanos: Option<i128>,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ft = match (opt.secs, opt.nanos) {
        (Some(time), None) => FileTime::from_unix_time(time),
        (None, Some(time)) => FileTime::from_unix_time_nanos(time),
        _ => unreachable!(),
    }
    .context("could not convert time")?;
    println!("{ft}");
    Ok(())
}
