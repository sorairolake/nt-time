// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of printing the file time.

// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

use anyhow::Context;
use clap::Parser;
use nt_time::{time::OffsetDateTime, FileTime};

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// File time to print.
    time: FileTime,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let dt = OffsetDateTime::try_from(opt.time).context("could not convert time")?;
    println!("{dt}");
    Ok(())
}
