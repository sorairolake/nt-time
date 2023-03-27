//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! An example of printing the Windows NT system time.

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
    /// Windows NT system time to print.
    time: u64,
}

#[cfg(feature = "std")]
fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ft = nt_time::FileTime::new(opt.time);
    let dt = time::OffsetDateTime::try_from(ft).context("could not convert time")?;
    println!("{dt}");
    Ok(())
}

#[cfg(not(feature = "std"))]
fn main() -> anyhow::Result<()> {
    anyhow::bail!("`std` feature is required");
}
