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

#[cfg(feature = "std")]
#[derive(Debug, clap::Parser)]
#[command(version, about)]
struct Opt {
    /// File time to print.
    time: nt_time::FileTime,
}

#[cfg(feature = "std")]
fn main() -> anyhow::Result<()> {
    use anyhow::Context;
    use clap::Parser;
    use nt_time::time::OffsetDateTime;

    let opt = Opt::parse();

    let dt = OffsetDateTime::try_from(opt.time).context("could not convert time")?;
    println!("{dt}");
    Ok(())
}

#[cfg(not(feature = "std"))]
fn main() -> anyhow::Result<()> {
    anyhow::bail!("`std` feature is required");
}
