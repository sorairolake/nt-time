// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting the file time to MS-DOS date and time.

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
    /// UTC offset of MS-DOS date and time.
    ///
    /// <OFFSET> takes the UTC offset in 15 minute intervals.
    #[arg(short, long, allow_hyphen_values(true))]
    offset: Option<i8>,

    /// File time to convert.
    time: nt_time::FileTime,
}

#[cfg(feature = "std")]
fn main() -> anyhow::Result<()> {
    use anyhow::Context;
    use clap::Parser;
    use nt_time::time::UtcOffset;

    let opt = Opt::parse();

    let offset = opt
        .offset
        .map(|o| UtcOffset::from_whole_seconds(i32::from(o) * 900))
        .transpose()
        .context("could not create the UTC offset")?;
    let dt = opt
        .time
        .to_dos_date_time(offset)
        .context("could not convert time")?;
    println!("{dt:?}");
    Ok(())
}

#[cfg(not(feature = "std"))]
fn main() -> anyhow::Result<()> {
    anyhow::bail!("`std` feature is required");
}
