// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting Unix time to the file time.

use anyhow::Context;
use clap::Parser;
use nt_time::FileTime;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// The number of whole seconds in Unix time to convert.
    #[arg(allow_hyphen_values(true))]
    secs: i64,

    /// The number of additional nanoseconds in Unix time to convert.
    #[arg(default_value_t)]
    nanos: u32,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ft =
        FileTime::from_unix_time(opt.secs, opt.nanos).context("could not convert Unix time")?;
    println!("{ft}");
    Ok(())
}
