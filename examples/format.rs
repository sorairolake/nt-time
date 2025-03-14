// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of printing the file time in a human-readable format.

use anyhow::Context;
use clap::Parser;
use nt_time::{FileTime, time::OffsetDateTime};

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
