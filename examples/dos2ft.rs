// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting MS-DOS date and time to the file time.

use anyhow::Context;
use clap::Parser;
use nt_time::FileTime;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// MS-DOS date to convert.
    date: u16,

    /// MS-DOS time to convert.
    time: u16,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ft = FileTime::from_dos_date_time(opt.date, opt.time)
        .context("could not convert date and time")?;
    println!("{ft}");
    Ok(())
}
