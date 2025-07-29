// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting the file time to MS-DOS date and time.

use anyhow::Context;
use clap::Parser;
use nt_time::FileTime;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// File time to convert.
    time: FileTime,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let dt = opt
        .time
        .to_dos_date_time()
        .context("could not convert time")?;
    println!("{dt:?}");
    Ok(())
}
