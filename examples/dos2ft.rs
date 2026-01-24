// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting MS-DOS date and time to the file time.

use anyhow::Context;
use clap::Parser;
use nt_time::{
    FileTime,
    dos_date_time::{Date, DateTime, Time},
};

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

    let (date, time) = (
        Date::new(opt.date).context("could not convert MS-DOS date")?,
        Time::new(opt.time).context("could not convert MS-DOS time")?,
    );
    let dt = DateTime::new(date, time);
    let ft = FileTime::from(dt);
    println!("{ft}");
    Ok(())
}
