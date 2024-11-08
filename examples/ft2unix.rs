// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of converting the file time to Unix time.

use clap::Parser;
use nt_time::FileTime;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// File time to convert.
    time: FileTime,
}

fn main() {
    let opt = Opt::parse();

    let ut = opt.time.to_unix_time();
    println!("{ut:?}");
}
