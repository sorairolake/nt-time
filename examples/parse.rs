// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of printing a human-readable date and time as the file time.

use anyhow::Context;
use clap::{Parser, ValueEnum};
use nt_time::{
    time::{
        error::Parse,
        format_description::well_known::{Iso8601, Rfc2822, Rfc3339},
        OffsetDateTime,
    },
    FileTime,
};

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// The format of the output.
    #[arg(
        short,
        long,
        value_enum,
        default_value_t,
        value_name("FORMAT"),
        ignore_case(true)
    )]
    format: Format,

    /// Date and time to print.
    ///
    /// <DATE> is a string representing a date and time in either ISO 8601, RFC
    /// 2822, or RFC 3339 format.
    #[arg(value_parser(parse_offset_date_time), value_name("DATE"))]
    dt: OffsetDateTime,
}

#[derive(Clone, Debug, Default, ValueEnum)]
pub enum Format {
    /// Underlying 64-bit unsigned integer value.
    #[default]
    Raw,

    /// Byte array in big-endian (network) byte order which represents the
    /// memory representation of the underlying 64-bit unsigned integer value.
    BeBytes,

    /// Byte array in little-endian byte order which represents the memory
    /// representation of the underlying 64-bit unsigned integer value.
    LeBytes,

    /// High-order and low-order parts of the underlying 64-bit unsigned integer
    /// value.
    HighLow,
}

fn parse_offset_date_time(dt: &str) -> Result<OffsetDateTime, Parse> {
    OffsetDateTime::parse(dt, &Iso8601::DEFAULT)
        .or_else(|_| OffsetDateTime::parse(dt, &Rfc2822))
        .or_else(|_| OffsetDateTime::parse(dt, &Rfc3339))
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ft = FileTime::try_from(opt.dt).context("could not convert time")?;
    match opt.format {
        Format::Raw => println!("{}", ft.to_raw()),
        Format::BeBytes => println!("{:#04x?}", ft.to_be_bytes()),
        Format::LeBytes => println!("{:#04x?}", ft.to_le_bytes()),
        Format::HighLow => println!("{:#010x?}", ft.to_high_low()),
    }
    Ok(())
}
