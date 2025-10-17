// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of printing a human-readable date and time as the file time.

use std::{ops::Deref, str::FromStr};

use anyhow::Context;
use clap::{Parser, ValueEnum};
use nt_time::{
    FileTime,
    time::{
        OffsetDateTime,
        error::Parse,
        format_description::well_known::{Iso8601, Rfc2822, Rfc3339},
    },
};

#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// The format of the output.
    #[arg(short, long, value_enum, default_value_t, ignore_case(true))]
    format: Format,

    /// Date and time to print.
    ///
    /// <DATE> is a string representing a date and time in either ISO 8601, RFC
    /// 2822, or RFC 3339 format.
    #[arg(value_name("DATE"))]
    dt: DateTime,
}

#[derive(Clone, Debug, Default, ValueEnum)]
enum Format {
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

#[derive(Clone, Debug)]
struct DateTime(OffsetDateTime);

impl Deref for DateTime {
    type Target = OffsetDateTime;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FromStr for DateTime {
    type Err = Parse;

    fn from_str(dt: &str) -> Result<Self, Self::Err> {
        OffsetDateTime::parse(dt, &Iso8601::DEFAULT)
            .or_else(|_| OffsetDateTime::parse(dt, &Rfc2822))
            .or_else(|_| OffsetDateTime::parse(dt, &Rfc3339))
            .map(Self)
    }
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let ft = FileTime::try_from(*opt.dt).context("could not convert time")?;
    match opt.format {
        Format::Raw => println!("{}", ft.to_raw()),
        Format::BeBytes => println!("{:#04x?}", ft.to_be_bytes()),
        Format::LeBytes => println!("{:#04x?}", ft.to_le_bytes()),
        Format::HighLow => println!("{:#010x?}", ft.to_high_low()),
    }
    Ok(())
}
