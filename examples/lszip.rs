// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An example of listing information about files in a ZIP archive.
//!
//! The UTC offset of the stored timestamp is considered UTC.

// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

#[cfg(feature = "std")]
use anyhow::Context;
#[cfg(feature = "std")]
use clap::Parser;

#[cfg(feature = "std")]
#[derive(Debug, Parser)]
#[command(version, about)]
struct Opt {
    /// ZIP archive to list information about files.
    archive: std::path::PathBuf,
}

#[cfg(feature = "std")]
fn main() -> anyhow::Result<()> {
    use std::{fs::File, io::BufReader};

    use comfy_table::Table;
    use dialoguer::{theme::ColorfulTheme, Password};
    use nt_time::{time::OffsetDateTime, FileTime};
    use zip::{result::ZipError, ZipArchive};

    let opt = Opt::parse();

    let file = File::open(&opt.archive)
        .with_context(|| format!("could not open {}", opt.archive.display()))?;
    let reader = BufReader::new(file);
    let mut archive = ZipArchive::new(reader).context("could not read a ZIP archive")?;

    let passphrase = if matches!(
        archive.by_index(0),
        Err(ZipError::UnsupportedArchive(ZipError::PASSWORD_REQUIRED))
    ) {
        Password::with_theme(&ColorfulTheme::default())
            .with_prompt("Enter passphrase")
            .interact()
            .context("could not read passphrase")?
    } else {
        String::default()
    };

    let mut table = Table::new();
    table
        .load_preset(comfy_table::presets::ASCII_HORIZONTAL_ONLY)
        .set_header([
            "File time",
            "Date",
            "Time",
            "Attr",
            "Size",
            "Compressed",
            "Name",
        ]);
    for i in 0..archive.len() {
        let file = archive
            .by_index_decrypt(i, passphrase.as_bytes())
            .context("could not get a contained file")?
            .context("passphrase is incorrect")?;
        let Some(path) = file.enclosed_name() else {
            eprintln!("{} may be an unsafe path", file.name());
            continue;
        };
        let attribute = if file.is_dir() {
            String::from("D----")
        } else {
            String::from("-----")
        };
        let mtime = file.last_modified();
        let ft = FileTime::from_dos_date_time(mtime.datepart(), mtime.timepart(), None, None)
            .context("could not convert the stored timestamp to the file time")?;
        let dt = OffsetDateTime::try_from(ft)
            .context("could not convert the file time to a `OffsetDateTime`")?;

        table.add_row([
            ft.to_string(),
            dt.date().to_string(),
            dt.time().to_string(),
            attribute,
            file.size().to_string(),
            file.compressed_size().to_string(),
            path.display().to_string(),
        ]);
    }
    println!("{table}");
    Ok(())
}

#[cfg(not(feature = "std"))]
fn main() -> anyhow::Result<()> {
    anyhow::bail!("`std` feature is required");
}
