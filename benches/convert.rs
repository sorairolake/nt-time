// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]
// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

extern crate test;

use nt_time::{time::OffsetDateTime, FileTime};
use test::Bencher;

#[bench]
fn from_file_time_to_u64(b: &mut Bencher) {
    b.iter(|| u64::from(FileTime::NT_TIME_EPOCH));
}

#[bench]
fn try_from_file_time_to_i64(b: &mut Bencher) {
    b.iter(|| i64::try_from(FileTime::NT_TIME_EPOCH).unwrap());
}

#[cfg(feature = "std")]
#[bench]
fn from_file_time_to_system_time(b: &mut Bencher) {
    use std::time::SystemTime;

    b.iter(|| SystemTime::from(FileTime::UNIX_EPOCH));
}

#[bench]
fn try_from_file_time_to_offset_date_time(b: &mut Bencher) {
    b.iter(|| OffsetDateTime::try_from(FileTime::UNIX_EPOCH).unwrap());
}

#[cfg(feature = "chrono")]
#[bench]
fn from_file_time_to_chrono_date_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| DateTime::<Utc>::from(FileTime::UNIX_EPOCH));
}

#[bench]
fn from_u64_to_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::from(u64::MIN));
}

#[bench]
fn try_from_i64_to_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::try_from(i64::default()).unwrap());
}

#[cfg(feature = "std")]
#[bench]
fn try_from_system_time_to_file_time(b: &mut Bencher) {
    use std::time::SystemTime;

    b.iter(|| FileTime::try_from(SystemTime::UNIX_EPOCH).unwrap());
}

#[bench]
fn try_from_offset_date_time_to_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::try_from(OffsetDateTime::UNIX_EPOCH).unwrap());
}

#[cfg(feature = "chrono")]
#[bench]
fn try_from_chrono_date_time_to_file_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| FileTime::try_from(DateTime::<Utc>::UNIX_EPOCH).unwrap());
}
