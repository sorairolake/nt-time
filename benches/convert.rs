// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

#[cfg(feature = "std")]
use std::time::SystemTime;

#[cfg(feature = "chrono")]
use chrono::Utc;
#[cfg(feature = "jiff")]
use jiff::Timestamp;
use nt_time::{FileTime, time::UtcDateTime};
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
    b.iter(|| SystemTime::from(FileTime::UNIX_EPOCH));
}

#[bench]
fn try_from_file_time_to_utc_date_time(b: &mut Bencher) {
    b.iter(|| UtcDateTime::try_from(FileTime::UNIX_EPOCH).unwrap());
}

#[cfg(feature = "chrono")]
#[bench]
fn from_file_time_to_chrono_date_time(b: &mut Bencher) {
    b.iter(|| chrono::DateTime::<Utc>::from(FileTime::UNIX_EPOCH));
}

#[cfg(feature = "jiff")]
#[bench]
fn try_from_file_time_to_jiff_timestamp(b: &mut Bencher) {
    b.iter(|| Timestamp::try_from(FileTime::UNIX_EPOCH).unwrap());
}

#[cfg(feature = "dos-date-time")]
#[bench]
fn try_from_file_time_to_dos_date_time(b: &mut Bencher) {
    b.iter(|| dos_date_time::DateTime::try_from(FileTime::new(119_600_064_000_000_000)).unwrap());
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
    b.iter(|| FileTime::try_from(SystemTime::UNIX_EPOCH).unwrap());
}

#[bench]
fn try_from_utc_date_time_to_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::try_from(UtcDateTime::UNIX_EPOCH).unwrap());
}

#[cfg(feature = "chrono")]
#[bench]
fn try_from_chrono_date_time_to_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::try_from(chrono::DateTime::<Utc>::UNIX_EPOCH).unwrap());
}

#[cfg(feature = "jiff")]
#[bench]
fn try_from_jiff_timestamp_to_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::try_from(Timestamp::UNIX_EPOCH).unwrap());
}

#[cfg(feature = "dos-date-time")]
#[bench]
fn from_dos_date_time_to_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::from(dos_date_time::DateTime::MIN));
}
