// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use nt_time::{
    FileTime,
    time::{OffsetDateTime, macros::datetime},
};
use test::Bencher;

#[bench]
fn equality(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH == FileTime::NT_TIME_EPOCH);
}

#[bench]
fn order(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
}

#[cfg(feature = "std")]
#[bench]
fn equality_system_time_and_file_time(b: &mut Bencher) {
    use std::time::SystemTime;

    b.iter(|| SystemTime::UNIX_EPOCH == FileTime::UNIX_EPOCH);
}

#[cfg(feature = "std")]
#[bench]
fn equality_file_time_and_system_time(b: &mut Bencher) {
    use std::time::SystemTime;

    b.iter(|| FileTime::UNIX_EPOCH == SystemTime::UNIX_EPOCH);
}

#[bench]
fn equality_offset_date_time_and_file_time(b: &mut Bencher) {
    b.iter(|| datetime!(1601-01-01 00:00 UTC) == FileTime::NT_TIME_EPOCH);
}

#[bench]
fn equality_file_time_and_offset_date_time(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH == datetime!(1601-01-01 00:00 UTC));
}

#[cfg(feature = "chrono")]
#[bench]
fn equality_chrono_date_time_and_file_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| {
        "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap() == FileTime::NT_TIME_EPOCH
    });
}

#[cfg(feature = "chrono")]
#[bench]
fn equality_file_time_and_chrono_date_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| {
        FileTime::NT_TIME_EPOCH == "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()
    });
}

#[cfg(feature = "jiff")]
#[bench]
fn equality_jiff_timestamp_and_file_time(b: &mut Bencher) {
    use jiff::Timestamp;

    b.iter(|| Timestamp::from_second(-11_644_473_600).unwrap() == FileTime::NT_TIME_EPOCH);
}

#[cfg(feature = "jiff")]
#[bench]
fn equality_file_time_and_jiff_timestamp(b: &mut Bencher) {
    use jiff::Timestamp;

    b.iter(|| FileTime::NT_TIME_EPOCH == Timestamp::from_second(-11_644_473_600).unwrap());
}

#[cfg(feature = "std")]
#[bench]
fn order_system_time_and_file_time(b: &mut Bencher) {
    use std::time::SystemTime;

    b.iter(|| SystemTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
}

#[cfg(feature = "std")]
#[bench]
fn order_file_time_and_system_time(b: &mut Bencher) {
    use std::time::SystemTime;

    b.iter(|| {
        FileTime::UNIX_EPOCH
            > (SystemTime::UNIX_EPOCH - (FileTime::UNIX_EPOCH - FileTime::NT_TIME_EPOCH))
    });
}

#[bench]
fn order_offset_date_time_and_file_time(b: &mut Bencher) {
    b.iter(|| OffsetDateTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
}

#[bench]
fn order_file_time_and_offset_date_time(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH > datetime!(1601-01-01 00:00 UTC));
}

#[cfg(feature = "chrono")]
#[bench]
fn order_chrono_date_time_and_file_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| DateTime::<Utc>::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
}

#[cfg(feature = "chrono")]
#[bench]
fn order_file_time_and_chrono_date_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| FileTime::UNIX_EPOCH > "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap());
}

#[cfg(feature = "jiff")]
#[bench]
fn order_jiff_timestamp_and_file_time(b: &mut Bencher) {
    use jiff::Timestamp;

    b.iter(|| Timestamp::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
}

#[cfg(feature = "jiff")]
#[bench]
fn order_file_time_and_jiff_timestamp(b: &mut Bencher) {
    use jiff::Timestamp;

    b.iter(|| FileTime::UNIX_EPOCH > Timestamp::from_second(-11_644_473_600).unwrap());
}
