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

use nt_time::{time::macros::datetime, FileTime};
use test::Bencher;

#[bench]
fn checked_add(b: &mut Bencher) {
    use core::time::Duration;

    b.iter(|| FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(100)));
}

#[bench]
fn checked_sub(b: &mut Bencher) {
    use core::time::Duration;

    b.iter(|| FileTime::MAX.checked_sub(Duration::from_nanos(100)));
}

#[bench]
fn saturating_add(b: &mut Bencher) {
    use core::time::Duration;

    b.iter(|| FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(100)));
}

#[bench]
fn saturating_sub(b: &mut Bencher) {
    use core::time::Duration;

    b.iter(|| FileTime::MAX.saturating_sub(Duration::from_nanos(100)));
}

#[bench]
fn add_std_duration(b: &mut Bencher) {
    use core::time::Duration;

    b.iter(|| FileTime::NT_TIME_EPOCH + Duration::from_nanos(100));
}

#[bench]
fn add_positive_time_duration(b: &mut Bencher) {
    use time::Duration;

    b.iter(|| FileTime::NT_TIME_EPOCH + Duration::nanoseconds(100));
}

#[bench]
fn add_negative_time_duration(b: &mut Bencher) {
    use time::Duration;

    b.iter(|| FileTime::MAX + Duration::nanoseconds(-100));
}

#[cfg(feature = "chrono")]
#[bench]
fn add_positive_chrono_time_delta(b: &mut Bencher) {
    use chrono::TimeDelta;

    b.iter(|| FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(100));
}

#[cfg(feature = "chrono")]
#[bench]
fn add_negative_chrono_time_delta(b: &mut Bencher) {
    use chrono::TimeDelta;

    b.iter(|| FileTime::MAX + TimeDelta::nanoseconds(-100));
}

#[bench]
fn sub_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::MAX - FileTime::NT_TIME_EPOCH);
}

#[bench]
fn sub_std_duration(b: &mut Bencher) {
    use core::time::Duration;

    b.iter(|| FileTime::MAX - Duration::from_nanos(100));
}

#[bench]
fn sub_positive_time_duration(b: &mut Bencher) {
    use time::Duration;

    b.iter(|| FileTime::MAX - Duration::nanoseconds(100));
}

#[bench]
fn sub_negative_time_duration(b: &mut Bencher) {
    use time::Duration;

    b.iter(|| FileTime::NT_TIME_EPOCH - Duration::nanoseconds(-100));
}

#[cfg(feature = "chrono")]
#[bench]
fn sub_positive_chrono_time_delta(b: &mut Bencher) {
    use chrono::TimeDelta;

    b.iter(|| FileTime::MAX - TimeDelta::nanoseconds(100));
}

#[cfg(feature = "chrono")]
#[bench]
fn sub_negative_chrono_time_delta(b: &mut Bencher) {
    use chrono::TimeDelta;

    b.iter(|| FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(-100));
}

#[cfg(feature = "std")]
#[bench]
fn sub_file_time_from_system_time(b: &mut Bencher) {
    use std::time::{Duration, SystemTime};

    b.iter(|| {
        (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
            - FileTime::new(9_223_372_036_854_775_806)
    });
}

#[cfg(feature = "std")]
#[bench]
fn sub_system_time_from_file_time(b: &mut Bencher) {
    use std::time::{Duration, SystemTime};

    b.iter(|| {
        FileTime::new(9_223_372_036_854_775_807)
            - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_600))
    });
}

#[bench]
fn sub_file_time_from_offset_date_time(b: &mut Bencher) {
    b.iter(|| datetime!(9999-12-31 23:59:59.999_999_900 UTC) - FileTime::NT_TIME_EPOCH);
}

#[bench]
fn sub_offset_date_time_from_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::new(2_650_467_743_999_999_999) - datetime!(1601-01-01 00:00 UTC));
}

#[cfg(feature = "chrono")]
#[bench]
fn sub_file_time_from_chrono_date_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| {
        "+60056-05-28 05:36:10.955161500 UTC"
            .parse::<DateTime<Utc>>()
            .unwrap()
            - FileTime::NT_TIME_EPOCH
    });
}

#[cfg(feature = "chrono")]
#[bench]
fn sub_chrono_date_time_from_file_time(b: &mut Bencher) {
    use chrono::{DateTime, Utc};

    b.iter(|| FileTime::MAX - "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap());
}
