// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use core::time::Duration;
#[cfg(feature = "std")]
use std::time::SystemTime;

#[cfg(feature = "chrono")]
use chrono::{DateTime, TimeDelta, Utc};
#[cfg(feature = "jiff")]
use jiff::{Timestamp, ToSpan};
use nt_time::FileTime;
use test::Bencher;
use time::macros::datetime;

#[bench]
fn checked_add(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(100)));
}

#[bench]
fn checked_sub(b: &mut Bencher) {
    b.iter(|| FileTime::MAX.checked_sub(Duration::from_nanos(100)));
}

#[bench]
fn saturating_add(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(100)));
}

#[bench]
fn saturating_sub(b: &mut Bencher) {
    b.iter(|| FileTime::MAX.saturating_sub(Duration::from_nanos(100)));
}

#[bench]
fn add_std_duration(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH + Duration::from_nanos(100));
}

#[bench]
fn add_positive_time_duration(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH + time::Duration::nanoseconds(100));
}

#[bench]
fn add_negative_time_duration(b: &mut Bencher) {
    b.iter(|| FileTime::MAX + -time::Duration::nanoseconds(100));
}

#[cfg(feature = "chrono")]
#[bench]
fn add_positive_chrono_time_delta(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(100));
}

#[cfg(feature = "chrono")]
#[bench]
fn add_negative_chrono_time_delta(b: &mut Bencher) {
    b.iter(|| FileTime::MAX + -TimeDelta::nanoseconds(100));
}

#[cfg(feature = "jiff")]
#[bench]
fn add_positive_jiff_span(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH + 100.nanoseconds());
}

#[cfg(feature = "jiff")]
#[bench]
fn add_negative_jiff_span(b: &mut Bencher) {
    b.iter(|| FileTime::MAX + -(100.nanoseconds()));
}

#[bench]
fn sub_file_time(b: &mut Bencher) {
    b.iter(|| FileTime::MAX - FileTime::NT_TIME_EPOCH);
}

#[bench]
fn sub_std_duration(b: &mut Bencher) {
    b.iter(|| FileTime::MAX - Duration::from_nanos(100));
}

#[bench]
fn sub_positive_time_duration(b: &mut Bencher) {
    b.iter(|| FileTime::MAX - time::Duration::nanoseconds(100));
}

#[bench]
fn sub_negative_time_duration(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH - -time::Duration::nanoseconds(100));
}

#[cfg(feature = "chrono")]
#[bench]
fn sub_positive_chrono_time_delta(b: &mut Bencher) {
    b.iter(|| FileTime::MAX - TimeDelta::nanoseconds(100));
}

#[cfg(feature = "chrono")]
#[bench]
fn sub_negative_chrono_time_delta(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH - -TimeDelta::nanoseconds(100));
}

#[cfg(feature = "jiff")]
#[bench]
fn sub_positive_jiff_span(b: &mut Bencher) {
    b.iter(|| FileTime::MAX - 100.nanoseconds());
}

#[cfg(feature = "jiff")]
#[bench]
fn sub_negative_jiff_span(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH - -(100.nanoseconds()));
}

#[cfg(feature = "std")]
#[bench]
fn sub_file_time_from_system_time(b: &mut Bencher) {
    b.iter(|| {
        (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
            - FileTime::new(9_223_372_036_854_775_806)
    });
}

#[cfg(feature = "std")]
#[bench]
fn sub_system_time_from_file_time(b: &mut Bencher) {
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
    b.iter(|| FileTime::new(2_650_467_743_999_999_999) - datetime!(1601-01-01 00:00:00 UTC));
}

#[cfg(feature = "chrono")]
#[bench]
fn sub_file_time_from_chrono_date_time(b: &mut Bencher) {
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
    b.iter(|| FileTime::MAX - "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap());
}

#[cfg(feature = "jiff")]
#[bench]
fn sub_file_time_from_jiff_timestamp(b: &mut Bencher) {
    b.iter(|| (Timestamp::MAX - 99.nanoseconds()) - FileTime::NT_TIME_EPOCH);
}

#[cfg(feature = "jiff")]
#[bench]
fn sub_jiff_timestamp_from_file_time(b: &mut Bencher) {
    b.iter(|| {
        FileTime::new(2_650_466_808_009_999_999) - Timestamp::from_second(-11_644_473_600).unwrap()
    });
}
