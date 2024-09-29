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

use nt_time::FileTime;
use test::Bencher;

#[bench]
fn to_unix_time(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH.to_unix_time());
}

#[bench]
fn to_unix_time_secs(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH.to_unix_time_secs());
}

#[bench]
fn to_unix_time_millis(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH.to_unix_time_millis());
}

#[bench]
fn to_unix_time_micros(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH.to_unix_time_micros());
}

#[bench]
fn to_unix_time_nanos(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH.to_unix_time_nanos());
}

#[bench]
fn from_unix_time(b: &mut Bencher) {
    b.iter(|| FileTime::from_unix_time(i64::default(), u32::MIN).unwrap());
}

#[bench]
fn from_unix_time_secs(b: &mut Bencher) {
    b.iter(|| FileTime::from_unix_time_secs(i64::default()).unwrap());
}

#[bench]
fn from_unix_time_millis(b: &mut Bencher) {
    b.iter(|| FileTime::from_unix_time_millis(i64::default()).unwrap());
}

#[bench]
fn from_unix_time_micros(b: &mut Bencher) {
    b.iter(|| FileTime::from_unix_time_micros(i64::default()).unwrap());
}

#[bench]
fn from_unix_time_nanos(b: &mut Bencher) {
    b.iter(|| FileTime::from_unix_time_nanos(i128::default()).unwrap());
}
