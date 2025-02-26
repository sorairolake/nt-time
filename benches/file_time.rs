// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use nt_time::FileTime;
use test::Bencher;

#[cfg(feature = "std")]
#[bench]
fn now(b: &mut Bencher) {
    b.iter(FileTime::now);
}

#[bench]
fn new(b: &mut Bencher) {
    b.iter(|| FileTime::new(u64::MIN));
}

#[bench]
fn to_raw(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.to_raw());
}

#[bench]
fn to_be_bytes(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.to_be_bytes());
}

#[bench]
fn to_le_bytes(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.to_le_bytes());
}

#[bench]
fn to_ne_bytes(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.to_ne_bytes());
}

#[bench]
fn from_be_bytes(b: &mut Bencher) {
    b.iter(|| FileTime::from_be_bytes([u8::MIN; 8]));
}

#[bench]
fn from_le_bytes(b: &mut Bencher) {
    b.iter(|| FileTime::from_le_bytes([u8::MIN; 8]));
}

#[bench]
fn from_ne_bytes(b: &mut Bencher) {
    b.iter(|| FileTime::from_ne_bytes([u8::MIN; 8]));
}

#[bench]
fn to_high_low(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.to_high_low());
}

#[bench]
fn from_high_low(b: &mut Bencher) {
    b.iter(|| FileTime::from_high_low(u32::MIN, u32::MIN));
}

#[bench]
fn default(b: &mut Bencher) {
    b.iter(FileTime::default);
}
