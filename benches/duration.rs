// SPDX-FileCopyrightText: 2026 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use core::time::Duration;

use nt_time::FileTime;
use test::Bencher;

#[bench]
fn to_duration(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH.to_duration());
}

#[bench]
fn from_duration(b: &mut Bencher) {
    b.iter(|| FileTime::from_duration(Duration::ZERO).unwrap());
}
