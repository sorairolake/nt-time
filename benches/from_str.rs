// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use core::str::FromStr;

use nt_time::FileTime;
use test::Bencher;

#[bench]
fn from_str(b: &mut Bencher) {
    b.iter(|| FileTime::from_str("116444736000000000").unwrap());
}
