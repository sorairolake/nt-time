// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use nt_time::FileTime;
use test::Bencher;

#[bench]
fn equality(b: &mut Bencher) {
    b.iter(|| FileTime::NT_TIME_EPOCH == FileTime::NT_TIME_EPOCH);
}

#[bench]
fn order(b: &mut Bencher) {
    b.iter(|| FileTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
}
