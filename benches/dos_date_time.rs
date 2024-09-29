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
fn to_dos_date_time(b: &mut Bencher) {
    b.iter(|| {
        FileTime::new(119_600_064_000_000_000)
            .to_dos_date_time(None)
            .unwrap()
    });
}

#[bench]
fn from_dos_date_time(b: &mut Bencher) {
    b.iter(|| FileTime::from_dos_date_time(0x0021, u16::MIN, None, None).unwrap());
}
