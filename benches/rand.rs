// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![cfg(feature = "rand")]
#![feature(test)]
// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

extern crate test;

use nt_time::{
    rand::{rngs::mock::StepRng, Rng},
    FileTime,
};
use test::Bencher;

#[bench]
fn sample(b: &mut Bencher) {
    let mut rng = StepRng::new(0, 1);
    b.iter(|| rng.gen::<FileTime>());
}
