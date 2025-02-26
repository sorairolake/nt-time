// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![cfg(feature = "rand")]
#![feature(test)]

extern crate test;

use nt_time::{
    FileTime,
    rand::{Rng, rngs::mock::StepRng},
};
use test::Bencher;

#[bench]
fn sample(b: &mut Bencher) {
    let mut rng = StepRng::new(0, 1);
    b.iter(|| rng.random::<FileTime>());
}
