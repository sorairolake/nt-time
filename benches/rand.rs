// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![cfg(feature = "rand")]
#![feature(test)]

extern crate test;

use nt_time::FileTime;
use rand::Rng;
use rand_pcg::{Pcg64Mcg, rand_core::SeedableRng};
use test::Bencher;

#[bench]
fn sample(b: &mut Bencher) {
    let mut rng = Pcg64Mcg::from_seed(Default::default());
    b.iter(|| rng.random::<FileTime>());
}
