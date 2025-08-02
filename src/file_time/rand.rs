// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of [`rand`] for [`FileTime`].

use rand::{
    Rng,
    distr::{Distribution, StandardUniform},
};

use super::FileTime;

impl Distribution<FileTime> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FileTime {
        FileTime::new(rng.random())
    }
}

#[cfg(test)]
mod tests {
    use rand_pcg::{Pcg64Mcg, rand_core::SeedableRng};

    use super::*;

    #[test]
    fn sample() {
        let mut rng = Pcg64Mcg::from_seed(Default::default());
        let buf: [FileTime; 8] = rng.random();
        assert_eq!(
            buf,
            [
                FileTime::new(0xe160_e532_6180_0aab),
                FileTime::new(0x2a29_11d5_87fc_4ed5),
                FileTime::new(0xdfe7_5554_bbd3_4d0d),
                FileTime::new(0x2a4c_f66b_2879_6f51),
                FileTime::new(0x500e_b6de_08bd_473b),
                FileTime::new(0x8660_66c5_0dab_6374),
                FileTime::new(0xe8e3_3086_f142_3eff),
                FileTime::new(0x7d67_17b2_e579_844f)
            ]
        );
    }
}
