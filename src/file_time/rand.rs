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
                FileTime::new(0xE160_E532_6180_0AAB),
                FileTime::new(0x2A29_11D5_87FC_4ED5),
                FileTime::new(0xDFE7_5554_BBD3_4D0D),
                FileTime::new(0x2A4C_F66B_2879_6F51),
                FileTime::new(0x500E_B6DE_08BD_473B),
                FileTime::new(0x8660_66C5_0DAB_6374),
                FileTime::new(0xE8E3_3086_F142_3EFF),
                FileTime::new(0x7D67_17B2_E579_844F)
            ]
        );
    }
}
