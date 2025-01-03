// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of [`rand`] for [`FileTime`].

use rand::{
    distributions::{Distribution, Standard},
    Rng,
};

use super::FileTime;

impl Distribution<FileTime> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> FileTime {
        FileTime::new(rng.gen())
    }
}

#[cfg(test)]
mod tests {
    use rand::rngs::mock::StepRng;

    use super::*;

    #[test]
    fn sample() {
        let mut rng = StepRng::new(0, 1);
        let buf: [FileTime; 4] = rng.gen();
        assert_eq!(
            buf,
            [
                FileTime::new(0),
                FileTime::new(1),
                FileTime::new(2),
                FileTime::new(3)
            ]
        );
    }
}
