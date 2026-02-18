// SPDX-FileCopyrightText: 2026 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and [`Duration`].

use core::time::Duration;

use super::FileTime;
use crate::error::{FileTimeRangeError, FileTimeRangeErrorKind};

impl FileTime {
    /// Returns this `FileTime` as a [`Duration`] since
    /// [`FileTime::NT_TIME_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_duration(), Duration::ZERO);
    /// assert_eq!(
    ///     FileTime::UNIX_EPOCH.to_duration(),
    ///     Duration::from_hours(3_234_576)
    /// );
    /// assert_eq!(
    ///     FileTime::SIGNED_MAX.to_duration(),
    ///     Duration::new(922_337_203_685, 477_580_700)
    /// );
    /// assert_eq!(
    ///     FileTime::MAX.to_duration(),
    ///     Duration::new(1_844_674_407_370, 955_161_500)
    /// );
    /// ```
    #[must_use]
    pub fn to_duration(self) -> Duration {
        Duration::from_nanos_u128(u128::from(self.to_raw()) * 100)
    }

    /// Creates a `FileTime` from a [`Duration`] since
    /// [`FileTime::NT_TIME_EPOCH`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `duration` is greater than [`FileTime::MAX`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_duration(Duration::ZERO),
    ///     Ok(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::from_duration(Duration::from_hours(3_234_576)),
    ///     Ok(FileTime::UNIX_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::from_duration(Duration::new(922_337_203_685, 477_580_700)),
    ///     Ok(FileTime::SIGNED_MAX)
    /// );
    /// assert_eq!(
    ///     FileTime::from_duration(Duration::new(1_844_674_407_370, 955_161_500)),
    ///     Ok(FileTime::MAX)
    /// );
    ///
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_duration(Duration::new(1_844_674_407_370, 955_161_600)).is_err());
    /// ```
    pub fn from_duration(duration: Duration) -> Result<Self, FileTimeRangeError> {
        let ft = u64::try_from(duration.as_nanos() / 100)
            .map_err(|_| FileTimeRangeErrorKind::Overflow)?;
        let ft = Self::new(ft);
        Ok(ft)
    }
}

#[cfg(test)]
mod tests {
    use super::{super::FILE_TIMES_PER_SEC, *};

    #[test]
    fn to_duration() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_duration(), Duration::ZERO);
        assert_eq!(FileTime::new(1).to_duration(), Duration::from_nanos(100));
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC - 1).to_duration(),
            Duration::from_nanos(999_999_900)
        );
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC).to_duration(),
            Duration::from_secs(1)
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(100)).to_duration(),
            Duration::new(11_644_473_599, 999_999_900)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.to_duration(),
            Duration::from_hours(3_234_576)
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(100)).to_duration(),
            Duration::new(11_644_473_600, 100)
        );
        assert_eq!(
            FileTime::SIGNED_MAX.to_duration(),
            Duration::new(922_337_203_685, 477_580_700)
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(100)).to_duration(),
            Duration::new(1_844_674_407_370, 955_161_400)
        );
        assert_eq!(
            FileTime::MAX.to_duration(),
            Duration::new(1_844_674_407_370, 955_161_500)
        );
    }

    #[test]
    fn from_duration() {
        assert_eq!(
            FileTime::from_duration(Duration::ZERO).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_nanos(1)).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_nanos(99)).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_nanos(100)).unwrap(),
            FileTime::new(1)
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_nanos(999_999_900)).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_nanos(999_999_901)).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_nanos(999_999_999)).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_secs(1)).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC)
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(11_644_473_599, 999_999_900)).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(11_644_473_599, 999_999_901)).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(11_644_473_599, 999_999_999)).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_duration(Duration::from_hours(3_234_576)).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(11_644_473_600, 1)).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(11_644_473_600, 99)).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(11_644_473_600, 100)).unwrap(),
            FileTime::UNIX_EPOCH + Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(922_337_203_685, 477_580_700)).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_duration(Duration::new(1_844_674_407_370, 955_161_500)).unwrap(),
            FileTime::MAX
        );
    }

    #[test]
    fn from_duration_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_duration(Duration::new(1_844_674_407_370, 955_161_600)).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
        assert_eq!(
            FileTime::from_duration(Duration::MAX).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }
}
