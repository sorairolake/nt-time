// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and [Unix time].
//!
//! [Unix time]: https://en.wikipedia.org/wiki/Unix_time

use crate::error::{FileTimeRangeError, FileTimeRangeErrorKind};

use super::{FileTime, FILE_TIMES_PER_SEC};

impl FileTime {
    #[allow(clippy::missing_panics_doc)]
    /// Returns [Unix time] which represents the same date and time as this
    /// `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_unix_time(), -11_644_473_600);
    /// assert_eq!(FileTime::UNIX_EPOCH.to_unix_time(), i64::default());
    /// assert_eq!(FileTime::MAX.to_unix_time(), 1_833_029_933_770);
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[must_use]
    pub fn to_unix_time(self) -> i64 {
        i64::try_from(self.to_raw() / FILE_TIMES_PER_SEC)
            .expect("Unix time should be in the range of `i64`")
            - 11_644_473_600
    }

    /// Returns [Unix time] in nanoseconds which represents the same date and
    /// time as this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.to_unix_time_nanos(),
    ///     -11_644_473_600_000_000_000
    /// );
    /// assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_nanos(), i128::default());
    /// assert_eq!(
    ///     FileTime::MAX.to_unix_time_nanos(),
    ///     1_833_029_933_770_955_161_500
    /// );
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[must_use]
    pub fn to_unix_time_nanos(self) -> i128 {
        (i128::from(self.to_raw()) * 100) - 11_644_473_600_000_000_000
    }

    /// Creates a `FileTime` with the given [Unix time].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `time` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_unix_time(-11_644_473_600).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time(i64::default()).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time(1_833_029_933_770).unwrap(),
    ///     FileTime::MAX - Duration::from_nanos(955_161_500)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::from_unix_time(-11_644_473_601).is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_unix_time(1_833_029_933_771).is_err());
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    pub fn from_unix_time(timestamp: i64) -> Result<Self, FileTimeRangeError> {
        (timestamp <= 1_833_029_933_770)
            .then_some(timestamp)
            .ok_or_else(|| FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow))
            .and_then(|ts| {
                u64::try_from(ts + 11_644_473_600)
                    .map_err(|_| FileTimeRangeError::new(FileTimeRangeErrorKind::Negative))
            })
            .map(|t| t * FILE_TIMES_PER_SEC)
            .map(Self::new)
    }

    /// Creates a `FileTime` with the given [Unix time] in nanoseconds.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `time` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_unix_time_nanos(-11_644_473_600_000_000_000).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_nanos(i128::default()).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_500).unwrap(),
    ///     FileTime::MAX
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::from_unix_time_nanos(-11_644_473_600_000_000_100).is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_501).is_err());
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    pub fn from_unix_time_nanos(timestamp: i128) -> Result<Self, FileTimeRangeError> {
        (timestamp <= 1_833_029_933_770_955_161_500)
            .then_some(timestamp)
            .ok_or_else(|| FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow))
            .and_then(|ts| {
                ((ts + 11_644_473_600_000_000_000) / 100)
                    .try_into()
                    .map_err(|_| FileTimeRangeError::new(FileTimeRangeErrorKind::Negative))
            })
            .map(Self::new)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_unix_time() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_unix_time(), -11_644_473_600);
        assert_eq!(FileTime::UNIX_EPOCH.to_unix_time(), i64::default());
        assert_eq!(FileTime::MAX.to_unix_time(), 1_833_029_933_770);
    }

    #[test]
    fn to_unix_time_nanos() {
        assert_eq!(
            FileTime::NT_TIME_EPOCH.to_unix_time_nanos(),
            -11_644_473_600_000_000_000
        );
        assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_nanos(), i128::default());
        assert_eq!(
            FileTime::MAX.to_unix_time_nanos(),
            1_833_029_933_770_955_161_500
        );
    }

    #[test]
    fn from_unix_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_601).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            FileTime::from_unix_time(i64::MIN).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
    }

    #[test]
    fn from_unix_time() {
        use core::time::Duration;

        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default()).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(1_833_029_933_770).unwrap(),
            FileTime::MAX - Duration::from_nanos(955_161_500)
        );
    }

    #[test]
    fn from_unix_time_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_unix_time(1_833_029_933_771).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
        assert_eq!(
            FileTime::from_unix_time(i64::MAX).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
    }

    #[test]
    fn from_unix_time_nanos_before_nt_time_epoch() {
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_600_000_000_100).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::MIN).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
    }

    #[test]
    fn from_unix_time_nanos() {
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_600_000_000_000).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default()).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_500).unwrap(),
            FileTime::MAX
        );
    }

    #[test]
    fn from_unix_time_nanos_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_501).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::MAX).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
    }
}
