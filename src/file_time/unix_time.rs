// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and [Unix time].
//!
//! [Unix time]: https://en.wikipedia.org/wiki/Unix_time

use crate::error::{FileTimeRangeError, FileTimeRangeErrorKind};

use super::FileTime;

const NANOS_PER_SEC: u32 = 1_000_000_000;

impl FileTime {
    #[allow(clippy::missing_panics_doc)]
    /// Returns [Unix time] which represents the same date and time as this
    /// `FileTime`.
    ///
    /// The first return value represents the number of whole seconds, and the
    /// second return value represents the number of additional nanoseconds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_unix_time(), (-11_644_473_600, 0));
    /// assert_eq!(FileTime::UNIX_EPOCH.to_unix_time(), (0, 0));
    /// assert_eq!(
    ///     FileTime::MAX.to_unix_time(),
    ///     (1_833_029_933_770, 955_161_500)
    /// );
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[must_use]
    pub fn to_unix_time(self) -> (i64, u32) {
        let ts = self.to_unix_time_nanos();
        let secs = i64::try_from(ts.div_euclid(1_000_000_000))
            .expect("the number of seconds should be in the range of `i64`");
        let mut subsec_nanos = u32::try_from(ts.abs() % 1_000_000_000)
            .expect("the number of nanoseconds should be in the range of `u32`");
        if secs.is_negative() && subsec_nanos != 0 {
            subsec_nanos = NANOS_PER_SEC - subsec_nanos;
        }
        (secs, subsec_nanos)
    }

    /// Returns [Unix time] in seconds which represents the same date and time
    /// as this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_unix_time_secs(), -11_644_473_600);
    /// assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_secs(), 0);
    /// assert_eq!(FileTime::MAX.to_unix_time_secs(), 1_833_029_933_770);
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[must_use]
    #[inline]
    pub fn to_unix_time_secs(self) -> i64 {
        self.to_unix_time().0
    }

    #[allow(clippy::missing_panics_doc)]
    /// Returns [Unix time] in milliseconds which represents the same date and
    /// time as this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.to_unix_time_millis(),
    ///     -11_644_473_600_000
    /// );
    /// assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_millis(), 0);
    /// assert_eq!(FileTime::MAX.to_unix_time_millis(), 1_833_029_933_770_955);
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[must_use]
    #[inline]
    pub fn to_unix_time_millis(self) -> i64 {
        self.to_unix_time_nanos()
            .div_euclid(1_000_000)
            .try_into()
            .expect("the number of milliseconds should be in the range of `i64`")
    }

    #[allow(clippy::missing_panics_doc)]
    /// Returns [Unix time] in microseconds which represents the same date and
    /// time as this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.to_unix_time_micros(),
    ///     -11_644_473_600_000_000
    /// );
    /// assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_micros(), 0);
    /// assert_eq!(
    ///     FileTime::MAX.to_unix_time_micros(),
    ///     1_833_029_933_770_955_161
    /// );
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[must_use]
    #[inline]
    pub fn to_unix_time_micros(self) -> i64 {
        self.to_unix_time_nanos()
            .div_euclid(1000)
            .try_into()
            .expect("the number of microseconds should be in the range of `i64`")
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
    /// assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_nanos(), 0);
    /// assert_eq!(
    ///     FileTime::MAX.to_unix_time_nanos(),
    ///     1_833_029_933_770_955_161_500
    /// );
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[must_use]
    #[inline]
    pub fn to_unix_time_nanos(self) -> i128 {
        (i128::from(self.to_raw()) * 100) - 11_644_473_600_000_000_000
    }

    /// Creates a `FileTime` with the given [Unix time].
    ///
    /// `secs` is the number of whole seconds, and `nanos` is the number of
    /// additional nanoseconds.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided Unix time is out of range for the file
    /// time.
    ///
    /// # Panics
    ///
    /// Panics if `nanos` is not less than 1 second.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_unix_time(-11_644_473_600, 0).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time(0, 0).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time(1_833_029_933_770, 955_161_500).unwrap(),
    ///     FileTime::MAX
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::from_unix_time(-11_644_473_601, 999_999_999).is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_unix_time(1_833_029_933_770, 955_161_501).is_err());
    /// ```
    ///
    /// The number of additional nanoseconds must be less than 1 second:
    ///
    /// ```should_panic
    /// # use nt_time::FileTime;
    /// #
    /// let _: FileTime = FileTime::from_unix_time(0, 1_000_000_000).unwrap();
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[inline]
    pub fn from_unix_time(secs: i64, nanos: u32) -> Result<Self, FileTimeRangeError> {
        assert!(nanos < NANOS_PER_SEC);
        let ts = (i128::from(secs) * 1_000_000_000) + i128::from(nanos);
        Self::from_unix_time_nanos(ts)
    }

    /// Creates a `FileTime` with the given [Unix time] in seconds.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `secs` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_unix_time_secs(-11_644_473_600).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_secs(0).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_secs(1_833_029_933_770).unwrap(),
    ///     FileTime::MAX - Duration::from_nanos(955_161_500)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::from_unix_time_secs(-11_644_473_601).is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_unix_time_secs(1_833_029_933_771).is_err());
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[inline]
    pub fn from_unix_time_secs(secs: i64) -> Result<Self, FileTimeRangeError> {
        Self::from_unix_time(secs, 0)
    }

    /// Creates a `FileTime` with the given [Unix time] in milliseconds.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `millis` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_unix_time_millis(-11_644_473_600_000).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_millis(0).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_millis(1_833_029_933_770_955).unwrap(),
    ///     FileTime::MAX - Duration::from_nanos(161_500)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::from_unix_time_millis(-11_644_473_600_001).is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_unix_time_millis(1_833_029_933_770_956).is_err());
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[inline]
    pub fn from_unix_time_millis(millis: i64) -> Result<Self, FileTimeRangeError> {
        let nanos = i128::from(millis) * 1_000_000;
        Self::from_unix_time_nanos(nanos)
    }

    /// Creates a `FileTime` with the given [Unix time] in microseconds.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `micros` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_unix_time_micros(-11_644_473_600_000_000).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_micros(0).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_micros(1_833_029_933_770_955_161).unwrap(),
    ///     FileTime::MAX - Duration::from_nanos(500)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::from_unix_time_micros(-11_644_473_600_000_001).is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_unix_time_micros(1_833_029_933_770_955_162).is_err());
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    #[inline]
    pub fn from_unix_time_micros(micros: i64) -> Result<Self, FileTimeRangeError> {
        let nanos = i128::from(micros) * 1000;
        Self::from_unix_time_nanos(nanos)
    }

    /// Creates a `FileTime` with the given [Unix time] in nanoseconds.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `nanos` is out of range for the file time.
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
    ///     FileTime::from_unix_time_nanos(0).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_500).unwrap(),
    ///     FileTime::MAX
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::from_unix_time_nanos(-11_644_473_600_000_000_001).is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_501).is_err());
    /// ```
    ///
    /// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
    pub fn from_unix_time_nanos(nanos: i128) -> Result<Self, FileTimeRangeError> {
        (nanos <= 1_833_029_933_770_955_161_500)
            .then_some(nanos)
            .ok_or_else(|| FileTimeRangeErrorKind::Overflow.into())
            .and_then(|ts| {
                (ts + 11_644_473_600_000_000_000)
                    .div_euclid(100)
                    .try_into()
                    .map_err(|_| FileTimeRangeErrorKind::Negative.into())
            })
            .map(Self::new)
    }
}

#[cfg(test)]
mod tests {
    use core::time::Duration;

    use super::{super::FILE_TIMES_PER_SEC, *};

    #[test]
    fn to_unix_time() {
        assert_eq!(
            FileTime::NT_TIME_EPOCH.to_unix_time(),
            (-11_644_473_600, u32::MIN)
        );
        assert_eq!(FileTime::new(1).to_unix_time(), (-11_644_473_600, 100));
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC - 1).to_unix_time(),
            (-11_644_473_600, NANOS_PER_SEC - 100)
        );
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC).to_unix_time(),
            (-11_644_473_599, u32::MIN)
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(100)).to_unix_time(),
            (i64::default() - 1, NANOS_PER_SEC - 100)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.to_unix_time(),
            (i64::default(), u32::MIN)
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(100)).to_unix_time(),
            (i64::default(), 100)
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(100)).to_unix_time(),
            (1_833_029_933_770, 955_161_400)
        );
        assert_eq!(
            FileTime::MAX.to_unix_time(),
            (1_833_029_933_770, 955_161_500)
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn to_unix_time_roundtrip(ft: u64) {
        use proptest::prop_assert;

        let ts = FileTime::new(ft).to_unix_time();
        prop_assert!((-11_644_473_600..=1_833_029_933_770).contains(&ts.0));
        prop_assert!(ts.1 < NANOS_PER_SEC);
    }

    #[test]
    fn to_unix_time_secs() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_unix_time_secs(), -11_644_473_600);
        assert_eq!(FileTime::new(1).to_unix_time_secs(), -11_644_473_600);
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC - 1).to_unix_time_secs(),
            -11_644_473_600
        );
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC).to_unix_time_secs(),
            -11_644_473_599
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_secs(1)).to_unix_time_secs(),
            i64::default() - 1
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(999_999_900)).to_unix_time_secs(),
            i64::default() - 1
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(100)).to_unix_time_secs(),
            i64::default() - 1
        );
        assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_secs(), i64::default());
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(100)).to_unix_time_secs(),
            i64::default()
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(999_999_900)).to_unix_time_secs(),
            i64::default()
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_secs(1)).to_unix_time_secs(),
            i64::default() + 1
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(955_161_600)).to_unix_time_secs(),
            1_833_029_933_769
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(955_161_500)).to_unix_time_secs(),
            1_833_029_933_770
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(955_161_400)).to_unix_time_secs(),
            1_833_029_933_770
        );
        assert_eq!(FileTime::MAX.to_unix_time_secs(), 1_833_029_933_770);
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn to_unix_time_secs_roundtrip(ft: u64) {
        use proptest::prop_assert;

        let ts = FileTime::new(ft).to_unix_time_secs();
        prop_assert!((-11_644_473_600..=1_833_029_933_770).contains(&ts));
    }

    #[test]
    fn to_unix_time_millis() {
        assert_eq!(
            FileTime::NT_TIME_EPOCH.to_unix_time_millis(),
            -11_644_473_600_000
        );
        assert_eq!(FileTime::new(1).to_unix_time_millis(), -11_644_473_600_000);
        assert_eq!(
            FileTime::new(9999).to_unix_time_millis(),
            -11_644_473_600_000
        );
        assert_eq!(
            FileTime::new(10000).to_unix_time_millis(),
            -11_644_473_599_999
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_millis(1)).to_unix_time_millis(),
            i64::default() - 1
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(999_900)).to_unix_time_millis(),
            i64::default() - 1
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(100)).to_unix_time_millis(),
            i64::default() - 1
        );
        assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_millis(), i64::default());
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(999_900)).to_unix_time_millis(),
            i64::default()
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(100)).to_unix_time_millis(),
            i64::default()
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_millis(1)).to_unix_time_millis(),
            i64::default() + 1
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(161_600)).to_unix_time_millis(),
            1_833_029_933_770_954
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(161_500)).to_unix_time_millis(),
            1_833_029_933_770_955
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(161_400)).to_unix_time_millis(),
            1_833_029_933_770_955
        );
        assert_eq!(FileTime::MAX.to_unix_time_millis(), 1_833_029_933_770_955);
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn to_unix_time_millis_roundtrip(ft: u64) {
        use proptest::prop_assert;

        let ts = FileTime::new(ft).to_unix_time_millis();
        prop_assert!((-11_644_473_600_000..=1_833_029_933_770_955).contains(&ts));
    }

    #[test]
    fn to_unix_time_micros() {
        assert_eq!(
            FileTime::NT_TIME_EPOCH.to_unix_time_micros(),
            -11_644_473_600_000_000
        );
        assert_eq!(
            FileTime::new(1).to_unix_time_micros(),
            -11_644_473_600_000_000
        );
        assert_eq!(
            FileTime::new(9).to_unix_time_micros(),
            -11_644_473_600_000_000
        );
        assert_eq!(
            FileTime::new(10).to_unix_time_micros(),
            -11_644_473_599_999_999
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_micros(1)).to_unix_time_micros(),
            i64::default() - 1
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(900)).to_unix_time_micros(),
            i64::default() - 1
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(100)).to_unix_time_micros(),
            i64::default() - 1
        );
        assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_micros(), i64::default());
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(100)).to_unix_time_micros(),
            i64::default()
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(900)).to_unix_time_micros(),
            i64::default()
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_micros(1)).to_unix_time_micros(),
            i64::default() + 1
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(600)).to_unix_time_micros(),
            1_833_029_933_770_955_160
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(500)).to_unix_time_micros(),
            1_833_029_933_770_955_161
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(400)).to_unix_time_micros(),
            1_833_029_933_770_955_161
        );
        assert_eq!(
            FileTime::MAX.to_unix_time_micros(),
            1_833_029_933_770_955_161
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn to_unix_time_micros_roundtrip(ft: u64) {
        use proptest::prop_assert;

        let ts = FileTime::new(ft).to_unix_time_micros();
        prop_assert!((-11_644_473_600_000_000..=1_833_029_933_770_955_161).contains(&ts));
    }

    #[test]
    fn to_unix_time_nanos() {
        assert_eq!(
            FileTime::NT_TIME_EPOCH.to_unix_time_nanos(),
            -11_644_473_600_000_000_000
        );
        assert_eq!(
            FileTime::new(1).to_unix_time_nanos(),
            -11_644_473_599_999_999_900
        );
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC - 1).to_unix_time_nanos(),
            -11_644_473_599_000_000_100
        );
        assert_eq!(
            FileTime::new(FILE_TIMES_PER_SEC).to_unix_time_nanos(),
            -11_644_473_599_000_000_000
        );
        assert_eq!(
            (FileTime::UNIX_EPOCH - Duration::from_nanos(100)).to_unix_time_nanos(),
            i128::default() - 100
        );
        assert_eq!(FileTime::UNIX_EPOCH.to_unix_time_nanos(), i128::default());
        assert_eq!(
            (FileTime::UNIX_EPOCH + Duration::from_nanos(100)).to_unix_time_nanos(),
            i128::default() + 100
        );
        assert_eq!(
            (FileTime::MAX - Duration::from_nanos(100)).to_unix_time_nanos(),
            1_833_029_933_770_955_161_400
        );
        assert_eq!(
            FileTime::MAX.to_unix_time_nanos(),
            1_833_029_933_770_955_161_500
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn to_unix_time_nanos_roundtrip(ft: u64) {
        use proptest::prop_assert;

        let ts = FileTime::new(ft).to_unix_time_nanos();
        prop_assert!((-11_644_473_600_000_000_000..=1_833_029_933_770_955_161_500).contains(&ts));
    }

    #[test]
    fn from_unix_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_601, NANOS_PER_SEC - 1).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_601, NANOS_PER_SEC - 99).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_601, NANOS_PER_SEC - 100).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time(i64::MIN, NANOS_PER_SEC - 1).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time(i64::MIN, u32::MIN).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_before_nt_time_epoch_roundtrip(
        #[strategy(..=-11_644_473_601_i64)] secs: i64,
        #[strategy(..NANOS_PER_SEC)] nanos: u32,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time(secs, nanos).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn from_unix_time() {
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600, 0).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600, 1).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600, 99).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600, 100).unwrap(),
            FileTime::new(1)
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600, NANOS_PER_SEC - 100).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600, NANOS_PER_SEC - 99).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_600, NANOS_PER_SEC - 1).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_unix_time(-11_644_473_599, 0).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC)
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default() - 1, NANOS_PER_SEC - 100).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default() - 1, NANOS_PER_SEC - 99).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default() - 1, NANOS_PER_SEC - 1).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default(), u32::MIN).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default(), 1).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default(), 99).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time(i64::default(), 100).unwrap(),
            FileTime::UNIX_EPOCH + Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time(1_833_029_933_770, 955_161_500).unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_roundtrip(
        #[strategy(-11_644_473_600..=1_833_029_933_770_i64)] secs: i64,
        #[strategy(..NANOS_PER_SEC)] nanos: u32,
    ) {
        use proptest::{prop_assert, prop_assume};

        if secs == 1_833_029_933_770 {
            prop_assume!(nanos <= 955_161_500);
        }

        prop_assert!(FileTime::from_unix_time(secs, nanos).is_ok());
    }

    #[test]
    fn from_unix_time_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_unix_time(1_833_029_933_770, 955_161_501).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
        assert_eq!(
            FileTime::from_unix_time(i64::MAX, u32::MIN).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
        assert_eq!(
            FileTime::from_unix_time(i64::MAX, NANOS_PER_SEC - 1).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_with_too_big_date_time_roundtrip(
        #[strategy(1_833_029_933_770_i64..)] secs: i64,
        #[strategy(..NANOS_PER_SEC)] nanos: u32,
    ) {
        use proptest::{prop_assert_eq, prop_assume};

        if secs == 1_833_029_933_770 {
            prop_assume!(nanos > 955_161_500);
        }

        prop_assert_eq!(
            FileTime::from_unix_time(secs, nanos).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[test]
    #[should_panic]
    #[allow(clippy::should_panic_without_expect)]
    fn from_unix_time_with_too_big_subsec_nanos() {
        let _: FileTime = FileTime::from_unix_time(i64::default(), NANOS_PER_SEC).unwrap();
    }

    #[test]
    fn from_unix_time_secs_before_nt_time_epoch() {
        assert_eq!(
            FileTime::from_unix_time_secs(-11_644_473_601).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time_secs(i64::MIN).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_secs_before_nt_time_epoch_roundtrip(
        #[strategy(..=-11_644_473_601_i64)] ts: i64,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_secs(ts).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn from_unix_time_secs() {
        assert_eq!(
            FileTime::from_unix_time_secs(-11_644_473_600).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_secs(-11_644_473_599).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC)
        );
        assert_eq!(
            FileTime::from_unix_time_secs(i64::default() - 1).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_secs(1)
        );
        assert_eq!(
            FileTime::from_unix_time_secs(i64::default()).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_secs(i64::default() + 1).unwrap(),
            FileTime::UNIX_EPOCH + Duration::from_secs(1)
        );
        assert_eq!(
            FileTime::from_unix_time_secs(1_833_029_933_770).unwrap(),
            FileTime::MAX - Duration::from_nanos(955_161_500)
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_secs_roundtrip(#[strategy(-11_644_473_600..=1_833_029_933_770_i64)] ts: i64) {
        use proptest::prop_assert;

        prop_assert!(FileTime::from_unix_time_secs(ts).is_ok());
    }

    #[test]
    fn from_unix_time_secs_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_unix_time_secs(1_833_029_933_771).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
        assert_eq!(
            FileTime::from_unix_time_secs(i64::MAX).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_secs_with_too_big_date_time_roundtrip(
        #[strategy(1_833_029_933_771_i64..)] ts: i64,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_secs(ts).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[test]
    fn from_unix_time_millis_before_nt_time_epoch() {
        assert_eq!(
            FileTime::from_unix_time_millis(-11_644_473_600_001).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time_millis(i64::MIN).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_millis_before_nt_time_epoch_roundtrip(
        #[strategy(..=-11_644_473_600_001_i64)] ts: i64,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_millis(ts).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn from_unix_time_millis() {
        assert_eq!(
            FileTime::from_unix_time_millis(-11_644_473_600_000).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_millis(-11_644_473_599_999).unwrap(),
            FileTime::new(10000)
        );
        assert_eq!(
            FileTime::from_unix_time_millis(i64::default() - 1).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_millis(1)
        );
        assert_eq!(
            FileTime::from_unix_time_millis(i64::default()).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_millis(i64::default() + 1).unwrap(),
            FileTime::UNIX_EPOCH + Duration::from_millis(1)
        );
        assert_eq!(
            FileTime::from_unix_time_millis(1_833_029_933_770_955).unwrap(),
            FileTime::MAX - Duration::from_nanos(161_500)
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_millis_roundtrip(
        #[strategy(-11_644_473_600_000..=1_833_029_933_770_955_i64)] ts: i64,
    ) {
        use proptest::prop_assert;

        prop_assert!(FileTime::from_unix_time_millis(ts).is_ok());
    }

    #[test]
    fn from_unix_time_millis_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_unix_time_millis(1_833_029_933_770_956).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
        assert_eq!(
            FileTime::from_unix_time_millis(i64::MAX).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_millis_with_too_big_date_time_roundtrip(
        #[strategy(1_833_029_933_770_956_i64..)] ts: i64,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_millis(ts).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[test]
    fn from_unix_time_micros_before_nt_time_epoch() {
        assert_eq!(
            FileTime::from_unix_time_micros(-11_644_473_600_000_001).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time_micros(i64::MIN).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_micros_before_nt_time_epoch_roundtrip(
        #[strategy(..=-11_644_473_600_000_001_i64)] ts: i64,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_micros(ts).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn from_unix_time_micros() {
        assert_eq!(
            FileTime::from_unix_time_micros(-11_644_473_600_000_000).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_micros(-11_644_473_599_999_999).unwrap(),
            FileTime::new(10)
        );
        assert_eq!(
            FileTime::from_unix_time_micros(i64::default() - 1).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_micros(1)
        );
        assert_eq!(
            FileTime::from_unix_time_micros(i64::default()).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_micros(i64::default() + 1).unwrap(),
            FileTime::UNIX_EPOCH + Duration::from_micros(1)
        );
        assert_eq!(
            FileTime::from_unix_time_micros(1_833_029_933_770_955_161).unwrap(),
            FileTime::MAX - Duration::from_nanos(500)
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_micros_roundtrip(
        #[strategy(-11_644_473_600_000_000..=1_833_029_933_770_955_161_i64)] ts: i64,
    ) {
        use proptest::prop_assert;

        prop_assert!(FileTime::from_unix_time_micros(ts).is_ok());
    }

    #[test]
    fn from_unix_time_micros_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_unix_time_micros(1_833_029_933_770_955_162).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
        assert_eq!(
            FileTime::from_unix_time_micros(i64::MAX).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_micros_with_too_big_date_time_roundtrip(
        #[strategy(1_833_029_933_770_955_162_i64..)] ts: i64,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_micros(ts).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[test]
    fn from_unix_time_nanos_before_nt_time_epoch() {
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_600_000_000_100).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_600_000_000_099).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_600_000_000_001).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::MIN).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_nanos_before_nt_time_epoch_roundtrip(
        #[strategy(..=-11_644_473_600_000_000_001_i128)] ts: i128,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_nanos(ts).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn from_unix_time_nanos() {
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_600_000_000_000).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_599_999_999_999).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_599_999_999_901).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_599_999_999_900).unwrap(),
            FileTime::new(1)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_599_000_000_100).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_599_000_000_099).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_599_000_000_001).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC - 1)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(-11_644_473_599_000_000_000).unwrap(),
            FileTime::new(FILE_TIMES_PER_SEC)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default() - 100).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default() - 99).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default() - 1).unwrap(),
            FileTime::UNIX_EPOCH - Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default()).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default() + 1).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default() + 99).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::default() + 100).unwrap(),
            FileTime::UNIX_EPOCH + Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_500).unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_nanos_roundtrip(
        #[strategy(-11_644_473_600_000_000_000..=1_833_029_933_770_955_161_500_i128)] ts: i128,
    ) {
        use proptest::prop_assert;

        prop_assert!(FileTime::from_unix_time_nanos(ts).is_ok());
    }

    #[test]
    fn from_unix_time_nanos_with_too_big_date_time() {
        assert_eq!(
            FileTime::from_unix_time_nanos(1_833_029_933_770_955_161_501).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
        assert_eq!(
            FileTime::from_unix_time_nanos(i128::MAX).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_unix_time_nanos_with_too_big_date_time_roundtrip(
        #[strategy(1_833_029_933_770_955_161_501_i128..)] ts: i128,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::from_unix_time_nanos(ts).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }
}
