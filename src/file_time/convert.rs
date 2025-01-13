// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and other types.

use core::num::TryFromIntError;

use time::{error::ComponentRange, OffsetDateTime};

use super::FileTime;
use crate::error::{FileTimeRangeError, FileTimeRangeErrorKind};

impl From<FileTime> for u64 {
    /// Converts a `FileTime` to the file time.
    ///
    /// Equivalent to [`FileTime::to_raw`] except that it is not callable in
    /// const contexts.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(u64::from(FileTime::NT_TIME_EPOCH), u64::MIN);
    /// assert_eq!(u64::from(FileTime::UNIX_EPOCH), 116_444_736_000_000_000);
    /// assert_eq!(u64::from(FileTime::SIGNED_MAX), i64::MAX as u64);
    /// assert_eq!(u64::from(FileTime::MAX), u64::MAX);
    /// ```
    #[inline]
    fn from(ft: FileTime) -> Self {
        ft.to_raw()
    }
}

impl TryFrom<FileTime> for i64 {
    type Error = TryFromIntError;

    /// Converts a `FileTime` to the file time.
    ///
    /// The file time is sometimes represented as an [`i64`] value, such as in
    /// the [`DateTime.FromFileTimeUtc`] method and the
    /// [`DateTime.ToFileTimeUtc`] method in [.NET].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `ft` is after "+30828-09-14 02:48:05.477580700 UTC".
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(i64::try_from(FileTime::NT_TIME_EPOCH).unwrap(), 0);
    /// assert_eq!(
    ///     i64::try_from(FileTime::UNIX_EPOCH).unwrap(),
    ///     116_444_736_000_000_000
    /// );
    /// assert_eq!(i64::try_from(FileTime::SIGNED_MAX).unwrap(), i64::MAX);
    ///
    /// assert!(i64::try_from(FileTime::MAX).is_err());
    /// ```
    ///
    /// [`DateTime.FromFileTimeUtc`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.fromfiletimeutc
    /// [`DateTime.ToFileTimeUtc`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.tofiletimeutc
    /// [.NET]: https://dotnet.microsoft.com/
    #[inline]
    fn try_from(ft: FileTime) -> Result<Self, Self::Error> {
        ft.to_raw().try_into()
    }
}

#[cfg(feature = "std")]
impl From<FileTime> for std::time::SystemTime {
    /// Converts a `FileTime` to a [`SystemTime`](std::time::SystemTime).
    ///
    /// # Panics
    ///
    /// Panics if the resulting time cannot be represented by a
    /// [`SystemTime`](std::time::SystemTime).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::time::{Duration, SystemTime};
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     SystemTime::from(FileTime::NT_TIME_EPOCH),
    ///     SystemTime::UNIX_EPOCH - Duration::from_secs(11_644_473_600)
    /// );
    /// assert_eq!(
    ///     SystemTime::from(FileTime::UNIX_EPOCH),
    ///     SystemTime::UNIX_EPOCH
    /// );
    /// ```
    #[inline]
    fn from(ft: FileTime) -> Self {
        use std::time::Duration;

        use super::FILE_TIMES_PER_SEC;

        let duration = Duration::new(
            ft.to_raw() / FILE_TIMES_PER_SEC,
            u32::try_from((ft.to_raw() % FILE_TIMES_PER_SEC) * 100)
                .expect("the number of nanoseconds should be in the range of `u32`"),
        );
        (Self::UNIX_EPOCH - (FileTime::UNIX_EPOCH - FileTime::NT_TIME_EPOCH)) + duration
    }
}

impl TryFrom<FileTime> for OffsetDateTime {
    type Error = ComponentRange;

    /// Converts a `FileTime` to a [`OffsetDateTime`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `time` is out of range for [`OffsetDateTime`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     time::{macros::datetime, OffsetDateTime},
    /// #     FileTime,
    /// # };
    /// #
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
    ///     datetime!(1601-01-01 00:00 UTC)
    /// );
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::UNIX_EPOCH).unwrap(),
    ///     OffsetDateTime::UNIX_EPOCH
    /// );
    /// ```
    ///
    /// With the `large-dates` feature disabled, returns [`Err`] if the file
    /// time represents after "9999-12-31 23:59:59.999999900 UTC":
    ///
    /// ```
    /// # #[cfg(not(feature = "large-dates"))]
    /// # {
    /// # use nt_time::{time::OffsetDateTime, FileTime};
    /// #
    /// assert!(OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).is_err());
    /// # }
    /// ```
    ///
    /// With the `large-dates` feature enabled, this always succeeds:
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// # use nt_time::{
    /// #     time::{macros::datetime, OffsetDateTime},
    /// #     FileTime,
    /// # };
    /// #
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).unwrap(),
    ///     datetime!(+10000-01-01 00:00 UTC)
    /// );
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::SIGNED_MAX).unwrap(),
    ///     datetime!(+30828-09-14 02:48:05.477_580_700 UTC)
    /// );
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::MAX).unwrap(),
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
    /// );
    /// # }
    /// ```
    #[inline]
    fn try_from(ft: FileTime) -> Result<Self, Self::Error> {
        Self::from_unix_timestamp_nanos(ft.to_unix_time_nanos())
    }
}

#[cfg(feature = "chrono")]
impl From<FileTime> for chrono::DateTime<chrono::Utc> {
    /// Converts a `FileTime` to a [`DateTime<Utc>`](chrono::DateTime).
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     chrono::{DateTime, Utc},
    /// #     FileTime,
    /// # };
    /// #
    /// assert_eq!(
    ///     DateTime::<Utc>::from(FileTime::NT_TIME_EPOCH),
    ///     "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()
    /// );
    /// assert_eq!(
    ///     DateTime::<Utc>::from(FileTime::UNIX_EPOCH),
    ///     DateTime::<Utc>::UNIX_EPOCH
    /// );
    /// ```
    #[inline]
    fn from(ft: FileTime) -> Self {
        let ut = ft.to_unix_time();
        Self::from_timestamp(ut.0, ut.1)
            .expect("Unix time in nanoseconds should be in the range of `DateTime<Utc>`")
    }
}

impl From<u64> for FileTime {
    /// Converts the file time to a `FileTime`.
    ///
    /// Equivalent to [`FileTime::new`] except that it is not callable in const
    /// contexts.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::from(u64::MIN), FileTime::NT_TIME_EPOCH);
    /// assert_eq!(
    ///     FileTime::from(116_444_736_000_000_000),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(FileTime::from(i64::MAX as u64), FileTime::SIGNED_MAX);
    /// assert_eq!(FileTime::from(u64::MAX), FileTime::MAX);
    /// ```
    #[inline]
    fn from(ft: u64) -> Self {
        Self::new(ft)
    }
}

impl TryFrom<i64> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts the file time to a `FileTime`.
    ///
    /// The file time is sometimes represented as an [`i64`] value, such as in
    /// the [`DateTime.FromFileTimeUtc`] method and the
    /// [`DateTime.ToFileTimeUtc`] method in [.NET].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `ft` is negative.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::try_from(0_i64).unwrap(), FileTime::NT_TIME_EPOCH);
    /// assert_eq!(
    ///     FileTime::try_from(116_444_736_000_000_000_i64).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(FileTime::try_from(i64::MAX).unwrap(), FileTime::SIGNED_MAX);
    ///
    /// assert!(FileTime::try_from(i64::MIN).is_err());
    /// ```
    ///
    /// [`DateTime.FromFileTimeUtc`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.fromfiletimeutc
    /// [`DateTime.ToFileTimeUtc`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.tofiletimeutc
    /// [.NET]: https://dotnet.microsoft.com/
    #[inline]
    fn try_from(ft: i64) -> Result<Self, Self::Error> {
        ft.try_into()
            .map_err(|_| FileTimeRangeErrorKind::Negative.into())
            .map(Self::new)
    }
}

#[cfg(feature = "std")]
impl TryFrom<std::time::SystemTime> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts a [`SystemTime`](std::time::SystemTime) to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `time` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::time::{Duration, SystemTime};
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::try_from(SystemTime::UNIX_EPOCH - Duration::from_secs(11_644_473_600)).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(SystemTime::UNIX_EPOCH).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::try_from(
    ///     SystemTime::UNIX_EPOCH - Duration::from_nanos(11_644_473_600_000_000_100)
    /// )
    /// .is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// #[cfg(not(windows))]
    /// assert!(FileTime::try_from(
    ///     SystemTime::UNIX_EPOCH + Duration::new(1_833_029_933_770, 955_161_600)
    /// )
    /// .is_err());
    /// ```
    #[inline]
    fn try_from(st: std::time::SystemTime) -> Result<Self, Self::Error> {
        use std::time::SystemTime;

        let elapsed = st
            .duration_since(SystemTime::UNIX_EPOCH - (Self::UNIX_EPOCH - Self::NT_TIME_EPOCH))
            .map(|d| d.as_nanos())
            .map_err(|_| FileTimeRangeErrorKind::Negative)?;
        let ft = u64::try_from(elapsed / 100).map_err(|_| FileTimeRangeErrorKind::Overflow)?;
        Ok(Self::new(ft))
    }
}

impl TryFrom<OffsetDateTime> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts a [`OffsetDateTime`] to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `dt` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     time::{macros::datetime, Duration, OffsetDateTime},
    /// #     FileTime,
    /// # };
    /// #
    /// assert_eq!(
    ///     FileTime::try_from(datetime!(1601-01-01 00:00 UTC)).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(OffsetDateTime::UNIX_EPOCH).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(
    ///     FileTime::try_from(datetime!(1601-01-01 00:00 UTC) - Duration::nanoseconds(100)).is_err()
    /// );
    /// ```
    ///
    /// With the `large-dates` feature enabled, returns [`Err`] if
    /// [`OffsetDateTime`] represents after "+60056-05-28 05:36:10.955161500
    /// UTC":
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// # use nt_time::{
    /// #     time::{macros::datetime, Duration},
    /// #     FileTime,
    /// # };
    /// #
    /// assert!(FileTime::try_from(
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC) + Duration::nanoseconds(100)
    /// )
    /// .is_err());
    /// # }
    /// ```
    #[inline]
    fn try_from(dt: OffsetDateTime) -> Result<Self, Self::Error> {
        Self::from_unix_time_nanos(dt.unix_timestamp_nanos())
    }
}

#[cfg(feature = "chrono")]
impl TryFrom<chrono::DateTime<chrono::Utc>> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts a [`DateTime<Utc>`](chrono::DateTime) to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `dt` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     chrono::{DateTime, TimeDelta, Utc},
    /// #     FileTime,
    /// # };
    /// #
    /// assert_eq!(
    ///     FileTime::try_from("1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(DateTime::<Utc>::UNIX_EPOCH).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::try_from(
    ///     "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap() - TimeDelta::nanoseconds(100)
    /// )
    /// .is_err());
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::try_from(
    ///     "+60056-05-28 05:36:10.955161500 UTC"
    ///         .parse::<DateTime<Utc>>()
    ///         .unwrap()
    ///         + TimeDelta::nanoseconds(100)
    /// )
    /// .is_err());
    /// ```
    #[inline]
    fn try_from(dt: chrono::DateTime<chrono::Utc>) -> Result<Self, Self::Error> {
        Self::from_unix_time(dt.timestamp(), dt.timestamp_subsec_nanos())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_file_time_to_u64() {
        assert_eq!(u64::from(FileTime::NT_TIME_EPOCH), u64::MIN);
        assert_eq!(u64::from(FileTime::UNIX_EPOCH), 116_444_736_000_000_000);
        assert_eq!(u64::from(FileTime::SIGNED_MAX), i64::MAX as u64);
        assert_eq!(u64::from(FileTime::MAX), u64::MAX);
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_file_time_to_u64_roundtrip(ft: FileTime) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(u64::from(ft), ft.to_raw());
    }

    #[test]
    fn try_from_file_time_to_i64() {
        assert_eq!(
            i64::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
            i64::default()
        );
        assert_eq!(
            i64::try_from(FileTime::UNIX_EPOCH).unwrap(),
            116_444_736_000_000_000
        );
        assert_eq!(i64::try_from(FileTime::SIGNED_MAX).unwrap(), i64::MAX);
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn try_from_file_time_to_i64_roundtrip(ft: FileTime) {
        use proptest::prop_assert;

        if ft <= FileTime::SIGNED_MAX {
            prop_assert!(i64::try_from(ft).is_ok());
        } else {
            prop_assert!(i64::try_from(ft).is_err());
        }
    }

    #[test]
    fn try_from_file_time_to_i64_with_too_big_file_time() {
        assert!(i64::try_from(FileTime::new(u64::try_from(i64::MAX).unwrap() + 1)).is_err());
        assert!(i64::try_from(FileTime::MAX).is_err());
    }

    #[cfg(feature = "std")]
    #[test]
    fn from_file_time_to_system_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            SystemTime::from(FileTime::NT_TIME_EPOCH),
            SystemTime::UNIX_EPOCH - (FileTime::UNIX_EPOCH - FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            SystemTime::from(FileTime::UNIX_EPOCH),
            SystemTime::UNIX_EPOCH
        );
        assert_eq!(
            SystemTime::from(FileTime::new(2_650_467_743_999_999_999)),
            SystemTime::UNIX_EPOCH + Duration::new(253_402_300_799, 999_999_900)
        );
        assert_eq!(
            SystemTime::from(FileTime::new(2_650_467_744_000_000_000)),
            SystemTime::UNIX_EPOCH + Duration::from_secs(253_402_300_800)
        );
        // Largest `SystemTime` on Windows.
        assert_eq!(
            SystemTime::from(FileTime::new(9_223_372_036_854_775_807)),
            SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700)
        );
        if !cfg!(windows) {
            assert_eq!(
                SystemTime::from(FileTime::MAX),
                SystemTime::UNIX_EPOCH + Duration::new(1_833_029_933_770, 955_161_500)
            );
        }
    }

    #[test]
    fn try_from_file_time_to_offset_date_time() {
        use time::macros::datetime;

        assert_eq!(
            OffsetDateTime::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
            datetime!(1601-01-01 00:00 UTC)
        );
        assert_eq!(
            OffsetDateTime::try_from(FileTime::UNIX_EPOCH).unwrap(),
            OffsetDateTime::UNIX_EPOCH
        );
        assert_eq!(
            OffsetDateTime::try_from(FileTime::new(2_650_467_743_999_999_999)).unwrap(),
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
        );
    }

    #[cfg(not(feature = "large-dates"))]
    #[test]
    fn try_from_file_time_to_offset_date_time_with_invalid_file_time() {
        assert!(OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).is_err());
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_file_time_to_offset_date_time_with_large_dates() {
        use time::macros::datetime;

        assert_eq!(
            OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).unwrap(),
            datetime!(+10000-01-01 00:00 UTC)
        );
        assert_eq!(
            OffsetDateTime::try_from(FileTime::SIGNED_MAX).unwrap(),
            datetime!(+30828-09-14 02:48:05.477_580_700 UTC)
        );
        assert_eq!(
            OffsetDateTime::try_from(FileTime::MAX).unwrap(),
            datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn from_file_time_to_chrono_date_time() {
        use chrono::{DateTime, Utc};

        assert_eq!(
            DateTime::<Utc>::from(FileTime::NT_TIME_EPOCH),
            "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()
        );
        assert_eq!(
            DateTime::<Utc>::from(FileTime::UNIX_EPOCH),
            DateTime::<Utc>::UNIX_EPOCH
        );
        assert_eq!(
            DateTime::<Utc>::from(FileTime::new(2_650_467_743_999_999_999)),
            "9999-12-31 23:59:59.999999900 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
        );
        assert_eq!(
            DateTime::<Utc>::from(FileTime::new(2_650_467_744_000_000_000)),
            "+10000-01-01 00:00:00 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
        );
        assert_eq!(
            DateTime::<Utc>::from(FileTime::SIGNED_MAX),
            "+30828-09-14 02:48:05.477580700 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
        );
        assert_eq!(
            DateTime::<Utc>::from(FileTime::MAX),
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
        );
    }

    #[test]
    fn from_u64_to_file_time() {
        assert_eq!(FileTime::from(u64::MIN), FileTime::NT_TIME_EPOCH);
        assert_eq!(
            FileTime::from(116_444_736_000_000_000),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(FileTime::from(i64::MAX as u64), FileTime::SIGNED_MAX);
        assert_eq!(FileTime::from(u64::MAX), FileTime::MAX);
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn from_u64_to_file_time_roundtrip(ft: u64) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(FileTime::from(ft), FileTime::new(ft));
    }

    #[test]
    fn try_from_i64_to_file_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::try_from(i64::MIN).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
        assert_eq!(
            FileTime::try_from(i64::default() - 1).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn try_from_i64_to_file_time_before_nt_time_epoch_roundtrip(
        #[strategy(..i64::default())] ft: i64,
    ) {
        use proptest::prop_assert_eq;

        prop_assert_eq!(
            FileTime::try_from(ft).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn try_from_i64_to_file_time() {
        assert_eq!(
            FileTime::try_from(i64::default()).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::try_from(116_444_736_000_000_000_i64).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(FileTime::try_from(i64::MAX).unwrap(), FileTime::SIGNED_MAX);
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn try_from_i64_to_file_time_roundtrip(#[strategy(i64::default()..)] ft: i64) {
        use proptest::prop_assert;

        prop_assert!(FileTime::try_from(ft).is_ok());
    }

    #[cfg(feature = "std")]
    #[test]
    fn try_from_system_time_to_file_time_before_nt_time_epoch() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            FileTime::try_from(if cfg!(windows) {
                SystemTime::UNIX_EPOCH - Duration::from_nanos(11_644_473_600_000_000_100)
            } else {
                SystemTime::UNIX_EPOCH - Duration::from_nanos(11_644_473_600_000_000_001)
            })
            .unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn try_from_system_time_to_file_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            FileTime::try_from(
                SystemTime::UNIX_EPOCH - (FileTime::UNIX_EPOCH - FileTime::NT_TIME_EPOCH)
            )
            .unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::try_from(SystemTime::UNIX_EPOCH).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::try_from(
                SystemTime::UNIX_EPOCH + Duration::new(253_402_300_799, 999_999_900)
            )
            .unwrap(),
            FileTime::new(2_650_467_743_999_999_999)
        );
        assert_eq!(
            FileTime::try_from(SystemTime::UNIX_EPOCH + Duration::from_secs(253_402_300_800))
                .unwrap(),
            FileTime::new(2_650_467_744_000_000_000)
        );
        // Largest `SystemTime` on Windows.
        assert_eq!(
            FileTime::try_from(
                SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700)
            )
            .unwrap(),
            FileTime::new(9_223_372_036_854_775_807)
        );
        if !cfg!(windows) {
            assert_eq!(
                FileTime::try_from(
                    SystemTime::UNIX_EPOCH + Duration::new(1_833_029_933_770, 955_161_500)
                )
                .unwrap(),
                FileTime::MAX
            );
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn try_from_system_time_to_file_time_with_too_big_system_time() {
        use std::time::{Duration, SystemTime};

        if cfg!(windows) {
            assert!(SystemTime::UNIX_EPOCH
                .checked_add(Duration::new(910_692_730_085, 477_580_800))
                .is_none());
        } else {
            assert_eq!(
                FileTime::try_from(
                    SystemTime::UNIX_EPOCH + Duration::new(1_833_029_933_770, 955_161_600)
                )
                .unwrap_err(),
                FileTimeRangeErrorKind::Overflow.into()
            );
        }
    }

    #[test]
    fn try_from_offset_date_time_to_file_time_before_nt_time_epoch() {
        use time::{macros::datetime, Duration};

        assert_eq!(
            FileTime::try_from(datetime!(1601-01-01 00:00 UTC) - Duration::nanoseconds(100))
                .unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn try_from_offset_date_time_to_file_time() {
        use time::macros::datetime;

        assert_eq!(
            FileTime::try_from(datetime!(1601-01-01 00:00 UTC)).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::try_from(OffsetDateTime::UNIX_EPOCH).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::try_from(datetime!(9999-12-31 23:59:59.999_999_999 UTC)).unwrap(),
            FileTime::new(2_650_467_743_999_999_999)
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_offset_date_time_to_file_time_with_large_dates() {
        use time::macros::datetime;

        assert_eq!(
            FileTime::try_from(datetime!(+10000-01-01 00:00 UTC)).unwrap(),
            FileTime::new(2_650_467_744_000_000_000)
        );
        assert_eq!(
            FileTime::try_from(datetime!(+30828-09-14 02:48:05.477_580_700 UTC)).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::try_from(datetime!(+60056-05-28 05:36:10.955_161_500 UTC)).unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_offset_date_time_to_file_time_with_too_big_date_time() {
        use time::{macros::datetime, Duration};

        assert_eq!(
            FileTime::try_from(
                datetime!(+60056-05-28 05:36:10.955_161_500 UTC) + Duration::nanoseconds(100)
            )
            .unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn try_from_chrono_date_time_to_file_time_before_nt_time_epoch() {
        use chrono::{DateTime, TimeDelta, Utc};

        assert_eq!(
            FileTime::try_from(
                "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()
                    - TimeDelta::nanoseconds(100)
            )
            .unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn try_from_chrono_date_time_to_file_time() {
        use chrono::{DateTime, Utc};

        assert_eq!(
            FileTime::try_from("1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap())
                .unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::try_from(DateTime::<Utc>::UNIX_EPOCH).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::try_from(
                "9999-12-31 23:59:59.999999999 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
            )
            .unwrap(),
            FileTime::new(2_650_467_743_999_999_999)
        );
        assert_eq!(
            FileTime::try_from(
                "+10000-01-01 00:00:00 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
            )
            .unwrap(),
            FileTime::new(2_650_467_744_000_000_000)
        );
        assert_eq!(
            FileTime::try_from(
                "+30828-09-14 02:48:05.477580700 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
            )
            .unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::try_from(
                "+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
            )
            .unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn try_from_chrono_date_time_to_file_time_with_too_big_date_time() {
        use chrono::{DateTime, TimeDelta, Utc};

        assert_eq!(
            FileTime::try_from(
                "+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
                    + TimeDelta::nanoseconds(100)
            )
            .unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }
}
