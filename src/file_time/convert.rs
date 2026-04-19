// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and other types.

#[cfg(feature = "std")]
use std::time::SystemTime;

#[cfg(feature = "chrono")]
use chrono::Utc;
#[cfg(feature = "dos-date-time")]
use dos_date_time::{
    error::{DateTimeRangeError, DateTimeRangeErrorKind},
    time::PrimitiveDateTime,
};
#[cfg(feature = "jiff")]
use jiff::Timestamp;
use time::{UtcDateTime, error::ComponentRange};

use super::FileTime;
use crate::error::FileTimeRangeError;
#[cfg(feature = "std")]
use crate::error::FileTimeRangeErrorKind;

impl From<FileTime> for u64 {
    fn from(ft: FileTime) -> Self {
        ft.to_raw()
    }
}

#[cfg(feature = "std")]
impl From<FileTime> for SystemTime {
    /// Converts a `FileTime` to a [`SystemTime`].
    ///
    /// # Panics
    ///
    /// Panics if the resulting time cannot be represented by a [`SystemTime`].
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
    ///     SystemTime::UNIX_EPOCH - Duration::from_hours(3_234_576)
    /// );
    /// assert_eq!(
    ///     SystemTime::from(FileTime::UNIX_EPOCH),
    ///     SystemTime::UNIX_EPOCH
    /// );
    /// ```
    fn from(ft: FileTime) -> Self {
        let duration = ft.to_duration();
        (Self::UNIX_EPOCH - FileTime::UNIX_EPOCH.to_duration()) + duration
    }
}

impl TryFrom<FileTime> for UtcDateTime {
    type Error = ComponentRange;

    /// Converts a `FileTime` to an [`UtcDateTime`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `ft` is out of range for [`UtcDateTime`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     FileTime,
    /// #     time::{UtcDateTime, macros::utc_datetime},
    /// # };
    /// #
    /// assert_eq!(
    ///     UtcDateTime::try_from(FileTime::NT_TIME_EPOCH),
    ///     Ok(utc_datetime!(1601-01-01 00:00:00))
    /// );
    /// assert_eq!(
    ///     UtcDateTime::try_from(FileTime::UNIX_EPOCH),
    ///     Ok(UtcDateTime::UNIX_EPOCH)
    /// );
    /// ```
    ///
    /// With the `large-dates` feature disabled, returns [`Err`] if the file
    /// time represents after `9999-12-31 23:59:59.999999900 UTC`:
    ///
    /// ```
    /// # #[cfg(not(feature = "large-dates"))]
    /// # {
    /// # use nt_time::{FileTime, time::UtcDateTime};
    /// #
    /// assert!(UtcDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).is_err());
    /// # }
    /// ```
    ///
    /// With the `large-dates` feature enabled, this always succeeds:
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// # use nt_time::{
    /// #     FileTime,
    /// #     time::{UtcDateTime, macros::utc_datetime},
    /// # };
    /// #
    /// assert_eq!(
    ///     UtcDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)),
    ///     Ok(utc_datetime!(+10000-01-01 00:00:00))
    /// );
    /// assert_eq!(
    ///     UtcDateTime::try_from(FileTime::SIGNED_MAX),
    ///     Ok(utc_datetime!(+30828-09-14 02:48:05.477_580_700))
    /// );
    /// assert_eq!(
    ///     UtcDateTime::try_from(FileTime::MAX),
    ///     Ok(utc_datetime!(+60056-05-28 05:36:10.955_161_500))
    /// );
    /// # }
    /// ```
    fn try_from(ft: FileTime) -> Result<Self, Self::Error> {
        Self::from_unix_timestamp_nanos(ft.to_unix_time_nanos())
    }
}

#[cfg(feature = "chrono")]
#[expect(clippy::fallible_impl_from)]
impl From<FileTime> for chrono::DateTime<Utc> {
    /// Converts a `FileTime` to a [`chrono::DateTime<Utc>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     FileTime,
    /// #     chrono::{DateTime, Utc},
    /// # };
    /// #
    /// assert_eq!(
    ///     DateTime::from(FileTime::NT_TIME_EPOCH),
    ///     "1601-01-01T00:00:00Z".parse::<DateTime<Utc>>().unwrap()
    /// );
    /// assert_eq!(DateTime::from(FileTime::UNIX_EPOCH), DateTime::UNIX_EPOCH);
    /// ```
    fn from(ft: FileTime) -> Self {
        let ut = ft.to_unix_time();
        Self::from_timestamp(ut.0, ut.1).unwrap()
    }
}

#[cfg(feature = "jiff")]
impl TryFrom<FileTime> for Timestamp {
    type Error = jiff::Error;

    /// Converts a `FileTime` to a [`Timestamp`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `ft` is out of range for [`Timestamp`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{FileTime, jiff::Timestamp};
    /// #
    /// assert_eq!(
    ///     Timestamp::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
    ///     Timestamp::from_second(-11_644_473_600).unwrap()
    /// );
    /// assert_eq!(
    ///     Timestamp::try_from(FileTime::UNIX_EPOCH).unwrap(),
    ///     Timestamp::UNIX_EPOCH
    /// );
    ///
    /// assert!(Timestamp::try_from(FileTime::MAX).is_err());
    /// ```
    fn try_from(ft: FileTime) -> Result<Self, Self::Error> {
        Self::from_nanosecond(ft.to_unix_time_nanos())
    }
}

#[cfg(feature = "dos-date-time")]
impl TryFrom<FileTime> for dos_date_time::DateTime {
    type Error = DateTimeRangeError;

    /// Converts a `FileTime` to a [`dos_date_time::DateTime`].
    ///
    /// <div class="warning">
    ///
    /// This method may round towards zero, truncating more precise times that a
    /// [`dos_date_time::DateTime`] cannot store.
    ///
    /// </div>
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `ft` is out of range for [`dos_date_time::DateTime`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{FileTime, dos_date_time::DateTime};
    /// #
    /// // From `1980-01-01 00:00:00 UTC` to `1980-01-01 00:00:00`.
    /// assert_eq!(
    ///     DateTime::try_from(FileTime::new(119_600_064_000_000_000)),
    ///     Ok(DateTime::MIN)
    /// );
    /// // From `2107-12-31 23:59:59 UTC` to `2107-12-31 23:59:58`.
    /// assert_eq!(
    ///     DateTime::try_from(FileTime::new(159_992_927_990_000_000)),
    ///     Ok(DateTime::MAX)
    /// );
    ///
    /// // Before `1980-01-01 00:00:00 UTC`.
    /// assert!(DateTime::try_from(FileTime::new(119_600_063_990_000_000)).is_err());
    /// // After `2107-12-31 23:59:59.999999900 UTC`.
    /// assert!(DateTime::try_from(FileTime::new(159_992_928_000_000_000)).is_err());
    /// ```
    fn try_from(ft: FileTime) -> Result<Self, Self::Error> {
        let dt = UtcDateTime::try_from(ft).map_err(|_| DateTimeRangeErrorKind::Overflow)?;
        Self::from_date_time(dt.date(), dt.time())
    }
}

impl From<u64> for FileTime {
    fn from(ft: u64) -> Self {
        Self::new(ft)
    }
}

#[cfg(feature = "std")]
impl TryFrom<SystemTime> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts a [`SystemTime`] to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `st` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::time::{Duration, SystemTime};
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::try_from(SystemTime::UNIX_EPOCH - Duration::from_hours(3_234_576)),
    ///     Ok(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(SystemTime::UNIX_EPOCH),
    ///     Ok(FileTime::UNIX_EPOCH)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// #[cfg(not(windows))]
    /// assert!(
    ///     FileTime::try_from(
    ///         SystemTime::UNIX_EPOCH - Duration::from_nanos(11_644_473_600_000_000_001)
    ///     )
    ///     .is_err()
    /// );
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// #[cfg(not(windows))]
    /// assert!(
    ///     FileTime::try_from(SystemTime::UNIX_EPOCH + Duration::new(1_833_029_933_770, 955_161_600))
    ///         .is_err()
    /// );
    /// ```
    fn try_from(st: SystemTime) -> Result<Self, Self::Error> {
        let elapsed = st
            .duration_since(SystemTime::UNIX_EPOCH - Self::UNIX_EPOCH.to_duration())
            .map_err(|_| FileTimeRangeErrorKind::Negative)?;
        Self::from_duration(elapsed)
    }
}

impl TryFrom<UtcDateTime> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts an [`UtcDateTime`] to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `dt` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     FileTime,
    /// #     time::{UtcDateTime, macros::utc_datetime},
    /// # };
    /// #
    /// assert_eq!(
    ///     FileTime::try_from(utc_datetime!(1601-01-01 00:00:00)),
    ///     Ok(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(UtcDateTime::UNIX_EPOCH),
    ///     Ok(FileTime::UNIX_EPOCH)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::try_from(utc_datetime!(1600-12-31 23:59:59.999_999_900)).is_err());
    /// ```
    ///
    /// With the `large-dates` feature enabled, returns [`Err`] if
    /// [`UtcDateTime`] represents after `+60056-05-28 05:36:10.955161500 UTC`:
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// # use nt_time::{FileTime, time::macros::utc_datetime};
    /// #
    /// assert!(FileTime::try_from(utc_datetime!(+60056-05-28 05:36:10.955_161_600)).is_err());
    /// # }
    /// ```
    fn try_from(dt: UtcDateTime) -> Result<Self, Self::Error> {
        Self::from_unix_time_nanos(dt.unix_timestamp_nanos())
    }
}

#[cfg(feature = "chrono")]
impl TryFrom<chrono::DateTime<Utc>> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts a [`chrono::DateTime<Utc>`] to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `dt` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     FileTime,
    /// #     chrono::{DateTime, Utc},
    /// # };
    /// #
    /// assert_eq!(
    ///     FileTime::try_from("1601-01-01T00:00:00Z".parse::<DateTime<Utc>>().unwrap()),
    ///     Ok(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(DateTime::UNIX_EPOCH),
    ///     Ok(FileTime::UNIX_EPOCH)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(
    ///     FileTime::try_from(
    ///         "1600-12-31T23:59:59.999999900Z"
    ///             .parse::<DateTime<Utc>>()
    ///             .unwrap()
    ///     )
    ///     .is_err()
    /// );
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(
    ///     FileTime::try_from(
    ///         "+60056-05-28T05:36:10.955161600Z"
    ///             .parse::<DateTime<Utc>>()
    ///             .unwrap()
    ///     )
    ///     .is_err()
    /// );
    /// ```
    fn try_from(dt: chrono::DateTime<Utc>) -> Result<Self, Self::Error> {
        Self::from_unix_time(dt.timestamp(), dt.timestamp_subsec_nanos())
    }
}

#[cfg(feature = "jiff")]
impl TryFrom<Timestamp> for FileTime {
    type Error = FileTimeRangeError;

    /// Converts a [`Timestamp`] to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `ts` is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{FileTime, jiff::Timestamp};
    /// #
    /// assert_eq!(
    ///     FileTime::try_from(Timestamp::from_second(-11_644_473_600).unwrap()),
    ///     Ok(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(Timestamp::UNIX_EPOCH),
    ///     Ok(FileTime::UNIX_EPOCH)
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(
    ///     FileTime::try_from(Timestamp::from_nanosecond(-11_644_473_600_000_000_001).unwrap())
    ///         .is_err()
    /// );
    /// ```
    fn try_from(ts: Timestamp) -> Result<Self, Self::Error> {
        Self::from_unix_time_nanos(ts.as_nanosecond())
    }
}

#[cfg(feature = "dos-date-time")]
#[expect(clippy::fallible_impl_from)]
impl From<dos_date_time::DateTime> for FileTime {
    /// Converts a [`dos_date_time::DateTime`] to a `FileTime`.
    ///
    /// This method assumes the time zone of `dt` is the UTC time zone.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{FileTime, dos_date_time::DateTime};
    /// #
    /// // From `1980-01-01 00:00:00` to `1980-01-01 00:00:00 UTC`.
    /// assert_eq!(
    ///     FileTime::from(DateTime::MIN),
    ///     FileTime::new(119_600_064_000_000_000)
    /// );
    /// // From `2107-12-31 23:59:58` to `2107-12-31 23:59:58 UTC`.
    /// assert_eq!(
    ///     FileTime::from(DateTime::MAX),
    ///     FileTime::new(159_992_927_980_000_000)
    /// );
    /// ```
    fn from(dt: dos_date_time::DateTime) -> Self {
        let dt = PrimitiveDateTime::from(dt).as_utc();
        Self::try_from(dt).unwrap()
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use std::time::Duration;

    #[cfg(feature = "chrono")]
    use chrono::{TimeZone, Timelike};
    #[cfg(feature = "dos-date-time")]
    use dos_date_time::{Date, Time};
    #[cfg(feature = "jiff")]
    use jiff::ToSpan;
    #[cfg(feature = "std")]
    use proptest::prop_assert_eq;
    #[cfg(feature = "std")]
    use test_strategy::proptest;
    use time::macros::utc_datetime;

    use super::*;
    use crate::error::FileTimeRangeErrorKind;

    #[test]
    fn from_file_time_to_u64() {
        assert_eq!(u64::from(FileTime::NT_TIME_EPOCH), u64::MIN);
        assert_eq!(u64::from(FileTime::UNIX_EPOCH), 116_444_736_000_000_000);
        assert_eq!(u64::from(FileTime::SIGNED_MAX), i64::MAX as u64);
        assert_eq!(u64::from(FileTime::MAX), u64::MAX);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_file_time_to_u64_roundtrip(ft: FileTime) {
        prop_assert_eq!(u64::from(ft), ft.to_raw());
    }

    #[cfg(feature = "std")]
    #[test]
    fn from_file_time_to_system_time() {
        assert_eq!(
            SystemTime::from(FileTime::NT_TIME_EPOCH),
            SystemTime::UNIX_EPOCH - FileTime::UNIX_EPOCH.to_duration()
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
            SystemTime::UNIX_EPOCH + Duration::from_hours(70_389_528)
        );
        // Largest `SystemTime` on Windows.
        assert_eq!(
            SystemTime::from(FileTime::SIGNED_MAX),
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
    fn try_from_file_time_to_utc_date_time() {
        assert_eq!(
            UtcDateTime::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
            utc_datetime!(1601-01-01 00:00:00)
        );
        assert_eq!(
            UtcDateTime::try_from(FileTime::UNIX_EPOCH).unwrap(),
            UtcDateTime::UNIX_EPOCH
        );
        assert_eq!(
            UtcDateTime::try_from(FileTime::new(2_650_467_743_999_999_999)).unwrap(),
            utc_datetime!(9999-12-31 23:59:59.999_999_900)
        );
    }

    #[cfg(not(feature = "large-dates"))]
    #[test]
    fn try_from_file_time_to_utc_date_time_with_invalid_file_time() {
        assert!(UtcDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).is_err());
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_file_time_to_utc_date_time_with_large_dates() {
        assert_eq!(
            UtcDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).unwrap(),
            utc_datetime!(+10000-01-01 00:00:00)
        );
        assert_eq!(
            UtcDateTime::try_from(FileTime::SIGNED_MAX).unwrap(),
            utc_datetime!(+30828-09-14 02:48:05.477_580_700)
        );
        assert_eq!(
            UtcDateTime::try_from(FileTime::MAX).unwrap(),
            utc_datetime!(+60056-05-28 05:36:10.955_161_500)
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn from_file_time_to_chrono_date_time() {
        assert_eq!(
            chrono::DateTime::from(FileTime::NT_TIME_EPOCH),
            Utc.with_ymd_and_hms(1601, 1, 1, 0, 0, 0).unwrap()
        );
        assert_eq!(
            chrono::DateTime::from(FileTime::UNIX_EPOCH),
            chrono::DateTime::UNIX_EPOCH
        );
        assert_eq!(
            chrono::DateTime::from(FileTime::new(2_650_467_743_999_999_999)),
            Utc.with_ymd_and_hms(9999, 12, 31, 23, 59, 59)
                .unwrap()
                .with_nanosecond(999_999_900)
                .unwrap()
        );
        assert_eq!(
            chrono::DateTime::from(FileTime::new(2_650_467_744_000_000_000)),
            Utc.with_ymd_and_hms(10000, 1, 1, 0, 0, 0).unwrap()
        );
        assert_eq!(
            chrono::DateTime::from(FileTime::SIGNED_MAX),
            Utc.with_ymd_and_hms(30828, 9, 14, 2, 48, 5)
                .unwrap()
                .with_nanosecond(477_580_700)
                .unwrap()
        );
        assert_eq!(
            chrono::DateTime::from(FileTime::MAX),
            Utc.with_ymd_and_hms(60056, 5, 28, 5, 36, 10)
                .unwrap()
                .with_nanosecond(955_161_500)
                .unwrap()
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn try_from_file_time_to_jiff_timestamp() {
        assert_eq!(
            Timestamp::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
            Timestamp::from_second(-11_644_473_600).unwrap()
        );
        assert_eq!(
            Timestamp::try_from(FileTime::UNIX_EPOCH).unwrap(),
            Timestamp::UNIX_EPOCH
        );
        assert_eq!(
            Timestamp::try_from(FileTime::new(2_650_466_808_009_999_999)).unwrap(),
            Timestamp::MAX - 99.nanoseconds()
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn try_from_file_time_to_jiff_timestamp_with_invalid_file_time() {
        assert!(Timestamp::try_from(FileTime::new(2_650_466_808_010_000_000)).is_err());
    }

    #[cfg(feature = "dos-date-time")]
    #[test]
    fn try_from_file_time_to_dos_date_time_before_dos_date_time_epoch() {
        // `1979-12-31 23:59:58 UTC`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(119_600_063_980_000_000)).unwrap_err(),
            DateTimeRangeErrorKind::Negative.into()
        );
        // `1979-12-31 23:59:59 UTC`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(119_600_063_990_000_000)).unwrap_err(),
            DateTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "dos-date-time")]
    #[test]
    fn try_from_file_time_to_dos_date_time() {
        // From `1980-01-01 00:00:00 UTC` to `1980-01-01 00:00:00`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(119_600_064_000_000_000)).unwrap(),
            dos_date_time::DateTime::MIN
        );
        // From `1980-01-01 00:00:01 UTC` to `1980-01-01 00:00:00`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(119_600_064_010_000_000)).unwrap(),
            dos_date_time::DateTime::MIN
        );
        // <https://devblogs.microsoft.com/oldnewthing/20030905-02/?p=42653>.
        //
        // From `2002-11-27 03:25:00 UTC` to `2002-11-27 03:25:00`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(126_828_411_000_000_000)).unwrap(),
            dos_date_time::DateTime::new(
                Date::new(0b0010_1101_0111_1011).unwrap(),
                Time::new(0b0001_1011_0010_0000).unwrap()
            )
        );
        // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
        //
        // From `2018-11-17 10:38:30 UTC` to `2018-11-17 10:38:30`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(131_869_247_100_000_000)).unwrap(),
            dos_date_time::DateTime::new(
                Date::new(0b0100_1101_0111_0001).unwrap(),
                Time::new(0b0101_0100_1100_1111).unwrap()
            )
        );
        // From `2107-12-31 23:59:58 UTC` to `2107-12-31 23:59:58`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(159_992_927_980_000_000)).unwrap(),
            dos_date_time::DateTime::MAX
        );
        // From `2107-12-31 23:59:59 UTC` to `2107-12-31 23:59:58`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(159_992_927_990_000_000)).unwrap(),
            dos_date_time::DateTime::MAX
        );
    }

    #[cfg(feature = "dos-date-time")]
    #[test]
    fn try_from_file_time_to_dos_date_time_with_too_big_date_time() {
        // `2108-01-01 00:00:00 UTC`.
        assert_eq!(
            dos_date_time::DateTime::try_from(FileTime::new(159_992_928_000_000_000)).unwrap_err(),
            DateTimeRangeErrorKind::Overflow.into()
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
    #[proptest]
    fn from_u64_to_file_time_roundtrip(ft: u64) {
        prop_assert_eq!(FileTime::from(ft), FileTime::new(ft));
    }

    #[cfg(feature = "std")]
    #[cfg(not(windows))]
    #[test]
    fn try_from_system_time_to_file_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::try_from(
                SystemTime::UNIX_EPOCH - Duration::from_nanos(11_644_473_600_000_000_001)
            )
            .unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn try_from_system_time_to_file_time() {
        assert_eq!(
            FileTime::try_from(SystemTime::UNIX_EPOCH - FileTime::UNIX_EPOCH.to_duration())
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
            FileTime::try_from(SystemTime::UNIX_EPOCH + Duration::from_hours(70_389_528)).unwrap(),
            FileTime::new(2_650_467_744_000_000_000)
        );
        // Largest `SystemTime` on Windows.
        assert_eq!(
            FileTime::try_from(
                SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700)
            )
            .unwrap(),
            FileTime::SIGNED_MAX
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
        if cfg!(windows) {
            assert!(
                SystemTime::UNIX_EPOCH
                    .checked_add(Duration::new(910_692_730_085, 477_580_800))
                    .is_none()
            );
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
    fn try_from_utc_date_time_to_file_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::try_from(utc_datetime!(1600-12-31 23:59:59.999_999_900)).unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn try_from_utc_date_time_to_file_time() {
        assert_eq!(
            FileTime::try_from(utc_datetime!(1601-01-01 00:00:00)).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::try_from(UtcDateTime::UNIX_EPOCH).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::try_from(utc_datetime!(9999-12-31 23:59:59.999_999_999)).unwrap(),
            FileTime::new(2_650_467_743_999_999_999)
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_utc_date_time_to_file_time_with_large_dates() {
        assert_eq!(
            FileTime::try_from(utc_datetime!(+10000-01-01 00:00:00)).unwrap(),
            FileTime::new(2_650_467_744_000_000_000)
        );
        assert_eq!(
            FileTime::try_from(utc_datetime!(+30828-09-14 02:48:05.477_580_700)).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::try_from(utc_datetime!(+60056-05-28 05:36:10.955_161_500)).unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_utc_date_time_to_file_time_with_too_big_date_time() {
        assert_eq!(
            FileTime::try_from(utc_datetime!(+60056-05-28 05:36:10.955_161_600)).unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn try_from_chrono_date_time_to_file_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::try_from(
                Utc.with_ymd_and_hms(1600, 12, 31, 23, 59, 59)
                    .unwrap()
                    .with_nanosecond(999_999_900)
                    .unwrap()
            )
            .unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn try_from_chrono_date_time_to_file_time() {
        assert_eq!(
            FileTime::try_from(Utc.with_ymd_and_hms(1601, 1, 1, 0, 0, 0).unwrap()).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::try_from(chrono::DateTime::UNIX_EPOCH).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::try_from(
                Utc.with_ymd_and_hms(9999, 12, 31, 23, 59, 59)
                    .unwrap()
                    .with_nanosecond(999_999_900)
                    .unwrap()
            )
            .unwrap(),
            FileTime::new(2_650_467_743_999_999_999)
        );
        assert_eq!(
            FileTime::try_from(Utc.with_ymd_and_hms(10000, 1, 1, 0, 0, 0).unwrap()).unwrap(),
            FileTime::new(2_650_467_744_000_000_000)
        );
        assert_eq!(
            FileTime::try_from(
                Utc.with_ymd_and_hms(30828, 9, 14, 2, 48, 5)
                    .unwrap()
                    .with_nanosecond(477_580_700)
                    .unwrap()
            )
            .unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::try_from(
                Utc.with_ymd_and_hms(60056, 5, 28, 5, 36, 10)
                    .unwrap()
                    .with_nanosecond(955_161_500)
                    .unwrap()
            )
            .unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn try_from_chrono_date_time_to_file_time_with_too_big_date_time() {
        assert_eq!(
            FileTime::try_from(
                Utc.with_ymd_and_hms(60056, 5, 28, 5, 36, 10)
                    .unwrap()
                    .with_nanosecond(955_161_600)
                    .unwrap()
            )
            .unwrap_err(),
            FileTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn try_from_jiff_timestamp_to_file_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::try_from(Timestamp::from_nanosecond(-11_644_473_600_000_000_001).unwrap())
                .unwrap_err(),
            FileTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn try_from_jiff_timestamp_to_file_time() {
        assert_eq!(
            FileTime::try_from(Timestamp::from_second(-11_644_473_600).unwrap()).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::try_from(Timestamp::UNIX_EPOCH).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::try_from(Timestamp::MAX).unwrap(),
            FileTime::new(2_650_466_808_009_999_999)
        );
    }

    #[cfg(feature = "dos-date-time")]
    #[test]
    fn from_dos_date_time_to_file_time() {
        // From `1980-01-01 00:00:00` to `1980-01-01 00:00:00 UTC`.
        assert_eq!(
            FileTime::from(dos_date_time::DateTime::MIN),
            FileTime::new(119_600_064_000_000_000)
        );
        // <https://devblogs.microsoft.com/oldnewthing/20030905-02/?p=42653>.
        //
        // From `2002-11-26 19:25:00` to `2002-11-26 19:25:00 UTC`.
        assert_eq!(
            FileTime::from(dos_date_time::DateTime::new(
                Date::new(0b0010_1101_0111_1010).unwrap(),
                Time::new(0b1001_1011_0010_0000).unwrap()
            )),
            FileTime::new(126_828_123_000_000_000)
        );
        // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
        //
        // From `2018-11-17 10:38:30` to `2018-11-17 10:38:30 UTC`.
        assert_eq!(
            FileTime::from(dos_date_time::DateTime::new(
                Date::new(0b0100_1101_0111_0001).unwrap(),
                Time::new(0b0101_0100_1100_1111).unwrap()
            )),
            FileTime::new(131_869_247_100_000_000)
        );
        // From `2107-12-31 23:59:58` to `2107-12-31 23:59:58 UTC`.
        assert_eq!(
            FileTime::from(dos_date_time::DateTime::MAX),
            FileTime::new(159_992_927_980_000_000)
        );
    }
}
