// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and other types.

use core::num::TryFromIntError;

use time::{macros::datetime, OffsetDateTime};

use crate::error::{FileTimeRangeError, FileTimeRangeErrorKind, OffsetDateTimeRangeError};

use super::{FileTime, FILE_TIMES_PER_SEC};

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
    /// The file time may be represented as an [`i64`] value in [WinRT],[^clock]
    /// [.NET],[^fromfiletime][^tofiletime] etc.
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
    /// assert_eq!(
    ///     i64::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
    ///     i64::default()
    /// );
    /// assert_eq!(
    ///     i64::try_from(FileTime::UNIX_EPOCH).unwrap(),
    ///     116_444_736_000_000_000
    /// );
    ///
    /// assert!(i64::try_from(FileTime::MAX).is_err());
    /// ```
    ///
    /// [^clock]: <https://learn.microsoft.com/en-us/uwp/cpp-ref-for-winrt/clock>
    ///
    /// [^fromfiletime]: <https://learn.microsoft.com/en-us/dotnet/api/system.datetime.fromfiletime>
    ///
    /// [^tofiletime]: <https://learn.microsoft.com/en-us/dotnet/api/system.datetime.tofiletime>
    ///
    /// [WinRT]: https://learn.microsoft.com/en-us/windows/uwp/cpp-and-winrt-apis/
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
    fn from(ft: FileTime) -> Self {
        use std::time::Duration;

        let duration = Duration::new(
            ft.to_raw() / FILE_TIMES_PER_SEC,
            u32::try_from((ft.to_raw() % FILE_TIMES_PER_SEC) * 100)
                .expect("the number of nanoseconds should be in the range of `u32`"),
        );
        (Self::UNIX_EPOCH - (FileTime::UNIX_EPOCH - FileTime::NT_TIME_EPOCH)) + duration
    }
}

impl TryFrom<FileTime> for OffsetDateTime {
    type Error = OffsetDateTimeRangeError;

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
    /// # use nt_time::{time::OffsetDateTime, FileTime};
    /// #
    /// # #[cfg(not(feature = "large-dates"))]
    /// assert!(OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).is_err());
    /// ```
    ///
    /// With the `large-dates` feature enabled, this always succeeds:
    ///
    /// ```
    /// # use nt_time::{
    /// #     time::{macros::datetime, OffsetDateTime},
    /// #     FileTime,
    /// # };
    /// #
    /// # #[cfg(feature = "large-dates")]
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).unwrap(),
    ///     datetime!(+10000-01-01 00:00 UTC)
    /// );
    /// # #[cfg(feature = "large-dates")]
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::MAX).unwrap(),
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
    /// );
    /// ```
    fn try_from(ft: FileTime) -> Result<Self, Self::Error> {
        use time::Duration;

        let duration = Duration::new(
            i64::try_from(ft.to_raw() / FILE_TIMES_PER_SEC)
                .expect("the number of seconds should be in the range of `i64`"),
            i32::try_from((ft.to_raw() % FILE_TIMES_PER_SEC) * 100)
                .expect("the number of nanoseconds should be in the range of `i32`"),
        );
        datetime!(1601-01-01 00:00 UTC)
            .checked_add(duration)
            .ok_or(OffsetDateTimeRangeError)
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
    /// #     chrono::{DateTime, TimeZone, Utc},
    /// #     FileTime,
    /// # };
    /// #
    /// assert_eq!(
    ///     DateTime::<Utc>::from(FileTime::NT_TIME_EPOCH),
    ///     Utc.with_ymd_and_hms(1601, 1, 1, 0, 0, 0).unwrap()
    /// );
    /// assert_eq!(
    ///     DateTime::<Utc>::from(FileTime::UNIX_EPOCH),
    ///     DateTime::<Utc>::UNIX_EPOCH
    /// );
    /// ```
    fn from(ft: FileTime) -> Self {
        use chrono::TimeDelta;

        let duration = TimeDelta::seconds(
            i64::try_from(ft.to_raw() / FILE_TIMES_PER_SEC)
                .expect("the number of seconds should be in the range of `i64`"),
        ) + TimeDelta::nanoseconds(
            i64::try_from((ft.to_raw() % FILE_TIMES_PER_SEC) * 100)
                .expect("the number of nanoseconds should be in the range of `i64`"),
        );
        "1601-01-01 00:00:00 UTC"
            .parse::<Self>()
            .expect("date and time should be valid as RFC 3339")
            + duration
    }
}

#[cfg(feature = "zip")]
impl TryFrom<FileTime> for zip::DateTime {
    type Error = crate::error::DosDateTimeRangeError;

    /// Converts a `FileTime` to a [`zip::DateTime`].
    ///
    /// This method returns the UTC date and time. The resolution of
    /// [`zip::DateTime`] is 2 seconds, so the part of `ft` which is less than 2
    /// seconds is truncated.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `ft` is out of range for [`zip::DateTime`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{zip::DateTime, FileTime};
    /// #
    /// # {
    /// // `1980-01-01 00:00:00 UTC`.
    /// let dt = DateTime::try_from(FileTime::new(119_600_064_000_000_000)).unwrap();
    /// assert_eq!(dt.year(), 1980);
    /// assert_eq!(dt.month(), 1);
    /// assert_eq!(dt.day(), 1);
    /// assert_eq!(dt.hour(), 0);
    /// assert_eq!(dt.minute(), 0);
    /// assert_eq!(dt.second(), 0);
    /// # }
    /// # {
    /// // `2107-12-31 23:59:58 UTC`.
    /// let dt = DateTime::try_from(FileTime::new(159_992_927_980_000_000)).unwrap();
    /// assert_eq!(dt.year(), 2107);
    /// assert_eq!(dt.month(), 12);
    /// assert_eq!(dt.day(), 31);
    /// assert_eq!(dt.hour(), 23);
    /// assert_eq!(dt.minute(), 59);
    /// assert_eq!(dt.second(), 58);
    /// # }
    ///
    /// # {
    /// // `2107-12-31 23:59:59 UTC`.
    /// let dt = DateTime::try_from(FileTime::new(159_992_927_990_000_000)).unwrap();
    /// assert_eq!(dt.year(), 2107);
    /// assert_eq!(dt.month(), 12);
    /// assert_eq!(dt.day(), 31);
    /// assert_eq!(dt.hour(), 23);
    /// assert_eq!(dt.minute(), 59);
    /// assert_eq!(dt.second(), 58);
    /// # }
    ///
    /// // Before `1980-01-01 00:00:00`.
    /// assert!(DateTime::try_from(FileTime::new(119_600_063_990_000_000)).is_err());
    /// // After `2107-12-31 23:59:58`.
    /// assert!(DateTime::try_from(FileTime::new(159_992_928_000_000_000)).is_err());
    /// ```
    fn try_from(ft: FileTime) -> Result<Self, Self::Error> {
        let (date, time, ..) = ft.to_dos_date_time(None)?;
        let dt = Self::try_from_msdos(date, time)
            .expect("date and time should be valid as `zip::DateTime`");
        Ok(dt)
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
    /// The file time may be represented as an [`i64`] value in [WinRT],[^clock]
    /// [.NET],[^fromfiletime][^tofiletime] etc.
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
    /// assert_eq!(
    ///     FileTime::try_from(i64::default()).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(116_444_736_000_000_000_i64).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    ///
    /// assert!(FileTime::try_from(i64::MIN).is_err());
    /// ```
    ///
    /// [^clock]: <https://learn.microsoft.com/en-us/uwp/cpp-ref-for-winrt/clock>
    ///
    /// [^fromfiletime]: <https://learn.microsoft.com/en-us/dotnet/api/system.datetime.fromfiletime>
    ///
    /// [^tofiletime]: <https://learn.microsoft.com/en-us/dotnet/api/system.datetime.tofiletime>
    ///
    /// [WinRT]: https://learn.microsoft.com/en-us/windows/uwp/cpp-and-winrt-apis/
    /// [.NET]: https://dotnet.microsoft.com/
    #[inline]
    fn try_from(ft: i64) -> Result<Self, Self::Error> {
        ft.try_into()
            .map_err(|_| Self::Error::new(FileTimeRangeErrorKind::Negative))
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
    ///
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// #[cfg(not(windows))]
    /// assert!(FileTime::try_from(
    ///     SystemTime::UNIX_EPOCH + Duration::new(1_833_029_933_770, 955_161_600)
    /// )
    /// .is_err());
    /// ```
    fn try_from(st: std::time::SystemTime) -> Result<Self, Self::Error> {
        use std::time::SystemTime;

        let elapsed = st
            .duration_since(SystemTime::UNIX_EPOCH - (Self::UNIX_EPOCH - Self::NT_TIME_EPOCH))
            .map(|d| d.as_nanos())
            .map_err(|_| Self::Error::new(FileTimeRangeErrorKind::Negative))?;
        let ft = u64::try_from(elapsed / 100)
            .map_err(|_| Self::Error::new(FileTimeRangeErrorKind::Overflow))?;
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
    /// assert!(FileTime::try_from(datetime!(1601-01-01 00:00 UTC) - Duration::NANOSECOND).is_err());
    /// ```
    ///
    /// With the `large-dates` feature enabled, returns [`Err`] if
    /// [`OffsetDateTime`] represents after "+60056-05-28 05:36:10.955161500
    /// UTC":
    ///
    /// ```
    /// # use nt_time::{
    /// #     time::{macros::datetime, Duration},
    /// #     FileTime,
    /// # };
    /// #
    /// # #[cfg(feature = "large-dates")]
    /// assert!(FileTime::try_from(
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC) + Duration::nanoseconds(100)
    /// )
    /// .is_err());
    /// ```
    fn try_from(dt: OffsetDateTime) -> Result<Self, Self::Error> {
        use core::time::Duration;

        let elapsed = Duration::try_from(dt - datetime!(1601-01-01 00:00 UTC))
            .map(|d| d.as_nanos())
            .map_err(|_| Self::Error::new(FileTimeRangeErrorKind::Negative))?;
        let ft = u64::try_from(elapsed / 100)
            .map_err(|_| Self::Error::new(FileTimeRangeErrorKind::Overflow))?;
        Ok(Self::new(ft))
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
    /// #     chrono::{DateTime, TimeDelta, TimeZone, Utc},
    /// #     FileTime,
    /// # };
    /// #
    /// assert_eq!(
    ///     FileTime::try_from(Utc.with_ymd_and_hms(1601, 1, 1, 0, 0, 0).unwrap()).unwrap(),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::try_from(DateTime::<Utc>::UNIX_EPOCH).unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    ///
    /// // Before `1601-01-01 00:00:00 UTC`.
    /// assert!(FileTime::try_from(
    ///     Utc.with_ymd_and_hms(1601, 1, 1, 0, 0, 0).unwrap() - TimeDelta::nanoseconds(1)
    /// )
    /// .is_err());
    ///
    /// // After `+60056-05-28 05:36:10.955161500 UTC`.
    /// assert!(FileTime::try_from(
    ///     Utc.with_ymd_and_hms(60056, 5, 28, 5, 36, 10).unwrap()
    ///         + TimeDelta::nanoseconds(955_161_500)
    ///         + TimeDelta::nanoseconds(100)
    /// )
    /// .is_err());
    /// ```
    fn try_from(dt: chrono::DateTime<chrono::Utc>) -> Result<Self, Self::Error> {
        use chrono::{DateTime, Utc};

        let elapsed = (dt
            - "1601-01-01 00:00:00 UTC"
                .parse::<DateTime<Utc>>()
                .expect("date and time should be valid as RFC 3339"))
        .to_std()
        .map(|d| d.as_nanos())
        .map_err(|_| Self::Error::new(FileTimeRangeErrorKind::Negative))?;
        let ft = u64::try_from(elapsed / 100)
            .map_err(|_| Self::Error::new(FileTimeRangeErrorKind::Overflow))?;
        Ok(Self::new(ft))
    }
}

#[cfg(feature = "zip")]
impl From<zip::DateTime> for FileTime {
    /// Converts a [`zip::DateTime`] to a `FileTime`.
    ///
    /// This method assumes `dt` is in UTC.
    ///
    /// # Panics
    ///
    /// Panics if `dt` is an invalid [`zip::DateTime`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{zip::DateTime, FileTime};
    /// #
    /// assert_eq!(
    ///     FileTime::from(DateTime::from_date_and_time(1980, 1, 1, 0, 0, 0).unwrap()),
    ///     FileTime::new(119_600_064_000_000_000)
    /// );
    /// assert_eq!(
    ///     FileTime::from(DateTime::from_date_and_time(2107, 12, 31, 23, 59, 58).unwrap()),
    ///     FileTime::new(159_992_927_980_000_000)
    /// );
    /// ```
    fn from(dt: zip::DateTime) -> Self {
        assert!(dt.is_valid());
        let (date, time) = (dt.datepart(), dt.timepart());
        Self::from_dos_date_time(date, time, None, None)
            .expect("date and time should be valid as `zip::DateTime`")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_file_time_to_u64() {
        assert_eq!(u64::from(FileTime::NT_TIME_EPOCH), u64::MIN);
        assert_eq!(u64::from(FileTime::UNIX_EPOCH), 116_444_736_000_000_000);
        assert_eq!(u64::from(FileTime::MAX), u64::MAX);
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
        assert_eq!(
            i64::try_from(FileTime::new(i64::MAX.try_into().unwrap())).unwrap(),
            i64::MAX
        );
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
        // Maximum `SystemTime` on Windows.
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
        assert_eq!(
            OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).unwrap_err(),
            OffsetDateTimeRangeError
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_file_time_to_offset_date_time_with_large_dates() {
        assert_eq!(
            OffsetDateTime::try_from(FileTime::new(2_650_467_744_000_000_000)).unwrap(),
            datetime!(+10000-01-01 00:00 UTC)
        );
        assert_eq!(
            OffsetDateTime::try_from(FileTime::new(i64::MAX.try_into().unwrap())).unwrap(),
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
            DateTime::<Utc>::from(FileTime::new(i64::MAX.try_into().unwrap())),
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

    #[cfg(feature = "zip")]
    #[test]
    fn try_from_file_time_to_zip_date_time_before_zip_date_time() {
        use zip::DateTime;

        use crate::error::{DosDateTimeRangeError, DosDateTimeRangeErrorKind};

        // `1979-12-31 23:59:58 UTC`.
        assert_eq!(
            DateTime::try_from(FileTime::new(119_600_063_980_000_000)).unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
        // `1979-12-31 23:59:59 UTC`.
        assert_eq!(
            DateTime::try_from(FileTime::new(119_600_063_990_000_000)).unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
    }

    #[cfg(feature = "zip")]
    #[test]
    fn try_from_file_time_to_zip_date_time() {
        use zip::DateTime;

        {
            // `1980-01-01 00:00:00 UTC`.
            let dt = DateTime::try_from(FileTime::new(119_600_064_000_000_000)).unwrap();
            assert_eq!(dt.year(), 1980);
            assert_eq!(dt.month(), 1);
            assert_eq!(dt.day(), 1);
            assert_eq!(dt.hour(), 0);
            assert_eq!(dt.minute(), 0);
            assert_eq!(dt.second(), 0);
        }
        {
            // `1980-01-01 00:00:01 UTC`.
            let dt = DateTime::try_from(FileTime::new(119_600_064_010_000_000)).unwrap();
            assert_eq!(dt.year(), 1980);
            assert_eq!(dt.month(), 1);
            assert_eq!(dt.day(), 1);
            assert_eq!(dt.hour(), 0);
            assert_eq!(dt.minute(), 0);
            assert_eq!(dt.second(), 0);
        }
        {
            // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
            //
            // `2018-11-17 10:38:30 UTC`.
            let dt = DateTime::try_from(FileTime::new(131_869_247_100_000_000)).unwrap();
            assert_eq!(dt.year(), 2018);
            assert_eq!(dt.month(), 11);
            assert_eq!(dt.day(), 17);
            assert_eq!(dt.hour(), 10);
            assert_eq!(dt.minute(), 38);
            assert_eq!(dt.second(), 30);
        }
        {
            // `2107-12-31 23:59:58 UTC`.
            let dt = DateTime::try_from(FileTime::new(159_992_927_980_000_000)).unwrap();
            assert_eq!(dt.year(), 2107);
            assert_eq!(dt.month(), 12);
            assert_eq!(dt.day(), 31);
            assert_eq!(dt.hour(), 23);
            assert_eq!(dt.minute(), 59);
            assert_eq!(dt.second(), 58);
        }
        {
            // `2107-12-31 23:59:59 UTC`.
            let dt = DateTime::try_from(FileTime::new(159_992_927_990_000_000)).unwrap();
            assert_eq!(dt.year(), 2107);
            assert_eq!(dt.month(), 12);
            assert_eq!(dt.day(), 31);
            assert_eq!(dt.hour(), 23);
            assert_eq!(dt.minute(), 59);
            assert_eq!(dt.second(), 58);
        }
    }

    #[cfg(feature = "zip")]
    #[test]
    fn try_from_file_time_to_zip_date_time_after_zip_date_time() {
        use zip::DateTime;

        use crate::error::{DosDateTimeRangeError, DosDateTimeRangeErrorKind};

        // `2108-01-01 00:00:00 UTC`.
        assert_eq!(
            DateTime::try_from(FileTime::new(159_992_928_000_000_000)).unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
        );
    }

    #[test]
    fn from_u64_to_file_time() {
        assert_eq!(FileTime::from(u64::MIN), FileTime::NT_TIME_EPOCH);
        assert_eq!(
            FileTime::from(116_444_736_000_000_000),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(FileTime::from(u64::MAX), FileTime::MAX);
    }

    #[test]
    fn try_from_i64_to_file_time_before_nt_time_epoch() {
        assert_eq!(
            FileTime::try_from(i64::MIN).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            FileTime::try_from(i64::default() - 1).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
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
        assert_eq!(
            FileTime::try_from(i64::MAX).unwrap(),
            FileTime::new(i64::MAX.try_into().unwrap())
        );
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
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
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
        // Maximum `SystemTime` on Windows.
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
                FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
            );
        }
    }

    #[test]
    fn try_from_offset_date_time_to_file_time_before_nt_time_epoch() {
        use time::Duration;

        assert_eq!(
            FileTime::try_from(datetime!(1601-01-01 00:00 UTC) - Duration::NANOSECOND).unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
    }

    #[test]
    fn try_from_offset_date_time_to_file_time() {
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
        assert_eq!(
            FileTime::try_from(datetime!(+10000-01-01 00:00 UTC)).unwrap(),
            FileTime::new(2_650_467_744_000_000_000)
        );
        assert_eq!(
            FileTime::try_from(datetime!(+30828-09-14 02:48:05.477_580_700 UTC)).unwrap(),
            FileTime::new(i64::MAX.try_into().unwrap())
        );
        assert_eq!(
            FileTime::try_from(datetime!(+60056-05-28 05:36:10.955_161_500 UTC)).unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_offset_date_time_to_file_time_with_too_big_date_time() {
        use time::Duration;

        assert_eq!(
            FileTime::try_from(
                datetime!(+60056-05-28 05:36:10.955_161_500 UTC) + Duration::nanoseconds(100)
            )
            .unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn try_from_chrono_date_time_to_file_time_before_nt_time_epoch() {
        use chrono::{DateTime, TimeDelta, Utc};

        assert_eq!(
            FileTime::try_from(
                "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()
                    - TimeDelta::nanoseconds(1)
            )
            .unwrap_err(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
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
            FileTime::new(i64::MAX.try_into().unwrap())
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
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
    }

    #[cfg(feature = "zip")]
    #[test]
    fn from_zip_date_time_to_file_time() {
        use zip::DateTime;

        {
            let dt = DateTime::from_date_and_time(1980, 1, 1, 0, 0, 0).unwrap();
            assert_eq!(FileTime::from(dt), FileTime::new(119_600_064_000_000_000));
        }
        {
            let dt = DateTime::from_date_and_time(1980, 1, 1, 0, 0, 1).unwrap();
            assert_eq!(FileTime::from(dt), FileTime::new(119_600_064_000_000_000));
        }
        {
            // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
            let dt = DateTime::from_date_and_time(2018, 11, 17, 10, 38, 30).unwrap();
            assert_eq!(FileTime::from(dt), FileTime::new(131_869_247_100_000_000));
        }
        {
            let dt = DateTime::from_date_and_time(2107, 12, 31, 23, 59, 58).unwrap();
            assert_eq!(FileTime::from(dt), FileTime::new(159_992_927_980_000_000));
        }
        {
            let dt = DateTime::from_date_and_time(2107, 12, 31, 23, 59, 59).unwrap();
            assert_eq!(FileTime::from(dt), FileTime::new(159_992_927_980_000_000));
        }
    }
}
