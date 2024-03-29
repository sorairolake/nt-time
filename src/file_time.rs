// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A [Windows file time].
//!
//! [Windows file time]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times

use core::{
    cmp::Ordering,
    fmt, mem,
    num::TryFromIntError,
    ops::{Add, AddAssign, Sub, SubAssign},
    str::FromStr,
};

use time::{
    error::ComponentRange,
    macros::{datetime, offset},
    Date, OffsetDateTime, Time, UtcOffset,
};

use crate::error::{
    DosDateTimeRangeError, DosDateTimeRangeErrorKind, FileTimeRangeError, FileTimeRangeErrorKind,
    OffsetDateTimeRangeError, ParseFileTimeError,
};

const FILE_TIMES_PER_SEC: u64 = 10_000_000;

/// `FileTime` is a type that represents a [Windows file time].
///
/// This is a 64-bit unsigned integer value that represents the number of
/// 100-nanosecond intervals that have elapsed since "1601-01-01 00:00:00 UTC",
/// and is used as timestamps such as [NTFS] and [7z].
///
/// This represents the same value as the [`FILETIME`] structure of the [Win32
/// API], which represents a 64-bit unsigned integer value. Note that the
/// maximum value of the `FILETIME` structure that can be input to the
/// [`FileTimeToSystemTime`] function of the Win32 API is limited to
/// "+30828-09-14 02:48:05.477580700 UTC", which is equivalent to [`i64::MAX`].
///
/// [Windows file time]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
/// [NTFS]: https://en.wikipedia.org/wiki/NTFS
/// [7z]: https://www.7-zip.org/7z.html
/// [`FILETIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-filetime
/// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
/// [`FileTimeToSystemTime`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-filetimetosystemtime
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileTime(u64);

impl FileTime {
    /// The [NT time epoch].
    ///
    /// This is defined as "1601-01-01 00:00:00 UTC".
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
    /// ```
    ///
    /// [NT time epoch]: https://en.wikipedia.org/wiki/Epoch_(computing)
    pub const NT_TIME_EPOCH: Self = Self::new(u64::MIN);

    /// The [Unix epoch].
    ///
    /// This is defined as "1970-01-01 00:00:00 UTC".
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{time::OffsetDateTime, FileTime};
    /// #
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::UNIX_EPOCH).unwrap(),
    ///     OffsetDateTime::UNIX_EPOCH
    /// );
    /// ```
    ///
    /// [Unix epoch]: https://en.wikipedia.org/wiki/Unix_time
    pub const UNIX_EPOCH: Self = Self::new(134_774 * 86400 * FILE_TIMES_PER_SEC);

    /// The largest value that can be represented by the file time.
    ///
    /// This is "+60056-05-28 05:36:10.955161500 UTC".
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{
    /// #     time::{macros::datetime, OffsetDateTime},
    /// #     FileTime,
    /// # };
    /// #
    /// # #[cfg(feature = "large-dates")]
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::MAX).unwrap(),
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
    /// );
    /// ```
    pub const MAX: Self = Self::new(u64::MAX);

    /// Returns the file time corresponding to "now".
    ///
    /// # Panics
    ///
    /// Panics if "now" is out of range for the file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// let now = FileTime::now();
    /// ```
    #[cfg(feature = "std")]
    #[must_use]
    pub fn now() -> Self {
        use std::time::SystemTime;

        SystemTime::now()
            .try_into()
            .expect("the current date and time should be in the range of the file time")
    }

    /// Creates a new `FileTime` with the given file time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::new(u64::MIN), FileTime::NT_TIME_EPOCH);
    /// assert_eq!(FileTime::new(116_444_736_000_000_000), FileTime::UNIX_EPOCH);
    /// assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn new(ft: u64) -> Self {
        Self(ft)
    }

    /// Returns the contents of this `FileTime` as the underlying [`u64`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_raw(), u64::MIN);
    /// assert_eq!(FileTime::UNIX_EPOCH.to_raw(), 116_444_736_000_000_000);
    /// assert_eq!(FileTime::MAX.to_raw(), u64::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn to_raw(self) -> u64 {
        self.0
    }

    /// Returns the contents of this `FileTime` as the underlying [`u64`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.as_u64(), u64::MIN);
    /// assert_eq!(FileTime::UNIX_EPOCH.as_u64(), 116_444_736_000_000_000);
    /// assert_eq!(FileTime::MAX.as_u64(), u64::MAX);
    /// ```
    #[deprecated(since = "0.5.0", note = "use `FileTime::to_raw` instead")]
    #[must_use]
    #[inline]
    pub const fn as_u64(self) -> u64 {
        self.to_raw()
    }

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

    /// Returns [MS-DOS date and time] which represents the same date and time
    /// as this `FileTime`. This date and time is used as the timestamp such as
    /// [FAT], [exFAT] or [ZIP] file format.
    ///
    /// This method returns a `(date, time, resolution, offset)` tuple.
    ///
    /// `date` and `time` represents the local date and time. This date and time
    /// has no notion of time zone. The resolution of MS-DOS date and time is 2
    /// seconds, but additional [finer resolution] (10 ms units) can be
    /// provided. `resolution` represents this additional finer resolution.
    ///
    /// When the `offset` parameter is [`Some`], converts `date` and `time` from
    /// UTC to the local date and time with the provided [UTC offset] and
    /// returns it with the UTC offset. When the `offset` parameter is [`None`]
    /// or is not a multiple of 15 minute intervals, consider UTC to be the
    /// local date and time and returns [`None`] as the UTC offset.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the resulting date and time is out of range for
    /// MS-DOS date and time.
    ///
    /// # Panics
    ///
    /// Panics if `offset` is not in the range "UTC-16:00" to
    /// "UTC+15:45".[^offsetfromutc-field]
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{time::macros::offset, FileTime};
    /// #
    /// // `1980-01-01 00:00:00 UTC`.
    /// assert_eq!(
    ///     FileTime::new(119_600_064_000_000_000)
    ///         .to_dos_date_time(None)
    ///         .unwrap(),
    ///     (0x0021, u16::MIN, u8::MIN, None)
    /// );
    /// // `2107-12-31 23:59:59 UTC`.
    /// assert_eq!(
    ///     FileTime::new(159_992_927_990_000_000)
    ///         .to_dos_date_time(None)
    ///         .unwrap(),
    ///     (0xff9f, 0xbf7d, 100, None)
    /// );
    ///
    /// // Before `1980-01-01 00:00:00 UTC`.
    /// assert!(FileTime::new(119_600_063_990_000_000)
    ///     .to_dos_date_time(None)
    ///     .is_err());
    /// // After `2107-12-31 23:59:59.990000000 UTC`.
    /// assert!(FileTime::new(159_992_928_000_000_000)
    ///     .to_dos_date_time(None)
    ///     .is_err());
    ///
    /// // From `2002-11-27 03:25:00 UTC` to `2002-11-26 19:25:00 -08:00`.
    /// assert_eq!(
    ///     FileTime::new(126_828_411_000_000_000)
    ///         .to_dos_date_time(Some(offset!(-08:00)))
    ///         .unwrap(),
    ///     (0x2d7a, 0x9b20, u8::MIN, Some(offset!(-08:00)))
    /// );
    /// ```
    ///
    /// When the UTC offset is not a multiple of 15 minute intervals, consider
    /// UTC to be the local date and time:
    ///
    /// ```
    /// # use nt_time::{time::macros::offset, FileTime};
    /// #
    /// // `2002-11-27 03:25:00 UTC`.
    /// assert_eq!(
    ///     FileTime::new(126_828_411_000_000_000)
    ///         .to_dos_date_time(Some(offset!(-08:01)))
    ///         .unwrap(),
    ///     (0x2d7b, 0x1b20, u8::MIN, None)
    /// );
    /// // `2002-11-27 03:25:00 UTC`.
    /// assert_eq!(
    ///     FileTime::new(126_828_411_000_000_000)
    ///         .to_dos_date_time(Some(offset!(-08:14)))
    ///         .unwrap(),
    ///     (0x2d7b, 0x1b20, u8::MIN, None)
    /// );
    ///
    /// // From `2002-11-27 03:25:00 UTC` to `2002-11-26 19:10:00 -08:15`.
    /// assert_eq!(
    ///     FileTime::new(126_828_411_000_000_000)
    ///         .to_dos_date_time(Some(offset!(-08:15)))
    ///         .unwrap(),
    ///     (0x2d7a, 0x9940, u8::MIN, Some(offset!(-08:15)))
    /// );
    /// ```
    ///
    /// [^offsetfromutc-field]: <https://learn.microsoft.com/en-us/windows/win32/fileio/exfat-specification#74101-offsetfromutc-field>
    ///
    /// [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time
    /// [FAT]: https://en.wikipedia.org/wiki/File_Allocation_Table
    /// [exFAT]: https://en.wikipedia.org/wiki/ExFAT
    /// [ZIP]: https://en.wikipedia.org/wiki/ZIP_(file_format)
    /// [finer resolution]: https://learn.microsoft.com/en-us/windows/win32/fileio/exfat-specification#749-10msincrement-fields
    /// [UTC offset]: https://learn.microsoft.com/en-us/windows/win32/fileio/exfat-specification#7410-utcoffset-fields
    pub fn to_dos_date_time(
        self,
        offset: Option<UtcOffset>,
    ) -> Result<(u16, u16, u8, Option<UtcOffset>), DosDateTimeRangeError> {
        let offset = offset.filter(|o| o.whole_seconds() % 900 == 0);
        if let Some(o) = offset {
            // The UTC offset must be in the range of a 7-bit signed integer.
            assert!((offset!(-16:00)..=offset!(+15:45)).contains(&o));
        }
        let dt = OffsetDateTime::try_from(self)
            .ok()
            .and_then(|dt| dt.checked_to_offset(offset.unwrap_or(UtcOffset::UTC)))
            .ok_or_else(|| DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow))?;
        match dt.year() {
            ..=1979 => Err(DosDateTimeRangeError::new(
                DosDateTimeRangeErrorKind::Negative,
            )),
            2108.. => Err(DosDateTimeRangeError::new(
                DosDateTimeRangeErrorKind::Overflow,
            )),
            _ => {
                let (date, time) = (dt.date(), dt.time());

                let (second, minute, hour) = (time.second() / 2, time.minute(), time.hour());
                let resolution = ((time
                    - Time::from_hms(hour, minute, second * 2)
                        .expect("the MS-DOS time should be in the range of `Time`"))
                .whole_milliseconds()
                    / 10)
                    .try_into()
                    .expect("resolution should be in the range of `u8`");
                debug_assert!(resolution <= 199);
                let (second, minute, hour) =
                    (u16::from(second), u16::from(minute), u16::from(hour));
                let dos_time = second + (minute << 5) + (hour << 11);

                let (day, month, year) = (
                    i32::from(date.day()),
                    i32::from(u8::from(date.month())),
                    date.year() - 1980,
                );
                let dos_date = (day + (month << 5) + (year << 9))
                    .try_into()
                    .expect("the MS-DOS date should be in the range of `u16`");

                Ok((dos_date, dos_time, resolution, offset))
            }
        }
    }

    /// Creates a `FileTime` with the given [MS-DOS date and time]. This date
    /// and time is used as the timestamp such as [FAT], [exFAT] or [ZIP] file
    /// format.
    ///
    /// When `resolution` is [`Some`], additional [finer resolution] (10 ms
    /// units) is added to `time`.
    ///
    /// When `offset` is [`Some`], converts `date` and `time` from the local
    /// date and time with the provided [UTC offset] to UTC. When `offset` is
    /// [`None`] or is not a multiple of 15 minute intervals, consider UTC to be
    /// the local date and time.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `date` or `time` is an invalid date and time.
    ///
    /// # Panics
    ///
    /// Panics if any of the following are true:
    ///
    /// - `resolution` is greater than 199.
    /// - `offset` is not in the range "UTC-16:00" to
    ///   "UTC+15:45".[^offsetfromutc-field]
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{time::macros::offset, FileTime};
    /// #
    /// // `1980-01-01 00:00:00 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0x0021, u16::MIN, None, None).unwrap(),
    ///     FileTime::new(119_600_064_000_000_000)
    /// );
    /// // `2107-12-31 23:59:59 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0xff9f, 0xbf7d, Some(100), None).unwrap(),
    ///     FileTime::new(159_992_927_990_000_000)
    /// );
    ///
    /// // From `2002-11-26 19:25:00 -08:00` to `2002-11-27 03:25:00 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:00))).unwrap(),
    ///     FileTime::new(126_828_411_000_000_000)
    /// );
    ///
    /// // The Day field is 0.
    /// assert!(FileTime::from_dos_date_time(0x0020, u16::MIN, None, None).is_err());
    /// // The DoubleSeconds field is 30.
    /// assert!(FileTime::from_dos_date_time(0x0021, 0x001e, None, None).is_err());
    /// ```
    ///
    /// When the UTC offset is not a multiple of 15 minute intervals, consider
    /// UTC to be the local date and time:
    ///
    /// ```
    /// # use nt_time::{time::macros::offset, FileTime};
    /// #
    /// // From `2002-11-26 19:25:00 -08:01` to `2002-11-26 19:25:00 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:01))).unwrap(),
    ///     FileTime::new(126_828_123_000_000_000)
    /// );
    /// // From `2002-11-26 19:25:00 -08:14` to `2002-11-26 19:25:00 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:14))).unwrap(),
    ///     FileTime::new(126_828_123_000_000_000)
    /// );
    ///
    /// // From `2002-11-26 19:25:00 -08:15` to `2002-11-27 03:40:00 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:15))).unwrap(),
    ///     FileTime::new(126_828_420_000_000_000)
    /// );
    /// ```
    ///
    /// Additional finer resolution must be in the range 0 to 199:
    ///
    /// ```should_panic
    /// # use nt_time::FileTime;
    /// #
    /// let _: FileTime = FileTime::from_dos_date_time(0x0021, u16::MIN, Some(200), None).unwrap();
    /// ```
    ///
    /// [^offsetfromutc-field]: <https://learn.microsoft.com/en-us/windows/win32/fileio/exfat-specification#74101-offsetfromutc-field>
    ///
    /// [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time
    /// [FAT]: https://en.wikipedia.org/wiki/File_Allocation_Table
    /// [exFAT]: https://en.wikipedia.org/wiki/ExFAT
    /// [ZIP]: https://en.wikipedia.org/wiki/ZIP_(file_format)
    /// [finer resolution]: https://learn.microsoft.com/en-us/windows/win32/fileio/exfat-specification#749-10msincrement-fields
    /// [UTC offset]: https://learn.microsoft.com/en-us/windows/win32/fileio/exfat-specification#7410-utcoffset-fields
    pub fn from_dos_date_time(
        date: u16,
        time: u16,
        resolution: Option<u8>,
        offset: Option<UtcOffset>,
    ) -> Result<Self, ComponentRange> {
        use core::time::Duration;

        let (second, minute, hour) = (
            ((time & 0x1f) * 2)
                .try_into()
                .expect("second should be in the range of `u8`"),
            ((time >> 5) & 0x3f)
                .try_into()
                .expect("minute should be in the range of `u8`"),
            (time >> 11)
                .try_into()
                .expect("hour should be in the range of `u8`"),
        );
        let mut time = Time::from_hms(hour, minute, second)?;
        if let Some(res) = resolution {
            assert!(res <= 199);
            time += Duration::from_millis(u64::from(res) * 10);
        }

        let (day, month, year) = (
            (date & 0x1f)
                .try_into()
                .expect("day should be in the range of `u8`"),
            u8::try_from((date >> 5) & 0x0f)
                .expect("month should be in the range of `u8`")
                .try_into()?,
            ((date >> 9) + 1980).into(),
        );
        let date = Date::from_calendar_date(year, month, day)?;

        let offset = offset.filter(|o| o.whole_seconds() % 900 == 0);
        if let Some(o) = offset {
            // The UTC offset must be in the range of a 7-bit signed integer.
            assert!((offset!(-16:00)..=offset!(+15:45)).contains(&o));
        }
        let ft = OffsetDateTime::new_in_offset(date, time, offset.unwrap_or(UtcOffset::UTC))
            .try_into()
            .expect("MS-DOS date and time should be in the range of `FileTime`");
        Ok(ft)
    }

    /// Computes `self + rhs`, returning [`None`] if overflow occurred. The part
    /// of `rhs` less than 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(1)),
    ///     Some(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(100)),
    ///     Some(FileTime::new(1))
    /// );
    ///
    /// assert_eq!(FileTime::MAX.checked_add(Duration::from_nanos(100)), None);
    /// ```
    #[must_use]
    #[inline]
    pub fn checked_add(self, rhs: core::time::Duration) -> Option<Self> {
        let duration = u64::try_from(rhs.as_nanos() / 100).ok()?;
        self.to_raw().checked_add(duration).map(Self::new)
    }

    /// Computes `self - rhs`, returning [`None`] if the result would be
    /// negative or if overflow occurred. The part of `rhs` less than
    /// 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::MAX.checked_sub(Duration::from_nanos(1)),
    ///     Some(FileTime::MAX)
    /// );
    /// assert_eq!(
    ///     FileTime::MAX.checked_sub(Duration::from_nanos(100)),
    ///     Some(FileTime::new(u64::MAX - 1))
    /// );
    ///
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(100)),
    ///     None
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub fn checked_sub(self, rhs: core::time::Duration) -> Option<Self> {
        let duration = u64::try_from(rhs.as_nanos() / 100).ok()?;
        self.to_raw().checked_sub(duration).map(Self::new)
    }

    /// Computes `self + rhs`, returning [`FileTime::MAX`] if overflow occurred.
    /// The part of `rhs` less than 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(1)),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(100)),
    ///     FileTime::new(1)
    /// );
    ///
    /// assert_eq!(
    ///     FileTime::MAX.saturating_add(Duration::from_nanos(100)),
    ///     FileTime::MAX
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub fn saturating_add(self, rhs: core::time::Duration) -> Self {
        self.checked_add(rhs).unwrap_or(Self::MAX)
    }

    /// Computes `self - rhs`, returning [`FileTime::NT_TIME_EPOCH`] if the
    /// result would be negative or if overflow occurred. The part of `rhs` less
    /// than 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::MAX.saturating_sub(Duration::from_nanos(1)),
    ///     FileTime::MAX
    /// );
    /// assert_eq!(
    ///     FileTime::MAX.saturating_sub(Duration::from_nanos(100)),
    ///     FileTime::new(u64::MAX - 1)
    /// );
    ///
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(100)),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub fn saturating_sub(self, rhs: core::time::Duration) -> Self {
        self.checked_sub(rhs).unwrap_or_default()
    }

    /// Returns the memory representation of this `FileTime` as a byte array in
    /// big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_be_bytes(), [u8::MIN; 8]);
    /// assert_eq!(
    ///     FileTime::UNIX_EPOCH.to_be_bytes(),
    ///     [0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]
    /// );
    /// assert_eq!(FileTime::MAX.to_be_bytes(), [u8::MAX; 8]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn to_be_bytes(self) -> [u8; mem::size_of::<Self>()] {
        self.to_raw().to_be_bytes()
    }

    /// Returns the memory representation of this `FileTime` as a byte array in
    /// little-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_le_bytes(), [u8::MIN; 8]);
    /// assert_eq!(
    ///     FileTime::UNIX_EPOCH.to_le_bytes(),
    ///     [0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]
    /// );
    /// assert_eq!(FileTime::MAX.to_le_bytes(), [u8::MAX; 8]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn to_le_bytes(self) -> [u8; mem::size_of::<Self>()] {
        self.to_raw().to_le_bytes()
    }

    /// Creates a native endian `FileTime` value from its representation as a
    /// byte array in big-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_be_bytes([u8::MIN; 8]),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_be_bytes([0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(FileTime::from_be_bytes([u8::MAX; 8]), FileTime::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn from_be_bytes(bytes: [u8; mem::size_of::<Self>()]) -> Self {
        Self::new(u64::from_be_bytes(bytes))
    }

    /// Creates a native endian `FileTime` value from its representation as a
    /// byte array in little-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_le_bytes([u8::MIN; 8]),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_le_bytes([0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(FileTime::from_le_bytes([u8::MAX; 8]), FileTime::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn from_le_bytes(bytes: [u8; mem::size_of::<Self>()]) -> Self {
        Self::new(u64::from_le_bytes(bytes))
    }
}

impl Default for FileTime {
    /// Returns the default value of "1601-01-01 00:00:00 UTC".
    ///
    /// Equivalent to [`FileTime::NT_TIME_EPOCH`] except that it is not callable
    /// in const contexts.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::default(), FileTime::NT_TIME_EPOCH);
    /// ```
    #[inline]
    fn default() -> Self {
        Self::NT_TIME_EPOCH
    }
}

impl fmt::Display for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{}", FileTime::NT_TIME_EPOCH), "0");
    /// assert_eq!(format!("{}", FileTime::UNIX_EPOCH), "116444736000000000");
    /// assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::Octal for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#o}", FileTime::NT_TIME_EPOCH), "0o0");
    /// assert_eq!(
    ///     format!("{:022o}", FileTime::UNIX_EPOCH),
    ///     "0006355435732517500000"
    /// );
    /// assert_eq!(format!("{:o}", FileTime::MAX), "1777777777777777777777");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::LowerHex for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#x}", FileTime::NT_TIME_EPOCH), "0x0");
    /// assert_eq!(format!("{:016x}", FileTime::UNIX_EPOCH), "019db1ded53e8000");
    /// assert_eq!(format!("{:x}", FileTime::MAX), "ffffffffffffffff");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::UpperHex for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#X}", FileTime::NT_TIME_EPOCH), "0x0");
    /// assert_eq!(format!("{:016X}", FileTime::UNIX_EPOCH), "019DB1DED53E8000");
    /// assert_eq!(format!("{:X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::Binary for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#b}", FileTime::NT_TIME_EPOCH), "0b0");
    /// assert_eq!(
    ///     format!("{:064b}", FileTime::UNIX_EPOCH),
    ///     "0000000110011101101100011101111011010101001111101000000000000000"
    /// );
    /// assert_eq!(
    ///     format!("{:b}", FileTime::MAX),
    ///     "1111111111111111111111111111111111111111111111111111111111111111"
    /// );
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::LowerExp for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     format!("{:024e}", FileTime::NT_TIME_EPOCH),
    ///     "0000000000000000000000e0"
    /// );
    /// assert_eq!(format!("{:e}", FileTime::UNIX_EPOCH), "1.16444736e17");
    /// assert_eq!(format!("{:e}", FileTime::MAX), "1.8446744073709551615e19");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::UpperExp for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     format!("{:024E}", FileTime::NT_TIME_EPOCH),
    ///     "0000000000000000000000E0"
    /// );
    /// assert_eq!(format!("{:E}", FileTime::UNIX_EPOCH), "1.16444736E17");
    /// assert_eq!(format!("{:E}", FileTime::MAX), "1.8446744073709551615E19");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

#[cfg(feature = "std")]
impl PartialEq<FileTime> for std::time::SystemTime {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        self == &Self::from(*other)
    }
}

#[cfg(feature = "std")]
impl PartialEq<std::time::SystemTime> for FileTime {
    #[inline]
    fn eq(&self, other: &std::time::SystemTime) -> bool {
        use std::time::SystemTime;

        &SystemTime::from(*self) == other
    }
}

impl PartialEq<FileTime> for OffsetDateTime {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        self == &Self::try_from(*other).expect("`other` is out of range for `OffsetDateTime`")
    }
}

impl PartialEq<OffsetDateTime> for FileTime {
    #[inline]
    fn eq(&self, other: &OffsetDateTime) -> bool {
        &OffsetDateTime::try_from(*self).expect("`self` is out of range for `OffsetDateTime`")
            == other
    }
}

#[cfg(feature = "chrono")]
impl PartialEq<FileTime> for chrono::DateTime<chrono::Utc> {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        self == &Self::from(*other)
    }
}

#[cfg(feature = "chrono")]
impl PartialEq<chrono::DateTime<chrono::Utc>> for FileTime {
    #[inline]
    fn eq(&self, other: &chrono::DateTime<chrono::Utc>) -> bool {
        use chrono::{DateTime, Utc};

        &DateTime::<Utc>::from(*self) == other
    }
}

#[cfg(feature = "std")]
impl PartialOrd<FileTime> for std::time::SystemTime {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        self.partial_cmp(&Self::from(*other))
    }
}

#[cfg(feature = "std")]
impl PartialOrd<std::time::SystemTime> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &std::time::SystemTime) -> Option<Ordering> {
        use std::time::SystemTime;

        SystemTime::from(*self).partial_cmp(other)
    }
}

impl PartialOrd<FileTime> for OffsetDateTime {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        self.partial_cmp(
            &Self::try_from(*other).expect("`other` is out of range for `OffsetDateTime`"),
        )
    }
}

impl PartialOrd<OffsetDateTime> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &OffsetDateTime) -> Option<Ordering> {
        OffsetDateTime::try_from(*self)
            .expect("`self` is out of range for `OffsetDateTime`")
            .partial_cmp(other)
    }
}

#[cfg(feature = "chrono")]
impl PartialOrd<FileTime> for chrono::DateTime<chrono::Utc> {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        self.partial_cmp(&Self::from(*other))
    }
}

#[cfg(feature = "chrono")]
impl PartialOrd<chrono::DateTime<chrono::Utc>> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &chrono::DateTime<chrono::Utc>) -> Option<Ordering> {
        use chrono::{DateTime, Utc};

        DateTime::<Utc>::from(*self).partial_cmp(other)
    }
}

impl Add<core::time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn add(self, rhs: core::time::Duration) -> Self::Output {
        self.checked_add(rhs)
            .expect("overflow when adding duration to date and time")
    }
}

impl Add<time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn add(self, rhs: time::Duration) -> Self::Output {
        if rhs.is_positive() {
            self + rhs.unsigned_abs()
        } else {
            self - rhs.unsigned_abs()
        }
    }
}

#[cfg(feature = "chrono")]
impl Add<chrono::TimeDelta> for FileTime {
    type Output = Self;

    #[inline]
    fn add(self, rhs: chrono::TimeDelta) -> Self::Output {
        use chrono::TimeDelta;

        if rhs > TimeDelta::zero() {
            self + rhs.abs().to_std().expect("duration is less than zero")
        } else {
            self - rhs.abs().to_std().expect("duration is less than zero")
        }
    }
}

impl AddAssign<core::time::Duration> for FileTime {
    #[inline]
    fn add_assign(&mut self, rhs: core::time::Duration) {
        *self = *self + rhs;
    }
}

impl AddAssign<time::Duration> for FileTime {
    #[inline]
    fn add_assign(&mut self, rhs: time::Duration) {
        *self = *self + rhs;
    }
}

#[cfg(feature = "chrono")]
impl AddAssign<chrono::TimeDelta> for FileTime {
    #[inline]
    fn add_assign(&mut self, rhs: chrono::TimeDelta) {
        *self = *self + rhs;
    }
}

impl Sub for FileTime {
    type Output = core::time::Duration;

    fn sub(self, rhs: Self) -> Self::Output {
        let duration = self.to_raw() - rhs.to_raw();
        Self::Output::new(
            duration / FILE_TIMES_PER_SEC,
            u32::try_from((duration % FILE_TIMES_PER_SEC) * 100)
                .expect("the number of nanoseconds should be in the range of `u32`"),
        )
    }
}

impl Sub<core::time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: core::time::Duration) -> Self::Output {
        self.checked_sub(rhs)
            .expect("overflow when subtracting duration from date and time")
    }
}

impl Sub<time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: time::Duration) -> Self::Output {
        if rhs.is_positive() {
            self - rhs.unsigned_abs()
        } else {
            self + rhs.unsigned_abs()
        }
    }
}

#[cfg(feature = "chrono")]
impl Sub<chrono::TimeDelta> for FileTime {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: chrono::TimeDelta) -> Self::Output {
        use chrono::TimeDelta;

        if rhs > TimeDelta::zero() {
            self - rhs.abs().to_std().expect("duration is less than zero")
        } else {
            self + rhs.abs().to_std().expect("duration is less than zero")
        }
    }
}

#[cfg(feature = "std")]
impl Sub<FileTime> for std::time::SystemTime {
    type Output = std::time::Duration;

    #[inline]
    fn sub(self, rhs: FileTime) -> Self::Output {
        self.duration_since(rhs.into())
            .expect("RHS provided is later than LHS")
    }
}

#[cfg(feature = "std")]
impl Sub<std::time::SystemTime> for FileTime {
    type Output = std::time::Duration;

    #[inline]
    fn sub(self, rhs: std::time::SystemTime) -> Self::Output {
        use std::time::SystemTime;

        SystemTime::from(self)
            .duration_since(rhs)
            .expect("RHS provided is later than LHS")
    }
}

impl Sub<FileTime> for OffsetDateTime {
    type Output = time::Duration;

    #[inline]
    fn sub(self, rhs: FileTime) -> Self::Output {
        self - Self::try_from(rhs).expect("RHS is out of range for `OffsetDateTime`")
    }
}

impl Sub<OffsetDateTime> for FileTime {
    type Output = time::Duration;

    #[inline]
    fn sub(self, rhs: OffsetDateTime) -> Self::Output {
        OffsetDateTime::try_from(self).expect("LHS is out of range for `OffsetDateTime`") - rhs
    }
}

#[cfg(feature = "chrono")]
impl Sub<FileTime> for chrono::DateTime<chrono::Utc> {
    type Output = chrono::TimeDelta;

    #[inline]
    fn sub(self, rhs: FileTime) -> Self::Output {
        self - Self::from(rhs)
    }
}

#[cfg(feature = "chrono")]
impl Sub<chrono::DateTime<chrono::Utc>> for FileTime {
    type Output = chrono::TimeDelta;

    #[inline]
    fn sub(self, rhs: chrono::DateTime<chrono::Utc>) -> Self::Output {
        use chrono::{DateTime, Utc};

        DateTime::<Utc>::from(self) - rhs
    }
}

impl SubAssign<core::time::Duration> for FileTime {
    #[inline]
    fn sub_assign(&mut self, rhs: core::time::Duration) {
        *self = *self - rhs;
    }
}

impl SubAssign<time::Duration> for FileTime {
    #[inline]
    fn sub_assign(&mut self, rhs: time::Duration) {
        *self = *self - rhs;
    }
}

#[cfg(feature = "chrono")]
impl SubAssign<chrono::TimeDelta> for FileTime {
    #[inline]
    fn sub_assign(&mut self, rhs: chrono::TimeDelta) {
        *self = *self - rhs;
    }
}

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

        let duration = TimeDelta::try_seconds(
            i64::try_from(ft.to_raw() / FILE_TIMES_PER_SEC)
                .expect("the number of seconds should be in the range of `i64`"),
        )
        .expect("the number of seconds should be in the range of `TimeDelta`")
            + TimeDelta::nanoseconds(
                i64::try_from((ft.to_raw() % FILE_TIMES_PER_SEC) * 100)
                    .expect("the number of nanoseconds should be in the range of `i64`"),
            );
        "1601-01-01 00:00:00 UTC"
            .parse::<Self>()
            .expect("date and time should be valid as RFC 3339")
            + duration
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

impl FromStr for FileTime {
    type Err = ParseFileTimeError;

    /// Parses a string `s` to return a value of `FileTime`.
    ///
    /// The string is expected to be a decimal non-negative integer. If the
    /// string is not a decimal integer, use [`u64::from_str_radix`] and
    /// [`FileTime::new`] instead.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if [`u64::from_str`] returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::str::FromStr;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::from_str("0").unwrap(), FileTime::NT_TIME_EPOCH);
    /// assert_eq!(
    ///     FileTime::from_str("116444736000000000").unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_str("+18446744073709551615").unwrap(),
    ///     FileTime::MAX
    /// );
    ///
    /// assert!(FileTime::from_str("").is_err());
    ///
    /// assert!(FileTime::from_str("a").is_err());
    /// assert!(FileTime::from_str("-1").is_err());
    /// assert!(FileTime::from_str("+").is_err());
    /// assert!(FileTime::from_str("0 ").is_err());
    ///
    /// assert!(FileTime::from_str("18446744073709551616").is_err());
    /// ```
    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map_err(ParseFileTimeError::new).map(Self::new)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for FileTime {
    /// Serializes a `FileTime` into the given Serde serializer.
    ///
    /// This serializes using the underlying [`u64`] format.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     serde_json::to_string(&FileTime::UNIX_EPOCH).unwrap(),
    ///     "116444736000000000"
    /// );
    ///
    /// assert_eq!(
    ///     serde_json::to_string(&Some(FileTime::UNIX_EPOCH)).unwrap(),
    ///     "116444736000000000"
    /// );
    /// assert_eq!(serde_json::to_string(&None::<FileTime>).unwrap(), "null");
    /// ```
    #[inline]
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_newtype_struct("FileTime", &self.to_raw())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for FileTime {
    /// Deserializes a `FileTime` from the given Serde deserializer.
    ///
    /// This deserializes from its underlying [`u64`] representation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     serde_json::from_str::<FileTime>("116444736000000000").unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    ///
    /// assert_eq!(
    ///     serde_json::from_str::<Option<FileTime>>("116444736000000000").unwrap(),
    ///     Some(FileTime::UNIX_EPOCH)
    /// );
    /// assert_eq!(
    ///     serde_json::from_str::<Option<FileTime>>("null").unwrap(),
    ///     None
    /// );
    /// ```
    #[inline]
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::{de::Visitor, Deserializer};

        struct FileTimeVisitor;

        impl<'de> Visitor<'de> for FileTimeVisitor {
            type Value = FileTime;

            #[inline]
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "a newtype struct `FileTime`")
            }

            #[inline]
            fn visit_newtype_struct<D: Deserializer<'de>>(
                self,
                deserializer: D,
            ) -> Result<Self::Value, D::Error> {
                use serde::Deserialize;

                u64::deserialize(deserializer).map(FileTime::new)
            }
        }

        deserializer.deserialize_newtype_struct("FileTime", FileTimeVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clone() {
        assert_eq!(FileTime::NT_TIME_EPOCH.clone(), FileTime::NT_TIME_EPOCH);
    }

    #[test]
    fn copy() {
        let a = FileTime::NT_TIME_EPOCH;
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", FileTime::NT_TIME_EPOCH), "FileTime(0)");
        assert_eq!(
            format!("{:?}", FileTime::UNIX_EPOCH),
            "FileTime(116444736000000000)"
        );
        assert_eq!(
            format!("{:?}", FileTime::MAX),
            "FileTime(18446744073709551615)"
        );
    }

    #[test]
    fn equality() {
        assert_eq!(FileTime::NT_TIME_EPOCH, FileTime::NT_TIME_EPOCH);
        assert_ne!(FileTime::NT_TIME_EPOCH, FileTime::UNIX_EPOCH);
        assert_ne!(FileTime::NT_TIME_EPOCH, FileTime::MAX);
        assert_ne!(FileTime::UNIX_EPOCH, FileTime::NT_TIME_EPOCH);
        assert_eq!(FileTime::UNIX_EPOCH, FileTime::UNIX_EPOCH);
        assert_ne!(FileTime::UNIX_EPOCH, FileTime::MAX);
        assert_ne!(FileTime::MAX, FileTime::NT_TIME_EPOCH);
        assert_ne!(FileTime::MAX, FileTime::UNIX_EPOCH);
        assert_eq!(FileTime::MAX, FileTime::MAX);
    }

    #[test]
    fn order() {
        assert_eq!(FileTime::UNIX_EPOCH.cmp(&FileTime::MAX), Ordering::Less);
        assert_eq!(
            FileTime::UNIX_EPOCH.cmp(&FileTime::UNIX_EPOCH),
            Ordering::Equal
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.cmp(&FileTime::NT_TIME_EPOCH),
            Ordering::Greater
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn hash() {
        use std::{
            collections::hash_map::DefaultHasher,
            hash::{Hash, Hasher},
        };

        assert_ne!(
            {
                let mut hasher = DefaultHasher::new();
                FileTime::NT_TIME_EPOCH.hash(&mut hasher);
                hasher.finish()
            },
            {
                let mut hasher = DefaultHasher::new();
                FileTime::MAX.hash(&mut hasher);
                hasher.finish()
            }
        );
    }

    #[test]
    fn nt_time_epoch() {
        assert_eq!(
            OffsetDateTime::try_from(FileTime::NT_TIME_EPOCH).unwrap(),
            datetime!(1601-01-01 00:00 UTC)
        );
    }

    #[test]
    fn unix_epoch() {
        assert_eq!(
            OffsetDateTime::try_from(FileTime::UNIX_EPOCH).unwrap(),
            OffsetDateTime::UNIX_EPOCH
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn max() {
        assert_eq!(
            OffsetDateTime::try_from(FileTime::MAX).unwrap(),
            datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn now() {
        let now = FileTime::now();
        // After "2023-01-01 00:00:00 UTC".
        assert!(now >= FileTime::new(133_170_048_000_000_000));
    }

    #[test]
    fn new() {
        assert_eq!(FileTime::new(u64::MIN), FileTime::NT_TIME_EPOCH);
        assert_eq!(FileTime::new(116_444_736_000_000_000), FileTime::UNIX_EPOCH);
        assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
    }

    #[test]
    fn to_raw() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_raw(), u64::MIN);
        assert_eq!(FileTime::UNIX_EPOCH.to_raw(), 116_444_736_000_000_000);
        assert_eq!(FileTime::MAX.to_raw(), u64::MAX);
    }

    #[allow(deprecated)]
    #[test]
    fn as_u64() {
        assert_eq!(FileTime::NT_TIME_EPOCH.as_u64(), u64::MIN);
        assert_eq!(FileTime::UNIX_EPOCH.as_u64(), 116_444_736_000_000_000);
        assert_eq!(FileTime::MAX.as_u64(), u64::MAX);
    }

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

    #[test]
    fn to_dos_date_time_before_dos_date_time_epoch() {
        // `1979-12-31 23:59:58 UTC`.
        assert_eq!(
            FileTime::new(119_600_063_980_000_000)
                .to_dos_date_time(None)
                .unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
        // `1979-12-31 23:59:59 UTC`.
        assert_eq!(
            FileTime::new(119_600_063_990_000_000)
                .to_dos_date_time(None)
                .unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
        // `1980-01-01 00:59:58 UTC`.
        assert_eq!(
            FileTime::new(119_600_099_980_000_000)
                .to_dos_date_time(Some(offset!(-01:00)))
                .unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
        // `1980-01-01 00:59:59 UTC`.
        assert_eq!(
            FileTime::new(119_600_099_990_000_000)
                .to_dos_date_time(Some(offset!(-01:00)))
                .unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
    }

    #[allow(clippy::too_many_lines)]
    #[test]
    fn to_dos_date_time() {
        // `1980-01-01 00:00:00 UTC`.
        assert_eq!(
            FileTime::new(119_600_064_000_000_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0x0021, u16::MIN, u8::MIN, None)
        );
        // `1980-01-01 00:00:01 UTC`.
        assert_eq!(
            FileTime::new(119_600_064_010_000_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0x0021, u16::MIN, 100, None)
        );
        // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
        //
        // `2018-11-17 10:38:30 UTC`.
        assert_eq!(
            FileTime::new(131_869_247_100_000_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0x4d71, 0x54cf, u8::MIN, None)
        );
        // `2107-12-31 23:59:58 UTC`.
        assert_eq!(
            FileTime::new(159_992_927_980_000_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0xff9f, 0xbf7d, u8::MIN, None)
        );
        // `2107-12-31 23:59:59 UTC`.
        assert_eq!(
            FileTime::new(159_992_927_990_000_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0xff9f, 0xbf7d, 100, None)
        );

        // `1980-01-01 00:00:00.010000000 UTC`.
        assert_eq!(
            FileTime::new(119_600_064_000_100_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0x0021, u16::MIN, 1, None)
        );
        // `1980-01-01 00:00:00.100000000 UTC`.
        assert_eq!(
            FileTime::new(119_600_064_001_000_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0x0021, u16::MIN, 10, None)
        );
        // `1980-01-01 00:00:01.990000000 UTC`.
        assert_eq!(
            FileTime::new(119_600_064_019_900_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0x0021, u16::MIN, 199, None)
        );
        // `1980-01-01 00:00:02 UTC`.
        assert_eq!(
            FileTime::new(119_600_064_020_000_000)
                .to_dos_date_time(None)
                .unwrap(),
            (0x0021, 0x0001, u8::MIN, None)
        );

        // <https://devblogs.microsoft.com/oldnewthing/20030905-02/?p=42653>.
        //
        // From `2002-11-27 03:25:00 UTC` to `2002-11-26 19:25:00 -08:00`.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:00)))
                .unwrap(),
            (0x2d7a, 0x9b20, u8::MIN, Some(offset!(-08:00)))
        );
        // From `2002-11-27 03:25:00 UTC` to `2002-11-26 19:25:00 -08:00`.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08)))
                .unwrap(),
            (0x2d7a, 0x9b20, u8::MIN, Some(offset!(-08)))
        );
        // `2002-11-27 03:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:00:01)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, None)
        );
        // `2002-11-27 03:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:01)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, None)
        );
        // `2002-11-27 03:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:14)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, None)
        );
        // `2002-11-27 03:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:14:59)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, None)
        );
        // From `2002-11-27 03:25:00 UTC` to `2002-11-26 19:10:00 -08:15`.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:15)))
                .unwrap(),
            (0x2d7a, 0x9940, u8::MIN, Some(offset!(-08:15)))
        );
        // `2002-11-27 03:25:00 UTC`.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(UtcOffset::UTC))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, Some(UtcOffset::UTC))
        );
        // `2002-11-27 03:25:00 UTC`.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(+00:00)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, Some(UtcOffset::UTC))
        );

        // From `1980-01-01 00:00:00 UTC` to `1980-01-01 15:45:00 +15:45`.
        assert_eq!(
            FileTime::new(119_600_064_000_000_000)
                .to_dos_date_time(Some(offset!(+15:45)))
                .unwrap(),
            (0x0021, 0x7da0, u8::MIN, Some(offset!(+15:45)))
        );
        // From `2107-12-31 23:59:58 UTC` to `2107-12-31 07:59:58 -16:00`.
        assert_eq!(
            FileTime::new(159_992_927_980_000_000)
                .to_dos_date_time(Some(offset!(-16:00)))
                .unwrap(),
            (0xff9f, 0x3f7d, u8::MIN, Some(offset!(-16:00)))
        );
    }

    #[test]
    fn to_dos_date_time_with_too_big_date_time() {
        // `2108-01-01 00:00:00 UTC`.
        assert_eq!(
            FileTime::new(159_992_928_000_000_000)
                .to_dos_date_time(None)
                .unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
        );
        // `2107-12-31 23:00:00 UTC`.
        assert_eq!(
            FileTime::new(159_992_892_000_000_000)
                .to_dos_date_time(Some(offset!(+01:00)))
                .unwrap_err(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
        );
    }

    #[allow(clippy::should_panic_without_expect)]
    #[test]
    #[should_panic]
    fn to_dos_date_time_with_invalid_positive_offset() {
        // From `1980-01-01 00:00:00 UTC` to `1980-01-01 16:00:00 +16:00`.
        let _: (u16, u16, u8, Option<UtcOffset>) = FileTime::new(119_600_064_000_000_000)
            .to_dos_date_time(Some(offset!(+16:00)))
            .unwrap();
    }

    #[allow(clippy::should_panic_without_expect)]
    #[test]
    #[should_panic]
    fn to_dos_date_time_with_invalid_negative_offset() {
        // From `2107-12-31 23:59:58 UTC` to `2107-12-31 07:44:58 -16:15`.
        let _: (u16, u16, u8, Option<UtcOffset>) = FileTime::new(159_992_927_980_000_000)
            .to_dos_date_time(Some(offset!(-16:15)))
            .unwrap();
    }

    #[test]
    fn from_dos_date_time() {
        // `1980-01-01 00:00:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x0021, u16::MIN, None, None).unwrap(),
            FileTime::new(119_600_064_000_000_000)
        );
        // `1980-01-01 00:00:01 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x0021, u16::MIN, Some(100), None).unwrap(),
            FileTime::new(119_600_064_010_000_000)
        );
        // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
        //
        // `2018-11-17 10:38:30 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x4d71, 0x54cf, None, None).unwrap(),
            FileTime::new(131_869_247_100_000_000)
        );
        // `2107-12-31 23:59:58 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0xff9f, 0xbf7d, None, None).unwrap(),
            FileTime::new(159_992_927_980_000_000)
        );
        // `2107-12-31 23:59:59 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0xff9f, 0xbf7d, Some(100), None).unwrap(),
            FileTime::new(159_992_927_990_000_000)
        );

        // `1980-01-01 00:00:00.010000000 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x0021, u16::MIN, Some(1), None).unwrap(),
            FileTime::new(119_600_064_000_100_000)
        );
        // `1980-01-01 00:00:00.100000000 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x0021, u16::MIN, Some(10), None).unwrap(),
            FileTime::new(119_600_064_001_000_000)
        );
        // `1980-01-01 00:00:01.990000000 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x0021, u16::MIN, Some(199), None).unwrap(),
            FileTime::new(119_600_064_019_900_000)
        );

        // <https://devblogs.microsoft.com/oldnewthing/20030905-02/?p=42653>.
        //
        // From `2002-11-26 19:25:00 -08:00` to `2002-11-27 03:25:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:00))).unwrap(),
            FileTime::new(126_828_411_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:00` to `2002-11-27 03:25:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08))).unwrap(),
            FileTime::new(126_828_411_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:00:01` to `2002-11-26 19:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:00:01))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:01` to `2002-11-26 19:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:01))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:14` to `2002-11-26 19:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:14))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:14:59` to `2002-11-26 19:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, consider UTC to
        // be the local date and time.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:14:59))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:15` to `2002-11-27 03:40:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:15))).unwrap(),
            FileTime::new(126_828_420_000_000_000)
        );
        // `2002-11-26 19:25:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(UtcOffset::UTC)).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // `2002-11-26 19:25:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(+00:00))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );

        // From `2107-12-31 23:59:58 +15:45` to `2107-12-31 08:14:58 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0xff9f, 0xbf7d, None, Some(offset!(+15:45))).unwrap(),
            FileTime::new(159_992_360_980_000_000)
        );
        // From `1980-01-01 00:00:00 -16:00` to `1980-01-01 16:00:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0x0021, u16::MIN, None, Some(offset!(-16:00))).unwrap(),
            FileTime::new(119_600_640_000_000_000)
        );
    }

    #[test]
    fn from_dos_date_time_with_invalid_date_time() {
        // The Day field is 0.
        assert!(FileTime::from_dos_date_time(0x0020, u16::MIN, None, None).is_err());
        // The Day field is 30, which is after the last day of February.
        assert!(FileTime::from_dos_date_time(0x005e, u16::MIN, None, None).is_err());
        // The Month field is 0.
        assert!(FileTime::from_dos_date_time(0x0001, u16::MIN, None, None).is_err());
        // The Month field is 13.
        assert!(FileTime::from_dos_date_time(0x01a1, u16::MIN, None, None).is_err());

        // The DoubleSeconds field is 30.
        assert!(FileTime::from_dos_date_time(0x0021, 0x001e, None, None).is_err());
        // The Minute field is 60.
        assert!(FileTime::from_dos_date_time(0x0021, 0x0780, None, None).is_err());
        // The Hour field is 24.
        assert!(FileTime::from_dos_date_time(0x0021, 0xc000, None, None).is_err());
    }

    #[allow(clippy::should_panic_without_expect)]
    #[test]
    #[should_panic]
    fn from_dos_date_time_with_invalid_resolution() {
        let _: FileTime = FileTime::from_dos_date_time(0x0021, u16::MIN, Some(200), None).unwrap();
    }

    #[allow(clippy::should_panic_without_expect)]
    #[test]
    #[should_panic]
    fn from_dos_date_time_with_invalid_positive_offset() {
        // From `2107-12-31 23:59:58 +16:00` to `2107-12-31 07:59:58 UTC`.
        let _: FileTime =
            FileTime::from_dos_date_time(0xff9f, 0xbf7d, None, Some(offset!(+16:00))).unwrap();
    }

    #[allow(clippy::should_panic_without_expect)]
    #[test]
    #[should_panic]
    fn from_dos_date_time_with_invalid_negative_offset() {
        // From `1980-01-01 00:00:00 -16:15` to `1980-01-01 16:15:00 UTC`.
        let _: FileTime =
            FileTime::from_dos_date_time(0x0021, u16::MIN, None, Some(offset!(-16:15))).unwrap();
    }

    #[test]
    fn checked_add() {
        use core::time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::ZERO),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(1)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(99)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(100)),
            Some(FileTime::new(1))
        );

        assert_eq!(
            FileTime::MAX.checked_add(Duration::ZERO),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_add(Duration::from_nanos(1)),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_add(Duration::from_nanos(99)),
            Some(FileTime::MAX)
        );
        assert_eq!(FileTime::MAX.checked_add(Duration::from_nanos(100)), None);
    }

    #[test]
    fn checked_sub() {
        use core::time::Duration;

        assert_eq!(
            FileTime::MAX.checked_sub(Duration::ZERO),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_sub(Duration::from_nanos(1)),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_sub(Duration::from_nanos(99)),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_sub(Duration::from_nanos(100)),
            Some(FileTime::new(u64::MAX - 1))
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::ZERO),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(1)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(99)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(100)),
            None
        );
    }

    #[test]
    fn saturating_add() {
        use core::time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::ZERO),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(1)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(99)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(100)),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX.saturating_add(Duration::ZERO), FileTime::MAX);
        assert_eq!(
            FileTime::MAX.saturating_add(Duration::from_nanos(1)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_add(Duration::from_nanos(99)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_add(Duration::from_nanos(100)),
            FileTime::MAX
        );
    }

    #[test]
    fn saturating_sub() {
        use core::time::Duration;

        assert_eq!(FileTime::MAX.saturating_sub(Duration::ZERO), FileTime::MAX);
        assert_eq!(
            FileTime::MAX.saturating_sub(Duration::from_nanos(1)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_sub(Duration::from_nanos(99)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_sub(Duration::from_nanos(100)),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::ZERO),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(1)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(99)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(100)),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[test]
    fn to_be_bytes() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_be_bytes(), [u8::MIN; 8]);
        assert_eq!(
            FileTime::UNIX_EPOCH.to_be_bytes(),
            [0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]
        );
        assert_eq!(FileTime::MAX.to_be_bytes(), [u8::MAX; 8]);
    }

    #[test]
    fn to_le_bytes() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_le_bytes(), [u8::MIN; 8]);
        assert_eq!(
            FileTime::UNIX_EPOCH.to_le_bytes(),
            [0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]
        );
        assert_eq!(FileTime::MAX.to_le_bytes(), [u8::MAX; 8]);
    }

    #[test]
    fn from_be_bytes() {
        assert_eq!(
            FileTime::from_be_bytes([u8::MIN; 8]),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_be_bytes([0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(FileTime::from_be_bytes([u8::MAX; 8]), FileTime::MAX);
    }

    #[test]
    fn from_le_bytes() {
        assert_eq!(
            FileTime::from_le_bytes([u8::MIN; 8]),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_le_bytes([0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(FileTime::from_le_bytes([u8::MAX; 8]), FileTime::MAX);
    }

    #[test]
    fn default() {
        assert_eq!(FileTime::default(), FileTime::NT_TIME_EPOCH);
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{}", FileTime::UNIX_EPOCH), "116444736000000000");
        assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
    }

    #[test]
    fn octal() {
        assert_eq!(format!("{:o}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#o}", FileTime::NT_TIME_EPOCH), "0o0");
        assert_eq!(
            format!("{:022o}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000"
        );
        assert_eq!(
            format!("{:#024o}", FileTime::NT_TIME_EPOCH),
            "0o0000000000000000000000"
        );
        assert_eq!(format!("{:o}", FileTime::UNIX_EPOCH), "6355435732517500000");
        assert_eq!(
            format!("{:#o}", FileTime::UNIX_EPOCH),
            "0o6355435732517500000"
        );
        assert_eq!(
            format!("{:022o}", FileTime::UNIX_EPOCH),
            "0006355435732517500000"
        );
        assert_eq!(
            format!("{:#024o}", FileTime::UNIX_EPOCH),
            "0o0006355435732517500000"
        );
        assert_eq!(format!("{:o}", FileTime::MAX), "1777777777777777777777");
        assert_eq!(format!("{:#o}", FileTime::MAX), "0o1777777777777777777777");
        assert_eq!(format!("{:022o}", FileTime::MAX), "1777777777777777777777");
        assert_eq!(
            format!("{:#024o}", FileTime::MAX),
            "0o1777777777777777777777"
        );
    }

    #[test]
    fn lower_hex() {
        assert_eq!(format!("{:x}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#x}", FileTime::NT_TIME_EPOCH), "0x0");
        assert_eq!(
            format!("{:016x}", FileTime::NT_TIME_EPOCH),
            "0000000000000000"
        );
        assert_eq!(
            format!("{:#018x}", FileTime::NT_TIME_EPOCH),
            "0x0000000000000000"
        );
        assert_eq!(format!("{:x}", FileTime::UNIX_EPOCH), "19db1ded53e8000");
        assert_eq!(format!("{:#x}", FileTime::UNIX_EPOCH), "0x19db1ded53e8000");
        assert_eq!(format!("{:016x}", FileTime::UNIX_EPOCH), "019db1ded53e8000");
        assert_eq!(
            format!("{:#018x}", FileTime::UNIX_EPOCH),
            "0x019db1ded53e8000"
        );
        assert_eq!(format!("{:x}", FileTime::MAX), "ffffffffffffffff");
        assert_eq!(format!("{:#x}", FileTime::MAX), "0xffffffffffffffff");
        assert_eq!(format!("{:016x}", FileTime::MAX), "ffffffffffffffff");
        assert_eq!(format!("{:#018x}", FileTime::MAX), "0xffffffffffffffff");
    }

    #[test]
    fn upper_hex() {
        assert_eq!(format!("{:X}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#X}", FileTime::NT_TIME_EPOCH), "0x0");
        assert_eq!(
            format!("{:016X}", FileTime::NT_TIME_EPOCH),
            "0000000000000000"
        );
        assert_eq!(
            format!("{:#018X}", FileTime::NT_TIME_EPOCH),
            "0x0000000000000000"
        );
        assert_eq!(format!("{:X}", FileTime::UNIX_EPOCH), "19DB1DED53E8000");
        assert_eq!(format!("{:#X}", FileTime::UNIX_EPOCH), "0x19DB1DED53E8000");
        assert_eq!(format!("{:016X}", FileTime::UNIX_EPOCH), "019DB1DED53E8000");
        assert_eq!(
            format!("{:#018X}", FileTime::UNIX_EPOCH),
            "0x019DB1DED53E8000"
        );
        assert_eq!(format!("{:X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:#X}", FileTime::MAX), "0xFFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:016X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:#018X}", FileTime::MAX), "0xFFFFFFFFFFFFFFFF");
    }

    #[test]
    fn binary() {
        assert_eq!(format!("{:b}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#b}", FileTime::NT_TIME_EPOCH), "0b0");
        assert_eq!(
            format!("{:064b}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000000000000000000000000000000000000000000000"
        );
        assert_eq!(
            format!("{:#066b}", FileTime::NT_TIME_EPOCH),
            "0b0000000000000000000000000000000000000000000000000000000000000000"
        );
        assert_eq!(
            format!("{:b}", FileTime::UNIX_EPOCH),
            "110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:#b}", FileTime::UNIX_EPOCH),
            "0b110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:064b}", FileTime::UNIX_EPOCH),
            "0000000110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:#066b}", FileTime::UNIX_EPOCH),
            "0b0000000110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:b}", FileTime::MAX),
            "1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:#b}", FileTime::MAX),
            "0b1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:064b}", FileTime::MAX),
            "1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:#066b}", FileTime::MAX),
            "0b1111111111111111111111111111111111111111111111111111111111111111"
        );
    }

    #[test]
    fn lower_exp() {
        assert_eq!(format!("{:e}", FileTime::NT_TIME_EPOCH), "0e0");
        assert_eq!(
            format!("{:024e}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000e0"
        );
        assert_eq!(format!("{:e}", FileTime::UNIX_EPOCH), "1.16444736e17");
        assert_eq!(
            format!("{:024e}", FileTime::UNIX_EPOCH),
            "000000000001.16444736e17"
        );
        assert_eq!(format!("{:e}", FileTime::MAX), "1.8446744073709551615e19");
        assert_eq!(
            format!("{:024e}", FileTime::MAX),
            "1.8446744073709551615e19"
        );
    }

    #[test]
    fn upper_exp() {
        assert_eq!(format!("{:E}", FileTime::NT_TIME_EPOCH), "0E0");
        assert_eq!(
            format!("{:024E}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000E0"
        );
        assert_eq!(format!("{:E}", FileTime::UNIX_EPOCH), "1.16444736E17");
        assert_eq!(
            format!("{:024E}", FileTime::UNIX_EPOCH),
            "000000000001.16444736E17"
        );
        assert_eq!(format!("{:E}", FileTime::MAX), "1.8446744073709551615E19");
        assert_eq!(
            format!("{:024E}", FileTime::MAX),
            "1.8446744073709551615E19"
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn equality_system_time_and_file_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700)),
            FileTime::new(9_223_372_036_854_775_807)
        );
        assert_ne!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700)),
            FileTime::new(9_223_372_036_854_775_806)
        );
        assert_eq!(SystemTime::UNIX_EPOCH, FileTime::UNIX_EPOCH);
        assert_ne!(SystemTime::UNIX_EPOCH, FileTime::NT_TIME_EPOCH);
    }

    #[cfg(feature = "std")]
    #[test]
    fn equality_file_time_and_system_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807),
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
        );
        assert_ne!(
            FileTime::new(9_223_372_036_854_775_806),
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
        );
        assert_eq!(FileTime::UNIX_EPOCH, SystemTime::UNIX_EPOCH);
        assert_ne!(FileTime::NT_TIME_EPOCH, SystemTime::UNIX_EPOCH);
    }

    #[test]
    fn equality_offset_date_time_and_file_time() {
        assert_eq!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC),
            FileTime::new(2_650_467_743_999_999_999)
        );
        assert_ne!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC),
            FileTime::NT_TIME_EPOCH
        );
        assert_ne!(
            datetime!(1601-01-01 00:00 UTC),
            FileTime::new(2_650_467_743_999_999_999)
        );
        assert_eq!(datetime!(1601-01-01 00:00 UTC), FileTime::NT_TIME_EPOCH);
    }

    #[test]
    fn equality_file_time_and_offset_date_time() {
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999),
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
        );
        assert_ne!(
            FileTime::NT_TIME_EPOCH,
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
        );
        assert_ne!(
            FileTime::new(2_650_467_743_999_999_999),
            datetime!(1601-01-01 00:00 UTC)
        );
        assert_eq!(FileTime::NT_TIME_EPOCH, datetime!(1601-01-01 00:00 UTC));
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn equality_chrono_date_time_and_file_time() {
        use chrono::{DateTime, Utc};

        assert_eq!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap(),
            FileTime::MAX
        );
        assert_ne!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_ne!(
            "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap(),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn equality_file_time_and_chrono_date_time() {
        use chrono::{DateTime, Utc};

        assert_eq!(
            FileTime::MAX,
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
        );
        assert_ne!(
            FileTime::NT_TIME_EPOCH,
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
        );
        assert_ne!(
            FileTime::MAX,
            "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH,
            "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn order_system_time_and_file_time() {
        use std::time::SystemTime;

        assert_eq!(
            SystemTime::UNIX_EPOCH.partial_cmp(&FileTime::new(9_223_372_036_854_775_807)),
            Some(Ordering::Less)
        );
        assert_eq!(
            SystemTime::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert_eq!(
            SystemTime::UNIX_EPOCH.partial_cmp(&FileTime::NT_TIME_EPOCH),
            Some(Ordering::Greater)
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn order_file_time_and_system_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(
                &(SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
            ),
            Some(Ordering::Less)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&SystemTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(
                &(SystemTime::UNIX_EPOCH - (FileTime::UNIX_EPOCH - FileTime::NT_TIME_EPOCH))
            ),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn order_offset_date_time_and_file_time() {
        assert_eq!(
            OffsetDateTime::UNIX_EPOCH.partial_cmp(&FileTime::new(2_650_467_743_999_999_999)),
            Some(Ordering::Less)
        );
        assert_eq!(
            OffsetDateTime::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert_eq!(
            OffsetDateTime::UNIX_EPOCH.partial_cmp(&FileTime::NT_TIME_EPOCH),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn order_file_time_and_offset_date_time() {
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&datetime!(9999-12-31 23:59:59.999_999_900 UTC)),
            Some(Ordering::Less)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&OffsetDateTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&datetime!(1601-01-01 00:00 UTC)),
            Some(Ordering::Greater)
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn order_chrono_date_time_and_file_time() {
        use chrono::{DateTime, Utc};

        assert_eq!(
            DateTime::<Utc>::UNIX_EPOCH.partial_cmp(&FileTime::MAX),
            Some(Ordering::Less)
        );
        assert_eq!(
            DateTime::<Utc>::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert_eq!(
            DateTime::<Utc>::UNIX_EPOCH.partial_cmp(&FileTime::NT_TIME_EPOCH),
            Some(Ordering::Greater)
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn order_file_time_and_chrono_date_time() {
        use chrono::{DateTime, Utc};

        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(
                &"+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
            ),
            Some(Ordering::Less)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&DateTime::<Utc>::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert_eq!(
            FileTime::UNIX_EPOCH
                .partial_cmp(&"1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap()),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn add_std_duration() {
        use core::time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::from_nanos(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::from_nanos(99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::from_nanos(100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX + Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::from_nanos(1), FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::from_nanos(99), FileTime::MAX);
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_std_duration_with_overflow() {
        use core::time::Duration;

        let _: FileTime = FileTime::MAX + Duration::from_nanos(100);
    }

    #[test]
    fn add_positive_time_duration() {
        use time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::nanoseconds(100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX + Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::nanoseconds(99), FileTime::MAX);
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_positive_time_duration_with_overflow() {
        use time::Duration;

        let _: FileTime = FileTime::MAX + Duration::nanoseconds(100);
    }

    #[test]
    fn add_negative_time_duration() {
        use time::Duration;

        assert_eq!(FileTime::MAX + -Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX + -Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::nanoseconds(-99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX + Duration::nanoseconds(-100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH + -Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + -Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_negative_time_duration_with_overflow() {
        use time::Duration;

        let _: FileTime = FileTime::NT_TIME_EPOCH + Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX + TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX + TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX + TimeDelta::nanoseconds(99), FileTime::MAX);
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _: FileTime = FileTime::MAX + TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(FileTime::MAX + -TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX + -TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX + TimeDelta::nanoseconds(-99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX + TimeDelta::nanoseconds(-100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH + -TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + -TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _: FileTime = FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(-100);
    }

    #[test]
    fn add_assign_std_duration() {
        use core::time::Duration;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::from_nanos(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::from_nanos(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::from_nanos(100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::from_nanos(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::from_nanos(99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_assign_std_duration_with_overflow() {
        use core::time::Duration;

        let mut ft = FileTime::MAX;
        ft += Duration::from_nanos(100);
    }

    #[test]
    fn add_assign_positive_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::nanoseconds(100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_assign_positive_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::MAX;
        ft += Duration::nanoseconds(100);
    }

    #[test]
    fn add_assign_negative_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::MAX;
            ft += -Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_assign_negative_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft += Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_assign_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_assign_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::MAX;
        ft += TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_assign_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::MAX;
            ft += -TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_assign_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft += TimeDelta::nanoseconds(-100);
    }

    #[test]
    fn sub_file_time() {
        use core::time::Duration;

        assert_eq!(FileTime::MAX - FileTime::MAX, Duration::ZERO);
        assert_eq!(
            FileTime::MAX - (FileTime::MAX - Duration::from_nanos(100)),
            Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::MAX - FileTime::NT_TIME_EPOCH,
            Duration::new(1_844_674_407_370, 955_161_500)
        );
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn sub_file_time_with_overflow() {
        use core::time::Duration;

        let _: Duration = (FileTime::MAX - Duration::from_nanos(100)) - FileTime::MAX;
    }

    #[test]
    fn sub_std_duration() {
        use core::time::Duration;

        assert_eq!(FileTime::MAX - Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::from_nanos(1), FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::from_nanos(99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX - Duration::from_nanos(100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::from_nanos(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::from_nanos(99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_std_duration_with_overflow() {
        use core::time::Duration;

        let _: FileTime = FileTime::NT_TIME_EPOCH - Duration::from_nanos(100);
    }

    #[test]
    fn sub_positive_time_duration() {
        use time::Duration;

        assert_eq!(FileTime::MAX - Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::nanoseconds(99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX - Duration::nanoseconds(100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_positive_time_duration_with_overflow() {
        use time::Duration;

        let _: FileTime = FileTime::NT_TIME_EPOCH - Duration::nanoseconds(100);
    }

    #[test]
    fn sub_negative_time_duration() {
        use time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH - -Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - -Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::nanoseconds(-100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX - -Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX - -Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::nanoseconds(-99), FileTime::MAX);
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_negative_time_duration_with_overflow() {
        use time::Duration;

        let _: FileTime = FileTime::MAX - Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(FileTime::MAX - TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX - TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX - TimeDelta::nanoseconds(99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX - TimeDelta::nanoseconds(100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _: FileTime = FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(
            FileTime::NT_TIME_EPOCH - -TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - -TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(-100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX - -TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX - -TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX - TimeDelta::nanoseconds(-99), FileTime::MAX);
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _: FileTime = FileTime::MAX - TimeDelta::nanoseconds(-100);
    }

    #[cfg(feature = "std")]
    #[test]
    fn sub_file_time_from_system_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
                - FileTime::new(9_223_372_036_854_775_807),
            Duration::ZERO
        );
        assert_eq!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
                - FileTime::new(9_223_372_036_854_775_806),
            Duration::from_nanos(100)
        );
        assert_eq!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
                - FileTime::UNIX_EPOCH,
            Duration::new(910_692_730_085, 477_580_700)
        );
    }

    #[cfg(feature = "std")]
    #[test]
    #[should_panic(expected = "RHS provided is later than LHS")]
    fn sub_file_time_from_system_time_with_overflow() {
        use std::time::{Duration, SystemTime};

        let _: Duration = FileTime::new(9_223_372_036_854_775_806)
            - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700));
    }

    #[cfg(feature = "std")]
    #[test]
    fn sub_system_time_from_file_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700)),
            Duration::ZERO
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_699)),
            Duration::from_nanos(if cfg!(windows) { 100 } else { 1 })
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_601)),
            Duration::from_nanos(if cfg!(windows) { 100 } else { 99 })
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_600)),
            Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807) - SystemTime::UNIX_EPOCH,
            Duration::new(910_692_730_085, 477_580_700)
        );
    }

    #[cfg(feature = "std")]
    #[test]
    #[should_panic(expected = "RHS provided is later than LHS")]
    fn sub_system_time_from_file_time_with_overflow() {
        use std::time::{Duration, SystemTime};

        let _: Duration = (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_600))
            - FileTime::new(9_223_372_036_854_775_807);
    }

    #[test]
    fn sub_file_time_from_offset_date_time() {
        use time::Duration;

        assert_eq!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
                - FileTime::new(2_650_467_743_999_999_999),
            Duration::ZERO
        );
        assert_eq!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
                - (FileTime::new(2_650_467_743_999_999_999) - Duration::nanoseconds(100)),
            Duration::nanoseconds(100)
        );
        assert_eq!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC) - FileTime::NT_TIME_EPOCH,
            Duration::new(265_046_774_399, 999_999_900)
        );
    }

    #[test]
    fn sub_offset_date_time_from_file_time() {
        use time::Duration;

        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - datetime!(9999-12-31 23:59:59.999_999_900 UTC),
            Duration::ZERO
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - (datetime!(9999-12-31 23:59:59.999_999_900 UTC) - Duration::nanoseconds(1)),
            Duration::nanoseconds(1)
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - (datetime!(9999-12-31 23:59:59.999_999_900 UTC) - Duration::nanoseconds(99)),
            Duration::nanoseconds(99)
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - (datetime!(9999-12-31 23:59:59.999_999_900 UTC) - Duration::nanoseconds(100)),
            Duration::nanoseconds(100)
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999) - datetime!(1601-01-01 00:00 UTC),
            Duration::new(265_046_774_399, 999_999_900)
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_file_time_from_chrono_date_time() {
        use core::time::Duration;

        use chrono::{DateTime, TimeDelta, Utc};

        assert_eq!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
                - FileTime::MAX,
            TimeDelta::zero()
        );
        assert_eq!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
                - (FileTime::MAX - Duration::from_nanos(100)),
            TimeDelta::nanoseconds(100)
        );
        assert_eq!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
                - FileTime::NT_TIME_EPOCH,
            TimeDelta::new(1_844_674_407_370, 955_161_500).unwrap()
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_chrono_date_time_from_file_time() {
        use chrono::{DateTime, TimeDelta, Utc};

        assert_eq!(
            FileTime::MAX
                - "+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap(),
            TimeDelta::zero()
        );
        assert_eq!(
            FileTime::MAX
                - ("+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
                    - TimeDelta::nanoseconds(1)),
            TimeDelta::nanoseconds(1)
        );
        assert_eq!(
            FileTime::MAX
                - ("+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
                    - TimeDelta::nanoseconds(99)),
            TimeDelta::nanoseconds(99)
        );
        assert_eq!(
            FileTime::MAX
                - ("+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
                    - TimeDelta::nanoseconds(100)),
            TimeDelta::nanoseconds(100)
        );
        assert_eq!(
            FileTime::MAX - "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap(),
            TimeDelta::new(1_844_674_407_370, 955_161_500).unwrap()
        );
    }

    #[test]
    fn sub_assign_std_duration() {
        use core::time::Duration;

        {
            let mut ft = FileTime::MAX;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::from_nanos(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::from_nanos(99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::from_nanos(100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::from_nanos(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::from_nanos(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_assign_std_duration_with_overflow() {
        use core::time::Duration;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft -= Duration::from_nanos(100);
    }

    #[test]
    fn sub_assign_positive_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::MAX;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::nanoseconds(100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_assign_positive_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft -= Duration::nanoseconds(100);
    }

    #[test]
    fn sub_assign_negative_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft -= -Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_assign_negative_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::MAX;
        ft -= Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_assign_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_assign_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft -= TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_assign_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft -= -TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_assign_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::MAX;
        ft -= TimeDelta::nanoseconds(-100);
    }

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

    #[test]
    fn from_str() {
        assert_eq!(FileTime::from_str("0").unwrap(), FileTime::NT_TIME_EPOCH);
        assert_eq!(FileTime::from_str("+0").unwrap(), FileTime::NT_TIME_EPOCH);
        assert_eq!(
            FileTime::from_str("116444736000000000").unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str("+116444736000000000").unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str("18446744073709551615").unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str("+18446744073709551615").unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn from_str_when_empty() {
        use std::{
            error::Error,
            num::{IntErrorKind, ParseIntError},
        };

        assert_eq!(
            FileTime::from_str("")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::Empty
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn from_str_with_invalid_digit() {
        use std::{
            error::Error,
            num::{IntErrorKind, ParseIntError},
        };

        assert_eq!(
            FileTime::from_str("a")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("-1")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("+")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("-")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str(" 0")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("0 ")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn from_str_when_positive_overflow() {
        use std::{
            error::Error,
            num::{IntErrorKind, ParseIntError},
        };

        assert_eq!(
            FileTime::from_str("18446744073709551616")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde() {
        use serde_test::{assert_tokens, Token};

        assert_tokens(
            &FileTime::NT_TIME_EPOCH,
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MIN),
            ],
        );
        assert_tokens(
            &FileTime::UNIX_EPOCH,
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(116_444_736_000_000_000),
            ],
        );
        assert_tokens(
            &FileTime::MAX,
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MAX),
            ],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_error() {
        use serde_test::{assert_de_tokens_error, Token};

        assert_de_tokens_error::<FileTime>(
            &[Token::BorrowedStr("FileTime")],
            r#"invalid type: string "FileTime", expected a newtype struct `FileTime`"#,
        );
        assert_de_tokens_error::<FileTime>(
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::Bool(bool::default()),
            ],
            "invalid type: boolean `false`, expected u64",
        );
        assert_de_tokens_error::<FileTime>(
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::I64(i64::MIN),
            ],
            "invalid value: integer `-9223372036854775808`, expected u64",
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde_optional() {
        use serde_test::{assert_tokens, Token};

        assert_tokens(
            &Some(FileTime::NT_TIME_EPOCH),
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MIN),
            ],
        );
        assert_tokens(
            &Some(FileTime::UNIX_EPOCH),
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(116_444_736_000_000_000),
            ],
        );
        assert_tokens(
            &Some(FileTime::MAX),
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MAX),
            ],
        );
        assert_tokens(&None::<FileTime>, &[Token::None]);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_optional_error() {
        use serde_test::{assert_de_tokens_error, Token};

        assert_de_tokens_error::<Option<FileTime>>(
            &[Token::BorrowedStr("FileTime")],
            r#"invalid type: string "FileTime", expected option"#,
        );
        assert_de_tokens_error::<Option<FileTime>>(
            &[Token::Some, Token::BorrowedStr("FileTime")],
            r#"invalid type: string "FileTime", expected a newtype struct `FileTime`"#,
        );
        assert_de_tokens_error::<Option<FileTime>>(
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::Bool(bool::default()),
            ],
            "invalid type: boolean `false`, expected u64",
        );
        assert_de_tokens_error::<Option<FileTime>>(
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::I64(i64::MIN),
            ],
            "invalid value: integer `-9223372036854775808`, expected u64",
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&FileTime::NT_TIME_EPOCH).unwrap(),
            "0"
        );
        assert_eq!(
            serde_json::to_string(&FileTime::UNIX_EPOCH).unwrap(),
            "116444736000000000"
        );
        assert_eq!(
            serde_json::to_string(&FileTime::MAX).unwrap(),
            "18446744073709551615"
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serialize_optional_json() {
        assert_eq!(
            serde_json::to_string(&Some(FileTime::NT_TIME_EPOCH)).unwrap(),
            "0"
        );
        assert_eq!(
            serde_json::to_string(&Some(FileTime::UNIX_EPOCH)).unwrap(),
            "116444736000000000"
        );
        assert_eq!(
            serde_json::to_string(&Some(FileTime::MAX)).unwrap(),
            "18446744073709551615"
        );
        assert_eq!(serde_json::to_string(&None::<FileTime>).unwrap(), "null");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<FileTime>("0").unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            serde_json::from_str::<FileTime>("116444736000000000").unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            serde_json::from_str::<FileTime>("18446744073709551615").unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_optional_json() {
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("0").unwrap(),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("116444736000000000").unwrap(),
            Some(FileTime::UNIX_EPOCH)
        );
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("18446744073709551615").unwrap(),
            Some(FileTime::MAX)
        );
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("null").unwrap(),
            None
        );
    }
}
