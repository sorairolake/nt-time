// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and [MS-DOS date and
//! time].
//!
//! [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time

use time::{error::ComponentRange, macros::offset, Date, OffsetDateTime, Time, UtcOffset};

use crate::error::{DosDateTimeRangeError, DosDateTimeRangeErrorKind};

use super::FileTime;

impl FileTime {
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
    /// UTC to the local date and time in the provided time zone and returns it
    /// with the [UTC offset]. When the `offset` parameter is [`None`] or is not
    /// a multiple of 15 minute intervals, returns the UTC date and time as a
    /// date and time and [`None`] as the UTC offset.
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
    /// When the UTC offset is not a multiple of 15 minute intervals, returns
    /// the UTC date and time:
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
    /// date and time in the provided time zone to UTC. When `offset` is
    /// [`None`] or is not a multiple of 15 minute intervals, assumes the
    /// provided date and time is in UTC.
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
    /// When the [UTC offset] is not a multiple of 15 minute intervals, assumes
    /// the provided date and time is in UTC:
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
}

#[cfg(test)]
mod tests {
    use super::*;

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
        // When the UTC offset is not a multiple of 15 minute intervals, returns the UTC
        // date and time.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:00:01)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, None)
        );
        // `2002-11-27 03:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, returns the UTC
        // date and time.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:01)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, None)
        );
        // `2002-11-27 03:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, returns the UTC
        // date and time.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time(Some(offset!(-08:14)))
                .unwrap(),
            (0x2d7b, 0x1b20, u8::MIN, None)
        );
        // `2002-11-27 03:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, returns the UTC
        // date and time.
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
        // When the UTC offset is not a multiple of 15 minute intervals, assumes the
        // provided date and time is in UTC.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:00:01))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:01` to `2002-11-26 19:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, assumes the
        // provided date and time is in UTC.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:01))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:14` to `2002-11-26 19:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, assumes the
        // provided date and time is in UTC.
        assert_eq!(
            FileTime::from_dos_date_time(0x2d7a, 0x9b20, None, Some(offset!(-08:14))).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // From `2002-11-26 19:25:00 -08:14:59` to `2002-11-26 19:25:00 UTC`.
        //
        // When the UTC offset is not a multiple of 15 minute intervals, assumes the
        // provided date and time is in UTC.
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
}
