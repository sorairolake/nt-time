// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`FileTime`] and [MS-DOS date and
//! time].
//!
//! [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time

use time::{Date, OffsetDateTime, Time, error::ComponentRange};

use super::FileTime;
use crate::error::{DosDateTimeRangeError, DosDateTimeRangeErrorKind};

impl FileTime {
    #[allow(clippy::missing_panics_doc)]
    /// Returns [MS-DOS date and time] which represents the same date and time
    /// as this `FileTime`. This date and time is used as the timestamp such as
    /// [FAT] or [ZIP] file format.
    ///
    /// This method returns a `(date, time)` tuple if the result is [`Ok`].
    ///
    /// `date` and `time` represents the local date and time, and has no notion
    /// of time zone.
    ///
    /// <div class="warning">
    ///
    /// The resolution of MS-DOS date and time is 2 seconds. So this method
    /// rounds towards zero, truncating any fractional part of the exact result
    /// of dividing seconds by 2.
    ///
    /// </div>
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the resulting date and time are out of range for
    /// MS-DOS date and time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// // From `1980-01-01 00:00:00 UTC` to `1980-01-01 00:00:00`.
    /// assert_eq!(
    ///     FileTime::new(119_600_064_000_000_000).to_dos_date_time(),
    ///     Ok((0b0000_0000_0010_0001, u16::MIN))
    /// );
    /// // From `2107-12-31 23:59:59 UTC` to `2107-12-31 23:59:58`.
    /// assert_eq!(
    ///     FileTime::new(159_992_927_990_000_000).to_dos_date_time(),
    ///     Ok((0b1111_1111_1001_1111, 0b1011_1111_0111_1101))
    /// );
    ///
    /// // Before `1980-01-01 00:00:00 UTC`.
    /// assert!(
    ///     FileTime::new(119_600_063_990_000_000)
    ///         .to_dos_date_time()
    ///         .is_err()
    /// );
    /// // After `2107-12-31 23:59:59.999999900 UTC`.
    /// assert!(
    ///     FileTime::new(159_992_928_000_000_000)
    ///         .to_dos_date_time()
    ///         .is_err()
    /// );
    /// ```
    ///
    /// [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time
    /// [FAT]: https://en.wikipedia.org/wiki/File_Allocation_Table
    /// [ZIP]: https://en.wikipedia.org/wiki/ZIP_(file_format)
    pub fn to_dos_date_time(self) -> Result<(u16, u16), DosDateTimeRangeError> {
        let dt = OffsetDateTime::try_from(self).map_err(|_| DosDateTimeRangeErrorKind::Overflow)?;

        match dt.year() {
            ..=1979 => Err(DosDateTimeRangeErrorKind::Negative.into()),
            2108.. => Err(DosDateTimeRangeErrorKind::Overflow.into()),
            year => {
                let (year, month, day) = (
                    u16::try_from(year - 1980).expect("year should be in the range of `u16`"),
                    u16::from(u8::from(dt.month())),
                    u16::from(dt.day()),
                );
                let date = (year << 9) | (month << 5) | day;

                let (hour, minute, second) = (
                    u16::from(dt.hour()),
                    u16::from(dt.minute()),
                    u16::from(dt.second() / 2),
                );
                // <https://learn.microsoft.com/en-us/windows/win32/fileio/exfat-specification#7481-doubleseconds-field>.
                let second = second.min(29);
                let time = (hour << 11) | (minute << 5) | second;

                Ok((date, time))
            }
        }
    }

    #[allow(clippy::missing_panics_doc)]
    /// Creates a `FileTime` with the given [MS-DOS date and time]. This date
    /// and time is used as the timestamp such as [FAT] or [ZIP] file format.
    ///
    /// <div class="warning">
    ///
    /// The time zone for the local date and time are assumed to be UTC.
    ///
    /// </div>
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `date` or `time` is invalid date and time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// // From `1980-01-01 00:00:00` to `1980-01-01 00:00:00 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0b0000_0000_0010_0001, u16::MIN),
    ///     Ok(FileTime::new(119_600_064_000_000_000))
    /// );
    /// // From `2107-12-31 23:59:58` to `2107-12-31 23:59:58 UTC`.
    /// assert_eq!(
    ///     FileTime::from_dos_date_time(0b1111_1111_1001_1111, 0b1011_1111_0111_1101),
    ///     Ok(FileTime::new(159_992_927_980_000_000))
    /// );
    ///
    /// // The Day field is 0.
    /// assert!(FileTime::from_dos_date_time(0b0000_0000_0010_0000, u16::MIN).is_err());
    /// // The DoubleSeconds field is 30.
    /// assert!(FileTime::from_dos_date_time(0b0000_0000_0010_0001, 0b0000_0000_0001_1110).is_err());
    /// ```
    ///
    /// [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time
    /// [FAT]: https://en.wikipedia.org/wiki/File_Allocation_Table
    /// [ZIP]: https://en.wikipedia.org/wiki/ZIP_(file_format)
    pub fn from_dos_date_time(date: u16, time: u16) -> Result<Self, ComponentRange> {
        let (year, month, day) = (
            (1980 + (date >> 9)).into(),
            u8::try_from((date >> 5) & 0x0f)
                .expect("month should be in the range of `u8`")
                .try_into()?,
            (date & 0x1f)
                .try_into()
                .expect("day should be in the range of `u8`"),
        );
        let date = Date::from_calendar_date(year, month, day)?;

        let (hour, minute, second) = (
            (time >> 11)
                .try_into()
                .expect("hour should be in the range of `u8`"),
            ((time >> 5) & 0x3f)
                .try_into()
                .expect("minute should be in the range of `u8`"),
            ((time & 0x1f) * 2)
                .try_into()
                .expect("second should be in the range of `u8`"),
        );
        let time = Time::from_hms(hour, minute, second)?;

        let ft = OffsetDateTime::new_utc(date, time)
            .try_into()
            .expect("MS-DOS date and time should be in the range of `FileTime`");
        Ok(ft)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use proptest::{prop_assert, prop_assert_eq, prop_assume};
    #[cfg(feature = "std")]
    use test_strategy::proptest;

    use super::*;

    #[test]
    fn to_dos_date_time_before_dos_date_time_epoch() {
        // `1979-12-31 23:59:58 UTC`.
        assert_eq!(
            FileTime::new(119_600_063_980_000_000)
                .to_dos_date_time()
                .unwrap_err(),
            DosDateTimeRangeErrorKind::Negative.into()
        );
        // `1979-12-31 23:59:59 UTC`.
        assert_eq!(
            FileTime::new(119_600_063_990_000_000)
                .to_dos_date_time()
                .unwrap_err(),
            DosDateTimeRangeErrorKind::Negative.into()
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn to_dos_date_time_before_dos_date_time_epoch_roundtrip(
        #[strategy(..=119_600_063_980_000_000_u64)] ft: u64,
    ) {
        prop_assert_eq!(
            FileTime::new(ft).to_dos_date_time().unwrap_err(),
            DosDateTimeRangeErrorKind::Negative.into()
        );
    }

    #[test]
    fn to_dos_date_time() {
        // From `1980-01-01 00:00:00 UTC` to `1980-01-01 00:00:00`.
        assert_eq!(
            FileTime::new(119_600_064_000_000_000)
                .to_dos_date_time()
                .unwrap(),
            (0b0000_0000_0010_0001, u16::MIN)
        );
        // From `1980-01-01 00:00:01 UTC` to `1980-01-01 00:00:00`.
        assert_eq!(
            FileTime::new(119_600_064_010_000_000)
                .to_dos_date_time()
                .unwrap(),
            (0b0000_0000_0010_0001, u16::MIN)
        );
        // <https://devblogs.microsoft.com/oldnewthing/20030905-02/?p=42653>.
        //
        // From `2002-11-27 03:25:00 UTC` to `2002-11-27 03:25:00`.
        assert_eq!(
            FileTime::new(126_828_411_000_000_000)
                .to_dos_date_time()
                .unwrap(),
            (0b0010_1101_0111_1011, 0b0001_1011_0010_0000)
        );
        // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
        //
        // From `2018-11-17 10:38:30 UTC` to `2018-11-17 10:38:30`.
        assert_eq!(
            FileTime::new(131_869_247_100_000_000)
                .to_dos_date_time()
                .unwrap(),
            (0b0100_1101_0111_0001, 0b0101_0100_1100_1111)
        );
        // From `2107-12-31 23:59:58 UTC` to `2107-12-31 23:59:58`.
        assert_eq!(
            FileTime::new(159_992_927_980_000_000)
                .to_dos_date_time()
                .unwrap(),
            (0b1111_1111_1001_1111, 0b1011_1111_0111_1101)
        );
        // From `2107-12-31 23:59:59 UTC` to `2107-12-31 23:59:58`.
        assert_eq!(
            FileTime::new(159_992_927_990_000_000)
                .to_dos_date_time()
                .unwrap(),
            (0b1111_1111_1001_1111, 0b1011_1111_0111_1101)
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn to_dos_date_time_roundtrip(
        #[strategy(119_600_064_000_000_000..=159_992_927_980_000_000_u64)] ft: u64,
    ) {
        prop_assert!(FileTime::new(ft).to_dos_date_time().is_ok());
    }

    #[test]
    fn to_dos_date_time_with_too_big_date_time() {
        // `2108-01-01 00:00:00 UTC`.
        assert_eq!(
            FileTime::new(159_992_928_000_000_000)
                .to_dos_date_time()
                .unwrap_err(),
            DosDateTimeRangeErrorKind::Overflow.into()
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn to_dos_date_time_with_too_big_date_time_roundtrip(
        #[strategy(159_992_928_000_000_000_u64..)] ft: u64,
    ) {
        prop_assert_eq!(
            FileTime::new(ft).to_dos_date_time().unwrap_err(),
            DosDateTimeRangeErrorKind::Overflow.into()
        );
    }

    #[test]
    fn from_dos_date_time() {
        // From `1980-01-01 00:00:00` to `1980-01-01 00:00:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0b0000_0000_0010_0001, u16::MIN).unwrap(),
            FileTime::new(119_600_064_000_000_000)
        );
        // <https://devblogs.microsoft.com/oldnewthing/20030905-02/?p=42653>.
        //
        // From `2002-11-26 19:25:00` to `2002-11-26 19:25:00 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0b0010_1101_0111_1010, 0b1001_1011_0010_0000).unwrap(),
            FileTime::new(126_828_123_000_000_000)
        );
        // <https://github.com/zip-rs/zip/blob/v0.6.4/src/types.rs#L553-L569>.
        //
        // From `2018-11-17 10:38:30` to `2018-11-17 10:38:30 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0b0100_1101_0111_0001, 0b0101_0100_1100_1111).unwrap(),
            FileTime::new(131_869_247_100_000_000)
        );
        // From `2107-12-31 23:59:58` to `2107-12-31 23:59:58 UTC`.
        assert_eq!(
            FileTime::from_dos_date_time(0b1111_1111_1001_1111, 0b1011_1111_0111_1101).unwrap(),
            FileTime::new(159_992_927_980_000_000)
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_dos_date_time_roundtrip(
        #[strategy(1980..=2107_u16)] year: u16,
        #[strategy(1..=12_u8)] month: u8,
        #[strategy(1..=31_u8)] day: u8,
        #[strategy(..=23_u8)] hour: u8,
        #[strategy(..=59_u8)] minute: u8,
        #[strategy(..=58_u8)] second: u8,
    ) {
        prop_assume!(Date::from_calendar_date(year.into(), month.try_into().unwrap(), day).is_ok());
        prop_assume!(Time::from_hms(hour, minute, second).is_ok());

        let (year, month, day) = (year - 1980, u16::from(month), u16::from(day));
        let date = (year << 9) | (month << 5) | day;

        let (hour, minute, second) = (u16::from(hour), u16::from(minute), u16::from(second / 2));
        let time = (hour << 11) | (minute << 5) | second;

        prop_assert!(FileTime::from_dos_date_time(date, time).is_ok());
    }

    #[test]
    fn from_dos_date_time_with_invalid_date_time() {
        // The Day field is 0.
        assert!(FileTime::from_dos_date_time(0b0000_0000_0010_0000, u16::MIN).is_err());
        // The Day field is 30, which is after the last day of February.
        assert!(FileTime::from_dos_date_time(0b0000_0000_0101_1110, u16::MIN).is_err());
        // The Month field is 0.
        assert!(FileTime::from_dos_date_time(0b0000_0000_0000_0001, u16::MIN).is_err());
        // The Month field is 13.
        assert!(FileTime::from_dos_date_time(0b0000_0001_1010_0001, u16::MIN).is_err());

        // The DoubleSeconds field is 30.
        assert!(
            FileTime::from_dos_date_time(0b0000_0000_0010_0001, 0b0000_0000_0001_1110).is_err()
        );
        // The Minute field is 60.
        assert!(
            FileTime::from_dos_date_time(0b0000_0000_0010_0001, 0b0000_0111_1000_0000).is_err()
        );
        // The Hour field is 24.
        assert!(
            FileTime::from_dos_date_time(0b0000_0000_0010_0001, 0b1100_0000_0000_0000).is_err()
        );
    }
}
