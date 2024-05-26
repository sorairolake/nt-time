// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for comparing and ordering values.

use core::cmp::Ordering;

use time::OffsetDateTime;

use super::FileTime;

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

#[cfg(feature = "zip")]
impl PartialEq<FileTime> for zip::DateTime {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        &FileTime::from(*self) == other
    }
}

#[cfg(feature = "zip")]
impl PartialEq<zip::DateTime> for FileTime {
    #[inline]
    fn eq(&self, other: &zip::DateTime) -> bool {
        self == &Self::from(*other)
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

#[cfg(feature = "zip")]
impl PartialOrd<FileTime> for zip::DateTime {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        FileTime::from(*self).partial_cmp(other)
    }
}

#[cfg(feature = "zip")]
impl PartialOrd<zip::DateTime> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &zip::DateTime) -> Option<Ordering> {
        self.partial_cmp(&Self::from(*other))
    }
}

#[cfg(test)]
mod tests {
    use time::macros::datetime;

    use super::*;

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
        assert!(FileTime::UNIX_EPOCH < FileTime::MAX);
        assert_eq!(
            FileTime::UNIX_EPOCH.cmp(&FileTime::UNIX_EPOCH),
            Ordering::Equal
        );
        assert!(FileTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
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

    #[cfg(feature = "zip")]
    #[test]
    fn equality_zip_date_time_and_file_time() {
        use zip::DateTime;

        assert_eq!(
            DateTime::from_date_and_time(2107, 12, 31, 23, 59, 58).unwrap(),
            FileTime::new(159_992_927_980_000_000)
        );
        assert_ne!(
            DateTime::from_date_and_time(2107, 12, 31, 23, 59, 58).unwrap(),
            FileTime::new(119_600_064_000_000_000)
        );
        assert_ne!(
            DateTime::from_date_and_time(1980, 1, 1, 0, 0, 0).unwrap(),
            FileTime::new(159_992_927_980_000_000)
        );
        assert_eq!(
            DateTime::from_date_and_time(1980, 1, 1, 0, 0, 0).unwrap(),
            FileTime::new(119_600_064_000_000_000)
        );
    }

    #[cfg(feature = "zip")]
    #[test]
    fn equality_file_time_and_zip_date_time() {
        use zip::DateTime;

        assert_eq!(
            FileTime::new(159_992_927_980_000_000),
            DateTime::from_date_and_time(2107, 12, 31, 23, 59, 58).unwrap()
        );
        assert_ne!(
            FileTime::new(119_600_064_000_000_000),
            DateTime::from_date_and_time(2107, 12, 31, 23, 59, 58).unwrap()
        );
        assert_ne!(
            FileTime::new(159_992_927_980_000_000),
            DateTime::from_date_and_time(1980, 1, 1, 0, 0, 0).unwrap()
        );
        assert_eq!(
            FileTime::new(119_600_064_000_000_000),
            DateTime::from_date_and_time(1980, 1, 1, 0, 0, 0).unwrap()
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn order_system_time_and_file_time() {
        use std::time::SystemTime;

        assert!(SystemTime::UNIX_EPOCH < FileTime::new(9_223_372_036_854_775_807));
        assert_eq!(
            SystemTime::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(SystemTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
    }

    #[cfg(feature = "std")]
    #[test]
    fn order_file_time_and_system_time() {
        use std::time::{Duration, SystemTime};

        assert!(
            FileTime::UNIX_EPOCH
                < (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&SystemTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(
            FileTime::UNIX_EPOCH
                > (SystemTime::UNIX_EPOCH - (FileTime::UNIX_EPOCH - FileTime::NT_TIME_EPOCH))
        );
    }

    #[test]
    fn order_offset_date_time_and_file_time() {
        assert!(OffsetDateTime::UNIX_EPOCH < FileTime::new(2_650_467_743_999_999_999));
        assert_eq!(
            OffsetDateTime::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(OffsetDateTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
    }

    #[test]
    fn order_file_time_and_offset_date_time() {
        assert!(FileTime::UNIX_EPOCH < datetime!(9999-12-31 23:59:59.999_999_900 UTC));
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&OffsetDateTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(FileTime::UNIX_EPOCH > datetime!(1601-01-01 00:00 UTC));
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn order_chrono_date_time_and_file_time() {
        use chrono::{DateTime, Utc};

        assert!(DateTime::<Utc>::UNIX_EPOCH < FileTime::MAX);
        assert_eq!(
            DateTime::<Utc>::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(DateTime::<Utc>::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn order_file_time_and_chrono_date_time() {
        use chrono::{DateTime, Utc};

        assert!(
            FileTime::UNIX_EPOCH
                < "+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
        );
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&DateTime::<Utc>::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(FileTime::UNIX_EPOCH > "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap());
    }

    #[cfg(feature = "zip")]
    #[test]
    fn order_zip_date_time_and_file_time() {
        use zip::DateTime;

        assert!(
            DateTime::from_date_and_time(2018, 11, 17, 10, 38, 30).unwrap()
                < FileTime::new(159_992_927_980_000_000)
        );
        assert_eq!(
            DateTime::from_date_and_time(2018, 11, 17, 10, 38, 30)
                .unwrap()
                .partial_cmp(&FileTime::new(131_869_247_100_000_000)),
            Some(Ordering::Equal)
        );
        assert!(
            DateTime::from_date_and_time(2018, 11, 17, 10, 38, 30).unwrap()
                > FileTime::new(119_600_064_000_000_000)
        );
    }

    #[cfg(feature = "zip")]
    #[test]
    fn order_file_time_and_zip_date_time() {
        use zip::DateTime;

        assert!(
            FileTime::new(131_869_247_100_000_000)
                < DateTime::from_date_and_time(2107, 12, 31, 23, 59, 58).unwrap()
        );
        assert_eq!(
            FileTime::new(131_869_247_100_000_000)
                .partial_cmp(&DateTime::from_date_and_time(2018, 11, 17, 10, 38, 30).unwrap()),
            Some(Ordering::Equal)
        );
        assert!(
            FileTime::new(131_869_247_100_000_000)
                > DateTime::from_date_and_time(1980, 1, 1, 0, 0, 0).unwrap()
        );
    }
}
