// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for comparing and ordering values.

use core::cmp::Ordering;
#[cfg(feature = "std")]
use std::time::SystemTime;

#[cfg(feature = "chrono")]
use chrono::{DateTime, Utc};
#[cfg(feature = "jiff")]
use jiff::Timestamp;
use time::UtcDateTime;

use super::FileTime;

#[cfg(feature = "std")]
impl PartialEq<FileTime> for SystemTime {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        self == &Self::from(*other)
    }
}

#[cfg(feature = "std")]
impl PartialEq<SystemTime> for FileTime {
    #[inline]
    fn eq(&self, other: &SystemTime) -> bool {
        &SystemTime::from(*self) == other
    }
}

impl PartialEq<FileTime> for UtcDateTime {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        self == &Self::try_from(*other).expect("`other` is out of range for `UtcDateTime`")
    }
}

impl PartialEq<UtcDateTime> for FileTime {
    #[inline]
    fn eq(&self, other: &UtcDateTime) -> bool {
        &UtcDateTime::try_from(*self).expect("`self` is out of range for `UtcDateTime`") == other
    }
}

#[cfg(feature = "chrono")]
impl PartialEq<FileTime> for DateTime<Utc> {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        self == &Self::from(*other)
    }
}

#[cfg(feature = "chrono")]
impl PartialEq<DateTime<Utc>> for FileTime {
    #[inline]
    fn eq(&self, other: &DateTime<Utc>) -> bool {
        &DateTime::<Utc>::from(*self) == other
    }
}

#[cfg(feature = "jiff")]
impl PartialEq<FileTime> for Timestamp {
    #[inline]
    fn eq(&self, other: &FileTime) -> bool {
        self == &Self::try_from(*other).expect("`other` is out of range for `Timestamp`")
    }
}

#[cfg(feature = "jiff")]
impl PartialEq<Timestamp> for FileTime {
    #[inline]
    fn eq(&self, other: &Timestamp) -> bool {
        &Timestamp::try_from(*self).expect("`self` is out of range for `Timestamp`") == other
    }
}

#[cfg(feature = "std")]
impl PartialOrd<FileTime> for SystemTime {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        self.partial_cmp(&Self::from(*other))
    }
}

#[cfg(feature = "std")]
impl PartialOrd<SystemTime> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &SystemTime) -> Option<Ordering> {
        SystemTime::from(*self).partial_cmp(other)
    }
}

impl PartialOrd<FileTime> for UtcDateTime {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        self.partial_cmp(
            &Self::try_from(*other).expect("`other` is out of range for `UtcDateTime`"),
        )
    }
}

impl PartialOrd<UtcDateTime> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &UtcDateTime) -> Option<Ordering> {
        UtcDateTime::try_from(*self)
            .expect("`self` is out of range for `UtcDateTime`")
            .partial_cmp(other)
    }
}

#[cfg(feature = "chrono")]
impl PartialOrd<FileTime> for DateTime<Utc> {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        self.partial_cmp(&Self::from(*other))
    }
}

#[cfg(feature = "chrono")]
impl PartialOrd<DateTime<Utc>> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &DateTime<Utc>) -> Option<Ordering> {
        DateTime::<Utc>::from(*self).partial_cmp(other)
    }
}

#[cfg(feature = "jiff")]
impl PartialOrd<FileTime> for Timestamp {
    #[inline]
    fn partial_cmp(&self, other: &FileTime) -> Option<Ordering> {
        self.partial_cmp(&Self::try_from(*other).expect("`other` is out of range for `Timestamp`"))
    }
}

#[cfg(feature = "jiff")]
impl PartialOrd<Timestamp> for FileTime {
    #[inline]
    fn partial_cmp(&self, other: &Timestamp) -> Option<Ordering> {
        Timestamp::try_from(*self)
            .expect("`self` is out of range for `Timestamp`")
            .partial_cmp(other)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use std::time::Duration;

    #[cfg(feature = "jiff")]
    use jiff::ToSpan;
    use time::macros::utc_datetime;

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
    fn equality_utc_date_time_and_file_time() {
        assert_eq!(
            utc_datetime!(9999-12-31 23:59:59.999_999_900),
            FileTime::new(2_650_467_743_999_999_999)
        );
        assert_ne!(
            utc_datetime!(9999-12-31 23:59:59.999_999_900),
            FileTime::NT_TIME_EPOCH
        );
        assert_ne!(
            utc_datetime!(1601-01-01 00:00:00),
            FileTime::new(2_650_467_743_999_999_999)
        );
        assert_eq!(utc_datetime!(1601-01-01 00:00:00), FileTime::NT_TIME_EPOCH);
    }

    #[test]
    fn equality_file_time_and_utc_date_time() {
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999),
            utc_datetime!(9999-12-31 23:59:59.999_999_900)
        );
        assert_ne!(
            FileTime::NT_TIME_EPOCH,
            utc_datetime!(9999-12-31 23:59:59.999_999_900)
        );
        assert_ne!(
            FileTime::new(2_650_467_743_999_999_999),
            utc_datetime!(1601-01-01 00:00:00)
        );
        assert_eq!(FileTime::NT_TIME_EPOCH, utc_datetime!(1601-01-01 00:00:00));
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn equality_chrono_date_time_and_file_time() {
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

    #[cfg(feature = "jiff")]
    #[test]
    fn equality_jiff_timestamp_and_file_time() {
        assert_eq!(
            Timestamp::MAX - 99.nanoseconds(),
            FileTime::new(2_650_466_808_009_999_999)
        );
        assert_ne!(Timestamp::MAX - 99.nanoseconds(), FileTime::NT_TIME_EPOCH);
        assert_ne!(
            Timestamp::from_second(-11_644_473_600).unwrap(),
            FileTime::new(2_650_466_808_009_999_999)
        );
        assert_eq!(
            Timestamp::from_second(-11_644_473_600).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn equality_file_time_and_jiff_timestamp() {
        assert_eq!(
            FileTime::new(2_650_466_808_009_999_999),
            Timestamp::MAX - 99.nanoseconds()
        );
        assert_ne!(FileTime::NT_TIME_EPOCH, Timestamp::MAX - 99.nanoseconds());
        assert_ne!(
            FileTime::new(2_650_466_808_009_999_999),
            Timestamp::from_second(-11_644_473_600).unwrap()
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH,
            Timestamp::from_second(-11_644_473_600).unwrap()
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn order_system_time_and_file_time() {
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
    fn order_utc_date_time_and_file_time() {
        assert!(UtcDateTime::UNIX_EPOCH < FileTime::new(2_650_467_743_999_999_999));
        assert_eq!(
            UtcDateTime::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(UtcDateTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
    }

    #[test]
    fn order_file_time_and_utc_date_time() {
        assert!(FileTime::UNIX_EPOCH < utc_datetime!(9999-12-31 23:59:59.999_999_900));
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&UtcDateTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(FileTime::UNIX_EPOCH > utc_datetime!(1601-01-01 00:00:00));
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn order_chrono_date_time_and_file_time() {
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

    #[cfg(feature = "jiff")]
    #[test]
    fn order_jiff_timestamp_and_file_time() {
        assert!(Timestamp::UNIX_EPOCH < FileTime::new(2_650_466_808_009_999_999));
        assert_eq!(
            Timestamp::UNIX_EPOCH.partial_cmp(&FileTime::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(Timestamp::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn order_file_time_and_jiff_timestamp() {
        assert!(FileTime::UNIX_EPOCH < Timestamp::MAX);
        assert_eq!(
            FileTime::UNIX_EPOCH.partial_cmp(&Timestamp::UNIX_EPOCH),
            Some(Ordering::Equal)
        );
        assert!(FileTime::UNIX_EPOCH > Timestamp::from_second(-11_644_473_600).unwrap());
    }
}
