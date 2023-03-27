//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! The [Windows NT system time][file-time-docs-url].
//!
//! [file-time-docs-url]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times

use time::{macros::datetime, OffsetDateTime};

use crate::error;

/// `FileTime` is a type that represents the [Windows NT system
/// time][file-time-docs-url].
///
/// This is a 64-bit unsigned integer value that represents the number of
/// 100-nanosecond intervals that have elapsed since "1601-01-01 00:00:00 UTC".
///
/// [file-time-docs-url]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileTime(u64);

impl FileTime {
    /// The NT time epoch.
    ///
    /// This is defined as "1601-01-01 00:00:00 UTC".
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// # use time::{macros::datetime, OffsetDateTime};
    /// #
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::NT_EPOCH).unwrap(),
    ///     datetime!(1601-01-01 00:00 UTC)
    /// );
    /// ```
    pub const NT_EPOCH: Self = Self(u64::MIN);

    /// The largest value that can be represented by the Windows NT system time.
    ///
    /// This is "+60056-05-28 05:36:10.955161500 UTC".
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// # use time::{macros::datetime, OffsetDateTime};
    /// #
    /// # #[cfg(feature = "large-dates")]
    /// assert_eq!(
    ///     OffsetDateTime::try_from(FileTime::MAX).unwrap(),
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
    /// );
    /// ```
    pub const MAX: Self = Self(u64::MAX);

    /// Creates a new `FileTime` with the given Windows NT system time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::new(u64::MIN), FileTime::NT_EPOCH);
    /// assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn new(time: u64) -> Self {
        Self(time)
    }

    /// Converts a `FileTime` to the Windows NT system time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_EPOCH.as_u64(), u64::MIN);
    /// assert_eq!(FileTime::MAX.as_u64(), u64::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_u64(self) -> u64 {
        self.0
    }
}

impl Default for FileTime {
    /// Returns the default value of "1601-01-01 00:00:00 UTC".
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::default(), FileTime::NT_EPOCH);
    /// ```
    #[inline]
    fn default() -> Self {
        Self::NT_EPOCH
    }
}

impl From<FileTime> for u64 {
    /// Converts a `FileTime` to the Windows NT system time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(u64::from(FileTime::NT_EPOCH), u64::MIN);
    /// assert_eq!(u64::from(FileTime::MAX), u64::MAX);
    /// ```
    #[inline]
    fn from(time: FileTime) -> Self {
        time.as_u64()
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl TryFrom<FileTime> for std::time::SystemTime {
    type Error = error::OffsetDateTimeRangeError;

    /// Converts a `FileTime` to a [`SystemTime`](std::time::SystemTime).
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the `large-dates` feature is disabled and `time` is
    /// out of range of [`OffsetDateTime`].
    fn try_from(time: FileTime) -> Result<Self, Self::Error> {
        let dt = OffsetDateTime::try_from(time)?;
        Ok(Self::from(dt))
    }
}

impl TryFrom<FileTime> for OffsetDateTime {
    type Error = error::OffsetDateTimeRangeError;

    /// Converts a `FileTime` to a [`OffsetDateTime`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the `large-dates` feature is disabled and `time` is
    /// out of range of [`OffsetDateTime`].
    fn try_from(time: FileTime) -> Result<Self, Self::Error> {
        const NT_EPOCH: OffsetDateTime = datetime!(1601-01-01 00:00 UTC);
        let duration = time::Duration::new(
            i64::try_from(time.0 / 10_000_000)
                .expect("the number of seconds should be in the range of `i64`"),
            i32::try_from((time.0 % 10_000_000) * 100)
                .expect("the number of nanoseconds should be in the range of `i32`"),
        );
        NT_EPOCH
            .checked_add(duration)
            .ok_or(error::OffsetDateTimeRangeError)
    }
}

impl From<u64> for FileTime {
    /// Converts the Windows NT system time to a `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::from(u64::MIN), FileTime::NT_EPOCH);
    /// assert_eq!(FileTime::from(u64::MAX), FileTime::MAX);
    /// ```
    #[inline]
    fn from(time: u64) -> Self {
        Self::new(time)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl TryFrom<std::time::SystemTime> for FileTime {
    type Error = error::FileTimeRangeError;

    /// Converts a [`SystemTime`](std::time::SystemTime) to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `time` is out of range of the Windows NT system time.
    fn try_from(time: std::time::SystemTime) -> Result<Self, Self::Error> {
        Self::try_from(OffsetDateTime::from(time))
    }
}

impl TryFrom<OffsetDateTime> for FileTime {
    type Error = error::FileTimeRangeError;

    /// Converts a [`OffsetDateTime`] to a `FileTime`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `dt` is out of range of the Windows NT system time.
    fn try_from(dt: OffsetDateTime) -> Result<Self, Self::Error> {
        const NT_EPOCH: OffsetDateTime = datetime!(1601-01-01 00:00 UTC);
        let elapsed = core::time::Duration::try_from(dt - NT_EPOCH)
            .map(|d| d.as_nanos())
            .map_err(|_| error::FileTimeRangeError::new(error::FileTimeRangeErrorKind::Negative))?;
        let ft = u64::try_from(elapsed / 100)
            .map_err(|_| error::FileTimeRangeError::new(error::FileTimeRangeErrorKind::Overflow))?;
        Ok(Self(ft))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clone() {
        assert_eq!(FileTime::NT_EPOCH.clone(), FileTime::NT_EPOCH);
    }

    #[test]
    fn copy() {
        let a = FileTime::NT_EPOCH;
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", FileTime::NT_EPOCH), "FileTime(0)");
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
                FileTime::NT_EPOCH.hash(&mut hasher);
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
    fn ord() {
        use core::cmp::Ordering;

        assert_eq!(FileTime::NT_EPOCH.cmp(&FileTime::MAX), Ordering::Less);
        assert_eq!(FileTime::NT_EPOCH.cmp(&FileTime::NT_EPOCH), Ordering::Equal);
        assert_eq!(FileTime::MAX.cmp(&FileTime::NT_EPOCH), Ordering::Greater);
    }

    #[test]
    fn partial_eq() {
        assert!(FileTime::NT_EPOCH == FileTime::NT_EPOCH);
    }

    #[test]
    fn partial_ord() {
        use core::cmp::Ordering;

        assert_eq!(
            FileTime::NT_EPOCH.partial_cmp(&FileTime::MAX),
            Some(Ordering::Less)
        );
        assert_eq!(
            FileTime::NT_EPOCH.partial_cmp(&FileTime::NT_EPOCH),
            Some(Ordering::Equal)
        );
        assert_eq!(
            FileTime::MAX.partial_cmp(&FileTime::NT_EPOCH),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn nt_epoch() {
        assert_eq!(
            OffsetDateTime::try_from(FileTime::NT_EPOCH).unwrap(),
            datetime!(1601-01-01 00:00 UTC)
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

    #[test]
    fn new() {
        assert_eq!(FileTime::new(u64::MIN), FileTime::NT_EPOCH);
        assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
    }

    #[test]
    fn as_u64() {
        assert_eq!(FileTime::NT_EPOCH.as_u64(), u64::MIN);
        assert_eq!(FileTime::MAX.as_u64(), u64::MAX);
    }

    #[test]
    fn default_file_time() {
        assert_eq!(FileTime::default(), FileTime::NT_EPOCH);
    }

    #[test]
    fn from_file_time_to_u64() {
        assert_eq!(u64::from(FileTime::NT_EPOCH), u64::MIN);
        assert_eq!(u64::from(FileTime::MAX), u64::MAX);
    }

    #[cfg(feature = "std")]
    #[test]
    fn try_from_file_time_to_system_time() {
        assert_eq!(
            std::time::SystemTime::try_from(FileTime(116_444_736_000_000_000)).unwrap(),
            std::time::UNIX_EPOCH
        );
    }

    #[test]
    fn try_from_file_time_to_offset_date_time() {
        assert_eq!(
            OffsetDateTime::try_from(FileTime::NT_EPOCH).unwrap(),
            datetime!(1601-01-01 00:00 UTC)
        );
        assert_eq!(
            OffsetDateTime::try_from(FileTime(116_444_736_000_000_000)).unwrap(),
            OffsetDateTime::UNIX_EPOCH
        );
        assert_eq!(
            OffsetDateTime::try_from(FileTime(2_650_467_743_999_999_999)).unwrap(),
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
        );
    }

    #[cfg(not(feature = "large-dates"))]
    #[test]
    fn try_from_file_time_to_offset_date_time_with_invalid_file_time() {
        let dt = OffsetDateTime::try_from(FileTime(2_650_467_744_000_000_000)).unwrap_err();
        assert_eq!(dt, error::OffsetDateTimeRangeError);
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_file_time_to_offset_date_time_with_large_dates() {
        assert_eq!(
            OffsetDateTime::try_from(FileTime::MAX).unwrap(),
            datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
        );
    }

    #[test]
    fn from_u64_to_file_time() {
        assert_eq!(FileTime::from(u64::MIN), FileTime::NT_EPOCH);
        assert_eq!(FileTime::from(u64::MAX), FileTime::MAX);
    }

    #[cfg(feature = "std")]
    #[test]
    fn try_from_system_time_to_file_time() {
        assert_eq!(
            FileTime::try_from(std::time::UNIX_EPOCH).unwrap(),
            FileTime(116_444_736_000_000_000)
        );
    }

    #[test]
    fn try_from_offset_date_time_to_file_time_before_epoch() {
        let ft = FileTime::try_from(datetime!(1601-01-01 00:00 UTC) - time::Duration::NANOSECOND)
            .unwrap_err();
        assert_eq!(
            ft,
            error::FileTimeRangeError::new(error::FileTimeRangeErrorKind::Negative)
        );
    }

    #[test]
    fn try_from_offset_date_time_to_file_time() {
        assert_eq!(
            FileTime::try_from(datetime!(1601-01-01 00:00 UTC)).unwrap(),
            FileTime::NT_EPOCH
        );
        assert_eq!(
            FileTime::try_from(OffsetDateTime::UNIX_EPOCH).unwrap(),
            FileTime(116_444_736_000_000_000)
        );
        assert_eq!(
            FileTime::try_from(datetime!(9999-12-31 23:59:59.999_999_999 UTC)).unwrap(),
            FileTime(2_650_467_743_999_999_999)
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_offset_date_time_to_file_time_with_large_dates() {
        assert_eq!(
            FileTime::try_from(datetime!(+60056-05-28 05:36:10.955_161_500 UTC)).unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn try_from_offset_date_time_to_file_time_with_too_big_date_time() {
        let ft = FileTime::try_from(
            datetime!(+60056-05-28 05:36:10.955_161_500 UTC) + time::Duration::nanoseconds(100),
        )
        .unwrap_err();
        assert_eq!(
            ft,
            error::FileTimeRangeError::new(error::FileTimeRangeErrorKind::Overflow)
        );
    }
}
