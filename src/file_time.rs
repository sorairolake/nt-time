// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A [Windows file time].
//!
//! [Windows file time]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times

mod cmp;
mod consts;
mod convert;
mod dos_date_time;
mod fmt;
mod ops;
#[cfg(feature = "serde")]
mod serde;
mod unix_time;

use core::{mem, str::FromStr};

use crate::error::ParseFileTimeError;

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
}
