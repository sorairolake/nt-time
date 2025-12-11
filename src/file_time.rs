// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A [Windows file time].
//!
//! [Windows file time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/file-times

mod cmp;
mod consts;
mod convert;
mod dos_date_time;
mod fmt;
mod ops;
#[cfg(feature = "rand")]
mod rand;
#[cfg(feature = "serde")]
mod serde;
mod str;
mod unix_time;

use core::mem;
#[cfg(feature = "std")]
use std::time::SystemTime;

#[cfg(test)]
use proptest_derive::Arbitrary;

const FILE_TIMES_PER_SEC: u64 = 10_000_000;

/// `FileTime` is a type that represents a [Windows file time].
///
/// This is a 64-bit unsigned integer value that represents the number of
/// 100-nanosecond intervals that have elapsed since "1601-01-01 00:00:00 UTC",
/// and is used as timestamps such as [NTFS] and [7z]. Windows uses a file time
/// to record when an application creates, accesses, or writes to a file.
///
/// This represents the same value as the [`FILETIME`] structure of the [Win32
/// API], which represents a 64-bit unsigned integer value.
///
/// <div class="warning">
///
/// Note that many environments, such as the Win32 API, may limit the largest
/// value of the file time to "+30828-09-14 02:48:05.477580700 UTC", which is
/// equal to [`i64::MAX`], the largest value of a 64-bit signed integer type
/// when represented as an underlying integer value. This is the largest file
/// time accepted by the [`FileTimeToSystemTime`] function of the Win32 API.
///
/// </div>
///
/// Also, the file time is sometimes represented as an [`i64`] value, such as in
/// the [`DateTime.FromFileTimeUtc`] method and the [`DateTime.ToFileTimeUtc`]
/// method in [.NET].
///
/// Therefore, if you want the process to succeed in more environments, it is
/// generally recommended that you use [`FileTime::SIGNED_MAX`] as the largest
/// value instead of [`FileTime::MAX`].
///
/// [Windows file time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/file-times
/// [NTFS]: https://en.wikipedia.org/wiki/NTFS
/// [7z]: https://www.7-zip.org/7z.html
/// [`FILETIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-filetime
/// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
/// [`FileTimeToSystemTime`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-filetimetosystemtime
/// [`DateTime.FromFileTimeUtc`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.fromfiletimeutc
/// [`DateTime.ToFileTimeUtc`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.tofiletimeutc
/// [.NET]: https://dotnet.microsoft.com/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(test, derive(Arbitrary))]
#[repr(transparent)]
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
    #[inline]
    pub fn now() -> Self {
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
    /// assert_eq!(FileTime::new(i64::MAX as u64), FileTime::SIGNED_MAX);
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
    /// assert_eq!(FileTime::SIGNED_MAX.to_raw(), i64::MAX as u64);
    /// assert_eq!(FileTime::MAX.to_raw(), u64::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn to_raw(self) -> u64 {
        self.0
    }

    /// Returns the memory representation of this `FileTime` as a byte array in
    /// big-endian (network) byte order.
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
    /// assert_eq!(
    ///     FileTime::SIGNED_MAX.to_be_bytes(),
    ///     [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
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
    /// assert_eq!(
    ///     FileTime::SIGNED_MAX.to_le_bytes(),
    ///     [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
    /// );
    /// assert_eq!(FileTime::MAX.to_le_bytes(), [u8::MAX; 8]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn to_le_bytes(self) -> [u8; mem::size_of::<Self>()] {
        self.to_raw().to_le_bytes()
    }

    /// Returns the memory representation of this `FileTime` as a byte array in
    /// native byte order.
    ///
    /// <div class="warning">
    ///
    /// As the target platform's native endianness is used, portable code should
    /// use [`FileTime::to_be_bytes`] or [`FileTime::to_le_bytes`], as
    /// appropriate, instead.
    ///
    /// </div>
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_ne_bytes(), [u8::MIN; 8]);
    /// assert_eq!(
    ///     FileTime::UNIX_EPOCH.to_ne_bytes(),
    ///     if cfg!(target_endian = "big") {
    ///         [0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]
    ///     } else {
    ///         [0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]
    ///     }
    /// );
    /// assert_eq!(
    ///     FileTime::SIGNED_MAX.to_ne_bytes(),
    ///     if cfg!(target_endian = "big") {
    ///         [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
    ///     } else {
    ///         [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
    ///     }
    /// );
    /// assert_eq!(FileTime::MAX.to_ne_bytes(), [u8::MAX; 8]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn to_ne_bytes(self) -> [u8; mem::size_of::<Self>()] {
        self.to_raw().to_ne_bytes()
    }

    /// Creates a native endian `FileTime` value from its representation as a
    /// byte array in big endian.
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
    /// assert_eq!(
    ///     FileTime::from_be_bytes([0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
    ///     FileTime::SIGNED_MAX
    /// );
    /// assert_eq!(FileTime::from_be_bytes([u8::MAX; 8]), FileTime::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn from_be_bytes(bytes: [u8; mem::size_of::<Self>()]) -> Self {
        Self::new(u64::from_be_bytes(bytes))
    }

    /// Creates a native endian `FileTime` value from its representation as a
    /// byte array in little endian.
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
    /// assert_eq!(
    ///     FileTime::from_le_bytes([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
    ///     FileTime::SIGNED_MAX
    /// );
    /// assert_eq!(FileTime::from_le_bytes([u8::MAX; 8]), FileTime::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn from_le_bytes(bytes: [u8; mem::size_of::<Self>()]) -> Self {
        Self::new(u64::from_le_bytes(bytes))
    }

    /// Creates a native endian `FileTime` value from its memory representation
    /// as a byte array in native endianness.
    ///
    /// <div class="warning">
    ///
    /// As the target platform's native endianness is used, portable code likely
    /// wants to use [`FileTime::from_be_bytes`] or [`FileTime::from_le_bytes`],
    /// as appropriate instead.
    ///
    /// </div>
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_ne_bytes([u8::MIN; 8]),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_ne_bytes(if cfg!(target_endian = "big") {
    ///         [0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]
    ///     } else {
    ///         [0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]
    ///     }),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_ne_bytes(if cfg!(target_endian = "big") {
    ///         [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
    ///     } else {
    ///         [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
    ///     }),
    ///     FileTime::SIGNED_MAX
    /// );
    /// assert_eq!(FileTime::from_ne_bytes([u8::MAX; 8]), FileTime::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub const fn from_ne_bytes(bytes: [u8; mem::size_of::<Self>()]) -> Self {
        Self::new(u64::from_ne_bytes(bytes))
    }

    #[allow(clippy::cast_possible_truncation)]
    /// Returns the high-order and low-order parts of this `FileTime`.
    ///
    /// The first return value represents the high-order part of this
    /// `FileTime`, and the second return value represents the low-order part of
    /// this `FileTime`.
    ///
    /// The first return value corresponds to the `dwHighDateTime` member of the
    /// [`FILETIME`] structure of the [Win32 API], and the second return value
    /// corresponds to the `dwLowDateTime` member of the `FILETIME` structure.
    /// The data type of these members is [`DWORD`], a 32-bit unsigned integer
    /// type the same as [`u32`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH.to_high_low(), (u32::MIN, u32::MIN));
    /// assert_eq!(
    ///     FileTime::UNIX_EPOCH.to_high_low(),
    ///     (0x019d_b1de, 0xd53e_8000)
    /// );
    /// assert_eq!(
    ///     FileTime::SIGNED_MAX.to_high_low(),
    ///     (i32::MAX as u32, u32::MAX)
    /// );
    /// assert_eq!(FileTime::MAX.to_high_low(), (u32::MAX, u32::MAX));
    /// ```
    ///
    /// [`FILETIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-filetime
    /// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
    /// [`DWORD`]: https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-dtyp/262627d8-3418-4627-9218-4ffe110850b2
    #[must_use]
    #[inline]
    pub const fn to_high_low(self) -> (u32, u32) {
        let raw = self.to_raw();
        ((raw >> u32::BITS) as u32, raw as u32)
    }

    /// Creates a `FileTime` from [`u32`] values representing the high-order and
    /// low-order parts of the file time.
    ///
    /// `high` corresponds to the `dwHighDateTime` member of the [`FILETIME`]
    /// structure of the [Win32 API], and `low` corresponds to the
    /// `dwLowDateTime` member of the `FILETIME` structure. The data type of
    /// these members is [`DWORD`], a 32-bit unsigned integer type the same as
    /// [`u32`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_high_low(u32::MIN, u32::MIN),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_high_low(0x019d_b1de, 0xd53e_8000),
    ///     FileTime::UNIX_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::from_high_low(i32::MAX as u32, u32::MAX),
    ///     FileTime::SIGNED_MAX
    /// );
    /// assert_eq!(FileTime::from_high_low(u32::MAX, u32::MAX), FileTime::MAX);
    /// ```
    ///
    /// [`FILETIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-filetime
    /// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
    /// [`DWORD`]: https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-dtyp/262627d8-3418-4627-9218-4ffe110850b2
    #[must_use]
    #[inline]
    pub const fn from_high_low(high: u32, low: u32) -> Self {
        let raw = ((high as u64) << u32::BITS) | (low as u64);
        Self::new(raw)
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

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
    };

    #[cfg(feature = "std")]
    use proptest::prop_assert_eq;
    #[cfg(feature = "std")]
    use test_strategy::proptest;

    use super::*;

    #[test]
    fn size_of() {
        assert_eq!(mem::size_of::<FileTime>(), mem::size_of::<u64>());
    }

    #[test]
    fn align_of() {
        assert_eq!(mem::align_of::<FileTime>(), mem::align_of::<u64>());
    }

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
        assert_eq!(FileTime::new(i64::MAX as u64), FileTime::SIGNED_MAX);
        assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
    }

    #[test]
    const fn new_is_const_fn() {
        const _: FileTime = FileTime::new(u64::MIN);
    }

    #[test]
    fn to_raw() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_raw(), u64::MIN);
        assert_eq!(FileTime::UNIX_EPOCH.to_raw(), 116_444_736_000_000_000);
        assert_eq!(FileTime::SIGNED_MAX.to_raw(), i64::MAX as u64);
        assert_eq!(FileTime::MAX.to_raw(), u64::MAX);
    }

    #[test]
    const fn to_raw_is_const_fn() {
        const _: u64 = FileTime::NT_TIME_EPOCH.to_raw();
    }

    #[test]
    fn to_be_bytes() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_be_bytes(), [u8::MIN; 8]);
        assert_eq!(
            FileTime::UNIX_EPOCH.to_be_bytes(),
            [0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]
        );
        assert_eq!(
            FileTime::SIGNED_MAX.to_be_bytes(),
            [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
        );
        assert_eq!(FileTime::MAX.to_be_bytes(), [u8::MAX; 8]);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn to_be_bytes_roundtrip(ft: FileTime) {
        prop_assert_eq!(ft.to_be_bytes(), ft.to_raw().to_be_bytes());
    }

    #[test]
    const fn to_be_bytes_is_const_fn() {
        const _: [u8; 8] = FileTime::NT_TIME_EPOCH.to_be_bytes();
    }

    #[test]
    fn to_le_bytes() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_le_bytes(), [u8::MIN; 8]);
        assert_eq!(
            FileTime::UNIX_EPOCH.to_le_bytes(),
            [0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]
        );
        assert_eq!(
            FileTime::SIGNED_MAX.to_le_bytes(),
            [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
        );
        assert_eq!(FileTime::MAX.to_le_bytes(), [u8::MAX; 8]);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn to_le_bytes_roundtrip(ft: FileTime) {
        prop_assert_eq!(ft.to_le_bytes(), ft.to_raw().to_le_bytes());
    }

    #[test]
    const fn to_le_bytes_is_const_fn() {
        const _: [u8; 8] = FileTime::NT_TIME_EPOCH.to_le_bytes();
    }

    #[test]
    fn to_ne_bytes() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_ne_bytes(), [u8::MIN; 8]);
        assert_eq!(
            FileTime::UNIX_EPOCH.to_ne_bytes(),
            if cfg!(target_endian = "big") {
                [0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]
            } else {
                [0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]
            }
        );
        assert_eq!(
            FileTime::SIGNED_MAX.to_ne_bytes(),
            if cfg!(target_endian = "big") {
                [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
            } else {
                [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
            }
        );
        assert_eq!(FileTime::MAX.to_ne_bytes(), [u8::MAX; 8]);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn to_ne_bytes_roundtrip(ft: FileTime) {
        prop_assert_eq!(ft.to_ne_bytes(), ft.to_raw().to_ne_bytes());
    }

    #[test]
    const fn to_ne_bytes_is_const_fn() {
        const _: [u8; 8] = FileTime::NT_TIME_EPOCH.to_ne_bytes();
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
        assert_eq!(
            FileTime::from_be_bytes([0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
            FileTime::SIGNED_MAX
        );
        assert_eq!(FileTime::from_be_bytes([u8::MAX; 8]), FileTime::MAX);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_be_bytes_roundtrip(bytes: [u8; mem::size_of::<FileTime>()]) {
        prop_assert_eq!(
            FileTime::from_be_bytes(bytes),
            FileTime::new(u64::from_be_bytes(bytes))
        );
    }

    #[test]
    const fn from_be_bytes_is_const_fn() {
        const _: FileTime = FileTime::from_be_bytes([u8::MIN; 8]);
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
        assert_eq!(
            FileTime::from_le_bytes([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
            FileTime::SIGNED_MAX
        );
        assert_eq!(FileTime::from_le_bytes([u8::MAX; 8]), FileTime::MAX);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_le_bytes_roundtrip(bytes: [u8; mem::size_of::<FileTime>()]) {
        prop_assert_eq!(
            FileTime::from_le_bytes(bytes),
            FileTime::new(u64::from_le_bytes(bytes))
        );
    }

    #[test]
    const fn from_le_bytes_is_const_fn() {
        const _: FileTime = FileTime::from_le_bytes([u8::MIN; 8]);
    }

    #[test]
    fn from_ne_bytes() {
        assert_eq!(
            FileTime::from_ne_bytes([u8::MIN; 8]),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_ne_bytes(if cfg!(target_endian = "big") {
                [0x01, 0x9d, 0xb1, 0xde, 0xd5, 0x3e, 0x80, 0x00]
            } else {
                [0x00, 0x80, 0x3e, 0xd5, 0xde, 0xb1, 0x9d, 0x01]
            }),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_ne_bytes(if cfg!(target_endian = "big") {
                [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
            } else {
                [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]
            }),
            FileTime::SIGNED_MAX
        );
        assert_eq!(FileTime::from_ne_bytes([u8::MAX; 8]), FileTime::MAX);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_ne_bytes_roundtrip(bytes: [u8; mem::size_of::<FileTime>()]) {
        prop_assert_eq!(
            FileTime::from_ne_bytes(bytes),
            FileTime::new(u64::from_ne_bytes(bytes))
        );
    }

    #[test]
    const fn from_ne_bytes_is_const_fn() {
        const _: FileTime = FileTime::from_ne_bytes([u8::MIN; 8]);
    }

    #[test]
    fn to_high_low() {
        assert_eq!(FileTime::NT_TIME_EPOCH.to_high_low(), (u32::MIN, u32::MIN));
        assert_eq!(
            FileTime::UNIX_EPOCH.to_high_low(),
            (0x019d_b1de, 0xd53e_8000)
        );
        assert_eq!(
            FileTime::SIGNED_MAX.to_high_low(),
            (i32::MAX as u32, u32::MAX)
        );
        assert_eq!(FileTime::MAX.to_high_low(), (u32::MAX, u32::MAX));
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn to_high_low_roundtrip(ft: FileTime) {
        let raw = ft.to_raw();
        prop_assert_eq!(ft.to_high_low(), ((raw >> u32::BITS) as u32, raw as u32));
    }

    #[test]
    const fn to_high_low_is_const_fn() {
        const _: (u32, u32) = FileTime::NT_TIME_EPOCH.to_high_low();
    }

    #[test]
    fn from_high_low() {
        assert_eq!(
            FileTime::from_high_low(u32::MIN, u32::MIN),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_high_low(0x019d_b1de, 0xd53e_8000),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_high_low(i32::MAX as u32, u32::MAX),
            FileTime::SIGNED_MAX
        );
        assert_eq!(FileTime::from_high_low(u32::MAX, u32::MAX), FileTime::MAX);
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_high_low_roundtrip(high: u32, low: u32) {
        let raw = (u64::from(high) << u32::BITS) | u64::from(low);
        prop_assert_eq!(FileTime::from_high_low(high, low), FileTime::new(raw));
    }

    #[test]
    const fn from_high_low_is_const_fn() {
        const _: FileTime = FileTime::from_high_low(u32::MIN, u32::MIN);
    }

    #[test]
    fn default() {
        assert_eq!(FileTime::default(), FileTime::NT_TIME_EPOCH);
    }
}
