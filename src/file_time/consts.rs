// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`FileTime`].

use super::{FileTime, FILE_TIMES_PER_SEC};

impl FileTime {
    /// The [NT time epoch].
    ///
    /// This is defined as "1601-01-01 00:00:00 UTC", which was the first year
    /// of the 400-year Gregorian calendar cycle at the time Windows NT was
    /// being designed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{time::macros::datetime, FileTime};
    /// #
    /// assert_eq!(FileTime::NT_TIME_EPOCH, datetime!(1601-01-01 00:00 UTC));
    /// ```
    ///
    /// [NT time epoch]: https://en.wikipedia.org/wiki/Epoch_(computing)
    pub const NT_TIME_EPOCH: Self = Self::new(u64::MIN);

    /// The [Unix epoch].
    ///
    /// This is defined as "1970-01-01 00:00:00 UTC", which is 11,644,473,600
    /// seconds after [`FileTime::NT_TIME_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{time::OffsetDateTime, FileTime};
    /// #
    /// assert_eq!(FileTime::UNIX_EPOCH, OffsetDateTime::UNIX_EPOCH);
    /// ```
    ///
    /// [Unix epoch]: https://en.wikipedia.org/wiki/Unix_time
    pub const UNIX_EPOCH: Self = Self::new(134_774 * 86400 * FILE_TIMES_PER_SEC);

    /// The largest file time accepted by the [`FileTimeToSystemTime`] function
    /// of the [Win32 API].
    ///
    /// This is "+30828-09-14 02:48:05.477580700 UTC", which is equal to the
    /// largest value of a 64-bit signed integer type when represented as an
    /// underlying integer value.
    ///
    /// The [`FILETIME`] structure of the Win32 API represents a 64-bit unsigned
    /// integer value, but the Win32 API may limit the largest value to
    /// [`i64::MAX`], and the file time is sometimes represented as an [`i64`]
    /// value, such as the [`winrt::clock`] struct in [WinRT], or the
    /// [`DateTime.FromFileTime`] method and the [`DateTime.ToFileTime`] method
    /// in [.NET], so if you want the process to succeed in more environments,
    /// it is generally recommended that you use this constant as the largest
    /// value instead of [`FileTime::MAX`].
    ///
    /// Note that the actual largest value of the [`SYSTEMTIME`] structure of
    /// the Win32 API is "+30827-12-31 23:59:59.999000000" (which is either in
    /// UTC or local time, depending on the function that is being called),
    /// which is different from this constant. The `FileTimeToSystemTime`
    /// function accepts the value of this constant, but it is an invalid date
    /// and time for the `SYSTEMTIME` structure.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// # use nt_time::{time::macros::datetime, FileTime};
    /// #
    /// assert_eq!(
    ///     FileTime::SIGNED_MAX,
    ///     datetime!(+30828-09-14 02:48:05.477_580_700 UTC)
    /// );
    /// # }
    /// ```
    ///
    /// [`FileTimeToSystemTime`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-filetimetosystemtime
    /// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
    /// [`FILETIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-filetime
    /// [`winrt::clock`]: https://learn.microsoft.com/en-us/uwp/cpp-ref-for-winrt/clock
    /// [WinRT]: https://learn.microsoft.com/en-us/windows/uwp/cpp-and-winrt-apis/
    /// [`DateTime.FromFileTime`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.fromfiletime
    /// [`DateTime.ToFileTime`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.tofiletime
    /// [.NET]: https://dotnet.microsoft.com/
    /// [`SYSTEMTIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-systemtime
    pub const SIGNED_MAX: Self = Self::new(i64::MAX as u64);

    /// The largest value that can be represented by the file time.
    ///
    /// This is "+60056-05-28 05:36:10.955161500 UTC".
    ///
    /// This is the theoretical largest value that the [`FILETIME`] structure of
    /// the [Win32 API] can represent.
    ///
    /// The Win32 API may limit the largest file time to [`i64::MAX`], and the
    /// file time is sometimes represented as an [`i64`] value, such as the
    /// [`winrt::clock`] struct in [WinRT], or the [`DateTime.FromFileTime`]
    /// method and the [`DateTime.ToFileTime`] method in [.NET], so if you want
    /// the process to succeed in more environments, it is generally recommended
    /// that you use [`FileTime::SIGNED_MAX`] as the largest value instead of
    /// this constant.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// # use nt_time::{time::macros::datetime, FileTime};
    /// #
    /// assert_eq!(
    ///     FileTime::MAX,
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
    /// );
    /// # }
    /// ```
    ///
    /// [`FILETIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-filetime
    /// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
    /// [`winrt::clock`]: https://learn.microsoft.com/en-us/uwp/cpp-ref-for-winrt/clock
    /// [WinRT]: https://learn.microsoft.com/en-us/windows/uwp/cpp-and-winrt-apis/
    /// [`DateTime.FromFileTime`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.fromfiletime
    /// [`DateTime.ToFileTime`]: https://learn.microsoft.com/en-us/dotnet/api/system.datetime.tofiletime
    /// [.NET]: https://dotnet.microsoft.com/
    pub const MAX: Self = Self::new(u64::MAX);
}

#[cfg(test)]
mod tests {
    use time::{macros::datetime, OffsetDateTime};

    use super::*;

    #[test]
    fn nt_time_epoch() {
        assert_eq!(FileTime::NT_TIME_EPOCH, datetime!(1601-01-01 00:00 UTC));
    }

    #[test]
    fn unix_epoch() {
        assert_eq!(FileTime::UNIX_EPOCH, OffsetDateTime::UNIX_EPOCH);
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn signed_max() {
        assert_eq!(
            FileTime::SIGNED_MAX,
            datetime!(+30828-09-14 02:48:05.477_580_700 UTC)
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn max() {
        assert_eq!(
            FileTime::MAX,
            datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
        );
    }
}
