// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`FileTime`].

use super::{FILE_TIMES_PER_SEC, FileTime};

impl FileTime {
    /// The [NT time epoch].
    ///
    /// This is defined as `1601-01-01 00:00:00 UTC`, which was the first year
    /// of the 400-year Gregorian calendar cycle at the time Windows NT was
    /// being designed.
    ///
    /// # Examples
    ///
    /// ```
    /// use nt_time::{FileTime, time::macros::utc_datetime};
    ///
    /// assert_eq!(FileTime::NT_TIME_EPOCH, utc_datetime!(1601-01-01 00:00:00));
    /// ```
    ///
    /// [NT time epoch]: https://en.wikipedia.org/wiki/Epoch_(computing)
    pub const NT_TIME_EPOCH: Self = Self::new(u64::MIN);

    /// The [Unix epoch].
    ///
    /// This is defined as `1970-01-01 00:00:00 UTC`, which is 134,774 days
    /// after [`FileTime::NT_TIME_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```
    /// use nt_time::{FileTime, time::macros::utc_datetime};
    ///
    /// assert_eq!(FileTime::UNIX_EPOCH, utc_datetime!(1970-01-01 00:00:00));
    /// ```
    ///
    /// [Unix epoch]: https://en.wikipedia.org/wiki/Unix_time
    pub const UNIX_EPOCH: Self = Self::new(134_774 * 86400 * FILE_TIMES_PER_SEC);

    /// The largest file time accepted by the [`FileTimeToSystemTime`] function
    /// of the [Win32 API].
    ///
    /// This is `+30828-09-14 02:48:05.477580700 UTC`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// use nt_time::{FileTime, time::macros::utc_datetime};
    ///
    /// assert_eq!(
    ///     FileTime::SIGNED_MAX,
    ///     utc_datetime!(+30828-09-14 02:48:05.477_580_700)
    /// );
    /// # }
    /// ```
    ///
    /// [`FileTimeToSystemTime`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-filetimetosystemtime
    /// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
    pub const SIGNED_MAX: Self = Self::new(i64::MAX as u64);

    /// The largest value that can be represented by the file time.
    ///
    /// This is `+60056-05-28 05:36:10.955161500 UTC`, which is the theoretical
    /// largest value that the [`FILETIME`] structure of the [Win32 API] can
    /// represent.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "large-dates")]
    /// # {
    /// use nt_time::{FileTime, time::macros::utc_datetime};
    ///
    /// assert_eq!(
    ///     FileTime::MAX,
    ///     utc_datetime!(+60056-05-28 05:36:10.955_161_500)
    /// );
    /// # }
    /// ```
    ///
    /// [`FILETIME`]: https://learn.microsoft.com/en-us/windows/win32/api/minwinbase/ns-minwinbase-filetime
    /// [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
    pub const MAX: Self = Self::new(u64::MAX);
}

#[cfg(test)]
mod tests {
    use time::{UtcDateTime, macros::utc_datetime};

    use super::*;

    #[test]
    fn nt_time_epoch() {
        assert_eq!(FileTime::NT_TIME_EPOCH, utc_datetime!(1601-01-01 00:00:00));
    }

    #[test]
    fn unix_epoch() {
        assert_eq!(FileTime::UNIX_EPOCH, UtcDateTime::UNIX_EPOCH);
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn signed_max() {
        assert_eq!(
            FileTime::SIGNED_MAX,
            utc_datetime!(+30828-09-14 02:48:05.477_580_700)
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn max() {
        assert_eq!(
            FileTime::MAX,
            utc_datetime!(+60056-05-28 05:36:10.955_161_500)
        );
    }
}
