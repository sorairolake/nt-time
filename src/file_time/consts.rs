// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`FileTime`].

use super::{FileTime, FILE_TIMES_PER_SEC};

impl FileTime {
    /// The [NT time epoch].
    ///
    /// This is defined as "1601-01-01 00:00:00 UTC".
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
    /// This is defined as "1970-01-01 00:00:00 UTC".
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

    /// The largest value that can be represented by the file time.
    ///
    /// This is "+60056-05-28 05:36:10.955161500 UTC".
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{time::macros::datetime, FileTime};
    /// #
    /// # #[cfg(feature = "large-dates")]
    /// assert_eq!(
    ///     FileTime::MAX,
    ///     datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
    /// );
    /// ```
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
    fn max() {
        assert_eq!(
            FileTime::MAX,
            datetime!(+60056-05-28 05:36:10.955_161_500 UTC)
        );
    }
}
