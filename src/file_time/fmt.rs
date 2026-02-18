// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for formatting and printing [`FileTime`].

use core::fmt;

use super::FileTime;

impl fmt::Display for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{}", FileTime::NT_TIME_EPOCH), "0");
    /// assert_eq!(format!("{}", FileTime::UNIX_EPOCH), "116444736000000000");
    /// assert_eq!(format!("{}", FileTime::SIGNED_MAX), "9223372036854775807");
    /// assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use proptest::prop_assert_eq;
    #[cfg(feature = "std")]
    use test_strategy::proptest;

    use super::*;

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", FileTime::NT_TIME_EPOCH), "FileTime(0)");
        assert_eq!(
            format!("{:?}", FileTime::UNIX_EPOCH),
            "FileTime(116444736000000000)"
        );
        assert_eq!(
            format!("{:?}", FileTime::SIGNED_MAX),
            "FileTime(9223372036854775807)"
        );
        assert_eq!(
            format!("{:?}", FileTime::MAX),
            "FileTime(18446744073709551615)"
        );
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{}", FileTime::UNIX_EPOCH), "116444736000000000");
        assert_eq!(format!("{}", FileTime::SIGNED_MAX), "9223372036854775807");
        assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn display_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft}"), format!("{}", ft.to_raw()));
    }
}
