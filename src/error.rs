// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Error types for this crate.

use core::{
    error::Error,
    fmt,
    num::{IntErrorKind, ParseIntError},
};

/// The error type indicating that a [`FileTime`](crate::FileTime) was out of
/// range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FileTimeRangeError(FileTimeRangeErrorKind);

impl FileTimeRangeError {
    pub(crate) const fn new(kind: FileTimeRangeErrorKind) -> Self {
        Self(kind)
    }

    /// Returns the corresponding [`FileTimeRangeErrorKind`] for this error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{FileTime, error::FileTimeRangeErrorKind};
    /// #
    /// let err = FileTime::from_unix_time_secs(i64::MIN).unwrap_err();
    /// assert_eq!(err.kind(), FileTimeRangeErrorKind::Negative);
    ///
    /// let err = FileTime::from_unix_time_secs(i64::MAX).unwrap_err();
    /// assert_eq!(err.kind(), FileTimeRangeErrorKind::Overflow);
    /// ```
    #[must_use]
    pub const fn kind(&self) -> FileTimeRangeErrorKind {
        self.0
    }
}

impl fmt::Display for FileTimeRangeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind().fmt(f)
    }
}

impl Error for FileTimeRangeError {}

impl From<FileTimeRangeErrorKind> for FileTimeRangeError {
    fn from(kind: FileTimeRangeErrorKind) -> Self {
        Self::new(kind)
    }
}

/// Details of the error that caused a [`FileTimeRangeError`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FileTimeRangeErrorKind {
    /// Value was negative.
    ///
    /// This means the file time was before "1601-01-01 00:00:00 UTC".
    Negative,

    /// Value was too big to be represented as [`FileTime`](crate::FileTime).
    ///
    /// This means the file time was after "+60056-05-28 05:36:10.955161500
    /// UTC".
    Overflow,
}

impl fmt::Display for FileTimeRangeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Negative => write!(f, "file time is before `1601-01-01 00:00:00 UTC`"),
            Self::Overflow => write!(
                f,
                "file time is after `+60056-05-28 05:36:10.955161500 UTC`"
            ),
        }
    }
}

/// An error which can be returned when parsing a [`FileTime`](crate::FileTime).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseFileTimeError(ParseIntError);

impl ParseFileTimeError {
    pub(crate) const fn new(inner: ParseIntError) -> Self {
        Self(inner)
    }
}

impl fmt::Display for ParseFileTimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = &self.0;
        if inner.kind() == &IntErrorKind::PosOverflow {
            write!(
                f,
                "file time is after `+60056-05-28 05:36:10.955161500 UTC`"
            )
        } else {
            inner.fmt(f)
        }
    }
}

impl Error for ParseFileTimeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    #[test]
    fn clone_file_time_range_error() {
        assert_eq!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative).clone(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow).clone(),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
    }

    #[test]
    fn copy_file_time_range_error() {
        {
            let a = FileTimeRangeError::new(FileTimeRangeErrorKind::Negative);
            let b = a;
            assert_eq!(a, b);
        }

        {
            let a = FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow);
            let b = a;
            assert_eq!(a, b);
        }
    }

    #[test]
    fn debug_file_time_range_error() {
        assert_eq!(
            format!(
                "{:?}",
                FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
            ),
            "FileTimeRangeError(Negative)"
        );
        assert_eq!(
            format!(
                "{:?}",
                FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
            ),
            "FileTimeRangeError(Overflow)"
        );
    }

    #[test]
    fn file_time_range_error_equality() {
        assert_eq!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
        assert_ne!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
        assert_ne!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
    }

    #[test]
    fn kind_file_time_range_error() {
        assert_eq!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative).kind(),
            FileTimeRangeErrorKind::Negative
        );
        assert_eq!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow).kind(),
            FileTimeRangeErrorKind::Overflow
        );
    }

    #[test]
    const fn kind_file_time_range_error_is_const_fn() {
        const _: FileTimeRangeErrorKind =
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative).kind();
    }

    #[test]
    fn display_file_time_range_error() {
        assert_eq!(
            format!(
                "{}",
                FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
            ),
            "file time is before `1601-01-01 00:00:00 UTC`"
        );
        assert_eq!(
            format!(
                "{}",
                FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
            ),
            "file time is after `+60056-05-28 05:36:10.955161500 UTC`"
        );
    }

    #[test]
    fn source_file_time_range_error() {
        assert!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
                .source()
                .is_none()
        );
        assert!(
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
                .source()
                .is_none()
        );
    }

    #[test]
    fn from_file_time_range_error_kind_to_file_time_range_error() {
        assert_eq!(
            FileTimeRangeError::from(FileTimeRangeErrorKind::Negative),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            FileTimeRangeError::from(FileTimeRangeErrorKind::Overflow),
            FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
        );
    }

    #[test]
    fn clone_file_time_range_error_kind() {
        assert_eq!(
            FileTimeRangeErrorKind::Negative.clone(),
            FileTimeRangeErrorKind::Negative
        );
        assert_eq!(
            FileTimeRangeErrorKind::Overflow.clone(),
            FileTimeRangeErrorKind::Overflow
        );
    }

    #[test]
    fn copy_file_time_range_error_kind() {
        {
            let a = FileTimeRangeErrorKind::Negative;
            let b = a;
            assert_eq!(a, b);
        }

        {
            let a = FileTimeRangeErrorKind::Overflow;
            let b = a;
            assert_eq!(a, b);
        }
    }

    #[test]
    fn debug_file_time_range_error_kind() {
        assert_eq!(
            format!("{:?}", FileTimeRangeErrorKind::Negative),
            "Negative"
        );
        assert_eq!(
            format!("{:?}", FileTimeRangeErrorKind::Overflow),
            "Overflow"
        );
    }

    #[test]
    fn file_time_range_error_kind_equality() {
        assert_eq!(
            FileTimeRangeErrorKind::Negative,
            FileTimeRangeErrorKind::Negative
        );
        assert_ne!(
            FileTimeRangeErrorKind::Negative,
            FileTimeRangeErrorKind::Overflow
        );
        assert_ne!(
            FileTimeRangeErrorKind::Overflow,
            FileTimeRangeErrorKind::Negative
        );
        assert_eq!(
            FileTimeRangeErrorKind::Overflow,
            FileTimeRangeErrorKind::Overflow
        );
    }

    #[test]
    fn display_file_time_range_error_kind() {
        assert_eq!(
            format!("{}", FileTimeRangeErrorKind::Negative),
            "file time is before `1601-01-01 00:00:00 UTC`"
        );
        assert_eq!(
            format!("{}", FileTimeRangeErrorKind::Overflow),
            "file time is after `+60056-05-28 05:36:10.955161500 UTC`"
        );
    }

    #[test]
    fn debug_parse_file_time_error() {
        assert_eq!(
            format!(
                "{:?}",
                ParseFileTimeError::new(u64::from_str("").unwrap_err())
            ),
            "ParseFileTimeError(ParseIntError { kind: Empty })"
        );
        assert_eq!(
            format!(
                "{:?}",
                ParseFileTimeError::new(u64::from_str("a").unwrap_err())
            ),
            "ParseFileTimeError(ParseIntError { kind: InvalidDigit })"
        );
        assert_eq!(
            format!(
                "{:?}",
                ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err())
            ),
            "ParseFileTimeError(ParseIntError { kind: PosOverflow })"
        );
    }

    #[test]
    fn parse_file_time_error_equality() {
        assert_eq!(
            ParseFileTimeError::new(u64::from_str("").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("").unwrap_err())
        );
        assert_ne!(
            ParseFileTimeError::new(u64::from_str("").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("a").unwrap_err())
        );
        assert_ne!(
            ParseFileTimeError::new(u64::from_str("").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err())
        );
        assert_ne!(
            ParseFileTimeError::new(u64::from_str("a").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("").unwrap_err())
        );
        assert_eq!(
            ParseFileTimeError::new(u64::from_str("a").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("a").unwrap_err())
        );
        assert_ne!(
            ParseFileTimeError::new(u64::from_str("a").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err())
        );
        assert_ne!(
            ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("").unwrap_err())
        );
        assert_ne!(
            ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("a").unwrap_err())
        );
        assert_eq!(
            ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err()),
            ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err())
        );
    }

    #[test]
    fn display_parse_file_time_error() {
        assert_eq!(
            format!(
                "{}",
                ParseFileTimeError::new(u64::from_str("").unwrap_err())
            ),
            "cannot parse integer from empty string"
        );
        assert_eq!(
            format!(
                "{}",
                ParseFileTimeError::new(u64::from_str("a").unwrap_err())
            ),
            "invalid digit found in string"
        );
        assert_eq!(
            format!(
                "{}",
                ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err())
            ),
            "file time is after `+60056-05-28 05:36:10.955161500 UTC`"
        );
    }

    #[test]
    fn source_parse_file_time_error() {
        assert_eq!(
            ParseFileTimeError::new(u64::from_str("").unwrap_err())
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::Empty
        );
        assert_eq!(
            ParseFileTimeError::new(u64::from_str("a").unwrap_err())
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            ParseFileTimeError::new(u64::from_str("18446744073709551616").unwrap_err())
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
    }
}
