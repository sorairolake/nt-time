// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Error types for this crate.

use core::{
    fmt,
    num::{IntErrorKind, ParseIntError},
};

/// The error type indicating that [MS-DOS date and time] was out of range.
///
/// [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time
#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DosDateTimeRangeError(DosDateTimeRangeErrorKind);

impl DosDateTimeRangeError {
    #[inline]
    pub(crate) const fn new(kind: DosDateTimeRangeErrorKind) -> Self {
        Self(kind)
    }

    /// Returns the corresponding [`DosDateTimeRangeErrorKind`] for this error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{error::DosDateTimeRangeErrorKind, FileTime};
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH
    ///         .to_dos_date_time(None)
    ///         .unwrap_err()
    ///         .kind(),
    ///     DosDateTimeRangeErrorKind::Negative
    /// );
    /// assert_eq!(
    ///     FileTime::MAX.to_dos_date_time(None).unwrap_err().kind(),
    ///     DosDateTimeRangeErrorKind::Overflow
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub const fn kind(&self) -> DosDateTimeRangeErrorKind {
        self.0
    }
}

impl fmt::Display for DosDateTimeRangeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind().fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DosDateTimeRangeError {}

/// Details of the error that caused a [`DosDateTimeRangeError`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DosDateTimeRangeErrorKind {
    /// Value was negative.
    ///
    /// This means the date and time was before "1980-01-01 00:00:00".
    Negative,

    /// Value was too big to be represented as [MS-DOS date and time].
    ///
    /// This means the date and time was after "2107-12-31 23:59:59.990000000".
    ///
    /// [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time
    Overflow,
}

impl fmt::Display for DosDateTimeRangeErrorKind {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Negative => {
                write!(f, "date and time is before `1980-01-01 00:00:00`")
            }
            Self::Overflow => {
                write!(f, "date and time is after `2107-12-31 23:59:59.990000000`")
            }
        }
    }
}

/// The error type indicating that a [`OffsetDateTime`](time::OffsetDateTime)
/// was out of range.
#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OffsetDateTimeRangeError;

impl fmt::Display for OffsetDateTimeRangeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "date and time is out of range for `OffsetDateTime`")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OffsetDateTimeRangeError {}

/// The error type indicating that a [`FileTime`](crate::FileTime) was out of
/// range.
#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FileTimeRangeError(FileTimeRangeErrorKind);

impl FileTimeRangeError {
    #[inline]
    pub(crate) const fn new(kind: FileTimeRangeErrorKind) -> Self {
        Self(kind)
    }

    /// Returns the corresponding [`FileTimeRangeErrorKind`] for this error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{error::FileTimeRangeErrorKind, FileTime};
    /// #
    /// assert_eq!(
    ///     FileTime::from_unix_time(i64::MIN).unwrap_err().kind(),
    ///     FileTimeRangeErrorKind::Negative
    /// );
    /// assert_eq!(
    ///     FileTime::from_unix_time(i64::MAX).unwrap_err().kind(),
    ///     FileTimeRangeErrorKind::Overflow
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub const fn kind(&self) -> FileTimeRangeErrorKind {
        self.0
    }
}

impl fmt::Display for FileTimeRangeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind().fmt(f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FileTimeRangeError {}

/// Details of the error that caused a [`FileTimeRangeError`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FileTimeRangeErrorKind {
    /// Value was negative.
    ///
    /// This means the date and time was before "1601-01-01 00:00:00 UTC".
    Negative,

    /// Value was too big to be represented as [`FileTime`](crate::FileTime).
    ///
    /// This means the date and time was after "+60056-05-28 05:36:10.955161500
    /// UTC".
    Overflow,
}

impl fmt::Display for FileTimeRangeErrorKind {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Negative => {
                write!(f, "date and time is before `1601-01-01 00:00:00 UTC`")
            }
            Self::Overflow => {
                write!(
                    f,
                    "date and time is after `+60056-05-28 05:36:10.955161500 UTC`"
                )
            }
        }
    }
}

/// An error which can be returned when parsing a [`FileTime`](crate::FileTime).
#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseFileTimeError(ParseIntError);

impl ParseFileTimeError {
    #[inline]
    pub(crate) const fn new(inner: ParseIntError) -> Self {
        Self(inner)
    }
}

impl fmt::Display for ParseFileTimeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = &self.0;
        if inner.kind() == &IntErrorKind::PosOverflow {
            write!(
                f,
                "date and time is after `+60056-05-28 05:36:10.955161500 UTC`"
            )
        } else {
            inner.fmt(f)
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseFileTimeError {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    #[test]
    fn clone_dos_date_time_range_error() {
        assert_eq!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative).clone(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow).clone(),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
        );
    }

    #[test]
    fn copy_dos_date_time_range_error() {
        {
            let a = DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative);
            let b = a;
            assert_eq!(a, b);
        }

        {
            let a = DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow);
            let b = a;
            assert_eq!(a, b);
        }
    }

    #[test]
    fn debug_dos_date_time_range_error() {
        assert_eq!(
            format!(
                "{:?}",
                DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
            ),
            "DosDateTimeRangeError(Negative)"
        );
        assert_eq!(
            format!(
                "{:?}",
                DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
            ),
            "DosDateTimeRangeError(Overflow)"
        );
    }

    #[test]
    fn dos_date_time_range_error_equality() {
        assert_eq!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
        assert_ne!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
        );
        assert_ne!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
        );
        assert_eq!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow),
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
        );
    }

    #[test]
    fn kind_dos_date_time_range_error() {
        assert_eq!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative).kind(),
            DosDateTimeRangeErrorKind::Negative
        );
        assert_eq!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow).kind(),
            DosDateTimeRangeErrorKind::Overflow
        );
    }

    #[test]
    fn display_dos_date_time_range_error() {
        assert_eq!(
            format!(
                "{}",
                DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
            ),
            "date and time is before `1980-01-01 00:00:00`"
        );
        assert_eq!(
            format!(
                "{}",
                DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
            ),
            "date and time is after `2107-12-31 23:59:59.990000000`"
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn source_dos_date_time_range_error() {
        use std::error::Error;

        assert!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Negative)
                .source()
                .is_none()
        );
        assert!(
            DosDateTimeRangeError::new(DosDateTimeRangeErrorKind::Overflow)
                .source()
                .is_none()
        );
    }

    #[test]
    fn clone_dos_date_time_range_error_kind() {
        assert_eq!(
            DosDateTimeRangeErrorKind::Negative.clone(),
            DosDateTimeRangeErrorKind::Negative
        );
        assert_eq!(
            DosDateTimeRangeErrorKind::Overflow.clone(),
            DosDateTimeRangeErrorKind::Overflow
        );
    }

    #[test]
    fn copy_dos_date_time_range_error_kind() {
        {
            let a = DosDateTimeRangeErrorKind::Negative;
            let b = a;
            assert_eq!(a, b);
        }

        {
            let a = DosDateTimeRangeErrorKind::Overflow;
            let b = a;
            assert_eq!(a, b);
        }
    }

    #[test]
    fn debug_dos_date_time_range_error_kind() {
        assert_eq!(
            format!("{:?}", DosDateTimeRangeErrorKind::Negative),
            "Negative"
        );
        assert_eq!(
            format!("{:?}", DosDateTimeRangeErrorKind::Overflow),
            "Overflow"
        );
    }

    #[test]
    fn dos_date_time_range_error_kind_equality() {
        assert_eq!(
            DosDateTimeRangeErrorKind::Negative,
            DosDateTimeRangeErrorKind::Negative
        );
        assert_ne!(
            DosDateTimeRangeErrorKind::Negative,
            DosDateTimeRangeErrorKind::Overflow
        );
        assert_ne!(
            DosDateTimeRangeErrorKind::Overflow,
            DosDateTimeRangeErrorKind::Negative
        );
        assert_eq!(
            DosDateTimeRangeErrorKind::Overflow,
            DosDateTimeRangeErrorKind::Overflow
        );
    }

    #[test]
    fn display_dos_date_time_range_error_kind() {
        assert_eq!(
            format!("{}", DosDateTimeRangeErrorKind::Negative),
            "date and time is before `1980-01-01 00:00:00`"
        );
        assert_eq!(
            format!("{}", DosDateTimeRangeErrorKind::Overflow),
            "date and time is after `2107-12-31 23:59:59.990000000`"
        );
    }

    #[test]
    fn clone_offset_date_time_range_error() {
        assert_eq!(OffsetDateTimeRangeError.clone(), OffsetDateTimeRangeError);
    }

    #[test]
    fn copy_offset_date_time_range_error() {
        let a = OffsetDateTimeRangeError;
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn debug_offset_date_time_range_error() {
        assert_eq!(
            format!("{OffsetDateTimeRangeError:?}"),
            "OffsetDateTimeRangeError"
        );
    }

    #[test]
    fn offset_date_time_range_error_equality() {
        assert_eq!(OffsetDateTimeRangeError, OffsetDateTimeRangeError);
    }

    #[test]
    fn display_offset_date_time_range_error() {
        assert_eq!(
            format!("{OffsetDateTimeRangeError}"),
            "date and time is out of range for `OffsetDateTime`"
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn source_offset_date_time_range_error() {
        use std::error::Error;

        assert!(OffsetDateTimeRangeError.source().is_none());
    }

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
    fn display_file_time_range_error() {
        assert_eq!(
            format!(
                "{}",
                FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
            ),
            "date and time is before `1601-01-01 00:00:00 UTC`"
        );
        assert_eq!(
            format!(
                "{}",
                FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
            ),
            "date and time is after `+60056-05-28 05:36:10.955161500 UTC`"
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn source_file_time_range_error() {
        use std::error::Error;

        assert!(FileTimeRangeError::new(FileTimeRangeErrorKind::Negative)
            .source()
            .is_none());
        assert!(FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow)
            .source()
            .is_none());
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
            "date and time is before `1601-01-01 00:00:00 UTC`"
        );
        assert_eq!(
            format!("{}", FileTimeRangeErrorKind::Overflow),
            "date and time is after `+60056-05-28 05:36:10.955161500 UTC`"
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
            "date and time is after `+60056-05-28 05:36:10.955161500 UTC`"
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn source_parse_file_time_error() {
        use std::error::Error;

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
