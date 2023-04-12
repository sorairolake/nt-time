//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! Error types for this crate.

use core::fmt;

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
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
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

    const fn kind(self) -> FileTimeRangeErrorKind {
        self.0
    }
}

impl fmt::Display for FileTimeRangeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            FileTimeRangeErrorKind::Negative => {
                write!(f, "date and time is before `1601-01-01 00:00:00 UTC`")
            }
            FileTimeRangeErrorKind::Overflow => {
                write!(
                    f,
                    "date and time is after `+60056-05-28 05:36:10.955161500 UTC`"
                )
            }
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for FileTimeRangeError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FileTimeRangeErrorKind {
    Negative,
    Overflow,
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let a = FileTimeRangeError::new(FileTimeRangeErrorKind::Negative);
        let b = a;
        assert_eq!(a, b);

        let c = FileTimeRangeError::new(FileTimeRangeErrorKind::Overflow);
        let d = c;
        assert_eq!(c, d);
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
}
