//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! Error types for this crate.

use core::fmt;

/// The error type returned when a conversion from a
/// [`FileTime`](crate::FileTime) to a [`OffsetDateTime`](time::OffsetDateTime)
/// fails.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct TryFromFileTimeError;

impl fmt::Display for TryFromFileTimeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "file time is after `9999-12-31 23:59:59.999999900 UTC`")
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for TryFromFileTimeError {}

/// The error type returned when a conversion from a
/// [`OffsetDateTime`](time::OffsetDateTime) to a [`FileTime`](crate::FileTime)
/// fails.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct TryFromOffsetDateTimeError;

impl fmt::Display for TryFromOffsetDateTimeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "date time is out of range of file time")
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for TryFromOffsetDateTimeError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_try_from_file_time_error() {
        assert_eq!(
            format!("{TryFromFileTimeError}"),
            "file time is after `9999-12-31 23:59:59.999999900 UTC`"
        );
    }

    #[test]
    fn display_try_from_offset_date_time_error() {
        assert_eq!(
            format!("{TryFromOffsetDateTimeError}"),
            "date time is out of range of file time"
        );
    }
}
