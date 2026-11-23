// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for comparing and ordering values.

use core::cmp::Ordering;
#[cfg(feature = "std")]
use std::time::SystemTime;

#[cfg(feature = "chrono")]
use chrono::{DateTime, Utc};
use time::UtcDateTime;

use super::FileTime;

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use std::time::Duration;

    #[cfg(feature = "chrono")]
    use chrono::{TimeZone, Timelike};
    #[cfg(feature = "jiff")]
    use jiff::ToSpan;
    use time::macros::utc_datetime;

    use super::*;

    #[test]
    fn equality() {
        assert_eq!(FileTime::NT_TIME_EPOCH, FileTime::NT_TIME_EPOCH);
        assert_ne!(FileTime::NT_TIME_EPOCH, FileTime::UNIX_EPOCH);
        assert_ne!(FileTime::NT_TIME_EPOCH, FileTime::MAX);
        assert_ne!(FileTime::UNIX_EPOCH, FileTime::NT_TIME_EPOCH);
        assert_eq!(FileTime::UNIX_EPOCH, FileTime::UNIX_EPOCH);
        assert_ne!(FileTime::UNIX_EPOCH, FileTime::MAX);
        assert_ne!(FileTime::MAX, FileTime::NT_TIME_EPOCH);
        assert_ne!(FileTime::MAX, FileTime::UNIX_EPOCH);
        assert_eq!(FileTime::MAX, FileTime::MAX);
    }

    #[test]
    fn order() {
        assert!(FileTime::UNIX_EPOCH < FileTime::MAX);
        assert_eq!(
            FileTime::UNIX_EPOCH.cmp(&FileTime::UNIX_EPOCH),
            Ordering::Equal
        );
        assert!(FileTime::UNIX_EPOCH > FileTime::NT_TIME_EPOCH);
    }
}
