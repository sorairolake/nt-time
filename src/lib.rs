// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `nt-time` crate is a [Windows file time] library.
//!
//! The [`FileTime`] is a type that represents the file time, which is a 64-bit
//! unsigned integer value that represents the number of 100-nanosecond
//! intervals that have elapsed since "1601-01-01 00:00:00 UTC", and is used as
//! timestamps such as [NTFS] or [7z]. Windows uses a file time to record when
//! an application creates, accesses, or writes to a file.
//!
//! # Examples
//!
//! ## Basic usage
//!
//! [`FileTime`] can be converted from and to a type which represents time such
//! as [`time::UtcDateTime`]. Addition and subtraction are also supported.
//!
//! ```
//! use core::time::Duration;
//!
//! use nt_time::{
//!     FileTime,
//!     time::{UtcDateTime, macros::utc_datetime},
//! };
//!
//! let ft = FileTime::NT_TIME_EPOCH;
//! assert_eq!(
//!     UtcDateTime::try_from(ft),
//!     Ok(utc_datetime!(1601-01-01 00:00:00))
//! );
//!
//! let ft = ft + Duration::from_secs(11_644_473_600);
//! assert_eq!(UtcDateTime::try_from(ft), Ok(UtcDateTime::UNIX_EPOCH));
//! assert_eq!(ft.to_raw(), 116_444_736_000_000_000);
//!
//! // The practical largest file time.
//! assert_eq!(FileTime::try_from(i64::MAX), Ok(FileTime::SIGNED_MAX));
//! // The theoretical largest file time.
//! assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
//! ```
//!
//! ## Formatting and printing the file time
//!
//! The formatting traits for [`FileTime`] are implemented to show the
//! underlying [`u64`] value. If you need a human-readable date and time,
//! convert [`FileTime`] to a type which represents time such as
//! [`time::UtcDateTime`].
//!
//! ```
//! use nt_time::{FileTime, time::UtcDateTime};
//!
//! let ft = FileTime::NT_TIME_EPOCH;
//! assert_eq!(format!("{ft}"), "0");
//!
//! let dt = UtcDateTime::try_from(ft).unwrap();
//! assert_eq!(format!("{dt}"), "1601-01-01 0:00:00.0 +00");
//! ```
//!
//! [Windows file time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/file-times
//! [NTFS]: https://en.wikipedia.org/wiki/NTFS
//! [7z]: https://www.7-zip.org/7z.html

#![doc(html_root_url = "https://docs.rs/nt-time/0.12.1/")]
#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
// Lint levels of rustc.
#![deny(missing_docs)]

#[cfg(test)]
#[macro_use]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod error;
mod file_time;
#[cfg(feature = "serde")]
pub mod serde_with;

#[cfg(feature = "chrono")]
pub use chrono;
#[cfg(feature = "dos-date-time")]
pub use dos_date_time;
#[cfg(feature = "jiff")]
pub use jiff;
#[cfg(feature = "rand")]
pub use rand;
#[cfg(feature = "serde")]
pub use serde;
pub use time;

pub use crate::file_time::FileTime;
