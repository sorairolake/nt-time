// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `nt-time` crate is a [Windows file time] library.
//!
//! # Examples
//!
//! ## Basic usage
//!
//! The [`FileTime`] is a type that represents the file time. This type can be
//! converted from and to a type which represents time such as
//! [`time::OffsetDateTime`]. Addition and subtraction are also supported.
//!
//! ```
//! use core::time::Duration;
//!
//! use nt_time::{
//!     time::{macros::datetime, OffsetDateTime},
//!     FileTime,
//! };
//!
//! let ft = FileTime::NT_TIME_EPOCH;
//! assert_eq!(
//!     OffsetDateTime::try_from(ft).unwrap(),
//!     datetime!(1601-01-01 00:00 UTC)
//! );
//!
//! let ft = ft + Duration::from_secs(11_644_473_600);
//! assert_eq!(
//!     OffsetDateTime::try_from(ft).unwrap(),
//!     OffsetDateTime::UNIX_EPOCH
//! );
//! assert_eq!(ft.to_raw(), 116_444_736_000_000_000);
//!
//! assert_eq!(FileTime::new(u64::MAX), FileTime::MAX);
//! ```
//!
//! ## Conversion from and to other system times
//!
//! [`FileTime`] can be converted from and to other system times such as [Unix
//! time] or [MS-DOS date and time].
//!
//! ```
//! use core::time::Duration;
//!
//! use nt_time::{
//!     time::{OffsetDateTime, UtcOffset},
//!     FileTime,
//! };
//!
//! // `1970-01-01 00:00:00 UTC`.
//! let ut = i64::default();
//! assert_eq!(
//!     OffsetDateTime::from_unix_timestamp(ut).unwrap(),
//!     OffsetDateTime::UNIX_EPOCH
//! );
//!
//! let ft = FileTime::from_unix_time_secs(ut).unwrap();
//! assert_eq!(ft, FileTime::UNIX_EPOCH);
//!
//! // `1980-01-01 00:00:00 UTC`.
//! let ft = ft + Duration::from_secs(315_532_800);
//! let dos_dt = ft.to_dos_date_time(Some(UtcOffset::UTC)).unwrap();
//! assert_eq!(dos_dt, (0x0021, u16::MIN, u8::MIN, Some(UtcOffset::UTC)));
//! ```
//!
//! ## Formatting and printing the file time
//!
//! The formatting traits for [`FileTime`] are implemented to show the
//! underlying [`u64`] value. If you need a human-readable date and time,
//! convert [`FileTime`] to a type which represents time such as
//! [`time::OffsetDateTime`].
//!
//! ```
//! use nt_time::{time::OffsetDateTime, FileTime};
//!
//! let ft = FileTime::NT_TIME_EPOCH;
//! assert_eq!(format!("{ft}"), "0");
//! assert_eq!(
//!     format!("{}", OffsetDateTime::try_from(ft).unwrap()),
//!     "1601-01-01 0:00:00.0 +00:00:00"
//! );
//! ```
//!
//! [Windows file time]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
//! [Unix time]: https://en.wikipedia.org/wiki/Unix_time
//! [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time

#![doc(html_root_url = "https://docs.rs/nt-time/0.10.4/")]
#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg))]
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
#[cfg(feature = "rand")]
pub use rand;
#[cfg(feature = "serde")]
pub use serde;
pub use time;

pub use crate::file_time::FileTime;
