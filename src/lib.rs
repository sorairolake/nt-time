// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `nt-time` crate is a [Windows file time] library.
//!
//! The [`FileTime`] is a type that represents the file time, which is a 64-bit
//! unsigned integer value that represents the number of 100-nanosecond
//! intervals that have elapsed since "1601-01-01 00:00:00 UTC", and is used as
//! timestamps such as [NTFS] and [7z]. Windows uses a file time to record when
//! an application creates, accesses, or writes to a file.
//!
//! <div class="warning">
//!
//! Note that many environments, such as the [Win32 API], may limit the largest
//! value of the file time to "+30828-09-14 02:48:05.477580700 UTC", which is
//! equal to [`i64::MAX`], the largest value of a 64-bit signed integer type
//! when represented as an underlying integer value. This is the largest file
//! time accepted by the [`FileTimeToSystemTime`] function of the Win32 API.
//!
//! </div>
//!
//! # Examples
//!
//! ## Basic usage
//!
//! [`FileTime`] can be converted from and to a type which represents time such
//! as [`time::OffsetDateTime`]. Addition and subtraction are also supported.
//!
//! ```
//! use core::time::Duration;
//!
//! use nt_time::{
//!     FileTime,
//!     time::{OffsetDateTime, macros::datetime},
//! };
//!
//! let ft = FileTime::NT_TIME_EPOCH;
//! assert_eq!(
//!     OffsetDateTime::try_from(ft),
//!     Ok(datetime!(1601-01-01 00:00 UTC))
//! );
//!
//! let ft = ft + Duration::from_secs(11_644_473_600);
//! assert_eq!(OffsetDateTime::try_from(ft), Ok(OffsetDateTime::UNIX_EPOCH));
//! assert_eq!(ft.to_raw(), 116_444_736_000_000_000);
//!
//! // The practical largest file time.
//! assert_eq!(FileTime::try_from(i64::MAX), Ok(FileTime::SIGNED_MAX));
//! // The theoretical largest file time.
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
//!     FileTime,
//!     time::{OffsetDateTime, UtcOffset},
//! };
//!
//! // `1970-01-01 00:00:00 UTC`.
//! let ut = i64::default();
//! assert_eq!(
//!     OffsetDateTime::from_unix_timestamp(ut),
//!     Ok(OffsetDateTime::UNIX_EPOCH)
//! );
//!
//! let ft = FileTime::from_unix_time_secs(ut).unwrap();
//! assert_eq!(ft, FileTime::UNIX_EPOCH);
//!
//! // `1980-01-01 00:00:00 UTC`.
//! let ft = ft + Duration::from_secs(315_532_800);
//! let dos_dt = ft.to_dos_date_time(Some(UtcOffset::UTC));
//! assert_eq!(
//!     dos_dt,
//!     Ok((0x0021, u16::MIN, u8::MIN, Some(UtcOffset::UTC)))
//! );
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
//! use nt_time::{FileTime, time::OffsetDateTime};
//!
//! let ft = FileTime::NT_TIME_EPOCH;
//! assert_eq!(format!("{ft}"), "0");
//!
//! let dt = OffsetDateTime::try_from(ft).unwrap();
//! assert_eq!(format!("{dt}"), "1601-01-01 0:00:00.0 +00:00:00");
//! ```
//!
//! [Windows file time]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
//! [NTFS]: https://en.wikipedia.org/wiki/NTFS
//! [7z]: https://www.7-zip.org/7z.html
//! [Win32 API]: https://learn.microsoft.com/en-us/windows/win32/
//! [`FileTimeToSystemTime`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-filetimetosystemtime
//! [Unix time]: https://en.wikipedia.org/wiki/Unix_time
//! [MS-DOS date and time]: https://learn.microsoft.com/en-us/windows/win32/sysinfo/ms-dos-date-and-time

#![doc(html_root_url = "https://docs.rs/nt-time/0.11.0/")]
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
#[cfg(feature = "jiff")]
pub use jiff;
#[cfg(feature = "rand")]
pub use rand;
#[cfg(feature = "serde")]
pub use serde;
pub use time;

pub use crate::file_time::FileTime;
