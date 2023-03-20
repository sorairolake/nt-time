//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! The `nt-time` crate is a [Windows NT system time][file-time-docs-url]
//! library.
//!
//! This is used as timestamps such as Windows and [7z][7z-format-url].
//!
//! # Features
//!
//! ## Default features
//!
//! - `std`: Enables features that depend on the standard library.
//!
//! ## Optional features
//!
//! - `large-dates`: Enables the `large-dates` feature of the
//!   [`time`][time-crate-url] crate.
//!
//! [file-time-docs-url]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
//! [7z-format-url]: https://www.7-zip.org/7z.html
//! [time-crate-url]: https://crates.io/crates/time

#![doc(html_root_url = "https://docs.rs/nt-time/0.1.0/")]
#![no_std]
#![cfg_attr(doc_cfg, feature(doc_cfg))]
// Lint levels of rustc.
#![forbid(unsafe_code)]
#![deny(missing_debug_implementations, missing_docs)]
#![warn(rust_2018_idioms)]
// Lint levels of Clippy.
#![warn(clippy::cargo, clippy::nursery, clippy::pedantic)]

#[cfg(test)]
#[macro_use]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

mod error;
mod filetime;

pub use crate::{
    error::{TryFromFileTimeError, TryFromOffsetDateTimeError},
    filetime::FileTime,
};
