//
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (C) 2023 Shun Sakai
//

//! The `nt-time` crate is a [Windows NT system time][file-time-docs-url]
//! library.
//!
//! # Features
//!
//! ## Default features
//!
//! - `std`: Enables features that depend on the standard library.
//! - `time`: Enables the [`time`][time-crate-url] crate.
//!
//! ## Optional features
//!
//! - `large-dates`: Enables the `large-dates` feature of the
//!   [`time`][time-crate-url] crate.
//!
//! [file-time-docs-url]: https://docs.microsoft.com/en-us/windows/win32/sysinfo/file-times
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

#[must_use]
pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
