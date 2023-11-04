// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Differential formats for [Serde].
//!
//! [Serde]: https://serde.rs/

#[cfg(feature = "serde-human-readable")]
pub mod iso_8601;
#[cfg(feature = "serde-human-readable")]
pub mod rfc_2822;
#[cfg(feature = "serde-human-readable")]
pub mod rfc_3339;
pub mod unix_time;
