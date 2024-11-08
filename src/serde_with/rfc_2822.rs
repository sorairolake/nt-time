// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use the well-known [RFC 2822 format] when serializing and deserializing a
//! [`FileTime`].
//!
//! Use this module in combination with Serde's [`with`] attribute.
//!
//! # Examples
//!
//! ```
//! use nt_time::{
//!     serde::{Deserialize, Serialize},
//!     serde_with::rfc_2822,
//!     FileTime,
//! };
//!
//! #[derive(Deserialize, Serialize)]
//! struct Time {
//!     #[serde(with = "rfc_2822")]
//!     time: FileTime,
//! }
//!
//! let ft = Time {
//!     time: FileTime::UNIX_EPOCH,
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":"Thu, 01 Jan 1970 00:00:00 +0000"}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, FileTime::UNIX_EPOCH);
//! ```
//!
//! [RFC 2822 format]: https://datatracker.ietf.org/doc/html/rfc2822#section-3.3
//! [`with`]: https://serde.rs/field-attrs.html#with

pub mod option;

use serde::{de::Error as _, ser::Error as _, Deserializer, Serializer};
use time::serde::rfc2822;

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes a [`FileTime`] into the given Serde serializer.
///
/// This serializes using the well-known [RFC 2822 format].
///
/// [RFC 2822 format]: https://datatracker.ietf.org/doc/html/rfc2822#section-3.3
#[inline]
pub fn serialize<S: Serializer>(ft: &FileTime, serializer: S) -> Result<S::Ok, S::Error> {
    rfc2822::serialize(&(*ft).try_into().map_err(S::Error::custom)?, serializer)
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes a [`FileTime`] from the given Serde deserializer.
///
/// This deserializes from its [RFC 2822 representation].
///
/// [RFC 2822 representation]: https://datatracker.ietf.org/doc/html/rfc2822#section-3.3
#[inline]
pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<FileTime, D::Error> {
    FileTime::try_from(rfc2822::deserialize(deserializer)?).map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use serde_test::{assert_ser_tokens_error, assert_tokens, Token};

    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::rfc_2822")]
        time: FileTime,
    }

    #[test]
    fn serde() {
        assert_tokens(
            &Test {
                time: FileTime::UNIX_EPOCH,
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::BorrowedStr("Thu, 01 Jan 1970 00:00:00 +0000"),
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn serialize_error() {
        assert_ser_tokens_error::<Test>(
            &Test {
                time: FileTime::NT_TIME_EPOCH,
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
            ],
            "The year component cannot be formatted into the requested format.",
        );
    }

    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::UNIX_EPOCH
            })
            .unwrap(),
            r#"{"time":"Thu, 01 Jan 1970 00:00:00 +0000"}"#
        );
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":"Thu, 01 Jan 1970 00:00:00 +0000"}"#).unwrap(),
            Test {
                time: FileTime::UNIX_EPOCH
            }
        );
    }
}
