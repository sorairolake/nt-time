// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use the well-known [RFC 3339 format] when serializing and deserializing a
//! [`FileTime`].
//!
//! Use this module in combination with Serde's [`with`] attribute.
//!
//! # Examples
//!
//! ```
//! use nt_time::{
//!     serde::{Deserialize, Serialize},
//!     serde_with::rfc_3339,
//!     FileTime,
//! };
//!
//! #[derive(Deserialize, Serialize)]
//! struct Time {
//!     #[serde(with = "rfc_3339")]
//!     time: FileTime,
//! }
//!
//! let ft = Time {
//!     time: FileTime::UNIX_EPOCH,
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":"1970-01-01T00:00:00Z"}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, FileTime::UNIX_EPOCH);
//! ```
//!
//! [RFC 3339 format]: https://datatracker.ietf.org/doc/html/rfc3339#section-5.6
//! [`with`]: https://serde.rs/field-attrs.html#with

pub mod option;

use serde::{de::Error as _, ser::Error as _, Deserializer, Serializer};
use time::serde::rfc3339;

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes a [`FileTime`] into the given Serde serializer.
///
/// This serializes using the well-known [RFC 3339 format].
///
/// [RFC 3339 format]: https://datatracker.ietf.org/doc/html/rfc3339#section-5.6
#[inline]
pub fn serialize<S: Serializer>(ft: &FileTime, serializer: S) -> Result<S::Ok, S::Error> {
    rfc3339::serialize(&(*ft).try_into().map_err(S::Error::custom)?, serializer)
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes a [`FileTime`] from the given Serde deserializer.
///
/// This deserializes from its [RFC 3339 representation].
///
/// [RFC 3339 representation]: https://datatracker.ietf.org/doc/html/rfc3339#section-5.6
#[inline]
pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<FileTime, D::Error> {
    FileTime::try_from(rfc3339::deserialize(deserializer)?).map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use serde_test::{assert_de_tokens_error, assert_ser_tokens_error, assert_tokens, Token};

    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::rfc_3339")]
        time: FileTime,
    }

    #[test]
    fn serde() {
        assert_tokens(
            &Test {
                time: FileTime::NT_TIME_EPOCH,
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::BorrowedStr("1601-01-01T00:00:00Z"),
                Token::StructEnd,
            ],
        );
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
                Token::BorrowedStr("1970-01-01T00:00:00Z"),
                Token::StructEnd,
            ],
        );
    }

    #[cfg(not(feature = "large-dates"))]
    #[test]
    fn serialize_error_without_large_dates() {
        assert_ser_tokens_error::<Test>(
            &Test {
                time: FileTime::MAX,
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
            ],
            "timestamp must be in the range -377705116800..=253402300799",
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn serialize_error_with_large_dates() {
        assert_ser_tokens_error::<Test>(
            &Test {
                time: FileTime::MAX,
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
    fn deserialize_error() {
        assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::BorrowedStr("1600-12-31T23:59:59.999999900Z"),
                Token::StructEnd,
            ],
            "date and time is before `1601-01-01 00:00:00 UTC`",
        );
    }

    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::NT_TIME_EPOCH
            })
            .unwrap(),
            r#"{"time":"1601-01-01T00:00:00Z"}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::UNIX_EPOCH
            })
            .unwrap(),
            r#"{"time":"1970-01-01T00:00:00Z"}"#
        );
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":"1601-01-01T00:00:00Z"}"#).unwrap(),
            Test {
                time: FileTime::NT_TIME_EPOCH
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":"1970-01-01T00:00:00Z"}"#).unwrap(),
            Test {
                time: FileTime::UNIX_EPOCH
            }
        );
    }
}
