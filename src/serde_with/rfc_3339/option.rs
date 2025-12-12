// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use the well-known [RFC 3339 format] when serializing and deserializing an
//! [`Option<FileTime>`].
//!
//! Use this module in combination with Serde's [`with`] attribute.
//!
//! # Examples
//!
//! ```
//! use nt_time::{
//!     FileTime,
//!     serde::{Deserialize, Serialize},
//!     serde_with::rfc_3339,
//! };
//!
//! #[derive(Deserialize, Serialize)]
//! struct Time {
//!     #[serde(with = "rfc_3339::option")]
//!     time: Option<FileTime>,
//! }
//!
//! let ft = Time {
//!     time: Some(FileTime::UNIX_EPOCH),
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":"1970-01-01T00:00:00Z"}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, Some(FileTime::UNIX_EPOCH));
//!
//! let ft = Time { time: None };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":null}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, None);
//! ```
//!
//! [RFC 3339 format]: https://datatracker.ietf.org/doc/html/rfc3339#section-5.6
//! [`with`]: https://serde.rs/field-attrs.html#with

use serde::{Deserializer, Serializer, de::Error as _, ser::Error as _};
use time::{OffsetDateTime, UtcDateTime, serde::rfc3339};

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes an [`Option<FileTime>`] into the given Serde serializer.
///
/// This serializes using the well-known [RFC 3339 format].
///
/// [RFC 3339 format]: https://datatracker.ietf.org/doc/html/rfc3339#section-5.6
#[inline]
pub fn serialize<S: Serializer>(ft: &Option<FileTime>, serializer: S) -> Result<S::Ok, S::Error> {
    rfc3339::option::serialize(
        &(*ft)
            .map(UtcDateTime::try_from)
            .transpose()
            .map_err(S::Error::custom)?
            .map(OffsetDateTime::from),
        serializer,
    )
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes an [`Option<FileTime>`] from the given Serde deserializer.
///
/// This deserializes from its [RFC 3339 representation].
///
/// [RFC 3339 representation]: https://datatracker.ietf.org/doc/html/rfc3339#section-5.6
#[inline]
pub fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<FileTime>, D::Error> {
    rfc3339::option::deserialize(deserializer)?
        .map(UtcDateTime::from)
        .map(FileTime::try_from)
        .transpose()
        .map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use serde_test::Token;

    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::rfc_3339::option")]
        time: Option<FileTime>,
    }

    #[test]
    fn serde() {
        serde_test::assert_tokens(
            &Test {
                time: Some(FileTime::NT_TIME_EPOCH),
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::BorrowedStr("1601-01-01T00:00:00Z"),
                Token::StructEnd,
            ],
        );
        serde_test::assert_tokens(
            &Test {
                time: Some(FileTime::UNIX_EPOCH),
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::BorrowedStr("1970-01-01T00:00:00Z"),
                Token::StructEnd,
            ],
        );
        serde_test::assert_tokens(
            &Test { time: None },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::None,
                Token::StructEnd,
            ],
        );
    }

    #[cfg(not(feature = "large-dates"))]
    #[test]
    fn serialize_error_without_large_dates() {
        serde_test::assert_ser_tokens_error::<Test>(
            &Test {
                time: Some(FileTime::MAX),
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
        serde_test::assert_ser_tokens_error::<Test>(
            &Test {
                time: Some(FileTime::MAX),
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
        serde_test::assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::BorrowedStr("1600-12-31T23:59:59.999999900Z"),
                Token::StructEnd,
            ],
            "file time is before `1601-01-01 00:00:00 UTC`",
        );
    }

    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::NT_TIME_EPOCH)
            })
            .unwrap(),
            r#"{"time":"1601-01-01T00:00:00Z"}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::UNIX_EPOCH)
            })
            .unwrap(),
            r#"{"time":"1970-01-01T00:00:00Z"}"#
        );
        assert_eq!(
            serde_json::to_string(&Test { time: None }).unwrap(),
            r#"{"time":null}"#
        );
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":"1601-01-01T00:00:00Z"}"#).unwrap(),
            Test {
                time: Some(FileTime::NT_TIME_EPOCH)
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":"1970-01-01T00:00:00Z"}"#).unwrap(),
            Test {
                time: Some(FileTime::UNIX_EPOCH)
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":null}"#).unwrap(),
            Test { time: None }
        );
    }
}
