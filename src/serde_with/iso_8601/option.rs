// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use the well-known [ISO 8601 format] when serializing and deserializing an
//! [`Option<FileTime>`].
//!
//! Use this module in combination with Serde's [`with`] attribute.
//!
//! <div class="warning">
//!
//! If the `large-dates` feature is not enabled, the largest date and time is
//! "9999-12-31 23:59:59.999999999 UTC".
//!
//! </div>
//!
//! # Examples
//!
//! ```
//! use nt_time::{
//!     FileTime,
//!     serde::{Deserialize, Serialize},
//!     serde_with::iso_8601,
//! };
//!
//! #[derive(Deserialize, Serialize)]
//! struct Time {
//!     #[serde(with = "iso_8601::option")]
//!     time: Option<FileTime>,
//! }
//!
//! let ft = Time {
//!     time: Some(FileTime::UNIX_EPOCH),
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":"+001970-01-01T00:00:00.000000000Z"}"#);
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
//! [ISO 8601 format]: https://www.iso.org/iso-8601-date-and-time-format.html
//! [`with`]: https://serde.rs/field-attrs.html#with

use serde::{Deserializer, Serializer, de::Error as _, ser::Error as _};
use time::{OffsetDateTime, serde::iso8601};

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes an [`Option<FileTime>`] into the given Serde serializer.
///
/// This serializes using the well-known [ISO 8601 format].
///
/// [ISO 8601 format]: https://www.iso.org/iso-8601-date-and-time-format.html
#[inline]
pub fn serialize<S: Serializer>(ft: &Option<FileTime>, serializer: S) -> Result<S::Ok, S::Error> {
    iso8601::option::serialize(
        &(*ft)
            .map(OffsetDateTime::try_from)
            .transpose()
            .map_err(S::Error::custom)?,
        serializer,
    )
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes an [`Option<FileTime>`] from the given Serde deserializer.
///
/// This deserializes from its [ISO 8601 representation].
///
/// [ISO 8601 representation]: https://www.iso.org/iso-8601-date-and-time-format.html
#[inline]
pub fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<FileTime>, D::Error> {
    iso8601::option::deserialize(deserializer)?
        .map(FileTime::try_from)
        .transpose()
        .map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use serde_test::{Token, assert_de_tokens_error, assert_tokens};

    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::iso_8601::option")]
        time: Option<FileTime>,
    }

    #[test]
    fn serde() {
        assert_tokens(
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
                Token::BorrowedStr("+001601-01-01T00:00:00.000000000Z"),
                Token::StructEnd,
            ],
        );
        assert_tokens(
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
                Token::BorrowedStr("+001970-01-01T00:00:00.000000000Z"),
                Token::StructEnd,
            ],
        );
        assert_tokens(
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

    #[cfg(feature = "large-dates")]
    #[test]
    fn serde_with_large_dates() {
        assert_tokens(
            &Test {
                time: Some(FileTime::MAX),
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::BorrowedStr("+060056-05-28T05:36:10.955161500Z"),
                Token::StructEnd,
            ],
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
                Token::Some,
                Token::BorrowedStr("+001600-12-31T23:59:59.999999900Z"),
                Token::StructEnd,
            ],
            "date and time is before `1601-01-01 00:00:00 UTC`",
        );
    }

    #[cfg(not(feature = "large-dates"))]
    #[test]
    fn deserialize_error_without_large_dates() {
        assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::BorrowedStr("+010000-01-01T00:00:00.000000000Z"),
                Token::StructEnd,
            ],
            "unexpected trailing characters; the end of input was expected",
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn deserialize_error_with_large_dates() {
        assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::BorrowedStr("+060056-05-28T05:36:10.955161600Z"),
                Token::StructEnd,
            ],
            "date and time is after `+60056-05-28 05:36:10.955161500 UTC`",
        );
    }

    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::NT_TIME_EPOCH)
            })
            .unwrap(),
            r#"{"time":"+001601-01-01T00:00:00.000000000Z"}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::UNIX_EPOCH)
            })
            .unwrap(),
            r#"{"time":"+001970-01-01T00:00:00.000000000Z"}"#
        );
        assert_eq!(
            serde_json::to_string(&Test { time: None }).unwrap(),
            r#"{"time":null}"#
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn serialize_json_with_large_dates() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::MAX)
            })
            .unwrap(),
            r#"{"time":"+060056-05-28T05:36:10.955161500Z"}"#
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

    #[cfg(feature = "large-dates")]
    #[test]
    fn deserialize_json_with_large_dates() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":"+060056-05-28T05:36:10.955161500Z"}"#)
                .unwrap(),
            Test {
                time: Some(FileTime::MAX)
            }
        );
    }
}
