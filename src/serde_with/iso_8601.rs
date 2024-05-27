// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use the well-known [ISO 8601 format] when serializing and deserializing a
//! [`FileTime`].
//!
//! Use this module in combination with Serde's [`with`] attribute.
//!
//! If the `large-dates` feature is not enabled, the maximum date and time is
//! "9999-12-31 23:59:59.999999999 UTC".
//!
//! # Examples
//!
//! ```
//! use nt_time::{
//!     serde::{Deserialize, Serialize},
//!     serde_with::iso_8601,
//!     FileTime,
//! };
//!
//! #[derive(Deserialize, Serialize)]
//! struct Time {
//!     #[serde(with = "iso_8601")]
//!     time: FileTime,
//! }
//!
//! let ft = Time {
//!     time: FileTime::UNIX_EPOCH,
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":"+001970-01-01T00:00:00.000000000Z"}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, FileTime::UNIX_EPOCH);
//! ```
//!
//! [ISO 8601 format]: https://www.iso.org/iso-8601-date-and-time-format.html
//! [`with`]: https://serde.rs/field-attrs.html#with

pub mod option;

use serde::{de::Error as _, ser::Error as _, Deserializer, Serializer};
use time::serde::iso8601;

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes a [`FileTime`] into the given Serde serializer.
///
/// This serializes using the well-known [ISO 8601 format].
///
/// [ISO 8601 format]: https://www.iso.org/iso-8601-date-and-time-format.html
pub fn serialize<S: Serializer>(ft: &FileTime, serializer: S) -> Result<S::Ok, S::Error> {
    iso8601::serialize(&(*ft).try_into().map_err(S::Error::custom)?, serializer)
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes a [`FileTime`] from the given Serde deserializer.
///
/// This deserializes from its [ISO 8601 representation].
///
/// [ISO 8601 representation]: https://www.iso.org/iso-8601-date-and-time-format.html
pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<FileTime, D::Error> {
    FileTime::try_from(iso8601::deserialize(deserializer)?).map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use serde_test::{assert_de_tokens_error, assert_tokens, Token};

    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::iso_8601")]
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
                Token::BorrowedStr("+001601-01-01T00:00:00.000000000Z"),
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
                Token::BorrowedStr("+001970-01-01T00:00:00.000000000Z"),
                Token::StructEnd,
            ],
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn serde_with_large_dates() {
        assert_tokens(
            &Test {
                time: FileTime::MAX,
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
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
                time: FileTime::NT_TIME_EPOCH
            })
            .unwrap(),
            r#"{"time":"+001601-01-01T00:00:00.000000000Z"}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::UNIX_EPOCH
            })
            .unwrap(),
            r#"{"time":"+001970-01-01T00:00:00.000000000Z"}"#
        );
    }

    #[cfg(feature = "large-dates")]
    #[test]
    fn serialize_json_with_large_dates() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::MAX
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

    #[cfg(feature = "large-dates")]
    #[test]
    fn deserialize_json_with_large_dates() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":"+060056-05-28T05:36:10.955161500Z"}"#)
                .unwrap(),
            Test {
                time: FileTime::MAX
            }
        );
    }
}
