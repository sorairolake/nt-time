// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use [Unix time] when serializing and deserializing an [`Option<FileTime>`].
//!
//! Use this module in combination with Serde's [`with`] attribute.
//!
//! # Examples
//!
//! ```
//! use nt_time::{
//!     FileTime,
//!     serde::{Deserialize, Serialize},
//!     serde_with::unix_time,
//! };
//!
//! #[derive(Deserialize, Serialize)]
//! struct Time {
//!     #[serde(with = "unix_time::option")]
//!     time: Option<FileTime>,
//! }
//!
//! let ft = Time {
//!     time: Some(FileTime::NT_TIME_EPOCH),
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":-11644473600}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, Some(FileTime::NT_TIME_EPOCH));
//!
//! let ft = Time { time: None };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":null}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, None);
//! ```
//!
//! [Unix time]: https://en.wikipedia.org/wiki/Unix_time
//! [`with`]: https://serde.rs/field-attrs.html#with

use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error};

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes an [`Option<FileTime>`] into the given Serde serializer.
///
/// This serializes using [Unix time] in seconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
#[inline]
pub fn serialize<S: Serializer>(ft: &Option<FileTime>, serializer: S) -> Result<S::Ok, S::Error> {
    ft.map(FileTime::to_unix_time_secs).serialize(serializer)
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes an [`Option<FileTime>`] from the given Serde deserializer.
///
/// This deserializes from its [Unix time] in seconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
#[inline]
pub fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<FileTime>, D::Error> {
    Option::deserialize(deserializer)?
        .map(FileTime::from_unix_time_secs)
        .transpose()
        .map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use core::time::Duration;
    #[cfg(feature = "std")]
    use std::string::String;

    #[cfg(feature = "std")]
    use proptest::{prop_assert_eq, prop_assume};
    use serde_test::Token;
    #[cfg(feature = "std")]
    use test_strategy::proptest;

    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::unix_time::option")]
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
                Token::I64(-11_644_473_600),
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
                Token::I64(i64::default()),
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

    #[test]
    fn serialize() {
        serde_test::assert_ser_tokens(
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
                Token::I64(1_833_029_933_770),
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn deserialize() {
        serde_test::assert_de_tokens(
            &Test {
                time: Some(FileTime::MAX - Duration::from_nanos(955_161_500)),
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::I64(1_833_029_933_770),
                Token::StructEnd,
            ],
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
                Token::I64(-11_644_473_601),
                Token::StructEnd,
            ],
            "file time is before `1601-01-01 00:00:00 UTC`",
        );
        serde_test::assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::I64(1_833_029_933_771),
                Token::StructEnd,
            ],
            "file time is after `+60056-05-28 05:36:10.955161500 UTC`",
        );
    }

    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::NT_TIME_EPOCH)
            })
            .unwrap(),
            r#"{"time":-11644473600}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::UNIX_EPOCH)
            })
            .unwrap(),
            r#"{"time":0}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: Some(FileTime::MAX)
            })
            .unwrap(),
            r#"{"time":1833029933770}"#
        );
        assert_eq!(
            serde_json::to_string(&Test { time: None }).unwrap(),
            r#"{"time":null}"#
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn serialize_json_roundtrip(timestamp: Option<i64>) {
        if let Some(ts) = timestamp {
            prop_assume!((-11_644_473_600..=1_833_029_933_770).contains(&ts));
        }

        let ft = Test {
            time: timestamp
                .map(FileTime::from_unix_time_secs)
                .transpose()
                .unwrap(),
        };
        let json = serde_json::to_string(&ft).unwrap();
        if let Some(ts) = timestamp {
            prop_assert_eq!(json, format!(r#"{{"time":{ts}}}"#));
        } else {
            prop_assert_eq!(json, r#"{"time":null}"#);
        }
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":-11644473600}"#).unwrap(),
            Test {
                time: Some(FileTime::NT_TIME_EPOCH)
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":0}"#).unwrap(),
            Test {
                time: Some(FileTime::UNIX_EPOCH)
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":1833029933770}"#).unwrap(),
            Test {
                time: Some(FileTime::MAX - Duration::from_nanos(955_161_500))
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":null}"#).unwrap(),
            Test { time: None }
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn deserialize_json_roundtrip(timestamp: Option<i64>) {
        if let Some(ts) = timestamp {
            prop_assume!((-11_644_473_600..=1_833_029_933_770).contains(&ts));
        }

        let json = if let Some(ts) = timestamp {
            format!(r#"{{"time":{ts}}}"#)
        } else {
            String::from(r#"{"time":null}"#)
        };
        let ft = serde_json::from_str::<Test>(&json).unwrap();
        prop_assert_eq!(
            ft.time,
            timestamp
                .map(FileTime::from_unix_time_secs)
                .transpose()
                .unwrap()
        );
    }
}
