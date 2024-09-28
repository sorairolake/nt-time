// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use [Unix time] in microseconds when serializing and deserializing an
//! [`Option<FileTime>`].
//!
//! Use this module in combination with Serde's [`with`] attribute.
//!
//! # Examples
//!
//! ```
//! use nt_time::{
//!     serde::{Deserialize, Serialize},
//!     serde_with::unix_time,
//!     FileTime,
//! };
//!
//! #[derive(Deserialize, Serialize)]
//! struct Time {
//!     #[serde(with = "unix_time::microseconds::option")]
//!     time: Option<FileTime>,
//! }
//!
//! let ft = Time {
//!     time: Some(FileTime::NT_TIME_EPOCH),
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":-11644473600000000}"#);
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

use serde::{de::Error, Deserialize, Deserializer, Serialize, Serializer};

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes an [`Option<FileTime>`] into the given Serde serializer.
///
/// This serializes using [Unix time] in microseconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
pub fn serialize<S: Serializer>(ft: &Option<FileTime>, serializer: S) -> Result<S::Ok, S::Error> {
    ft.map(FileTime::to_unix_time_micros).serialize(serializer)
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes an [`Option<FileTime>`] from the given Serde deserializer.
///
/// This deserializes from its [Unix time] in microseconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
pub fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<FileTime>, D::Error> {
    Option::deserialize(deserializer)?
        .map(FileTime::from_unix_time_micros)
        .transpose()
        .map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use core::time::Duration;

    use serde_test::{
        assert_de_tokens, assert_de_tokens_error, assert_ser_tokens, assert_tokens, Token,
    };

    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::unix_time::microseconds::option")]
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
                Token::I64(-11_644_473_600_000_000),
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
                Token::I64(i64::default()),
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

    #[test]
    fn serialize() {
        assert_ser_tokens(
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
                Token::I64(1_833_029_933_770_955_161),
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn deserialize() {
        assert_de_tokens(
            &Test {
                time: Some(FileTime::MAX - Duration::from_nanos(500)),
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::I64(1_833_029_933_770_955_161),
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
                Token::I64(-11_644_473_600_000_001),
                Token::StructEnd,
            ],
            "date and time is before `1601-01-01 00:00:00 UTC`",
        );
        assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::I64(1_833_029_933_770_955_162),
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
            r#"{"time":-11644473600000000}"#
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
            r#"{"time":1833029933770955161}"#
        );
        assert_eq!(
            serde_json::to_string(&Test { time: None }).unwrap(),
            r#"{"time":null}"#
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn serialize_json_roundtrip(timestamp: Option<i64>) {
        use proptest::{prop_assert_eq, prop_assume};

        if let Some(ts) = timestamp {
            prop_assume!((-11_644_473_600_000_000..=1_833_029_933_770_955_161).contains(&ts));
        }

        let ft = Test {
            time: timestamp
                .map(FileTime::from_unix_time_micros)
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
            serde_json::from_str::<Test>(r#"{"time":-11644473600000000}"#).unwrap(),
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
            serde_json::from_str::<Test>(r#"{"time":1833029933770955161}"#).unwrap(),
            Test {
                time: Some(FileTime::MAX - Duration::from_nanos(500))
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":null}"#).unwrap(),
            Test { time: None }
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn deserialize_json_roundtrip(timestamp: Option<i64>) {
        use std::string::String;

        use proptest::{prop_assert_eq, prop_assume};

        if let Some(ts) = timestamp {
            prop_assume!((-11_644_473_600_000_000..=1_833_029_933_770_955_161).contains(&ts));
        }

        #[allow(clippy::option_if_let_else)]
        let json = if let Some(ts) = timestamp {
            format!(r#"{{"time":{ts}}}"#)
        } else {
            String::from(r#"{"time":null}"#)
        };
        let ft = serde_json::from_str::<Test>(&json).unwrap();
        prop_assert_eq!(
            ft.time,
            timestamp
                .map(FileTime::from_unix_time_micros)
                .transpose()
                .unwrap()
        );
    }
}
