// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use [Unix time] when serializing and deserializing a [`FileTime`].
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
//!     #[serde(with = "unix_time")]
//!     time: FileTime,
//! }
//!
//! let ft = Time {
//!     time: FileTime::UNIX_EPOCH,
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":0}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, FileTime::UNIX_EPOCH);
//! ```
//!
//! [Unix time]: https://en.wikipedia.org/wiki/Unix_time
//! [`with`]: https://serde.rs/field-attrs.html#with

pub mod option;

use serde::{de::Error, Deserialize, Deserializer, Serialize, Serializer};

use crate::FileTime;

#[allow(clippy::missing_errors_doc)]
/// Serializes a [`FileTime`] into the given Serde serializer.
///
/// This serializes using [Unix time] in seconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
pub fn serialize<S: Serializer>(ft: &FileTime, serializer: S) -> Result<S::Ok, S::Error> {
    ft.to_unix_time_secs().serialize(serializer)
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes a [`FileTime`] from the given Serde deserializer.
///
/// This deserializes from its [Unix time] in seconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<FileTime, D::Error> {
    FileTime::from_unix_time_secs(<_>::deserialize(deserializer)?).map_err(D::Error::custom)
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
        #[serde(with = "crate::serde_with::unix_time")]
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
                Token::I64(-11_644_473_600),
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
                Token::I64(i64::default()),
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn serialize() {
        assert_ser_tokens(
            &Test {
                time: FileTime::MAX,
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::I64(1_833_029_933_770),
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn deserialize() {
        assert_de_tokens(
            &Test {
                time: FileTime::MAX - Duration::from_nanos(955_161_500),
            },
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::I64(1_833_029_933_770),
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
                Token::I64(-11_644_473_601),
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
                Token::I64(1_833_029_933_771),
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
            r#"{"time":-11644473600}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::UNIX_EPOCH
            })
            .unwrap(),
            r#"{"time":0}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::MAX
            })
            .unwrap(),
            r#"{"time":1833029933770}"#
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn serialize_json_roundtrip(#[strategy(-11_644_473_600..=1_833_029_933_770_i64)] ts: i64) {
        use proptest::prop_assert_eq;

        let ft = Test {
            time: FileTime::from_unix_time_secs(ts).unwrap(),
        };
        let json = serde_json::to_string(&ft).unwrap();
        prop_assert_eq!(json, format!(r#"{{"time":{ts}}}"#));
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":-11644473600}"#).unwrap(),
            Test {
                time: FileTime::NT_TIME_EPOCH
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":0}"#).unwrap(),
            Test {
                time: FileTime::UNIX_EPOCH
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":1833029933770}"#).unwrap(),
            Test {
                time: FileTime::MAX - Duration::from_nanos(955_161_500)
            }
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn deserialize_json_roundtrip(#[strategy(-11_644_473_600..=1_833_029_933_770_i64)] ts: i64) {
        use proptest::prop_assert_eq;

        let json = format!(r#"{{"time":{ts}}}"#);
        let ft = serde_json::from_str::<Test>(&json).unwrap();
        prop_assert_eq!(ft.time, FileTime::from_unix_time_secs(ts).unwrap());
    }
}
