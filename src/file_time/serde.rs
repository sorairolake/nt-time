// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! [Serde] support for [`FileTime`].
//!
//! [Serde]: https://serde.rs/

use core::fmt;

use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Visitor};

use super::FileTime;

impl Serialize for FileTime {
    /// Serializes a `FileTime` into the given Serde serializer.
    ///
    /// This serializes using the underlying [`u64`] format.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{serde::Serialize, FileTime};
    /// #
    /// #[derive(Serialize)]
    /// struct Time {
    ///     time: FileTime,
    /// }
    ///
    /// let ft = Time {
    ///     time: FileTime::UNIX_EPOCH,
    /// };
    /// let json = serde_json::to_string(&ft).unwrap();
    /// assert_eq!(json, r#"{"time":116444736000000000}"#);
    /// ```
    ///
    /// ```
    /// # use nt_time::{serde::Serialize, FileTime};
    /// #
    /// #[derive(Serialize)]
    /// struct Time {
    ///     time: Option<FileTime>,
    /// }
    ///
    /// let ft = Time {
    ///     time: Some(FileTime::UNIX_EPOCH),
    /// };
    /// let json = serde_json::to_string(&ft).unwrap();
    /// assert_eq!(json, r#"{"time":116444736000000000}"#);
    ///
    /// let ft = Time { time: None };
    /// let json = serde_json::to_string(&ft).unwrap();
    /// assert_eq!(json, r#"{"time":null}"#);
    /// ```
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_newtype_struct("FileTime", &self.to_raw())
    }
}

impl<'de> Deserialize<'de> for FileTime {
    /// Deserializes a `FileTime` from the given Serde deserializer.
    ///
    /// This deserializes from its underlying [`u64`] representation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::{serde::Deserialize, FileTime};
    /// #
    /// #[derive(Deserialize)]
    /// struct Time {
    ///     time: FileTime,
    /// }
    ///
    /// let ft: Time = serde_json::from_str(r#"{"time":116444736000000000}"#).unwrap();
    /// assert_eq!(ft.time, FileTime::UNIX_EPOCH);
    /// ```
    ///
    /// ```
    /// # use nt_time::{serde::Deserialize, FileTime};
    /// #
    /// #[derive(Deserialize)]
    /// struct Time {
    ///     time: Option<FileTime>,
    /// }
    ///
    /// let ft: Time = serde_json::from_str(r#"{"time":116444736000000000}"#).unwrap();
    /// assert_eq!(ft.time, Some(FileTime::UNIX_EPOCH));
    ///
    /// let ft: Time = serde_json::from_str(r#"{"time":null}"#).unwrap();
    /// assert_eq!(ft.time, None);
    /// ```
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct FileTimeVisitor;

        impl<'de> Visitor<'de> for FileTimeVisitor {
            type Value = FileTime;

            #[inline]
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "a newtype struct `FileTime`")
            }

            #[inline]
            fn visit_newtype_struct<D: Deserializer<'de>>(
                self,
                deserializer: D,
            ) -> Result<Self::Value, D::Error> {
                <_>::deserialize(deserializer).map(FileTime::new)
            }
        }

        deserializer.deserialize_newtype_struct("FileTime", FileTimeVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        time: FileTime,
    }

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct TestOption {
        time: Option<FileTime>,
    }

    #[test]
    fn serde() {
        use serde_test::{Token, assert_tokens};

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
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MIN),
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
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(116_444_736_000_000_000),
                Token::StructEnd,
            ],
        );
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
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MAX),
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn deserialize_error() {
        use serde_test::{Token, assert_de_tokens_error};

        assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::BorrowedStr("FileTime"),
            ],
            r#"invalid type: string "FileTime", expected a newtype struct `FileTime`"#,
        );
        assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::NewtypeStruct { name: "FileTime" },
                Token::Bool(bool::default()),
            ],
            "invalid type: boolean `false`, expected u64",
        );
        assert_de_tokens_error::<Test>(
            &[
                Token::Struct {
                    name: "Test",
                    len: 1,
                },
                Token::Str("time"),
                Token::NewtypeStruct { name: "FileTime" },
                Token::I64(i64::MIN),
            ],
            "invalid value: integer `-9223372036854775808`, expected u64",
        );
    }

    #[test]
    fn serde_optional() {
        use serde_test::{Token, assert_tokens};

        assert_tokens(
            &TestOption {
                time: Some(FileTime::NT_TIME_EPOCH),
            },
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MIN),
                Token::StructEnd,
            ],
        );
        assert_tokens(
            &TestOption {
                time: Some(FileTime::UNIX_EPOCH),
            },
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(116_444_736_000_000_000),
                Token::StructEnd,
            ],
        );
        assert_tokens(
            &TestOption {
                time: Some(FileTime::MAX),
            },
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MAX),
                Token::StructEnd,
            ],
        );
        assert_tokens(
            &TestOption { time: None },
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::None,
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn deserialize_optional_error() {
        use serde_test::{Token, assert_de_tokens_error};

        assert_de_tokens_error::<TestOption>(
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::BorrowedStr("FileTime"),
            ],
            r#"invalid type: string "FileTime", expected option"#,
        );
        assert_de_tokens_error::<TestOption>(
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::BorrowedStr("FileTime"),
            ],
            r#"invalid type: string "FileTime", expected a newtype struct `FileTime`"#,
        );
        assert_de_tokens_error::<TestOption>(
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::Bool(bool::default()),
            ],
            "invalid type: boolean `false`, expected u64",
        );
        assert_de_tokens_error::<TestOption>(
            &[
                Token::Struct {
                    name: "TestOption",
                    len: 1,
                },
                Token::Str("time"),
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::I64(i64::MIN),
            ],
            "invalid value: integer `-9223372036854775808`, expected u64",
        );
    }

    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::NT_TIME_EPOCH
            })
            .unwrap(),
            r#"{"time":0}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::UNIX_EPOCH
            })
            .unwrap(),
            r#"{"time":116444736000000000}"#
        );
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::MAX
            })
            .unwrap(),
            r#"{"time":18446744073709551615}"#
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn serialize_json_roundtrip(raw: u64) {
        use proptest::prop_assert_eq;

        let ft = Test {
            time: FileTime::new(raw),
        };
        let json = serde_json::to_string(&ft).unwrap();
        prop_assert_eq!(json, format!(r#"{{"time":{raw}}}"#));
    }

    #[test]
    fn serialize_optional_json() {
        assert_eq!(
            serde_json::to_string(&TestOption {
                time: Some(FileTime::NT_TIME_EPOCH)
            })
            .unwrap(),
            r#"{"time":0}"#
        );
        assert_eq!(
            serde_json::to_string(&TestOption {
                time: Some(FileTime::UNIX_EPOCH)
            })
            .unwrap(),
            r#"{"time":116444736000000000}"#
        );
        assert_eq!(
            serde_json::to_string(&TestOption {
                time: Some(FileTime::MAX)
            })
            .unwrap(),
            r#"{"time":18446744073709551615}"#
        );
        assert_eq!(
            serde_json::to_string(&TestOption { time: None }).unwrap(),
            r#"{"time":null}"#
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn serialize_optional_json_roundtrip(raw: Option<u64>) {
        use proptest::prop_assert_eq;

        let ft = TestOption {
            time: raw.map(FileTime::new),
        };
        let json = serde_json::to_string(&ft).unwrap();
        if let Some(r) = raw {
            prop_assert_eq!(json, format!(r#"{{"time":{r}}}"#));
        } else {
            prop_assert_eq!(json, r#"{"time":null}"#);
        }
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":0}"#).unwrap(),
            Test {
                time: FileTime::NT_TIME_EPOCH
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":116444736000000000}"#).unwrap(),
            Test {
                time: FileTime::UNIX_EPOCH
            }
        );
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":18446744073709551615}"#).unwrap(),
            Test {
                time: FileTime::MAX
            }
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn deserialize_json_roundtrip(raw: u64) {
        use proptest::prop_assert_eq;

        let json = format!(r#"{{"time":{raw}}}"#);
        let ft = serde_json::from_str::<Test>(&json).unwrap();
        prop_assert_eq!(ft.time, FileTime::new(raw));
    }

    #[test]
    fn deserialize_optional_json() {
        assert_eq!(
            serde_json::from_str::<TestOption>(r#"{"time":0}"#).unwrap(),
            TestOption {
                time: Some(FileTime::NT_TIME_EPOCH)
            }
        );
        assert_eq!(
            serde_json::from_str::<TestOption>(r#"{"time":116444736000000000}"#).unwrap(),
            TestOption {
                time: Some(FileTime::UNIX_EPOCH)
            }
        );
        assert_eq!(
            serde_json::from_str::<TestOption>(r#"{"time":18446744073709551615}"#).unwrap(),
            TestOption {
                time: Some(FileTime::MAX)
            }
        );
        assert_eq!(
            serde_json::from_str::<TestOption>(r#"{"time":null}"#).unwrap(),
            TestOption { time: None }
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn deserialize_optional_json_roundtrip(raw: Option<u64>) {
        use std::string::String;

        use proptest::prop_assert_eq;

        let json = if let Some(r) = raw {
            format!(r#"{{"time":{r}}}"#)
        } else {
            String::from(r#"{"time":null}"#)
        };
        let ft = serde_json::from_str::<TestOption>(&json).unwrap();
        prop_assert_eq!(ft.time, raw.map(FileTime::new));
    }
}
