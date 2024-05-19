// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! [Serde] support for [`FileTime`].
//!
//! [Serde]: https://serde.rs/

use core::fmt;

use serde::{de::Visitor, Deserialize, Deserializer, Serialize, Serializer};

use super::FileTime;

impl Serialize for FileTime {
    /// Serializes a `FileTime` into the given Serde serializer.
    ///
    /// This serializes using the underlying [`u64`] format.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     serde_json::to_string(&FileTime::UNIX_EPOCH).unwrap(),
    ///     "116444736000000000"
    /// );
    ///
    /// assert_eq!(
    ///     serde_json::to_string(&Some(FileTime::UNIX_EPOCH)).unwrap(),
    ///     "116444736000000000"
    /// );
    /// assert_eq!(serde_json::to_string(&None::<FileTime>).unwrap(), "null");
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
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     serde_json::from_str::<FileTime>("116444736000000000").unwrap(),
    ///     FileTime::UNIX_EPOCH
    /// );
    ///
    /// assert_eq!(
    ///     serde_json::from_str::<Option<FileTime>>("116444736000000000").unwrap(),
    ///     Some(FileTime::UNIX_EPOCH)
    /// );
    /// assert_eq!(
    ///     serde_json::from_str::<Option<FileTime>>("null").unwrap(),
    ///     None
    /// );
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
                u64::deserialize(deserializer).map(FileTime::new)
            }
        }

        deserializer.deserialize_newtype_struct("FileTime", FileTimeVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde() {
        use serde_test::{assert_tokens, Token};

        assert_tokens(
            &FileTime::NT_TIME_EPOCH,
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MIN),
            ],
        );
        assert_tokens(
            &FileTime::UNIX_EPOCH,
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(116_444_736_000_000_000),
            ],
        );
        assert_tokens(
            &FileTime::MAX,
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MAX),
            ],
        );
    }

    #[test]
    fn deserialize_error() {
        use serde_test::{assert_de_tokens_error, Token};

        assert_de_tokens_error::<FileTime>(
            &[Token::BorrowedStr("FileTime")],
            r#"invalid type: string "FileTime", expected a newtype struct `FileTime`"#,
        );
        assert_de_tokens_error::<FileTime>(
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::Bool(bool::default()),
            ],
            "invalid type: boolean `false`, expected u64",
        );
        assert_de_tokens_error::<FileTime>(
            &[
                Token::NewtypeStruct { name: "FileTime" },
                Token::I64(i64::MIN),
            ],
            "invalid value: integer `-9223372036854775808`, expected u64",
        );
    }

    #[test]
    fn serde_optional() {
        use serde_test::{assert_tokens, Token};

        assert_tokens(
            &Some(FileTime::NT_TIME_EPOCH),
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MIN),
            ],
        );
        assert_tokens(
            &Some(FileTime::UNIX_EPOCH),
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(116_444_736_000_000_000),
            ],
        );
        assert_tokens(
            &Some(FileTime::MAX),
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::U64(u64::MAX),
            ],
        );
        assert_tokens(&None::<FileTime>, &[Token::None]);
    }

    #[test]
    fn deserialize_optional_error() {
        use serde_test::{assert_de_tokens_error, Token};

        assert_de_tokens_error::<Option<FileTime>>(
            &[Token::BorrowedStr("FileTime")],
            r#"invalid type: string "FileTime", expected option"#,
        );
        assert_de_tokens_error::<Option<FileTime>>(
            &[Token::Some, Token::BorrowedStr("FileTime")],
            r#"invalid type: string "FileTime", expected a newtype struct `FileTime`"#,
        );
        assert_de_tokens_error::<Option<FileTime>>(
            &[
                Token::Some,
                Token::NewtypeStruct { name: "FileTime" },
                Token::Bool(bool::default()),
            ],
            "invalid type: boolean `false`, expected u64",
        );
        assert_de_tokens_error::<Option<FileTime>>(
            &[
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
            serde_json::to_string(&FileTime::NT_TIME_EPOCH).unwrap(),
            "0"
        );
        assert_eq!(
            serde_json::to_string(&FileTime::UNIX_EPOCH).unwrap(),
            "116444736000000000"
        );
        assert_eq!(
            serde_json::to_string(&FileTime::MAX).unwrap(),
            "18446744073709551615"
        );
    }

    #[test]
    fn serialize_optional_json() {
        assert_eq!(
            serde_json::to_string(&Some(FileTime::NT_TIME_EPOCH)).unwrap(),
            "0"
        );
        assert_eq!(
            serde_json::to_string(&Some(FileTime::UNIX_EPOCH)).unwrap(),
            "116444736000000000"
        );
        assert_eq!(
            serde_json::to_string(&Some(FileTime::MAX)).unwrap(),
            "18446744073709551615"
        );
        assert_eq!(serde_json::to_string(&None::<FileTime>).unwrap(), "null");
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<FileTime>("0").unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            serde_json::from_str::<FileTime>("116444736000000000").unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            serde_json::from_str::<FileTime>("18446744073709551615").unwrap(),
            FileTime::MAX
        );
    }

    #[test]
    fn deserialize_optional_json() {
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("0").unwrap(),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("116444736000000000").unwrap(),
            Some(FileTime::UNIX_EPOCH)
        );
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("18446744073709551615").unwrap(),
            Some(FileTime::MAX)
        );
        assert_eq!(
            serde_json::from_str::<Option<FileTime>>("null").unwrap(),
            None
        );
    }
}
