// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Use [Unix time] in nanoseconds when serializing and deserializing a
//! [`FileTime`].
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
//!     #[serde(with = "unix_time::nanoseconds")]
//!     time: FileTime,
//! }
//!
//! let ft = Time {
//!     time: FileTime::NT_TIME_EPOCH,
//! };
//! let json = serde_json::to_string(&ft).unwrap();
//! assert_eq!(json, r#"{"time":-11644473600000000000}"#);
//!
//! let ft: Time = serde_json::from_str(&json).unwrap();
//! assert_eq!(ft.time, FileTime::NT_TIME_EPOCH);
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
/// This serializes using [Unix time] in nanoseconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
#[inline]
pub fn serialize<S: Serializer>(ft: &FileTime, serializer: S) -> Result<S::Ok, S::Error> {
    ft.to_unix_time_nanos().serialize(serializer)
}

#[allow(clippy::missing_errors_doc)]
/// Deserializes a [`FileTime`] from the given Serde deserializer.
///
/// This deserializes from its [Unix time] in nanoseconds.
///
/// [Unix time]: https://en.wikipedia.org/wiki/Unix_time
#[inline]
pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<FileTime, D::Error> {
    FileTime::from_unix_time_nanos(<_>::deserialize(deserializer)?).map_err(D::Error::custom)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct Test {
        #[serde(with = "crate::serde_with::unix_time::nanoseconds")]
        time: FileTime,
    }

    #[test]
    fn serialize_json() {
        assert_eq!(
            serde_json::to_string(&Test {
                time: FileTime::NT_TIME_EPOCH
            })
            .unwrap(),
            r#"{"time":-11644473600000000000}"#
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
            r#"{"time":1833029933770955161500}"#
        );
    }

    #[test]
    fn deserialize_json() {
        assert_eq!(
            serde_json::from_str::<Test>(r#"{"time":-11644473600000000000}"#).unwrap(),
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
            serde_json::from_str::<Test>(r#"{"time":1833029933770955161500}"#).unwrap(),
            Test {
                time: FileTime::MAX
            }
        );
    }
}
