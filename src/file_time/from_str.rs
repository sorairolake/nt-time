// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for parsing a [`FileTime`] from a string.

use core::str::FromStr;

use super::FileTime;
use crate::error::ParseFileTimeError;

impl FromStr for FileTime {
    type Err = ParseFileTimeError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let ft = src.parse().map_err(ParseFileTimeError::new)?;
        let ft = Self::new(ft);
        Ok(ft)
    }
}

#[cfg(test)]
mod tests {
    use core::{
        error::Error,
        num::{IntErrorKind, ParseIntError},
    };

    #[cfg(feature = "std")]
    use proptest::{prop_assert, prop_assert_eq};
    #[cfg(feature = "std")]
    use test_strategy::proptest;

    use super::*;

    #[test]
    fn from_str() {
        assert_eq!(FileTime::from_str("0").unwrap(), FileTime::NT_TIME_EPOCH);
        assert_eq!(FileTime::from_str("+0").unwrap(), FileTime::NT_TIME_EPOCH);
        assert_eq!(
            FileTime::from_str("116444736000000000").unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str("+116444736000000000").unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str("9223372036854775807").unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str("+9223372036854775807").unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str("18446744073709551615").unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str("+18446744073709551615").unwrap(),
            FileTime::MAX
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_str_roundtrip(#[strategy(r"\+?[0-9]{1,19}")] s: std::string::String) {
        let ft = s.parse().unwrap();
        prop_assert_eq!(FileTime::from_str(&s).unwrap(), FileTime::new(ft));
    }

    #[test]
    fn from_str_when_empty() {
        assert_eq!(
            FileTime::from_str("")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::Empty
        );
    }

    #[test]
    fn from_str_with_invalid_digit() {
        assert_eq!(
            FileTime::from_str("a")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("_")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("-1")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("+")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("-")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str(" 0")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str("0 ")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn from_str_with_invalid_digit_roundtrip(
        #[strategy(r"-[0-9]+|[^0-9]+")] s: std::string::String,
    ) {
        prop_assert!(FileTime::from_str(&s).is_err());
    }

    #[test]
    fn from_str_when_positive_overflow() {
        assert_eq!(
            FileTime::from_str("18446744073709551616")
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
    }
}
