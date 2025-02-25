// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for string related operations.

use core::str::FromStr;

use super::FileTime;
use crate::error::ParseFileTimeError;

impl FileTime {
    /// Parses a `FileTime` from a string slice with digits in a given base.
    ///
    /// The string is expected to be an optional `+` sign followed by only
    /// digits. Leading and trailing non-digit characters (including whitespace)
    /// represent an error. Underscores (which are accepted in Rust literals)
    /// also represent an error.
    ///
    /// Digits are a subset of these characters, depending on `radix`:
    ///
    /// - `0-9`
    /// - `a-z`
    /// - `A-Z`
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if [`u64::from_str_radix`] returns an error.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is not in the range from 2 to 36.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::from_str_radix("0", 2),
    ///     Ok(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::from_str_radix("6355435732517500000", 8),
    ///     Ok(FileTime::UNIX_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::from_str_radix("+9223372036854775807", 10),
    ///     Ok(FileTime::SIGNED_MAX)
    /// );
    /// assert_eq!(
    ///     FileTime::from_str_radix("+ffffffffffffffff", 16),
    ///     Ok(FileTime::MAX)
    /// );
    ///
    /// assert!(FileTime::from_str_radix("8", 8).is_err());
    ///
    /// assert!(FileTime::from_str_radix("", 16).is_err());
    ///
    /// assert!(FileTime::from_str_radix("Z", 16).is_err());
    /// assert!(FileTime::from_str_radix("_", 16).is_err());
    /// assert!(FileTime::from_str_radix("-1", 16).is_err());
    /// assert!(FileTime::from_str_radix("+", 16).is_err());
    /// assert!(FileTime::from_str_radix("0 ", 16).is_err());
    ///
    /// assert!(FileTime::from_str_radix("3W5E11264SGSG", 36).is_err());
    /// ```
    ///
    /// `radix` must be greater than or equal to 2:
    ///
    /// ```should_panic
    /// # use nt_time::FileTime;
    /// #
    /// let _ = FileTime::from_str_radix("0", 1);
    /// ```
    ///
    /// `radix` must be less than or equal to 36:
    ///
    /// ```should_panic
    /// # use nt_time::FileTime;
    /// #
    /// let _ = FileTime::from_str_radix("0", 37);
    /// ```
    #[inline]
    pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseFileTimeError> {
        u64::from_str_radix(src, radix)
            .map_err(ParseFileTimeError::new)
            .map(Self::new)
    }
}

impl FromStr for FileTime {
    type Err = ParseFileTimeError;

    /// Parses a string `src` to return a value of `FileTime`.
    ///
    /// <div class="warning">
    ///
    /// The string is expected to be a decimal non-negative integer. If the
    /// string is not a decimal integer, use [`FileTime::from_str_radix`]
    /// instead.
    ///
    /// </div>
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if [`u64::from_str`] returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::str::FromStr;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(FileTime::from_str("0"), Ok(FileTime::NT_TIME_EPOCH));
    /// assert_eq!(
    ///     FileTime::from_str("116444736000000000"),
    ///     Ok(FileTime::UNIX_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::from_str("+9223372036854775807"),
    ///     Ok(FileTime::SIGNED_MAX)
    /// );
    /// assert_eq!(
    ///     FileTime::from_str("+18446744073709551615"),
    ///     Ok(FileTime::MAX)
    /// );
    ///
    /// assert!(FileTime::from_str("").is_err());
    ///
    /// assert!(FileTime::from_str("a").is_err());
    /// assert!(FileTime::from_str("_").is_err());
    /// assert!(FileTime::from_str("-1").is_err());
    /// assert!(FileTime::from_str("+").is_err());
    /// assert!(FileTime::from_str("0 ").is_err());
    ///
    /// assert!(FileTime::from_str("18446744073709551616").is_err());
    /// ```
    #[inline]
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str_radix(src, 10)
    }
}

#[cfg(test)]
mod tests {
    use core::{
        error::Error,
        num::{IntErrorKind, ParseIntError},
    };

    use super::*;

    #[test]
    fn from_str_radix() {
        assert_eq!(
            FileTime::from_str_radix("0", 2).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+0", 2).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix(
                "110011101101100011101111011010101001111101000000000000000",
                2
            )
            .unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix(
                "+110011101101100011101111011010101001111101000000000000000",
                2
            )
            .unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix(
                "111111111111111111111111111111111111111111111111111111111111111",
                2
            )
            .unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix(
                "+111111111111111111111111111111111111111111111111111111111111111",
                2
            )
            .unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix(
                "1111111111111111111111111111111111111111111111111111111111111111",
                2
            )
            .unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix(
                "+1111111111111111111111111111111111111111111111111111111111111111",
                2
            )
            .unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("0", 8).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+0", 8).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("6355435732517500000", 8).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+6355435732517500000", 8).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("777777777777777777777", 8).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+777777777777777777777", 8).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("1777777777777777777777", 8).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+1777777777777777777777", 8).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("0", 10).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+0", 10).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("116444736000000000", 10).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+116444736000000000", 10).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("9223372036854775807", 10).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+9223372036854775807", 10).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("18446744073709551615", 10).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+18446744073709551615", 10).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("0", 16).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+0", 16).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("19db1ded53e8000", 16).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("19DB1DED53E8000", 16).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+19db1ded53e8000", 16).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+19DB1DED53E8000", 16).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("7fffffffffffffff", 16).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("7FFFFFFFFFFFFFFF", 16).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+7fffffffffffffff", 16).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+7FFFFFFFFFFFFFFF", 16).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("ffffffffffffffff", 16).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("FFFFFFFFFFFFFFFF", 16).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+ffffffffffffffff", 16).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+FFFFFFFFFFFFFFFF", 16).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("0", 36).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+0", 36).unwrap(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("vuk7p84etc0", 36).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("VUK7P84ETC0", 36).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+vuk7p84etc0", 36).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("+VUK7P84ETC0", 36).unwrap(),
            FileTime::UNIX_EPOCH
        );
        assert_eq!(
            FileTime::from_str_radix("1y2p0ij32e8e7", 36).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("1Y2P0IJ32E8E7", 36).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+1y2p0ij32e8e7", 36).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+1Y2P0IJ32E8E7", 36).unwrap(),
            FileTime::SIGNED_MAX
        );
        assert_eq!(
            FileTime::from_str_radix("3w5e11264sgsf", 36).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("3W5E11264SGSF", 36).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+3w5e11264sgsf", 36).unwrap(),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::from_str_radix("+3W5E11264SGSF", 36).unwrap(),
            FileTime::MAX
        );
    }

    #[test]
    fn from_str_radix_with_invalid_digit_radix() {
        assert_eq!(
            FileTime::from_str_radix("2", 2)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("8", 8)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("a", 10)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("A", 10)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("g", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("G", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
    }

    #[test]
    fn from_str_radix_when_empty() {
        assert_eq!(
            FileTime::from_str_radix("", 16)
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
    fn from_str_radix_with_invalid_digit() {
        assert_eq!(
            FileTime::from_str_radix("Z", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("_", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("-1", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("+", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("-", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix(" 0", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            FileTime::from_str_radix("0 ", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::InvalidDigit
        );
    }

    #[test]
    fn from_str_radix_when_positive_overflow() {
        assert_eq!(
            FileTime::from_str_radix(
                "10000000000000000000000000000000000000000000000000000000000000000",
                2
            )
            .unwrap_err()
            .source()
            .unwrap()
            .downcast_ref::<ParseIntError>()
            .unwrap()
            .kind(),
            &IntErrorKind::PosOverflow
        );
        assert_eq!(
            FileTime::from_str_radix("2000000000000000000000", 8)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
        assert_eq!(
            FileTime::from_str_radix("18446744073709551616", 10)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
        assert_eq!(
            FileTime::from_str_radix("10000000000000000", 16)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
        assert_eq!(
            FileTime::from_str_radix("3w5e11264sgsg", 36)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
        assert_eq!(
            FileTime::from_str_radix("3W5E11264SGSG", 36)
                .unwrap_err()
                .source()
                .unwrap()
                .downcast_ref::<ParseIntError>()
                .unwrap()
                .kind(),
            &IntErrorKind::PosOverflow
        );
    }

    #[test]
    #[should_panic]
    fn from_str_radix_when_radix_is_less_than_2() {
        let _ = FileTime::from_str_radix("0", 1);
    }

    #[test]
    #[should_panic]
    fn from_str_radix_when_radix_is_greater_than_36() {
        let _ = FileTime::from_str_radix("0", 37);
    }

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
    #[test_strategy::proptest]
    fn from_str_roundtrip(#[strategy(r"\+?[0-9]{1,19}")] s: std::string::String) {
        use proptest::prop_assert_eq;

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
    #[test_strategy::proptest]
    fn from_str_with_invalid_digit_roundtrip(
        #[strategy(r"-[0-9]+|[^0-9]+")] s: std::string::String,
    ) {
        use proptest::prop_assert;

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
