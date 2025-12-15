// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for formatting and printing [`FileTime`].

use core::fmt;

use super::FileTime;

impl fmt::Display for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{}", FileTime::NT_TIME_EPOCH), "0");
    /// assert_eq!(format!("{}", FileTime::UNIX_EPOCH), "116444736000000000");
    /// assert_eq!(format!("{}", FileTime::SIGNED_MAX), "9223372036854775807");
    /// assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::Octal for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#o}", FileTime::NT_TIME_EPOCH), "0o0");
    /// assert_eq!(
    ///     format!("{:022o}", FileTime::UNIX_EPOCH),
    ///     "0006355435732517500000"
    /// );
    /// assert_eq!(
    ///     format!("{:#024o}", FileTime::SIGNED_MAX),
    ///     "0o0777777777777777777777"
    /// );
    /// assert_eq!(format!("{:o}", FileTime::MAX), "1777777777777777777777");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::LowerHex for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#x}", FileTime::NT_TIME_EPOCH), "0x0");
    /// assert_eq!(format!("{:016x}", FileTime::UNIX_EPOCH), "019db1ded53e8000");
    /// assert_eq!(
    ///     format!("{:#018x}", FileTime::SIGNED_MAX),
    ///     "0x7fffffffffffffff"
    /// );
    /// assert_eq!(format!("{:x}", FileTime::MAX), "ffffffffffffffff");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::UpperHex for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#X}", FileTime::NT_TIME_EPOCH), "0x0");
    /// assert_eq!(format!("{:016X}", FileTime::UNIX_EPOCH), "019DB1DED53E8000");
    /// assert_eq!(
    ///     format!("{:#018X}", FileTime::SIGNED_MAX),
    ///     "0x7FFFFFFFFFFFFFFF"
    /// );
    /// assert_eq!(format!("{:X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::Binary for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(format!("{:#b}", FileTime::NT_TIME_EPOCH), "0b0");
    /// assert_eq!(
    ///     format!("{:064b}", FileTime::UNIX_EPOCH),
    ///     "0000000110011101101100011101111011010101001111101000000000000000"
    /// );
    /// assert_eq!(
    ///     format!("{:#066b}", FileTime::SIGNED_MAX),
    ///     "0b0111111111111111111111111111111111111111111111111111111111111111"
    /// );
    /// assert_eq!(
    ///     format!("{:b}", FileTime::MAX),
    ///     "1111111111111111111111111111111111111111111111111111111111111111"
    /// );
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::LowerExp for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     format!("{:024e}", FileTime::NT_TIME_EPOCH),
    ///     "0000000000000000000000e0"
    /// );
    /// assert_eq!(format!("{:e}", FileTime::UNIX_EPOCH), "1.16444736e17");
    /// assert_eq!(
    ///     format!("{:024e}", FileTime::SIGNED_MAX),
    ///     "09.223372036854775807e18"
    /// );
    /// assert_eq!(format!("{:e}", FileTime::MAX), "1.8446744073709551615e19");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

impl fmt::UpperExp for FileTime {
    /// Shows the underlying [`u64`] value of this `FileTime`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     format!("{:024E}", FileTime::NT_TIME_EPOCH),
    ///     "0000000000000000000000E0"
    /// );
    /// assert_eq!(format!("{:E}", FileTime::UNIX_EPOCH), "1.16444736E17");
    /// assert_eq!(
    ///     format!("{:024E}", FileTime::SIGNED_MAX),
    ///     "09.223372036854775807E18"
    /// );
    /// assert_eq!(format!("{:E}", FileTime::MAX), "1.8446744073709551615E19");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use proptest::prop_assert_eq;
    #[cfg(feature = "std")]
    use test_strategy::proptest;

    use super::*;

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", FileTime::NT_TIME_EPOCH), "FileTime(0)");
        assert_eq!(
            format!("{:?}", FileTime::UNIX_EPOCH),
            "FileTime(116444736000000000)"
        );
        assert_eq!(
            format!("{:?}", FileTime::SIGNED_MAX),
            "FileTime(9223372036854775807)"
        );
        assert_eq!(
            format!("{:?}", FileTime::MAX),
            "FileTime(18446744073709551615)"
        );
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{}", FileTime::UNIX_EPOCH), "116444736000000000");
        assert_eq!(format!("{}", FileTime::SIGNED_MAX), "9223372036854775807");
        assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn display_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft}"), format!("{}", ft.to_raw()));
    }

    #[test]
    fn octal() {
        assert_eq!(format!("{:o}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#o}", FileTime::NT_TIME_EPOCH), "0o0");
        assert_eq!(
            format!("{:022o}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000"
        );
        assert_eq!(
            format!("{:#024o}", FileTime::NT_TIME_EPOCH),
            "0o0000000000000000000000"
        );
        assert_eq!(format!("{:o}", FileTime::UNIX_EPOCH), "6355435732517500000");
        assert_eq!(
            format!("{:#o}", FileTime::UNIX_EPOCH),
            "0o6355435732517500000"
        );
        assert_eq!(
            format!("{:022o}", FileTime::UNIX_EPOCH),
            "0006355435732517500000"
        );
        assert_eq!(
            format!("{:#024o}", FileTime::UNIX_EPOCH),
            "0o0006355435732517500000"
        );
        assert_eq!(
            format!("{:o}", FileTime::SIGNED_MAX),
            "777777777777777777777"
        );
        assert_eq!(
            format!("{:#o}", FileTime::SIGNED_MAX),
            "0o777777777777777777777"
        );
        assert_eq!(
            format!("{:022o}", FileTime::SIGNED_MAX),
            "0777777777777777777777"
        );
        assert_eq!(
            format!("{:#024o}", FileTime::SIGNED_MAX),
            "0o0777777777777777777777"
        );
        assert_eq!(format!("{:o}", FileTime::MAX), "1777777777777777777777");
        assert_eq!(format!("{:#o}", FileTime::MAX), "0o1777777777777777777777");
        assert_eq!(format!("{:022o}", FileTime::MAX), "1777777777777777777777");
        assert_eq!(
            format!("{:#024o}", FileTime::MAX),
            "0o1777777777777777777777"
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn octal_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft:o}"), format!("{:o}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#o}"), format!("{:#o}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:022o}"), format!("{:022o}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#024o}"), format!("{:#024o}", ft.to_raw()));
    }

    #[test]
    fn lower_hex() {
        assert_eq!(format!("{:x}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#x}", FileTime::NT_TIME_EPOCH), "0x0");
        assert_eq!(
            format!("{:016x}", FileTime::NT_TIME_EPOCH),
            "0000000000000000"
        );
        assert_eq!(
            format!("{:#018x}", FileTime::NT_TIME_EPOCH),
            "0x0000000000000000"
        );
        assert_eq!(format!("{:x}", FileTime::UNIX_EPOCH), "19db1ded53e8000");
        assert_eq!(format!("{:#x}", FileTime::UNIX_EPOCH), "0x19db1ded53e8000");
        assert_eq!(format!("{:016x}", FileTime::UNIX_EPOCH), "019db1ded53e8000");
        assert_eq!(
            format!("{:#018x}", FileTime::UNIX_EPOCH),
            "0x019db1ded53e8000"
        );
        assert_eq!(format!("{:x}", FileTime::SIGNED_MAX), "7fffffffffffffff");
        assert_eq!(format!("{:#x}", FileTime::SIGNED_MAX), "0x7fffffffffffffff");
        assert_eq!(format!("{:016x}", FileTime::SIGNED_MAX), "7fffffffffffffff");
        assert_eq!(
            format!("{:#018x}", FileTime::SIGNED_MAX),
            "0x7fffffffffffffff"
        );
        assert_eq!(format!("{:x}", FileTime::MAX), "ffffffffffffffff");
        assert_eq!(format!("{:#x}", FileTime::MAX), "0xffffffffffffffff");
        assert_eq!(format!("{:016x}", FileTime::MAX), "ffffffffffffffff");
        assert_eq!(format!("{:#018x}", FileTime::MAX), "0xffffffffffffffff");
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn lower_hex_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft:x}"), format!("{:x}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#x}"), format!("{:#x}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:016x}"), format!("{:016x}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#018x}"), format!("{:#018x}", ft.to_raw()));
    }

    #[test]
    fn upper_hex() {
        assert_eq!(format!("{:X}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#X}", FileTime::NT_TIME_EPOCH), "0x0");
        assert_eq!(
            format!("{:016X}", FileTime::NT_TIME_EPOCH),
            "0000000000000000"
        );
        assert_eq!(
            format!("{:#018X}", FileTime::NT_TIME_EPOCH),
            "0x0000000000000000"
        );
        assert_eq!(format!("{:X}", FileTime::UNIX_EPOCH), "19DB1DED53E8000");
        assert_eq!(format!("{:#X}", FileTime::UNIX_EPOCH), "0x19DB1DED53E8000");
        assert_eq!(format!("{:016X}", FileTime::UNIX_EPOCH), "019DB1DED53E8000");
        assert_eq!(
            format!("{:#018X}", FileTime::UNIX_EPOCH),
            "0x019DB1DED53E8000"
        );
        assert_eq!(format!("{:X}", FileTime::SIGNED_MAX), "7FFFFFFFFFFFFFFF");
        assert_eq!(format!("{:#X}", FileTime::SIGNED_MAX), "0x7FFFFFFFFFFFFFFF");
        assert_eq!(format!("{:016X}", FileTime::SIGNED_MAX), "7FFFFFFFFFFFFFFF");
        assert_eq!(
            format!("{:#018X}", FileTime::SIGNED_MAX),
            "0x7FFFFFFFFFFFFFFF"
        );
        assert_eq!(format!("{:X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:#X}", FileTime::MAX), "0xFFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:016X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:#018X}", FileTime::MAX), "0xFFFFFFFFFFFFFFFF");
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn upper_hex_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft:X}"), format!("{:X}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#X}"), format!("{:#X}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:016X}"), format!("{:016X}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#018X}"), format!("{:#018X}", ft.to_raw()));
    }

    #[test]
    fn binary() {
        assert_eq!(format!("{:b}", FileTime::NT_TIME_EPOCH), "0");
        assert_eq!(format!("{:#b}", FileTime::NT_TIME_EPOCH), "0b0");
        assert_eq!(
            format!("{:064b}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000000000000000000000000000000000000000000000"
        );
        assert_eq!(
            format!("{:#066b}", FileTime::NT_TIME_EPOCH),
            "0b0000000000000000000000000000000000000000000000000000000000000000"
        );
        assert_eq!(
            format!("{:b}", FileTime::UNIX_EPOCH),
            "110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:#b}", FileTime::UNIX_EPOCH),
            "0b110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:064b}", FileTime::UNIX_EPOCH),
            "0000000110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:#066b}", FileTime::UNIX_EPOCH),
            "0b0000000110011101101100011101111011010101001111101000000000000000"
        );
        assert_eq!(
            format!("{:b}", FileTime::SIGNED_MAX),
            "111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:#b}", FileTime::SIGNED_MAX),
            "0b111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:064b}", FileTime::SIGNED_MAX),
            "0111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:#066b}", FileTime::SIGNED_MAX),
            "0b0111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:b}", FileTime::MAX),
            "1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:#b}", FileTime::MAX),
            "0b1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:064b}", FileTime::MAX),
            "1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            format!("{:#066b}", FileTime::MAX),
            "0b1111111111111111111111111111111111111111111111111111111111111111"
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn binary_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft:b}"), format!("{:b}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#b}"), format!("{:#b}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:064b}"), format!("{:064b}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:#066b}"), format!("{:#066b}", ft.to_raw()));
    }

    #[test]
    fn lower_exp() {
        assert_eq!(format!("{:e}", FileTime::NT_TIME_EPOCH), "0e0");
        assert_eq!(
            format!("{:024e}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000e0"
        );
        assert_eq!(format!("{:e}", FileTime::UNIX_EPOCH), "1.16444736e17");
        assert_eq!(
            format!("{:024e}", FileTime::UNIX_EPOCH),
            "000000000001.16444736e17"
        );
        assert_eq!(
            format!("{:e}", FileTime::SIGNED_MAX),
            "9.223372036854775807e18"
        );
        assert_eq!(
            format!("{:024e}", FileTime::SIGNED_MAX),
            "09.223372036854775807e18"
        );
        assert_eq!(format!("{:e}", FileTime::MAX), "1.8446744073709551615e19");
        assert_eq!(
            format!("{:024e}", FileTime::MAX),
            "1.8446744073709551615e19"
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn lower_exp_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft:e}"), format!("{:e}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:024e}"), format!("{:024e}", ft.to_raw()));
    }

    #[test]
    fn upper_exp() {
        assert_eq!(format!("{:E}", FileTime::NT_TIME_EPOCH), "0E0");
        assert_eq!(
            format!("{:024E}", FileTime::NT_TIME_EPOCH),
            "0000000000000000000000E0"
        );
        assert_eq!(format!("{:E}", FileTime::UNIX_EPOCH), "1.16444736E17");
        assert_eq!(
            format!("{:024E}", FileTime::UNIX_EPOCH),
            "000000000001.16444736E17"
        );
        assert_eq!(
            format!("{:E}", FileTime::SIGNED_MAX),
            "9.223372036854775807E18"
        );
        assert_eq!(
            format!("{:024E}", FileTime::SIGNED_MAX),
            "09.223372036854775807E18"
        );
        assert_eq!(format!("{:E}", FileTime::MAX), "1.8446744073709551615E19");
        assert_eq!(
            format!("{:024E}", FileTime::MAX),
            "1.8446744073709551615E19"
        );
    }

    #[cfg(feature = "std")]
    #[proptest]
    fn upper_exp_roundtrip(ft: FileTime) {
        prop_assert_eq!(format!("{ft:E}"), format!("{:E}", ft.to_raw()));
        prop_assert_eq!(format!("{ft:024E}"), format!("{:024E}", ft.to_raw()));
    }
}
