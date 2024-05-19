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
    /// assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
    /// ```
    #[inline]
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
    /// assert_eq!(format!("{:o}", FileTime::MAX), "1777777777777777777777");
    /// ```
    #[inline]
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
    /// assert_eq!(format!("{:x}", FileTime::MAX), "ffffffffffffffff");
    /// ```
    #[inline]
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
    /// assert_eq!(format!("{:X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
    /// ```
    #[inline]
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
    ///     format!("{:b}", FileTime::MAX),
    ///     "1111111111111111111111111111111111111111111111111111111111111111"
    /// );
    /// ```
    #[inline]
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
    /// assert_eq!(format!("{:e}", FileTime::MAX), "1.8446744073709551615e19");
    /// ```
    #[inline]
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
    /// assert_eq!(format!("{:E}", FileTime::MAX), "1.8446744073709551615E19");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        u64::from(*self).fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", FileTime::NT_TIME_EPOCH), "FileTime(0)");
        assert_eq!(
            format!("{:?}", FileTime::UNIX_EPOCH),
            "FileTime(116444736000000000)"
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
        assert_eq!(format!("{}", FileTime::MAX), "18446744073709551615");
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
        assert_eq!(format!("{:o}", FileTime::MAX), "1777777777777777777777");
        assert_eq!(format!("{:#o}", FileTime::MAX), "0o1777777777777777777777");
        assert_eq!(format!("{:022o}", FileTime::MAX), "1777777777777777777777");
        assert_eq!(
            format!("{:#024o}", FileTime::MAX),
            "0o1777777777777777777777"
        );
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
        assert_eq!(format!("{:x}", FileTime::MAX), "ffffffffffffffff");
        assert_eq!(format!("{:#x}", FileTime::MAX), "0xffffffffffffffff");
        assert_eq!(format!("{:016x}", FileTime::MAX), "ffffffffffffffff");
        assert_eq!(format!("{:#018x}", FileTime::MAX), "0xffffffffffffffff");
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
        assert_eq!(format!("{:X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:#X}", FileTime::MAX), "0xFFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:016X}", FileTime::MAX), "FFFFFFFFFFFFFFFF");
        assert_eq!(format!("{:#018X}", FileTime::MAX), "0xFFFFFFFFFFFFFFFF");
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
        assert_eq!(format!("{:e}", FileTime::MAX), "1.8446744073709551615e19");
        assert_eq!(
            format!("{:024e}", FileTime::MAX),
            "1.8446744073709551615e19"
        );
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
        assert_eq!(format!("{:E}", FileTime::MAX), "1.8446744073709551615E19");
        assert_eq!(
            format!("{:024E}", FileTime::MAX),
            "1.8446744073709551615E19"
        );
    }
}
