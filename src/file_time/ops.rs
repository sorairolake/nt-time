// SPDX-FileCopyrightText: 2023 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Operations for [`FileTime`].

use core::ops::{Add, AddAssign, Sub, SubAssign};

use time::OffsetDateTime;

use super::{FILE_TIMES_PER_SEC, FileTime};

impl FileTime {
    /// Computes `self + rhs`, returning [`None`] if overflow occurred. The part
    /// of `rhs` less than 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(1)),
    ///     Some(FileTime::NT_TIME_EPOCH)
    /// );
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(100)),
    ///     Some(FileTime::new(1))
    /// );
    ///
    /// assert_eq!(FileTime::MAX.checked_add(Duration::from_nanos(100)), None);
    /// ```
    #[must_use]
    #[inline]
    pub fn checked_add(self, rhs: core::time::Duration) -> Option<Self> {
        let duration = u64::try_from(rhs.as_nanos() / 100).ok()?;
        self.to_raw().checked_add(duration).map(Self::new)
    }

    /// Computes `self - rhs`, returning [`None`] if the result would be
    /// negative or if overflow occurred. The part of `rhs` less than
    /// 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::MAX.checked_sub(Duration::from_nanos(1)),
    ///     Some(FileTime::MAX)
    /// );
    /// assert_eq!(
    ///     FileTime::MAX.checked_sub(Duration::from_nanos(100)),
    ///     Some(FileTime::new(u64::MAX - 1))
    /// );
    ///
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(100)),
    ///     None
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub fn checked_sub(self, rhs: core::time::Duration) -> Option<Self> {
        let duration = u64::try_from(rhs.as_nanos() / 100).ok()?;
        self.to_raw().checked_sub(duration).map(Self::new)
    }

    /// Computes `self + rhs`, returning [`FileTime::MAX`] if overflow occurred.
    /// The part of `rhs` less than 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(1)),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(100)),
    ///     FileTime::new(1)
    /// );
    ///
    /// assert_eq!(
    ///     FileTime::MAX.saturating_add(Duration::from_nanos(100)),
    ///     FileTime::MAX
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub fn saturating_add(self, rhs: core::time::Duration) -> Self {
        self.checked_add(rhs).unwrap_or(Self::MAX)
    }

    /// Computes `self - rhs`, returning [`FileTime::NT_TIME_EPOCH`] if the
    /// result would be negative or if overflow occurred. The part of `rhs` less
    /// than 100-nanosecond is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use core::time::Duration;
    /// #
    /// # use nt_time::FileTime;
    /// #
    /// assert_eq!(
    ///     FileTime::MAX.saturating_sub(Duration::from_nanos(1)),
    ///     FileTime::MAX
    /// );
    /// assert_eq!(
    ///     FileTime::MAX.saturating_sub(Duration::from_nanos(100)),
    ///     FileTime::new(u64::MAX - 1)
    /// );
    ///
    /// assert_eq!(
    ///     FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(100)),
    ///     FileTime::NT_TIME_EPOCH
    /// );
    /// ```
    #[must_use]
    #[inline]
    pub fn saturating_sub(self, rhs: core::time::Duration) -> Self {
        self.checked_sub(rhs).unwrap_or_default()
    }
}

impl Add<core::time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn add(self, rhs: core::time::Duration) -> Self::Output {
        self.checked_add(rhs)
            .expect("overflow when adding duration to date and time")
    }
}

impl Add<time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn add(self, rhs: time::Duration) -> Self::Output {
        if rhs.is_positive() {
            self + rhs.unsigned_abs()
        } else {
            self - rhs.unsigned_abs()
        }
    }
}

#[cfg(feature = "chrono")]
impl Add<chrono::TimeDelta> for FileTime {
    type Output = Self;

    #[inline]
    fn add(self, rhs: chrono::TimeDelta) -> Self::Output {
        use chrono::TimeDelta;

        if rhs > TimeDelta::zero() {
            self + rhs.abs().to_std().expect("duration is less than zero")
        } else {
            self - rhs.abs().to_std().expect("duration is less than zero")
        }
    }
}

#[cfg(feature = "jiff")]
impl Add<jiff::Span> for FileTime {
    type Output = Self;

    #[inline]
    fn add(self, rhs: jiff::Span) -> Self::Output {
        use core::time::Duration;

        if rhs.is_positive() {
            self + Duration::try_from(rhs.abs()).expect("duration is less than zero")
        } else {
            self - Duration::try_from(rhs.abs()).expect("duration is less than zero")
        }
    }
}

impl AddAssign<core::time::Duration> for FileTime {
    #[inline]
    fn add_assign(&mut self, rhs: core::time::Duration) {
        *self = *self + rhs;
    }
}

impl AddAssign<time::Duration> for FileTime {
    #[inline]
    fn add_assign(&mut self, rhs: time::Duration) {
        *self = *self + rhs;
    }
}

#[cfg(feature = "chrono")]
impl AddAssign<chrono::TimeDelta> for FileTime {
    #[inline]
    fn add_assign(&mut self, rhs: chrono::TimeDelta) {
        *self = *self + rhs;
    }
}

#[cfg(feature = "jiff")]
impl AddAssign<jiff::Span> for FileTime {
    #[inline]
    fn add_assign(&mut self, rhs: jiff::Span) {
        *self = *self + rhs;
    }
}

impl Sub for FileTime {
    type Output = core::time::Duration;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        let duration = self.to_raw() - rhs.to_raw();
        Self::Output::new(
            duration / FILE_TIMES_PER_SEC,
            u32::try_from((duration % FILE_TIMES_PER_SEC) * 100)
                .expect("the number of nanoseconds should be in the range of `u32`"),
        )
    }
}

impl Sub<core::time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: core::time::Duration) -> Self::Output {
        self.checked_sub(rhs)
            .expect("overflow when subtracting duration from date and time")
    }
}

impl Sub<time::Duration> for FileTime {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: time::Duration) -> Self::Output {
        if rhs.is_positive() {
            self - rhs.unsigned_abs()
        } else {
            self + rhs.unsigned_abs()
        }
    }
}

#[cfg(feature = "chrono")]
impl Sub<chrono::TimeDelta> for FileTime {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: chrono::TimeDelta) -> Self::Output {
        use chrono::TimeDelta;

        if rhs > TimeDelta::zero() {
            self - rhs.abs().to_std().expect("duration is less than zero")
        } else {
            self + rhs.abs().to_std().expect("duration is less than zero")
        }
    }
}

#[cfg(feature = "jiff")]
impl Sub<jiff::Span> for FileTime {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: jiff::Span) -> Self::Output {
        use core::time::Duration;

        if rhs.is_positive() {
            self - Duration::try_from(rhs.abs()).expect("duration is less than zero")
        } else {
            self + Duration::try_from(rhs.abs()).expect("duration is less than zero")
        }
    }
}

#[cfg(feature = "std")]
impl Sub<FileTime> for std::time::SystemTime {
    type Output = std::time::Duration;

    #[inline]
    fn sub(self, rhs: FileTime) -> Self::Output {
        self.duration_since(rhs.into())
            .expect("RHS provided is later than LHS")
    }
}

#[cfg(feature = "std")]
impl Sub<std::time::SystemTime> for FileTime {
    type Output = std::time::Duration;

    #[inline]
    fn sub(self, rhs: std::time::SystemTime) -> Self::Output {
        use std::time::SystemTime;

        SystemTime::from(self)
            .duration_since(rhs)
            .expect("RHS provided is later than LHS")
    }
}

impl Sub<FileTime> for OffsetDateTime {
    type Output = time::Duration;

    #[inline]
    fn sub(self, rhs: FileTime) -> Self::Output {
        self - Self::try_from(rhs).expect("RHS is out of range for `OffsetDateTime`")
    }
}

impl Sub<OffsetDateTime> for FileTime {
    type Output = time::Duration;

    #[inline]
    fn sub(self, rhs: OffsetDateTime) -> Self::Output {
        OffsetDateTime::try_from(self).expect("LHS is out of range for `OffsetDateTime`") - rhs
    }
}

#[cfg(feature = "chrono")]
impl Sub<FileTime> for chrono::DateTime<chrono::Utc> {
    type Output = chrono::TimeDelta;

    #[inline]
    fn sub(self, rhs: FileTime) -> Self::Output {
        self - Self::from(rhs)
    }
}

#[cfg(feature = "chrono")]
impl Sub<chrono::DateTime<chrono::Utc>> for FileTime {
    type Output = chrono::TimeDelta;

    #[inline]
    fn sub(self, rhs: chrono::DateTime<chrono::Utc>) -> Self::Output {
        use chrono::{DateTime, Utc};

        DateTime::<Utc>::from(self) - rhs
    }
}

#[cfg(feature = "jiff")]
impl Sub<FileTime> for jiff::Timestamp {
    type Output = jiff::Span;

    #[inline]
    fn sub(self, rhs: FileTime) -> Self::Output {
        self - Self::try_from(rhs).expect("RHS is out of range for `Timestamp`")
    }
}

#[cfg(feature = "jiff")]
impl Sub<jiff::Timestamp> for FileTime {
    type Output = jiff::Span;

    #[inline]
    fn sub(self, rhs: jiff::Timestamp) -> Self::Output {
        use jiff::Timestamp;

        Timestamp::try_from(self).expect("LHS is out of range for `Timestamp`") - rhs
    }
}

impl SubAssign<core::time::Duration> for FileTime {
    #[inline]
    fn sub_assign(&mut self, rhs: core::time::Duration) {
        *self = *self - rhs;
    }
}

impl SubAssign<time::Duration> for FileTime {
    #[inline]
    fn sub_assign(&mut self, rhs: time::Duration) {
        *self = *self - rhs;
    }
}

#[cfg(feature = "chrono")]
impl SubAssign<chrono::TimeDelta> for FileTime {
    #[inline]
    fn sub_assign(&mut self, rhs: chrono::TimeDelta) {
        *self = *self - rhs;
    }
}

#[cfg(feature = "jiff")]
impl SubAssign<jiff::Span> for FileTime {
    #[inline]
    fn sub_assign(&mut self, rhs: jiff::Span) {
        *self = *self - rhs;
    }
}

#[cfg(test)]
mod tests {
    use time::macros::datetime;

    use super::*;

    #[test]
    fn checked_add() {
        use core::time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::ZERO),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(1)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(99)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_add(Duration::from_nanos(100)),
            Some(FileTime::new(1))
        );

        assert_eq!(
            FileTime::MAX.checked_add(Duration::ZERO),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_add(Duration::from_nanos(1)),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_add(Duration::from_nanos(99)),
            Some(FileTime::MAX)
        );
        assert_eq!(FileTime::MAX.checked_add(Duration::from_nanos(100)), None);
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn checked_add_roundtrip(dur: std::time::Duration) {
        use std::time::Duration;

        use proptest::prop_assert;

        if dur <= Duration::new(1_844_674_407_370, 955_161_500) {
            prop_assert!(FileTime::NT_TIME_EPOCH.checked_add(dur).is_some());
        } else {
            prop_assert!(FileTime::NT_TIME_EPOCH.checked_add(dur).is_none());
        }
    }

    #[test]
    fn checked_sub() {
        use core::time::Duration;

        assert_eq!(
            FileTime::MAX.checked_sub(Duration::ZERO),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_sub(Duration::from_nanos(1)),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_sub(Duration::from_nanos(99)),
            Some(FileTime::MAX)
        );
        assert_eq!(
            FileTime::MAX.checked_sub(Duration::from_nanos(100)),
            Some(FileTime::new(u64::MAX - 1))
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::ZERO),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(1)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(99)),
            Some(FileTime::NT_TIME_EPOCH)
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.checked_sub(Duration::from_nanos(100)),
            None
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn checked_sub_roundtrip(dur: std::time::Duration) {
        use std::time::Duration;

        use proptest::prop_assert;

        if dur <= Duration::new(1_844_674_407_370, 955_161_500) {
            prop_assert!(FileTime::MAX.checked_add(dur).is_some());
        } else {
            prop_assert!(FileTime::MAX.checked_add(dur).is_none());
        }
    }

    #[test]
    fn saturating_add() {
        use core::time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::ZERO),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(1)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(99)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_add(Duration::from_nanos(100)),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX.saturating_add(Duration::ZERO), FileTime::MAX);
        assert_eq!(
            FileTime::MAX.saturating_add(Duration::from_nanos(1)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_add(Duration::from_nanos(99)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_add(Duration::from_nanos(100)),
            FileTime::MAX
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn saturating_add_roundtrip(dur: std::time::Duration) {
        use std::time::Duration;

        use proptest::{prop_assert_eq, prop_assert_ne};

        if dur <= Duration::new(1_844_674_407_370, 955_161_400) {
            prop_assert_ne!(FileTime::NT_TIME_EPOCH.saturating_add(dur), FileTime::MAX);
        } else {
            prop_assert_eq!(FileTime::NT_TIME_EPOCH.saturating_add(dur), FileTime::MAX);
        }
    }

    #[test]
    fn saturating_sub() {
        use core::time::Duration;

        assert_eq!(FileTime::MAX.saturating_sub(Duration::ZERO), FileTime::MAX);
        assert_eq!(
            FileTime::MAX.saturating_sub(Duration::from_nanos(1)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_sub(Duration::from_nanos(99)),
            FileTime::MAX
        );
        assert_eq!(
            FileTime::MAX.saturating_sub(Duration::from_nanos(100)),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::ZERO),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(1)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(99)),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH.saturating_sub(Duration::from_nanos(100)),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "std")]
    #[test_strategy::proptest]
    fn saturating_sub_roundtrip(dur: std::time::Duration) {
        use std::time::Duration;

        use proptest::{prop_assert_eq, prop_assert_ne};

        if dur <= Duration::new(1_844_674_407_370, 955_161_400) {
            prop_assert_ne!(FileTime::MAX.saturating_sub(dur), FileTime::NT_TIME_EPOCH);
        } else {
            prop_assert_eq!(FileTime::MAX.saturating_sub(dur), FileTime::NT_TIME_EPOCH);
        }
    }

    #[test]
    fn add_std_duration() {
        use core::time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::from_nanos(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::from_nanos(99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::from_nanos(100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX + Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::from_nanos(1), FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::from_nanos(99), FileTime::MAX);
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_std_duration_with_overflow() {
        use core::time::Duration;

        let _ = FileTime::MAX + Duration::from_nanos(100);
    }

    #[test]
    fn add_positive_time_duration() {
        use time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::nanoseconds(100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX + Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::nanoseconds(99), FileTime::MAX);
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_positive_time_duration_with_overflow() {
        use time::Duration;

        let _ = FileTime::MAX + Duration::nanoseconds(100);
    }

    #[test]
    fn add_negative_time_duration() {
        use time::Duration;

        assert_eq!(FileTime::MAX + -Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX + -Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX + Duration::nanoseconds(-99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX + Duration::nanoseconds(-100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH + -Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + -Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + Duration::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_negative_time_duration_with_overflow() {
        use time::Duration;

        let _ = FileTime::NT_TIME_EPOCH + Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX + TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX + TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX + TimeDelta::nanoseconds(99), FileTime::MAX);
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _ = FileTime::MAX + TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(FileTime::MAX + -TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX + -TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX + TimeDelta::nanoseconds(-99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX + TimeDelta::nanoseconds(-100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH + -TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + -TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _ = FileTime::NT_TIME_EPOCH + TimeDelta::nanoseconds(-100);
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn add_positive_jiff_span() {
        use jiff::{Span, ToSpan};

        assert_eq!(
            FileTime::NT_TIME_EPOCH + Span::new(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + 1.nanosecond(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + 99.nanoseconds(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + 100.nanoseconds(),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX + Span::new(), FileTime::MAX);
        assert_eq!(FileTime::MAX + 1.nanosecond(), FileTime::MAX);
        assert_eq!(FileTime::MAX + 99.nanoseconds(), FileTime::MAX);
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_positive_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let _ = FileTime::MAX + 100.nanoseconds();
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn add_negative_jiff_span() {
        use jiff::{Span, ToSpan};

        assert_eq!(FileTime::MAX + -Span::new(), FileTime::MAX);
        assert_eq!(FileTime::MAX + (-1).nanosecond(), FileTime::MAX);
        assert_eq!(FileTime::MAX + (-99).nanoseconds(), FileTime::MAX);
        assert_eq!(
            FileTime::MAX + (-100).nanoseconds(),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH + -Span::new(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + (-1).nanosecond(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH + (-99).nanoseconds(),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_negative_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let _ = FileTime::NT_TIME_EPOCH + (-100).nanoseconds();
    }

    #[test]
    fn add_assign_std_duration() {
        use core::time::Duration;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::from_nanos(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::from_nanos(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::from_nanos(100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::from_nanos(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::from_nanos(99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_assign_std_duration_with_overflow() {
        use core::time::Duration;

        let mut ft = FileTime::MAX;
        ft += Duration::from_nanos(100);
    }

    #[test]
    fn add_assign_positive_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::nanoseconds(100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft += Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_assign_positive_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::MAX;
        ft += Duration::nanoseconds(100);
    }

    #[test]
    fn add_assign_negative_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::MAX;
            ft += -Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += Duration::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_assign_negative_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft += Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_assign_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_assign_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::MAX;
        ft += TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn add_assign_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::MAX;
            ft += -TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += TimeDelta::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_assign_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft += TimeDelta::nanoseconds(-100);
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn add_assign_positive_jiff_span() {
        use jiff::{Span, ToSpan};

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += Span::new();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += 1.nanosecond();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += 99.nanoseconds();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += 100.nanoseconds();
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft += Span::new();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += 1.nanosecond();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += 99.nanoseconds();
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn add_assign_positive_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let mut ft = FileTime::MAX;
        ft += 100.nanoseconds();
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn add_assign_negative_jiff_span() {
        use jiff::{Span, ToSpan};

        {
            let mut ft = FileTime::MAX;
            ft += -Span::new();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += (-1).nanosecond();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += (-99).nanoseconds();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft += (-100).nanoseconds();
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += -Span::new();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += (-1).nanosecond();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft += (-99).nanoseconds();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn add_assign_negative_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft += (-100).nanoseconds();
    }

    #[test]
    fn sub_file_time() {
        use core::time::Duration;

        assert_eq!(FileTime::MAX - FileTime::MAX, Duration::ZERO);
        assert_eq!(
            FileTime::MAX - (FileTime::MAX - Duration::from_nanos(100)),
            Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::MAX - FileTime::NT_TIME_EPOCH,
            Duration::new(1_844_674_407_370, 955_161_500)
        );
    }

    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn sub_file_time_with_overflow() {
        use core::time::Duration;

        let _ = (FileTime::MAX - Duration::from_nanos(100)) - FileTime::MAX;
    }

    #[test]
    fn sub_std_duration() {
        use core::time::Duration;

        assert_eq!(FileTime::MAX - Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::from_nanos(1), FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::from_nanos(99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX - Duration::from_nanos(100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::from_nanos(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::from_nanos(99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_std_duration_with_overflow() {
        use core::time::Duration;

        let _ = FileTime::NT_TIME_EPOCH - Duration::from_nanos(100);
    }

    #[test]
    fn sub_positive_time_duration() {
        use time::Duration;

        assert_eq!(FileTime::MAX - Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::nanoseconds(99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX - Duration::nanoseconds(100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_positive_time_duration_with_overflow() {
        use time::Duration;

        let _ = FileTime::NT_TIME_EPOCH - Duration::nanoseconds(100);
    }

    #[test]
    fn sub_negative_time_duration() {
        use time::Duration;

        assert_eq!(
            FileTime::NT_TIME_EPOCH - -Duration::ZERO,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - -Duration::NANOSECOND,
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - Duration::nanoseconds(-100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX - -Duration::ZERO, FileTime::MAX);
        assert_eq!(FileTime::MAX - -Duration::NANOSECOND, FileTime::MAX);
        assert_eq!(FileTime::MAX - Duration::nanoseconds(-99), FileTime::MAX);
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_negative_time_duration_with_overflow() {
        use time::Duration;

        let _ = FileTime::MAX - Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(FileTime::MAX - TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX - TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX - TimeDelta::nanoseconds(99), FileTime::MAX);
        assert_eq!(
            FileTime::MAX - TimeDelta::nanoseconds(100),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(99),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _ = FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        assert_eq!(
            FileTime::NT_TIME_EPOCH - -TimeDelta::zero(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - -TimeDelta::nanoseconds(1),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(-99),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - TimeDelta::nanoseconds(-100),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX - -TimeDelta::zero(), FileTime::MAX);
        assert_eq!(FileTime::MAX - -TimeDelta::nanoseconds(1), FileTime::MAX);
        assert_eq!(FileTime::MAX - TimeDelta::nanoseconds(-99), FileTime::MAX);
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let _ = FileTime::MAX - TimeDelta::nanoseconds(-100);
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn sub_positive_jiff_span() {
        use jiff::{Span, ToSpan};

        assert_eq!(FileTime::MAX - Span::new(), FileTime::MAX);
        assert_eq!(FileTime::MAX - 1.nanosecond(), FileTime::MAX);
        assert_eq!(FileTime::MAX - 99.nanoseconds(), FileTime::MAX);
        assert_eq!(
            FileTime::MAX - 100.nanoseconds(),
            FileTime::new(u64::MAX - 1)
        );

        assert_eq!(
            FileTime::NT_TIME_EPOCH - Span::new(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - 1.nanosecond(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - 99.nanoseconds(),
            FileTime::NT_TIME_EPOCH
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_positive_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let _ = FileTime::NT_TIME_EPOCH - 100.nanoseconds();
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn sub_negative_jiff_span() {
        use jiff::{Span, ToSpan};

        assert_eq!(
            FileTime::NT_TIME_EPOCH - -Span::new(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - (-1).nanosecond(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - (-99).nanoseconds(),
            FileTime::NT_TIME_EPOCH
        );
        assert_eq!(
            FileTime::NT_TIME_EPOCH - (-100).nanoseconds(),
            FileTime::new(1)
        );

        assert_eq!(FileTime::MAX - -Span::new(), FileTime::MAX);
        assert_eq!(FileTime::MAX - (-1).nanosecond(), FileTime::MAX);
        assert_eq!(FileTime::MAX - (-99).nanoseconds(), FileTime::MAX);
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_negative_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let _ = FileTime::MAX - (-100).nanoseconds();
    }

    #[cfg(feature = "std")]
    #[test]
    fn sub_file_time_from_system_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
                - FileTime::new(9_223_372_036_854_775_807),
            Duration::ZERO
        );
        assert_eq!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
                - FileTime::new(9_223_372_036_854_775_806),
            Duration::from_nanos(100)
        );
        assert_eq!(
            (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700))
                - FileTime::UNIX_EPOCH,
            Duration::new(910_692_730_085, 477_580_700)
        );
    }

    #[cfg(feature = "std")]
    #[test]
    #[should_panic(expected = "RHS provided is later than LHS")]
    fn sub_file_time_from_system_time_with_overflow() {
        use std::time::{Duration, SystemTime};

        let _ = FileTime::new(9_223_372_036_854_775_806)
            - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700));
    }

    #[cfg(feature = "std")]
    #[test]
    fn sub_system_time_from_file_time() {
        use std::time::{Duration, SystemTime};

        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_700)),
            Duration::ZERO
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_699)),
            Duration::from_nanos(if cfg!(windows) { 100 } else { 1 })
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_601)),
            Duration::from_nanos(if cfg!(windows) { 100 } else { 99 })
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807)
                - (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_600)),
            Duration::from_nanos(100)
        );
        assert_eq!(
            FileTime::new(9_223_372_036_854_775_807) - SystemTime::UNIX_EPOCH,
            Duration::new(910_692_730_085, 477_580_700)
        );
    }

    #[cfg(feature = "std")]
    #[test]
    #[should_panic(expected = "RHS provided is later than LHS")]
    fn sub_system_time_from_file_time_with_overflow() {
        use std::time::{Duration, SystemTime};

        let _ = (SystemTime::UNIX_EPOCH + Duration::new(910_692_730_085, 477_580_600))
            - FileTime::new(9_223_372_036_854_775_807);
    }

    #[test]
    fn sub_file_time_from_offset_date_time() {
        use time::Duration;

        assert_eq!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
                - FileTime::new(2_650_467_743_999_999_999),
            Duration::ZERO
        );
        assert_eq!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC)
                - (FileTime::new(2_650_467_743_999_999_999) - Duration::nanoseconds(100)),
            Duration::nanoseconds(100)
        );
        assert_eq!(
            datetime!(9999-12-31 23:59:59.999_999_900 UTC) - FileTime::NT_TIME_EPOCH,
            Duration::new(265_046_774_399, 999_999_900)
        );
    }

    #[test]
    fn sub_offset_date_time_from_file_time() {
        use time::Duration;

        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - datetime!(9999-12-31 23:59:59.999_999_900 UTC),
            Duration::ZERO
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - (datetime!(9999-12-31 23:59:59.999_999_900 UTC) - Duration::nanoseconds(1)),
            Duration::nanoseconds(1)
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - (datetime!(9999-12-31 23:59:59.999_999_900 UTC) - Duration::nanoseconds(99)),
            Duration::nanoseconds(99)
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999)
                - (datetime!(9999-12-31 23:59:59.999_999_900 UTC) - Duration::nanoseconds(100)),
            Duration::nanoseconds(100)
        );
        assert_eq!(
            FileTime::new(2_650_467_743_999_999_999) - datetime!(1601-01-01 00:00 UTC),
            Duration::new(265_046_774_399, 999_999_900)
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_file_time_from_chrono_date_time() {
        use core::time::Duration;

        use chrono::{DateTime, TimeDelta, Utc};

        assert_eq!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
                - FileTime::MAX,
            TimeDelta::zero()
        );
        assert_eq!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
                - (FileTime::MAX - Duration::from_nanos(100)),
            TimeDelta::nanoseconds(100)
        );
        assert_eq!(
            "+60056-05-28 05:36:10.955161500 UTC"
                .parse::<DateTime<Utc>>()
                .unwrap()
                - FileTime::NT_TIME_EPOCH,
            TimeDelta::new(1_844_674_407_370, 955_161_500).unwrap()
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_chrono_date_time_from_file_time() {
        use chrono::{DateTime, TimeDelta, Utc};

        assert_eq!(
            FileTime::MAX
                - "+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap(),
            TimeDelta::zero()
        );
        assert_eq!(
            FileTime::MAX
                - ("+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
                    - TimeDelta::nanoseconds(1)),
            TimeDelta::nanoseconds(1)
        );
        assert_eq!(
            FileTime::MAX
                - ("+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
                    - TimeDelta::nanoseconds(99)),
            TimeDelta::nanoseconds(99)
        );
        assert_eq!(
            FileTime::MAX
                - ("+60056-05-28 05:36:10.955161500 UTC"
                    .parse::<DateTime<Utc>>()
                    .unwrap()
                    - TimeDelta::nanoseconds(100)),
            TimeDelta::nanoseconds(100)
        );
        assert_eq!(
            FileTime::MAX - "1601-01-01 00:00:00 UTC".parse::<DateTime<Utc>>().unwrap(),
            TimeDelta::new(1_844_674_407_370, 955_161_500).unwrap()
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn sub_file_time_from_jiff_timestamp() {
        use jiff::{Span, Timestamp, ToSpan};

        assert_eq!(
            (Timestamp::MAX - 99.nanoseconds()) - FileTime::new(2_650_466_808_009_999_999),
            Span::new().fieldwise()
        );
        assert_eq!(
            (Timestamp::MAX - 99.nanoseconds())
                - (FileTime::new(2_650_466_808_009_999_999) - 100.nanoseconds()),
            100.nanoseconds().fieldwise()
        );
        assert_eq!(
            (Timestamp::MAX - 99.nanoseconds()) - FileTime::NT_TIME_EPOCH,
            265_046_680_800_i64
                .seconds()
                .milliseconds(999)
                .microseconds(999)
                .nanoseconds(900)
                .fieldwise()
        );
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn sub_jiff_timestamp_from_file_time() {
        use jiff::{Span, Timestamp, ToSpan};

        assert_eq!(
            FileTime::new(2_650_466_808_009_999_999) - (Timestamp::MAX - 99.nanoseconds()),
            Span::new().fieldwise()
        );
        assert_eq!(
            FileTime::new(2_650_466_808_009_999_999)
                - ((Timestamp::MAX - 99.nanoseconds()) - 1.nanosecond()),
            1.nanosecond().fieldwise()
        );
        assert_eq!(
            FileTime::new(2_650_466_808_009_999_999)
                - ((Timestamp::MAX - 99.nanoseconds()) - 99.nanoseconds()),
            99.nanoseconds().fieldwise()
        );
        assert_eq!(
            FileTime::new(2_650_466_808_009_999_999)
                - ((Timestamp::MAX - 99.nanoseconds()) - 100.nanoseconds()),
            100.nanoseconds().fieldwise()
        );
        assert_eq!(
            FileTime::new(2_650_466_808_009_999_999)
                - Timestamp::from_second(-11_644_473_600).unwrap(),
            265_046_680_800_i64
                .seconds()
                .milliseconds(999)
                .microseconds(999)
                .nanoseconds(900)
                .fieldwise()
        );
    }

    #[test]
    fn sub_assign_std_duration() {
        use core::time::Duration;

        {
            let mut ft = FileTime::MAX;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::from_nanos(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::from_nanos(99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::from_nanos(100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::from_nanos(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::from_nanos(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_assign_std_duration_with_overflow() {
        use core::time::Duration;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft -= Duration::from_nanos(100);
    }

    #[test]
    fn sub_assign_positive_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::MAX;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::nanoseconds(100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_assign_positive_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft -= Duration::nanoseconds(100);
    }

    #[test]
    fn sub_assign_negative_time_duration() {
        use time::Duration;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -Duration::ZERO;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Duration::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft -= -Duration::ZERO;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= -Duration::NANOSECOND;
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= Duration::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_assign_negative_time_duration_with_overflow() {
        use time::Duration;

        let mut ft = FileTime::MAX;
        ft -= Duration::nanoseconds(-100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_assign_positive_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(100);
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_assign_positive_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft -= TimeDelta::nanoseconds(100);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn sub_assign_negative_chrono_time_delta() {
        use chrono::TimeDelta;

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -TimeDelta::zero();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= TimeDelta::nanoseconds(-100);
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft -= -TimeDelta::zero();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= -TimeDelta::nanoseconds(1);
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= TimeDelta::nanoseconds(-99);
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_assign_negative_chrono_time_delta_with_overflow() {
        use chrono::TimeDelta;

        let mut ft = FileTime::MAX;
        ft -= TimeDelta::nanoseconds(-100);
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn sub_assign_positive_jiff_span() {
        use jiff::{Span, ToSpan};

        {
            let mut ft = FileTime::MAX;
            ft -= Span::new();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= 1.nanosecond();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= 99.nanoseconds();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= 100.nanoseconds();
            assert_eq!(ft, FileTime::new(u64::MAX - 1));
        }

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= Span::new();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= 1.nanosecond();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= 99.nanoseconds();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when subtracting duration from date and time")]
    fn sub_assign_positive_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let mut ft = FileTime::NT_TIME_EPOCH;
        ft -= 100.nanoseconds();
    }

    #[cfg(feature = "jiff")]
    #[test]
    fn sub_assign_negative_jiff_span() {
        use jiff::{Span, ToSpan};

        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= -Span::new();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= (-1).nanosecond();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= (-99).nanoseconds();
            assert_eq!(ft, FileTime::NT_TIME_EPOCH);
        }
        {
            let mut ft = FileTime::NT_TIME_EPOCH;
            ft -= (-100).nanoseconds();
            assert_eq!(ft, FileTime::new(1));
        }

        {
            let mut ft = FileTime::MAX;
            ft -= -Span::new();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= (-1).nanosecond();
            assert_eq!(ft, FileTime::MAX);
        }
        {
            let mut ft = FileTime::MAX;
            ft -= (-99).nanoseconds();
            assert_eq!(ft, FileTime::MAX);
        }
    }

    #[cfg(feature = "jiff")]
    #[test]
    #[should_panic(expected = "overflow when adding duration to date and time")]
    fn sub_assign_negative_jiff_span_with_overflow() {
        use jiff::ToSpan;

        let mut ft = FileTime::MAX;
        ft -= (-100).nanoseconds();
    }
}
