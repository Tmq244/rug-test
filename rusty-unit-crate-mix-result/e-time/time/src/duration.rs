//! The [`Duration`] struct and its associated `impl`s.

use core::cmp::Ordering;
use core::convert::{TryFrom, TryInto};
use core::fmt;
use core::iter::Sum;
use core::ops::{Add, Div, Mul, Neg, Sub, SubAssign};
use core::time::Duration as StdDuration;

use crate::error;
#[cfg(feature = "std")]
use crate::Instant;

/// By explicitly inserting this enum where padding is expected, the compiler is able to better
/// perform niche value optimization.
#[repr(u32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Padding {
    #[allow(clippy::missing_docs_in_private_items)]
    Optimize,
}

impl Default for Padding {
    fn default() -> Self {
        Self::Optimize
    }
}

/// A span of time with nanosecond precision.
///
/// Each `Duration` is composed of a whole number of seconds and a fractional part represented in
/// nanoseconds.
///
/// This implementation allows for negative durations, unlike [`core::time::Duration`].
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Duration {
    /// Number of whole seconds.
    seconds: i64,
    /// Number of nanoseconds within the second. The sign always matches the `seconds` field.
    nanoseconds: i32, // always -10^9 < nanoseconds < 10^9
    #[allow(clippy::missing_docs_in_private_items)]
    padding: Padding,
}

impl fmt::Debug for Duration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Duration")
            .field("seconds", &self.seconds)
            .field("nanoseconds", &self.nanoseconds)
            .finish()
    }
}

impl Duration {
    // region: constants
    /// Equivalent to `0.seconds()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::ZERO, 0.seconds());
    /// ```
    pub const ZERO: Self = Self::seconds(0);

    /// Equivalent to `1.nanoseconds()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::NANOSECOND, 1.nanoseconds());
    /// ```
    pub const NANOSECOND: Self = Self::nanoseconds(1);

    /// Equivalent to `1.microseconds()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::MICROSECOND, 1.microseconds());
    /// ```
    pub const MICROSECOND: Self = Self::microseconds(1);

    /// Equivalent to `1.milliseconds()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::MILLISECOND, 1.milliseconds());
    /// ```
    pub const MILLISECOND: Self = Self::milliseconds(1);

    /// Equivalent to `1.seconds()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::SECOND, 1.seconds());
    /// ```
    pub const SECOND: Self = Self::seconds(1);

    /// Equivalent to `1.minutes()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::MINUTE, 1.minutes());
    /// ```
    pub const MINUTE: Self = Self::minutes(1);

    /// Equivalent to `1.hours()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::HOUR, 1.hours());
    /// ```
    pub const HOUR: Self = Self::hours(1);

    /// Equivalent to `1.days()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::DAY, 1.days());
    /// ```
    pub const DAY: Self = Self::days(1);

    /// Equivalent to `1.weeks()`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::WEEK, 1.weeks());
    /// ```
    pub const WEEK: Self = Self::weeks(1);

    /// The minimum possible duration. Adding any negative duration to this will cause an overflow.
    pub const MIN: Self = Self::new_unchecked(i64::MIN, -999_999_999);

    /// The maximum possible duration. Adding any positive duration to this will cause an overflow.
    pub const MAX: Self = Self::new_unchecked(i64::MAX, 999_999_999);
    // endregion constants

    // region: is_{sign}
    /// Check if a duration is exactly zero.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert!(0.seconds().is_zero());
    /// assert!(!1.nanoseconds().is_zero());
    /// ```
    pub const fn is_zero(self) -> bool {
        self.seconds == 0 && self.nanoseconds == 0
    }

    /// Check if a duration is negative.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert!((-1).seconds().is_negative());
    /// assert!(!0.seconds().is_negative());
    /// assert!(!1.seconds().is_negative());
    /// ```
    pub const fn is_negative(self) -> bool {
        self.seconds < 0 || self.nanoseconds < 0
    }

    /// Check if a duration is positive.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert!(1.seconds().is_positive());
    /// assert!(!0.seconds().is_positive());
    /// assert!(!(-1).seconds().is_positive());
    /// ```
    pub const fn is_positive(self) -> bool {
        self.seconds > 0 || self.nanoseconds > 0
    }
    // endregion is_{sign}

    // region: abs
    /// Get the absolute value of the duration.
    ///
    /// This method saturates the returned value if it would otherwise overflow.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.seconds().abs(), 1.seconds());
    /// assert_eq!(0.seconds().abs(), 0.seconds());
    /// assert_eq!((-1).seconds().abs(), 1.seconds());
    /// ```
    pub const fn abs(self) -> Self {
        Self::new_unchecked(self.seconds.saturating_abs(), self.nanoseconds.abs())
    }

    /// Convert the existing `Duration` to a `std::time::Duration` and its sign. This doesn't
    /// actually require the standard library, but is currently only used when it's enabled.
    #[allow(clippy::missing_const_for_fn)] // false positive
    #[cfg(feature = "std")]
    pub(crate) fn abs_std(self) -> StdDuration {
        StdDuration::new(self.seconds.unsigned_abs(), self.nanoseconds.unsigned_abs())
    }
    // endregion abs

    // region: constructors
    /// Create a new `Duration` without checking the validity of the components.
    pub(crate) const fn new_unchecked(seconds: i64, nanoseconds: i32) -> Self {
        Self {
            seconds,
            nanoseconds,
            padding: Padding::Optimize,
        }
    }

    /// Create a new `Duration` with the provided seconds and nanoseconds. If nanoseconds is at
    /// least ±10<sup>9</sup>, it will wrap to the number of seconds.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::new(1, 0), 1.seconds());
    /// assert_eq!(Duration::new(-1, 0), (-1).seconds());
    /// assert_eq!(Duration::new(1, 2_000_000_000), 3.seconds());
    /// ```
    pub const fn new(mut seconds: i64, mut nanoseconds: i32) -> Self {
        seconds += nanoseconds as i64 / 1_000_000_000;
        nanoseconds %= 1_000_000_000;

        if seconds > 0 && nanoseconds < 0 {
            seconds -= 1;
            nanoseconds += 1_000_000_000;
        } else if seconds < 0 && nanoseconds > 0 {
            seconds += 1;
            nanoseconds -= 1_000_000_000;
        }

        Self::new_unchecked(seconds, nanoseconds)
    }

    /// Create a new `Duration` with the given number of weeks. Equivalent to
    /// `Duration::seconds(weeks * 604_800)`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::weeks(1), 604_800.seconds());
    /// ```
    pub const fn weeks(weeks: i64) -> Self {
        Self::seconds(weeks * 604_800)
    }

    /// Create a new `Duration` with the given number of days. Equivalent to
    /// `Duration::seconds(days * 86_400)`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::days(1), 86_400.seconds());
    /// ```
    pub const fn days(days: i64) -> Self {
        Self::seconds(days * 86_400)
    }

    /// Create a new `Duration` with the given number of hours. Equivalent to
    /// `Duration::seconds(hours * 3_600)`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::hours(1), 3_600.seconds());
    /// ```
    pub const fn hours(hours: i64) -> Self {
        Self::seconds(hours * 3_600)
    }

    /// Create a new `Duration` with the given number of minutes. Equivalent to
    /// `Duration::seconds(minutes * 60)`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::minutes(1), 60.seconds());
    /// ```
    pub const fn minutes(minutes: i64) -> Self {
        Self::seconds(minutes * 60)
    }

    /// Create a new `Duration` with the given number of seconds.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::seconds(1), 1_000.milliseconds());
    /// ```
    pub const fn seconds(seconds: i64) -> Self {
        Self::new_unchecked(seconds, 0)
    }

    /// Creates a new `Duration` from the specified number of seconds represented as `f64`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::seconds_f64(0.5), 0.5.seconds());
    /// assert_eq!(Duration::seconds_f64(-0.5), -0.5.seconds());
    /// ```
    pub fn seconds_f64(seconds: f64) -> Self {
        Self::new_unchecked(seconds as _, ((seconds % 1.) * 1_000_000_000.) as _)
    }

    /// Creates a new `Duration` from the specified number of seconds represented as `f32`.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::seconds_f32(0.5), 0.5.seconds());
    /// assert_eq!(Duration::seconds_f32(-0.5), (-0.5).seconds());
    /// ```
    pub fn seconds_f32(seconds: f32) -> Self {
        Self::new_unchecked(seconds as _, ((seconds % 1.) * 1_000_000_000.) as _)
    }

    /// Create a new `Duration` with the given number of milliseconds.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::milliseconds(1), 1_000.microseconds());
    /// assert_eq!(Duration::milliseconds(-1), (-1_000).microseconds());
    /// ```
    pub const fn milliseconds(milliseconds: i64) -> Self {
        Self::new_unchecked(
            milliseconds / 1_000,
            ((milliseconds % 1_000) * 1_000_000) as _,
        )
    }

    /// Create a new `Duration` with the given number of microseconds.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::microseconds(1), 1_000.nanoseconds());
    /// assert_eq!(Duration::microseconds(-1), (-1_000).nanoseconds());
    /// ```
    pub const fn microseconds(microseconds: i64) -> Self {
        Self::new_unchecked(
            microseconds / 1_000_000,
            ((microseconds % 1_000_000) * 1_000) as _,
        )
    }

    /// Create a new `Duration` with the given number of nanoseconds.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(Duration::nanoseconds(1), 1.microseconds() / 1_000);
    /// assert_eq!(Duration::nanoseconds(-1), (-1).microseconds() / 1_000);
    /// ```
    pub const fn nanoseconds(nanoseconds: i64) -> Self {
        Self::new_unchecked(
            nanoseconds / 1_000_000_000,
            (nanoseconds % 1_000_000_000) as _,
        )
    }

    /// Create a new `Duration` with the given number of nanoseconds.
    ///
    /// As the input range cannot be fully mapped to the output, this should only be used where it's
    /// known to result in a valid value.
    pub(crate) const fn nanoseconds_i128(nanoseconds: i128) -> Self {
        Self::new_unchecked(
            (nanoseconds / 1_000_000_000) as _,
            (nanoseconds % 1_000_000_000) as _,
        )
    }
    // endregion constructors

    // region: getters
    /// Get the number of whole weeks in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.weeks().whole_weeks(), 1);
    /// assert_eq!((-1).weeks().whole_weeks(), -1);
    /// assert_eq!(6.days().whole_weeks(), 0);
    /// assert_eq!((-6).days().whole_weeks(), 0);
    /// ```
    pub const fn whole_weeks(self) -> i64 {
        self.whole_seconds() / 604_800
    }

    /// Get the number of whole days in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.days().whole_days(), 1);
    /// assert_eq!((-1).days().whole_days(), -1);
    /// assert_eq!(23.hours().whole_days(), 0);
    /// assert_eq!((-23).hours().whole_days(), 0);
    /// ```
    pub const fn whole_days(self) -> i64 {
        self.whole_seconds() / 86_400
    }

    /// Get the number of whole hours in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.hours().whole_hours(), 1);
    /// assert_eq!((-1).hours().whole_hours(), -1);
    /// assert_eq!(59.minutes().whole_hours(), 0);
    /// assert_eq!((-59).minutes().whole_hours(), 0);
    /// ```
    pub const fn whole_hours(self) -> i64 {
        self.whole_seconds() / 3_600
    }

    /// Get the number of whole minutes in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.minutes().whole_minutes(), 1);
    /// assert_eq!((-1).minutes().whole_minutes(), -1);
    /// assert_eq!(59.seconds().whole_minutes(), 0);
    /// assert_eq!((-59).seconds().whole_minutes(), 0);
    /// ```
    pub const fn whole_minutes(self) -> i64 {
        self.whole_seconds() / 60
    }

    /// Get the number of whole seconds in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.seconds().whole_seconds(), 1);
    /// assert_eq!((-1).seconds().whole_seconds(), -1);
    /// assert_eq!(1.minutes().whole_seconds(), 60);
    /// assert_eq!((-1).minutes().whole_seconds(), -60);
    /// ```
    pub const fn whole_seconds(self) -> i64 {
        self.seconds
    }

    /// Get the number of fractional seconds in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.5.seconds().as_seconds_f64(), 1.5);
    /// assert_eq!((-1.5).seconds().as_seconds_f64(), -1.5);
    /// ```
    pub fn as_seconds_f64(self) -> f64 {
        self.seconds as f64 + self.nanoseconds as f64 / 1_000_000_000.
    }

    /// Get the number of fractional seconds in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.5.seconds().as_seconds_f32(), 1.5);
    /// assert_eq!((-1.5).seconds().as_seconds_f32(), -1.5);
    /// ```
    pub fn as_seconds_f32(self) -> f32 {
        self.seconds as f32 + self.nanoseconds as f32 / 1_000_000_000.
    }

    /// Get the number of whole milliseconds in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.seconds().whole_milliseconds(), 1_000);
    /// assert_eq!((-1).seconds().whole_milliseconds(), -1_000);
    /// assert_eq!(1.milliseconds().whole_milliseconds(), 1);
    /// assert_eq!((-1).milliseconds().whole_milliseconds(), -1);
    /// ```
    pub const fn whole_milliseconds(self) -> i128 {
        self.seconds as i128 * 1_000 + self.nanoseconds as i128 / 1_000_000
    }

    /// Get the number of milliseconds past the number of whole seconds.
    ///
    /// Always in the range `-1_000..1_000`.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.4.seconds().subsec_milliseconds(), 400);
    /// assert_eq!((-1.4).seconds().subsec_milliseconds(), -400);
    /// ```
    // Allow the lint, as the value is guaranteed to be less than 1000.
    pub const fn subsec_milliseconds(self) -> i16 {
        (self.nanoseconds / 1_000_000) as _
    }

    /// Get the number of whole microseconds in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.milliseconds().whole_microseconds(), 1_000);
    /// assert_eq!((-1).milliseconds().whole_microseconds(), -1_000);
    /// assert_eq!(1.microseconds().whole_microseconds(), 1);
    /// assert_eq!((-1).microseconds().whole_microseconds(), -1);
    /// ```
    pub const fn whole_microseconds(self) -> i128 {
        self.seconds as i128 * 1_000_000 + self.nanoseconds as i128 / 1_000
    }

    /// Get the number of microseconds past the number of whole seconds.
    ///
    /// Always in the range `-1_000_000..1_000_000`.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.0004.seconds().subsec_microseconds(), 400);
    /// assert_eq!((-1.0004).seconds().subsec_microseconds(), -400);
    /// ```
    pub const fn subsec_microseconds(self) -> i32 {
        self.nanoseconds / 1_000
    }

    /// Get the number of nanoseconds in the duration.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.microseconds().whole_nanoseconds(), 1_000);
    /// assert_eq!((-1).microseconds().whole_nanoseconds(), -1_000);
    /// assert_eq!(1.nanoseconds().whole_nanoseconds(), 1);
    /// assert_eq!((-1).nanoseconds().whole_nanoseconds(), -1);
    /// ```
    pub const fn whole_nanoseconds(self) -> i128 {
        self.seconds as i128 * 1_000_000_000 + self.nanoseconds as i128
    }

    /// Get the number of nanoseconds past the number of whole seconds.
    ///
    /// The returned value will always be in the range `-1_000_000_000..1_000_000_000`.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(1.000_000_400.seconds().subsec_nanoseconds(), 400);
    /// assert_eq!((-1.000_000_400).seconds().subsec_nanoseconds(), -400);
    /// ```
    pub const fn subsec_nanoseconds(self) -> i32 {
        self.nanoseconds
    }
    // endregion getters

    // region: checked arithmetic
    /// Computes `self + rhs`, returning `None` if an overflow occurred.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(5.seconds().checked_add(5.seconds()), Some(10.seconds()));
    /// assert_eq!(Duration::MAX.checked_add(1.nanoseconds()), None);
    /// assert_eq!((-5).seconds().checked_add(5.seconds()), Some(0.seconds()));
    /// ```
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        let mut seconds = const_try_opt!(self.seconds.checked_add(rhs.seconds));
        let mut nanoseconds = self.nanoseconds + rhs.nanoseconds;

        if nanoseconds >= 1_000_000_000 || seconds < 0 && nanoseconds > 0 {
            nanoseconds -= 1_000_000_000;
            seconds = const_try_opt!(seconds.checked_add(1));
        } else if nanoseconds <= -1_000_000_000 || seconds > 0 && nanoseconds < 0 {
            nanoseconds += 1_000_000_000;
            seconds = const_try_opt!(seconds.checked_sub(1));
        }

        Some(Self::new_unchecked(seconds, nanoseconds))
    }

    /// Computes `self - rhs`, returning `None` if an overflow occurred.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(5.seconds().checked_sub(5.seconds()), Some(Duration::ZERO));
    /// assert_eq!(Duration::MIN.checked_sub(1.nanoseconds()), None);
    /// assert_eq!(5.seconds().checked_sub(10.seconds()), Some((-5).seconds()));
    /// ```
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        let mut seconds = const_try_opt!(self.seconds.checked_sub(rhs.seconds));
        let mut nanoseconds = self.nanoseconds - rhs.nanoseconds;

        if nanoseconds >= 1_000_000_000 || seconds < 0 && nanoseconds > 0 {
            nanoseconds -= 1_000_000_000;
            seconds = const_try_opt!(seconds.checked_add(1));
        } else if nanoseconds <= -1_000_000_000 || seconds > 0 && nanoseconds < 0 {
            nanoseconds += 1_000_000_000;
            seconds = const_try_opt!(seconds.checked_sub(1));
        }

        Some(Self::new_unchecked(seconds, nanoseconds))
    }

    /// Computes `self * rhs`, returning `None` if an overflow occurred.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(5.seconds().checked_mul(2), Some(10.seconds()));
    /// assert_eq!(5.seconds().checked_mul(-2), Some((-10).seconds()));
    /// assert_eq!(5.seconds().checked_mul(0), Some(0.seconds()));
    /// assert_eq!(Duration::MAX.checked_mul(2), None);
    /// assert_eq!(Duration::MIN.checked_mul(2), None);
    /// ```
    pub const fn checked_mul(self, rhs: i32) -> Option<Self> {
        // Multiply nanoseconds as i64, because it cannot overflow that way.
        let total_nanos = self.nanoseconds as i64 * rhs as i64;
        let extra_secs = total_nanos / 1_000_000_000;
        let nanoseconds = (total_nanos % 1_000_000_000) as _;
        let seconds = const_try_opt!(
            const_try_opt!(self.seconds.checked_mul(rhs as _)).checked_add(extra_secs)
        );

        Some(Self::new_unchecked(seconds, nanoseconds))
    }

    /// Computes `self / rhs`, returning `None` if `rhs == 0` or if the result would overflow.
    ///
    /// ```rust
    /// # use time::ext::NumericalDuration;
    /// assert_eq!(10.seconds().checked_div(2), Some(5.seconds()));
    /// assert_eq!(10.seconds().checked_div(-2), Some((-5).seconds()));
    /// assert_eq!(1.seconds().checked_div(0), None);
    /// ```
    pub const fn checked_div(self, rhs: i32) -> Option<Self> {
        let seconds = const_try_opt!(self.seconds.checked_div(rhs as i64));
        let carry = self.seconds - seconds * (rhs as i64);
        let extra_nanos = const_try_opt!((carry * 1_000_000_000).checked_div(rhs as i64));
        let nanoseconds = const_try_opt!(self.nanoseconds.checked_div(rhs)) + (extra_nanos as i32);

        Some(Self::new_unchecked(seconds, nanoseconds))
    }
    // endregion checked arithmetic

    // region: saturating arithmetic
    /// Computes `self + rhs`, saturating if an overflow occurred.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(5.seconds().saturating_add(5.seconds()), 10.seconds());
    /// assert_eq!(Duration::MAX.saturating_add(1.nanoseconds()), Duration::MAX);
    /// assert_eq!(
    ///     Duration::MIN.saturating_add((-1).nanoseconds()),
    ///     Duration::MIN
    /// );
    /// assert_eq!((-5).seconds().saturating_add(5.seconds()), Duration::ZERO);
    /// ```
    pub const fn saturating_add(self, rhs: Self) -> Self {
        let (mut seconds, overflow) = self.seconds.overflowing_add(rhs.seconds);
        if overflow {
            if self.seconds > 0 {
                return Self::MAX;
            }
            return Self::MIN;
        }
        let mut nanoseconds = self.nanoseconds + rhs.nanoseconds;

        if nanoseconds >= 1_000_000_000 || seconds < 0 && nanoseconds > 0 {
            nanoseconds -= 1_000_000_000;
            seconds = match seconds.checked_add(1) {
                Some(seconds) => seconds,
                None => return Self::MAX,
            };
        } else if nanoseconds <= -1_000_000_000 || seconds > 0 && nanoseconds < 0 {
            nanoseconds += 1_000_000_000;
            seconds = match seconds.checked_sub(1) {
                Some(seconds) => seconds,
                None => return Self::MIN,
            };
        }

        Self::new_unchecked(seconds, nanoseconds)
    }

    /// Computes `self - rhs`, saturating if an overflow occurred.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(5.seconds().saturating_sub(5.seconds()), Duration::ZERO);
    /// assert_eq!(Duration::MIN.saturating_sub(1.nanoseconds()), Duration::MIN);
    /// assert_eq!(
    ///     Duration::MAX.saturating_sub((-1).nanoseconds()),
    ///     Duration::MAX
    /// );
    /// assert_eq!(5.seconds().saturating_sub(10.seconds()), (-5).seconds());
    /// ```
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        let (mut seconds, overflow) = self.seconds.overflowing_sub(rhs.seconds);
        if overflow {
            if self.seconds > 0 {
                return Self::MAX;
            }
            return Self::MIN;
        }
        let mut nanoseconds = self.nanoseconds - rhs.nanoseconds;

        if nanoseconds >= 1_000_000_000 || seconds < 0 && nanoseconds > 0 {
            nanoseconds -= 1_000_000_000;
            seconds = match seconds.checked_add(1) {
                Some(seconds) => seconds,
                None => return Self::MAX,
            };
        } else if nanoseconds <= -1_000_000_000 || seconds > 0 && nanoseconds < 0 {
            nanoseconds += 1_000_000_000;
            seconds = match seconds.checked_sub(1) {
                Some(seconds) => seconds,
                None => return Self::MIN,
            };
        }

        Self::new_unchecked(seconds, nanoseconds)
    }

    /// Computes `self * rhs`, saturating if an overflow occurred.
    ///
    /// ```rust
    /// # use time::{Duration, ext::NumericalDuration};
    /// assert_eq!(5.seconds().saturating_mul(2), 10.seconds());
    /// assert_eq!(5.seconds().saturating_mul(-2), (-10).seconds());
    /// assert_eq!(5.seconds().saturating_mul(0), Duration::ZERO);
    /// assert_eq!(Duration::MAX.saturating_mul(2), Duration::MAX);
    /// assert_eq!(Duration::MIN.saturating_mul(2), Duration::MIN);
    /// assert_eq!(Duration::MAX.saturating_mul(-2), Duration::MIN);
    /// assert_eq!(Duration::MIN.saturating_mul(-2), Duration::MAX);
    /// ```
    pub const fn saturating_mul(self, rhs: i32) -> Self {
        // Multiply nanoseconds as i64, because it cannot overflow that way.
        let total_nanos = self.nanoseconds as i64 * rhs as i64;
        let extra_secs = total_nanos / 1_000_000_000;
        let nanoseconds = (total_nanos % 1_000_000_000) as _;
        let (seconds, overflow1) = self.seconds.overflowing_mul(rhs as _);
        if overflow1 {
            if self.seconds > 0 && rhs > 0 || self.seconds < 0 && rhs < 0 {
                return Self::MAX;
            }
            return Self::MIN;
        }
        let (seconds, overflow2) = seconds.overflowing_add(extra_secs);
        if overflow2 {
            if self.seconds > 0 && rhs > 0 {
                return Self::MAX;
            }
            return Self::MIN;
        }

        Self::new_unchecked(seconds, nanoseconds)
    }
    // endregion saturating arithmetic

    /// Runs a closure, returning the duration of time it took to run. The return value of the
    /// closure is provided in the second part of the tuple.
    #[cfg(feature = "std")]
    pub fn time_fn<T>(f: impl FnOnce() -> T) -> (Self, T) {
        let start = Instant::now();
        let return_value = f();
        let end = Instant::now();

        (end - start, return_value)
    }
}

// region: trait impls
impl TryFrom<StdDuration> for Duration {
    type Error = error::ConversionRange;

    fn try_from(original: StdDuration) -> Result<Self, error::ConversionRange> {
        Ok(Self::new(
            original
                .as_secs()
                .try_into()
                .map_err(|_| error::ConversionRange)?,
            original.subsec_nanos() as _,
        ))
    }
}

impl TryFrom<Duration> for StdDuration {
    type Error = error::ConversionRange;

    fn try_from(duration: Duration) -> Result<Self, error::ConversionRange> {
        Ok(Self::new(
            duration
                .seconds
                .try_into()
                .map_err(|_| error::ConversionRange)?,
            duration
                .nanoseconds
                .try_into()
                .map_err(|_| error::ConversionRange)?,
        ))
    }
}

impl Add for Duration {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs)
            .expect("overflow when adding durations")
    }
}

impl Add<StdDuration> for Duration {
    type Output = Self;

    fn add(self, std_duration: StdDuration) -> Self::Output {
        self + Self::try_from(std_duration)
            .expect("overflow converting `std::time::Duration` to `time::Duration`")
    }
}

impl Add<Duration> for StdDuration {
    type Output = Duration;

    fn add(self, rhs: Duration) -> Self::Output {
        rhs + self
    }
}

impl_add_assign!(Duration: Duration, StdDuration);

impl Neg for Duration {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new_unchecked(-self.seconds, -self.nanoseconds)
    }
}

impl Sub for Duration {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("overflow when subtracting durations")
    }
}

impl Sub<StdDuration> for Duration {
    type Output = Self;

    fn sub(self, rhs: StdDuration) -> Self::Output {
        self - Self::try_from(rhs)
            .expect("overflow converting `std::time::Duration` to `time::Duration`")
    }
}

impl Sub<Duration> for StdDuration {
    type Output = Duration;

    fn sub(self, rhs: Duration) -> Self::Output {
        Duration::try_from(self)
            .expect("overflow converting `std::time::Duration` to `time::Duration`")
            - rhs
    }
}

impl_sub_assign!(Duration: Duration, StdDuration);

impl SubAssign<Duration> for StdDuration {
    fn sub_assign(&mut self, rhs: Duration) {
        *self = (*self - rhs).try_into().expect(
            "Cannot represent a resulting duration in std. Try `let x = x - rhs;`, which will \
             change the type.",
        );
    }
}

/// Implement `Mul` (reflexively) and `Div` for `Duration` for various types.
macro_rules! duration_mul_div_int {
    ($($type:ty),+) => {$(
        impl Mul<$type> for Duration {
            type Output = Self;

            fn mul(self, rhs: $type) -> Self::Output {
                Self::nanoseconds_i128(
                    self.whole_nanoseconds()
                        .checked_mul(rhs as _)
                        .expect("overflow when multiplying duration")
                )
            }
        }

        impl Mul<Duration> for $type {
            type Output = Duration;

            fn mul(self, rhs: Duration) -> Self::Output {
                rhs * self
            }
        }

        impl Div<$type> for Duration {
            type Output = Self;

            fn div(self, rhs: $type) -> Self::Output {
                Self::nanoseconds_i128(self.whole_nanoseconds() / rhs as i128)
            }
        }
    )+};
}
duration_mul_div_int![i8, i16, i32, u8, u16, u32];

impl Mul<f32> for Duration {
    type Output = Self;

    fn mul(self, rhs: f32) -> Self::Output {
        Self::seconds_f32(self.as_seconds_f32() * rhs)
    }
}

impl Mul<Duration> for f32 {
    type Output = Duration;

    fn mul(self, rhs: Duration) -> Self::Output {
        rhs * self
    }
}

impl Mul<f64> for Duration {
    type Output = Self;

    fn mul(self, rhs: f64) -> Self::Output {
        Self::seconds_f64(self.as_seconds_f64() * rhs)
    }
}

impl Mul<Duration> for f64 {
    type Output = Duration;

    fn mul(self, rhs: Duration) -> Self::Output {
        rhs * self
    }
}

impl_mul_assign!(Duration: i8, i16, i32, u8, u16, u32, f32, f64);

impl Div<f32> for Duration {
    type Output = Self;

    fn div(self, rhs: f32) -> Self::Output {
        Self::seconds_f32(self.as_seconds_f32() / rhs)
    }
}

impl Div<f64> for Duration {
    type Output = Self;

    fn div(self, rhs: f64) -> Self::Output {
        Self::seconds_f64(self.as_seconds_f64() / rhs)
    }
}

impl_div_assign!(Duration: i8, i16, i32, u8, u16, u32, f32, f64);

impl Div for Duration {
    type Output = f64;

    fn div(self, rhs: Self) -> Self::Output {
        self.as_seconds_f64() / rhs.as_seconds_f64()
    }
}

impl Div<StdDuration> for Duration {
    type Output = f64;

    fn div(self, rhs: StdDuration) -> Self::Output {
        self.as_seconds_f64() / rhs.as_secs_f64()
    }
}

impl Div<Duration> for StdDuration {
    type Output = f64;

    fn div(self, rhs: Duration) -> Self::Output {
        self.as_secs_f64() / rhs.as_seconds_f64()
    }
}

impl PartialEq<StdDuration> for Duration {
    fn eq(&self, rhs: &StdDuration) -> bool {
        Ok(*self) == Self::try_from(*rhs)
    }
}

impl PartialEq<Duration> for StdDuration {
    fn eq(&self, rhs: &Duration) -> bool {
        rhs == self
    }
}

impl PartialOrd<StdDuration> for Duration {
    fn partial_cmp(&self, rhs: &StdDuration) -> Option<Ordering> {
        if rhs.as_secs() > i64::MAX as _ {
            return Some(Ordering::Less);
        }

        Some(
            self.seconds
                .cmp(&(rhs.as_secs() as _))
                .then_with(|| self.nanoseconds.cmp(&(rhs.subsec_nanos() as _))),
        )
    }
}

impl PartialOrd<Duration> for StdDuration {
    fn partial_cmp(&self, rhs: &Duration) -> Option<Ordering> {
        rhs.partial_cmp(self).map(Ordering::reverse)
    }
}

impl Sum for Duration {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|a, b| a + b).unwrap_or_default()
    }
}

impl<'a> Sum<&'a Self> for Duration {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().sum()
    }
}
// endregion trait impls

#[cfg(test)]
mod tests_rug_118 {
    use super::*;
    use crate::duration::Padding;

    #[test]
    fn test_default_padding() {
        let default_padding: Padding = Padding::default();
    }
}#[cfg(test)]
mod tests_rug_119 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = 0.seconds();

        assert!(p0.is_zero());

        let p1: Duration = 1.nanoseconds();
        assert!(!p1.is_zero());
    }
}#[cfg(test)]
mod tests_rug_120 {
    use super::*;
    use crate::duration::Duration;
    use crate::ext::NumericalDuration;

    #[test]
    fn test_is_negative() {
        let mut p0: Duration = (-1).seconds();

        assert!(p0.is_negative());

        let mut p1: Duration = 0.seconds();
        assert!(!p1.is_negative());

        let mut p2: Duration = 1.seconds();
        assert!(!p2.is_negative());
    }
}#[cfg(test)]
mod tests_rug_121 {
    use super::*;
    use crate::duration::Duration; // Add this use statement based on the sample code

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5); // Using the sample code to construct the variable

        assert!(p0.is_positive());
    }

    #[test]
    fn test_zero_duration() {
        let p0: Duration = Duration::seconds(0);

        assert!(!p0.is_positive());
    }

    #[test]
    fn test_negative_duration() {
        let p0: Duration = Duration::seconds(-1);

        assert!(!p0.is_positive());
    }
}#[cfg(test)]
mod tests_rug_122 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: Duration = 1.seconds();

        assert_eq!(p0.abs(), 1.seconds());

        let p1: Duration = 0.seconds();
        
        assert_eq!(p1.abs(), 0.seconds());

        let p2: Duration = (-1).seconds();
        
        assert_eq!(p2.abs(), 1.seconds());
    }
}#[cfg(test)]
mod tests_rug_123 {
    use super::*;
    use crate::duration::Duration;
    use std::time::Duration as StdDuration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);

        let result = <Duration>::abs_std(p0);
        assert_eq!(result, StdDuration::new(5, 0));
    }
}#[cfg(test)]
mod tests_rug_124 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: i64 = 86400; // Sample data for seconds (1 day)
        let mut p1: i32 = 123_456_789; // Sample data for nanoseconds

        <Duration>::new_unchecked(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_125 {
    use super::*;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;
        let mut p1: i32 = 2_000_000_000;

        Duration::new(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_126 {
    use super::*;
    use crate::{Duration};

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;

        Duration::weeks(p0);
    }
}#[cfg(test)]
mod tests_rug_127 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_days() {
        let p0: i64 = 1;

        Duration::days(p0);
    }
}#[cfg(test)]
mod tests_rug_128 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;

        <Duration>::hours(p0);
    }
}#[cfg(test)]
mod tests_rug_129 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;

        <Duration>::minutes(p0);
    }
}#[cfg(test)]
mod tests_rug_130 {
    use super::*;
    use crate::{Duration};

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;

        Duration::seconds(p0);
    }
}#[cfg(test)]
mod tests_rug_131 {
    use super::*;
    use crate::{Duration};

    #[test]
    fn test_seconds_f64() {
        let mut p0: f64 = 0.5;

        Duration::seconds_f64(p0);

        p0 = -0.5;
        Duration::seconds_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_132 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_rug() {
        let mut p0: f32 = 0.5;

        Duration::seconds_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_133 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;

        Duration::milliseconds(p0);
        
        // Additional test cases
        p0 = -1;
        Duration::milliseconds(p0);

        p0 = 0;
        Duration::milliseconds(p0);

        p0 = 123456789;
        Duration::milliseconds(p0);

        p0 = -987654321;
        Duration::milliseconds(p0);
    }
}#[cfg(test)]
mod tests_rug_134 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_microseconds() {
        let p0: i64 = 1;

        assert_eq!(Duration::microseconds(p0), 1_000.nanoseconds());
        
        let p1: i64 = -1;
        
        assert_eq!(Duration::microseconds(p1), (-1_000).nanoseconds());
    }
}#[cfg(test)]
mod tests_rug_135 {
    use super::*;
    use crate::{Duration};

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;

        <Duration>::nanoseconds(p0);

        p0 = -1;
        <Duration>::nanoseconds(p0);
    }
}#[cfg(test)]
mod tests_rug_136 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: i128 = 1_234_567_890;

        <Duration>::nanoseconds_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_137 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: Duration = 1.weeks();
        assert_eq!(p0.whole_weeks(), 1);

        let p1: Duration = (-1).weeks();
        assert_eq!(p1.whole_weeks(), -1);

        let p2: Duration = 6.days();
        assert_eq!(p2.whole_weeks(), 0);

        let p3: Duration = (-6).days();
        assert_eq!(p3.whole_weeks(), 0);
    }
}#[cfg(test)]
mod tests_rug_138 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_whole_days() {
        let p0: Duration = 1.days();
        assert_eq!(p0.whole_days(), 1);

        let p1: Duration = (-1).days();
        assert_eq!(p1.whole_days(), -1);

        let p2: Duration = 23.hours();
        assert_eq!(p2.whole_days(), 0);

        let p3: Duration = (-23).hours();
        assert_eq!(p3.whole_days(), 0);
    }
}#[cfg(test)]
mod tests_rug_139 {
    use super::*;
    use crate::ext::NumericalDuration;

    #[test]
    fn test_whole_hours() {
        let p0: Duration = 1.hours();
        assert_eq!(p0.whole_hours(), 1);

        let p1: Duration = (-1).hours();
        assert_eq!(p1.whole_hours(), -1);

        let p2: Duration = 59.minutes();
        assert_eq!(p2.whole_hours(), 0);

        let p3: Duration = (-59).minutes();
        assert_eq!(p3.whole_hours(), 0);
    }
}#[cfg(test)]
mod tests_rug_140 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_whole_minutes() {
        let p0: Duration = 1.minutes();
        assert_eq!(p0.whole_minutes(), 1);

        let p1: Duration = (-1).minutes();
        assert_eq!(p1.whole_minutes(), -1);

        let p2: Duration = 59.seconds();
        assert_eq!(p2.whole_minutes(), 0);

        let p3: Duration = (-59).seconds();
        assert_eq!(p3.whole_minutes(), 0);
    }
}#[cfg(test)]
mod tests_rug_141 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_whole_seconds() {
        let p0: Duration = 1.seconds();
        assert_eq!(p0.whole_seconds(), 1);

        let p1: Duration = (-1).seconds();
        assert_eq!(p1.whole_seconds(), -1);

        let p2: Duration = 1.minutes();
        assert_eq!(p2.whole_seconds(), 60);

        let p3: Duration = (-1).minutes();
        assert_eq!(p3.whole_seconds(), -60);
    }
}#[cfg(test)]
mod tests_rug_142 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_as_seconds_f64() {
        let p0: Duration = 1.5.seconds(); // create the local variable with type Duration

        assert_eq!(p0.as_seconds_f64(), 1.5);
    }

    #[test]
    fn test_as_seconds_f64_negative() {
        let p0: Duration = (-1.5).seconds(); // create the local variable with type Duration

        assert_eq!(p0.as_seconds_f64(), -1.5);
    }
}#[cfg(test)]
mod tests_rug_143 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = 1.5.seconds();

        assert_eq!(p0.as_seconds_f32(), 1.5);

        let mut p1: Duration = (-1.5).seconds();
        
        assert_eq!(p1.as_seconds_f32(), -1.5);
    }
}#[cfg(test)]
mod tests_rug_144 {
    use super::*;
    use crate::ext::NumericalDuration; // Added from the example to ensure NumericalDuration is available

    #[test]
    fn test_whole_milliseconds() {
        let p0: Duration = 1.seconds(); // using sample code to construct the variable
        assert_eq!(p0.whole_milliseconds(), 1_000);

        let p1: Duration = (-1).seconds();
        assert_eq!(p1.whole_milliseconds(), -1_000);

        let p2: Duration = 1.milliseconds();
        assert_eq!(p2.whole_milliseconds(), 1);

        let p3: Duration = (-1).milliseconds();
        assert_eq!(p3.whole_milliseconds(), -1);
    }
}#[cfg(test)]
mod tests_rug_145 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_subsec_milliseconds() {
        let p0: Duration = 1.4.seconds();

        assert_eq!(p0.subsec_milliseconds(), 400);
    }

    #[test]
    fn test_subsec_milliseconds_negative() {
        let p1: Duration = (-1.4).seconds();

        assert_eq!(p1.subsec_milliseconds(), -400);
    }
}#[cfg(test)]
mod tests_rug_146 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_whole_microseconds() {
        let p0: Duration = 1.milliseconds();
        assert_eq!(p0.whole_microseconds(), 1_000);

        let p1: Duration = (-1).milliseconds();
        assert_eq!(p1.whole_microseconds(), -1_000);

        let p2: Duration = 1.microseconds();
        assert_eq!(p2.whole_microseconds(), 1);

        let p3: Duration = (-1).microseconds();
        assert_eq!(p3.whole_microseconds(), -1);

        let p4: Duration = Duration::seconds(5);
        assert_eq!(p4.whole_microseconds(), 5_000_000);
    }
}#[cfg(test)]
mod tests_rug_147 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: Duration = 1.0004.seconds();

        assert_eq!(p0.subsec_microseconds(), 400);
    }

    #[test]
    fn test_negative_subsec_microseconds() {
        let p1: Duration = (-1.0004).seconds();

        assert_eq!(p1.subsec_microseconds(), -400);
    }
}#[cfg(test)]
mod tests_rug_148 {
    use super::*;
    use crate::ext::NumericalDuration;
    use crate::Duration;

    #[test]
    fn test_whole_nanoseconds() {
        let p0: Duration = 1.microseconds(); // create the local variable with type Duration

        assert_eq!(p0.whole_nanoseconds(), 1_000);

        let p1: Duration = (-1).microseconds(); // create the local variable with type Duration

        assert_eq!(p1.whole_nanoseconds(), -1_000);

        let p2: Duration = 1.nanoseconds(); // create the local variable with type Duration

        assert_eq!(p2.whole_nanoseconds(), 1);

        let p3: Duration = (-1).nanoseconds(); // create the local variable with type Duration

        assert_eq!(p3.whole_nanoseconds(), -1);

        let p4: Duration = Duration::seconds(5); // create the local variable with type Duration

        assert_eq!(p4.whole_nanoseconds(), 5_000_000_000);
    }
}#[cfg(test)]
mod tests_rug_149 {
    use super::*;
    use crate::ext::NumericalDuration; // Assuming this is needed for the `.seconds()` method

    #[test]
    fn test_subsec_nanoseconds() {
        let p0: Duration = 1.000_000_400.seconds();
        let p1: Duration = (-1.000_000_400).seconds();

        assert_eq!(p0.subsec_nanoseconds(), 400);
        assert_eq!(p1.subsec_nanoseconds(), -400);
    }
}#[cfg(test)]
mod tests_rug_150 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_rug() {
        let p0: Duration = 5.seconds();
        let p1: Duration = 5.seconds();

        assert_eq!(p0.checked_add(p1), Some(10.seconds()));

        let p2: Duration = Duration::MAX;
        let p3: Duration = 1.nanoseconds();

        assert_eq!(p2.checked_add(p3), None);

        let p4: Duration = (-5).seconds();
        let p5: Duration = 5.seconds();

        assert_eq!(p4.checked_add(p5), Some(0.seconds()));
    }
}#[cfg(test)]
mod tests_rug_151 {
    use super::*;
    use crate::duration::Duration;
    use crate::ext::NumericalDuration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5); // create the local variable with type Duration using sample code
        let mut p1: Duration = Duration::seconds(5); // create the local variable with type Duration using sample code

        assert_eq!(Duration::checked_sub(p0, p1), Some(Duration::ZERO));
    }

    #[test]
    fn test_rug_min() {
        let mut p0: Duration = Duration::MIN; // create the local variable with type Duration
        let mut p1: Duration = Duration::nanoseconds(1); // create the local variable with type Duration

        assert_eq!(Duration::checked_sub(p0, p1), None);
    }

    #[test]
    fn test_rug_negative() {
        let mut p0: Duration = Duration::seconds(5); // create the local variable with type Duration
        let mut p1: Duration = Duration::seconds(10); // create the local variable with type Duration

        assert_eq!(Duration::checked_sub(p0, p1), Some((-5).seconds()));
    }
}#[cfg(test)]
mod tests_rug_152 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_rug() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = 2;

        assert_eq!(p0.checked_mul(p1), Some(Duration::seconds(10)));
    }

    #[test]
    fn test_rug_negative() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = -2;

        assert_eq!(p0.checked_mul(p1), Some(Duration::seconds(-10)));
    }

    #[test]
    fn test_rug_zero() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = 0;

        assert_eq!(p0.checked_mul(p1), Some(Duration::seconds(0)));
    }

    #[test]
    fn test_rug_max_overflow() {
        let p0: Duration = Duration::MAX;
        let p1: i32 = 2;

        assert_eq!(p0.checked_mul(p1), None);
    }

    #[test]
    fn test_rug_min_overflow() {
        let p0: Duration = Duration::MIN;
        let p1: i32 = 2;

        assert_eq!(p0.checked_mul(p1), None);
    }
}#[cfg(test)]
mod tests_rug_153 {
    use super::*;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: Duration = Duration::seconds(10); // create the local variable with type Duration using sample code
        let p1: i32 = 2; // initialize the second argument with a sample value

        assert_eq!(p0.checked_div(p1), Some(Duration::seconds(5)));
    }

    #[test]
    fn test_rug_negative() {
        let p0: Duration = Duration::seconds(10); // create the local variable with type Duration using sample code
        let p1: i32 = -2; // initialize the second argument with a sample value

        assert_eq!(p0.checked_div(p1), Some(Duration::seconds(-5)));
    }

    #[test]
    fn test_rug_zero() {
        let p0: Duration = Duration::seconds(1); // create the local variable with type Duration using sample code
        let p1: i32 = 0; // initialize the second argument with a sample value

        assert_eq!(p0.checked_div(p1), None);
    }
}#[cfg(test)]
mod tests_rug_154 {
    use super::*;
    use crate::{Duration, ext::NumericalDuration};

    #[test]
    fn test_saturating_add() {
        let p0: Duration = 5.seconds();
        let p1: Duration = 5.seconds();

        assert_eq!(p0.saturating_add(p1), 10.seconds());

        let max_duration: Duration = Duration::MAX;
        let one_nanosecond: Duration = 1.nanoseconds();

        assert_eq!(max_duration.saturating_add(one_nanosecond), Duration::MAX);

        let min_duration: Duration = Duration::MIN;
        let negative_one_nanosecond: Duration = (-1).nanoseconds();

        assert_eq!(min_duration.saturating_add(negative_one_nanosecond), Duration::MIN);

        let negative_five_seconds: Duration = (-5).seconds();
        let five_seconds: Duration = 5.seconds();

        assert_eq!(negative_five_seconds.saturating_add(five_seconds), Duration::ZERO);
    }
}#[cfg(test)]
mod tests_rug_155 {
    use super::*;
    use crate::duration::Duration;
    use crate::ext::NumericalDuration;

    #[test]
    fn test_rug() {
        let p0: Duration = Duration::seconds(5);
        let p1: Duration = Duration::seconds(5);

        assert_eq!(p0.saturating_sub(p1), Duration::ZERO);

        let p2: Duration = Duration::MIN;
        let p3: Duration = Duration::nanoseconds(1);

        assert_eq!(p2.saturating_sub(p3), Duration::MIN);

        let p4: Duration = Duration::MAX;
        let p5: Duration = Duration::nanoseconds(-1);

        assert_eq!(p4.saturating_sub(p5), Duration::MAX);

        let p6: Duration = Duration::seconds(5);
        let p7: Duration = Duration::seconds(10);

        assert_eq!(p6.saturating_sub(p7), Duration::seconds(-5));
    }
}#[cfg(test)]
mod tests_rug_156 {
    use super::*;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = 2;

        <Duration>::saturating_mul(p0, p1);
    }

    #[test]
    fn test_saturating_mul_positive() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = 2;

        assert_eq!(p0.saturating_mul(p1), Duration::seconds(10));
    }

    #[test]
    fn test_saturating_mul_negative() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = -2;

        assert_eq!(p0.saturating_mul(p1), Duration::seconds(-10));
    }

    #[test]
    fn test_saturating_mul_zero() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = 0;

        assert_eq!(p0.saturating_mul(p1), Duration::ZERO);
    }

    #[test]
    fn test_saturating_mul_max_positive() {
        let p0: Duration = Duration::MAX;
        let p1: i32 = 2;

        assert_eq!(p0.saturating_mul(p1), Duration::MAX);
    }

    #[test]
    fn test_saturating_mul_min_positive() {
        let p0: Duration = Duration::MIN;
        let p1: i32 = 2;

        assert_eq!(p0.saturating_mul(p1), Duration::MIN);
    }

    #[test]
    fn test_saturating_mul_max_negative() {
        let p0: Duration = Duration::MAX;
        let p1: i32 = -2;

        assert_eq!(p0.saturating_mul(p1), Duration::MIN);
    }

    #[test]
    fn test_saturating_mul_min_negative() {
        let p0: Duration = Duration::MIN;
        let p1: i32 = -2;

        assert_eq!(p0.saturating_mul(p1), Duration::MAX);
    }
}#[cfg(test)]
mod tests_rug_157 {
    use super::*;
    use std::time::Instant;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut data = 42;
        let p0 = || { data += 1; data };

        let (elapsed, result) = Duration::time_fn(p0);

        assert!(elapsed > Duration::ZERO);
        assert_eq!(result, 43);
    }
}#[cfg(test)]
mod tests_rug_162 {
    use super::*;
    use std::ops::Add;
    use std::time::Duration as StdDuration;

    #[test]
    fn test_rug() {
        let mut p0: StdDuration = StdDuration::new(3600, 123_456_789); // create the local variable v6 with type std::time::Duration
        let mut p1: Duration = Duration::seconds(5); // create the local variable v4 with type Duration

        p0.add(p1);
    }
}#[cfg(test)]
mod tests_rug_164 {
    use super::*;
    use std::ops::Sub;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: Duration = Duration::seconds(3);

        <Duration as Sub>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_168 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: i8 = 3;

        <Duration as Mul<i8>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_169 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 3; // example value for i8
        let mut p1 = Duration::seconds(5); // create the local variable v4 with type Duration

        p0.mul(p1);
    }
}#[cfg(test)]
mod tests_rug_171 {
    use super::*;
    use std::ops::Mul;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: i16 = 3;

        <Duration as Mul<i16>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_172 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 3; // sample data for i16
        let mut p1: Duration = Duration::seconds(5); // using the provided sample code to construct Duration

        p0.mul(p1);
    }
}#[cfg(test)]
mod tests_rug_175 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 3; // sample data for i32 type
        let mut p1: Duration = Duration::seconds(5); // using the provided sample code

        <i32 as Mul<Duration>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_176 {
    use super::*;
    use std::ops::Div;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: Duration = Duration::seconds(5);
        let p1: i32 = 2;

        p0.div(p1);
    }
}#[cfg(test)]
mod tests_rug_177 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_mul() {
        let mut p0: Duration = Duration::seconds(5); // create the local variable v4 with type Duration
        let mut p1: u8 = 3; // sample data for u8

        <Duration as Mul<u8>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_178 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 3; // sample data for u8 type
        let mut p1: Duration = Duration::seconds(5); // using the provided sample code

        p0.mul(p1);
    }
}#[cfg(test)]
mod tests_rug_180 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: u16 = 3;

        <Duration as Mul<u16>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_182 {
    use super::*;
    use std::ops::Div;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: u16 = 2;

        <Duration as Div<u16>>::div(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_184 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: u32 = 10; // sample data for u32 type
        let p1: Duration = Duration::seconds(5); // using the provided sample code to construct Duration

        <u32 as Mul<Duration>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_186 {
    use super::*;
    use crate::Duration;
    use std::ops::Mul;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5); // create the local variable v4 with type Duration
        let mut p1: f32 = 2.5; // sample data for f32

        p0.mul(p1);
    }
}#[cfg(test)]
mod tests_rug_187 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let p0: f32 = 2.5;
        let p1 = Duration::seconds(5);

        <f32>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_188 {
    use super::*;
    use std::ops::Mul;
    use crate::duration::Duration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: f64 = 2.0;

        <Duration as Mul<f64>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_189 {
    use super::*;
    use std::ops::Mul;
    use crate::Duration;

    #[test]
    fn test_mul() {
        let p0: f64 = 3.5; // example sample data for f64 type
        let p1 = Duration::seconds(5); // using the provided sample code to construct Duration

        <f64 as Mul<Duration>>::mul(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_190 {
    use super::*;
    use std::ops::Div;
    use crate::Duration;

    #[test]
    fn test_div() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: f32 = 2.0;

        p0.div(p1);
    }
}#[cfg(test)]
mod tests_rug_191 {
    use super::*;
    use std::ops::Div;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0: Duration = Duration::seconds(5);
        let mut p1: f64 = 2.0;

        <Duration as Div<f64>>::div(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_192 {
    use super::*;
    use std::ops::Div;
    use crate::Duration;

    #[test]
    fn test_rug() {
        let mut p0 = Duration::seconds(5);
        let mut p1 = Duration::seconds(2);

        <Duration as Div>::div(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_194 {
    use super::*;
    use std::time::Duration as StdDuration;
    use crate::duration::Duration;

    #[test]
    fn test_div() {
        let mut p0: StdDuration = StdDuration::new(3600, 123_456_789); // create the local variable v6 with type std::time::Duration
        let mut p1: Duration = Duration::seconds(5); // create the local variable v4 with type Duration

        p0.div(p1);
    }
}