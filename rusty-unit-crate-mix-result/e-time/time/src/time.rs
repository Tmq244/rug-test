//! The [`Time`] struct and its associated `impl`s.

use core::fmt;
use core::ops::{Add, Sub};
use core::time::Duration as StdDuration;
#[cfg(feature = "formatting")]
use std::io;

#[cfg(feature = "formatting")]
use crate::formatting::Formattable;
#[cfg(feature = "parsing")]
use crate::parsing::Parsable;
use crate::util::DateAdjustment;
use crate::{error, Duration};

/// By explicitly inserting this enum where padding is expected, the compiler is able to better
/// perform niche value optimization.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Padding {
    #[allow(clippy::missing_docs_in_private_items)]
    Optimize,
}

/// The clock time within a given date. Nanosecond precision.
///
/// All minutes are assumed to have exactly 60 seconds; no attempt is made to handle leap seconds
/// (either positive or negative).
///
/// When comparing two `Time`s, they are assumed to be in the same calendar date.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Time {
    #[allow(clippy::missing_docs_in_private_items)]
    hour: u8,
    #[allow(clippy::missing_docs_in_private_items)]
    minute: u8,
    #[allow(clippy::missing_docs_in_private_items)]
    second: u8,
    #[allow(clippy::missing_docs_in_private_items)]
    nanosecond: u32,
    #[allow(clippy::missing_docs_in_private_items)]
    padding: Padding,
}

impl fmt::Debug for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Time")
            .field("hour", &self.hour)
            .field("minute", &self.minute)
            .field("second", &self.second)
            .field("nanosecond", &self.nanosecond)
            .finish()
    }
}

impl Time {
    /// Create a `Time` that is exactly midnight.
    ///
    /// ```rust
    /// # use time::{Time, macros::time};
    /// assert_eq!(Time::MIDNIGHT, time!(0:00));
    /// ```
    pub const MIDNIGHT: Self = Self::__from_hms_nanos_unchecked(0, 0, 0, 0);

    /// The smallest value that can be represented by `Time`.
    ///
    /// `00:00:00.0`
    pub(crate) const MIN: Self = Self::__from_hms_nanos_unchecked(0, 0, 0, 0);

    /// The largest value that can be represented by `Time`.
    ///
    /// `23:59:59.999_999_999`
    pub(crate) const MAX: Self = Self::__from_hms_nanos_unchecked(23, 59, 59, 999_999_999);

    // region: constructors
    /// Create a `Time` from its components.
    #[doc(hidden)]
    pub const fn __from_hms_nanos_unchecked(
        hour: u8,
        minute: u8,
        second: u8,
        nanosecond: u32,
    ) -> Self {
        Self {
            hour,
            minute,
            second,
            nanosecond,
            padding: Padding::Optimize,
        }
    }

    /// Attempt to create a `Time` from the hour, minute, and second.
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms(1, 2, 3).is_ok());
    /// ```
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms(24, 0, 0).is_err()); // 24 isn't a valid hour.
    /// assert!(Time::from_hms(0, 60, 0).is_err()); // 60 isn't a valid minute.
    /// assert!(Time::from_hms(0, 0, 60).is_err()); // 60 isn't a valid second.
    /// ```
    pub const fn from_hms(hour: u8, minute: u8, second: u8) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(hour in 0 => 23);
        ensure_value_in_range!(minute in 0 => 59);
        ensure_value_in_range!(second in 0 => 59);
        Ok(Self::__from_hms_nanos_unchecked(hour, minute, second, 0))
    }

    /// Attempt to create a `Time` from the hour, minute, second, and millisecond.
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms_milli(1, 2, 3, 4).is_ok());
    /// ```
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms_milli(24, 0, 0, 0).is_err()); // 24 isn't a valid hour.
    /// assert!(Time::from_hms_milli(0, 60, 0, 0).is_err()); // 60 isn't a valid minute.
    /// assert!(Time::from_hms_milli(0, 0, 60, 0).is_err()); // 60 isn't a valid second.
    /// assert!(Time::from_hms_milli(0, 0, 0, 1_000).is_err()); // 1_000 isn't a valid millisecond.
    /// ```
    pub const fn from_hms_milli(
        hour: u8,
        minute: u8,
        second: u8,
        millisecond: u16,
    ) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(hour in 0 => 23);
        ensure_value_in_range!(minute in 0 => 59);
        ensure_value_in_range!(second in 0 => 59);
        ensure_value_in_range!(millisecond in 0 => 999);
        Ok(Self::__from_hms_nanos_unchecked(
            hour,
            minute,
            second,
            millisecond as u32 * 1_000_000,
        ))
    }

    /// Attempt to create a `Time` from the hour, minute, second, and microsecond.
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms_micro(1, 2, 3, 4).is_ok());
    /// ```
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms_micro(24, 0, 0, 0).is_err()); // 24 isn't a valid hour.
    /// assert!(Time::from_hms_micro(0, 60, 0, 0).is_err()); // 60 isn't a valid minute.
    /// assert!(Time::from_hms_micro(0, 0, 60, 0).is_err()); // 60 isn't a valid second.
    /// assert!(Time::from_hms_micro(0, 0, 0, 1_000_000).is_err()); // 1_000_000 isn't a valid microsecond.
    /// ```
    pub const fn from_hms_micro(
        hour: u8,
        minute: u8,
        second: u8,
        microsecond: u32,
    ) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(hour in 0 => 23);
        ensure_value_in_range!(minute in 0 => 59);
        ensure_value_in_range!(second in 0 => 59);
        ensure_value_in_range!(microsecond in 0 => 999_999);
        Ok(Self::__from_hms_nanos_unchecked(
            hour,
            minute,
            second,
            microsecond * 1_000,
        ))
    }

    /// Attempt to create a `Time` from the hour, minute, second, and nanosecond.
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms_nano(1, 2, 3, 4).is_ok());
    /// ```
    ///
    /// ```rust
    /// # use time::Time;
    /// assert!(Time::from_hms_nano(24, 0, 0, 0).is_err()); // 24 isn't a valid hour.
    /// assert!(Time::from_hms_nano(0, 60, 0, 0).is_err()); // 60 isn't a valid minute.
    /// assert!(Time::from_hms_nano(0, 0, 60, 0).is_err()); // 60 isn't a valid second.
    /// assert!(Time::from_hms_nano(0, 0, 0, 1_000_000_000).is_err()); // 1_000_000_000 isn't a valid nanosecond.
    /// ```
    pub const fn from_hms_nano(
        hour: u8,
        minute: u8,
        second: u8,
        nanosecond: u32,
    ) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(hour in 0 => 23);
        ensure_value_in_range!(minute in 0 => 59);
        ensure_value_in_range!(second in 0 => 59);
        ensure_value_in_range!(nanosecond in 0 => 999_999_999);
        Ok(Self::__from_hms_nanos_unchecked(
            hour, minute, second, nanosecond,
        ))
    }
    // endregion constructors

    // region: getters
    /// Get the clock hour, minute, and second.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00:00).as_hms(), (0, 0, 0));
    /// assert_eq!(time!(23:59:59).as_hms(), (23, 59, 59));
    /// ```
    pub const fn as_hms(self) -> (u8, u8, u8) {
        (self.hour, self.minute, self.second)
    }

    /// Get the clock hour, minute, second, and millisecond.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00:00).as_hms_milli(), (0, 0, 0, 0));
    /// assert_eq!(time!(23:59:59.999).as_hms_milli(), (23, 59, 59, 999));
    /// ```
    pub const fn as_hms_milli(self) -> (u8, u8, u8, u16) {
        (
            self.hour,
            self.minute,
            self.second,
            (self.nanosecond / 1_000_000) as u16,
        )
    }

    /// Get the clock hour, minute, second, and microsecond.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00:00).as_hms_micro(), (0, 0, 0, 0));
    /// assert_eq!(
    ///     time!(23:59:59.999_999).as_hms_micro(),
    ///     (23, 59, 59, 999_999)
    /// );
    /// ```
    pub const fn as_hms_micro(self) -> (u8, u8, u8, u32) {
        (self.hour, self.minute, self.second, self.nanosecond / 1_000)
    }

    /// Get the clock hour, minute, second, and nanosecond.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00:00).as_hms_nano(), (0, 0, 0, 0));
    /// assert_eq!(
    ///     time!(23:59:59.999_999_999).as_hms_nano(),
    ///     (23, 59, 59, 999_999_999)
    /// );
    /// ```
    pub const fn as_hms_nano(self) -> (u8, u8, u8, u32) {
        (self.hour, self.minute, self.second, self.nanosecond)
    }

    /// Get the clock hour.
    ///
    /// The returned value will always be in the range `0..24`.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00:00).hour(), 0);
    /// assert_eq!(time!(23:59:59).hour(), 23);
    /// ```
    pub const fn hour(self) -> u8 {
        self.hour
    }

    /// Get the minute within the hour.
    ///
    /// The returned value will always be in the range `0..60`.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00:00).minute(), 0);
    /// assert_eq!(time!(23:59:59).minute(), 59);
    /// ```
    pub const fn minute(self) -> u8 {
        self.minute
    }

    /// Get the second within the minute.
    ///
    /// The returned value will always be in the range `0..60`.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00:00).second(), 0);
    /// assert_eq!(time!(23:59:59).second(), 59);
    /// ```
    pub const fn second(self) -> u8 {
        self.second
    }

    /// Get the milliseconds within the second.
    ///
    /// The returned value will always be in the range `0..1_000`.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00).millisecond(), 0);
    /// assert_eq!(time!(23:59:59.999).millisecond(), 999);
    /// ```
    pub const fn millisecond(self) -> u16 {
        (self.nanosecond / 1_000_000) as _
    }

    /// Get the microseconds within the second.
    ///
    /// The returned value will always be in the range `0..1_000_000`.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00).microsecond(), 0);
    /// assert_eq!(time!(23:59:59.999_999).microsecond(), 999_999);
    /// ```
    pub const fn microsecond(self) -> u32 {
        self.nanosecond / 1_000
    }

    /// Get the nanoseconds within the second.
    ///
    /// The returned value will always be in the range `0..1_000_000_000`.
    ///
    /// ```rust
    /// # use time::macros::time;
    /// assert_eq!(time!(0:00).nanosecond(), 0);
    /// assert_eq!(time!(23:59:59.999_999_999).nanosecond(), 999_999_999);
    /// ```
    pub const fn nanosecond(self) -> u32 {
        self.nanosecond
    }
    // endregion getters

    // region: arithmetic helpers
    /// Add the sub-day time of the [`Duration`] to the `Time`. Wraps on overflow, returning whether
    /// the date is different.
    pub(crate) const fn adjusting_add(self, duration: Duration) -> (DateAdjustment, Self) {
        let mut nanoseconds = self.nanosecond as i32 + duration.subsec_nanoseconds();
        let mut seconds = self.second as i8 + (duration.whole_seconds() % 60) as i8;
        let mut minutes = self.minute as i8 + (duration.whole_minutes() % 60) as i8;
        let mut hours = self.hour as i8 + (duration.whole_hours() % 24) as i8;
        let mut date_adjustment = DateAdjustment::None;

        cascade!(nanoseconds in 0..1_000_000_000 => seconds);
        cascade!(seconds in 0..60 => minutes);
        cascade!(minutes in 0..60 => hours);
        if hours >= 24 {
            hours -= 24;
            date_adjustment = DateAdjustment::Next;
        } else if hours < 0 {
            hours += 24;
            date_adjustment = DateAdjustment::Previous;
        }

        (
            date_adjustment,
            Self::__from_hms_nanos_unchecked(
                hours as _,
                minutes as _,
                seconds as _,
                nanoseconds as _,
            ),
        )
    }

    /// Subtract the sub-day time of the [`Duration`] to the `Time`. Wraps on overflow, returning
    /// whether the date is different.
    pub(crate) const fn adjusting_sub(self, duration: Duration) -> (DateAdjustment, Self) {
        let mut nanoseconds = self.nanosecond as i32 - duration.subsec_nanoseconds();
        let mut seconds = self.second as i8 - (duration.whole_seconds() % 60) as i8;
        let mut minutes = self.minute as i8 - (duration.whole_minutes() % 60) as i8;
        let mut hours = self.hour as i8 - (duration.whole_hours() % 24) as i8;
        let mut date_adjustment = DateAdjustment::None;

        cascade!(nanoseconds in 0..1_000_000_000 => seconds);
        cascade!(seconds in 0..60 => minutes);
        cascade!(minutes in 0..60 => hours);
        if hours >= 24 {
            hours -= 24;
            date_adjustment = DateAdjustment::Next;
        } else if hours < 0 {
            hours += 24;
            date_adjustment = DateAdjustment::Previous;
        }

        (
            date_adjustment,
            Self::__from_hms_nanos_unchecked(
                hours as _,
                minutes as _,
                seconds as _,
                nanoseconds as _,
            ),
        )
    }

    /// Add the sub-day time of the [`std::time::Duration`] to the `Time`. Wraps on overflow,
    /// returning whether the date is the previous date as the first element of the tuple.
    pub(crate) const fn adjusting_add_std(self, duration: StdDuration) -> (bool, Self) {
        let mut nanosecond = self.nanosecond + duration.subsec_nanos();
        let mut second = self.second + (duration.as_secs() % 60) as u8;
        let mut minute = self.minute + ((duration.as_secs() / 60) % 60) as u8;
        let mut hour = self.hour + ((duration.as_secs() / 3_600) % 24) as u8;
        let mut is_next_day = false;

        cascade!(nanosecond in 0..1_000_000_000 => second);
        cascade!(second in 0..60 => minute);
        cascade!(minute in 0..60 => hour);
        if hour >= 24 {
            hour -= 24;
            is_next_day = true;
        }

        (
            is_next_day,
            Self::__from_hms_nanos_unchecked(hour, minute, second, nanosecond),
        )
    }

    /// Subtract the sub-day time of the [`std::time::Duration`] to the `Time`. Wraps on overflow,
    /// returning whether the date is the previous date as the first element of the tuple.
    pub(crate) const fn adjusting_sub_std(self, duration: StdDuration) -> (bool, Self) {
        let mut nanosecond = self.nanosecond as i32 - duration.subsec_nanos() as i32;
        let mut second = self.second as i8 - (duration.as_secs() % 60) as i8;
        let mut minute = self.minute as i8 - ((duration.as_secs() / 60) % 60) as i8;
        let mut hour = self.hour as i8 - ((duration.as_secs() / 3_600) % 24) as i8;
        let mut is_previous_day = false;

        cascade!(nanosecond in 0..1_000_000_000 => second);
        cascade!(second in 0..60 => minute);
        cascade!(minute in 0..60 => hour);
        if hour < 0 {
            hour += 24;
            is_previous_day = true;
        }

        (
            is_previous_day,
            Self::__from_hms_nanos_unchecked(hour as _, minute as _, second as _, nanosecond as _),
        )
    }
    // endregion arithmetic helpers
}

// region: formatting & parsing
#[cfg(feature = "formatting")]
impl Time {
    /// Format the `Time` using the provided [format description](crate::format_description).
    pub fn format_into(
        self,
        output: &mut impl io::Write,
        format: &(impl Formattable + ?Sized),
    ) -> Result<usize, crate::error::Format> {
        format.format_into(output, None, Some(self), None)
    }

    /// Format the `Time` using the provided [format description](crate::format_description).
    ///
    /// ```rust
    /// # use time::{format_description, macros::time};
    /// let format = format_description::parse("[hour]:[minute]:[second]")?;
    /// assert_eq!(time!(12:00).format(&format)?, "12:00:00");
    /// # Ok::<_, time::Error>(())
    /// ```
    pub fn format(
        self,
        format: &(impl Formattable + ?Sized),
    ) -> Result<String, crate::error::Format> {
        format.format(None, Some(self), None)
    }
}

#[cfg(feature = "parsing")]
impl Time {
    /// Parse a `Time` from the input using the provided [format
    /// description](crate::format_description).
    ///
    /// ```rust
    /// # use time::{format_description, macros::time, Time};
    /// let format = format_description::parse("[hour]:[minute]:[second]")?;
    /// assert_eq!(Time::parse("12:00:00", &format)?, time!(12:00));
    /// # Ok::<_, time::Error>(())
    /// ```
    pub fn parse(
        input: &str,
        description: &(impl Parsable + ?Sized),
    ) -> Result<Self, error::Parse> {
        description.parse_time(input.as_bytes())
    }
}

impl fmt::Display for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (value, width) = match self.nanosecond() {
            nanos if nanos % 10 != 0 => (nanos, 9),
            nanos if (nanos / 10) % 10 != 0 => (nanos / 10, 8),
            nanos if (nanos / 100) % 10 != 0 => (nanos / 100, 7),
            nanos if (nanos / 1_000) % 10 != 0 => (nanos / 1_000, 6),
            nanos if (nanos / 10_000) % 10 != 0 => (nanos / 10_000, 5),
            nanos if (nanos / 100_000) % 10 != 0 => (nanos / 100_000, 4),
            nanos if (nanos / 1_000_000) % 10 != 0 => (nanos / 1_000_000, 3),
            nanos if (nanos / 10_000_000) % 10 != 0 => (nanos / 10_000_000, 2),
            nanos => (nanos / 100_000_000, 1),
        };
        write!(
            f,
            "{}:{:02}:{:02}.{:0width$}",
            self.hour,
            self.minute,
            self.second,
            value,
            width = width
        )
    }
}
// endregion formatting & parsing

// region: trait impls
impl Add<Duration> for Time {
    type Output = Self;

    /// Add the sub-day time of the [`Duration`] to the `Time`. Wraps on overflow.
    ///
    /// ```rust
    /// # use time::{ext::NumericalDuration, macros::time};
    /// assert_eq!(time!(12:00) + 2.hours(), time!(14:00));
    /// assert_eq!(time!(0:00:01) + (-2).seconds(), time!(23:59:59));
    /// ```
    fn add(self, duration: Duration) -> Self::Output {
        self.adjusting_add(duration).1
    }
}

impl Add<StdDuration> for Time {
    type Output = Self;

    /// Add the sub-day time of the [`std::time::Duration`] to the `Time`. Wraps on overflow.
    ///
    /// ```rust
    /// # use time::{ext::NumericalStdDuration, macros::time};
    /// assert_eq!(time!(12:00) + 2.std_hours(), time!(14:00));
    /// assert_eq!(time!(23:59:59) + 2.std_seconds(), time!(0:00:01));
    /// ```
    fn add(self, duration: StdDuration) -> Self::Output {
        self.adjusting_add_std(duration).1
    }
}

impl_add_assign!(Time: Duration, StdDuration);

impl Sub<Duration> for Time {
    type Output = Self;

    /// Subtract the sub-day time of the [`Duration`] from the `Time`. Wraps on overflow.
    ///
    /// ```rust
    /// # use time::{ext::NumericalDuration, macros::time};
    /// assert_eq!(time!(14:00) - 2.hours(), time!(12:00));
    /// assert_eq!(time!(23:59:59) - (-2).seconds(), time!(0:00:01));
    /// ```
    fn sub(self, duration: Duration) -> Self::Output {
        self.adjusting_sub(duration).1
    }
}

impl Sub<StdDuration> for Time {
    type Output = Self;

    /// Subtract the sub-day time of the [`std::time::Duration`] from the `Time`. Wraps on overflow.
    ///
    /// ```rust
    /// # use time::{ext::NumericalStdDuration, macros::time};
    /// assert_eq!(time!(14:00) - 2.std_hours(), time!(12:00));
    /// assert_eq!(time!(0:00:01) - 2.std_seconds(), time!(23:59:59));
    /// ```
    fn sub(self, duration: StdDuration) -> Self::Output {
        self.adjusting_sub_std(duration).1
    }
}

impl_sub_assign!(Time: Duration, StdDuration);

impl Sub for Time {
    type Output = Duration;

    /// Subtract two `Time`s, returning the [`Duration`] between. This assumes both `Time`s are in
    /// the same calendar day.
    ///
    /// ```rust
    /// # use time::{ext::NumericalDuration, macros::time};
    /// assert_eq!(time!(0:00) - time!(0:00), 0.seconds());
    /// assert_eq!(time!(1:00) - time!(0:00), 1.hours());
    /// assert_eq!(time!(0:00) - time!(1:00), (-1).hours());
    /// assert_eq!(time!(0:00) - time!(23:00), (-23).hours());
    /// ```
    fn sub(self, rhs: Self) -> Self::Output {
        let hour_diff = (self.hour as i8) - (rhs.hour as i8);
        let minute_diff = (self.minute as i8) - (rhs.minute as i8);
        let mut second_diff = (self.second as i8) - (rhs.second as i8);
        let mut nanosecond_diff = (self.nanosecond as i32) - (rhs.nanosecond as i32);

        cascade!(nanosecond_diff in 0..1_000_000_000 => second_diff);

        Duration::new_unchecked(
            hour_diff as i64 * 3_600 + minute_diff as i64 * 60 + second_diff as i64,
            nanosecond_diff,
        )
    }
}

// endregion trait impls
#[cfg(test)]
mod tests_rug_332 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 12;
        let mut p1: u8 = 34;
        let mut p2: u8 = 56;
        let mut p3: u32 = 789_012_345;

        Time::__from_hms_nanos_unchecked(p0, p1, p2, p3);
    }
}#[cfg(test)]
mod tests_rug_333 {
    use super::*;
    use crate::{Time, error::ComponentRange};

    #[test]
    fn test_rug() {
        let mut p0: u8 = 1; // Sample data from the comments
        let mut p1: u8 = 2; // Sample data from the comments
        let mut p2: u8 = 3; // Sample data from the comments

        assert!(Time::from_hms(p0, p1, p2).is_ok());

        p0 = 24;
        assert!(Time::from_hms(p0, p1, p2).is_err()); // 24 isn't a valid hour.

        p0 = 0;
        p1 = 60;
        assert!(Time::from_hms(p0, p1, p2).is_err()); // 60 isn't a valid minute.

        p1 = 0;
        p2 = 60;
        assert!(Time::from_hms(p0, p1, p2).is_err()); // 60 isn't a valid second.
    }
}#[cfg(test)]
mod tests_rug_334 {
    use super::*;
    use crate::Time;
    use crate::error::ComponentRange;

    #[test]
    fn test_valid_time() {
        let hour: u8 = 1;
        let minute: u8 = 2;
        let second: u8 = 3;
        let millisecond: u16 = 4;

        assert!(Time::from_hms_milli(hour, minute, second, millisecond).is_ok());
    }

    #[test]
    fn test_invalid_hour() {
        let hour: u8 = 24;
        let minute: u8 = 0;
        let second: u8 = 0;
        let millisecond: u16 = 0;

        assert!(Time::from_hms_milli(hour, minute, second, millisecond).is_err());
    }

    #[test]
    fn test_invalid_minute() {
        let hour: u8 = 0;
        let minute: u8 = 60;
        let second: u8 = 0;
        let millisecond: u16 = 0;

        assert!(Time::from_hms_milli(hour, minute, second, millisecond).is_err());
    }

    #[test]
    fn test_invalid_second() {
        let hour: u8 = 0;
        let minute: u8 = 0;
        let second: u8 = 60;
        let millisecond: u16 = 0;

        assert!(Time::from_hms_milli(hour, minute, second, millisecond).is_err());
    }

    #[test]
    fn test_invalid_millisecond() {
        let hour: u8 = 0;
        let minute: u8 = 0;
        let second: u8 = 0;
        let millisecond: u16 = 1_000;

        assert!(Time::from_hms_milli(hour, minute, second, millisecond).is_err());
    }
}#[cfg(test)]
mod tests_rug_335 {
    use super::*;
    use crate::Time;
    use crate::error::ComponentRange;

    #[test]
    fn test_valid_time() {
        let p0: u8 = 1;
        let p1: u8 = 2;
        let p2: u8 = 3;
        let p3: u32 = 4;

        assert!(Time::from_hms_micro(p0, p1, p2, p3).is_ok());
    }

    #[test]
    fn test_invalid_hour() {
        let p0: u8 = 24;
        let p1: u8 = 0;
        let p2: u8 = 0;
        let p3: u32 = 0;

        assert!(Time::from_hms_micro(p0, p1, p2, p3).is_err());
    }

    #[test]
    fn test_invalid_minute() {
        let p0: u8 = 0;
        let p1: u8 = 60;
        let p2: u8 = 0;
        let p3: u32 = 0;

        assert!(Time::from_hms_micro(p0, p1, p2, p3).is_err());
    }

    #[test]
    fn test_invalid_second() {
        let p0: u8 = 0;
        let p1: u8 = 0;
        let p2: u8 = 60;
        let p3: u32 = 0;

        assert!(Time::from_hms_micro(p0, p1, p2, p3).is_err());
    }

    #[test]
    fn test_invalid_microsecond() {
        let p0: u8 = 0;
        let p1: u8 = 0;
        let p2: u8 = 0;
        let p3: u32 = 1_000_000;

        assert!(Time::from_hms_micro(p0, p1, p2, p3).is_err());
    }
}#[cfg(test)]
mod tests_rug_336 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 1;
        let mut p1: u8 = 2;
        let mut p2: u8 = 3;
        let mut p3: u32 = 4;

        assert!(Time::from_hms_nano(p0, p1, p2, p3).is_ok());

        p0 = 24;
        assert!(Time::from_hms_nano(p0, p1, p2, p3).is_err());

        p0 = 0;
        p1 = 60;
        assert!(Time::from_hms_nano(p0, p1, p2, p3).is_err());

        p1 = 0;
        p2 = 60;
        assert!(Time::from_hms_nano(p0, p1, p2, p3).is_err());

        p2 = 0;
        p3 = 1_000_000_000;
        assert!(Time::from_hms_nano(p0, p1, p2, p3).is_err());
    }
}#[cfg(test)]
mod tests_rug_337 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.as_hms(), (12, 30, 45));
    }
}#[cfg(test)]
mod tests_rug_338 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.as_hms_milli(), (12, 30, 45, 678));
    }
}#[cfg(test)]
mod tests_rug_339 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_rug() {
        let p0 = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.as_hms_micro(), (12, 30, 45, 678_901));
    }
}#[cfg(test)]
mod tests_rug_340 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.as_hms_nano(), (12, 30, 45, 678_901_234));
    }
}#[cfg(test)]
mod tests_rug_341 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.hour(), 12);
    }
}#[cfg(test)]
mod tests_rug_342 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_minute() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.minute(), 30);
    }
}#[cfg(test)]
mod tests_rug_343 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_second() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.second(), 45);
    }
}#[cfg(test)]
mod tests_rug_344 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_millisecond() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.millisecond(), 678);
    }

    #[test]
    fn test_millisecond_zero() {
        let p0: Time = Time::__from_hms_nanos_unchecked(0, 0, 0, 0);

        assert_eq!(p0.millisecond(), 0);
    }

    #[test]
    fn test_millisecond_max() {
        let p0: Time = Time::__from_hms_nanos_unchecked(23, 59, 59, 999_999_999);

        assert_eq!(p0.millisecond(), 999);
    }
}#[cfg(test)]
mod tests_rug_345 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_microsecond() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.microsecond(), 678_901);
    }

    #[test]
    fn test_microsecond_zero() {
        let p0: Time = Time::__from_hms_nanos_unchecked(0, 0, 0, 0);

        assert_eq!(p0.microsecond(), 0);
    }

    #[test]
    fn test_microsecond_max() {
        let p0: Time = Time::__from_hms_nanos_unchecked(23, 59, 59, 999_999_000);

        assert_eq!(p0.microsecond(), 999_999);
    }
}#[cfg(test)]
mod tests_rug_346 {
    use super::*;
    use crate::Time;

    #[test]
    fn test_nanosecond() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        assert_eq!(p0.nanosecond(), 678_901_234);
    }

    #[test]
    fn test_nanosecond_midnight() {
        let p0: Time = Time::__from_hms_nanos_unchecked(0, 0, 0, 0);

        assert_eq!(p0.nanosecond(), 0);
    }

    #[test]
    fn test_nanosecond_end_of_day() {
        let p0: Time = Time::__from_hms_nanos_unchecked(23, 59, 59, 999_999_999);

        assert_eq!(p0.nanosecond(), 999_999_999);
    }
}#[cfg(test)]
mod tests_rug_347 {
    use super::*;
    use crate::{Time, Duration};

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let p1: Duration = Duration::seconds(5);

        <Time>::adjusting_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_348 {
    use super::*;
    use crate::{Time, Duration};

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let p1: Duration = Duration::seconds(5);

        <Time>::adjusting_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_349 {
    use super::*;
    use crate::Time;
    use std::time::Duration as StdDuration;

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let p1: StdDuration = StdDuration::new(3600, 123_456_789);

        let result = Time::adjusting_add_std(p0, p1);
        assert_eq!(result, (true, Time::__from_hms_nanos_unchecked(13, 30, 46, 802_358_023)));
    }
}#[cfg(test)]
mod tests_rug_350 {
    use super::*;
    use crate::Time;
    use std::time::Duration as StdDuration;

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let p1: StdDuration = StdDuration::new(3600, 123_456_789);

        <Time>::adjusting_sub_std(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_352 {
    use super::*;
    use crate::{Time, ext::NumericalStdDuration};
    use std::ops::Add;
    use std::time::Duration;

    #[test]
    fn test_add() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let p1: Duration = Duration::new(3600, 123_456_789);

        let result = p0.add(p1);
        // You can add assertions here to verify the result if needed
    }
}#[cfg(test)]
mod tests_rug_353 {
    use super::*;
    use crate::{Time, Duration};
    use std::ops::Sub;

    #[test]
    fn test_sub() {
        let mut p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let mut p1: Duration = Duration::seconds(5);

        <Time as Sub<Duration>>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_354 {
    use super::*;
    use crate::{Time};
    use std::ops::Sub;
    use std::time::Duration;

    #[test]
    fn test_rug() {
        let p0: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let p1: Duration = Duration::new(3600, 123_456_789);

        <Time as Sub<Duration>>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_355 {
    use super::*;
    use crate::Time;
    use std::ops::Sub;

    #[test]
    fn test_sub() {
        let p0 = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);
        let p1 = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        <Time as Sub>::sub(p0, p1);
    }
}