// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The time zone, which calculates offsets from the local time to UTC.
//!
//! There are four operations provided by the `TimeZone` trait:
//!
//! 1. Converting the local `NaiveDateTime` to `DateTime<Tz>`
//! 2. Converting the UTC `NaiveDateTime` to `DateTime<Tz>`
//! 3. Converting `DateTime<Tz>` to the local `NaiveDateTime`
//! 4. Constructing `DateTime<Tz>` objects from various offsets
//!
//! 1 is used for constructors. 2 is used for the `with_timezone` method of date and time types.
//! 3 is used for other methods, e.g. `year()` or `format()`, and provided by an associated type
//! which implements `Offset` (which then passed to `TimeZone` for actual implementations).
//! Technically speaking `TimeZone` has a total knowledge about given timescale,
//! but `Offset` is used as a cache to avoid the repeated conversion
//! and provides implementations for 1 and 3.
//! An `TimeZone` instance can be reconstructed from the corresponding `Offset` instance.

use core::fmt;

use crate::format::{parse, ParseResult, Parsed, StrftimeItems};
use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};
use crate::Weekday;
#[allow(deprecated)]
use crate::{Date, DateTime};

mod fixed;
pub use self::fixed::FixedOffset;

#[cfg(feature = "clock")]
mod local;
#[cfg(feature = "clock")]
pub use self::local::Local;

mod utc;
pub use self::utc::Utc;

/// The conversion result from the local time to the timezone-aware datetime types.
#[derive(Clone, PartialEq, Debug, Copy, Eq, Hash)]
pub enum LocalResult<T> {
    /// Given local time representation is invalid.
    /// This can occur when, for example, the positive timezone transition.
    None,
    /// Given local time representation has a single unique result.
    Single(T),
    /// Given local time representation has multiple results and thus ambiguous.
    /// This can occur when, for example, the negative timezone transition.
    Ambiguous(T /*min*/, T /*max*/),
}

impl<T> LocalResult<T> {
    /// Returns `Some` only when the conversion result is unique, or `None` otherwise.
    #[must_use]
    pub fn single(self) -> Option<T> {
        match self {
            LocalResult::Single(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some` for the earliest possible conversion result, or `None` if none.
    #[must_use]
    pub fn earliest(self) -> Option<T> {
        match self {
            LocalResult::Single(t) | LocalResult::Ambiguous(t, _) => Some(t),
            _ => None,
        }
    }

    /// Returns `Some` for the latest possible conversion result, or `None` if none.
    #[must_use]
    pub fn latest(self) -> Option<T> {
        match self {
            LocalResult::Single(t) | LocalResult::Ambiguous(_, t) => Some(t),
            _ => None,
        }
    }

    /// Maps a `LocalResult<T>` into `LocalResult<U>` with given function.
    #[must_use]
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> LocalResult<U> {
        match self {
            LocalResult::None => LocalResult::None,
            LocalResult::Single(v) => LocalResult::Single(f(v)),
            LocalResult::Ambiguous(min, max) => LocalResult::Ambiguous(f(min), f(max)),
        }
    }
}

#[allow(deprecated)]
impl<Tz: TimeZone> LocalResult<Date<Tz>> {
    /// Makes a new `DateTime` from the current date and given `NaiveTime`.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    #[must_use]
    pub fn and_time(self, time: NaiveTime) -> LocalResult<DateTime<Tz>> {
        match self {
            LocalResult::Single(d) => {
                d.and_time(time).map_or(LocalResult::None, LocalResult::Single)
            }
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    #[must_use]
    pub fn and_hms_opt(self, hour: u32, min: u32, sec: u32) -> LocalResult<DateTime<Tz>> {
        match self {
            LocalResult::Single(d) => {
                d.and_hms_opt(hour, min, sec).map_or(LocalResult::None, LocalResult::Single)
            }
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    #[must_use]
    pub fn and_hms_milli_opt(
        self,
        hour: u32,
        min: u32,
        sec: u32,
        milli: u32,
    ) -> LocalResult<DateTime<Tz>> {
        match self {
            LocalResult::Single(d) => d
                .and_hms_milli_opt(hour, min, sec, milli)
                .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    #[must_use]
    pub fn and_hms_micro_opt(
        self,
        hour: u32,
        min: u32,
        sec: u32,
        micro: u32,
    ) -> LocalResult<DateTime<Tz>> {
        match self {
            LocalResult::Single(d) => d
                .and_hms_micro_opt(hour, min, sec, micro)
                .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Propagates any error. Ambiguous result would be discarded.
    #[inline]
    #[must_use]
    pub fn and_hms_nano_opt(
        self,
        hour: u32,
        min: u32,
        sec: u32,
        nano: u32,
    ) -> LocalResult<DateTime<Tz>> {
        match self {
            LocalResult::Single(d) => d
                .and_hms_nano_opt(hour, min, sec, nano)
                .map_or(LocalResult::None, LocalResult::Single),
            _ => LocalResult::None,
        }
    }
}

impl<T: fmt::Debug> LocalResult<T> {
    /// Returns the single unique conversion result, or panics accordingly.
    #[must_use]
    #[track_caller]
    pub fn unwrap(self) -> T {
        match self {
            LocalResult::None => panic!("No such local time"),
            LocalResult::Single(t) => t,
            LocalResult::Ambiguous(t1, t2) => {
                panic!("Ambiguous local time, ranging from {:?} to {:?}", t1, t2)
            }
        }
    }
}

/// The offset from the local time to UTC.
pub trait Offset: Sized + Clone + fmt::Debug {
    /// Returns the fixed offset from UTC to the local time stored.
    fn fix(&self) -> FixedOffset;
}

/// The time zone.
///
/// The methods here are the primarily constructors for [`Date`](../struct.Date.html) and
/// [`DateTime`](../struct.DateTime.html) types.
pub trait TimeZone: Sized + Clone {
    /// An associated offset type.
    /// This type is used to store the actual offset in date and time types.
    /// The original `TimeZone` value can be recovered via `TimeZone::from_offset`.
    type Offset: Offset;

    /// Make a new `DateTime` from year, month, day, time components and current time zone.
    ///
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// Returns `LocalResult::None` on invalid input data.
    fn with_ymd_and_hms(
        &self,
        year: i32,
        month: u32,
        day: u32,
        hour: u32,
        min: u32,
        sec: u32,
    ) -> LocalResult<DateTime<Self>> {
        match NaiveDate::from_ymd_opt(year, month, day).and_then(|d| d.and_hms_opt(hour, min, sec))
        {
            Some(dt) => self.from_local_datetime(&dt),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Date` from year, month, day and the current time zone.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The time zone normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Panics on the out-of-range date, invalid month and/or day.
    #[deprecated(since = "0.4.23", note = "use `with_ymd_and_hms()` instead")]
    #[allow(deprecated)]
    fn ymd(&self, year: i32, month: u32, day: u32) -> Date<Self> {
        self.ymd_opt(year, month, day).unwrap()
    }

    /// Makes a new `Date` from year, month, day and the current time zone.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The time zone normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Returns `None` on the out-of-range date, invalid month and/or day.
    #[deprecated(since = "0.4.23", note = "use `with_ymd_and_hms()` instead")]
    #[allow(deprecated)]
    fn ymd_opt(&self, year: i32, month: u32, day: u32) -> LocalResult<Date<Self>> {
        match NaiveDate::from_ymd_opt(year, month, day) {
            Some(d) => self.from_local_date(&d),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Date` from year, day of year (DOY or "ordinal") and the current time zone.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The time zone normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Panics on the out-of-range date and/or invalid DOY.
    #[deprecated(
        since = "0.4.23",
        note = "use `from_local_datetime()` with a `NaiveDateTime` instead"
    )]
    #[allow(deprecated)]
    fn yo(&self, year: i32, ordinal: u32) -> Date<Self> {
        self.yo_opt(year, ordinal).unwrap()
    }

    /// Makes a new `Date` from year, day of year (DOY or "ordinal") and the current time zone.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    ///
    /// The time zone normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Returns `None` on the out-of-range date and/or invalid DOY.
    #[deprecated(
        since = "0.4.23",
        note = "use `from_local_datetime()` with a `NaiveDateTime` instead"
    )]
    #[allow(deprecated)]
    fn yo_opt(&self, year: i32, ordinal: u32) -> LocalResult<Date<Self>> {
        match NaiveDate::from_yo_opt(year, ordinal) {
            Some(d) => self.from_local_date(&d),
            None => LocalResult::None,
        }
    }

    /// Makes a new `Date` from ISO week date (year and week number), day of the week (DOW) and
    /// the current time zone.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    /// The resulting `Date` may have a different year from the input year.
    ///
    /// The time zone normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Panics on the out-of-range date and/or invalid week number.
    #[deprecated(
        since = "0.4.23",
        note = "use `from_local_datetime()` with a `NaiveDateTime` instead"
    )]
    #[allow(deprecated)]
    fn isoywd(&self, year: i32, week: u32, weekday: Weekday) -> Date<Self> {
        self.isoywd_opt(year, week, weekday).unwrap()
    }

    /// Makes a new `Date` from ISO week date (year and week number), day of the week (DOW) and
    /// the current time zone.
    /// This assumes the proleptic Gregorian calendar, with the year 0 being 1 BCE.
    /// The resulting `Date` may have a different year from the input year.
    ///
    /// The time zone normally does not affect the date (unless it is between UTC-24 and UTC+24),
    /// but it will propagate to the `DateTime` values constructed via this date.
    ///
    /// Returns `None` on the out-of-range date and/or invalid week number.
    #[deprecated(
        since = "0.4.23",
        note = "use `from_local_datetime()` with a `NaiveDateTime` instead"
    )]
    #[allow(deprecated)]
    fn isoywd_opt(&self, year: i32, week: u32, weekday: Weekday) -> LocalResult<Date<Self>> {
        match NaiveDate::from_isoywd_opt(year, week, weekday) {
            Some(d) => self.from_local_date(&d),
            None => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// Panics on the out-of-range number of seconds and/or invalid nanosecond,
    /// for a non-panicking version see [`timestamp_opt`](#method.timestamp_opt).
    #[deprecated(since = "0.4.23", note = "use `timestamp_opt()` instead")]
    fn timestamp(&self, secs: i64, nsecs: u32) -> DateTime<Self> {
        self.timestamp_opt(secs, nsecs).unwrap()
    }

    /// Makes a new `DateTime` from the number of non-leap seconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// Returns `LocalResult::None` on out-of-range number of seconds and/or
    /// invalid nanosecond, otherwise always returns `LocalResult::Single`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, TimeZone};
    ///
    /// assert_eq!(Utc.timestamp_opt(1431648000, 0).unwrap().to_string(), "2015-05-15 00:00:00 UTC");
    /// ```
    fn timestamp_opt(&self, secs: i64, nsecs: u32) -> LocalResult<DateTime<Self>> {
        match NaiveDateTime::from_timestamp_opt(secs, nsecs) {
            Some(dt) => LocalResult::Single(self.from_utc_datetime(&dt)),
            None => LocalResult::None,
        }
    }

    /// Makes a new `DateTime` from the number of non-leap milliseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    /// Panics on out-of-range number of milliseconds for a non-panicking
    /// version see [`timestamp_millis_opt`](#method.timestamp_millis_opt).
    #[deprecated(since = "0.4.23", note = "use `timestamp_millis_opt()` instead")]
    fn timestamp_millis(&self, millis: i64) -> DateTime<Self> {
        self.timestamp_millis_opt(millis).unwrap()
    }

    /// Makes a new `DateTime` from the number of non-leap milliseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    ///
    /// Returns `LocalResult::None` on out-of-range number of milliseconds
    /// and/or invalid nanosecond, otherwise always returns
    /// `LocalResult::Single`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, TimeZone, LocalResult};
    /// match Utc.timestamp_millis_opt(1431648000) {
    ///     LocalResult::Single(dt) => assert_eq!(dt.timestamp(), 1431648),
    ///     _ => panic!("Incorrect timestamp_millis"),
    /// };
    /// ```
    fn timestamp_millis_opt(&self, millis: i64) -> LocalResult<DateTime<Self>> {
        let (mut secs, mut millis) = (millis / 1000, millis % 1000);
        if millis < 0 {
            secs -= 1;
            millis += 1000;
        }
        self.timestamp_opt(secs, millis as u32 * 1_000_000)
    }

    /// Makes a new `DateTime` from the number of non-leap nanoseconds
    /// since January 1, 1970 0:00:00 UTC (aka "UNIX timestamp").
    ///
    /// Unlike [`timestamp_millis`](#method.timestamp_millis), this never
    /// panics.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Utc, TimeZone};
    ///
    /// assert_eq!(Utc.timestamp_nanos(1431648000000000).timestamp(), 1431648);
    /// ```
    fn timestamp_nanos(&self, nanos: i64) -> DateTime<Self> {
        let (mut secs, mut nanos) = (nanos / 1_000_000_000, nanos % 1_000_000_000);
        if nanos < 0 {
            secs -= 1;
            nanos += 1_000_000_000;
        }
        self.timestamp_opt(secs, nanos as u32).unwrap()
    }

    /// Parses a string with the specified format string and returns a
    /// `DateTime` with the current offset.
    ///
    /// See the [`crate::format::strftime`] module on the
    /// supported escape sequences.
    ///
    /// If the to-be-parsed string includes an offset, it *must* match the
    /// offset of the TimeZone, otherwise an error will be returned.
    ///
    /// See also [`DateTime::parse_from_str`] which gives a [`DateTime`] with
    /// parsed [`FixedOffset`].
    fn datetime_from_str(&self, s: &str, fmt: &str) -> ParseResult<DateTime<Self>> {
        let mut parsed = Parsed::new();
        parse(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_datetime_with_timezone(self)
    }

    /// Reconstructs the time zone from the offset.
    fn from_offset(offset: &Self::Offset) -> Self;

    /// Creates the offset(s) for given local `NaiveDate` if possible.
    fn offset_from_local_date(&self, local: &NaiveDate) -> LocalResult<Self::Offset>;

    /// Creates the offset(s) for given local `NaiveDateTime` if possible.
    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<Self::Offset>;

    /// Converts the local `NaiveDate` to the timezone-aware `Date` if possible.
    #[allow(clippy::wrong_self_convention)]
    #[deprecated(since = "0.4.23", note = "use `from_local_datetime()` instead")]
    #[allow(deprecated)]
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<Self>> {
        self.offset_from_local_date(local).map(|offset| {
            // since FixedOffset is within +/- 1 day, the date is never affected
            Date::from_utc(*local, offset)
        })
    }

    /// Converts the local `NaiveDateTime` to the timezone-aware `DateTime` if possible.
    #[allow(clippy::wrong_self_convention)]
    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Self>> {
        self.offset_from_local_datetime(local)
            .map(|offset| DateTime::from_utc(*local - offset.fix(), offset))
    }

    /// Creates the offset for given UTC `NaiveDate`. This cannot fail.
    fn offset_from_utc_date(&self, utc: &NaiveDate) -> Self::Offset;

    /// Creates the offset for given UTC `NaiveDateTime`. This cannot fail.
    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> Self::Offset;

    /// Converts the UTC `NaiveDate` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    #[allow(clippy::wrong_self_convention)]
    #[deprecated(since = "0.4.23", note = "use `from_utc_datetime()` instead")]
    #[allow(deprecated)]
    fn from_utc_date(&self, utc: &NaiveDate) -> Date<Self> {
        Date::from_utc(*utc, self.offset_from_utc_date(utc))
    }

    /// Converts the UTC `NaiveDateTime` to the local time.
    /// The UTC is continuous and thus this cannot fail (but can give the duplicate local time).
    #[allow(clippy::wrong_self_convention)]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Self> {
        DateTime::from_utc(*utc, self.offset_from_utc_datetime(utc))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_negative_millis() {
        let dt = Utc.timestamp_millis_opt(-1000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.timestamp_millis_opt(-7000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:53 UTC");
        let dt = Utc.timestamp_millis_opt(-7001).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:52.999 UTC");
        let dt = Utc.timestamp_millis_opt(-7003).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:52.997 UTC");
        let dt = Utc.timestamp_millis_opt(-999).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.001 UTC");
        let dt = Utc.timestamp_millis_opt(-1).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999 UTC");
        let dt = Utc.timestamp_millis_opt(-60000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.timestamp_millis_opt(-3600000).unwrap();
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");

        for (millis, expected) in &[
            (-7000, "1969-12-31 23:59:53 UTC"),
            (-7001, "1969-12-31 23:59:52.999 UTC"),
            (-7003, "1969-12-31 23:59:52.997 UTC"),
        ] {
            match Utc.timestamp_millis_opt(*millis) {
                LocalResult::Single(dt) => {
                    assert_eq!(dt.to_string(), *expected);
                }
                e => panic!("Got {:?} instead of an okay answer", e),
            }
        }
    }

    #[test]
    fn test_negative_nanos() {
        let dt = Utc.timestamp_nanos(-1_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59 UTC");
        let dt = Utc.timestamp_nanos(-999_999_999);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.000000001 UTC");
        let dt = Utc.timestamp_nanos(-1);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:59.999999999 UTC");
        let dt = Utc.timestamp_nanos(-60_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:59:00 UTC");
        let dt = Utc.timestamp_nanos(-3_600_000_000_000);
        assert_eq!(dt.to_string(), "1969-12-31 23:00:00 UTC");
    }

    #[test]
    fn test_nanos_never_panics() {
        Utc.timestamp_nanos(i64::max_value());
        Utc.timestamp_nanos(i64::default());
        Utc.timestamp_nanos(i64::min_value());
    }
}
#[cfg(test)]
mod tests_rug_439 {
    use super::*;
    use crate::{Local, DateTime};

    #[test]
    fn test_rug() {
        let mut p0: Local = Local;
        let mut p1: i32 = 2023;
        let mut p2: u32 = 10;
        let mut p3: u32 = 5;
        let mut p4: u32 = 14;
        let mut p5: u32 = 30;
        let mut p6: u32 = 45;

        p0.with_ymd_and_hms(p1, p2, p3, p4, p5, p6);
    }
}#[cfg(test)]
mod tests_rug_440 {
    use crate::FixedOffset;
    use crate::offset::TimeZone;

    #[test]
    fn test_rug() {
        let p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();
        let p1: i32 = 2023;
        let p2: u32 = 10;
        let p3: u32 = 5;

        p0.ymd(p1, p2, p3);
    }
}#[cfg(test)]
mod tests_rug_441 {
    use super::*;
    use crate::FixedOffset;
    use crate::offset::TimeZone;

    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap(); // create the local variable v7 with type FixedOffset
        let mut p1: i32 = 2023;
        let mut p2: u32 = 10;
        let mut p3: u32 = 15;

        let _result = p0.ymd_opt(p1, p2, p3);

    }
}#[cfg(test)]
mod tests_rug_442 {
    use crate::offset::{TimeZone, fixed::FixedOffset};

    #[test]
    fn test_rug() {
        let p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap(); // create the local variable v7 with type FixedOffset
        let p1: i32 = 2023;
        let p2: u32 = 60;

        p0.yo(p1, p2);
    }
}#[cfg(test)]
mod tests_rug_443 {
    use crate::offset::{TimeZone, fixed::FixedOffset};
    use crate::naive::NaiveDate;
    use crate::LocalResult;

    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap(); // create the local variable v7 with type FixedOffset
        let mut p1: i32 = 2023;
        let mut p2: u32 = 60;

        let result = crate::offset::TimeZone::yo_opt(&p0, p1, p2);

        match result {
            LocalResult::Single(date) => println!("Date: {}", date),
            LocalResult::Ambiguous(date1, date2) => println!("Ambiguous Dates: {}, {}", date1, date2),
            LocalResult::None => println!("No valid date"),
        }
    }
}#[cfg(test)]
mod tests_rug_446 {
    use crate::{Local, DateTime, offset::TimeZone};

    #[test]
    fn test_rug() {
        let mut p0: Local = Local;
        let mut p1: i64 = 1633072800; // Sample Unix timestamp for October 1, 2021
        let mut p2: u32 = 123456789; // Sample nanoseconds

        let _dt: DateTime<Local> = crate::offset::TimeZone::timestamp(&p0, p1, p2);
    }
}#[cfg(test)]
mod tests_rug_447 {
    use crate::{offset::TimeZone, FixedOffset};
    
    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();
        let mut p1: i64 = 1431648000;
        let mut p2: u32 = 0;

        let result = crate::offset::TimeZone::timestamp_opt(&p0, p1, p2);
        
        assert_eq!(result.unwrap().to_string(), "2015-05-15 05:00:00 +05:00");
    }
}#[cfg(test)]
mod tests_rug_449 {
    use crate::{FixedOffset, TimeZone, LocalResult};

    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap(); // create the local variable with type FixedOffset
        let mut p1: i64 = 1431648000; // sample data for milliseconds

        match p0.timestamp_millis_opt(p1) {
            LocalResult::Single(dt) => assert_eq!(dt.timestamp(), 1431648),
            _ => panic!("Incorrect timestamp_millis"),
        };
    }
}#[cfg(test)]
mod tests_rug_450 {
    use crate::{FixedOffset, offset::TimeZone};

    #[test]
    fn test_rug() {
        let v7: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();
        let nanos: i64 = 1431648000000000;

        let _dt = v7.timestamp_nanos(nanos);
    }
}#[cfg(test)]
mod tests_rug_451 {
    use crate::{Local, DateTime, offset::TimeZone};

    #[test]
    fn test_rug() {
        let mut p0: Local = Local;
        let mut p1: &str = "2023-10-15 14:30:00";
        let mut p2: &str = "%Y-%m-%d %H:%M:%S";

        let _result: DateTime<Local> = crate::offset::TimeZone::datetime_from_str(&p0, p1, p2).unwrap();
    }
}#[cfg(test)]
mod tests_rug_452 {
    use super::*;
    use crate::{Local, DateTime, NaiveDate};

    #[test]
    fn test_rug() {
        let mut p0: Local = Local::now().timezone();
        let mut p1: NaiveDate = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap();

        crate::offset::TimeZone::from_local_date(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_453 {
    use super::*;
    use crate::{Local, DateTime, naive::{NaiveDate, NaiveTime}};

    #[test]
    fn test_from_local_datetime() {
        let p0: Local = Local;
        let p1: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        crate::offset::TimeZone::from_local_datetime(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_454 {
    use crate::{FixedOffset, naive::NaiveDate};
    use crate::offset::TimeZone;

    #[test]
    fn test_rug() {
        let p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();
        let p1: NaiveDate = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap();

        TimeZone::from_utc_date(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_455 {
    use super::*;
    use crate::{FixedOffset, NaiveDate, NaiveDateTime, NaiveTime};

    #[test]
    fn test_rug() {
        let mut offset = FixedOffset::east_opt(5 * 3600).unwrap(); // create the local variable with type FixedOffset
        let mut naive_datetime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        crate::offset::TimeZone::from_utc_datetime(&offset, &naive_datetime);
    }
}#[cfg(test)]
mod tests_rug_456 {
    use crate::offset::{self, Local};
    use super::*;

    #[test]
    fn test_rug() {
        let p0: offset::LocalResult<_> = offset::LocalResult::Single(Local::now());

        assert!(p0.single().is_some());
    }
}#[cfg(test)]
mod tests_rug_457 {
    use crate::offset::{self, Local};
    
    #[test]
    fn test_rug() {
        let p0: offset::LocalResult<_> = offset::LocalResult::Single(Local::now());

        assert!(p0.earliest().is_some());
    }
}#[cfg(test)]
mod tests_rug_458 {
    use super::*;
    use crate::offset::{self, Local};

    #[test]
    fn test_latest() {
        let p0: offset::LocalResult<_> = offset::LocalResult::Single(Local::now());

        assert!(p0.latest().is_some());
    }
}#[cfg(test)]
mod tests_rug_460 {
    use super::*;
    use crate::{NaiveTime, offset::LocalResult, date::Date, Utc};

    #[test]
    fn test_rug() {
        let p0: LocalResult<Date<Utc>> = LocalResult::Single(Utc.ymd(2023, 10, 5));
        let p1: NaiveTime = NaiveTime::from_hms_nano(12, 34, 56, 789_012_345);

        <LocalResult<Date<Utc>>>::and_time(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_461 {
    use super::*;
    use crate::{offset::LocalResult, date::Date, Utc};

    #[test]
    fn test_rug() {
        let mut p0: LocalResult<Date<Utc>> = LocalResult::Single(Utc.ymd(2023, 10, 5));
        let mut p1: u32 = 14;
        let mut p2: u32 = 30;
        let mut p3: u32 = 45;

        <LocalResult<Date<Utc>>>::and_hms_opt(p0, p1, p2, p3);
    }
}#[cfg(test)]
mod tests_rug_462 {
    use super::*;
    use crate::{offset::LocalResult, date::Date, Utc};

    #[test]
    fn test_rug() {
        let mut p0: LocalResult<Date<Utc>> = LocalResult::Single(Utc.ymd(2023, 10, 5));
        let mut p1: u32 = 14;
        let mut p2: u32 = 30;
        let mut p3: u32 = 45;
        let mut p4: u32 = 999;

        <LocalResult<Date<Utc>>>::and_hms_milli_opt(p0, p1, p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_463 {
    use super::*;
    use crate::{offset::LocalResult, date::Date, Utc};

    #[test]
    fn test_rug() {
        let mut p0: LocalResult<Date<Utc>> = LocalResult::Single(Utc.ymd(2023, 10, 5));
        let mut p1: u32 = 14;
        let mut p2: u32 = 30;
        let mut p3: u32 = 45;
        let mut p4: u32 = 67890;

        p0.and_hms_micro_opt(p1, p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_464 {
    use super::*;
    use crate::{offset::LocalResult, date::Date, Utc};

    #[test]
    fn test_rug() {
        let mut p0: LocalResult<Date<Utc>> = LocalResult::Single(Utc.ymd(2023, 10, 5));
        let mut p1: u32 = 14;
        let mut p2: u32 = 30;
        let mut p3: u32 = 45;
        let mut p4: u32 = 1_000_000_000;

        <LocalResult<Date<Utc>>>::and_hms_nano_opt(p0, p1, p2, p3, p4);
    }
}