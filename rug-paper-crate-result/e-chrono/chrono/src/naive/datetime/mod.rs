// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! ISO 8601 date and time without timezone.

#[cfg(any(feature = "alloc", feature = "std", test))]
use core::borrow::Borrow;
use core::convert::TryFrom;
use core::fmt::Write;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::{fmt, str};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::format::DelayedFormat;
use crate::format::{parse, parse_and_remainder, ParseError, ParseResult, Parsed, StrftimeItems};
use crate::format::{Fixed, Item, Numeric, Pad};
use crate::naive::{Days, IsoWeek, NaiveDate, NaiveTime};
use crate::offset::Utc;
use crate::oldtime::Duration as OldDuration;
use crate::{DateTime, Datelike, LocalResult, Months, TimeZone, Timelike, Weekday};

#[cfg(feature = "rustc-serialize")]
pub(super) mod rustc_serialize;

/// Tools to help serializing/deserializing `NaiveDateTime`s
#[cfg(feature = "serde")]
pub(crate) mod serde;

#[cfg(test)]
mod tests;

/// The tight upper bound guarantees that a duration with `|Duration| >= 2^MAX_SECS_BITS`
/// will always overflow the addition with any date and time type.
///
/// So why is this needed? `Duration::seconds(rhs)` may overflow, and we don't have
/// an alternative returning `Option` or `Result`. Thus we need some early bound to avoid
/// touching that call when we are already sure that it WILL overflow...
const MAX_SECS_BITS: usize = 44;

/// The minimum possible `NaiveDateTime`.
#[deprecated(since = "0.4.20", note = "Use NaiveDateTime::MIN instead")]
pub const MIN_DATETIME: NaiveDateTime = NaiveDateTime::MIN;
/// The maximum possible `NaiveDateTime`.
#[deprecated(since = "0.4.20", note = "Use NaiveDateTime::MAX instead")]
pub const MAX_DATETIME: NaiveDateTime = NaiveDateTime::MAX;

/// ISO 8601 combined date and time without timezone.
///
/// # Example
///
/// `NaiveDateTime` is commonly created from [`NaiveDate`](./struct.NaiveDate.html).
///
/// ```
/// use chrono::{NaiveDate, NaiveDateTime};
///
/// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(9, 10, 11).unwrap();
/// # let _ = dt;
/// ```
///
/// You can use typical [date-like](../trait.Datelike.html) and
/// [time-like](../trait.Timelike.html) methods,
/// provided that relevant traits are in the scope.
///
/// ```
/// # use chrono::{NaiveDate, NaiveDateTime};
/// # let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(9, 10, 11).unwrap();
/// use chrono::{Datelike, Timelike, Weekday};
///
/// assert_eq!(dt.weekday(), Weekday::Fri);
/// assert_eq!(dt.num_seconds_from_midnight(), 33011);
/// ```
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct NaiveDateTime {
    date: NaiveDate,
    time: NaiveTime,
}

impl NaiveDateTime {
    /// Makes a new `NaiveDateTime` from date and time components.
    /// Equivalent to [`date.and_time(time)`](./struct.NaiveDate.html#method.and_time)
    /// and many other helper constructors on `NaiveDate`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveTime, NaiveDateTime};
    ///
    /// let d = NaiveDate::from_ymd_opt(2015, 6, 3).unwrap();
    /// let t = NaiveTime::from_hms_milli_opt(12, 34, 56, 789).unwrap();
    ///
    /// let dt = NaiveDateTime::new(d, t);
    /// assert_eq!(dt.date(), d);
    /// assert_eq!(dt.time(), t);
    /// ```
    #[inline]
    pub const fn new(date: NaiveDate, time: NaiveTime) -> NaiveDateTime {
        NaiveDateTime { date, time }
    }

    /// Makes a new `NaiveDateTime` corresponding to a UTC date and time,
    /// from the number of non-leap seconds
    /// since the midnight UTC on January 1, 1970 (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// For a non-naive version of this function see
    /// [`TimeZone::timestamp`](../offset/trait.TimeZone.html#method.timestamp).
    ///
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the
    /// [leap second](./struct.NaiveTime.html#leap-second-handling). (The true "UNIX
    /// timestamp" cannot represent a leap second unambiguously.)
    ///
    /// Panics on the out-of-range number of seconds and/or invalid nanosecond.
    #[deprecated(since = "0.4.23", note = "use `from_timestamp_opt()` instead")]
    #[inline]
    #[must_use]
    pub fn from_timestamp(secs: i64, nsecs: u32) -> NaiveDateTime {
        let datetime = NaiveDateTime::from_timestamp_opt(secs, nsecs);
        datetime.expect("invalid or out-of-range datetime")
    }

    /// Creates a new [NaiveDateTime] from milliseconds since the UNIX epoch.
    ///
    /// The UNIX epoch starts on midnight, January 1, 1970, UTC.
    ///
    /// Returns `None` on an out-of-range number of milliseconds.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDateTime;
    /// let timestamp_millis: i64 = 1662921288000; //Sunday, September 11, 2022 6:34:48 PM
    /// let naive_datetime = NaiveDateTime::from_timestamp_millis(timestamp_millis);
    /// assert!(naive_datetime.is_some());
    /// assert_eq!(timestamp_millis, naive_datetime.unwrap().timestamp_millis());
    ///
    /// // Negative timestamps (before the UNIX epoch) are supported as well.
    /// let timestamp_millis: i64 = -2208936075000; //Mon Jan 01 1900 14:38:45 GMT+0000
    /// let naive_datetime = NaiveDateTime::from_timestamp_millis(timestamp_millis);
    /// assert!(naive_datetime.is_some());
    /// assert_eq!(timestamp_millis, naive_datetime.unwrap().timestamp_millis());
    /// ```
    #[inline]
    #[must_use]
    pub fn from_timestamp_millis(millis: i64) -> Option<NaiveDateTime> {
        let secs = millis.div_euclid(1000);
        let nsecs = millis.rem_euclid(1000) as u32 * 1_000_000;
        NaiveDateTime::from_timestamp_opt(secs, nsecs)
    }

    /// Creates a new [NaiveDateTime] from microseconds since the UNIX epoch.
    ///
    /// The UNIX epoch starts on midnight, January 1, 1970, UTC.
    ///
    /// Returns `None` on an out-of-range number of microseconds.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDateTime;
    /// let timestamp_micros: i64 = 1662921288000000; //Sunday, September 11, 2022 6:34:48 PM
    /// let naive_datetime = NaiveDateTime::from_timestamp_micros(timestamp_micros);
    /// assert!(naive_datetime.is_some());
    /// assert_eq!(timestamp_micros, naive_datetime.unwrap().timestamp_micros());
    ///
    /// // Negative timestamps (before the UNIX epoch) are supported as well.
    /// let timestamp_micros: i64 = -2208936075000000; //Mon Jan 01 1900 14:38:45 GMT+0000
    /// let naive_datetime = NaiveDateTime::from_timestamp_micros(timestamp_micros);
    /// assert!(naive_datetime.is_some());
    /// assert_eq!(timestamp_micros, naive_datetime.unwrap().timestamp_micros());
    /// ```
    #[inline]
    #[must_use]
    pub fn from_timestamp_micros(micros: i64) -> Option<NaiveDateTime> {
        let secs = micros.div_euclid(1_000_000);
        let nsecs = micros.rem_euclid(1_000_000) as u32 * 1000;
        NaiveDateTime::from_timestamp_opt(secs, nsecs)
    }

    /// Makes a new `NaiveDateTime` corresponding to a UTC date and time,
    /// from the number of non-leap seconds
    /// since the midnight UTC on January 1, 1970 (aka "UNIX timestamp")
    /// and the number of nanoseconds since the last whole non-leap second.
    ///
    /// The nanosecond part can exceed 1,000,000,000
    /// in order to represent the [leap second](./struct.NaiveTime.html#leap-second-handling).
    /// (The true "UNIX timestamp" cannot represent a leap second unambiguously.)
    ///
    /// Returns `None` on the out-of-range number of seconds (more than 262 000 years away
    /// from common era) and/or invalid nanosecond (2 seconds or more).
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDateTime;
    /// use std::i64;
    ///
    /// let from_timestamp_opt = NaiveDateTime::from_timestamp_opt;
    ///
    /// assert!(from_timestamp_opt(0, 0).is_some());
    /// assert!(from_timestamp_opt(0, 999_999_999).is_some());
    /// assert!(from_timestamp_opt(0, 1_500_000_000).is_some()); // leap second
    /// assert!(from_timestamp_opt(0, 2_000_000_000).is_none());
    /// assert!(from_timestamp_opt(i64::MAX, 0).is_none());
    /// ```
    #[inline]
    #[must_use]
    pub fn from_timestamp_opt(secs: i64, nsecs: u32) -> Option<NaiveDateTime> {
        let days = secs.div_euclid(86_400);
        let secs = secs.rem_euclid(86_400);
        let date = i32::try_from(days)
            .ok()
            .and_then(|days| days.checked_add(719_163))
            .and_then(NaiveDate::from_num_days_from_ce_opt);
        let time = NaiveTime::from_num_seconds_from_midnight_opt(secs as u32, nsecs);
        match (date, time) {
            (Some(date), Some(time)) => Some(NaiveDateTime { date, time }),
            (_, _) => None,
        }
    }

    /// Parses a string with the specified format string and returns a new `NaiveDateTime`.
    /// See the [`format::strftime` module](../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDateTime, NaiveDate};
    ///
    /// let parse_from_str = NaiveDateTime::parse_from_str;
    ///
    /// assert_eq!(parse_from_str("2015-09-05 23:56:04", "%Y-%m-%d %H:%M:%S"),
    ///            Ok(NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_opt(23, 56, 4).unwrap()));
    /// assert_eq!(parse_from_str("5sep2015pm012345.6789", "%d%b%Y%p%I%M%S%.f"),
    ///            Ok(NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_micro_opt(13, 23, 45, 678_900).unwrap()));
    /// ```
    ///
    /// Offset is ignored for the purpose of parsing.
    ///
    /// ```
    /// # use chrono::{NaiveDateTime, NaiveDate};
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// assert_eq!(parse_from_str("2014-5-17T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
    ///            Ok(NaiveDate::from_ymd_opt(2014, 5, 17).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// ```
    ///
    /// [Leap seconds](./struct.NaiveTime.html#leap-second-handling) are correctly handled by
    /// treating any time of the form `hh:mm:60` as a leap second.
    /// (This equally applies to the formatting, so the round trip is possible.)
    ///
    /// ```
    /// # use chrono::{NaiveDateTime, NaiveDate};
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// assert_eq!(parse_from_str("2015-07-01 08:59:60.123", "%Y-%m-%d %H:%M:%S%.f"),
    ///            Ok(NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_milli_opt(8, 59, 59, 1_123).unwrap()));
    /// ```
    ///
    /// Missing seconds are assumed to be zero,
    /// but out-of-bound times or insufficient fields are errors otherwise.
    ///
    /// ```
    /// # use chrono::{NaiveDateTime, NaiveDate};
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// assert_eq!(parse_from_str("94/9/4 7:15", "%y/%m/%d %H:%M"),
    ///            Ok(NaiveDate::from_ymd_opt(1994, 9, 4).unwrap().and_hms_opt(7, 15, 0).unwrap()));
    ///
    /// assert!(parse_from_str("04m33s", "%Mm%Ss").is_err());
    /// assert!(parse_from_str("94/9/4 12", "%y/%m/%d %H").is_err());
    /// assert!(parse_from_str("94/9/4 17:60", "%y/%m/%d %H:%M").is_err());
    /// assert!(parse_from_str("94/9/4 24:00:00", "%y/%m/%d %H:%M:%S").is_err());
    /// ```
    ///
    /// All parsed fields should be consistent to each other, otherwise it's an error.
    ///
    /// ```
    /// # use chrono::NaiveDateTime;
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// let fmt = "%Y-%m-%d %H:%M:%S = UNIX timestamp %s";
    /// assert!(parse_from_str("2001-09-09 01:46:39 = UNIX timestamp 999999999", fmt).is_ok());
    /// assert!(parse_from_str("1970-01-01 00:00:00 = UNIX timestamp 1", fmt).is_err());
    /// ```
    ///
    /// Years before 1 BCE or after 9999 CE, require an initial sign
    ///
    ///```
    /// # use chrono::NaiveDateTime;
    /// # let parse_from_str = NaiveDateTime::parse_from_str;
    /// let fmt = "%Y-%m-%d %H:%M:%S";
    /// assert!(parse_from_str("10000-09-09 01:46:39", fmt).is_err());
    /// assert!(parse_from_str("+10000-09-09 01:46:39", fmt).is_ok());
    ///```
    pub fn parse_from_str(s: &str, fmt: &str) -> ParseResult<NaiveDateTime> {
        let mut parsed = Parsed::new();
        parse(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_naive_datetime_with_offset(0) // no offset adjustment
    }

    /// Parses a string with the specified format string and returns a new `NaiveDateTime`, and a
    /// slice with the remaining portion of the string.
    /// See the [`format::strftime` module](../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// Similar to [`parse_from_str`](#method.parse_from_str).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use chrono::{NaiveDate, NaiveDateTime};
    /// let (datetime, remainder) = NaiveDateTime::parse_and_remainder(
    ///     "2015-02-18 23:16:09 trailing text", "%Y-%m-%d %H:%M:%S").unwrap();
    /// assert_eq!(
    ///     datetime,
    ///     NaiveDate::from_ymd_opt(2015, 2, 18).unwrap().and_hms_opt(23, 16, 9).unwrap()
    /// );
    /// assert_eq!(remainder, " trailing text");
    /// ```
    pub fn parse_and_remainder<'a>(s: &'a str, fmt: &str) -> ParseResult<(NaiveDateTime, &'a str)> {
        let mut parsed = Parsed::new();
        let remainder = parse_and_remainder(&mut parsed, s, StrftimeItems::new(fmt))?;
        parsed.to_naive_datetime_with_offset(0).map(|d| (d, remainder)) // no offset adjustment
    }

    /// Retrieves a date component.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(9, 10, 11).unwrap();
    /// assert_eq!(dt.date(), NaiveDate::from_ymd_opt(2016, 7, 8).unwrap());
    /// ```
    #[inline]
    pub const fn date(&self) -> NaiveDate {
        self.date
    }

    /// Retrieves a time component.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveTime};
    ///
    /// let dt = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(9, 10, 11).unwrap();
    /// assert_eq!(dt.time(), NaiveTime::from_hms_opt(9, 10, 11).unwrap());
    /// ```
    #[inline]
    pub const fn time(&self) -> NaiveTime {
        self.time
    }

    /// Returns the number of non-leap seconds since the midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_milli_opt(0, 0, 1, 980).unwrap();
    /// assert_eq!(dt.timestamp(), 1);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_opt(1, 46, 40).unwrap();
    /// assert_eq!(dt.timestamp(), 1_000_000_000);
    ///
    /// let dt = NaiveDate::from_ymd_opt(1969, 12, 31).unwrap().and_hms_opt(23, 59, 59).unwrap();
    /// assert_eq!(dt.timestamp(), -1);
    ///
    /// let dt = NaiveDate::from_ymd_opt(-1, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();
    /// assert_eq!(dt.timestamp(), -62198755200);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp(&self) -> i64 {
        const UNIX_EPOCH_DAY: i64 = 719_163;
        let gregorian_day = i64::from(self.date.num_days_from_ce());
        let seconds_from_midnight = i64::from(self.time.num_seconds_from_midnight());
        (gregorian_day - UNIX_EPOCH_DAY) * 86_400 + seconds_from_midnight
    }

    /// Returns the number of non-leap *milliseconds* since midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// Note also that this does reduce the number of years that can be
    /// represented from ~584 Billion to ~584 Million. (If this is a problem,
    /// please file an issue to let me know what domain needs millisecond
    /// precision over billions of years, I'm curious.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_milli_opt(0, 0, 1, 444).unwrap();
    /// assert_eq!(dt.timestamp_millis(), 1_444);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_milli_opt(1, 46, 40, 555).unwrap();
    /// assert_eq!(dt.timestamp_millis(), 1_000_000_000_555);
    ///
    /// let dt = NaiveDate::from_ymd_opt(1969, 12, 31).unwrap().and_hms_milli_opt(23, 59, 59, 100).unwrap();
    /// assert_eq!(dt.timestamp_millis(), -900);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_millis(&self) -> i64 {
        let as_ms = self.timestamp() * 1000;
        as_ms + i64::from(self.timestamp_subsec_millis())
    }

    /// Returns the number of non-leap *microseconds* since midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// Note also that this does reduce the number of years that can be
    /// represented from ~584 Billion to ~584 Thousand. (If this is a problem,
    /// please file an issue to let me know what domain needs microsecond
    /// precision over millennia, I'm curious.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_micro_opt(0, 0, 1, 444).unwrap();
    /// assert_eq!(dt.timestamp_micros(), 1_000_444);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_micro_opt(1, 46, 40, 555).unwrap();
    /// assert_eq!(dt.timestamp_micros(), 1_000_000_000_000_555);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_micros(&self) -> i64 {
        let as_us = self.timestamp() * 1_000_000;
        as_us + i64::from(self.timestamp_subsec_micros())
    }

    /// Returns the number of non-leap *nanoseconds* since midnight on January 1, 1970.
    ///
    /// Note that this does *not* account for the timezone!
    /// The true "UNIX timestamp" would count seconds since the midnight *UTC* on the epoch.
    ///
    /// # Panics
    ///
    /// Note also that this does reduce the number of years that can be
    /// represented from ~584 Billion to ~584 years. The dates that can be
    /// represented as nanoseconds are between 1677-09-21T00:12:44.0 and
    /// 2262-04-11T23:47:16.854775804.
    ///
    /// (If this is a problem, please file an issue to let me know what domain
    /// needs nanosecond precision over millennia, I'm curious.)
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime};
    ///
    /// let dt = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_nano_opt(0, 0, 1, 444).unwrap();
    /// assert_eq!(dt.timestamp_nanos(), 1_000_000_444);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_nano_opt(1, 46, 40, 555).unwrap();
    ///
    /// const A_BILLION: i64 = 1_000_000_000;
    /// let nanos = dt.timestamp_nanos();
    /// assert_eq!(nanos, 1_000_000_000_000_000_555);
    /// assert_eq!(
    ///     Some(dt),
    ///     NaiveDateTime::from_timestamp_opt(nanos / A_BILLION, (nanos % A_BILLION) as u32)
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_nanos(&self) -> i64 {
        let as_ns = self.timestamp() * 1_000_000_000;
        as_ns + i64::from(self.timestamp_subsec_nanos())
    }

    /// Returns the number of milliseconds since the last whole non-leap second.
    ///
    /// The return value ranges from 0 to 999,
    /// or for [leap seconds](./struct.NaiveTime.html#leap-second-handling), to 1,999.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_nano_opt(9, 10, 11, 123_456_789).unwrap();
    /// assert_eq!(dt.timestamp_subsec_millis(), 123);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_nano_opt(8, 59, 59, 1_234_567_890).unwrap();
    /// assert_eq!(dt.timestamp_subsec_millis(), 1_234);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_subsec_millis(&self) -> u32 {
        self.timestamp_subsec_nanos() / 1_000_000
    }

    /// Returns the number of microseconds since the last whole non-leap second.
    ///
    /// The return value ranges from 0 to 999,999,
    /// or for [leap seconds](./struct.NaiveTime.html#leap-second-handling), to 1,999,999.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_nano_opt(9, 10, 11, 123_456_789).unwrap();
    /// assert_eq!(dt.timestamp_subsec_micros(), 123_456);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_nano_opt(8, 59, 59, 1_234_567_890).unwrap();
    /// assert_eq!(dt.timestamp_subsec_micros(), 1_234_567);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_subsec_micros(&self) -> u32 {
        self.timestamp_subsec_nanos() / 1_000
    }

    /// Returns the number of nanoseconds since the last whole non-leap second.
    ///
    /// The return value ranges from 0 to 999,999,999,
    /// or for [leap seconds](./struct.NaiveTime.html#leap-second-handling), to 1,999,999,999.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_nano_opt(9, 10, 11, 123_456_789).unwrap();
    /// assert_eq!(dt.timestamp_subsec_nanos(), 123_456_789);
    ///
    /// let dt = NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_nano_opt(8, 59, 59, 1_234_567_890).unwrap();
    /// assert_eq!(dt.timestamp_subsec_nanos(), 1_234_567_890);
    /// ```
    #[inline]
    #[must_use]
    pub fn timestamp_subsec_nanos(&self) -> u32 {
        self.time.nanosecond()
    }

    /// Adds given `Duration` to the current date and time.
    ///
    /// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
    /// the addition assumes that **there is no leap second ever**,
    /// except when the `NaiveDateTime` itself represents a leap second
    /// in which case the assumption becomes that **there is exactly a single leap second ever**.
    ///
    /// Returns `None` when it will result in overflow.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Duration, NaiveDate};
    ///
    /// let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
    ///
    /// let d = from_ymd(2016, 7, 8);
    /// let hms = |h, m, s| d.and_hms_opt(h, m, s).unwrap();
    /// assert_eq!(hms(3, 5, 7).checked_add_signed(Duration::zero()),
    ///            Some(hms(3, 5, 7)));
    /// assert_eq!(hms(3, 5, 7).checked_add_signed(Duration::seconds(1)),
    ///            Some(hms(3, 5, 8)));
    /// assert_eq!(hms(3, 5, 7).checked_add_signed(Duration::seconds(-1)),
    ///            Some(hms(3, 5, 6)));
    /// assert_eq!(hms(3, 5, 7).checked_add_signed(Duration::seconds(3600 + 60)),
    ///            Some(hms(4, 6, 7)));
    /// assert_eq!(hms(3, 5, 7).checked_add_signed(Duration::seconds(86_400)),
    ///            Some(from_ymd(2016, 7, 9).and_hms_opt(3, 5, 7).unwrap()));
    ///
    /// let hmsm = |h, m, s, milli| d.and_hms_milli_opt(h, m, s, milli).unwrap();
    /// assert_eq!(hmsm(3, 5, 7, 980).checked_add_signed(Duration::milliseconds(450)),
    ///            Some(hmsm(3, 5, 8, 430)));
    /// ```
    ///
    /// Overflow returns `None`.
    ///
    /// ```
    /// # use chrono::{Duration, NaiveDate};
    /// # let hms = |h, m, s| NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(h, m, s).unwrap();
    /// assert_eq!(hms(3, 5, 7).checked_add_signed(Duration::days(1_000_000_000)), None);
    /// ```
    ///
    /// Leap seconds are handled,
    /// but the addition assumes that it is the only leap second happened.
    ///
    /// ```
    /// # use chrono::{Duration, NaiveDate};
    /// # let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
    /// # let hmsm = |h, m, s, milli| from_ymd(2016, 7, 8).and_hms_milli_opt(h, m, s, milli).unwrap();
    /// let leap = hmsm(3, 5, 59, 1_300);
    /// assert_eq!(leap.checked_add_signed(Duration::zero()),
    ///            Some(hmsm(3, 5, 59, 1_300)));
    /// assert_eq!(leap.checked_add_signed(Duration::milliseconds(-500)),
    ///            Some(hmsm(3, 5, 59, 800)));
    /// assert_eq!(leap.checked_add_signed(Duration::milliseconds(500)),
    ///            Some(hmsm(3, 5, 59, 1_800)));
    /// assert_eq!(leap.checked_add_signed(Duration::milliseconds(800)),
    ///            Some(hmsm(3, 6, 0, 100)));
    /// assert_eq!(leap.checked_add_signed(Duration::seconds(10)),
    ///            Some(hmsm(3, 6, 9, 300)));
    /// assert_eq!(leap.checked_add_signed(Duration::seconds(-10)),
    ///            Some(hmsm(3, 5, 50, 300)));
    /// assert_eq!(leap.checked_add_signed(Duration::days(1)),
    ///            Some(from_ymd(2016, 7, 9).and_hms_milli_opt(3, 5, 59, 300).unwrap()));
    /// ```
    #[must_use]
    pub fn checked_add_signed(self, rhs: OldDuration) -> Option<NaiveDateTime> {
        let (time, rhs) = self.time.overflowing_add_signed(rhs);

        // early checking to avoid overflow in OldDuration::seconds
        if rhs <= (-1 << MAX_SECS_BITS) || rhs >= (1 << MAX_SECS_BITS) {
            return None;
        }

        let date = self.date.checked_add_signed(OldDuration::seconds(rhs))?;
        Some(NaiveDateTime { date, time })
    }

    /// Adds given `Months` to the current date and time.
    ///
    /// Returns `None` when it will result in overflow.
    ///
    /// Overflow returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Months, NaiveDate};
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap()
    ///         .checked_add_months(Months::new(1)),
    ///     Some(NaiveDate::from_ymd_opt(2014, 2, 1).unwrap().and_hms_opt(1, 0, 0).unwrap())
    /// );
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap()
    ///         .checked_add_months(Months::new(core::i32::MAX as u32 + 1)),
    ///     None
    /// );
    /// ```
    #[must_use]
    pub fn checked_add_months(self, rhs: Months) -> Option<NaiveDateTime> {
        Some(Self { date: self.date.checked_add_months(rhs)?, time: self.time })
    }

    /// Subtracts given `Duration` from the current date and time.
    ///
    /// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
    /// the subtraction assumes that **there is no leap second ever**,
    /// except when the `NaiveDateTime` itself represents a leap second
    /// in which case the assumption becomes that **there is exactly a single leap second ever**.
    ///
    /// Returns `None` when it will result in overflow.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Duration, NaiveDate};
    ///
    /// let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
    ///
    /// let d = from_ymd(2016, 7, 8);
    /// let hms = |h, m, s| d.and_hms_opt(h, m, s).unwrap();
    /// assert_eq!(hms(3, 5, 7).checked_sub_signed(Duration::zero()),
    ///            Some(hms(3, 5, 7)));
    /// assert_eq!(hms(3, 5, 7).checked_sub_signed(Duration::seconds(1)),
    ///            Some(hms(3, 5, 6)));
    /// assert_eq!(hms(3, 5, 7).checked_sub_signed(Duration::seconds(-1)),
    ///            Some(hms(3, 5, 8)));
    /// assert_eq!(hms(3, 5, 7).checked_sub_signed(Duration::seconds(3600 + 60)),
    ///            Some(hms(2, 4, 7)));
    /// assert_eq!(hms(3, 5, 7).checked_sub_signed(Duration::seconds(86_400)),
    ///            Some(from_ymd(2016, 7, 7).and_hms_opt(3, 5, 7).unwrap()));
    ///
    /// let hmsm = |h, m, s, milli| d.and_hms_milli_opt(h, m, s, milli).unwrap();
    /// assert_eq!(hmsm(3, 5, 7, 450).checked_sub_signed(Duration::milliseconds(670)),
    ///            Some(hmsm(3, 5, 6, 780)));
    /// ```
    ///
    /// Overflow returns `None`.
    ///
    /// ```
    /// # use chrono::{Duration, NaiveDate};
    /// # let hms = |h, m, s| NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(h, m, s).unwrap();
    /// assert_eq!(hms(3, 5, 7).checked_sub_signed(Duration::days(1_000_000_000)), None);
    /// ```
    ///
    /// Leap seconds are handled,
    /// but the subtraction assumes that it is the only leap second happened.
    ///
    /// ```
    /// # use chrono::{Duration, NaiveDate};
    /// # let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
    /// # let hmsm = |h, m, s, milli| from_ymd(2016, 7, 8).and_hms_milli_opt(h, m, s, milli).unwrap();
    /// let leap = hmsm(3, 5, 59, 1_300);
    /// assert_eq!(leap.checked_sub_signed(Duration::zero()),
    ///            Some(hmsm(3, 5, 59, 1_300)));
    /// assert_eq!(leap.checked_sub_signed(Duration::milliseconds(200)),
    ///            Some(hmsm(3, 5, 59, 1_100)));
    /// assert_eq!(leap.checked_sub_signed(Duration::milliseconds(500)),
    ///            Some(hmsm(3, 5, 59, 800)));
    /// assert_eq!(leap.checked_sub_signed(Duration::seconds(60)),
    ///            Some(hmsm(3, 5, 0, 300)));
    /// assert_eq!(leap.checked_sub_signed(Duration::days(1)),
    ///            Some(from_ymd(2016, 7, 7).and_hms_milli_opt(3, 6, 0, 300).unwrap()));
    /// ```
    #[must_use]
    pub fn checked_sub_signed(self, rhs: OldDuration) -> Option<NaiveDateTime> {
        let (time, rhs) = self.time.overflowing_sub_signed(rhs);

        // early checking to avoid overflow in OldDuration::seconds
        if rhs <= (-1 << MAX_SECS_BITS) || rhs >= (1 << MAX_SECS_BITS) {
            return None;
        }

        let date = self.date.checked_sub_signed(OldDuration::seconds(rhs))?;
        Some(NaiveDateTime { date, time })
    }

    /// Subtracts given `Months` from the current date and time.
    ///
    /// Returns `None` when it will result in overflow.
    ///
    /// Overflow returns `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Months, NaiveDate};
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap()
    ///         .checked_sub_months(Months::new(1)),
    ///     Some(NaiveDate::from_ymd_opt(2013, 12, 1).unwrap().and_hms_opt(1, 0, 0).unwrap())
    /// );
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap()
    ///         .checked_sub_months(Months::new(core::i32::MAX as u32 + 1)),
    ///     None
    /// );
    /// ```
    #[must_use]
    pub fn checked_sub_months(self, rhs: Months) -> Option<NaiveDateTime> {
        Some(Self { date: self.date.checked_sub_months(rhs)?, time: self.time })
    }

    /// Add a duration in [`Days`] to the date part of the `NaiveDateTime`
    ///
    /// Returns `None` if the resulting date would be out of range.
    #[must_use]
    pub fn checked_add_days(self, days: Days) -> Option<Self> {
        Some(Self { date: self.date.checked_add_days(days)?, ..self })
    }

    /// Subtract a duration in [`Days`] from the date part of the `NaiveDateTime`
    ///
    /// Returns `None` if the resulting date would be out of range.
    #[must_use]
    pub fn checked_sub_days(self, days: Days) -> Option<Self> {
        Some(Self { date: self.date.checked_sub_days(days)?, ..self })
    }

    /// Subtracts another `NaiveDateTime` from the current date and time.
    /// This does not overflow or underflow at all.
    ///
    /// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
    /// the subtraction assumes that **there is no leap second ever**,
    /// except when any of the `NaiveDateTime`s themselves represents a leap second
    /// in which case the assumption becomes that
    /// **there are exactly one (or two) leap second(s) ever**.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Duration, NaiveDate};
    ///
    /// let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
    ///
    /// let d = from_ymd(2016, 7, 8);
    /// assert_eq!(d.and_hms_opt(3, 5, 7).unwrap().signed_duration_since(d.and_hms_opt(2, 4, 6).unwrap()),
    ///            Duration::seconds(3600 + 60 + 1));
    ///
    /// // July 8 is 190th day in the year 2016
    /// let d0 = from_ymd(2016, 1, 1);
    /// assert_eq!(d.and_hms_milli_opt(0, 7, 6, 500).unwrap().signed_duration_since(d0.and_hms_opt(0, 0, 0).unwrap()),
    ///            Duration::seconds(189 * 86_400 + 7 * 60 + 6) + Duration::milliseconds(500));
    /// ```
    ///
    /// Leap seconds are handled, but the subtraction assumes that
    /// there were no other leap seconds happened.
    ///
    /// ```
    /// # use chrono::{Duration, NaiveDate};
    /// # let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
    /// let leap = from_ymd(2015, 6, 30).and_hms_milli_opt(23, 59, 59, 1_500).unwrap();
    /// assert_eq!(leap.signed_duration_since(from_ymd(2015, 6, 30).and_hms_opt(23, 0, 0).unwrap()),
    ///            Duration::seconds(3600) + Duration::milliseconds(500));
    /// assert_eq!(from_ymd(2015, 7, 1).and_hms_opt(1, 0, 0).unwrap().signed_duration_since(leap),
    ///            Duration::seconds(3600) - Duration::milliseconds(500));
    /// ```
    #[must_use]
    pub fn signed_duration_since(self, rhs: NaiveDateTime) -> OldDuration {
        self.date.signed_duration_since(rhs.date) + self.time.signed_duration_since(rhs.time)
    }

    /// Formats the combined date and time with the specified formatting items.
    /// Otherwise it is the same as the ordinary [`format`](#method.format) method.
    ///
    /// The `Iterator` of items should be `Clone`able,
    /// since the resulting `DelayedFormat` value may be formatted multiple times.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    /// use chrono::format::strftime::StrftimeItems;
    ///
    /// let fmt = StrftimeItems::new("%Y-%m-%d %H:%M:%S");
    /// let dt = NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_opt(23, 56, 4).unwrap();
    /// assert_eq!(dt.format_with_items(fmt.clone()).to_string(), "2015-09-05 23:56:04");
    /// assert_eq!(dt.format("%Y-%m-%d %H:%M:%S").to_string(),    "2015-09-05 23:56:04");
    /// ```
    ///
    /// The resulting `DelayedFormat` can be formatted directly via the `Display` trait.
    ///
    /// ```
    /// # use chrono::NaiveDate;
    /// # use chrono::format::strftime::StrftimeItems;
    /// # let fmt = StrftimeItems::new("%Y-%m-%d %H:%M:%S").clone();
    /// # let dt = NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_opt(23, 56, 4).unwrap();
    /// assert_eq!(format!("{}", dt.format_with_items(fmt)), "2015-09-05 23:56:04");
    /// ```
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    #[must_use]
    pub fn format_with_items<'a, I, B>(&self, items: I) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        DelayedFormat::new(Some(self.date), Some(self.time), items)
    }

    /// Formats the combined date and time with the specified format string.
    /// See the [`format::strftime` module](../format/strftime/index.html)
    /// on the supported escape sequences.
    ///
    /// This returns a `DelayedFormat`,
    /// which gets converted to a string only when actual formatting happens.
    /// You may use the `to_string` method to get a `String`,
    /// or just feed it into `print!` and other formatting macros.
    /// (In this way it avoids the redundant memory allocation.)
    ///
    /// A wrong format string does *not* issue an error immediately.
    /// Rather, converting or formatting the `DelayedFormat` fails.
    /// You are recommended to immediately use `DelayedFormat` for this reason.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::NaiveDate;
    ///
    /// let dt = NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_opt(23, 56, 4).unwrap();
    /// assert_eq!(dt.format("%Y-%m-%d %H:%M:%S").to_string(), "2015-09-05 23:56:04");
    /// assert_eq!(dt.format("around %l %p on %b %-d").to_string(), "around 11 PM on Sep 5");
    /// ```
    ///
    /// The resulting `DelayedFormat` can be formatted directly via the `Display` trait.
    ///
    /// ```
    /// # use chrono::NaiveDate;
    /// # let dt = NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_opt(23, 56, 4).unwrap();
    /// assert_eq!(format!("{}", dt.format("%Y-%m-%d %H:%M:%S")), "2015-09-05 23:56:04");
    /// assert_eq!(format!("{}", dt.format("around %l %p on %b %-d")), "around 11 PM on Sep 5");
    /// ```
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    #[must_use]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }

    /// Converts the `NaiveDateTime` into the timezone-aware `DateTime<Tz>`
    /// with the provided timezone, if possible.
    ///
    /// This can fail in cases where the local time represented by the `NaiveDateTime`
    /// is not a valid local timestamp in the target timezone due to an offset transition
    /// for example if the target timezone had a change from +00:00 to +01:00
    /// occuring at 2015-09-05 22:59:59, then a local time of 2015-09-05 23:56:04
    /// could never occur. Similarly, if the offset transitioned in the opposite direction
    /// then there would be two local times of 2015-09-05 23:56:04, one at +00:00 and one
    /// at +01:00.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, FixedOffset};
    /// let hour = 3600;
    /// let tz = FixedOffset::east_opt(5 * hour).unwrap();
    /// let dt = NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_opt(23, 56, 4).unwrap().and_local_timezone(tz).unwrap();
    /// assert_eq!(dt.timezone(), tz);
    /// ```
    #[must_use]
    pub fn and_local_timezone<Tz: TimeZone>(&self, tz: Tz) -> LocalResult<DateTime<Tz>> {
        tz.from_local_datetime(self)
    }

    /// Converts the `NaiveDateTime` into the timezone-aware `DateTime<Utc>`.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, Utc};
    /// let dt = NaiveDate::from_ymd_opt(2023, 1, 30).unwrap().and_hms_opt(19, 32, 33).unwrap().and_utc();
    /// assert_eq!(dt.timezone(), Utc);
    /// ```
    #[must_use]
    pub fn and_utc(&self) -> DateTime<Utc> {
        Utc.from_utc_datetime(self)
    }

    /// The minimum possible `NaiveDateTime`.
    pub const MIN: Self = Self { date: NaiveDate::MIN, time: NaiveTime::MIN };
    /// The maximum possible `NaiveDateTime`.
    pub const MAX: Self = Self { date: NaiveDate::MAX, time: NaiveTime::MAX };
}

impl Datelike for NaiveDateTime {
    /// Returns the year number in the [calendar date](./struct.NaiveDate.html#calendar-date).
    ///
    /// See also the [`NaiveDate::year`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.year(), 2015);
    /// ```
    #[inline]
    fn year(&self) -> i32 {
        self.date.year()
    }

    /// Returns the month number starting from 1.
    ///
    /// The return value ranges from 1 to 12.
    ///
    /// See also the [`NaiveDate::month`](./struct.NaiveDate.html#method.month) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.month(), 9);
    /// ```
    #[inline]
    fn month(&self) -> u32 {
        self.date.month()
    }

    /// Returns the month number starting from 0.
    ///
    /// The return value ranges from 0 to 11.
    ///
    /// See also the [`NaiveDate::month0`](./struct.NaiveDate.html#method.month0) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.month0(), 8);
    /// ```
    #[inline]
    fn month0(&self) -> u32 {
        self.date.month0()
    }

    /// Returns the day of month starting from 1.
    ///
    /// The return value ranges from 1 to 31. (The last day of month differs by months.)
    ///
    /// See also the [`NaiveDate::day`](./struct.NaiveDate.html#method.day) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.day(), 25);
    /// ```
    #[inline]
    fn day(&self) -> u32 {
        self.date.day()
    }

    /// Returns the day of month starting from 0.
    ///
    /// The return value ranges from 0 to 30. (The last day of month differs by months.)
    ///
    /// See also the [`NaiveDate::day0`](./struct.NaiveDate.html#method.day0) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.day0(), 24);
    /// ```
    #[inline]
    fn day0(&self) -> u32 {
        self.date.day0()
    }

    /// Returns the day of year starting from 1.
    ///
    /// The return value ranges from 1 to 366. (The last day of year differs by years.)
    ///
    /// See also the [`NaiveDate::ordinal`](./struct.NaiveDate.html#method.ordinal) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.ordinal(), 268);
    /// ```
    #[inline]
    fn ordinal(&self) -> u32 {
        self.date.ordinal()
    }

    /// Returns the day of year starting from 0.
    ///
    /// The return value ranges from 0 to 365. (The last day of year differs by years.)
    ///
    /// See also the [`NaiveDate::ordinal0`](./struct.NaiveDate.html#method.ordinal0) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.ordinal0(), 267);
    /// ```
    #[inline]
    fn ordinal0(&self) -> u32 {
        self.date.ordinal0()
    }

    /// Returns the day of week.
    ///
    /// See also the [`NaiveDate::weekday`](./struct.NaiveDate.html#method.weekday) method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike, Weekday};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.weekday(), Weekday::Fri);
    /// ```
    #[inline]
    fn weekday(&self) -> Weekday {
        self.date.weekday()
    }

    #[inline]
    fn iso_week(&self) -> IsoWeek {
        self.date.iso_week()
    }

    /// Makes a new `NaiveDateTime` with the year number changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveDate::with_year`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_year(2016), Some(NaiveDate::from_ymd_opt(2016, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_year(-308), Some(NaiveDate::from_ymd_opt(-308, 9, 25).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// ```
    #[inline]
    fn with_year(&self, year: i32) -> Option<NaiveDateTime> {
        self.date.with_year(year).map(|d| NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the month number (starting from 1) changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveDate::with_month`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 30).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_month(10), Some(NaiveDate::from_ymd_opt(2015, 10, 30).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_month(13), None); // no month 13
    /// assert_eq!(dt.with_month(2), None); // no February 30
    /// ```
    #[inline]
    fn with_month(&self, month: u32) -> Option<NaiveDateTime> {
        self.date.with_month(month).map(|d| NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the month number (starting from 0) changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveDate::with_month0`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 30).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_month0(9), Some(NaiveDate::from_ymd_opt(2015, 10, 30).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_month0(12), None); // no month 13
    /// assert_eq!(dt.with_month0(1), None); // no February 30
    /// ```
    #[inline]
    fn with_month0(&self, month0: u32) -> Option<NaiveDateTime> {
        self.date.with_month0(month0).map(|d| NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of month (starting from 1) changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveDate::with_day`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_day(30), Some(NaiveDate::from_ymd_opt(2015, 9, 30).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_day(31), None); // no September 31
    /// ```
    #[inline]
    fn with_day(&self, day: u32) -> Option<NaiveDateTime> {
        self.date.with_day(day).map(|d| NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of month (starting from 0) changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveDate::with_day0`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_day0(29), Some(NaiveDate::from_ymd_opt(2015, 9, 30).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_day0(30), None); // no September 31
    /// ```
    #[inline]
    fn with_day0(&self, day0: u32) -> Option<NaiveDateTime> {
        self.date.with_day0(day0).map(|d| NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of year (starting from 1) changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveDate::with_ordinal`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_ordinal(60),
    ///            Some(NaiveDate::from_ymd_opt(2015, 3, 1).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_ordinal(366), None); // 2015 had only 365 days
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 9, 8).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_ordinal(60),
    ///            Some(NaiveDate::from_ymd_opt(2016, 2, 29).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_ordinal(366),
    ///            Some(NaiveDate::from_ymd_opt(2016, 12, 31).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// ```
    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<NaiveDateTime> {
        self.date.with_ordinal(ordinal).map(|d| NaiveDateTime { date: d, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the day of year (starting from 0) changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveDate::with_ordinal0`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Datelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_ordinal0(59),
    ///            Some(NaiveDate::from_ymd_opt(2015, 3, 1).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_ordinal0(365), None); // 2015 had only 365 days
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 9, 8).unwrap().and_hms_opt(12, 34, 56).unwrap();
    /// assert_eq!(dt.with_ordinal0(59),
    ///            Some(NaiveDate::from_ymd_opt(2016, 2, 29).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// assert_eq!(dt.with_ordinal0(365),
    ///            Some(NaiveDate::from_ymd_opt(2016, 12, 31).unwrap().and_hms_opt(12, 34, 56).unwrap()));
    /// ```
    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<NaiveDateTime> {
        self.date.with_ordinal0(ordinal0).map(|d| NaiveDateTime { date: d, ..*self })
    }
}

impl Timelike for NaiveDateTime {
    /// Returns the hour number from 0 to 23.
    ///
    /// See also the [`NaiveTime::hour`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.hour(), 12);
    /// ```
    #[inline]
    fn hour(&self) -> u32 {
        self.time.hour()
    }

    /// Returns the minute number from 0 to 59.
    ///
    /// See also the [`NaiveTime::minute`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.minute(), 34);
    /// ```
    #[inline]
    fn minute(&self) -> u32 {
        self.time.minute()
    }

    /// Returns the second number from 0 to 59.
    ///
    /// See also the [`NaiveTime::second`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.second(), 56);
    /// ```
    #[inline]
    fn second(&self) -> u32 {
        self.time.second()
    }

    /// Returns the number of nanoseconds since the whole non-leap second.
    /// The range from 1,000,000,000 to 1,999,999,999 represents
    /// the [leap second](./struct.NaiveTime.html#leap-second-handling).
    ///
    /// See also the [`NaiveTime::nanosecond`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.nanosecond(), 789_000_000);
    /// ```
    #[inline]
    fn nanosecond(&self) -> u32 {
        self.time.nanosecond()
    }

    /// Makes a new `NaiveDateTime` with the hour number changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the [`NaiveTime::with_hour`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.with_hour(7),
    ///            Some(NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(7, 34, 56, 789).unwrap()));
    /// assert_eq!(dt.with_hour(24), None);
    /// ```
    #[inline]
    fn with_hour(&self, hour: u32) -> Option<NaiveDateTime> {
        self.time.with_hour(hour).map(|t| NaiveDateTime { time: t, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the minute number changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    ///
    /// See also the
    /// [`NaiveTime::with_minute`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.with_minute(45),
    ///            Some(NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 45, 56, 789).unwrap()));
    /// assert_eq!(dt.with_minute(60), None);
    /// ```
    #[inline]
    fn with_minute(&self, min: u32) -> Option<NaiveDateTime> {
        self.time.with_minute(min).map(|t| NaiveDateTime { time: t, ..*self })
    }

    /// Makes a new `NaiveDateTime` with the second number changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid. As
    /// with the [`NaiveDateTime::second`] method, the input range is
    /// restricted to 0 through 59.
    ///
    /// See also the [`NaiveTime::with_second`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.with_second(17),
    ///            Some(NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 17, 789).unwrap()));
    /// assert_eq!(dt.with_second(60), None);
    /// ```
    #[inline]
    fn with_second(&self, sec: u32) -> Option<NaiveDateTime> {
        self.time.with_second(sec).map(|t| NaiveDateTime { time: t, ..*self })
    }

    /// Makes a new `NaiveDateTime` with nanoseconds since the whole non-leap second changed.
    ///
    /// Returns `None` when the resulting `NaiveDateTime` would be invalid.
    /// As with the [`NaiveDateTime::nanosecond`] method,
    /// the input range can exceed 1,000,000,000 for leap seconds.
    ///
    /// See also the [`NaiveTime::with_nanosecond`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{NaiveDate, NaiveDateTime, Timelike};
    ///
    /// let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_milli_opt(12, 34, 56, 789).unwrap();
    /// assert_eq!(dt.with_nanosecond(333_333_333),
    ///            Some(NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_nano_opt(12, 34, 56, 333_333_333).unwrap()));
    /// assert_eq!(dt.with_nanosecond(1_333_333_333), // leap second
    ///            Some(NaiveDate::from_ymd_opt(2015, 9, 8).unwrap().and_hms_nano_opt(12, 34, 56, 1_333_333_333).unwrap()));
    /// assert_eq!(dt.with_nanosecond(2_000_000_000), None);
    /// ```
    #[inline]
    fn with_nanosecond(&self, nano: u32) -> Option<NaiveDateTime> {
        self.time.with_nanosecond(nano).map(|t| NaiveDateTime { time: t, ..*self })
    }
}

/// An addition of `Duration` to `NaiveDateTime` yields another `NaiveDateTime`.
///
/// As a part of Chrono's [leap second handling], the addition assumes that **there is no leap
/// second ever**, except when the `NaiveDateTime` itself represents a leap  second in which case
/// the assumption becomes that **there is exactly a single leap second ever**.
///
/// Panics on underflow or overflow. Use [`NaiveDateTime::checked_add_signed`]
/// to detect that.
///
/// # Example
///
/// ```
/// use chrono::{Duration, NaiveDate};
///
/// let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
///
/// let d = from_ymd(2016, 7, 8);
/// let hms = |h, m, s| d.and_hms_opt(h, m, s).unwrap();
/// assert_eq!(hms(3, 5, 7) + Duration::zero(),             hms(3, 5, 7));
/// assert_eq!(hms(3, 5, 7) + Duration::seconds(1),         hms(3, 5, 8));
/// assert_eq!(hms(3, 5, 7) + Duration::seconds(-1),        hms(3, 5, 6));
/// assert_eq!(hms(3, 5, 7) + Duration::seconds(3600 + 60), hms(4, 6, 7));
/// assert_eq!(hms(3, 5, 7) + Duration::seconds(86_400),
///            from_ymd(2016, 7, 9).and_hms_opt(3, 5, 7).unwrap());
/// assert_eq!(hms(3, 5, 7) + Duration::days(365),
///            from_ymd(2017, 7, 8).and_hms_opt(3, 5, 7).unwrap());
///
/// let hmsm = |h, m, s, milli| d.and_hms_milli_opt(h, m, s, milli).unwrap();
/// assert_eq!(hmsm(3, 5, 7, 980) + Duration::milliseconds(450), hmsm(3, 5, 8, 430));
/// ```
///
/// Leap seconds are handled,
/// but the addition assumes that it is the only leap second happened.
///
/// ```
/// # use chrono::{Duration, NaiveDate};
/// # let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
/// # let hmsm = |h, m, s, milli| from_ymd(2016, 7, 8).and_hms_milli_opt(h, m, s, milli).unwrap();
/// let leap = hmsm(3, 5, 59, 1_300);
/// assert_eq!(leap + Duration::zero(),             hmsm(3, 5, 59, 1_300));
/// assert_eq!(leap + Duration::milliseconds(-500), hmsm(3, 5, 59, 800));
/// assert_eq!(leap + Duration::milliseconds(500),  hmsm(3, 5, 59, 1_800));
/// assert_eq!(leap + Duration::milliseconds(800),  hmsm(3, 6, 0, 100));
/// assert_eq!(leap + Duration::seconds(10),        hmsm(3, 6, 9, 300));
/// assert_eq!(leap + Duration::seconds(-10),       hmsm(3, 5, 50, 300));
/// assert_eq!(leap + Duration::days(1),
///            from_ymd(2016, 7, 9).and_hms_milli_opt(3, 5, 59, 300).unwrap());
/// ```
///
/// [leap second handling]: crate::NaiveTime#leap-second-handling
impl Add<OldDuration> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn add(self, rhs: OldDuration) -> NaiveDateTime {
        self.checked_add_signed(rhs).expect("`NaiveDateTime + Duration` overflowed")
    }
}

impl AddAssign<OldDuration> for NaiveDateTime {
    #[inline]
    fn add_assign(&mut self, rhs: OldDuration) {
        *self = self.add(rhs);
    }
}

impl Add<Months> for NaiveDateTime {
    type Output = NaiveDateTime;

    /// An addition of months to `NaiveDateTime` clamped to valid days in resulting month.
    ///
    /// # Panics
    ///
    /// Panics if the resulting date would be out of range.
    ///
    /// # Example
    ///
    /// ```
    /// use chrono::{Months, NaiveDate};
    ///
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap() + Months::new(1),
    ///     NaiveDate::from_ymd_opt(2014, 2, 1).unwrap().and_hms_opt(1, 0, 0).unwrap()
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(0, 2, 0).unwrap() + Months::new(11),
    ///     NaiveDate::from_ymd_opt(2014, 12, 1).unwrap().and_hms_opt(0, 2, 0).unwrap()
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(0, 0, 3).unwrap() + Months::new(12),
    ///     NaiveDate::from_ymd_opt(2015, 1, 1).unwrap().and_hms_opt(0, 0, 3).unwrap()
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(0, 0, 4).unwrap() + Months::new(13),
    ///     NaiveDate::from_ymd_opt(2015, 2, 1).unwrap().and_hms_opt(0, 0, 4).unwrap()
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2014, 1, 31).unwrap().and_hms_opt(0, 5, 0).unwrap() + Months::new(1),
    ///     NaiveDate::from_ymd_opt(2014, 2, 28).unwrap().and_hms_opt(0, 5, 0).unwrap()
    /// );
    /// assert_eq!(
    ///     NaiveDate::from_ymd_opt(2020, 1, 31).unwrap().and_hms_opt(6, 0, 0).unwrap() + Months::new(1),
    ///     NaiveDate::from_ymd_opt(2020, 2, 29).unwrap().and_hms_opt(6, 0, 0).unwrap()
    /// );
    /// ```
    fn add(self, rhs: Months) -> Self::Output {
        Self { date: self.date.checked_add_months(rhs).unwrap(), time: self.time }
    }
}

/// A subtraction of `Duration` from `NaiveDateTime` yields another `NaiveDateTime`.
/// It is the same as the addition with a negated `Duration`.
///
/// As a part of Chrono's [leap second handling] the subtraction assumes that **there is no leap
/// second ever**, except when the `NaiveDateTime` itself represents a leap second in which case
/// the assumption becomes that **there is exactly a single leap second ever**.
///
/// Panics on underflow or overflow. Use [`NaiveDateTime::checked_sub_signed`]
/// to detect that.
///
/// # Example
///
/// ```
/// use chrono::{Duration, NaiveDate};
///
/// let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
///
/// let d = from_ymd(2016, 7, 8);
/// let hms = |h, m, s| d.and_hms_opt(h, m, s).unwrap();
/// assert_eq!(hms(3, 5, 7) - Duration::zero(),             hms(3, 5, 7));
/// assert_eq!(hms(3, 5, 7) - Duration::seconds(1),         hms(3, 5, 6));
/// assert_eq!(hms(3, 5, 7) - Duration::seconds(-1),        hms(3, 5, 8));
/// assert_eq!(hms(3, 5, 7) - Duration::seconds(3600 + 60), hms(2, 4, 7));
/// assert_eq!(hms(3, 5, 7) - Duration::seconds(86_400),
///            from_ymd(2016, 7, 7).and_hms_opt(3, 5, 7).unwrap());
/// assert_eq!(hms(3, 5, 7) - Duration::days(365),
///            from_ymd(2015, 7, 9).and_hms_opt(3, 5, 7).unwrap());
///
/// let hmsm = |h, m, s, milli| d.and_hms_milli_opt(h, m, s, milli).unwrap();
/// assert_eq!(hmsm(3, 5, 7, 450) - Duration::milliseconds(670), hmsm(3, 5, 6, 780));
/// ```
///
/// Leap seconds are handled,
/// but the subtraction assumes that it is the only leap second happened.
///
/// ```
/// # use chrono::{Duration, NaiveDate};
/// # let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
/// # let hmsm = |h, m, s, milli| from_ymd(2016, 7, 8).and_hms_milli_opt(h, m, s, milli).unwrap();
/// let leap = hmsm(3, 5, 59, 1_300);
/// assert_eq!(leap - Duration::zero(),            hmsm(3, 5, 59, 1_300));
/// assert_eq!(leap - Duration::milliseconds(200), hmsm(3, 5, 59, 1_100));
/// assert_eq!(leap - Duration::milliseconds(500), hmsm(3, 5, 59, 800));
/// assert_eq!(leap - Duration::seconds(60),       hmsm(3, 5, 0, 300));
/// assert_eq!(leap - Duration::days(1),
///            from_ymd(2016, 7, 7).and_hms_milli_opt(3, 6, 0, 300).unwrap());
/// ```
///
/// [leap second handling]: crate::NaiveTime#leap-second-handling
impl Sub<OldDuration> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn sub(self, rhs: OldDuration) -> NaiveDateTime {
        self.checked_sub_signed(rhs).expect("`NaiveDateTime - Duration` overflowed")
    }
}

impl SubAssign<OldDuration> for NaiveDateTime {
    #[inline]
    fn sub_assign(&mut self, rhs: OldDuration) {
        *self = self.sub(rhs);
    }
}

/// A subtraction of Months from `NaiveDateTime` clamped to valid days in resulting month.
///
/// # Panics
///
/// Panics if the resulting date would be out of range.
///
/// # Example
///
/// ```
/// use chrono::{Months, NaiveDate};
///
/// assert_eq!(
///     NaiveDate::from_ymd_opt(2014, 01, 01).unwrap().and_hms_opt(01, 00, 00).unwrap() - Months::new(11),
///     NaiveDate::from_ymd_opt(2013, 02, 01).unwrap().and_hms_opt(01, 00, 00).unwrap()
/// );
/// assert_eq!(
///     NaiveDate::from_ymd_opt(2014, 01, 01).unwrap().and_hms_opt(00, 02, 00).unwrap() - Months::new(12),
///     NaiveDate::from_ymd_opt(2013, 01, 01).unwrap().and_hms_opt(00, 02, 00).unwrap()
/// );
/// assert_eq!(
///     NaiveDate::from_ymd_opt(2014, 01, 01).unwrap().and_hms_opt(00, 00, 03).unwrap() - Months::new(13),
///     NaiveDate::from_ymd_opt(2012, 12, 01).unwrap().and_hms_opt(00, 00, 03).unwrap()
/// );
/// ```
impl Sub<Months> for NaiveDateTime {
    type Output = NaiveDateTime;

    fn sub(self, rhs: Months) -> Self::Output {
        Self { date: self.date.checked_sub_months(rhs).unwrap(), time: self.time }
    }
}

/// Subtracts another `NaiveDateTime` from the current date and time.
/// This does not overflow or underflow at all.
///
/// As a part of Chrono's [leap second handling](./struct.NaiveTime.html#leap-second-handling),
/// the subtraction assumes that **there is no leap second ever**,
/// except when any of the `NaiveDateTime`s themselves represents a leap second
/// in which case the assumption becomes that
/// **there are exactly one (or two) leap second(s) ever**.
///
/// The implementation is a wrapper around [`NaiveDateTime::signed_duration_since`].
///
/// # Example
///
/// ```
/// use chrono::{Duration, NaiveDate};
///
/// let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
///
/// let d = from_ymd(2016, 7, 8);
/// assert_eq!(d.and_hms_opt(3, 5, 7).unwrap() - d.and_hms_opt(2, 4, 6).unwrap(), Duration::seconds(3600 + 60 + 1));
///
/// // July 8 is 190th day in the year 2016
/// let d0 = from_ymd(2016, 1, 1);
/// assert_eq!(d.and_hms_milli_opt(0, 7, 6, 500).unwrap() - d0.and_hms_opt(0, 0, 0).unwrap(),
///            Duration::seconds(189 * 86_400 + 7 * 60 + 6) + Duration::milliseconds(500));
/// ```
///
/// Leap seconds are handled, but the subtraction assumes that no other leap
/// seconds happened.
///
/// ```
/// # use chrono::{Duration, NaiveDate};
/// # let from_ymd = |y, m, d| NaiveDate::from_ymd_opt(y, m, d).unwrap();
/// let leap = from_ymd(2015, 6, 30).and_hms_milli_opt(23, 59, 59, 1_500).unwrap();
/// assert_eq!(leap - from_ymd(2015, 6, 30).and_hms_opt(23, 0, 0).unwrap(),
///            Duration::seconds(3600) + Duration::milliseconds(500));
/// assert_eq!(from_ymd(2015, 7, 1).and_hms_opt(1, 0, 0).unwrap() - leap,
///            Duration::seconds(3600) - Duration::milliseconds(500));
/// ```
impl Sub<NaiveDateTime> for NaiveDateTime {
    type Output = OldDuration;

    #[inline]
    fn sub(self, rhs: NaiveDateTime) -> OldDuration {
        self.signed_duration_since(rhs)
    }
}

impl Add<Days> for NaiveDateTime {
    type Output = NaiveDateTime;

    fn add(self, days: Days) -> Self::Output {
        self.checked_add_days(days).unwrap()
    }
}

impl Sub<Days> for NaiveDateTime {
    type Output = NaiveDateTime;

    fn sub(self, days: Days) -> Self::Output {
        self.checked_sub_days(days).unwrap()
    }
}

/// The `Debug` output of the naive date and time `dt` is the same as
/// [`dt.format("%Y-%m-%dT%H:%M:%S%.f")`](crate::format::strftime).
///
/// The string printed can be readily parsed via the `parse` method on `str`.
///
/// It should be noted that, for leap seconds not on the minute boundary,
/// it may print a representation not distinguishable from non-leap seconds.
/// This doesn't matter in practice, since such leap seconds never happened.
/// (By the time of the first leap second on 1972-06-30,
/// every time zone offset around the world has standardized to the 5-minute alignment.)
///
/// # Example
///
/// ```
/// use chrono::NaiveDate;
///
/// let dt = NaiveDate::from_ymd_opt(2016, 11, 15).unwrap().and_hms_opt(7, 39, 24).unwrap();
/// assert_eq!(format!("{:?}", dt), "2016-11-15T07:39:24");
/// ```
///
/// Leap seconds may also be used.
///
/// ```
/// # use chrono::NaiveDate;
/// let dt = NaiveDate::from_ymd_opt(2015, 6, 30).unwrap().and_hms_milli_opt(23, 59, 59, 1_500).unwrap();
/// assert_eq!(format!("{:?}", dt), "2015-06-30T23:59:60.500");
/// ```
impl fmt::Debug for NaiveDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.date.fmt(f)?;
        f.write_char('T')?;
        self.time.fmt(f)
    }
}

/// The `Display` output of the naive date and time `dt` is the same as
/// [`dt.format("%Y-%m-%d %H:%M:%S%.f")`](crate::format::strftime).
///
/// It should be noted that, for leap seconds not on the minute boundary,
/// it may print a representation not distinguishable from non-leap seconds.
/// This doesn't matter in practice, since such leap seconds never happened.
/// (By the time of the first leap second on 1972-06-30,
/// every time zone offset around the world has standardized to the 5-minute alignment.)
///
/// # Example
///
/// ```
/// use chrono::NaiveDate;
///
/// let dt = NaiveDate::from_ymd_opt(2016, 11, 15).unwrap().and_hms_opt(7, 39, 24).unwrap();
/// assert_eq!(format!("{}", dt), "2016-11-15 07:39:24");
/// ```
///
/// Leap seconds may also be used.
///
/// ```
/// # use chrono::NaiveDate;
/// let dt = NaiveDate::from_ymd_opt(2015, 6, 30).unwrap().and_hms_milli_opt(23, 59, 59, 1_500).unwrap();
/// assert_eq!(format!("{}", dt), "2015-06-30 23:59:60.500");
/// ```
impl fmt::Display for NaiveDateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.date.fmt(f)?;
        f.write_char(' ')?;
        self.time.fmt(f)
    }
}

/// Parsing a `str` into a `NaiveDateTime` uses the same format,
/// [`%Y-%m-%dT%H:%M:%S%.f`](crate::format::strftime), as in `Debug`.
///
/// # Example
///
/// ```
/// use chrono::{NaiveDateTime, NaiveDate};
///
/// let dt = NaiveDate::from_ymd_opt(2015, 9, 18).unwrap().and_hms_opt(23, 56, 4).unwrap();
/// assert_eq!("2015-09-18T23:56:04".parse::<NaiveDateTime>(), Ok(dt));
///
/// let dt = NaiveDate::from_ymd_opt(12345, 6, 7).unwrap().and_hms_milli_opt(7, 59, 59, 1_500).unwrap(); // leap second
/// assert_eq!("+12345-6-7T7:59:60.5".parse::<NaiveDateTime>(), Ok(dt));
///
/// assert!("foo".parse::<NaiveDateTime>().is_err());
/// ```
impl str::FromStr for NaiveDateTime {
    type Err = ParseError;

    fn from_str(s: &str) -> ParseResult<NaiveDateTime> {
        const ITEMS: &[Item<'static>] = &[
            Item::Numeric(Numeric::Year, Pad::Zero),
            Item::Space(""),
            Item::Literal("-"),
            Item::Numeric(Numeric::Month, Pad::Zero),
            Item::Space(""),
            Item::Literal("-"),
            Item::Numeric(Numeric::Day, Pad::Zero),
            Item::Space(""),
            Item::Literal("T"), // XXX shouldn't this be case-insensitive?
            Item::Numeric(Numeric::Hour, Pad::Zero),
            Item::Space(""),
            Item::Literal(":"),
            Item::Numeric(Numeric::Minute, Pad::Zero),
            Item::Space(""),
            Item::Literal(":"),
            Item::Numeric(Numeric::Second, Pad::Zero),
            Item::Fixed(Fixed::Nanosecond),
            Item::Space(""),
        ];

        let mut parsed = Parsed::new();
        parse(&mut parsed, s, ITEMS.iter())?;
        parsed.to_naive_datetime_with_offset(0)
    }
}

/// The default value for a NaiveDateTime is one with epoch 0
/// that is, 1st of January 1970 at 00:00:00.
///
/// # Example
///
/// ```rust
/// use chrono::NaiveDateTime;
///
/// let default_date = NaiveDateTime::default();
/// assert_eq!(Some(default_date), NaiveDateTime::from_timestamp_opt(0, 0));
/// ```
impl Default for NaiveDateTime {
    fn default() -> Self {
        NaiveDateTime::from_timestamp_opt(0, 0).unwrap()
    }
}

#[cfg(all(test, any(feature = "rustc-serialize", feature = "serde")))]
fn test_encodable_json<F, E>(to_string: F)
where
    F: Fn(&NaiveDateTime) -> Result<String, E>,
    E: ::std::fmt::Debug,
{
    assert_eq!(
        to_string(
            &NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_milli_opt(9, 10, 48, 90).unwrap()
        )
        .ok(),
        Some(r#""2016-07-08T09:10:48.090""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::from_ymd_opt(2014, 7, 24).unwrap().and_hms_opt(12, 34, 6).unwrap())
            .ok(),
        Some(r#""2014-07-24T12:34:06""#.into())
    );
    assert_eq!(
        to_string(
            &NaiveDate::from_ymd_opt(0, 1, 1).unwrap().and_hms_milli_opt(0, 0, 59, 1_000).unwrap()
        )
        .ok(),
        Some(r#""0000-01-01T00:00:60""#.into())
    );
    assert_eq!(
        to_string(
            &NaiveDate::from_ymd_opt(-1, 12, 31).unwrap().and_hms_nano_opt(23, 59, 59, 7).unwrap()
        )
        .ok(),
        Some(r#""-0001-12-31T23:59:59.000000007""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::MIN.and_hms_opt(0, 0, 0).unwrap()).ok(),
        Some(r#""-262144-01-01T00:00:00""#.into())
    );
    assert_eq!(
        to_string(&NaiveDate::MAX.and_hms_nano_opt(23, 59, 59, 1_999_999_999).unwrap()).ok(),
        Some(r#""+262143-12-31T23:59:60.999999999""#.into())
    );
}

#[cfg(all(test, any(feature = "rustc-serialize", feature = "serde")))]
fn test_decodable_json<F, E>(from_str: F)
where
    F: Fn(&str) -> Result<NaiveDateTime, E>,
    E: ::std::fmt::Debug,
{
    assert_eq!(
        from_str(r#""2016-07-08T09:10:48.090""#).ok(),
        Some(
            NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_milli_opt(9, 10, 48, 90).unwrap()
        )
    );
    assert_eq!(
        from_str(r#""2016-7-8T9:10:48.09""#).ok(),
        Some(
            NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_milli_opt(9, 10, 48, 90).unwrap()
        )
    );
    assert_eq!(
        from_str(r#""2014-07-24T12:34:06""#).ok(),
        Some(NaiveDate::from_ymd_opt(2014, 7, 24).unwrap().and_hms_opt(12, 34, 6).unwrap())
    );
    assert_eq!(
        from_str(r#""0000-01-01T00:00:60""#).ok(),
        Some(NaiveDate::from_ymd_opt(0, 1, 1).unwrap().and_hms_milli_opt(0, 0, 59, 1_000).unwrap())
    );
    assert_eq!(
        from_str(r#""0-1-1T0:0:60""#).ok(),
        Some(NaiveDate::from_ymd_opt(0, 1, 1).unwrap().and_hms_milli_opt(0, 0, 59, 1_000).unwrap())
    );
    assert_eq!(
        from_str(r#""-0001-12-31T23:59:59.000000007""#).ok(),
        Some(NaiveDate::from_ymd_opt(-1, 12, 31).unwrap().and_hms_nano_opt(23, 59, 59, 7).unwrap())
    );
    assert_eq!(
        from_str(r#""-262144-01-01T00:00:00""#).ok(),
        Some(NaiveDate::MIN.and_hms_opt(0, 0, 0).unwrap())
    );
    assert_eq!(
        from_str(r#""+262143-12-31T23:59:60.999999999""#).ok(),
        Some(NaiveDate::MAX.and_hms_nano_opt(23, 59, 59, 1_999_999_999).unwrap())
    );
    assert_eq!(
        from_str(r#""+262143-12-31T23:59:60.9999999999997""#).ok(), // excess digits are ignored
        Some(NaiveDate::MAX.and_hms_nano_opt(23, 59, 59, 1_999_999_999).unwrap())
    );

    // bad formats
    assert!(from_str(r#""""#).is_err());
    assert!(from_str(r#""2016-07-08""#).is_err());
    assert!(from_str(r#""09:10:48.090""#).is_err());
    assert!(from_str(r#""20160708T091048.090""#).is_err());
    assert!(from_str(r#""2000-00-00T00:00:00""#).is_err());
    assert!(from_str(r#""2000-02-30T00:00:00""#).is_err());
    assert!(from_str(r#""2001-02-29T00:00:00""#).is_err());
    assert!(from_str(r#""2002-02-28T24:00:00""#).is_err());
    assert!(from_str(r#""2002-02-28T23:60:00""#).is_err());
    assert!(from_str(r#""2002-02-28T23:59:61""#).is_err());
    assert!(from_str(r#""2016-07-08T09:10:48,090""#).is_err());
    assert!(from_str(r#""2016-07-08 09:10:48.090""#).is_err());
    assert!(from_str(r#""2016-007-08T09:10:48.090""#).is_err());
    assert!(from_str(r#""yyyy-mm-ddThh:mm:ss.fffffffff""#).is_err());
    assert!(from_str(r#"20160708000000"#).is_err());
    assert!(from_str(r#"{}"#).is_err());
    // pre-0.3.0 rustc-serialize format is now invalid
    assert!(from_str(r#"{"date":{"ymdf":20},"time":{"secs":0,"frac":0}}"#).is_err());
    assert!(from_str(r#"null"#).is_err());
}

#[cfg(all(test, feature = "rustc-serialize"))]
fn test_decodable_json_timestamp<F, E>(from_str: F)
where
    F: Fn(&str) -> Result<rustc_serialize::TsSeconds, E>,
    E: ::std::fmt::Debug,
{
    assert_eq!(
        *from_str("0").unwrap(),
        NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap(),
        "should parse integers as timestamps"
    );
    assert_eq!(
        *from_str("-1").unwrap(),
        NaiveDate::from_ymd_opt(1969, 12, 31).unwrap().and_hms_opt(23, 59, 59).unwrap(),
        "should parse integers as timestamps"
    );
}
#[cfg(test)]
mod tests_rug_473 {
    use crate::{NaiveDate, NaiveTime, naive::datetime::NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDate = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap();
        let p1: NaiveTime = NaiveTime::from_hms_nano(12, 34, 56, 789_012_345);

        let _dt = NaiveDateTime::new(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_474 {
    use super::*;
    use crate::naive::NaiveDateTime;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1_609_459_200; // Sample timestamp for January 1, 2021
        let mut p1: u32 = 123_456_789;   // Sample nanoseconds

        NaiveDateTime::from_timestamp(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_475 {
    use super::*;
    use crate::naive::NaiveDateTime;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1662921288000; // Sunday, September 11, 2022 6:34:48 PM

        let naive_datetime = NaiveDateTime::from_timestamp_millis(p0);
        assert!(naive_datetime.is_some());
        assert_eq!(p0, naive_datetime.unwrap().timestamp_millis());

        p0 = -2208936075000; // Mon Jan 01 1900 14:38:45 GMT+0000
        let naive_datetime = NaiveDateTime::from_timestamp_millis(p0);
        assert!(naive_datetime.is_some());
        assert_eq!(p0, naive_datetime.unwrap().timestamp_millis());
    }
}#[cfg(test)]
mod tests_rug_476 {
    use super::*;
    use crate::naive::NaiveDateTime;

    #[test]
    fn test_from_timestamp_micros() {
        let timestamp_micros_positive: i64 = 1662921288000000; // Sunday, September 11, 2022 6:34:48 PM
        let timestamp_micros_negative: i64 = -2208936075000000; // Mon Jan 01 1900 14:38:45 GMT+0000

        let result_positive = NaiveDateTime::from_timestamp_micros(timestamp_micros_positive);
        assert!(result_positive.is_some());
        assert_eq!(timestamp_micros_positive, result_positive.unwrap().timestamp_micros());

        let result_negative = NaiveDateTime::from_timestamp_micros(timestamp_micros_negative);
        assert!(result_negative.is_some());
        assert_eq!(timestamp_micros_negative, result_negative.unwrap().timestamp_micros());
    }
}#[cfg(test)]
mod tests_rug_477 {
    use super::*;
    use crate::NaiveDateTime;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 0;
        let mut p1: u32 = 0;

        NaiveDateTime::from_timestamp_opt(p0, p1);
        assert!(NaiveDateTime::from_timestamp_opt(0, 0).is_some());
        assert!(NaiveDateTime::from_timestamp_opt(0, 999_999_999).is_some());
        assert!(NaiveDateTime::from_timestamp_opt(0, 1_500_000_000).is_some()); // leap second
        assert!(NaiveDateTime::from_timestamp_opt(0, 2_000_000_000).is_none());
        assert!(NaiveDateTime::from_timestamp_opt(i64::MAX, 0).is_none());
    }
}#[cfg(test)]
mod tests_rug_478 {
    use super::*;
    use crate::{NaiveDateTime, NaiveDate};

    #[test]
    fn test_rug() {
        let p0: &str = "2015-09-05 23:56:04";
        let p1: &str = "%Y-%m-%d %H:%M:%S";

        assert_eq!(
            NaiveDateTime::parse_from_str(p0, p1),
            Ok(NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_opt(23, 56, 4).unwrap())
        );

        let p0: &str = "5sep2015pm012345.6789";
        let p1: &str = "%d%b%Y%p%I%M%S%.f";

        assert_eq!(
            NaiveDateTime::parse_from_str(p0, p1),
            Ok(NaiveDate::from_ymd_opt(2015, 9, 5).unwrap().and_hms_micro_opt(13, 23, 45, 678_900).unwrap())
        );

        let p0: &str = "2014-5-17T12:34:56+09:30";
        let p1: &str = "%Y-%m-%dT%H:%M:%S%z";

        assert_eq!(
            NaiveDateTime::parse_from_str(p0, p1),
            Ok(NaiveDate::from_ymd_opt(2014, 5, 17).unwrap().and_hms_opt(12, 34, 56).unwrap())
        );

        let p0: &str = "2015-07-01 08:59:60.123";
        let p1: &str = "%Y-%m-%d %H:%M:%S%.f";

        assert_eq!(
            NaiveDateTime::parse_from_str(p0, p1),
            Ok(NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_milli_opt(8, 59, 59, 1_123).unwrap())
        );

        let p0: &str = "94/9/4 7:15";
        let p1: &str = "%y/%m/%d %H:%M";

        assert_eq!(
            NaiveDateTime::parse_from_str(p0, p1),
            Ok(NaiveDate::from_ymd_opt(1994, 9, 4).unwrap().and_hms_opt(7, 15, 0).unwrap())
        );

        let p0: &str = "04m33s";
        let p1: &str = "%Mm%Ss";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_err());

        let p0: &str = "94/9/4 12";
        let p1: &str = "%y/%m/%d %H";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_err());

        let p0: &str = "94/9/4 17:60";
        let p1: &str = "%y/%m/%d %H:%M";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_err());

        let p0: &str = "94/9/4 24:00:00";
        let p1: &str = "%y/%m/%d %H:%M:%S";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_err());

        let p0: &str = "2001-09-09 01:46:39 = UNIX timestamp 999999999";
        let p1: &str = "%Y-%m-%d %H:%M:%S = UNIX timestamp %s";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_ok());

        let p0: &str = "1970-01-01 00:00:00 = UNIX timestamp 1";
        let p1: &str = "%Y-%m-%d %H:%M:%S = UNIX timestamp %s";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_err());

        let p0: &str = "10000-09-09 01:46:39";
        let p1: &str = "%Y-%m-%d %H:%M:%S";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_err());

        let p0: &str = "+10000-09-09 01:46:39";
        let p1: &str = "%Y-%m-%d %H:%M:%S";

        assert!(NaiveDateTime::parse_from_str(p0, p1).is_ok());
    }
}#[cfg(test)]
mod tests_rug_479 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveDateTime};
    
    #[test]
    fn test_rug() {
        let p0: &str = "2015-02-18 23:16:09 trailing text";
        let p1: &str = "%Y-%m-%d %H:%M:%S";

        let result = <NaiveDateTime>::parse_and_remainder(p0, p1);
        assert!(result.is_ok());

        let (datetime, remainder) = result.unwrap();
        assert_eq!(
            datetime,
            NaiveDate::from_ymd_opt(2015, 2, 18).unwrap().and_hms_opt(23, 16, 9).unwrap()
        );
        assert_eq!(remainder, " trailing text");
    }
}#[cfg(test)]
mod tests_rug_480 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.date(), NaiveDate::from_ymd_opt(2023, 10, 5).unwrap());
    }
}#[cfg(test)]
mod tests_rug_481 {
    use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.time(), NaiveTime::from_hms_opt(14, 30, 0).unwrap());
    }
}#[cfg(test)]
mod tests_rug_482 {
    use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        p0.timestamp();
    }
}#[cfg(test)]
mod tests_rug_483 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let dt1: NaiveDateTime = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_milli_opt(0, 0, 1, 444).unwrap();
        let dt2: NaiveDateTime = NaiveDate::from_ymd_opt(2001, 9, 9).unwrap().and_hms_milli_opt(1, 46, 40, 555).unwrap();
        let dt3: NaiveDateTime = NaiveDate::from_ymd_opt(1969, 12, 31).unwrap().and_hms_milli_opt(23, 59, 59, 100).unwrap();
        let dt4: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(dt1.timestamp_millis(), 1_444);
        assert_eq!(dt2.timestamp_millis(), 1_000_000_000_555);
        assert_eq!(dt3.timestamp_millis(), -900);
        // Additional test case
        assert_eq!(dt4.timestamp_millis(), 1701801000000);
    }
}#[cfg(test)]
mod tests_rug_484 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_micro_opt(14, 30, 0, 0).unwrap();

        assert_eq!(p0.timestamp_micros(), 1701805800000000);
    }
}#[cfg(test)]
mod tests_rug_485 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_nano_opt(14, 30, 0, 123456789).unwrap();

        p0.timestamp_nanos();
    }
}#[cfg(test)]
mod tests_rug_486 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let dt1: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_nano_opt(9, 10, 11, 123_456_789).unwrap();
        let dt2: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_nano_opt(8, 59, 59, 1_234_567_890).unwrap();
        let dt3: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(dt1.timestamp_subsec_millis(), 123);
        assert_eq!(dt2.timestamp_subsec_millis(), 1_234);
        assert_eq!(dt3.timestamp_subsec_millis(), 0);
    }
}#[cfg(test)]
mod tests_rug_487 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.timestamp_subsec_micros(), 0);

        let p1: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_nano_opt(9, 10, 11, 123_456_789).unwrap();
        assert_eq!(p1.timestamp_subsec_micros(), 123_456);

        let p2: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_nano_opt(8, 59, 59, 1_234_567_890).unwrap();
        assert_eq!(p2.timestamp_subsec_micros(), 1_234_567);
    }
}#[cfg(test)]
mod tests_rug_488 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_nano_opt(9, 10, 11, 123_456_789).unwrap();

        assert_eq!(p0.timestamp_subsec_nanos(), 123_456_789);

        let p1: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 7, 1).unwrap().and_hms_nano_opt(8, 59, 59, 1_234_567_890).unwrap();

        assert_eq!(p1.timestamp_subsec_nanos(), 1_234_567_890);

        let p2: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p2.timestamp_subsec_nanos(), 0);
    }
}#[cfg(test)]
mod tests_rug_489 {
    use crate::{naive::{NaiveDate, NaiveDateTime}, Duration as OldDuration};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: OldDuration = OldDuration::seconds(60); // Example duration

        assert_eq!(p0.checked_add_signed(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 31, 0).unwrap()));
    }

    #[test]
    fn test_with_zero_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 7).unwrap();
        let p1: OldDuration = OldDuration::zero();

        assert_eq!(p0.checked_add_signed(p1), Some(NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 7).unwrap()));
    }

    #[test]
    fn test_with_positive_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 7).unwrap();
        let p1: OldDuration = OldDuration::seconds(1);

        assert_eq!(p0.checked_add_signed(p1), Some(NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 8).unwrap()));
    }

    #[test]
    fn test_with_negative_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 7).unwrap();
        let p1: OldDuration = OldDuration::seconds(-1);

        assert_eq!(p0.checked_add_signed(p1), Some(NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 6).unwrap()));
    }

    #[test]
    fn test_with_large_positive_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 7).unwrap();
        let p1: OldDuration = OldDuration::days(1);

        assert_eq!(p0.checked_add_signed(p1), Some(NaiveDate::from_ymd_opt(2016, 7, 9).unwrap().and_hms_opt(3, 5, 7).unwrap()));
    }

    #[test]
    fn test_with_large_negative_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 7).unwrap();
        let p1: OldDuration = OldDuration::days(-1);

        assert_eq!(p0.checked_add_signed(p1), Some(NaiveDate::from_ymd_opt(2016, 7, 7).unwrap().and_hms_opt(3, 5, 7).unwrap()));
    }

    #[test]
    fn test_with_overflow() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_opt(3, 5, 7).unwrap();
        let p1: OldDuration = OldDuration::days(1_000_000_000);

        assert_eq!(p0.checked_add_signed(p1), None);
    }

    #[test]
    fn test_with_leap_second() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_milli_opt(3, 5, 59, 1_300).unwrap();
        let p1: OldDuration = OldDuration::milliseconds(500);

        assert_eq!(p0.checked_add_signed(p1), Some(NaiveDate::from_ymd_opt(2016, 7, 8).unwrap().and_hms_milli_opt(3, 5, 59, 1_800).unwrap()));
    }
}#[cfg(test)]
mod tests_rug_490 {
    use crate::{naive::{NaiveDate, NaiveTime}, naive::datetime::NaiveDateTime, Duration, Months};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Months = Months::new(5);

        assert_eq!(
            p0.checked_add_months(p1),
            Some(NaiveDate::from_ymd_opt(2024, 3, 5).unwrap().and_hms_opt(14, 30, 0).unwrap())
        );

        let p2: NaiveDateTime = NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap();
        let p3: Months = Months::new(core::i32::MAX as u32 + 1);

        assert_eq!(
            p2.checked_add_months(p3),
            None
        );
    }
}#[cfg(test)]
mod tests_rug_491 {
    use crate::{naive::NaiveDate, naive::NaiveDateTime, Duration};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Duration = Duration::seconds(60);

        assert_eq!(p0.checked_sub_signed(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 29, 0).unwrap()));
    }

    #[test]
    fn test_rug_zero_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Duration = Duration::zero();

        assert_eq!(p0.checked_sub_signed(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));
    }

    #[test]
    fn test_rug_negative_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Duration = Duration::seconds(-60);

        assert_eq!(p0.checked_sub_signed(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 31, 0).unwrap()));
    }

    #[test]
    fn test_rug_large_duration() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Duration = Duration::days(1);

        assert_eq!(p0.checked_sub_signed(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 4).unwrap().and_hms_opt(14, 30, 0).unwrap()));
    }

    #[test]
    fn test_rug_overflow() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Duration = Duration::days(1_000_000_000);

        assert_eq!(p0.checked_sub_signed(p1), None);
    }
}#[cfg(test)]
mod tests_rug_492 {
    use crate::{naive::{NaiveDate, NaiveTime}, Months, naive::datetime::NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Months = Months::new(5);

        assert_eq!(
            p0.checked_sub_months(p1),
            Some(NaiveDate::from_ymd_opt(2023, 5, 5).unwrap().and_hms_opt(14, 30, 0).unwrap())
        );

        let p2: NaiveDateTime = NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap();
        let p3: Months = Months::new(core::i32::MAX as u32 + 1);

        assert_eq!(
            p2.checked_sub_months(p3),
            None
        );
    }
}#[cfg(test)]
mod tests_rug_493 {
    use super::*;
    use crate::{naive::{NaiveDate, NaiveTime}, Days};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Days = Days::new(10);

        assert!(p0.checked_add_days(p1).is_some());
    }
}#[cfg(test)]
mod tests_rug_494 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveTime};
    use crate::Days;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Days = Days::new(10);

        <NaiveDateTime>::checked_sub_days(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_495 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(12, 15, 0).unwrap();

        let duration = p0.signed_duration_since(p1);
        assert_eq!(duration.num_seconds(), 7500);
    }
}#[cfg(test)]
mod tests_rug_496 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveTime};
    use crate::format::strftime::StrftimeItems;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: StrftimeItems<'_> = StrftimeItems::new("%Y-%m-%d %H:%M:%S");

        <NaiveDateTime>::format_with_items(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_497 {
    use crate::naive::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: &str = "%Y-%m-%d %H:%M:%S";

        <NaiveDateTime>::format(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_499 {
    use crate::{NaiveDate, NaiveTime, naive::datetime::NaiveDateTime, DateTime, Utc};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        let dt = p0.and_utc();
        assert_eq!(dt.timezone(), Utc);
    }
}#[cfg(test)]
mod tests_rug_500 {
    use crate::Datelike;
    use crate::naive::{NaiveDate, NaiveTime};
    use crate::naive::NaiveDateTime;

    #[test]
    fn test_rug() {
        let v20: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(v20.year(), 2023);
    }
}#[cfg(test)]
mod tests_rug_501 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, NaiveDateTime};

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(<NaiveDateTime as Datelike>::month(&p0), 10);
    }
}#[cfg(test)]
mod tests_rug_502 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, naive::datetime::NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.month0(), 9);
    }
}#[cfg(test)]
mod tests_rug_503 {
    use crate::{naive::{NaiveDate, NaiveDateTime}, Datelike};

    #[test]
    fn test_day() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        
        assert_eq!(p0.day(), 5);
    }
}#[cfg(test)]
mod tests_rug_504 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, naive::NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.day0(), 4);
    }
}#[cfg(test)]
mod tests_rug_505 {
    use super::*;
    use crate::Datelike;
    use crate::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_ordinal() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.ordinal(), 278);
    }
}#[cfg(test)]
mod tests_rug_506 {
    use crate::{Datelike, naive::{NaiveDate, NaiveDateTime, NaiveTime}};

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.ordinal0(), 278);
    }
}#[cfg(test)]
mod tests_rug_507 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, Weekday};

    #[test]
    fn test_weekday() {
        let dt: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(dt.weekday(), Weekday::Thu);
    }
}#[cfg(test)]
mod tests_rug_508 {
    use super::*;
    use crate::Datelike;
    use crate::naive::{NaiveDate, NaiveTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        <NaiveDateTime as Datelike>::iso_week(&p0);
    }
}#[cfg(test)]
mod tests_rug_509 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, naive::datetime::NaiveDateTime};

    #[test]
    fn test_with_year() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: i32 = 2024;

        assert_eq!(p0.with_year(p1), Some(NaiveDate::from_ymd_opt(2024, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p1: i32 = -308;
        assert_eq!(p0.with_year(p1), Some(NaiveDate::from_ymd_opt(-308, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p1: i32 = 2023; // No change
        assert_eq!(p0.with_year(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p1: i32 = 2028; // Leap year check
        assert_eq!(p0.with_year(p1), Some(NaiveDate::from_ymd_opt(2028, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p1: i32 = 9999; // Edge case
        assert_eq!(p0.with_year(p1), Some(NaiveDate::from_ymd_opt(9999, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p1: i32 = -9999; // Edge case
        assert_eq!(p0.with_year(p1), Some(NaiveDate::from_ymd_opt(-9999, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2024, 2, 29).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: i32 = 2023; // Invalid date in non-leap year
        assert_eq!(p0.with_year(p1), None);
    }
}#[cfg(test)]
mod tests_rug_510 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, naive::datetime::NaiveDateTime};

    #[test]
    fn test_with_month() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2015, 9, 30).unwrap().and_hms_opt(12, 34, 56).unwrap();
        let p1: u32 = 10;

        assert_eq!(p0.with_month(p1), Some(NaiveDate::from_ymd_opt(2015, 10, 30).unwrap().and_hms_opt(12, 34, 56).unwrap()));
        
        let p1_invalid: u32 = 13;
        assert_eq!(p0.with_month(p1_invalid), None);
        
        let p1_february_30: u32 = 2;
        assert_eq!(p0.with_month(p1_february_30), None);
    }
}#[cfg(test)]
mod tests_rug_511 {
    use super::*;
    use crate::Datelike;
    use crate::naive::{NaiveDate, NaiveTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 9;

        assert_eq!(p0.with_month0(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p1: u32 = 12;
        assert_eq!(p0.with_month0(p1), None);

        let p1: u32 = 1;
        assert_eq!(p0.with_month0(p1), None);
    }
}#[cfg(test)]
mod tests_rug_512 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, naive::datetime::NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 15;

        assert_eq!(p0.with_day(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 15).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        let p1_invalid: u32 = 32;
        assert_eq!(p0.with_day(p1_invalid), None);
    }
}#[cfg(test)]
mod tests_rug_513 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, naive::datetime::NaiveDateTime};

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let mut p1: u32 = 29;

        assert_eq!(p0.with_day0(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 30).unwrap().and_hms_opt(14, 30, 0).unwrap()));

        p1 = 30;
        assert_eq!(p0.with_day0(p1), None); // no October 31
    }
}#[cfg(test)]
mod tests_rug_514 {
    use super::*;
    use crate::Datelike;
    use crate::{naive::{NaiveDate, NaiveTime}, naive::datetime::NaiveDateTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 60;

        assert_eq!(p0.with_ordinal(p1),
                   Some(NaiveDate::from_ymd_opt(2023, 3, 1).unwrap().and_hms_opt(14, 30, 0).unwrap()));
        
        let p1_invalid: u32 = 367;
        assert_eq!(p0.with_ordinal(p1_invalid), None);
    }
}#[cfg(test)]
mod tests_rug_515 {
    use super::*;
    use crate::Datelike;
    use crate::{NaiveDate, NaiveTime};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 300;

        assert_eq!(p0.with_ordinal0(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 28).unwrap().and_hms_opt(14, 30, 0).unwrap()));
    }
}#[cfg(test)]
mod tests_rug_516 {
    use super::*;
    use crate::Timelike;
    use crate::{naive::{NaiveDate, NaiveDateTime}};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.hour(), 14);
    }
}#[cfg(test)]
mod tests_rug_517 {
    use super::*;
    use crate::Timelike;
    use crate::{NaiveDate, naive::NaiveDateTime};

    #[test]
    fn test_minute() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.minute(), 30);
    }
}#[cfg(test)]
mod tests_rug_518 {
    use crate::{naive::{NaiveDate, NaiveDateTime}, Timelike};

    #[test]
    fn test_second() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.second(), 0);
    }
}#[cfg(test)]
mod tests_rug_519 {
    use super::*;
    use crate::Timelike;
    use crate::{NaiveDate, NaiveDateTime};

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        assert_eq!(p0.nanosecond(), 0);
    }
}#[cfg(test)]
mod tests_rug_520 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveDateTime};
    use crate::Timelike;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 7;

        assert_eq!(p0.with_hour(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(7, 30, 0).unwrap()));

        let p1_invalid: u32 = 24;
        assert_eq!(p0.with_hour(p1_invalid), None);
    }
}#[cfg(test)]
mod tests_rug_521 {
    use super::*;
    use crate::{NaiveDate, NaiveDateTime, Timelike};

    #[test]
    fn test_with_minute() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 45;

        assert_eq!(p0.with_minute(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 45, 0).unwrap()));

        let p1_invalid: u32 = 60;
        assert_eq!(p0.with_minute(p1_invalid), None);
    }
}#[cfg(test)]
mod tests_rug_522 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveDateTime};
    use crate::Timelike;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 17;

        assert_eq!(p0.with_second(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_milli_opt(14, 30, 17, 0).unwrap()));

        let p1_invalid: u32 = 60;

        assert_eq!(p0.with_second(p1_invalid), None);
    }
}#[cfg(test)]
mod tests_rug_523 {
    use super::*;
    use crate::Timelike;
    use crate::{naive::{NaiveDate, NaiveDateTime}};

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: u32 = 333_333_333;

        assert_eq!(p0.with_nanosecond(p1), Some(NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_nano_opt(14, 30, 0, 333_333_333).unwrap()));
    }
}#[cfg(test)]
mod tests_rug_524 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveTime};
    use crate::oldtime::Duration;
    use std::ops::Add;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let start_time = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(12, 0, 0).unwrap();
        let end_time = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(16, 0, 0).unwrap();
        let p1: Duration = end_time.signed_duration_since(start_time);

        p0.add(p1);
    }
}#[cfg(test)]
mod tests_rug_525 {
    use super::*;
    use crate::{naive::{NaiveDate, NaiveTime}, Duration};
    use std::ops::AddAssign;

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Duration = Duration::hours(5);

        <NaiveDateTime as AddAssign<Duration>>::add_assign(&mut p0, p1);
    }
}#[cfg(test)]
mod tests_rug_526 {
    use crate::{naive::{NaiveDate, NaiveDateTime, NaiveTime}, Duration, Months};
    use std::ops::Add;

    #[test]
    fn test_add() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(1, 0, 0).unwrap();
        let p1: Months = Months::new(1);

        let result = <NaiveDateTime as Add<Months>>::add(p0, p1);
        assert_eq!(result, NaiveDate::from_ymd_opt(2014, 2, 1).unwrap().and_hms_opt(1, 0, 0).unwrap());

        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(0, 2, 0).unwrap();
        let p1: Months = Months::new(11);

        let result = <NaiveDateTime as Add<Months>>::add(p0, p1);
        assert_eq!(result, NaiveDate::from_ymd_opt(2014, 12, 1).unwrap().and_hms_opt(0, 2, 0).unwrap());

        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(0, 0, 3).unwrap();
        let p1: Months = Months::new(12);

        let result = <NaiveDateTime as Add<Months>>::add(p0, p1);
        assert_eq!(result, NaiveDate::from_ymd_opt(2015, 1, 1).unwrap().and_hms_opt(0, 0, 3).unwrap());

        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2014, 1, 1).unwrap().and_hms_opt(0, 0, 4).unwrap();
        let p1: Months = Months::new(13);

        let result = <NaiveDateTime as Add<Months>>::add(p0, p1);
        assert_eq!(result, NaiveDate::from_ymd_opt(2015, 2, 1).unwrap().and_hms_opt(0, 0, 4).unwrap());

        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2014, 1, 31).unwrap().and_hms_opt(0, 5, 0).unwrap();
        let p1: Months = Months::new(1);

        let result = <NaiveDateTime as Add<Months>>::add(p0, p1);
        assert_eq!(result, NaiveDate::from_ymd_opt(2014, 2, 28).unwrap().and_hms_opt(0, 5, 0).unwrap());

        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2020, 1, 31).unwrap().and_hms_opt(6, 0, 0).unwrap();
        let p1: Months = Months::new(1);

        let result = <NaiveDateTime as Add<Months>>::add(p0, p1);
        assert_eq!(result, NaiveDate::from_ymd_opt(2020, 2, 29).unwrap().and_hms_opt(6, 0, 0).unwrap());
    }
}#[cfg(test)]
mod tests_rug_527 {
    use super::*;
    use crate::{naive::{NaiveDate, NaiveTime}, Duration as OldDuration};
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: OldDuration = OldDuration::days(5);

        <NaiveDateTime as Sub<OldDuration>>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_528 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveTime};
    use crate::oldtime::Duration;
    use std::ops::SubAssign;

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Duration = Duration::hours(5);

        p0.sub_assign(p1);
    }
}#[cfg(test)]
mod tests_rug_529 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveTime};
    use crate::Months;
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Months = Months::new(5);

        <NaiveDateTime as Sub<Months>>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_530 {
    use super::*;
    use crate::naive::{NaiveDate, NaiveTime};
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let p0 = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1 = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(12, 30, 0).unwrap();

        let _duration = p0.sub(p1);
    }
}#[cfg(test)]
mod tests_rug_531 {
    use super::*;
    use crate::{naive::{NaiveDate, NaiveTime}, Days};
    use std::ops::Add;

    #[test]
    fn test_rug() {
        let p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let p1: Days = Days::new(10);

        p0.add(p1);
    }
}#[cfg(test)]
mod tests_rug_532 {
    use super::*;
    use crate::{naive::{NaiveDate, NaiveTime}, Days};
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let mut p1: Days = Days::new(10);

        <NaiveDateTime as Sub<Days>>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_533 {
    use super::*;
    use crate::{naive::NaiveDateTime};
    use std::str::FromStr;

    #[test]
    fn test_rug() {
        let mut p0: &str = "2023-10-05T14:30:00.123456789";

        <NaiveDateTime as FromStr>::from_str(p0).unwrap();
    }
}#[cfg(test)]
mod tests_rug_534 {
    use super::*;
    use crate::naive::NaiveDateTime;
    use std::default::Default;

    #[test]
    fn test_rug() {
        let default_datetime: NaiveDateTime = <NaiveDateTime>::default();
        
        assert_eq!(default_datetime, NaiveDateTime::from_timestamp_opt(0, 0).unwrap());
    }
}