// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The time zone which has a fixed offset from UTC.

use core::fmt;
use core::ops::{Add, Sub};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::{LocalResult, Offset, TimeZone};
use crate::naive::{NaiveDate, NaiveDateTime, NaiveTime};
use crate::oldtime::Duration as OldDuration;
use crate::DateTime;
use crate::Timelike;

/// The time zone with fixed offset, from UTC-23:59:59 to UTC+23:59:59.
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on a `FixedOffset` struct is the preferred way to construct
/// `DateTime<FixedOffset>` instances. See the [`east_opt`](#method.east_opt) and
/// [`west_opt`](#method.west_opt) methods for examples.
#[derive(PartialEq, Eq, Hash, Copy, Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct FixedOffset {
    local_minus_utc: i32,
}

impl FixedOffset {
    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Panics on the out-of-bound `secs`.
    #[deprecated(since = "0.4.23", note = "use `east_opt()` instead")]
    #[must_use]
    pub fn east(secs: i32) -> FixedOffset {
        FixedOffset::east_opt(secs).expect("FixedOffset::east out of bounds")
    }

    /// Makes a new `FixedOffset` for the Eastern Hemisphere with given timezone difference.
    /// The negative `secs` means the Western Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    ///
    /// # Example
    ///
    #[cfg_attr(not(feature = "std"), doc = "```ignore")]
    #[cfg_attr(feature = "std", doc = "```")]
    /// use chrono::{FixedOffset, TimeZone};
    /// let hour = 3600;
    /// let datetime = FixedOffset::east_opt(5 * hour)
    ///     .unwrap()
    ///     .with_ymd_and_hms(2016, 11, 08, 0, 0, 0)
    ///     .unwrap();
    /// assert_eq!(&datetime.to_rfc3339(), "2016-11-08T00:00:00+05:00")
    /// ```
    #[must_use]
    pub const fn east_opt(secs: i32) -> Option<FixedOffset> {
        if -86_400 < secs && secs < 86_400 {
            Some(FixedOffset { local_minus_utc: secs })
        } else {
            None
        }
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Panics on the out-of-bound `secs`.
    #[deprecated(since = "0.4.23", note = "use `west_opt()` instead")]
    #[must_use]
    pub fn west(secs: i32) -> FixedOffset {
        FixedOffset::west_opt(secs).expect("FixedOffset::west out of bounds")
    }

    /// Makes a new `FixedOffset` for the Western Hemisphere with given timezone difference.
    /// The negative `secs` means the Eastern Hemisphere.
    ///
    /// Returns `None` on the out-of-bound `secs`.
    ///
    /// # Example
    ///
    #[cfg_attr(not(feature = "std"), doc = "```ignore")]
    #[cfg_attr(feature = "std", doc = "```")]
    /// use chrono::{FixedOffset, TimeZone};
    /// let hour = 3600;
    /// let datetime = FixedOffset::west_opt(5 * hour)
    ///     .unwrap()
    ///     .with_ymd_and_hms(2016, 11, 08, 0, 0, 0)
    ///     .unwrap();
    /// assert_eq!(&datetime.to_rfc3339(), "2016-11-08T00:00:00-05:00")
    /// ```
    #[must_use]
    pub const fn west_opt(secs: i32) -> Option<FixedOffset> {
        if -86_400 < secs && secs < 86_400 {
            Some(FixedOffset { local_minus_utc: -secs })
        } else {
            None
        }
    }

    /// Returns the number of seconds to add to convert from UTC to the local time.
    #[inline]
    pub const fn local_minus_utc(&self) -> i32 {
        self.local_minus_utc
    }

    /// Returns the number of seconds to add to convert from the local time to UTC.
    #[inline]
    pub const fn utc_minus_local(&self) -> i32 {
        -self.local_minus_utc
    }
}

impl TimeZone for FixedOffset {
    type Offset = FixedOffset;

    fn from_offset(offset: &FixedOffset) -> FixedOffset {
        *offset
    }

    fn offset_from_local_date(&self, _local: &NaiveDate) -> LocalResult<FixedOffset> {
        LocalResult::Single(*self)
    }
    fn offset_from_local_datetime(&self, _local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        LocalResult::Single(*self)
    }

    fn offset_from_utc_date(&self, _utc: &NaiveDate) -> FixedOffset {
        *self
    }
    fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> FixedOffset {
        *self
    }
}

impl Offset for FixedOffset {
    fn fix(&self) -> FixedOffset {
        *self
    }
}

impl fmt::Debug for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let offset = self.local_minus_utc;
        let (sign, offset) = if offset < 0 { ('-', -offset) } else { ('+', offset) };
        let sec = offset.rem_euclid(60);
        let mins = offset.div_euclid(60);
        let min = mins.rem_euclid(60);
        let hour = mins.div_euclid(60);
        if sec == 0 {
            write!(f, "{}{:02}:{:02}", sign, hour, min)
        } else {
            write!(f, "{}{:02}:{:02}:{:02}", sign, hour, min, sec)
        }
    }
}

impl fmt::Display for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

#[cfg(feature = "arbitrary")]
impl arbitrary::Arbitrary<'_> for FixedOffset {
    fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<FixedOffset> {
        let secs = u.int_in_range(-86_399..=86_399)?;
        let fixed_offset = FixedOffset::east_opt(secs)
            .expect("Could not generate a valid chrono::FixedOffset. It looks like implementation of Arbitrary for FixedOffset is erroneous.");
        Ok(fixed_offset)
    }
}

// addition or subtraction of FixedOffset to/from Timelike values is the same as
// adding or subtracting the offset's local_minus_utc value
// but keep keeps the leap second information.
// this should be implemented more efficiently, but for the time being, this is generic right now.

fn add_with_leapsecond<T>(lhs: &T, rhs: i32) -> T
where
    T: Timelike + Add<OldDuration, Output = T>,
{
    // extract and temporarily remove the fractional part and later recover it
    let nanos = lhs.nanosecond();
    let lhs = lhs.with_nanosecond(0).unwrap();
    (lhs + OldDuration::seconds(i64::from(rhs))).with_nanosecond(nanos).unwrap()
}

impl Add<FixedOffset> for NaiveTime {
    type Output = NaiveTime;

    #[inline]
    fn add(self, rhs: FixedOffset) -> NaiveTime {
        add_with_leapsecond(&self, rhs.local_minus_utc)
    }
}

impl Sub<FixedOffset> for NaiveTime {
    type Output = NaiveTime;

    #[inline]
    fn sub(self, rhs: FixedOffset) -> NaiveTime {
        add_with_leapsecond(&self, -rhs.local_minus_utc)
    }
}

impl Add<FixedOffset> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn add(self, rhs: FixedOffset) -> NaiveDateTime {
        add_with_leapsecond(&self, rhs.local_minus_utc)
    }
}

impl Sub<FixedOffset> for NaiveDateTime {
    type Output = NaiveDateTime;

    #[inline]
    fn sub(self, rhs: FixedOffset) -> NaiveDateTime {
        add_with_leapsecond(&self, -rhs.local_minus_utc)
    }
}

impl<Tz: TimeZone> Add<FixedOffset> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn add(self, rhs: FixedOffset) -> DateTime<Tz> {
        add_with_leapsecond(&self, rhs.local_minus_utc)
    }
}

impl<Tz: TimeZone> Sub<FixedOffset> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    #[inline]
    fn sub(self, rhs: FixedOffset) -> DateTime<Tz> {
        add_with_leapsecond(&self, -rhs.local_minus_utc)
    }
}

#[cfg(test)]
mod tests {
    use super::FixedOffset;
    use crate::offset::TimeZone;

    #[test]
    fn test_date_extreme_offset() {
        // starting from 0.3 we don't have an offset exceeding one day.
        // this makes everything easier!
        assert_eq!(
            format!(
                "{:?}",
                FixedOffset::east_opt(86399)
                    .unwrap()
                    .with_ymd_and_hms(2012, 2, 29, 5, 6, 7)
                    .unwrap()
            ),
            "2012-02-29T05:06:07+23:59:59".to_string()
        );
        assert_eq!(
            format!(
                "{:?}",
                FixedOffset::east_opt(86399)
                    .unwrap()
                    .with_ymd_and_hms(2012, 2, 29, 5, 6, 7)
                    .unwrap()
            ),
            "2012-02-29T05:06:07+23:59:59".to_string()
        );
        assert_eq!(
            format!(
                "{:?}",
                FixedOffset::west_opt(86399)
                    .unwrap()
                    .with_ymd_and_hms(2012, 3, 4, 5, 6, 7)
                    .unwrap()
            ),
            "2012-03-04T05:06:07-23:59:59".to_string()
        );
        assert_eq!(
            format!(
                "{:?}",
                FixedOffset::west_opt(86399)
                    .unwrap()
                    .with_ymd_and_hms(2012, 3, 4, 5, 6, 7)
                    .unwrap()
            ),
            "2012-03-04T05:06:07-23:59:59".to_string()
        );
    }
}
#[cfg(test)]
mod tests_rug_334 {
    use super::*;
    use crate::offset::fixed::FixedOffset;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 3600; // Example value for timezone difference in seconds (e.g., +1 hour)

        FixedOffset::east(p0);
    }
}#[cfg(test)]
mod tests_rug_335 {
    use super::*;
    use crate::{FixedOffset};

    #[test]
    fn test_rug() {
        let hour: i32 = 3600;
        let p0: i32 = 5 * hour;

        assert_eq!(FixedOffset::east_opt(p0).map(|offset| offset.local_minus_utc), Some(18000));
        
        let invalid_hour: i32 = 90000;
        assert_eq!(FixedOffset::east_opt(invalid_hour), None);
    }
}#[cfg(test)]
mod tests_rug_336 {
    use super::*;
    use crate::offset::fixed::FixedOffset;

    #[test]
    fn test_west() {
        let mut p0: i32 = -18000; // Sample data for Western Hemisphere offset (e.g., UTC-5)

        FixedOffset::west(p0);
    }
}#[cfg(test)]
mod tests_rug_337 {
    use super::*;
    use crate::{FixedOffset};

    #[test]
    fn test_rug() {
        let hour: i32 = 3600;
        let p0: i32 = 5 * hour;

        assert_eq!(FixedOffset::west_opt(p0), Some(FixedOffset { local_minus_utc: -18000 }));
        
        // Test out-of-bound values
        let out_of_bound_positive: i32 = 90000;
        let out_of_bound_negative: i32 = -90000;
        
        assert_eq!(FixedOffset::west_opt(out_of_bound_positive), None);
        assert_eq!(FixedOffset::west_opt(out_of_bound_negative), None);
    }
}#[cfg(test)]
mod tests_rug_338 {
    use crate::offset::fixed::FixedOffset;

    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        assert_eq!(p0.local_minus_utc(), 5 * 3600);
    }
}#[cfg(test)]
mod tests_rug_339 {
    use crate::FixedOffset;

    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        assert_eq!(p0.utc_minus_local(), -5 * 3600);
    }
}#[cfg(test)]
mod tests_rug_340 {
    use super::*;
    use crate::offset::fixed::FixedOffset;
    use crate::TimeZone;

    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        <FixedOffset>::from_offset(&p0);
    }
}#[cfg(test)]
mod tests_rug_342 {
    use super::*;
    use crate::TimeZone;
    use crate::{FixedOffset, naive::{NaiveDate, NaiveTime}};

    #[test]
    fn test_rug() {
        let mut p0 = FixedOffset::east_opt(5 * 3600).unwrap();
        let mut p1 = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        <FixedOffset as TimeZone>::offset_from_local_datetime(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_343 {
    use super::*;
    use crate::TimeZone;
    use crate::{FixedOffset, NaiveDate};

    #[test]
    fn test_rug() {
        let p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();
        let p1: NaiveDate = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap();

        p0.offset_from_utc_date(&p1);
    }
}#[cfg(test)]
mod tests_rug_344 {
    use super::*;
    use crate::TimeZone;
    use crate::{FixedOffset, naive::{NaiveDate, NaiveTime}, DateTime};

    #[test]
    fn test_rug() {
        let mut p0 = FixedOffset::east_opt(5 * 3600).unwrap();
        let mut p1 = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        <FixedOffset as TimeZone>::offset_from_utc_datetime(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_345 {
    use super::*;
    use crate::offset::{self, Offset};
    use crate::FixedOffset;

    #[test]
    fn test_rug() {
        let mut p0: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        <offset::fixed::FixedOffset as offset::Offset>::fix(&p0);
    }
}#[cfg(test)]
mod tests_rug_346 {
    use super::*;
    use crate::{NaiveTime, FixedOffset};
    use std::ops::Add;

    #[test]
    fn test_rug() {
        let p0: NaiveTime = NaiveTime::from_hms_nano(12, 34, 56, 789_012_345);
        let p1: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        p0.add(p1);
    }
}#[cfg(test)]
mod tests_rug_347 {
    use super::*;
    use crate::{NaiveTime, offset::FixedOffset};
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let p0: NaiveTime = NaiveTime::from_hms_nano(12, 34, 56, 789_012_345);
        let p1: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        <NaiveTime>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_348 {
    use super::*;
    use crate::{naive::{NaiveDate, NaiveTime}, offset::FixedOffset};
    use std::ops::Add;

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let mut p1: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        <NaiveDateTime>::add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_349 {
    use super::*;
    use crate::{naive::{NaiveDate, NaiveTime}, offset::fixed::FixedOffset};
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let mut p0: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();
        let mut p1: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        <NaiveDateTime as Sub<FixedOffset>>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_350 {
    use super::*;
    use crate::{Local, DateTime, offset::fixed::FixedOffset};
    use std::ops::Add;

    #[test]
    fn test_rug() {
        let p0: DateTime<Local> = Local::now();
        let p1: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        p0.add(p1);
    }
}#[cfg(test)]
mod tests_rug_351 {
    use super::*;
    use crate::{Local, DateTime, offset::fixed::FixedOffset};
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let p0: DateTime<Local> = Local::now();
        let p1: FixedOffset = FixedOffset::east_opt(5 * 3600).unwrap();

        <DateTime<Local>>::sub(p0, p1);
    }
}