// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! ISO 8601 calendar date with time zone.
#![allow(deprecated)]

#[cfg(any(feature = "alloc", feature = "std", test))]
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::{fmt, hash};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

#[cfg(feature = "unstable-locales")]
use crate::format::Locale;
#[cfg(any(feature = "alloc", feature = "std", test))]
use crate::format::{DelayedFormat, Item, StrftimeItems};
use crate::naive::{IsoWeek, NaiveDate, NaiveTime};
use crate::offset::{TimeZone, Utc};
use crate::oldtime::Duration as OldDuration;
use crate::DateTime;
use crate::{Datelike, Weekday};

/// ISO 8601 calendar date with time zone.
///
/// You almost certainly want to be using a [`NaiveDate`] instead of this type.
///
/// This type primarily exists to aid in the construction of DateTimes that
/// have a timezone by way of the [`TimeZone`] datelike constructors (e.g.
/// [`TimeZone::ymd`]).
///
/// This type should be considered ambiguous at best, due to the inherent lack
/// of precision required for the time zone resolution.
///
/// There are some guarantees on the usage of `Date<Tz>`:
///
/// - If properly constructed via [`TimeZone::ymd`] and others without an error,
///   the corresponding local date should exist for at least a moment.
///   (It may still have a gap from the offset changes.)
///
/// - The `TimeZone` is free to assign *any* [`Offset`](crate::offset::Offset) to the
///   local date, as long as that offset did occur in given day.
///
///   For example, if `2015-03-08T01:59-08:00` is followed by `2015-03-08T03:00-07:00`,
///   it may produce either `2015-03-08-08:00` or `2015-03-08-07:00`
///   but *not* `2015-03-08+00:00` and others.
///
/// - Once constructed as a full `DateTime`, [`DateTime::date`] and other associated
///   methods should return those for the original `Date`. For example, if `dt =
///   tz.ymd_opt(y,m,d).unwrap().hms(h,n,s)` were valid, `dt.date() == tz.ymd_opt(y,m,d).unwrap()`.
///
/// - The date is timezone-agnostic up to one day (i.e. practically always),
///   so the local date and UTC date should be equal for most cases
///   even though the raw calculation between `NaiveDate` and `Duration` may not.
#[deprecated(since = "0.4.23", note = "Use `NaiveDate` or `DateTime<Tz>` instead")]
#[derive(Clone)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
pub struct Date<Tz: TimeZone> {
    date: NaiveDate,
    offset: Tz::Offset,
}

/// The minimum possible `Date`.
#[allow(deprecated)]
#[deprecated(since = "0.4.20", note = "Use Date::MIN_UTC instead")]
pub const MIN_DATE: Date<Utc> = Date::<Utc>::MIN_UTC;
/// The maximum possible `Date`.
#[allow(deprecated)]
#[deprecated(since = "0.4.20", note = "Use Date::MAX_UTC instead")]
pub const MAX_DATE: Date<Utc> = Date::<Utc>::MAX_UTC;

impl<Tz: TimeZone> Date<Tz> {
    /// Makes a new `Date` with given *UTC* date and offset.
    /// The local date should be constructed via the `TimeZone` trait.
    //
    // note: this constructor is purposely not named to `new` to discourage the direct usage.
    #[inline]
    #[must_use]
    pub fn from_utc(date: NaiveDate, offset: Tz::Offset) -> Date<Tz> {
        Date { date, offset }
    }

    /// Makes a new `DateTime` from the current date and given `NaiveTime`.
    /// The offset in the current date is preserved.
    ///
    /// Panics on invalid datetime.
    #[inline]
    #[must_use]
    pub fn and_time(&self, time: NaiveTime) -> Option<DateTime<Tz>> {
        let localdt = self.naive_local().and_time(time);
        self.timezone().from_local_datetime(&localdt).single()
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Panics on invalid hour, minute and/or second.
    #[deprecated(since = "0.4.23", note = "Use and_hms_opt() instead")]
    #[inline]
    #[must_use]
    pub fn and_hms(&self, hour: u32, min: u32, sec: u32) -> DateTime<Tz> {
        self.and_hms_opt(hour, min, sec).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute and second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    #[inline]
    #[must_use]
    pub fn and_hms_opt(&self, hour: u32, min: u32, sec: u32) -> Option<DateTime<Tz>> {
        NaiveTime::from_hms_opt(hour, min, sec).and_then(|time| self.and_time(time))
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Panics on invalid hour, minute, second and/or millisecond.
    #[deprecated(since = "0.4.23", note = "Use and_hms_milli_opt() instead")]
    #[inline]
    #[must_use]
    pub fn and_hms_milli(&self, hour: u32, min: u32, sec: u32, milli: u32) -> DateTime<Tz> {
        self.and_hms_milli_opt(hour, min, sec, milli).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    #[inline]
    #[must_use]
    pub fn and_hms_milli_opt(
        &self,
        hour: u32,
        min: u32,
        sec: u32,
        milli: u32,
    ) -> Option<DateTime<Tz>> {
        NaiveTime::from_hms_milli_opt(hour, min, sec, milli).and_then(|time| self.and_time(time))
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Panics on invalid hour, minute, second and/or microsecond.
    #[deprecated(since = "0.4.23", note = "Use and_hms_micro_opt() instead")]
    #[inline]
    #[must_use]
    pub fn and_hms_micro(&self, hour: u32, min: u32, sec: u32, micro: u32) -> DateTime<Tz> {
        self.and_hms_micro_opt(hour, min, sec, micro).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    #[inline]
    #[must_use]
    pub fn and_hms_micro_opt(
        &self,
        hour: u32,
        min: u32,
        sec: u32,
        micro: u32,
    ) -> Option<DateTime<Tz>> {
        NaiveTime::from_hms_micro_opt(hour, min, sec, micro).and_then(|time| self.and_time(time))
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Panics on invalid hour, minute, second and/or nanosecond.
    #[deprecated(since = "0.4.23", note = "Use and_hms_nano_opt() instead")]
    #[inline]
    #[must_use]
    pub fn and_hms_nano(&self, hour: u32, min: u32, sec: u32, nano: u32) -> DateTime<Tz> {
        self.and_hms_nano_opt(hour, min, sec, nano).expect("invalid time")
    }

    /// Makes a new `DateTime` from the current date, hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    /// The offset in the current date is preserved.
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    #[inline]
    #[must_use]
    pub fn and_hms_nano_opt(
        &self,
        hour: u32,
        min: u32,
        sec: u32,
        nano: u32,
    ) -> Option<DateTime<Tz>> {
        NaiveTime::from_hms_nano_opt(hour, min, sec, nano).and_then(|time| self.and_time(time))
    }

    /// Makes a new `Date` for the next date.
    ///
    /// Panics when `self` is the last representable date.
    #[deprecated(since = "0.4.23", note = "Use succ_opt() instead")]
    #[inline]
    #[must_use]
    pub fn succ(&self) -> Date<Tz> {
        self.succ_opt().expect("out of bound")
    }

    /// Makes a new `Date` for the next date.
    ///
    /// Returns `None` when `self` is the last representable date.
    #[inline]
    #[must_use]
    pub fn succ_opt(&self) -> Option<Date<Tz>> {
        self.date.succ_opt().map(|date| Date::from_utc(date, self.offset.clone()))
    }

    /// Makes a new `Date` for the prior date.
    ///
    /// Panics when `self` is the first representable date.
    #[deprecated(since = "0.4.23", note = "Use pred_opt() instead")]
    #[inline]
    #[must_use]
    pub fn pred(&self) -> Date<Tz> {
        self.pred_opt().expect("out of bound")
    }

    /// Makes a new `Date` for the prior date.
    ///
    /// Returns `None` when `self` is the first representable date.
    #[inline]
    #[must_use]
    pub fn pred_opt(&self) -> Option<Date<Tz>> {
        self.date.pred_opt().map(|date| Date::from_utc(date, self.offset.clone()))
    }

    /// Retrieves an associated offset from UTC.
    #[inline]
    #[must_use]
    pub fn offset(&self) -> &Tz::Offset {
        &self.offset
    }

    /// Retrieves an associated time zone.
    #[inline]
    #[must_use]
    pub fn timezone(&self) -> Tz {
        TimeZone::from_offset(&self.offset)
    }

    /// Changes the associated time zone.
    /// This does not change the actual `Date` (but will change the string representation).
    #[inline]
    #[must_use]
    pub fn with_timezone<Tz2: TimeZone>(&self, tz: &Tz2) -> Date<Tz2> {
        tz.from_utc_date(&self.date)
    }

    /// Adds given `Duration` to the current date.
    ///
    /// Returns `None` when it will result in overflow.
    #[inline]
    #[must_use]
    pub fn checked_add_signed(self, rhs: OldDuration) -> Option<Date<Tz>> {
        let date = self.date.checked_add_signed(rhs)?;
        Some(Date { date, offset: self.offset })
    }

    /// Subtracts given `Duration` from the current date.
    ///
    /// Returns `None` when it will result in overflow.
    #[inline]
    #[must_use]
    pub fn checked_sub_signed(self, rhs: OldDuration) -> Option<Date<Tz>> {
        let date = self.date.checked_sub_signed(rhs)?;
        Some(Date { date, offset: self.offset })
    }

    /// Subtracts another `Date` from the current date.
    /// Returns a `Duration` of integral numbers.
    ///
    /// This does not overflow or underflow at all,
    /// as all possible output fits in the range of `Duration`.
    #[inline]
    #[must_use]
    pub fn signed_duration_since<Tz2: TimeZone>(self, rhs: Date<Tz2>) -> OldDuration {
        self.date.signed_duration_since(rhs.date)
    }

    /// Returns a view to the naive UTC date.
    #[inline]
    #[must_use]
    pub fn naive_utc(&self) -> NaiveDate {
        self.date
    }

    /// Returns a view to the naive local date.
    ///
    /// This is technically the same as [`naive_utc`](#method.naive_utc)
    /// because the offset is restricted to never exceed one day,
    /// but provided for the consistency.
    #[inline]
    #[must_use]
    pub fn naive_local(&self) -> NaiveDate {
        self.date
    }

    /// Returns the number of whole years from the given `base` until `self`.
    #[must_use]
    pub fn years_since(&self, base: Self) -> Option<u32> {
        self.date.years_since(base.date)
    }

    /// The minimum possible `Date`.
    pub const MIN_UTC: Date<Utc> = Date { date: NaiveDate::MIN, offset: Utc };
    /// The maximum possible `Date`.
    pub const MAX_UTC: Date<Utc> = Date { date: NaiveDate::MAX, offset: Utc };
}

/// Maps the local date to other date with given conversion function.
fn map_local<Tz: TimeZone, F>(d: &Date<Tz>, mut f: F) -> Option<Date<Tz>>
where
    F: FnMut(NaiveDate) -> Option<NaiveDate>,
{
    f(d.naive_local()).and_then(|date| d.timezone().from_local_date(&date).single())
}

impl<Tz: TimeZone> Date<Tz>
where
    Tz::Offset: fmt::Display,
{
    /// Formats the date with the specified formatting items.
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    #[must_use]
    pub fn format_with_items<'a, I, B>(&self, items: I) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        DelayedFormat::new_with_offset(Some(self.naive_local()), None, &self.offset, items)
    }

    /// Formats the date with the specified format string.
    /// See the [`crate::format::strftime`] module
    /// on the supported escape sequences.
    #[cfg(any(feature = "alloc", feature = "std", test))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[inline]
    #[must_use]
    pub fn format<'a>(&self, fmt: &'a str) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_with_items(StrftimeItems::new(fmt))
    }

    /// Formats the date with the specified formatting items and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[inline]
    #[must_use]
    pub fn format_localized_with_items<'a, I, B>(
        &self,
        items: I,
        locale: Locale,
    ) -> DelayedFormat<I>
    where
        I: Iterator<Item = B> + Clone,
        B: Borrow<Item<'a>>,
    {
        DelayedFormat::new_with_offset_and_locale(
            Some(self.naive_local()),
            None,
            &self.offset,
            items,
            locale,
        )
    }

    /// Formats the date with the specified format string and locale.
    /// See the [`crate::format::strftime`] module
    /// on the supported escape sequences.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[inline]
    #[must_use]
    pub fn format_localized<'a>(
        &self,
        fmt: &'a str,
        locale: Locale,
    ) -> DelayedFormat<StrftimeItems<'a>> {
        self.format_localized_with_items(StrftimeItems::new_with_locale(fmt, locale), locale)
    }
}

impl<Tz: TimeZone> Datelike for Date<Tz> {
    #[inline]
    fn year(&self) -> i32 {
        self.naive_local().year()
    }
    #[inline]
    fn month(&self) -> u32 {
        self.naive_local().month()
    }
    #[inline]
    fn month0(&self) -> u32 {
        self.naive_local().month0()
    }
    #[inline]
    fn day(&self) -> u32 {
        self.naive_local().day()
    }
    #[inline]
    fn day0(&self) -> u32 {
        self.naive_local().day0()
    }
    #[inline]
    fn ordinal(&self) -> u32 {
        self.naive_local().ordinal()
    }
    #[inline]
    fn ordinal0(&self) -> u32 {
        self.naive_local().ordinal0()
    }
    #[inline]
    fn weekday(&self) -> Weekday {
        self.naive_local().weekday()
    }
    #[inline]
    fn iso_week(&self) -> IsoWeek {
        self.naive_local().iso_week()
    }

    #[inline]
    fn with_year(&self, year: i32) -> Option<Date<Tz>> {
        map_local(self, |date| date.with_year(year))
    }

    #[inline]
    fn with_month(&self, month: u32) -> Option<Date<Tz>> {
        map_local(self, |date| date.with_month(month))
    }

    #[inline]
    fn with_month0(&self, month0: u32) -> Option<Date<Tz>> {
        map_local(self, |date| date.with_month0(month0))
    }

    #[inline]
    fn with_day(&self, day: u32) -> Option<Date<Tz>> {
        map_local(self, |date| date.with_day(day))
    }

    #[inline]
    fn with_day0(&self, day0: u32) -> Option<Date<Tz>> {
        map_local(self, |date| date.with_day0(day0))
    }

    #[inline]
    fn with_ordinal(&self, ordinal: u32) -> Option<Date<Tz>> {
        map_local(self, |date| date.with_ordinal(ordinal))
    }

    #[inline]
    fn with_ordinal0(&self, ordinal0: u32) -> Option<Date<Tz>> {
        map_local(self, |date| date.with_ordinal0(ordinal0))
    }
}

// we need them as automatic impls cannot handle associated types
impl<Tz: TimeZone> Copy for Date<Tz> where <Tz as TimeZone>::Offset: Copy {}
unsafe impl<Tz: TimeZone> Send for Date<Tz> where <Tz as TimeZone>::Offset: Send {}

impl<Tz: TimeZone, Tz2: TimeZone> PartialEq<Date<Tz2>> for Date<Tz> {
    fn eq(&self, other: &Date<Tz2>) -> bool {
        self.date == other.date
    }
}

impl<Tz: TimeZone> Eq for Date<Tz> {}

impl<Tz: TimeZone> PartialOrd for Date<Tz> {
    fn partial_cmp(&self, other: &Date<Tz>) -> Option<Ordering> {
        self.date.partial_cmp(&other.date)
    }
}

impl<Tz: TimeZone> Ord for Date<Tz> {
    fn cmp(&self, other: &Date<Tz>) -> Ordering {
        self.date.cmp(&other.date)
    }
}

impl<Tz: TimeZone> hash::Hash for Date<Tz> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.date.hash(state)
    }
}

impl<Tz: TimeZone> Add<OldDuration> for Date<Tz> {
    type Output = Date<Tz>;

    #[inline]
    fn add(self, rhs: OldDuration) -> Date<Tz> {
        self.checked_add_signed(rhs).expect("`Date + Duration` overflowed")
    }
}

impl<Tz: TimeZone> AddAssign<OldDuration> for Date<Tz> {
    #[inline]
    fn add_assign(&mut self, rhs: OldDuration) {
        self.date = self.date.checked_add_signed(rhs).expect("`Date + Duration` overflowed");
    }
}

impl<Tz: TimeZone> Sub<OldDuration> for Date<Tz> {
    type Output = Date<Tz>;

    #[inline]
    fn sub(self, rhs: OldDuration) -> Date<Tz> {
        self.checked_sub_signed(rhs).expect("`Date - Duration` overflowed")
    }
}

impl<Tz: TimeZone> SubAssign<OldDuration> for Date<Tz> {
    #[inline]
    fn sub_assign(&mut self, rhs: OldDuration) {
        self.date = self.date.checked_sub_signed(rhs).expect("`Date - Duration` overflowed");
    }
}

impl<Tz: TimeZone> Sub<Date<Tz>> for Date<Tz> {
    type Output = OldDuration;

    #[inline]
    fn sub(self, rhs: Date<Tz>) -> OldDuration {
        self.signed_duration_since(rhs)
    }
}

impl<Tz: TimeZone> fmt::Debug for Date<Tz> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.naive_local().fmt(f)?;
        self.offset.fmt(f)
    }
}

impl<Tz: TimeZone> fmt::Display for Date<Tz>
where
    Tz::Offset: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.naive_local().fmt(f)?;
        self.offset.fmt(f)
    }
}

// Note that implementation of Arbitrary cannot be automatically derived for Date<Tz>, due to
// the nontrivial bound <Tz as TimeZone>::Offset: Arbitrary.
#[cfg(feature = "arbitrary")]
impl<'a, Tz> arbitrary::Arbitrary<'a> for Date<Tz>
where
    Tz: TimeZone,
    <Tz as TimeZone>::Offset: arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Date<Tz>> {
        let date = NaiveDate::arbitrary(u)?;
        let offset = <Tz as TimeZone>::Offset::arbitrary(u)?;
        Ok(Date::from_utc(date, offset))
    }
}

#[cfg(test)]
mod tests {
    use super::Date;

    use crate::oldtime::Duration;
    use crate::{FixedOffset, NaiveDate, Utc};

    #[cfg(feature = "clock")]
    use crate::offset::{Local, TimeZone};

    #[test]
    #[cfg(feature = "clock")]
    fn test_years_elapsed() {
        const WEEKS_PER_YEAR: f32 = 52.1775;

        // This is always at least one year because 1 year = 52.1775 weeks.
        let one_year_ago = Utc::today() - Duration::weeks((WEEKS_PER_YEAR * 1.5).ceil() as i64);
        // A bit more than 2 years.
        let two_year_ago = Utc::today() - Duration::weeks((WEEKS_PER_YEAR * 2.5).ceil() as i64);

        assert_eq!(Utc::today().years_since(one_year_ago), Some(1));
        assert_eq!(Utc::today().years_since(two_year_ago), Some(2));

        // If the given DateTime is later than now, the function will always return 0.
        let future = Utc::today() + Duration::weeks(12);
        assert_eq!(Utc::today().years_since(future), None);
    }

    #[test]
    fn test_date_add_assign() {
        let naivedate = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap();
        let date = Date::<Utc>::from_utc(naivedate, Utc);
        let mut date_add = date;

        date_add += Duration::days(5);
        assert_eq!(date_add, date + Duration::days(5));

        let timezone = FixedOffset::east_opt(60 * 60).unwrap();
        let date = date.with_timezone(&timezone);
        let date_add = date_add.with_timezone(&timezone);

        assert_eq!(date_add, date + Duration::days(5));

        let timezone = FixedOffset::west_opt(2 * 60 * 60).unwrap();
        let date = date.with_timezone(&timezone);
        let date_add = date_add.with_timezone(&timezone);

        assert_eq!(date_add, date + Duration::days(5));
    }

    #[test]
    #[cfg(feature = "clock")]
    fn test_date_add_assign_local() {
        let naivedate = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap();

        let date = Local.from_utc_date(&naivedate);
        let mut date_add = date;

        date_add += Duration::days(5);
        assert_eq!(date_add, date + Duration::days(5));
    }

    #[test]
    fn test_date_sub_assign() {
        let naivedate = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap();
        let date = Date::<Utc>::from_utc(naivedate, Utc);
        let mut date_sub = date;

        date_sub -= Duration::days(5);
        assert_eq!(date_sub, date - Duration::days(5));

        let timezone = FixedOffset::east_opt(60 * 60).unwrap();
        let date = date.with_timezone(&timezone);
        let date_sub = date_sub.with_timezone(&timezone);

        assert_eq!(date_sub, date - Duration::days(5));

        let timezone = FixedOffset::west_opt(2 * 60 * 60).unwrap();
        let date = date.with_timezone(&timezone);
        let date_sub = date_sub.with_timezone(&timezone);

        assert_eq!(date_sub, date - Duration::days(5));
    }

    #[test]
    #[cfg(feature = "clock")]
    fn test_date_sub_assign_local() {
        let naivedate = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap();

        let date = Local.from_utc_date(&naivedate);
        let mut date_sub = date;

        date_sub -= Duration::days(5);
        assert_eq!(date_sub, date - Duration::days(5));
    }
}
#[cfg(test)]
mod tests_rug_1 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let mut p1 = '\n'.escape_unicode();

        crate::date::map_local(&p0, |date| Some(date));

    }
}#[cfg(test)]
mod tests_rug_2 {
    use super::*;
    use crate::{NaiveDate, FixedOffset, TimeZone};

    #[test]
    fn test_rug() {
        let mut p0: NaiveDate = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap();
        let mut p1: <FixedOffset as TimeZone>::Offset = FixedOffset::east_opt(0).unwrap();

        crate::date::Date::<FixedOffset>::from_utc(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_3 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc, NaiveTime, DateTime};

    #[test]
    fn test_rug() {
        let date: Date<Utc> = Utc.ymd(2023, 10, 5);
        let time: NaiveTime = NaiveTime::from_hms_nano(12, 34, 56, 789_012_345);

        let datetime: Option<DateTime<Utc>> = date.and_time(time);

        assert!(datetime.is_some());
    }
}#[cfg(test)]
mod tests_rug_4 {
    use crate::{Datelike, TimeZone, Utc, date::Date};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: u32 = 14;
        let p2: u32 = 30;
        let p3: u32 = 45;

        p0.and_hms(p1, p2, p3);
    }
}#[cfg(test)]
mod tests_rug_5 {
    use crate::{Datelike, TimeZone, Utc};
    use crate::date::Date;

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5); // create the local variable v1 with type date::Date<Tz>
        let p1: u32 = 14; // sample hour
        let p2: u32 = 30; // sample minute
        let p3: u32 = 45; // sample second

        assert!(p0.and_hms_opt(p1, p2, p3).is_some());

        // Test with invalid time
        let invalid_hour: u32 = 25;
        assert!(p0.and_hms_opt(invalid_hour, p2, p3).is_none());

        let invalid_minute: u32 = 60;
        assert!(p0.and_hms_opt(p1, invalid_minute, p3).is_none());

        let invalid_second: u32 = 60;
        assert!(p0.and_hms_opt(p1, p2, invalid_second).is_none());
    }
}#[cfg(test)]
mod tests_rug_6 {
    use crate::{Datelike, TimeZone, Utc, Date};

    #[test]
    fn test_rug() {
        let mut p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let mut p1: u32 = 14;
        let mut p2: u32 = 30;
        let mut p3: u32 = 45;
        let mut p4: u32 = 500;

        p0.and_hms_milli(p1, p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_7 {
    use crate::{Datelike, TimeZone, Utc, Date, DateTime};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: u32 = 14; // Sample hour
        let p2: u32 = 30; // Sample minute
        let p3: u32 = 45; // Sample second
        let p4: u32 = 500; // Sample millisecond

        assert!(p0.and_hms_milli_opt(p1, p2, p3, p4).is_some());
    }
}#[cfg(test)]
mod tests_rug_8 {
    use crate::{Datelike, TimeZone, Utc};

    #[test]
    fn test_rug() {
        let p0 = Utc.ymd(2023, 10, 5);
        let p1: u32 = 14;
        let p2: u32 = 30;
        let p3: u32 = 45;
        let p4: u32 = 123456;

        p0.and_hms_micro(p1, p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_9 {
    use crate::{Datelike, TimeZone, Utc};
    use crate::date::Date;

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: u32 = 14;
        let p2: u32 = 30;
        let p3: u32 = 45;
        let p4: u32 = 678901;

        assert!(p0.and_hms_micro_opt(p1, p2, p3, p4).is_some());
        
        // Test with invalid time
        let invalid_hour: u32 = 25;
        assert!(p0.and_hms_micro_opt(invalid_hour, p2, p3, p4).is_none());

        let invalid_minute: u32 = 60;
        assert!(p0.and_hms_micro_opt(p1, invalid_minute, p3, p4).is_none());

        let invalid_second: u32 = 60;
        assert!(p0.and_hms_micro_opt(p1, p2, invalid_second, p4).is_none());

        let invalid_micro: u32 = 1_000_000;
        assert!(p0.and_hms_micro_opt(p1, p2, p3, invalid_micro).is_none());
    }
}#[cfg(test)]
mod tests_rug_10 {
    use crate::{Datelike, TimeZone, Utc, Date};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: u32 = 14; // Sample hour
        let p2: u32 = 30; // Sample minute
        let p3: u32 = 45; // Sample second
        let p4: u32 = 1_234_567_890; // Sample nanosecond

        <Date<Utc>>::and_hms_nano(&p0, p1, p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_11 {
    use crate::{Datelike, TimeZone, Utc, DateTime, Date};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: u32 = 14;
        let p2: u32 = 30;
        let p3: u32 = 45;
        let p4: u32 = 1_234_567_890;

        let result = p0.and_hms_nano_opt(p1, p2, p3, p4);
        assert!(result.is_some());
    }
}#[cfg(test)]
mod tests_rug_13 {
    use crate::{Datelike, TimeZone, Utc, Date};

    #[test]
    fn test_rug() {
        let mut p0: Date<Utc> = Utc.ymd(2023, 10, 5); // create the local variable v1 with type date::Date<Tz>

        assert_eq!(p0.succ_opt(), Some(Utc.ymd(2023, 10, 6)));
    }
}#[cfg(test)]
mod tests_rug_14 {
    use crate::{Datelike, TimeZone, Utc};
    use super::*;

    #[test]
    fn test_rug() {
        let p0: crate::date::Date<Utc> = Utc.ymd(2023, 10, 5);

        crate::date::Date::<Utc>::pred(&p0);
    }
}#[cfg(test)]
mod tests_rug_15 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);

        assert!(p0.pred_opt().is_some());
        
        // Test the first representable date
        let first_date = Date::<Utc>::from_utc(NaiveDate::MIN, Utc);
        assert!(first_date.pred_opt().is_none());
    }
}#[cfg(test)]
mod tests_rug_17 {
    use crate::{Datelike, TimeZone, Utc, Date};

    #[test]
    fn test_timezone() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);

        assert_eq!(p0.timezone(), Utc);
    }
}#[cfg(test)]
mod tests_rug_18 {
    use crate::{Datelike, TimeZone, Utc, FixedOffset, Date};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: &FixedOffset = &FixedOffset::east_opt(5 * 3600).unwrap();

        p0.with_timezone(p1);
    }
}#[cfg(test)]
mod tests_rug_19 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc, Duration};

    #[test]
    fn test_rug() {
        let mut p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let mut p1: Duration = Duration::days(10);

        assert_eq!(p0.checked_add_signed(p1), Some(Utc.ymd(2023, 10, 15)));
    }
}#[cfg(test)]
mod tests_rug_20 {
    use crate::{Datelike, Duration as OldDuration, TimeZone, Utc};

    #[test]
    fn test_rug() {
        let v1: crate::date::Date<Utc> = Utc.ymd(2023, 10, 5);
        let v2: OldDuration = OldDuration::days(10);

        let result = v1.checked_sub_signed(v2);

        assert_eq!(result.unwrap(), Utc.ymd(2023, 9, 25));
    }
}#[cfg(test)]
mod tests_rug_21 {
    use crate::{Datelike, TimeZone, Utc, Date};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: Date<Utc> = Utc.ymd(2023, 10, 5);

        p0.signed_duration_since(p1);
    }
}#[cfg(test)]
mod tests_rug_22 {
    use crate::{Datelike, TimeZone, Utc, Date};

    #[test]
    fn test_rug() {
        let mut p0: Date<Utc> = Utc.ymd(2023, 10, 5);

        assert_eq!(p0.naive_utc(), Utc.ymd(2023, 10, 5).naive_utc());
    }
}#[cfg(test)]
mod tests_rug_23 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc, Date};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);

        assert_eq!(p0.naive_local(), p0.naive_utc());
    }
}#[cfg(test)]
mod tests_rug_24 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc};

    #[test]
    fn test_rug() {
        let mut p0 = Utc.ymd(2023, 10, 5); // create the local variable v1 with type date::Date<Tz>
        let mut p1 = Utc.ymd(2022, 10, 5); // create the local variable v1 with type date::Date<Tz>

        assert_eq!(p0.years_since(p1), Some(1));
    }
}#[cfg(test)]
mod tests_rug_25 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc};
    use crate::format::StrftimeItems;

    #[test]
    fn test_rug() {
        let mut date = Utc.ymd(2023, 10, 5);
        let mut items = StrftimeItems::new("%Y-%m-%d %H:%M:%S");

        crate::date::Date::<Utc>::format_with_items(&date, items);
    }
}#[cfg(test)]
mod tests_rug_26 {
    use super::*;
    use crate::{Datelike, TimeZone, Utc, date::Date};

    #[test]
    fn test_rug() {
        let p0: Date<Utc> = Utc.ymd(2023, 10, 5);
        let p1: &str = "%Y-%m-%d";

        <Date<Utc>>::format(&p0, p1);
    }
}