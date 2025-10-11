//! The [`Date`] struct and its associated `impl`s.

use core::fmt;
use core::ops::{Add, Sub};
use core::time::Duration as StdDuration;
#[cfg(feature = "formatting")]
use std::io;

#[cfg(feature = "formatting")]
use crate::formatting::Formattable;
#[cfg(feature = "parsing")]
use crate::parsing::Parsable;
use crate::util::{days_in_year, days_in_year_month, is_leap_year, weeks_in_year};
use crate::{error, Duration, Month, PrimitiveDateTime, Time, Weekday};

/// The minimum valid year.
#[cfg(feature = "large-dates")]
pub(crate) const MIN_YEAR: i32 = -999_999;
/// The maximum valid year.
#[cfg(feature = "large-dates")]
pub(crate) const MAX_YEAR: i32 = 999_999;

/// The minimum valid year.
#[cfg(not(feature = "large-dates"))]
pub(crate) const MIN_YEAR: i32 = -9999;
/// The maximum valid year.
#[cfg(not(feature = "large-dates"))]
pub(crate) const MAX_YEAR: i32 = 9999;

/// Date in the proleptic Gregorian calendar.
///
/// By default, years between ±9999 inclusive are representable. This can be expanded to ±999,999
/// inclusive by enabling the `large-dates` crate feature. Doing so has performance implications
/// and introduces some ambiguities when parsing.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Date {
    /// Bitpacked field containing both the year and ordinal.
    // |     xx     | xxxxxxxxxxxxxxxxxxxxx | xxxxxxxxx |
    // |   2 bits   |        21 bits        |  9 bits   |
    // | unassigned |         year          |  ordinal  |
    // The year is 15 bits when `large-dates` is not enabled.
    pub(crate) value: i32,
}

impl fmt::Debug for Date {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Date")
            .field("year", &self.year())
            .field("ordinal", &self.ordinal())
            .finish()
    }
}

impl Date {
    /// The minimum valid `Date`.
    ///
    /// The value of this may vary depending on the feature flags enabled.
    pub const MIN: Self = Self::__from_ordinal_date_unchecked(MIN_YEAR, 1);

    /// The maximum valid `Date`.
    ///
    /// The value of this may vary depending on the feature flags enabled.
    pub const MAX: Self = Self::__from_ordinal_date_unchecked(MAX_YEAR, days_in_year(MAX_YEAR));

    // region: constructors
    /// Construct a `Date` from the year and ordinal values, the validity of which must be
    /// guaranteed by the caller.
    #[doc(hidden)]
    pub const fn __from_ordinal_date_unchecked(year: i32, ordinal: u16) -> Self {
        Self {
            value: (year << 9) | ordinal as i32,
        }
    }

    /// Attempt to create a `Date` from the year, month, and day.
    ///
    /// ```rust
    /// # use time::{Date, Month};
    /// assert!(Date::from_calendar_date(2019, Month::January, 1).is_ok());
    /// assert!(Date::from_calendar_date(2019, Month::December, 31).is_ok());
    /// ```
    ///
    /// ```rust
    /// # use time::{Date, Month};
    /// assert!(Date::from_calendar_date(2019, Month::February, 29).is_err()); // 2019 isn't a leap year.
    /// ```
    pub const fn from_calendar_date(
        year: i32,
        month: Month,
        day: u8,
    ) -> Result<Self, error::ComponentRange> {
        /// Cumulative days through the beginning of a month in both common and leap years.
        const DAYS_CUMULATIVE_COMMON_LEAP: [[u16; 12]; 2] = [
            [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334],
            [0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335],
        ];

        ensure_value_in_range!(year in MIN_YEAR => MAX_YEAR);
        ensure_value_in_range!(day conditionally in 1 => days_in_year_month(year, month));

        Ok(Self::__from_ordinal_date_unchecked(
            year,
            DAYS_CUMULATIVE_COMMON_LEAP[is_leap_year(year) as usize][month as usize - 1]
                + day as u16,
        ))
    }

    /// Attempt to create a `Date` from the year and ordinal day number.
    ///
    /// ```rust
    /// # use time::Date;
    /// assert!(Date::from_ordinal_date(2019, 1).is_ok());
    /// assert!(Date::from_ordinal_date(2019, 365).is_ok());
    /// ```
    ///
    /// ```rust
    /// # use time::Date;
    /// assert!(Date::from_ordinal_date(2019, 366).is_err()); // 2019 isn't a leap year.
    /// ```
    pub const fn from_ordinal_date(year: i32, ordinal: u16) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(year in MIN_YEAR => MAX_YEAR);
        ensure_value_in_range!(ordinal conditionally in 1 => days_in_year(year));
        Ok(Self::__from_ordinal_date_unchecked(year, ordinal))
    }

    /// Attempt to create a `Date` from the ISO year, week, and weekday.
    ///
    /// ```rust
    /// # use time::{Date, Weekday::*};
    /// assert!(Date::from_iso_week_date(2019, 1, Monday).is_ok());
    /// assert!(Date::from_iso_week_date(2019, 1, Tuesday).is_ok());
    /// assert!(Date::from_iso_week_date(2020, 53, Friday).is_ok());
    /// ```
    ///
    /// ```rust
    /// # use time::{Date, Weekday::*};
    /// assert!(Date::from_iso_week_date(2019, 53, Monday).is_err()); // 2019 doesn't have 53 weeks.
    /// ```
    pub const fn from_iso_week_date(
        year: i32,
        week: u8,
        weekday: Weekday,
    ) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(year in MIN_YEAR => MAX_YEAR);
        ensure_value_in_range!(week conditionally in 1 => weeks_in_year(year));

        let adj_year = year - 1;
        let raw = 365 * adj_year + div_floor!(adj_year, 4) - div_floor!(adj_year, 100)
            + div_floor!(adj_year, 400);
        let jan_4 = match (raw % 7) as i8 {
            -6 | 1 => 8,
            -5 | 2 => 9,
            -4 | 3 => 10,
            -3 | 4 => 4,
            -2 | 5 => 5,
            -1 | 6 => 6,
            _ => 7,
        };
        let ordinal = week as i16 * 7 + weekday.number_from_monday() as i16 - jan_4;

        Ok(if ordinal <= 0 {
            Self::__from_ordinal_date_unchecked(
                year - 1,
                (ordinal as u16).wrapping_add(days_in_year(year - 1)),
            )
        } else if ordinal > days_in_year(year) as i16 {
            Self::__from_ordinal_date_unchecked(year + 1, ordinal as u16 - days_in_year(year))
        } else {
            Self::__from_ordinal_date_unchecked(year, ordinal as _)
        })
    }

    /// Create a `Date` from the Julian day.
    ///
    /// The algorithm to perform this conversion is derived from one provided by Peter Baum; it is
    /// freely available [here](https://www.researchgate.net/publication/316558298_Date_Algorithms).
    ///
    /// ```rust
    /// # use time::{Date, macros::date};
    /// assert_eq!(Date::from_julian_day(0), Ok(date!(-4713 - 11 - 24)));
    /// assert_eq!(Date::from_julian_day(2_451_545), Ok(date!(2000 - 01 - 01)));
    /// assert_eq!(Date::from_julian_day(2_458_485), Ok(date!(2019 - 01 - 01)));
    /// assert_eq!(Date::from_julian_day(2_458_849), Ok(date!(2019 - 12 - 31)));
    /// ```
    #[doc(alias = "from_julian_date")]
    pub const fn from_julian_day(julian_day: i32) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(
            julian_day in Self::MIN.to_julian_day() => Self::MAX.to_julian_day()
        );
        Ok(Self::from_julian_day_unchecked(julian_day))
    }

    /// Create a `Date` from the Julian day.
    ///
    /// This does not check the validity of the provided Julian day, and as such may result in an
    /// internally invalid value.
    #[doc(alias = "from_julian_date_unchecked")]
    pub(crate) const fn from_julian_day_unchecked(julian_day: i32) -> Self {
        #![allow(trivial_numeric_casts)] // cast depends on type alias

        /// A type that is either `i32` or `i64`. This subtle difference allows for optimization
        /// based on the valid values.
        #[cfg(feature = "large-dates")]
        type MaybeWidened = i64;
        #[allow(clippy::missing_docs_in_private_items)]
        #[cfg(not(feature = "large-dates"))]
        type MaybeWidened = i32;

        // To avoid a potential overflow, the value may need to be widened for some arithmetic.

        let z = julian_day - 1_721_119;
        let g = 100 * z as MaybeWidened - 25;
        let a = (g / 3_652_425) as i32;
        let b = a - a / 4;
        let mut year = div_floor!(100 * b as MaybeWidened + g, 36525) as i32;
        let mut ordinal = (b + z - div_floor!(36525 * year as MaybeWidened, 100) as i32) as _;

        if is_leap_year(year) {
            ordinal += 60;
            cascade!(ordinal in 1..367 => year);
        } else {
            ordinal += 59;
            cascade!(ordinal in 1..366 => year);
        }

        Self::__from_ordinal_date_unchecked(year, ordinal)
    }
    // endregion constructors

    // region: getters
    /// Get the year of the date.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(2019 - 01 - 01).year(), 2019);
    /// assert_eq!(date!(2019 - 12 - 31).year(), 2019);
    /// assert_eq!(date!(2020 - 01 - 01).year(), 2020);
    /// ```
    pub const fn year(self) -> i32 {
        self.value >> 9
    }

    /// Get the month.
    ///
    /// ```rust
    /// # use time::{macros::date, Month};
    /// assert_eq!(date!(2019 - 01 - 01).month(), Month::January);
    /// assert_eq!(date!(2019 - 12 - 31).month(), Month::December);
    /// ```
    pub const fn month(self) -> Month {
        self.month_day().0
    }

    /// Get the day of the month.
    ///
    /// The returned value will always be in the range `1..=31`.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(2019 - 01 - 01).day(), 1);
    /// assert_eq!(date!(2019 - 12 - 31).day(), 31);
    /// ```
    pub const fn day(self) -> u8 {
        self.month_day().1
    }

    /// Get the month and day. This is more efficient than fetching the components individually.
    // For whatever reason, rustc has difficulty optimizing this function. It's significantly faster
    // to write the statements out by hand.
    pub(crate) const fn month_day(self) -> (Month, u8) {
        /// The number of days up to and including the given month. Common years
        /// are first, followed by leap years.
        const CUMULATIVE_DAYS_IN_MONTH_COMMON_LEAP: [[u16; 11]; 2] = [
            [31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334],
            [31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335],
        ];

        let days = CUMULATIVE_DAYS_IN_MONTH_COMMON_LEAP[is_leap_year(self.year()) as usize];
        let ordinal = self.ordinal();

        if ordinal > days[10] {
            (Month::December, (ordinal - days[10]) as _)
        } else if ordinal > days[9] {
            (Month::November, (ordinal - days[9]) as _)
        } else if ordinal > days[8] {
            (Month::October, (ordinal - days[8]) as _)
        } else if ordinal > days[7] {
            (Month::September, (ordinal - days[7]) as _)
        } else if ordinal > days[6] {
            (Month::August, (ordinal - days[6]) as _)
        } else if ordinal > days[5] {
            (Month::July, (ordinal - days[5]) as _)
        } else if ordinal > days[4] {
            (Month::June, (ordinal - days[4]) as _)
        } else if ordinal > days[3] {
            (Month::May, (ordinal - days[3]) as _)
        } else if ordinal > days[2] {
            (Month::April, (ordinal - days[2]) as _)
        } else if ordinal > days[1] {
            (Month::March, (ordinal - days[1]) as _)
        } else if ordinal > days[0] {
            (Month::February, (ordinal - days[0]) as _)
        } else {
            (Month::January, ordinal as _)
        }
    }

    /// Get the day of the year.
    ///
    /// The returned value will always be in the range `1..=366` (`1..=365` for common years).
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(2019 - 01 - 01).ordinal(), 1);
    /// assert_eq!(date!(2019 - 12 - 31).ordinal(), 365);
    /// ```
    pub const fn ordinal(self) -> u16 {
        (self.value & 0x1FF) as _
    }

    /// Get the ISO 8601 year and week number.
    pub(crate) const fn iso_year_week(self) -> (i32, u8) {
        let (year, ordinal) = self.to_ordinal_date();

        match ((ordinal + 10 - self.weekday().number_from_monday() as u16) / 7) as _ {
            0 => (year - 1, weeks_in_year(year - 1)),
            53 if weeks_in_year(year) == 52 => (year + 1, 1),
            week => (year, week),
        }
    }

    /// Get the ISO week number.
    ///
    /// The returned value will always be in the range `1..=53`.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(2019 - 01 - 01).iso_week(), 1);
    /// assert_eq!(date!(2019 - 10 - 04).iso_week(), 40);
    /// assert_eq!(date!(2020 - 01 - 01).iso_week(), 1);
    /// assert_eq!(date!(2020 - 12 - 31).iso_week(), 53);
    /// assert_eq!(date!(2021 - 01 - 01).iso_week(), 53);
    /// ```
    pub const fn iso_week(self) -> u8 {
        self.iso_year_week().1
    }

    /// Get the week number where week 1 begins on the first Sunday.
    ///
    /// The returned value will always be in the range `0..=53`.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(2019 - 01 - 01).sunday_based_week(), 0);
    /// assert_eq!(date!(2020 - 01 - 01).sunday_based_week(), 0);
    /// assert_eq!(date!(2020 - 12 - 31).sunday_based_week(), 52);
    /// assert_eq!(date!(2021 - 01 - 01).sunday_based_week(), 0);
    /// ```
    pub const fn sunday_based_week(self) -> u8 {
        ((self.ordinal() as i16 - self.weekday().number_days_from_sunday() as i16 + 6) / 7) as _
    }

    /// Get the week number where week 1 begins on the first Monday.
    ///
    /// The returned value will always be in the range `0..=53`.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(2019 - 01 - 01).monday_based_week(), 0);
    /// assert_eq!(date!(2020 - 01 - 01).monday_based_week(), 0);
    /// assert_eq!(date!(2020 - 12 - 31).monday_based_week(), 52);
    /// assert_eq!(date!(2021 - 01 - 01).monday_based_week(), 0);
    /// ```
    pub const fn monday_based_week(self) -> u8 {
        ((self.ordinal() as i16 - self.weekday().number_days_from_monday() as i16 + 6) / 7) as _
    }

    /// Get the year, month, and day.
    ///
    /// ```rust
    /// # use time::{macros::date, Month};
    /// assert_eq!(
    ///     date!(2019 - 01 - 01).to_calendar_date(),
    ///     (2019, Month::January, 1)
    /// );
    /// ```
    pub const fn to_calendar_date(self) -> (i32, Month, u8) {
        let (month, day) = self.month_day();
        (self.year(), month, day)
    }

    /// Get the year and ordinal day number.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(2019 - 01 - 01).to_ordinal_date(), (2019, 1));
    /// ```
    pub const fn to_ordinal_date(self) -> (i32, u16) {
        (self.year(), self.ordinal())
    }

    /// Get the ISO 8601 year, week number, and weekday.
    ///
    /// ```rust
    /// # use time::{Weekday::*, macros::date};
    /// assert_eq!(date!(2019 - 01 - 01).to_iso_week_date(), (2019, 1, Tuesday));
    /// assert_eq!(date!(2019 - 10 - 04).to_iso_week_date(), (2019, 40, Friday));
    /// assert_eq!(
    ///     date!(2020 - 01 - 01).to_iso_week_date(),
    ///     (2020, 1, Wednesday)
    /// );
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).to_iso_week_date(),
    ///     (2020, 53, Thursday)
    /// );
    /// assert_eq!(date!(2021 - 01 - 01).to_iso_week_date(), (2020, 53, Friday));
    /// ```
    pub const fn to_iso_week_date(self) -> (i32, u8, Weekday) {
        let (year, ordinal) = self.to_ordinal_date();
        let weekday = self.weekday();

        match ((ordinal + 10 - self.weekday().number_from_monday() as u16) / 7) as _ {
            0 => (year - 1, weeks_in_year(year - 1), weekday),
            53 if weeks_in_year(year) == 52 => (year + 1, 1, weekday),
            week => (year, week, weekday),
        }
    }

    /// Get the weekday.
    ///
    /// ```rust
    /// # use time::{Weekday::*, macros::date};
    /// assert_eq!(date!(2019 - 01 - 01).weekday(), Tuesday);
    /// assert_eq!(date!(2019 - 02 - 01).weekday(), Friday);
    /// assert_eq!(date!(2019 - 03 - 01).weekday(), Friday);
    /// assert_eq!(date!(2019 - 04 - 01).weekday(), Monday);
    /// assert_eq!(date!(2019 - 05 - 01).weekday(), Wednesday);
    /// assert_eq!(date!(2019 - 06 - 01).weekday(), Saturday);
    /// assert_eq!(date!(2019 - 07 - 01).weekday(), Monday);
    /// assert_eq!(date!(2019 - 08 - 01).weekday(), Thursday);
    /// assert_eq!(date!(2019 - 09 - 01).weekday(), Sunday);
    /// assert_eq!(date!(2019 - 10 - 01).weekday(), Tuesday);
    /// assert_eq!(date!(2019 - 11 - 01).weekday(), Friday);
    /// assert_eq!(date!(2019 - 12 - 01).weekday(), Sunday);
    /// ```
    pub const fn weekday(self) -> Weekday {
        match self.to_julian_day() % 7 {
            -6 | 1 => Weekday::Tuesday,
            -5 | 2 => Weekday::Wednesday,
            -4 | 3 => Weekday::Thursday,
            -3 | 4 => Weekday::Friday,
            -2 | 5 => Weekday::Saturday,
            -1 | 6 => Weekday::Sunday,
            _ => Weekday::Monday,
        }
    }

    /// Get the next calendar date.
    ///
    /// ```rust
    /// # use time::{Date, macros::date};
    /// assert_eq!(
    ///     date!(2019 - 01 - 01).next_day(),
    ///     Some(date!(2019 - 01 - 02))
    /// );
    /// assert_eq!(
    ///     date!(2019 - 01 - 31).next_day(),
    ///     Some(date!(2019 - 02 - 01))
    /// );
    /// assert_eq!(
    ///     date!(2019 - 12 - 31).next_day(),
    ///     Some(date!(2020 - 01 - 01))
    /// );
    /// assert_eq!(Date::MAX.next_day(), None);
    /// ```
    pub const fn next_day(self) -> Option<Self> {
        if self.ordinal() == 366 || (self.ordinal() == 365 && !is_leap_year(self.year())) {
            if self.value == Self::MAX.value {
                None
            } else {
                Some(Self::__from_ordinal_date_unchecked(self.year() + 1, 1))
            }
        } else {
            Some(Self {
                value: self.value + 1,
            })
        }
    }

    /// Get the previous calendar date.
    ///
    /// ```rust
    /// # use time::{Date, macros::date};
    /// assert_eq!(
    ///     date!(2019 - 01 - 02).previous_day(),
    ///     Some(date!(2019 - 01 - 01))
    /// );
    /// assert_eq!(
    ///     date!(2019 - 02 - 01).previous_day(),
    ///     Some(date!(2019 - 01 - 31))
    /// );
    /// assert_eq!(
    ///     date!(2020 - 01 - 01).previous_day(),
    ///     Some(date!(2019 - 12 - 31))
    /// );
    /// assert_eq!(Date::MIN.previous_day(), None);
    /// ```
    pub const fn previous_day(self) -> Option<Self> {
        if self.ordinal() != 1 {
            Some(Self {
                value: self.value - 1,
            })
        } else if self.value == Self::MIN.value {
            None
        } else {
            Some(Self::__from_ordinal_date_unchecked(
                self.year() - 1,
                days_in_year(self.year() - 1),
            ))
        }
    }

    /// Get the Julian day for the date.
    ///
    /// The algorithm to perform this conversion is derived from one provided by Peter Baum; it is
    /// freely available [here](https://www.researchgate.net/publication/316558298_Date_Algorithms).
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert_eq!(date!(-4713 - 11 - 24).to_julian_day(), 0);
    /// assert_eq!(date!(2000 - 01 - 01).to_julian_day(), 2_451_545);
    /// assert_eq!(date!(2019 - 01 - 01).to_julian_day(), 2_458_485);
    /// assert_eq!(date!(2019 - 12 - 31).to_julian_day(), 2_458_849);
    /// ```
    pub const fn to_julian_day(self) -> i32 {
        let year = self.year() - 1;
        let ordinal = self.ordinal() as i32;

        ordinal + 365 * year + div_floor!(year, 4) - div_floor!(year, 100)
            + div_floor!(year, 400)
            + 1_721_425
    }
    // endregion getters

    // region: checked arithmetic
    /// Computes `self + duration`, returning `None` if an overflow occurred.
    ///
    /// ```rust
    /// # use time::{Date, ext::NumericalDuration, macros::date};
    /// assert_eq!(Date::MAX.checked_add(1.days()), None);
    /// assert_eq!(Date::MIN.checked_add((-2).days()), None);
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).checked_add(2.days()),
    ///     Some(date!(2021 - 01 - 02))
    /// );
    /// ```
    ///
    /// # Note
    ///
    /// This function only takes whole days into account.
    ///
    /// ```rust
    /// # use time::{Date, ext::NumericalDuration, macros::date};
    /// assert_eq!(Date::MAX.checked_add(23.hours()), Some(Date::MAX));
    /// assert_eq!(Date::MIN.checked_add((-23).hours()), Some(Date::MIN));
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).checked_add(23.hours()),
    ///     Some(date!(2020 - 12 - 31))
    /// );
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).checked_add(47.hours()),
    ///     Some(date!(2021 - 01 - 01))
    /// );
    /// ```
    pub const fn checked_add(self, duration: Duration) -> Option<Self> {
        let whole_days = duration.whole_days();
        if whole_days < i32::MIN as i64 || whole_days > i32::MAX as i64 {
            return None;
        }

        let julian_day = const_try_opt!(self.to_julian_day().checked_add(whole_days as _));
        if let Ok(date) = Self::from_julian_day(julian_day) {
            Some(date)
        } else {
            None
        }
    }

    /// Computes `self - duration`, returning `None` if an overflow occurred.
    ///
    /// ```
    /// # use time::{Date, ext::NumericalDuration, macros::date};
    /// assert_eq!(Date::MAX.checked_sub((-2).days()), None);
    /// assert_eq!(Date::MIN.checked_sub(1.days()), None);
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).checked_sub(2.days()),
    ///     Some(date!(2020 - 12 - 29))
    /// );
    /// ```
    ///
    /// # Note
    ///
    /// This function only takes whole days into account.
    ///
    /// ```
    /// # use time::{Date, ext::NumericalDuration, macros::date};
    /// assert_eq!(Date::MAX.checked_sub((-23).hours()), Some(Date::MAX));
    /// assert_eq!(Date::MIN.checked_sub(23.hours()), Some(Date::MIN));
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).checked_sub(23.hours()),
    ///     Some(date!(2020 - 12 - 31))
    /// );
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).checked_sub(47.hours()),
    ///     Some(date!(2020 - 12 - 30))
    /// );
    /// ```
    pub const fn checked_sub(self, duration: Duration) -> Option<Self> {
        let whole_days = duration.whole_days();
        if whole_days < i32::MIN as i64 || whole_days > i32::MAX as i64 {
            return None;
        }

        let julian_day = const_try_opt!(self.to_julian_day().checked_sub(whole_days as _));
        if let Ok(date) = Self::from_julian_day(julian_day) {
            Some(date)
        } else {
            None
        }
    }
    // endregion: checked arithmetic

    // region: saturating arithmetic
    /// Computes `self + duration`, saturating value on overflow.
    ///
    /// ```rust
    /// # use time::{Date, ext::NumericalDuration, macros::date};
    /// assert_eq!(Date::MAX.saturating_add(1.days()), Date::MAX);
    /// assert_eq!(Date::MIN.saturating_add((-2).days()), Date::MIN);
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).saturating_add(2.days()),
    ///     date!(2021 - 01 - 02)
    /// );
    /// ```
    ///
    /// # Note
    ///
    /// This function only takes whole days into account.
    ///
    /// ```rust
    /// # use time::{ext::NumericalDuration, macros::date};
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).saturating_add(23.hours()),
    ///     date!(2020 - 12 - 31)
    /// );
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).saturating_add(47.hours()),
    ///     date!(2021 - 01 - 01)
    /// );
    /// ```
    pub const fn saturating_add(self, duration: Duration) -> Self {
        if let Some(datetime) = self.checked_add(duration) {
            datetime
        } else if duration.is_negative() {
            Self::MIN
        } else {
            Self::MAX
        }
    }

    /// Computes `self - duration`, saturating value on overflow.
    ///
    /// ```
    /// # use time::{Date, ext::NumericalDuration, macros::date};
    /// assert_eq!(Date::MAX.saturating_sub((-2).days()), Date::MAX);
    /// assert_eq!(Date::MIN.saturating_sub(1.days()), Date::MIN);
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).saturating_sub(2.days()),
    ///     date!(2020 - 12 - 29)
    /// );
    /// ```
    ///
    /// # Note
    ///
    /// This function only takes whole days into account.
    ///
    /// ```
    /// # use time::{ext::NumericalDuration, macros::date};
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).saturating_sub(23.hours()),
    ///     date!(2020 - 12 - 31)
    /// );
    /// assert_eq!(
    ///     date!(2020 - 12 - 31).saturating_sub(47.hours()),
    ///     date!(2020 - 12 - 30)
    /// );
    /// ```
    pub const fn saturating_sub(self, duration: Duration) -> Self {
        if let Some(datetime) = self.checked_sub(duration) {
            datetime
        } else if duration.is_negative() {
            Self::MAX
        } else {
            Self::MIN
        }
    }
    // region: saturating arithmetic
}

// region: attach time
/// Methods to add a [`Time`] component, resulting in a [`PrimitiveDateTime`].
impl Date {
    /// Create a [`PrimitiveDateTime`] using the existing date. The [`Time`] component will be set
    /// to midnight.
    ///
    /// ```rust
    /// # use time::macros::{date, datetime};
    /// assert_eq!(date!(1970-01-01).midnight(), datetime!(1970-01-01 0:00));
    /// ```
    pub const fn midnight(self) -> PrimitiveDateTime {
        PrimitiveDateTime::new(self, Time::MIDNIGHT)
    }

    /// Create a [`PrimitiveDateTime`] using the existing date and the provided [`Time`].
    ///
    /// ```rust
    /// # use time::macros::{date, datetime, time};
    /// assert_eq!(
    ///     date!(1970-01-01).with_time(time!(0:00)),
    ///     datetime!(1970-01-01 0:00),
    /// );
    /// ```
    pub const fn with_time(self, time: Time) -> PrimitiveDateTime {
        PrimitiveDateTime::new(self, time)
    }

    /// Attempt to create a [`PrimitiveDateTime`] using the existing date and the provided time.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert!(date!(1970 - 01 - 01).with_hms(0, 0, 0).is_ok());
    /// assert!(date!(1970 - 01 - 01).with_hms(24, 0, 0).is_err());
    /// ```
    pub const fn with_hms(
        self,
        hour: u8,
        minute: u8,
        second: u8,
    ) -> Result<PrimitiveDateTime, error::ComponentRange> {
        Ok(PrimitiveDateTime::new(
            self,
            const_try!(Time::from_hms(hour, minute, second)),
        ))
    }

    /// Attempt to create a [`PrimitiveDateTime`] using the existing date and the provided time.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert!(date!(1970 - 01 - 01).with_hms_milli(0, 0, 0, 0).is_ok());
    /// assert!(date!(1970 - 01 - 01).with_hms_milli(24, 0, 0, 0).is_err());
    /// ```
    pub const fn with_hms_milli(
        self,
        hour: u8,
        minute: u8,
        second: u8,
        millisecond: u16,
    ) -> Result<PrimitiveDateTime, error::ComponentRange> {
        Ok(PrimitiveDateTime::new(
            self,
            const_try!(Time::from_hms_milli(hour, minute, second, millisecond)),
        ))
    }

    /// Attempt to create a [`PrimitiveDateTime`] using the existing date and the provided time.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert!(date!(1970 - 01 - 01).with_hms_micro(0, 0, 0, 0).is_ok());
    /// assert!(date!(1970 - 01 - 01).with_hms_micro(24, 0, 0, 0).is_err());
    /// ```
    pub const fn with_hms_micro(
        self,
        hour: u8,
        minute: u8,
        second: u8,
        microsecond: u32,
    ) -> Result<PrimitiveDateTime, error::ComponentRange> {
        Ok(PrimitiveDateTime::new(
            self,
            const_try!(Time::from_hms_micro(hour, minute, second, microsecond)),
        ))
    }

    /// Attempt to create a [`PrimitiveDateTime`] using the existing date and the provided time.
    ///
    /// ```rust
    /// # use time::macros::date;
    /// assert!(date!(1970 - 01 - 01).with_hms_nano(0, 0, 0, 0).is_ok());
    /// assert!(date!(1970 - 01 - 01).with_hms_nano(24, 0, 0, 0).is_err());
    /// ```
    pub const fn with_hms_nano(
        self,
        hour: u8,
        minute: u8,
        second: u8,
        nanosecond: u32,
    ) -> Result<PrimitiveDateTime, error::ComponentRange> {
        Ok(PrimitiveDateTime::new(
            self,
            const_try!(Time::from_hms_nano(hour, minute, second, nanosecond)),
        ))
    }
}
// endregion attach time

// region: formatting & parsing
#[cfg(feature = "formatting")]
impl Date {
    /// Format the `Date` using the provided [format description](crate::format_description).
    pub fn format_into(
        self,
        output: &mut impl io::Write,
        format: &(impl Formattable + ?Sized),
    ) -> Result<usize, error::Format> {
        format.format_into(output, Some(self), None, None)
    }

    /// Format the `Date` using the provided [format description](crate::format_description).
    ///
    /// ```rust
    /// # use time::{format_description, macros::date};
    /// let format = format_description::parse("[year]-[month]-[day]")?;
    /// assert_eq!(date!(2020 - 01 - 02).format(&format)?, "2020-01-02");
    /// # Ok::<_, time::Error>(())
    /// ```
    pub fn format(self, format: &(impl Formattable + ?Sized)) -> Result<String, error::Format> {
        format.format(Some(self), None, None)
    }
}

#[cfg(feature = "parsing")]
impl Date {
    /// Parse a `Date` from the input using the provided [format
    /// description](crate::format_description).
    ///
    /// ```rust
    /// # use time::{format_description, macros::date, Date};
    /// let format = format_description::parse("[year]-[month]-[day]")?;
    /// assert_eq!(Date::parse("2020-01-02", &format)?, date!(2020 - 01 - 02));
    /// # Ok::<_, time::Error>(())
    /// ```
    pub fn parse(
        input: &str,
        description: &(impl Parsable + ?Sized),
    ) -> Result<Self, error::Parse> {
        description.parse_date(input.as_bytes())
    }
}

impl fmt::Display for Date {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if cfg!(feature = "large-dates") && self.year().abs() >= 10_000 {
            write!(
                f,
                "{:+}-{:02}-{:02}",
                self.year(),
                self.month() as u8,
                self.day()
            )
        } else {
            write!(
                f,
                "{:0width$}-{:02}-{:02}",
                self.year(),
                self.month() as u8,
                self.day(),
                width = 4 + (self.year() < 0) as usize
            )
        }
    }
}
// endregion formatting & parsing

// region: trait impls
impl Add<Duration> for Date {
    type Output = Self;

    fn add(self, duration: Duration) -> Self::Output {
        self.checked_add(duration)
            .expect("overflow adding duration to date")
    }
}

impl Add<StdDuration> for Date {
    type Output = Self;

    fn add(self, duration: StdDuration) -> Self::Output {
        Self::from_julian_day(self.to_julian_day() + (duration.as_secs() / 86_400) as i32)
            .expect("overflow adding duration to date")
    }
}

impl_add_assign!(Date: Duration, StdDuration);

impl Sub<Duration> for Date {
    type Output = Self;

    fn sub(self, duration: Duration) -> Self::Output {
        self.checked_sub(duration)
            .expect("overflow subtracting duration from date")
    }
}

impl Sub<StdDuration> for Date {
    type Output = Self;

    fn sub(self, duration: StdDuration) -> Self::Output {
        Self::from_julian_day(self.to_julian_day() - (duration.as_secs() / 86_400) as i32)
            .expect("overflow subtracting duration from date")
    }
}

impl_sub_assign!(Date: Duration, StdDuration);

impl Sub for Date {
    type Output = Duration;

    fn sub(self, other: Self) -> Self::Output {
        Duration::days((self.to_julian_day() - other.to_julian_day()) as _)
    }
}
// endregion trait impls
#[cfg(test)]
mod tests_rug_37 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: i32 = 2023;
        let mut p1: u16 = 365;

        crate::date::Date::__from_ordinal_date_unchecked(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_38 {
    use super::*;
    use crate::{Date, Month};
    use std::num::NonZeroU8;

    #[test]
    fn test_rug() {
        let p0: i32 = 2019;
        let p1: Month = Month::from_number(NonZeroU8::new(1).unwrap()).unwrap();
        let p2: u8 = 1;

        assert!(Date::from_calendar_date(p0, p1, p2).is_ok());
    }

    #[test]
    fn test_rug_leap_year_fail() {
        let p0: i32 = 2019;
        let p1: Month = Month::February;
        let p2: u8 = 29;

        assert!(Date::from_calendar_date(p0, p1, p2).is_err());
    }

    #[test]
    fn test_rug_leap_year_success() {
        let p0: i32 = 2020;
        let p1: Month = Month::February;
        let p2: u8 = 29;

        assert!(Date::from_calendar_date(p0, p1, p2).is_ok());
    }

    #[test]
    fn test_rug_december() {
        let p0: i32 = 2019;
        let p1: Month = Month::December;
        let p2: u8 = 31;

        assert!(Date::from_calendar_date(p0, p1, p2).is_ok());
    }
}#[cfg(test)]
mod tests_rug_39 {
    use super::*;
    use crate::Date;
    
    #[test]
    fn test_rug() {
        let mut p0: i32 = 2019;
        let mut p1: u16 = 1;

        assert!(<Date>::from_ordinal_date(p0, p1).is_ok());

        p1 = 365;
        assert!(<Date>::from_ordinal_date(p0, p1).is_ok());

        p1 = 366;
        assert!(<Date>::from_ordinal_date(p0, p1).is_err());
    }
}#[cfg(test)]
mod tests_rug_40 {
    use super::*;
    use crate::date::Date;
    use crate::weekday::Weekday;

    #[test]
    fn test_rug() {
        let p0: i32 = 2019;
        let p1: u8 = 1;
        let p2 = Weekday::Tuesday;

        assert!(Date::from_iso_week_date(p0, p1, p2).is_ok());
    }

    #[test]
    fn test_rug_invalid() {
        let p0: i32 = 2019;
        let p1: u8 = 53;
        let p2 = Weekday::Monday;

        assert!(Date::from_iso_week_date(p0, p1, p2).is_err());
    }
}#[cfg(test)]
mod tests_rug_42 {
    use super::*;
    use crate::date::Date;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2459617; // Sample Julian day for January 1, 2022

        Date::from_julian_day_unchecked(p0);
    }
}#[cfg(test)]
mod tests_rug_43 {
    use super::*;
    use crate::{Date};

    #[test]
    fn test_year() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.year(), 2023);
    }

    #[test]
    fn test_year_edge_cases() {
        let date1: Date = Date::from_ordinal_date(2019, 1).unwrap();
        let date2: Date = Date::from_ordinal_date(2019, 365).unwrap();
        let date3: Date = Date::from_ordinal_date(2020, 1).unwrap();

        assert_eq!(date1.year(), 2019);
        assert_eq!(date2.year(), 2019);
        assert_eq!(date3.year(), 2020);
    }
}#[cfg(test)]
mod tests_rug_44 {
    use super::*;
    use crate::{Date, Month};

    #[test]
    fn test_rug() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.month(), Month::January);
    }
}#[cfg(test)]
mod tests_rug_45 {
    use super::*;
    use crate::Date;

    #[test]
    fn test_day() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.day(), 1);
    }
}#[cfg(test)]
mod tests_rug_46 {
    use super::*;
    use crate::{Date, Month};

    #[test]
    fn test_month_day() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.month_day(), (Month::January, 1));

        let p1: Date = Date::from_ordinal_date(2023, 60).unwrap();
        assert_eq!(p1.month_day(), (Month::February, 29));

        let p2: Date = Date::from_ordinal_date(2024, 60).unwrap();
        assert_eq!(p2.month_day(), (Month::February, 29));

        let p3: Date = Date::from_ordinal_date(2023, 365).unwrap();
        assert_eq!(p3.month_day(), (Month::December, 31));

        let p4: Date = Date::from_ordinal_date(2024, 366).unwrap();
        assert_eq!(p4.month_day(), (Month::December, 31));
    }
}#[cfg(test)]
mod tests_rug_47 {
    use super::*;
    use crate::Date;

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.ordinal(), 1);
    }
}#[cfg(test)]
mod tests_rug_48 {
    use super::*;
    use crate::Date;

    #[test]
    fn test_iso_year_week() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        p0.iso_year_week();
    }
}#[cfg(test)]
mod tests_rug_49 {
    use super::*;
    use crate::Date;

    #[test]
    fn test_iso_week() {
        let date1: Date = Date::from_ordinal_date(2019, 1).unwrap();
        let date2: Date = Date::from_ordinal_date(2019, 278).unwrap(); // October 4th
        let date3: Date = Date::from_ordinal_date(2020, 1).unwrap();
        let date4: Date = Date::from_ordinal_date(2020, 366).unwrap(); // December 31st
        let date5: Date = Date::from_ordinal_date(2021, 1).unwrap();

        assert_eq!(date1.iso_week(), 1);
        assert_eq!(date2.iso_week(), 40);
        assert_eq!(date3.iso_week(), 1);
        assert_eq!(date4.iso_week(), 53);
        assert_eq!(date5.iso_week(), 53);
    }
}#[cfg(test)]
mod tests_rug_50 {
    use super::*;
    use crate::Date;

    #[test]
    fn test_sunday_based_week() {
        let date1: Date = Date::from_ordinal_date(2019, 1).unwrap();
        let date2: Date = Date::from_ordinal_date(2020, 1).unwrap();
        let date3: Date = Date::from_ordinal_date(2020, 365).unwrap(); // December 31, 2020
        let date4: Date = Date::from_ordinal_date(2021, 1).unwrap();

        assert_eq!(date1.sunday_based_week(), 0);
        assert_eq!(date2.sunday_based_week(), 0);
        assert_eq!(date3.sunday_based_week(), 52);
        assert_eq!(date4.sunday_based_week(), 0);
    }
}#[cfg(test)]
mod tests_rug_51 {
    use super::*;
    use crate::{Date};

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.monday_based_week(), 0);
    }

    #[test]
    fn test_monday_based_week() {
        let date1: Date = Date::from_ordinal_date(2019, 1).unwrap();
        let date2: Date = Date::from_ordinal_date(2020, 1).unwrap();
        let date3: Date = Date::from_ordinal_date(2020, 365).unwrap(); // 2020-12-31
        let date4: Date = Date::from_ordinal_date(2021, 1).unwrap();

        assert_eq!(date1.monday_based_week(), 0);
        assert_eq!(date2.monday_based_week(), 0);
        assert_eq!(date3.monday_based_week(), 52);
        assert_eq!(date4.monday_based_week(), 0);
    }
}#[cfg(test)]
mod tests_rug_52 {
    use super::*;
    use crate::{Date, Month};

    #[test]
    fn test_rug() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.to_calendar_date(), (2023, Month::January, 1));
    }
}#[cfg(test)]
mod tests_rug_53 {
    use super::*;
    use crate::Date;

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.to_ordinal_date(), (2023, 1));
    }
}#[cfg(test)]
mod tests_rug_54 {
    use super::*;
    use crate::date::Date;
    use crate::Weekday::{Tuesday, Friday, Wednesday, Thursday};

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2019, 1).unwrap();
        assert_eq!(p0.to_iso_week_date(), (2019, 1, Tuesday));

        let p1: Date = Date::from_ordinal_date(2019, 278).unwrap(); // October 4th, 2019
        assert_eq!(p1.to_iso_week_date(), (2019, 40, Friday));

        let p2: Date = Date::from_ordinal_date(2020, 1).unwrap();
        assert_eq!(p2.to_iso_week_date(), (2020, 1, Wednesday));

        let p3: Date = Date::from_ordinal_date(2020, 365).unwrap(); // December 31st, 2020
        assert_eq!(p3.to_iso_week_date(), (2020, 53, Thursday));

        let p4: Date = Date::from_ordinal_date(2021, 1).unwrap();
        assert_eq!(p4.to_iso_week_date(), (2020, 53, Friday));
    }
}#[cfg(test)]
mod tests_rug_58 {
    use super::*;
    use crate::date::Date;

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        assert_eq!(p0.to_julian_day(), 2_459_836);
    }

    #[test]
    fn test_to_julian_day_negative_year() {
        let p0: Date = Date::from_ordinal_date(-4713, 329).unwrap();

        assert_eq!(p0.to_julian_day(), 0);
    }

    #[test]
    fn test_to_julian_day_year_2000() {
        let p0: Date = Date::from_ordinal_date(2000, 1).unwrap();

        assert_eq!(p0.to_julian_day(), 2_451_545);
    }

    #[test]
    fn test_to_julian_day_year_2019_start() {
        let p0: Date = Date::from_ordinal_date(2019, 1).unwrap();

        assert_eq!(p0.to_julian_day(), 2_458_485);
    }

    #[test]
    fn test_to_julian_day_year_2019_end() {
        let p0: Date = Date::from_ordinal_date(2019, 365).unwrap();

        assert_eq!(p0.to_julian_day(), 2_458_849);
    }
}#[cfg(test)]
mod tests_rug_59 {
    use super::*;
    use crate::date::Date;
    use crate::duration::Duration;

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: Duration = Duration::days(1);

        assert_eq!(p0.checked_add(p1), Some(Date::from_ordinal_date(2023, 2).unwrap()));

        let p2: Date = Date::MAX;
        let p3: Duration = Duration::days(1);

        assert_eq!(p2.checked_add(p3), None);

        let p4: Date = Date::MIN;
        let p5: Duration = Duration::days(-2);

        assert_eq!(p4.checked_add(p5), None);

        let p6: Date = Date::from_ordinal_date(2020, 366).unwrap();
        let p7: Duration = Duration::days(1);

        assert_eq!(p6.checked_add(p7), Some(Date::from_ordinal_date(2021, 1).unwrap()));

        let p8: Date = Date::MAX;
        let p9: Duration = Duration::hours(23);

        assert_eq!(p8.checked_add(p9), Some(Date::MAX));

        let p10: Date = Date::MIN;
        let p11: Duration = Duration::hours(-23);

        assert_eq!(p10.checked_add(p11), Some(Date::MIN));

        let p12: Date = Date::from_ordinal_date(2020, 366).unwrap();
        let p13: Duration = Duration::hours(23);

        assert_eq!(p12.checked_add(p13), Some(Date::from_ordinal_date(2020, 366).unwrap()));

        let p14: Date = Date::from_ordinal_date(2020, 366).unwrap();
        let p15: Duration = Duration::hours(47);

        assert_eq!(p14.checked_add(p15), Some(Date::from_ordinal_date(2021, 1).unwrap()));
    }
}#[cfg(test)]
mod tests_rug_60 {
    use super::*;
    use crate::Date;
    use crate::ext::NumericalDuration;

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: Duration = (-2).days();

        assert_eq!(<Date>::checked_sub(p0, p1), Some(Date::from_ordinal_date(2022, 365).unwrap()));
    }

    #[test]
    fn test_max_checked_sub() {
        let p0: Date = Date::MAX;
        let p1: Duration = (-2).days();

        assert_eq!(<Date>::checked_sub(p0, p1), None);
    }

    #[test]
    fn test_min_checked_sub() {
        let p0: Date = Date::MIN;
        let p1: Duration = 1.days();

        assert_eq!(<Date>::checked_sub(p0, p1), None);
    }

    #[test]
    fn test_date_subtraction() {
        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = 2.days();

        assert_eq!(<Date>::checked_sub(p0, p1), Some(Date::from_ordinal_date(2020, 363).unwrap()));
    }

    #[test]
    fn test_max_checked_sub_with_hours() {
        let p0: Date = Date::MAX;
        let p1: Duration = (-23).hours();

        assert_eq!(<Date>::checked_sub(p0, p1), Some(Date::MAX));
    }

    #[test]
    fn test_min_checked_sub_with_hours() {
        let p0: Date = Date::MIN;
        let p1: Duration = 23.hours();

        assert_eq!(<Date>::checked_sub(p0, p1), Some(Date::MIN));
    }

    #[test]
    fn test_date_subtraction_with_hours() {
        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = 23.hours();

        assert_eq!(<Date>::checked_sub(p0, p1), Some(Date::from_ordinal_date(2020, 365).unwrap()));
    }

    #[test]
    fn test_date_subtraction_with_hours_crossing_day() {
        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = 47.hours();

        assert_eq!(<Date>::checked_sub(p0, p1), Some(Date::from_ordinal_date(2020, 364).unwrap()));
    }
}#[cfg(test)]
mod tests_rug_61 {
    use super::*;
    use crate::{Date, ext::NumericalDuration};

    #[test]
    fn test_saturating_add() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: Duration = Duration::days(2);

        assert_eq!(p0.saturating_add(p1), Date::from_ordinal_date(2023, 3).unwrap());

        let p0: Date = Date::MAX;
        let p1: Duration = Duration::days(1);

        assert_eq!(p0.saturating_add(p1), Date::MAX);

        let p0: Date = Date::MIN;
        let p1: Duration = (-2).days();

        assert_eq!(p0.saturating_add(p1), Date::MIN);

        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = Duration::hours(47);

        assert_eq!(p0.saturating_add(p1), Date::from_ordinal_date(2021, 1).unwrap());

        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = Duration::hours(23);

        assert_eq!(p0.saturating_add(p1), Date::from_ordinal_date(2020, 365).unwrap());
    }
}#[cfg(test)]
mod tests_rug_62 {
    use super::*;
    use crate::{Date, ext::NumericalDuration};

    #[test]
    fn test_saturating_sub() {
        let p0: Date = Date::MAX;
        let p1: Duration = (-2).days();

        assert_eq!(<Date>::saturating_sub(p0, p1), Date::MAX);

        let p0: Date = Date::MIN;
        let p1: Duration = 1.days();

        assert_eq!(<Date>::saturating_sub(p0, p1), Date::MIN);

        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = 2.days();

        assert_eq!(<Date>::saturating_sub(p0, p1), Date::from_ordinal_date(2020, 363).unwrap());

        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = 23.hours();

        assert_eq!(<Date>::saturating_sub(p0, p1), Date::from_ordinal_date(2020, 365).unwrap());

        let p0: Date = Date::from_ordinal_date(2020, 365).unwrap();
        let p1: Duration = 47.hours();

        assert_eq!(<Date>::saturating_sub(p0, p1), Date::from_ordinal_date(2020, 364).unwrap());
    }
}#[cfg(test)]
mod tests_rug_63 {
    use super::*;
    use crate::{Date, PrimitiveDateTime};

    #[test]
    fn test_midnight() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();

        let result: PrimitiveDateTime = p0.midnight();
        assert_eq!(result, PrimitiveDateTime::new(p0, Time::MIDNIGHT));
    }
}#[cfg(test)]
mod tests_rug_64 {
    use super::*;
    use crate::date::Date;
    use crate::time::Time;
    use crate::primitive_date_time::PrimitiveDateTime;

    #[test]
    fn test_rug() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let mut p1: Time = Time::__from_hms_nanos_unchecked(12, 30, 45, 678_901_234);

        let result: PrimitiveDateTime = p0.with_time(p1);
        
        assert_eq!(result, PrimitiveDateTime::new(p0, p1));
    }
}#[cfg(test)]
mod tests_rug_65 {
    use super::*;
    use crate::date::Date;
    use crate::error::ComponentRange;

    #[test]
    fn test_with_hms() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: u8 = 12; // Sample hour
        let p2: u8 = 34; // Sample minute
        let p3: u8 = 56; // Sample second

        assert!(p0.with_hms(p1, p2, p3).is_ok());
        assert!(p0.with_hms(24, 0, 0).is_err());
    }
}#[cfg(test)]
mod tests_rug_66 {
    use super::*;
    use crate::{Date, PrimitiveDateTime};

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: u8 = 12;
        let p2: u8 = 34;
        let p3: u8 = 56;
        let p4: u16 = 789;

        assert!(p0.with_hms_milli(p1, p2, p3, p4).is_ok());
    }

    #[test]
    fn test_rug_invalid_hour() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: u8 = 24;
        let p2: u8 = 34;
        let p3: u8 = 56;
        let p4: u16 = 789;

        assert!(p0.with_hms_milli(p1, p2, p3, p4).is_err());
    }
}#[cfg(test)]
mod tests_rug_67 {
    use super::*;
    use crate::Date;
    
    #[test]
    fn test_rug() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let mut p1: u8 = 12;
        let mut p2: u8 = 34;
        let mut p3: u8 = 56;
        let mut p4: u32 = 789_012;

        assert!(<Date>::with_hms_micro(p0, p1, p2, p3, p4).is_ok());
    }
}#[cfg(test)]
mod tests_rug_68 {
    use super::*;
    use crate::date::Date;
    use crate::error::ComponentRange;

    #[test]
    fn test_rug() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: u8 = 12;
        let p2: u8 = 34;
        let p3: u8 = 56;
        let p4: u32 = 789_012_345;

        assert!(<Date>::with_hms_nano(p0, p1, p2, p3, p4).is_ok());

        // Test invalid hour
        let p0_invalid_hour: Date = Date::from_ordinal_date(2023, 1).unwrap();
        assert!(<Date>::with_hms_nano(p0_invalid_hour, 24, p2, p3, p4).is_err());

        // Test invalid minute
        let p0_invalid_minute: Date = Date::from_ordinal_date(2023, 1).unwrap();
        assert!(<Date>::with_hms_nano(p0_invalid_minute, p1, 60, p3, p4).is_err());

        // Test invalid second
        let p0_invalid_second: Date = Date::from_ordinal_date(2023, 1).unwrap();
        assert!(<Date>::with_hms_nano(p0_invalid_second, p1, p2, 60, p4).is_err());

        // Test invalid nanosecond
        let p0_invalid_nanosecond: Date = Date::from_ordinal_date(2023, 1).unwrap();
        assert!(<Date>::with_hms_nano(p0_invalid_nanosecond, p1, p2, p3, 1_000_000_000).is_err());
    }
}#[cfg(test)]
mod tests_rug_69 {
    use super::*;
    use crate::date::Date;
    use crate::duration::Duration;
    use std::ops::Add;

    #[test]
    fn test_rug() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let mut p1: Duration = Duration::seconds(5);

        p0.add(p1);
    }
}#[cfg(test)]
mod tests_rug_70 {
    use super::*;
    use crate::date::Date;
    use std::ops::Add;
    use std::time::Duration;

    #[test]
    fn test_add() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: Duration = Duration::new(3600, 123_456_789);

        p0.add(p1);
    }
}#[cfg(test)]
mod tests_rug_71 {
    use super::*;
    use crate::date::Date;
    use crate::duration::Duration;
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let mut p1: Duration = Duration::seconds(5);

        <Date as Sub<Duration>>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_72 {
    use super::*;
    use crate::date::Date;
    use std::ops::Sub;
    use std::time::Duration;

    #[test]
    fn test_sub() {
        let p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let p1: Duration = Duration::new(3600, 123_456_789);

        <Date>::sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_73 {
    use super::*;
    use crate::date::Date;
    use std::ops::Sub;

    #[test]
    fn test_rug() {
        let mut p0: Date = Date::from_ordinal_date(2023, 1).unwrap();
        let mut p1: Date = Date::from_ordinal_date(2023, 1).unwrap();

        <Date>::sub(p0, p1);
    }
}