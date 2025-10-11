//! The `Month` enum and its associated `impl`s.

use core::convert::TryFrom;
use core::fmt;
use core::num::NonZeroU8;

use self::Month::*;
use crate::error;

/// Months of the year.
#[allow(clippy::missing_docs_in_private_items)] // variants
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Month {
    January = 1,
    February = 2,
    March = 3,
    April = 4,
    May = 5,
    June = 6,
    July = 7,
    August = 8,
    September = 9,
    October = 10,
    November = 11,
    December = 12,
}

impl Month {
    /// Create a `Month` from its numerical value.
    pub(crate) const fn from_number(n: NonZeroU8) -> Result<Self, error::ComponentRange> {
        match n.get() {
            1 => Ok(January),
            2 => Ok(February),
            3 => Ok(March),
            4 => Ok(April),
            5 => Ok(May),
            6 => Ok(June),
            7 => Ok(July),
            8 => Ok(August),
            9 => Ok(September),
            10 => Ok(October),
            11 => Ok(November),
            12 => Ok(December),
            n => Err(error::ComponentRange {
                name: "month",
                minimum: 1,
                maximum: 12,
                value: n as _,
                conditional_range: false,
            }),
        }
    }

    /// Get the previous month.
    ///
    /// ```rust
    /// # use time::Month;
    /// assert_eq!(Month::January.previous(), Month::December);
    /// ```
    pub const fn previous(self) -> Self {
        match self {
            January => December,
            February => January,
            March => February,
            April => March,
            May => April,
            June => May,
            July => June,
            August => July,
            September => August,
            October => September,
            November => October,
            December => November,
        }
    }

    /// Get the next month.
    ///
    /// ```rust
    /// # use time::Month;
    /// assert_eq!(Month::January.next(), Month::February);
    /// ```
    pub const fn next(self) -> Self {
        match self {
            January => February,
            February => March,
            March => April,
            April => May,
            May => June,
            June => July,
            July => August,
            August => September,
            September => October,
            October => November,
            November => December,
            December => January,
        }
    }
}

impl fmt::Display for Month {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            January => "January",
            February => "February",
            March => "March",
            April => "April",
            May => "May",
            June => "June",
            July => "July",
            August => "August",
            September => "September",
            October => "October",
            November => "November",
            December => "December",
        })
    }
}

impl From<Month> for u8 {
    fn from(month: Month) -> Self {
        month as _
    }
}

impl TryFrom<u8> for Month {
    type Error = error::ComponentRange;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match NonZeroU8::new(value) {
            Some(value) => Self::from_number(value),
            None => Err(error::ComponentRange {
                name: "month",
                minimum: 1,
                maximum: 12,
                value: 0,
                conditional_range: false,
            }),
        }
    }
}
#[cfg(test)]
mod tests_rug_231 {
    use super::*;
    use crate::month::{Month, error::ComponentRange};
    use std::num::NonZeroU8;

    #[test]
    fn test_rug() {
        let valid_month = NonZeroU8::new(1).unwrap();
        let invalid_month = NonZeroU8::new(42).unwrap();

        assert_eq!(Month::from_number(valid_month), Ok(Month::January));
        assert_eq!(
            Month::from_number(invalid_month),
            Err(ComponentRange {
                name: "month",
                minimum: 1,
                maximum: 12,
                value: 42,
                conditional_range: false,
            })
        );
    }
}#[cfg(test)]
mod tests_rug_232 {
    use super::*;
    use std::num::NonZeroU8;
    use crate::Month;

    #[test]
    fn test_rug() {
        let p0: Month = Month::from_number(NonZeroU8::new(1).unwrap()).unwrap();

        assert_eq!(p0.previous(), Month::December);
    }
}#[cfg(test)]
mod tests_rug_233 {
    use super::*;
    use std::num::NonZeroU8;
    use crate::Month;

    #[test]
    fn test_rug() {
        let mut p0: Month = Month::from_number(NonZeroU8::new(1).unwrap()).unwrap();

        assert_eq!(p0.next(), Month::February);
    }
}#[cfg(test)]
mod tests_rug_235 {
    use super::*;
    use std::convert::TryFrom;
    use crate::error; // Assuming the error module is in the same crate
    use crate::month::Month; // Assuming the Month struct is in the month module

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;

        assert_eq!(<Month as TryFrom<u8>>::try_from(p0).unwrap(), Month::May);

        let p1: u8 = 0;
        assert_eq!(
            <Month as TryFrom<u8>>::try_from(p1),
            Err(error::ComponentRange {
                name: "month",
                minimum: 1,
                maximum: 12,
                value: 0,
                conditional_range: false,
            })
        );

        let p2: u8 = 13;
        assert_eq!(
            <Month as TryFrom<u8>>::try_from(p2),
            Err(error::ComponentRange {
                name: "month",
                minimum: 1,
                maximum: 12,
                value: 13,
                conditional_range: false,
            })
        );
    }
}