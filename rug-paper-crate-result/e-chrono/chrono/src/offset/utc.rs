// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The UTC (Coordinated Universal Time) time zone.

use core::fmt;
#[cfg(all(
    feature = "clock",
    not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))
))]
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Deserialize, Serialize};

use super::{FixedOffset, LocalResult, Offset, TimeZone};
use crate::naive::{NaiveDate, NaiveDateTime};
#[cfg(feature = "clock")]
#[allow(deprecated)]
use crate::{Date, DateTime};

/// The UTC time zone. This is the most efficient time zone when you don't need the local time.
/// It is also used as an offset (which is also a dummy type).
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the UTC struct is the preferred way to construct `DateTime<Utc>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{DateTime, TimeZone, NaiveDateTime, Utc};
///
/// let dt = DateTime::<Utc>::from_utc(NaiveDateTime::from_timestamp_opt(61, 0).unwrap(), Utc);
///
/// assert_eq!(Utc.timestamp_opt(61, 0).unwrap(), dt);
/// assert_eq!(Utc.with_ymd_and_hms(1970, 1, 1, 0, 1, 1).unwrap(), dt);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "rkyv", derive(Archive, Deserialize, Serialize))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Utc;

#[cfg(feature = "clock")]
#[cfg_attr(docsrs, doc(cfg(feature = "clock")))]
impl Utc {
    /// Returns a `Date` which corresponds to the current date.
    #[deprecated(
        since = "0.4.23",
        note = "use `Utc::now()` instead, potentially with `.date_naive()`"
    )]
    #[allow(deprecated)]
    #[must_use]
    pub fn today() -> Date<Utc> {
        Utc::now().date()
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    #[must_use]
    pub fn now() -> DateTime<Utc> {
        let now =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        let naive =
            NaiveDateTime::from_timestamp_opt(now.as_secs() as i64, now.subsec_nanos()).unwrap();
        DateTime::from_utc(naive, Utc)
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    #[must_use]
    pub fn now() -> DateTime<Utc> {
        let now = js_sys::Date::new_0();
        DateTime::<Utc>::from(now)
    }
}

impl TimeZone for Utc {
    type Offset = Utc;

    fn from_offset(_state: &Utc) -> Utc {
        Utc
    }

    fn offset_from_local_date(&self, _local: &NaiveDate) -> LocalResult<Utc> {
        LocalResult::Single(Utc)
    }
    fn offset_from_local_datetime(&self, _local: &NaiveDateTime) -> LocalResult<Utc> {
        LocalResult::Single(Utc)
    }

    fn offset_from_utc_date(&self, _utc: &NaiveDate) -> Utc {
        Utc
    }
    fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> Utc {
        Utc
    }
}

impl Offset for Utc {
    fn fix(&self) -> FixedOffset {
        FixedOffset::east_opt(0).unwrap()
    }
}

impl fmt::Debug for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Z")
    }
}

impl fmt::Display for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "UTC")
    }
}
#[cfg(test)]
mod tests_rug_580 {
    use crate::{offset::Utc, Date};

    #[test]
    fn test_today() {
        let today_date: Date<Utc> = Utc::today();
        
        // Example assertion to check if the returned date is indeed today
        assert_eq!(today_date, Utc::now().date());
    }
}#[cfg(test)]
mod tests_rug_581 {
    use super::*;
    use crate::{DateTime, NaiveDateTime, Utc};
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn test_rug() {
        let now: SystemTime = SystemTime::now();
        let duration_since_epoch: std::time::Duration = now.duration_since(UNIX_EPOCH).expect("system time before Unix epoch");
        let secs: i64 = duration_since_epoch.as_secs() as i64;
        let nanos: u32 = duration_since_epoch.subsec_nanos();
        let naive_datetime: NaiveDateTime = NaiveDateTime::from_timestamp_opt(secs, nanos).unwrap();
        let datetime_utc: DateTime<Utc> = DateTime::from_utc(naive_datetime, Utc);

        // The actual test assertion can be something like this
        assert_eq!(datetime_utc.timezone(), Utc);
    }
}#[cfg(test)]
mod tests_rug_582 {
    use super::*;
    use crate::{offset::utc::Utc, TimeZone};

    #[test]
    fn test_rug() {
        let mut p0: &Utc = &Utc;

        <Utc as TimeZone>::from_offset(p0);
    }
}#[cfg(test)]
mod tests_rug_583 {
    use super::*;
    use crate::{NaiveDate, offset::utc::Utc, TimeZone};

    #[test]
    fn test_rug() {
        let p0 = Utc;
        let p1 = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap();

        <Utc as TimeZone>::offset_from_local_date(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_584 {
    use super::*;
    use crate::TimeZone;
    use crate::{NaiveDate, NaiveTime, offset::utc::Utc};

    #[test]
    fn test_rug() {
        let p0 = Utc;
        let p1 = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        <Utc>::offset_from_local_datetime(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_585 {
    use super::*;
    use crate::TimeZone;
    use crate::{NaiveDate, offset::Utc};

    #[test]
    fn test_rug() {
        let p0 = Utc;
        let p1 = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap();

        <Utc as TimeZone>::offset_from_utc_date(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_586 {
    use super::*;
    use crate::TimeZone;
    use crate::{naive::{NaiveDate, NaiveTime}, offset::Utc};

    #[test]
    fn test_rug() {
        let p0 = Utc;
        let p1: NaiveDateTime = NaiveDate::from_ymd_opt(2023, 10, 5).unwrap().and_hms_opt(14, 30, 0).unwrap();

        <Utc as TimeZone>::offset_from_utc_datetime(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_587 {
    use super::*;
    use crate::offset::{Offset, Utc};
    use crate::Date;
    use crate::TimeZone;

    #[test]
    fn test_rug() {
        let mut p0 = Utc;

        let _result: FixedOffset = <Utc as Offset>::fix(&p0);
    }
}