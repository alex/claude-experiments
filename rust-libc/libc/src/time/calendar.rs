//! Conversions between `time_t` and broken-down UTC time.
//!
//! Uses Howard Hinnant's `days_from_civil` / `civil_from_days`, which are
//! exact for the whole 64-bit range without loops.

use super::Tm;
use core::ffi::c_int;

/// Day names for `%a`/`%A`.
pub static WDAY_NAMES: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
/// Full day names.
pub static WDAY_FULL: [&str; 7] = [
    "Sunday",
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
];
/// Month names for `%b`/`%B`.
pub static MON_NAMES: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
];
/// Full month names.
pub static MON_FULL: [&str; 12] = [
    "January",
    "February",
    "March",
    "April",
    "May",
    "June",
    "July",
    "August",
    "September",
    "October",
    "November",
    "December",
];

/// Days since 1970-01-01 of the given civil date (month 1..=12).
pub fn days_from_civil(y: i64, m: u32, d: u32) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y.rem_euclid(400) as u64;
    let mp = (m as u64 + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d as u64 - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe as i64 - 719_468
}

/// Civil date (year, month 1..=12, day) of a day count since 1970-01-01.
pub fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// Whether `y` is a leap year.
pub fn is_leap(y: i64) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

/// Converts seconds since the epoch to broken-down UTC time. Returns
/// `None` if the year does not fit in an `int`.
pub fn to_tm(t: i64) -> Option<Tm> {
    let days = t.div_euclid(86_400);
    let secs = t.rem_euclid(86_400);
    let (y, m, d) = civil_from_days(days);
    let year = c_int::try_from(y - 1900).ok()?;
    let yday = days - days_from_civil(y, 1, 1);
    Some(Tm {
        tm_sec: (secs % 60) as c_int,
        tm_min: (secs / 60 % 60) as c_int,
        tm_hour: (secs / 3600) as c_int,
        tm_mday: d as c_int,
        tm_mon: m as c_int - 1,
        tm_year: year,
        tm_wday: (days + 4).rem_euclid(7) as c_int,
        tm_yday: yday as c_int,
        tm_isdst: 0,
        tm_gmtoff: 0,
        tm_zone: super::UTC.as_ptr() as *const crate::c_char,
    })
}

/// Converts broken-down time (possibly with out-of-range fields, which
/// are normalised arithmetically) to seconds since the epoch.
pub fn from_tm(tm: &Tm) -> Option<i64> {
    let year = tm.tm_year as i64 + 1900;
    let mon = tm.tm_mon as i64;
    let year = year.checked_add(mon.div_euclid(12))?;
    let mon = mon.rem_euclid(12) as u32 + 1;
    let days = days_from_civil(year, mon, 1).checked_add(tm.tm_mday as i64 - 1)?;
    days.checked_mul(86_400)?
        .checked_add((tm.tm_hour as i64).checked_mul(3600)?)?
        .checked_add((tm.tm_min as i64).checked_mul(60)?)?
        .checked_add(tm.tm_sec as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn epoch_and_known_dates() {
        let tm = to_tm(0).unwrap();
        assert_eq!(
            (tm.tm_year, tm.tm_mon, tm.tm_mday, tm.tm_wday, tm.tm_yday),
            (70, 0, 1, 4, 0)
        );
        let tm = to_tm(951_782_400).unwrap(); // 2000-02-29 00:00:00 UTC
        assert_eq!(
            (tm.tm_year, tm.tm_mon, tm.tm_mday, tm.tm_wday, tm.tm_yday),
            (100, 1, 29, 2, 59)
        );
        let tm = to_tm(-1).unwrap();
        assert_eq!(
            (
                tm.tm_year, tm.tm_mon, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec
            ),
            (69, 11, 31, 23, 59, 59)
        );
        let tm = to_tm(1_700_000_000).unwrap(); // 2023-11-14 22:13:20 UTC
        assert_eq!(
            (
                tm.tm_year, tm.tm_mon, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec, tm.tm_wday
            ),
            (123, 10, 14, 22, 13, 20, 2)
        );
        assert!(to_tm(i64::MAX).is_none());
    }

    #[test]
    fn round_trips_and_normalisation() {
        for t in [
            0i64,
            1,
            -1,
            86_399,
            86_400,
            951_782_400,
            1_700_000_000,
            -2_208_988_800,
            253_402_300_799,
            -62_135_596_800,
        ] {
            let tm = to_tm(t).unwrap();
            assert_eq!(from_tm(&tm), Some(t), "{t}");
        }
        // Month 13 of 2023 is January 2024; day 0 is the last day of the
        // previous month.
        let tm = Tm {
            tm_year: 123,
            tm_mon: 13,
            tm_mday: 0,
            ..Tm::default()
        };
        let t = from_tm(&tm).unwrap();
        let n = to_tm(t).unwrap();
        assert_eq!((n.tm_year, n.tm_mon, n.tm_mday), (124, 0, 31));
        assert!(is_leap(2000) && !is_leap(1900) && is_leap(2024) && !is_leap(2023));
    }
}
