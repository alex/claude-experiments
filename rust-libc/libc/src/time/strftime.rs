//! `strftime(3)`.

use super::Tm;
use super::calendar::{MON_FULL, MON_NAMES, WDAY_FULL, WDAY_NAMES, days_from_civil};
use crate::c_char;
use core::fmt::Write;

/// Output buffer that fails once full (C requires 0 to be returned when
/// the result does not fit).
struct Out<'a> {
    buf: &'a mut [u8],
    len: usize,
}

impl Write for Out<'_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        if s.len() > self.buf.len() - self.len {
            return Err(core::fmt::Error);
        }
        self.buf[self.len..self.len + s.len()].copy_from_slice(s.as_bytes());
        self.len += s.len();
        Ok(())
    }
}

/// ISO 8601 week-based year and week number.
fn iso_week(tm: &Tm) -> (i64, u32) {
    let year = tm.tm_year as i64 + 1900;
    let wday = (tm.tm_wday as i64 + 6) % 7; // Monday = 0
    let yday = tm.tm_yday as i64;
    // Thursday of the current week decides the year.
    let thursday = yday - wday + 3;
    let (y, thursday) = if thursday < 0 {
        let prev_days = if super::calendar::is_leap(year - 1) {
            366
        } else {
            365
        };
        (year - 1, thursday + prev_days)
    } else {
        let days = if super::calendar::is_leap(year) {
            366
        } else {
            365
        };
        if thursday >= days {
            (year + 1, thursday - days)
        } else {
            (year, thursday)
        }
    };
    (y, (thursday / 7 + 1) as u32)
}

/// Formats `tm` per `fmt` into `buf`; returns the length, or `None` if it
/// does not fit.
pub fn format(buf: &mut [u8], fmt: &[u8], tm: &Tm) -> Option<usize> {
    let mut out = Out { buf, len: 0 };
    let mut i = 0;
    while i < fmt.len() {
        let c = fmt[i];
        i += 1;
        if c != b'%' {
            out.write_str(core::str::from_utf8(&[c]).unwrap_or("?"))
                .ok()?;
            continue;
        }
        // Skip the E and O modifiers.
        while i < fmt.len() && matches!(fmt[i], b'E' | b'O') {
            i += 1;
        }
        let spec = *fmt.get(i)?;
        i += 1;
        let year = tm.tm_year as i64 + 1900;
        let name = |names: &'static [&'static str], idx: i32| -> &'static str {
            usize::try_from(idx)
                .ok()
                .and_then(|i| names.get(i).copied())
                .unwrap_or("?")
        };
        match spec {
            b'a' => out.write_str(name(&WDAY_NAMES, tm.tm_wday)).ok()?,
            b'A' => out.write_str(name(&WDAY_FULL, tm.tm_wday)).ok()?,
            b'b' | b'h' => out.write_str(name(&MON_NAMES, tm.tm_mon)).ok()?,
            b'B' => out.write_str(name(&MON_FULL, tm.tm_mon)).ok()?,
            b'c' => write!(
                out,
                "{} {} {:2} {:02}:{:02}:{:02} {}",
                name(&WDAY_NAMES, tm.tm_wday),
                name(&MON_NAMES, tm.tm_mon),
                tm.tm_mday,
                tm.tm_hour,
                tm.tm_min,
                tm.tm_sec,
                year
            )
            .ok()?,
            b'C' => write!(out, "{:02}", year.div_euclid(100)).ok()?,
            b'd' => write!(out, "{:02}", tm.tm_mday).ok()?,
            b'D' => write!(
                out,
                "{:02}/{:02}/{:02}",
                tm.tm_mon as i64 + 1,
                tm.tm_mday,
                year.rem_euclid(100)
            )
            .ok()?,
            b'e' => write!(out, "{:2}", tm.tm_mday).ok()?,
            b'F' => write!(out, "{}-{:02}-{:02}", year, tm.tm_mon as i64 + 1, tm.tm_mday).ok()?,
            b'G' => write!(out, "{}", iso_week(tm).0).ok()?,
            b'g' => write!(out, "{:02}", iso_week(tm).0.rem_euclid(100)).ok()?,
            b'H' => write!(out, "{:02}", tm.tm_hour).ok()?,
            b'I' => write!(out, "{:02}", (tm.tm_hour as i64 + 11).rem_euclid(12) + 1).ok()?,
            b'j' => write!(out, "{:03}", tm.tm_yday as i64 + 1).ok()?,
            b'k' => write!(out, "{:2}", tm.tm_hour).ok()?,
            b'l' => write!(out, "{:2}", (tm.tm_hour as i64 + 11).rem_euclid(12) + 1).ok()?,
            b'm' => write!(out, "{:02}", tm.tm_mon as i64 + 1).ok()?,
            b'M' => write!(out, "{:02}", tm.tm_min).ok()?,
            b'n' => out.write_str("\n").ok()?,
            b'p' => out
                .write_str(if tm.tm_hour < 12 { "AM" } else { "PM" })
                .ok()?,
            b'P' => out
                .write_str(if tm.tm_hour < 12 { "am" } else { "pm" })
                .ok()?,
            b'r' => write!(
                out,
                "{:02}:{:02}:{:02} {}",
                (tm.tm_hour as i64 + 11).rem_euclid(12) + 1,
                tm.tm_min,
                tm.tm_sec,
                if tm.tm_hour < 12 { "AM" } else { "PM" }
            )
            .ok()?,
            b'R' => write!(out, "{:02}:{:02}", tm.tm_hour, tm.tm_min).ok()?,
            b's' => write!(out, "{}", super::calendar::from_tm(tm).unwrap_or(0)).ok()?,
            b'S' => write!(out, "{:02}", tm.tm_sec).ok()?,
            b't' => out.write_str("\t").ok()?,
            b'T' => write!(out, "{:02}:{:02}:{:02}", tm.tm_hour, tm.tm_min, tm.tm_sec).ok()?,
            b'u' => write!(out, "{}", (tm.tm_wday as i64 + 6).rem_euclid(7) + 1).ok()?,
            b'U' => write!(out, "{:02}", (tm.tm_yday as i64 + 7 - tm.tm_wday as i64) / 7).ok()?,
            b'V' => write!(out, "{:02}", iso_week(tm).1).ok()?,
            b'w' => write!(out, "{}", tm.tm_wday).ok()?,
            b'W' => write!(out, "{:02}", (tm.tm_yday as i64 + 7 - (tm.tm_wday as i64 + 6).rem_euclid(7)) / 7).ok()?,
            b'x' => write!(
                out,
                "{:02}/{:02}/{:02}",
                tm.tm_mon as i64 + 1,
                tm.tm_mday,
                year.rem_euclid(100)
            )
            .ok()?,
            b'X' => write!(out, "{:02}:{:02}:{:02}", tm.tm_hour, tm.tm_min, tm.tm_sec).ok()?,
            b'y' => write!(out, "{:02}", year.rem_euclid(100)).ok()?,
            b'Y' => write!(out, "{}", year).ok()?,
            b'z' => {
                let off = tm.tm_gmtoff;
                let sign = if off < 0 { '-' } else { '+' };
                let off = off.unsigned_abs();
                write!(out, "{sign}{:02}{:02}", off / 3600, off % 3600 / 60).ok()?
            }
            b'Z' => {
                if tm.tm_zone.is_null() {
                    out.write_str("UTC").ok()?
                } else {
                    // SAFETY: tm_zone points to a NUL-terminated string.
                    let len = unsafe { crate::string::search::strlen(tm.tm_zone as *const u8) };
                    // SAFETY: as above.
                    let s = unsafe { core::slice::from_raw_parts(tm.tm_zone as *const u8, len) };
                    out.write_str(core::str::from_utf8(s).unwrap_or("?")).ok()?
                }
            }
            b'%' => out.write_str("%").ok()?,
            _ => {
                out.write_str("%").ok()?;
                out.write_str(core::str::from_utf8(&[spec]).unwrap_or("?"))
                    .ok()?
            }
        }
    }
    let _ = days_from_civil;
    Some(out.len)
}

/// `strftime(3)`.
///
/// # Safety
/// `buf` must be valid for `max` bytes; `fmt` NUL-terminated; `tm` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strftime(
    buf: *mut c_char,
    max: usize,
    fmt: *const c_char,
    tm: *const Tm,
) -> usize {
    if max == 0 {
        return 0;
    }
    // SAFETY: caller contract.
    let (out, fmt, tm) = unsafe {
        (
            core::slice::from_raw_parts_mut(buf as *mut u8, max),
            core::slice::from_raw_parts(
                fmt as *const u8,
                crate::string::search::strlen(fmt as *const u8),
            ),
            &*tm,
        )
    };
    // The text may fill all but the last byte, which holds the NUL.
    match format(&mut out[..max - 1], fmt, tm) {
        Some(len) => {
            out[len] = 0;
            len
        }
        None => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(t: i64, f: &str) -> String {
        let tm = super::super::calendar::to_tm(t).unwrap();
        let mut buf = [0u8; 128];
        let n = format(&mut buf, f.as_bytes(), &tm).unwrap();
        String::from_utf8(buf[..n].to_vec()).unwrap()
    }

    #[test]
    fn conversions() {
        let t = 1_700_000_000; // Tue Nov 14 22:13:20 2023
        assert_eq!(fmt(t, "%Y-%m-%d %H:%M:%S"), "2023-11-14 22:13:20");
        assert_eq!(fmt(t, "%a %A %b %B %h"), "Tue Tuesday Nov November Nov");
        assert_eq!(fmt(t, "%c"), "Tue Nov 14 22:13:20 2023");
        assert_eq!(fmt(t, "%C %y %j %e %I %p %P"), "20 23 318 14 10 PM pm");
        assert_eq!(
            fmt(t, "%D|%F|%T|%R|%r"),
            "11/14/23|2023-11-14|22:13:20|22:13|10:13:20 PM"
        );
        assert_eq!(fmt(t, "%u %w %U %W %V %G %g"), "2 2 46 46 46 2023 23");
        assert_eq!(fmt(t, "%s %z %Z %% %n%t"), "1700000000 +0000 UTC % \n\t");
        assert_eq!(fmt(t, "%k|%l"), "22|10");
        assert_eq!(fmt(0, "%c %V %G"), "Thu Jan  1 00:00:00 1970 01 1970");
        // 2021-01-01 is in ISO week 53 of 2020.
        assert_eq!(fmt(1_609_459_200, "%V %G %U %W"), "53 2020 00 00");
        let tm = super::super::calendar::to_tm(t).unwrap();
        let mut small = [0u8; 4];
        assert_eq!(format(&mut small, b"%Y-%m", &tm), None);
    }
}
