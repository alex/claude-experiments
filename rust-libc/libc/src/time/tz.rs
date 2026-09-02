//! Time zones: the `TZ` variable, TZif files and POSIX rule strings.
//!
//! `tzset` resolves `TZ` (unset: `/etc/localtime`; `:path` or a zone
//! name under `/usr/share/zoneinfo`; otherwise a POSIX rule such as
//! `EST5EDT,M3.2.0,M11.1.0`) into a table of transitions plus a rule for
//! the years beyond the table, cached until `TZ` changes. `localtime` and
//! `mktime` consult that cache. Zone files are parsed with bounds checks
//! everywhere; a bad file simply yields UTC.

use crate::c_char;
use crate::sync::Mutex;
use crate::sys;
use crate::time::calendar;

/// Transitions kept from a zone file (the most recent ones win if a file
/// has more).
const MAX_TRANS: usize = 2048;
const MAX_TYPES: usize = 64;
const MAX_ABBR: usize = 512;
const MAX_TZ: usize = 256;
const SECS_PER_DAY: i64 = 86_400;

/// One local-time type: UTC offset (seconds east), DST flag, abbreviation
/// (offset into `abbr`).
#[derive(Clone, Copy, Default)]
struct Ttype {
    utoff: i32,
    isdst: bool,
    abbr: u16,
}

/// A date in a POSIX transition rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RuleDate {
    /// `Jn`: day `1..=365`, February 29 never counted.
    Julian(u16),
    /// `n`: day `0..=365`, February 29 counted.
    Zero(u16),
    /// `Mm.w.d`: the `w`th (`5` = last) weekday `d` of month `m`.
    Mwd(u8, u8, u8),
}

/// A POSIX rule: standard time and, optionally, daylight time with its
/// transition dates (local seconds after midnight).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rule {
    std_abbr: u16,
    std_off: i32,
    dst: Option<Dst>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Dst {
    abbr: u16,
    off: i32,
    start: (RuleDate, i32),
    end: (RuleDate, i32),
}

/// The cached zone.
pub struct Zone {
    /// The `TZ` value this was built from (`len == usize::MAX`: unset).
    tz: [u8; MAX_TZ],
    tz_len: usize,
    trans: [i64; MAX_TRANS],
    idx: [u8; MAX_TRANS],
    ntrans: usize,
    types: [Ttype; MAX_TYPES],
    ntypes: usize,
    abbr: [u8; MAX_ABBR],
    nabbr: usize,
    rule: Option<Rule>,
    loaded: bool,
}

// SAFETY: guarded by the mutex.
unsafe impl Send for Zone {}

static ZONE: Mutex<Zone> = Mutex::new(Zone {
    tz: [0; MAX_TZ],
    tz_len: 0,
    trans: [0; MAX_TRANS],
    idx: [0; MAX_TRANS],
    ntrans: 0,
    types: [Ttype {
        utoff: 0,
        isdst: false,
        abbr: 0,
    }; MAX_TYPES],
    ntypes: 0,
    abbr: [0; MAX_ABBR],
    nabbr: 0,
    rule: None,
    loaded: false,
});

/// What `localtime` needs for one instant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Local {
    /// Seconds east of UTC.
    pub gmtoff: i64,
    /// Daylight saving in effect.
    pub isdst: bool,
    /// Abbreviation, NUL-terminated, in stable storage.
    pub zone: *const c_char,
}

impl Zone {
    fn reset_utc(&mut self) {
        self.ntrans = 0;
        self.ntypes = 1;
        self.types[0] = Ttype {
            utoff: 0,
            isdst: false,
            abbr: 0,
        };
        self.abbr[..4].copy_from_slice(b"UTC\0");
        self.nabbr = 4;
        self.rule = None;
    }

    /// Appends a NUL-terminated abbreviation, returning its offset.
    fn add_abbr(&mut self, s: &[u8]) -> Option<u16> {
        if self.nabbr + s.len() + 1 > MAX_ABBR {
            return None;
        }
        let off = self.nabbr;
        self.abbr[off..off + s.len()].copy_from_slice(s);
        self.abbr[off + s.len()] = 0;
        self.nabbr += s.len() + 1;
        Some(off as u16)
    }

    fn abbr_ptr(&self, off: u16) -> *const c_char {
        // The pointer into the static table stays valid until the next
        // `tzset`, as POSIX allows.
        self.abbr[(off as usize).min(MAX_ABBR - 1)..].as_ptr() as *const c_char
    }

    /// Reloads if `TZ` changed.
    fn ensure(&mut self) {
        let mut tz = [0u8; MAX_TZ];
        // SAFETY: NUL-terminated literal; the value is copied under the
        // lock before anyone can change the environment again... except
        // that `setenv` from another thread is a caller's race, as in
        // every libc.
        let val = unsafe { crate::stdlib::env::getenv(c"TZ".as_ptr()) };
        let tz_len = if val.is_null() {
            usize::MAX
        } else {
            // SAFETY: NUL-terminated.
            let n = unsafe { crate::string::search::strlen(val as *const u8) }.min(MAX_TZ);
            // SAFETY: `n` bytes are readable.
            tz[..n].copy_from_slice(unsafe { core::slice::from_raw_parts(val as *const u8, n) });
            n
        };
        if self.loaded
            && tz_len == self.tz_len
            && (tz_len == usize::MAX || tz[..tz_len] == self.tz[..tz_len])
        {
            return;
        }
        self.tz = tz;
        self.tz_len = tz_len;
        self.loaded = true;
        self.reset_utc();
        let spec: &[u8] = if tz_len == usize::MAX {
            b""
        } else {
            &tz[..tz_len]
        };
        self.load(spec);
    }

    /// Loads the zone described by `spec` (the `TZ` value, or empty when
    /// unset).
    fn load(&mut self, spec: &[u8]) {
        let mut path = [0u8; 300];
        let file: Option<&[u8]> = if spec.is_empty() {
            Some(b"/etc/localtime")
        } else if let Some(p) = spec.strip_prefix(b":") {
            Some(p)
        } else if spec
            .first()
            .is_some_and(|b| b.is_ascii_alphabetic() || *b == b'<')
            && self.try_rule(spec)
        {
            None
        } else {
            Some(spec)
        };
        let Some(file) = file else {
            return;
        };
        let full: &[u8] = if file.starts_with(b"/") {
            file
        } else {
            // A zone name: no `..` components, nothing hidden.
            if file.is_empty()
                || file.len() > 200
                || file
                    .split(|&b| b == b'/')
                    .any(|c| c.is_empty() || c.starts_with(b"."))
                || !file
                    .iter()
                    .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'/' | b'_' | b'-' | b'+'))
            {
                return;
            }
            let prefix = b"/usr/share/zoneinfo/";
            path[..prefix.len()].copy_from_slice(prefix);
            path[prefix.len()..prefix.len() + file.len()].copy_from_slice(file);
            &path[..prefix.len() + file.len()]
        };
        let mut cpath = [0u8; 301];
        if full.len() >= cpath.len() {
            return;
        }
        cpath[..full.len()].copy_from_slice(full);
        let buf = crate::malloc::alloc(1 << 17);
        if buf.is_null() {
            return;
        }
        // SAFETY: the block has 128 KiB.
        let data = unsafe { core::slice::from_raw_parts_mut(buf, 1 << 17) };
        let n = read_file(cpath.as_ptr() as *const c_char, data);
        if n > 0 && !self.parse_tzif(&data[..n]) {
            self.reset_utc();
        }
        // SAFETY: our block.
        unsafe { crate::malloc::dealloc(buf) };
    }

    /// Installs a POSIX rule as the whole zone. Returns false if `spec` is
    /// not a valid rule (the zone is left unchanged).
    fn try_rule(&mut self, spec: &[u8]) -> bool {
        let nabbr = self.nabbr;
        match parse_rule(self, spec) {
            Some(rule) => {
                self.ntrans = 0;
                self.rule = Some(rule);
                true
            }
            None => {
                self.nabbr = nabbr;
                false
            }
        }
    }

    /// Parses a TZif file (versions 1 to 4), preferring the 64-bit block.
    fn parse_tzif(&mut self, data: &[u8]) -> bool {
        let header = |at: usize| -> Option<([usize; 6], u8)> {
            let h = data.get(at..at + 44)?;
            if &h[..4] != b"TZif" {
                return None;
            }
            let mut counts = [0usize; 6];
            for (i, c) in counts.iter_mut().enumerate() {
                *c = u32::from_be_bytes([
                    h[20 + 4 * i],
                    h[21 + 4 * i],
                    h[22 + 4 * i],
                    h[23 + 4 * i],
                ]) as usize;
            }
            Some((counts, h[4]))
        };
        let Some((v1, version)) = header(0) else {
            return false;
        };
        // Counts: isutcnt, isstdcnt, leapcnt, timecnt, typecnt, charcnt.
        let v1_len = |c: &[usize; 6]| c[3] * 5 + c[4] * 6 + c[5] + c[2] * 8 + c[1] + c[0];
        let (counts, at, time_size) = if version >= b'2' {
            let second = 44 + v1_len(&v1);
            let Some((v2, _)) = header(second) else {
                return false;
            };
            (v2, second + 44, 8usize)
        } else {
            (v1, 44, 4usize)
        };
        let [isutcnt, isstdcnt, leapcnt, timecnt, typecnt, charcnt] = counts;
        if typecnt == 0 || typecnt > MAX_TYPES || charcnt > MAX_ABBR {
            return false;
        }
        let times = at;
        let idx = times + timecnt * time_size;
        let types = idx + timecnt;
        let chars = types + typecnt * 6;
        let leaps = chars + charcnt;
        let end = leaps + leapcnt * (time_size + 4) + isstdcnt + isutcnt;
        if end > data.len() {
            return false;
        }
        // Keep the most recent transitions if there are too many.
        let skip = timecnt.saturating_sub(MAX_TRANS);
        self.ntrans = 0;
        for i in skip..timecnt {
            let t = if time_size == 8 {
                let b = &data[times + 8 * i..times + 8 * i + 8];
                i64::from_be_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
            } else {
                let b = &data[times + 4 * i..times + 4 * i + 4];
                i32::from_be_bytes([b[0], b[1], b[2], b[3]]) as i64
            };
            let ti = data[idx + i];
            if ti as usize >= typecnt {
                return false;
            }
            self.trans[self.ntrans] = t;
            self.idx[self.ntrans] = ti;
            self.ntrans += 1;
        }
        self.abbr[..charcnt].copy_from_slice(&data[chars..chars + charcnt]);
        self.nabbr = charcnt;
        if charcnt == 0 || self.abbr[charcnt - 1] != 0 {
            // Guarantee termination.
            if charcnt >= MAX_ABBR {
                return false;
            }
            self.abbr[charcnt] = 0;
            self.nabbr = charcnt + 1;
        }
        for i in 0..typecnt {
            let b = &data[types + 6 * i..types + 6 * i + 6];
            let abbr = b[5] as usize;
            if abbr >= self.nabbr {
                return false;
            }
            self.types[i] = Ttype {
                utoff: i32::from_be_bytes([b[0], b[1], b[2], b[3]]),
                isdst: b[4] != 0,
                abbr: abbr as u16,
            };
        }
        self.ntypes = typecnt;
        self.rule = None;
        if version >= b'2' {
            // Footer: "\n<rule>\n".
            let rest = &data[end..];
            if let Some(rest) = rest.strip_prefix(b"\n")
                && let Some(nl) = rest.iter().position(|&b| b == b'\n')
                && nl > 0
            {
                self.rule = parse_rule(self, &rest[..nl]);
            }
        }
        true
    }

    /// The local-time type in effect at `t`.
    fn lookup(&self, t: i64) -> Local {
        let ttype = if self.ntrans == 0 {
            match self.rule {
                Some(r) => return self.rule_lookup(&r, t),
                None => self.types[self.idx.first().copied().unwrap_or(0) as usize],
            }
        } else if t < self.trans[0] {
            // Before the first transition: the first standard-time type.
            self.types[..self.ntypes]
                .iter()
                .copied()
                .find(|t| !t.isdst)
                .unwrap_or(self.types[0])
        } else if t >= self.trans[self.ntrans - 1]
            && let Some(r) = self.rule
        {
            return self.rule_lookup(&r, t);
        } else {
            // Last transition at or before `t`.
            let i = self.trans[..self.ntrans].partition_point(|&x| x <= t) - 1;
            self.types[self.idx[i] as usize]
        };
        Local {
            gmtoff: ttype.utoff as i64,
            isdst: ttype.isdst,
            zone: self.abbr_ptr(ttype.abbr),
        }
    }

    fn rule_lookup(&self, r: &Rule, t: i64) -> Local {
        let Some(dst) = r.dst else {
            return Local {
                gmtoff: r.std_off as i64,
                isdst: false,
                zone: self.abbr_ptr(r.std_abbr),
            };
        };
        // Transition instants (UTC) for the year of `t` (by standard time).
        let (year, _, _) =
            calendar::civil_from_days((t + r.std_off as i64).div_euclid(SECS_PER_DAY));
        let start = rule_instant(year, dst.start, r.std_off as i64);
        let end = rule_instant(year, dst.end, dst.off as i64);
        let in_dst = if start <= end {
            start <= t && t < end
        } else {
            !(end <= t && t < start)
        };
        if in_dst {
            Local {
                gmtoff: dst.off as i64,
                isdst: true,
                zone: self.abbr_ptr(dst.abbr),
            }
        } else {
            Local {
                gmtoff: r.std_off as i64,
                isdst: false,
                zone: self.abbr_ptr(r.std_abbr),
            }
        }
    }
}

/// UTC instant of a rule date in `year`, where the transition happens at
/// local time `time` under offset `off`.
fn rule_instant(year: i64, (date, time): (RuleDate, i32), off: i64) -> i64 {
    let day = match date {
        RuleDate::Julian(n) => {
            let n = n as i64;
            let leap = calendar::is_leap(year);
            calendar::days_from_civil(year, 1, 1) + if leap && n >= 60 { n } else { n - 1 }
        }
        RuleDate::Zero(n) => calendar::days_from_civil(year, 1, 1) + n as i64,
        RuleDate::Mwd(m, w, d) => {
            let first = calendar::days_from_civil(year, m as u32, 1);
            // Weekday of the first of the month (days since epoch: day 0 was a Thursday).
            let first_wday = (first + 4).rem_euclid(7);
            let mut day = first + (d as i64 - first_wday).rem_euclid(7) + 7 * (w as i64 - 1);
            if w == 5 {
                let next = if m == 12 {
                    calendar::days_from_civil(year + 1, 1, 1)
                } else {
                    calendar::days_from_civil(year, m as u32 + 1, 1)
                };
                while day >= next {
                    day -= 7;
                }
            }
            day
        }
    };
    day * SECS_PER_DAY + time as i64 - off
}

// ---------------------------------------------------------------------
// POSIX rule strings.

/// Parses `[+-]hh[:mm[:ss]]`; returns seconds and the rest.
fn parse_offset(s: &[u8]) -> Option<(i32, &[u8])> {
    let (sign, s) = match s.first() {
        Some(b'-') => (-1, &s[1..]),
        Some(b'+') => (1, &s[1..]),
        _ => (1, s),
    };
    let mut total = 0i32;
    let mut rest = s;
    for (i, mul) in [3600, 60, 1].into_iter().enumerate() {
        let n = rest.iter().take_while(|b| b.is_ascii_digit()).count();
        if n == 0 || n > 3 {
            return None;
        }
        let v = rest[..n]
            .iter()
            .fold(0i32, |a, &d| a * 10 + (d - b'0') as i32);
        if (i == 0 && v > 167) || (i > 0 && v > 59) {
            return None;
        }
        total += v * mul;
        rest = &rest[n..];
        if rest.first() != Some(&b':') {
            break;
        }
        rest = &rest[1..];
    }
    Some((sign * total, rest))
}

/// Parses an abbreviation (`ABC` or `<+03>`); returns it and the rest.
fn parse_abbr(s: &[u8]) -> Option<(&[u8], &[u8])> {
    if let Some(rest) = s.strip_prefix(b"<") {
        let end = rest.iter().position(|&b| b == b'>')?;
        let name = &rest[..end];
        if name.len() < 3
            || !name
                .iter()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'+' | b'-'))
        {
            return None;
        }
        Some((name, &rest[end + 1..]))
    } else {
        let n = s.iter().take_while(|b| b.is_ascii_alphabetic()).count();
        if n < 3 {
            return None;
        }
        Some((&s[..n], &s[n..]))
    }
}

/// Parses up to three digits; returns the value and the rest.
fn num(s: &[u8]) -> Option<(u16, &[u8])> {
    let n = s.iter().take_while(|b| b.is_ascii_digit()).count();
    if n == 0 || n > 3 {
        return None;
    }
    Some((
        s[..n].iter().fold(0u16, |a, &d| a * 10 + (d - b'0') as u16),
        &s[n..],
    ))
}

fn parse_date(s: &[u8]) -> Option<((RuleDate, i32), &[u8])> {
    let (date, rest) = if let Some(rest) = s.strip_prefix(b"M") {
        let (m, rest) = num(rest)?;
        let rest = rest.strip_prefix(b".")?;
        let (w, rest) = num(rest)?;
        let rest = rest.strip_prefix(b".")?;
        let (d, rest) = num(rest)?;
        if !(1..=12).contains(&m) || !(1..=5).contains(&w) || d > 6 {
            return None;
        }
        (RuleDate::Mwd(m as u8, w as u8, d as u8), rest)
    } else if let Some(rest) = s.strip_prefix(b"J") {
        let (n, rest) = num(rest)?;
        if !(1..=365).contains(&n) {
            return None;
        }
        (RuleDate::Julian(n), rest)
    } else {
        let (n, rest) = num(s)?;
        if n > 365 {
            return None;
        }
        (RuleDate::Zero(n), rest)
    };
    let (time, rest) = match rest.strip_prefix(b"/") {
        Some(r) => parse_offset(r)?,
        None => (7200, rest),
    };
    Some(((date, time), rest))
}

/// Parses a POSIX `TZ` rule into `zone`'s abbreviation table.
fn parse_rule(zone: &mut Zone, s: &[u8]) -> Option<Rule> {
    let (std_name, rest) = parse_abbr(s)?;
    let (std_west, rest) = parse_offset(rest)?;
    let std_abbr = zone.add_abbr(std_name)?;
    let std_off = -std_west;
    if rest.is_empty() {
        return Some(Rule {
            std_abbr,
            std_off,
            dst: None,
        });
    }
    let (dst_name, rest) = parse_abbr(rest)?;
    let (dst_off, rest) = match rest.first() {
        Some(b',') | None => (std_off + 3600, rest),
        _ => {
            let (w, r) = parse_offset(rest)?;
            (-w, r)
        }
    };
    let dst_abbr = zone.add_abbr(dst_name)?;
    let (start, end) = match rest.strip_prefix(b",") {
        Some(r) => {
            let (start, r) = parse_date(r)?;
            let r = r.strip_prefix(b",")?;
            let (end, r) = parse_date(r)?;
            if !r.is_empty() {
                return None;
            }
            (start, end)
        }
        None => {
            if !rest.is_empty() {
                return None;
            }
            // No rule given: the US rules, as glibc and musl assume.
            (
                (RuleDate::Mwd(3, 2, 0), 7200),
                (RuleDate::Mwd(11, 1, 0), 7200),
            )
        }
    };
    Some(Rule {
        std_abbr,
        std_off,
        dst: Some(Dst {
            abbr: dst_abbr,
            off: dst_off,
            start,
            end,
        }),
    })
}

fn read_file(path: *const c_char, buf: &mut [u8]) -> usize {
    // SAFETY: `path` is NUL-terminated.
    let fd = unsafe { crate::fs::open(path, sys::O_CLOEXEC, 0) };
    if fd < 0 {
        return 0;
    }
    let mut n = 0;
    while n < buf.len() {
        // SAFETY: the buffer is valid for the remaining length.
        match unsafe { sys::read(fd, buf[n..].as_mut_ptr(), buf.len() - n) } {
            Ok(0) => break,
            Ok(k) => n += k,
            Err(e) if e == crate::errno::Errno::EINTR => {}
            Err(_) => break,
        }
    }
    let _ = sys::close(fd);
    n
}

// ---------------------------------------------------------------------
// Entry points used by `time/mod.rs`.

/// Local-time information for `t` under the current `TZ`.
pub fn local(t: i64) -> Local {
    let mut z = ZONE.lock();
    z.ensure();
    z.lookup(t)
}

/// Converts local broken-down seconds (as if UTC) to an instant, honouring
/// `isdst` (`None` when the caller does not know).
pub fn from_local(local_secs: i64, isdst: Option<bool>) -> i64 {
    let mut z = ZONE.lock();
    z.ensure();
    // Guess with the offset in effect at the local instant read as UTC,
    // then refine once with the offset at the guess.
    let first = z.lookup(local_secs);
    let mut t = local_secs - first.gmtoff;
    let mut info = z.lookup(t);
    if info.gmtoff != first.gmtoff {
        t = local_secs - info.gmtoff;
        info = z.lookup(t);
    }
    if let Some(want) = isdst
        && want != info.isdst
    {
        // The caller insists on the other kind of time: shift by the
        // difference between the zone's standard and daylight offsets.
        let (std, dst) = z.offsets();
        t += info.gmtoff - if want { dst.utoff } else { std.utoff } as i64;
    }
    t
}

impl Zone {
    /// The zone's standard and daylight types (the latter equal to the
    /// former when it has no daylight time): from the rule if there is
    /// one, else the latest transitions of each kind.
    fn offsets(&self) -> (Ttype, Ttype) {
        if let Some(r) = self.rule {
            let std = Ttype {
                utoff: r.std_off,
                isdst: false,
                abbr: r.std_abbr,
            };
            return match r.dst {
                Some(d) => (
                    std,
                    Ttype {
                        utoff: d.off,
                        isdst: true,
                        abbr: d.abbr,
                    },
                ),
                None => (std, std),
            };
        }
        let mut std: Option<Ttype> = None;
        let mut dst: Option<Ttype> = None;
        for i in (0..self.ntrans).rev() {
            let t = self.types[self.idx[i] as usize];
            if t.isdst {
                dst.get_or_insert(t);
            } else {
                std.get_or_insert(t);
            }
            if std.is_some() && dst.is_some() {
                break;
            }
        }
        let std = std.unwrap_or(self.types[0]);
        (std, dst.unwrap_or(std))
    }
}

/// `tzset` proper: reloads if needed and returns (standard abbreviation,
/// daylight abbreviation, standard offset west of UTC, has daylight).
pub fn tzset() -> (*const c_char, *const c_char, i64, bool) {
    let mut z = ZONE.lock();
    z.ensure();
    let (std, dst) = z.offsets();
    (
        z.abbr_ptr(std.abbr),
        z.abbr_ptr(dst.abbr),
        -(std.utoff as i64),
        dst.isdst,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zone_with_rule(spec: &str) -> Zone {
        let mut z = Zone {
            tz: [0; MAX_TZ],
            tz_len: 0,
            trans: [0; MAX_TRANS],
            idx: [0; MAX_TRANS],
            ntrans: 0,
            types: [Ttype::default(); MAX_TYPES],
            ntypes: 0,
            abbr: [0; MAX_ABBR],
            nabbr: 0,
            rule: None,
            loaded: true,
        };
        z.reset_utc();
        assert!(z.try_rule(spec.as_bytes()), "{spec}");
        z
    }

    fn abbr(l: &Local) -> String {
        // SAFETY: NUL-terminated inside the table.
        unsafe { core::ffi::CStr::from_ptr(l.zone) }
            .to_str()
            .unwrap()
            .to_string()
    }

    #[test]
    fn posix_rules() {
        let z = zone_with_rule("EST5EDT,M3.2.0,M11.1.0");
        // 2024-03-10 06:59:59Z is still EST; 07:00:00Z is EDT.
        let l = z.lookup(1_710_053_999);
        assert_eq!(
            (l.gmtoff, l.isdst, abbr(&l)),
            (-18_000, false, "EST".into())
        );
        let l = z.lookup(1_710_054_000);
        assert_eq!((l.gmtoff, l.isdst, abbr(&l)), (-14_400, true, "EDT".into()));
        // 2024-11-03 05:59:59Z EDT, 06:00:00Z EST.
        assert!(z.lookup(1_730_613_599).isdst);
        assert!(!z.lookup(1_730_613_600).isdst);
        // Southern hemisphere, quoted names, explicit dst offset, J dates.
        let z = zone_with_rule("<-03>3<-02>2,M10.1.0/0,M2.3.0/0");
        let l = z.lookup(1_704_067_200); // 2024-01-01: summer time
        assert_eq!((l.gmtoff, l.isdst, abbr(&l)), (-7_200, true, "-02".into()));
        assert!(!z.lookup(1_717_200_000).isdst); // 2024-06-01
        let z = zone_with_rule("CET-1CEST,J60/2,J300/3");
        assert!(z.lookup(1_717_200_000).isdst);
        assert!(!z.lookup(1_704_067_200).isdst);
        assert_eq!(z.lookup(1_704_067_200).gmtoff, 3600);
        // Bare "EST5EDT" gets the US rules; plain "UTC0" has none.
        let z = zone_with_rule("EST5EDT");
        assert!(z.lookup(1_717_200_000).isdst);
        let z = zone_with_rule("UTC0");
        assert_eq!(z.lookup(0).gmtoff, 0);
        for bad in [
            "",
            "E5",
            "EST5EDT,M13.1.0,M11.1.0",
            "EST5EDT,M3.2.0",
            "EST999",
            "<EST>5EDT,J0,J1",
        ] {
            let mut z = zone_with_rule("UTC0");
            assert!(!z.try_rule(bad.as_bytes()), "{bad}");
        }
    }

    #[test]
    fn rule_dates() {
        // First Sunday of November 2024 is the 3rd; last Sunday of March 2024 the 31st.
        assert_eq!(
            rule_instant(2024, (RuleDate::Mwd(11, 1, 0), 0), 0),
            calendar::days_from_civil(2024, 11, 3) * SECS_PER_DAY
        );
        assert_eq!(
            rule_instant(2024, (RuleDate::Mwd(3, 5, 0), 0), 0),
            calendar::days_from_civil(2024, 3, 31) * SECS_PER_DAY
        );
        // J60 is March 1 in every year; day 59 (zero-based) is Feb 29 in a leap year.
        assert_eq!(
            rule_instant(2024, (RuleDate::Julian(60), 0), 0),
            calendar::days_from_civil(2024, 3, 1) * SECS_PER_DAY
        );
        assert_eq!(
            rule_instant(2023, (RuleDate::Julian(60), 0), 0),
            calendar::days_from_civil(2023, 3, 1) * SECS_PER_DAY
        );
        assert_eq!(
            rule_instant(2024, (RuleDate::Zero(59), 0), 0),
            calendar::days_from_civil(2024, 2, 29) * SECS_PER_DAY
        );
    }

    #[test]
    fn tzif_files() {
        let Ok(data) = std::fs::read("/usr/share/zoneinfo/America/New_York") else {
            return;
        };
        let mut z = zone_with_rule("UTC0");
        assert!(z.parse_tzif(&data));
        assert!(z.ntrans > 100 && z.rule.is_some());
        let l = z.lookup(1_710_053_999);
        assert_eq!(
            (l.gmtoff, l.isdst, abbr(&l)),
            (-18_000, false, "EST".into())
        );
        let l = z.lookup(1_710_054_000);
        assert_eq!((l.gmtoff, l.isdst, abbr(&l)), (-14_400, true, "EDT".into()));
        // Far future: the footer rule.
        let l = z.lookup(4_102_444_800 + 200 * 86_400); // mid-2100
        assert!(l.isdst);
        // Before the first transition: standard time.
        assert!(!z.lookup(-5_000_000_000).isdst);
        // Truncated and corrupted files are rejected cleanly.
        assert!(!z.parse_tzif(&data[..100]));
        let mut bad = data.clone();
        bad[0] = b'X';
        assert!(!z.parse_tzif(&bad));
    }
}
