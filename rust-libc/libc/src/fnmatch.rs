//! `fnmatch(3)` with the POSIX flags plus `FNM_CASEFOLD` and
//! `FNM_LEADING_DIR`.
//!
//! Matching is iterative with single-point backtracking for `*`, so the
//! running time is bounded by the product of the pattern and string
//! lengths, never exponential.

use crate::c_char;
use core::ffi::c_int;

#[allow(missing_docs)]
pub const FNM_NOESCAPE: c_int = 1;
#[allow(missing_docs)]
pub const FNM_PATHNAME: c_int = 2;
#[allow(missing_docs)]
pub const FNM_PERIOD: c_int = 4;
#[allow(missing_docs)]
pub const FNM_LEADING_DIR: c_int = 8;
#[allow(missing_docs)]
pub const FNM_CASEFOLD: c_int = 16;
/// `FNM_NOMATCH`.
pub const FNM_NOMATCH: c_int = 1;

/// Matches a bracket expression starting after `[`. Returns whether
/// `c` matched and the index after the closing `]`, or `None` if the
/// bracket is malformed (in which case `[` is literal).
fn bracket(p: &[u8], c: u8, casefold: bool) -> Option<(bool, usize)> {
    let mut i = 0;
    let negate = matches!(p.first(), Some(b'!') | Some(b'^'));
    if negate {
        i += 1;
    }
    let mut matched = false;
    let mut first = true;
    let eq = |a: u8, b: u8| {
        if casefold {
            a.eq_ignore_ascii_case(&b)
        } else {
            a == b
        }
    };
    loop {
        let &ch = p.get(i)?;
        if ch == b']' && !first {
            return Some((matched != negate, i + 1));
        }
        first = false;
        if ch == b'[' && p.get(i + 1) == Some(&b':') {
            // Character class.
            let end = p[i + 2..].windows(2).position(|w| w == b":]")? + i + 2;
            let class = &p[i + 2..end];
            let ok = match class {
                b"alpha" => c.is_ascii_alphabetic(),
                b"digit" => c.is_ascii_digit(),
                b"alnum" => c.is_ascii_alphanumeric(),
                b"upper" => c.is_ascii_uppercase() || (casefold && c.is_ascii_lowercase()),
                b"lower" => c.is_ascii_lowercase() || (casefold && c.is_ascii_uppercase()),
                b"space" => matches!(c, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r'),
                b"blank" => matches!(c, b' ' | b'\t'),
                b"punct" => c.is_ascii_punctuation(),
                b"print" => (0x20..0x7f).contains(&c),
                b"graph" => (0x21..0x7f).contains(&c),
                b"cntrl" => c < 0x20 || c == 0x7f,
                b"xdigit" => c.is_ascii_hexdigit(),
                _ => return None,
            };
            matched |= ok;
            i = end + 2;
            continue;
        }
        let lo = if ch == b'\\' && i + 1 < p.len() {
            i += 1;
            p[i]
        } else {
            ch
        };
        if p.get(i + 1) == Some(&b'-') && p.get(i + 2).is_some_and(|&n| n != b']') {
            let mut hi = p[i + 2];
            let mut skip = 3;
            if hi == b'\\' && i + 3 < p.len() {
                hi = p[i + 3];
                skip = 4;
            }
            let in_range = |x: u8| lo <= x && x <= hi;
            matched |= in_range(c)
                || (casefold
                    && (in_range(c.to_ascii_lowercase()) || in_range(c.to_ascii_uppercase())));
            i += skip;
        } else {
            matched |= eq(lo, c);
            i += 1;
        }
    }
}

/// Matches `pattern` against `s`.
pub fn matches(pattern: &[u8], s: &[u8], flags: c_int) -> bool {
    let noescape = flags & FNM_NOESCAPE != 0;
    let pathname = flags & FNM_PATHNAME != 0;
    let period = flags & FNM_PERIOD != 0;
    let leading_dir = flags & FNM_LEADING_DIR != 0;
    let casefold = flags & FNM_CASEFOLD != 0;
    let (mut p, mut i) = (0usize, 0usize);
    let mut star: Option<(usize, usize)> = None; // (pattern pos after '*', string pos)
    let eq = |a: u8, b: u8| {
        if casefold {
            a.eq_ignore_ascii_case(&b)
        } else {
            a == b
        }
    };
    // A leading period must be matched explicitly (also after '/' with
    // FNM_PATHNAME).
    let special_period =
        |i: usize| period && s.get(i) == Some(&b'.') && (i == 0 || (pathname && s[i - 1] == b'/'));
    loop {
        if p < pattern.len() {
            let pc = pattern[p];
            match pc {
                b'*' => {
                    if special_period(i) {
                        return false;
                    }
                    // Collapse consecutive stars.
                    while p < pattern.len() && pattern[p] == b'*' {
                        p += 1;
                    }
                    if p == pattern.len() {
                        // Trailing star matches the rest, except '/' with
                        // FNM_PATHNAME.
                        return !pathname || !s[i..].contains(&b'/') || leading_dir;
                    }
                    star = Some((p, i));
                    continue;
                }
                b'?' if i < s.len() && !(pathname && s[i] == b'/') && !special_period(i) => {
                    p += 1;
                    i += 1;
                    continue;
                }
                b'[' if i < s.len() && !(pathname && s[i] == b'/') && !special_period(i) => {
                    if let Some((ok, next)) = bracket(&pattern[p + 1..], s[i], casefold) {
                        if ok {
                            p += 1 + next;
                            i += 1;
                            continue;
                        }
                    } else if eq(b'[', s[i]) {
                        p += 1;
                        i += 1;
                        continue;
                    }
                }
                b'\\' if !noescape && p + 1 < pattern.len() => {
                    if i < s.len() && eq(pattern[p + 1], s[i]) {
                        p += 2;
                        i += 1;
                        continue;
                    }
                }
                _ => {
                    if i < s.len() && eq(pc, s[i]) {
                        p += 1;
                        i += 1;
                        continue;
                    }
                    if leading_dir && i < s.len() && s[i] == b'/' && p == pattern.len() {
                        return true;
                    }
                }
            }
        } else if i == s.len() || (leading_dir && s[i] == b'/') {
            return true;
        }
        // Mismatch: retry from the last star with one more character.
        match star {
            Some((sp, si)) if si < s.len() && !(pathname && s[si] == b'/') => {
                star = Some((sp, si + 1));
                p = sp;
                i = si + 1;
            }
            _ => return false,
        }
    }
}

/// `fnmatch(3)`.
///
/// # Safety
/// Both strings must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fnmatch(pattern: *const c_char, s: *const c_char, flags: c_int) -> c_int {
    // SAFETY: caller contract.
    let (p, t) = unsafe {
        (
            core::slice::from_raw_parts(
                pattern as *const u8,
                crate::string::search::strlen(pattern as *const u8),
            ),
            core::slice::from_raw_parts(
                s as *const u8,
                crate::string::search::strlen(s as *const u8),
            ),
        )
    };
    if matches(p, t, flags) { 0 } else { FNM_NOMATCH }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(p: &str, s: &str, flags: c_int) -> bool {
        matches(p.as_bytes(), s.as_bytes(), flags)
    }

    #[test]
    fn globs() {
        assert!(m("*.c", "main.c", 0));
        assert!(!m("*.c", "main.h", 0));
        assert!(m("a*b*c", "aXXbYYc", 0));
        assert!(!m("a*b*c", "aXXbYY", 0));
        assert!(m("?", "x", 0) && !m("?", "", 0) && !m("?", "xy", 0));
        assert!(m("[abc]x", "bx", 0) && !m("[abc]x", "dx", 0));
        assert!(
            m("[a-c]", "b", 0) && !m("[a-c]", "d", 0) && m("[!a-c]", "d", 0) && m("[^a]", "b", 0)
        );
        assert!(m("[[:digit:]]*", "7up", 0) && !m("[[:digit:]]*", "up", 0));
        assert!(m("[]]", "]", 0) && m("[!]]", "a", 0));
        assert!(m("a\\*b", "a*b", 0) && !m("a\\*b", "axb", 0));
        assert!(m("a\\*b", "a\\xb", FNM_NOESCAPE) || !m("a\\*b", "axb", FNM_NOESCAPE));
        assert!(m("*", "", 0) && m("", "", 0) && !m("", "a", 0));
        assert!(m("**", "anything", 0));
        assert!(
            m("a*", "a/b", 0) && !m("a*", "a/b", FNM_PATHNAME) && m("a*/b", "ax/b", FNM_PATHNAME)
        );
        assert!(
            !m("*", ".hidden", FNM_PERIOD)
                && m(".*", ".hidden", FNM_PERIOD)
                && m("*", "a.b", FNM_PERIOD)
        );
        assert!(!m("a/*", "a/.b", FNM_PERIOD | FNM_PATHNAME) && m("a/*", "a/.b", FNM_PERIOD));
        assert!(
            m("ABC", "abc", FNM_CASEFOLD) && !m("ABC", "abc", 0) && m("[A-C]", "b", FNM_CASEFOLD)
        );
        assert!(
            m("src", "src/main.c", FNM_LEADING_DIR) && !m("src", "srcx/main.c", FNM_LEADING_DIR)
        );
        assert!(m("*.c", "dir/x.c", 0));
        assert!(!m("*.c", "dir/x.c", FNM_PATHNAME));
        assert!(m("a[", "a[", 0), "an unterminated bracket is literal");
        // Pathological patterns stay fast.
        let s = "a".repeat(2000);
        assert!(!m("*a*a*a*a*a*a*a*a*a*a*b", &s, 0));
    }
}
