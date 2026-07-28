//! Parametrisation id generation, byte-for-byte compatible with pytest's
//! `idmaker` for the value kinds that appear in practice.

use pyo3::prelude::*;
use pyo3::types::{PyBool, PyBytes, PyComplex, PyFloat, PyInt, PyString};
use rustc_hash::FxHashMap;

/// Escape a string the way pytest's `ascii_escaped` does.
pub fn ascii_escaped(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 || (c as u32) == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32));
            }
            c if (c as u32) < 0x7f => out.push(c),
            c if (c as u32) <= 0xff => out.push_str(&format!("\\x{:02x}", c as u32)),
            c if (c as u32) <= 0xffff => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push_str(&format!("\\U{:08x}", c as u32)),
        }
    }
    out
}

fn bytes_escaped(b: &[u8]) -> String {
    // Mirrors `val.decode("ascii", "backslashreplace")` followed by the
    // non-printable translation.  Note that, unlike the `str` path, a literal
    // backslash is *not* doubled here: `backslashreplace` only introduces
    // escapes for bytes that are not ASCII.
    let mut out = String::with_capacity(b.len());
    for &c in b {
        match c {
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7e => out.push(c as char),
            _ => out.push_str(&format!("\\x{c:02x}")),
        }
    }
    out
}

/// Render one parameter value into its id fragment.  Returns `None` when
/// pytest would fall back to `argname + index`.
pub fn idval(py: Python<'_>, val: &Bound<'_, PyAny>) -> Option<String> {
    if val.is_none() {
        return Some("None".to_string());
    }
    if let Ok(s) = val.cast::<PyString>() {
        return Some(ascii_escaped(s.to_str().ok()?));
    }
    if let Ok(b) = val.cast::<PyBytes>() {
        return Some(bytes_escaped(b.as_bytes()));
    }
    if val.is_instance_of::<PyBool>() {
        return Some(if val.is_truthy().ok()? { "True".into() } else { "False".into() });
    }
    if val.is_instance_of::<PyInt>() || val.is_instance_of::<PyFloat>() || val.is_instance_of::<PyComplex>() {
        return Some(val.str().ok()?.to_string());
    }
    // enum.Enum -> str(val)
    if let Ok(enum_mod) = py.import("enum") {
        if let Ok(enum_cls) = enum_mod.getattr("Enum") {
            if val.is_instance(&enum_cls).unwrap_or(false) {
                return Some(val.str().ok()?.to_string());
            }
        }
    }
    // Compiled regex -> its pattern.
    if let Ok(re_mod) = py.import("re") {
        if let Ok(pattern_cls) = re_mod.getattr("Pattern") {
            if val.is_instance(&pattern_cls).unwrap_or(false) {
                if let Ok(p) = val.getattr("pattern") {
                    if let Ok(s) = p.extract::<String>() {
                        return Some(ascii_escaped(&s));
                    }
                }
            }
        }
    }
    if let Ok(name) = val.getattr("__name__") {
        if let Ok(s) = name.extract::<String>() {
            return Some(s);
        }
    }
    None
}

/// Build the id for one parameter set.
pub fn idvalset(
    py: Python<'_>,
    values: &[Bound<'_, PyAny>],
    argnames: &[String],
    idx: usize,
    explicit_id: Option<&str>,
    user_id: Option<&str>,
) -> String {
    if let Some(id) = explicit_id {
        return ascii_escaped(id);
    }
    if let Some(id) = user_id {
        return ascii_escaped(id);
    }
    let mut parts = Vec::with_capacity(values.len());
    for (i, v) in values.iter().enumerate() {
        let argname = argnames.get(i).map(|s| s.as_str()).unwrap_or("arg");
        parts.push(idval(py, v).unwrap_or_else(|| format!("{argname}{idx}")));
    }
    parts.join("-")
}

/// Disambiguate duplicate ids exactly like pytest does.
pub fn make_unique(ids: &mut [String]) {
    let mut counts: FxHashMap<&str, usize> = FxHashMap::default();
    for id in ids.iter() {
        *counts.entry(id.as_str()).or_insert(0) += 1;
    }
    let dupes: Vec<String> = counts
        .iter()
        .filter(|(_, &c)| c > 1)
        .map(|(k, _)| (*k).to_string())
        .collect();
    if dupes.is_empty() {
        return;
    }
    let mut unique: rustc_hash::FxHashSet<String> = ids.iter().cloned().collect();
    let mut suffixes: FxHashMap<String, usize> = FxHashMap::default();
    for i in 0..ids.len() {
        let id = ids[i].clone();
        if !dupes.contains(&id) {
            continue;
        }
        let sep = if id.chars().last().map(|c| c.is_ascii_digit()).unwrap_or(false) {
            "_"
        } else {
            ""
        };
        let counter = suffixes.entry(id.clone()).or_insert(0);
        let mut new_id = format!("{id}{sep}{counter}");
        while unique.contains(&new_id) {
            *counter += 1;
            new_id = format!("{id}{sep}{counter}");
        }
        *counter += 1;
        unique.insert(new_id.clone());
        ids[i] = new_id;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes() {
        assert_eq!(ascii_escaped("abc"), "abc");
        assert_eq!(ascii_escaped("a\nb"), "a\\nb");
        assert_eq!(bytes_escaped(b"\x00\xff"), "\\x00\\xff");
        // A literal backslash stays single for bytes, unlike for str.
        assert_eq!(bytes_escaped(b"a\\b"), "a\\b");
    }

    #[test]
    fn unique_ids() {
        let mut ids = vec!["a".to_string(), "a".to_string(), "b".to_string()];
        make_unique(&mut ids);
        assert_eq!(ids, vec!["a0", "a1", "b"]);

        let mut ids = vec!["x1".to_string(), "x1".to_string()];
        make_unique(&mut ids);
        assert_eq!(ids, vec!["x1_0", "x1_1"]);
    }
}
