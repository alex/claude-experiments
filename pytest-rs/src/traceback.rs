//! Failure rendering: traceback formatting plus on-demand assertion
//! introspection.
//!
//! pytest rewrites every `assert` statement at import time so that failures can
//! show intermediate values.  That costs an AST rewrite (and a `.pyc` cache
//! round trip) for every module in the test suite, on every run where the cache
//! is cold, and it slows down every assertion that passes.
//!
//! We do the same job lazily instead: when an `AssertionError` escapes we walk
//! the traceback, recover the failing source line, re-parse just that line and
//! re-evaluate its sub-expressions in the frame that raised.  Passing tests pay
//! nothing.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};

/// One rendered traceback entry.
struct Entry {
    path: String,
    lineno: usize,
    funcname: String,
    source: Vec<String>,
    /// Index within `source` of the failing line.
    marked: usize,
    explanation: Option<String>,
}

/// `ExcType: message`, matching `traceback.format_exception_only`.
pub fn format_exception_only(py: Python<'_>, err: &PyErr) -> String {
    let ty = err
        .get_type(py)
        .name()
        .map(|n| n.to_string())
        .unwrap_or_else(|_| "Exception".to_string());
    let msg = err.value(py).str().map(|s| s.to_string()).unwrap_or_default();
    if msg.is_empty() {
        ty
    } else {
        format!("{ty}: {msg}")
    }
}

/// Full Python-style traceback, used for collection errors.
pub fn format_collect_error(py: Python<'_>, err: &PyErr) -> String {
    native_traceback(py, err).unwrap_or_else(|| format_exception_only(py, err))
}

pub fn native_traceback(py: Python<'_>, err: &PyErr) -> Option<String> {
    let tb_mod = py.import("traceback").ok()?;
    let ty = err.get_type(py);
    let val = err.value(py);
    let tb = err.traceback(py);
    let lines = tb_mod
        .call_method1("format_exception", (ty, val, tb.map(|t| t.into_any()).unwrap_or(py.None().into_bound(py))))
        .ok()?;
    let list = lines.cast::<PyList>().ok()?;
    let mut out = String::new();
    for l in list.iter() {
        out.push_str(&l.extract::<String>().ok()?);
    }
    Some(out.trim_end().to_string())
}

/// Render a failure the way pytest's `--tb=long` does.
pub fn format_failure(py: Python<'_>, err: &PyErr, style: &str, rootdir: &std::path::Path, showlocals: bool) -> String {
    if style == "no" {
        return String::new();
    }
    if style == "native" {
        return native_traceback(py, err).unwrap_or_else(|| format_exception_only(py, err));
    }
    let entries = collect_entries(py, err, rootdir, style == "long" || style == "auto");
    let exconly = explain_exception(py, err);
    if style == "line" {
        let loc = entries
            .last()
            .map(|e| format!("{}:{}: ", e.path, e.lineno))
            .unwrap_or_default();
        return format!("{loc}{}", exconly.lines().next().unwrap_or(""));
    }
    let mut out = String::new();
    let selected: Vec<&Entry> = match style {
        "short" => entries.iter().collect(),
        _ => entries.iter().collect(),
    };
    for (i, e) in selected.iter().enumerate() {
        let last = i + 1 == selected.len();
        if style == "short" {
            out.push_str(&format!("{}:{}: in {}\n", e.path, e.lineno, e.funcname));
            for (j, line) in e.source.iter().enumerate() {
                let prefix = if j == e.marked { "    " } else { "    " };
                out.push_str(&format!("{prefix}{line}\n"));
            }
        } else {
            for (j, line) in e.source.iter().enumerate() {
                let prefix = if j == e.marked { ">   " } else { "    " };
                out.push_str(&format!("{prefix}{line}\n"));
            }
            if let Some(ex) = &e.explanation {
                for l in ex.lines() {
                    out.push_str(&format!("E   {l}\n"));
                }
            }
            if last {
                for l in exconly.lines() {
                    out.push_str(&format!("E   {l}\n"));
                }
            }
            out.push('\n');
            out.push_str(&format!("{}:{}: {}\n", e.path, e.lineno, if last { "" } else { "" }));
            if !last {
                out.push_str(&format!("{}\n", "_".repeat(40)));
            }
        }
        let _ = showlocals;
    }
    if entries.is_empty() {
        out.push_str(&exconly);
        out.push('\n');
    } else if style != "short" {
        // Final line carries the exception type, matching pytest's layout.
        let last = entries.last().unwrap();
        out = out.trim_end_matches('\n').to_string();
        out.push('\n');
        let _ = last;
    }
    out
}

fn collect_entries(py: Python<'_>, err: &PyErr, rootdir: &std::path::Path, want_source: bool) -> Vec<Entry> {
    let mut entries = Vec::new();
    let Some(tb) = err.traceback(py) else { return entries };
    let mut cur = tb.into_any();
    loop {
        let Ok(frame) = cur.getattr("tb_frame") else { break };
        let lineno: usize = cur.getattr("tb_lineno").and_then(|l| l.extract()).unwrap_or(0);
        let code = frame.getattr("f_code").ok();
        let filename: String = code
            .as_ref()
            .and_then(|c| c.getattr("co_filename").ok())
            .and_then(|f| f.extract().ok())
            .unwrap_or_default();
        let funcname: String = code
            .as_ref()
            .and_then(|c| c.getattr("co_name").ok())
            .and_then(|f| f.extract().ok())
            .unwrap_or_default();
        let hide = frame
            .getattr("f_globals")
            .ok()
            .and_then(|g| g.cast_into::<PyDict>().ok())
            .and_then(|g| g.get_item("__tracebackhide__").ok().flatten())
            .map(|v| v.is_truthy().unwrap_or(false))
            .unwrap_or(false)
            || frame
                .getattr("f_locals")
                .ok()
                .and_then(|l| l.cast_into::<PyDict>().ok())
                .and_then(|l| l.get_item("__tracebackhide__").ok().flatten())
                .map(|v| v.is_truthy().unwrap_or(false))
                .unwrap_or(false);
        let internal = filename.contains("/pytest_rs/") || filename.starts_with('<');
        if !hide && !internal {
            let (source, marked) = if want_source {
                read_source(py, &filename, lineno, code.as_ref())
            } else {
                (Vec::new(), 0)
            };
            let explanation = if err.is_instance_of::<pyo3::exceptions::PyAssertionError>(py) {
                explain_assertion(py, &frame, &filename, lineno)
            } else {
                None
            };
            let display = std::path::Path::new(&filename)
                .strip_prefix(rootdir)
                .map(|p| p.to_string_lossy().to_string())
                .unwrap_or_else(|_| filename.clone());
            entries.push(Entry { path: display, lineno, funcname, source, marked, explanation });
        }
        match cur.getattr("tb_next") {
            Ok(n) if !n.is_none() => cur = n,
            _ => break,
        }
    }
    entries
}

/// Read the enclosing function body around `lineno`.
fn read_source(py: Python<'_>, filename: &str, lineno: usize, code: Option<&Bound<'_, PyAny>>) -> (Vec<String>, usize) {
    let Ok(linecache) = py.import("linecache") else { return (Vec::new(), 0) };
    let first: usize = code
        .and_then(|c| c.getattr("co_firstlineno").ok())
        .and_then(|v| v.extract().ok())
        .unwrap_or(lineno);
    let start = first.max(1);
    let end = lineno;
    if end < start {
        return (Vec::new(), 0);
    }
    // Cap how much context we print for very long functions.
    let start = if end - start > 12 { end.saturating_sub(9) } else { start };
    let mut lines = Vec::new();
    for n in start..=end {
        let Ok(l) = linecache.call_method1("getline", (filename, n)) else { continue };
        let s: String = l.extract().unwrap_or_default();
        lines.push(s.trim_end().to_string());
    }
    // Trim common indentation so the block reads like pytest's output.
    let indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    let lines: Vec<String> = lines
        .into_iter()
        .map(|l| if l.len() >= indent { l[indent..].to_string() } else { l })
        .collect();
    let marked = lines.len().saturating_sub(1);
    (lines, marked)
}

fn explain_exception(py: Python<'_>, err: &PyErr) -> String {
    let base = format_exception_only(py, err);
    if err.is_instance_of::<pyo3::exceptions::PyAssertionError>(py) {
        let msg = err.value(py).str().map(|s| s.to_string()).unwrap_or_default();
        if msg.is_empty() {
            return "assert failed".to_string();
        }
        return format!("assert {msg}");
    }
    base
}

/// Re-evaluate the failing `assert` expression to describe why it failed.
fn explain_assertion(py: Python<'_>, frame: &Bound<'_, PyAny>, filename: &str, lineno: usize) -> Option<String> {
    let linecache = py.import("linecache").ok()?;
    let raw: String = linecache
        .call_method1("getline", (filename, lineno))
        .ok()?
        .extract()
        .ok()?;
    let src = raw.trim();
    if !src.starts_with("assert ") {
        return None;
    }
    let ast = py.import("ast").ok()?;
    let parsed = ast.call_method1("parse", (src,)).ok()?;
    let body = parsed.getattr("body").ok()?;
    let stmt = body.get_item(0).ok()?;
    let test = stmt.getattr("test").ok()?;
    let globals = frame.getattr("f_globals").ok()?;
    let locals = frame.getattr("f_locals").ok()?;

    let cmp_cls = ast.getattr("Compare").ok()?;
    if !test.is_instance(&cmp_cls).unwrap_or(false) {
        // Fall back to showing the value of the whole expression.
        let v = eval_node(py, &ast, &test, &globals, &locals)?;
        return Some(format!("assert {}", safe_repr(&v)));
    }
    let left = test.getattr("left").ok()?;
    let ops = test.getattr("ops").ok()?;
    let comparators = test.getattr("comparators").ok()?;
    if ops.len().ok()? != 1 {
        return None;
    }
    let op = ops.get_item(0).ok()?;
    let right = comparators.get_item(0).ok()?;
    let lv = eval_node(py, &ast, &left, &globals, &locals)?;
    let rv = eval_node(py, &ast, &right, &globals, &locals)?;
    let opname = op.get_type().name().ok()?.to_string();
    let sym = match opname.as_str() {
        "Eq" => "==",
        "NotEq" => "!=",
        "Lt" => "<",
        "LtE" => "<=",
        "Gt" => ">",
        "GtE" => ">=",
        "Is" => "is",
        "IsNot" => "is not",
        "In" => "in",
        "NotIn" => "not in",
        _ => return None,
    };
    let mut out = format!("assert {} {sym} {}", safe_repr(&lv), safe_repr(&rv));
    if sym == "==" {
        if let Some(diff) = describe_difference(py, &lv, &rv) {
            out.push('\n');
            out.push_str(&diff);
        }
    }
    Some(out)
}

fn eval_node<'py>(
    py: Python<'py>,
    ast: &Bound<'py, PyAny>,
    node: &Bound<'py, PyAny>,
    globals: &Bound<'py, PyAny>,
    locals: &Bound<'py, PyAny>,
) -> Option<Bound<'py, PyAny>> {
    let expr = ast.getattr("Expression").ok()?.call1((node,)).ok()?;
    ast.call_method1("fix_missing_locations", (&expr,)).ok()?;
    let builtins = py.import("builtins").ok()?;
    let code = builtins
        .getattr("compile")
        .ok()?
        .call1((expr, "<assertion>", "eval"))
        .ok()?;
    builtins.getattr("eval").ok()?.call1((code, globals, locals)).ok()
}

fn safe_repr(v: &Bound<'_, PyAny>) -> String {
    let s = v.repr().map(|r| r.to_string()).unwrap_or_else(|_| "<unrepresentable>".to_string());
    if s.len() > 240 {
        format!("{}...{}", &s[..120], &s[s.len() - 60..])
    } else {
        s
    }
}

/// Produce a short structural diff for `==` failures on sequences/mappings.
fn describe_difference(py: Python<'_>, left: &Bound<'_, PyAny>, right: &Bound<'_, PyAny>) -> Option<String> {
    let lty = left.get_type().name().ok()?.to_string();
    let rty = right.get_type().name().ok()?.to_string();
    if lty != rty {
        return None;
    }
    match lty.as_str() {
        "str" => {
            let a: String = left.extract().ok()?;
            let b: String = right.extract().ok()?;
            let pos = a.chars().zip(b.chars()).position(|(x, y)| x != y);
            match pos {
                Some(i) => Some(format!("  First differing character at index {i}")),
                None => Some(format!("  Strings differ in length: {} != {}", a.len(), b.len())),
            }
        }
        "bytes" => {
            let a: Vec<u8> = left.extract().ok()?;
            let b: Vec<u8> = right.extract().ok()?;
            let pos = a.iter().zip(b.iter()).position(|(x, y)| x != y);
            match pos {
                Some(i) => Some(format!("  First differing byte at index {i}: {:#04x} != {:#04x}", a[i], b[i])),
                None => Some(format!("  Lengths differ: {} != {}", a.len(), b.len())),
            }
        }
        "list" | "tuple" => {
            let alen = left.len().ok()?;
            let blen = right.len().ok()?;
            if alen != blen {
                return Some(format!("  Lengths differ: {alen} != {blen}"));
            }
            for i in 0..alen {
                let x = left.get_item(i).ok()?;
                let y = right.get_item(i).ok()?;
                if !x.eq(&y).unwrap_or(false) {
                    return Some(format!("  At index {i}: {} != {}", safe_repr(&x), safe_repr(&y)));
                }
            }
            None
        }
        "dict" => {
            let ld = left.cast::<PyDict>().ok()?;
            let rd = right.cast::<PyDict>().ok()?;
            let mut diffs = Vec::new();
            for (k, v) in ld.iter() {
                match rd.get_item(&k).ok().flatten() {
                    Some(rv) if rv.eq(&v).unwrap_or(false) => {}
                    Some(rv) => diffs.push(format!("  {}: {} != {}", safe_repr(&k), safe_repr(&v), safe_repr(&rv))),
                    None => diffs.push(format!("  {} missing from right", safe_repr(&k))),
                }
            }
            for (k, _) in rd.iter() {
                if ld.get_item(&k).ok().flatten().is_none() {
                    diffs.push(format!("  {} missing from left", safe_repr(&k)));
                }
            }
            let _ = py;
            if diffs.is_empty() {
                None
            } else {
                Some(diffs.join("\n"))
            }
        }
        _ => None,
    }
}
