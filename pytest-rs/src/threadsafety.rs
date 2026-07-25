//! Static thread-safety analysis.
//!
//! Tests run on a pool of worker threads by default.  Some test bodies touch
//! process-global state — the `warnings` filter stack, `os.environ`, the
//! current working directory, the recursion limit — and cannot safely overlap
//! with anything else.  Rather than requiring users to annotate those tests we
//! inspect the compiled code objects: `co_names` records every global and
//! attribute name a function references, so a cheap recursive scan finds the
//! hazardous ones with no import-time rewriting and no runtime cost.
//!
//! The analysis is intentionally conservative in the direction of correctness:
//! a false positive only costs a little parallelism, a false negative costs a
//! flaky test.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyTuple};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Mutex;

/// Global/attribute names that imply mutation of interpreter-wide state.
const HOSTILE_NAMES: &[&str] = &[
    // warnings machinery — the filter stack is process global before 3.14's
    // context-aware warnings, and `catch_warnings` swaps it wholesale.
    "warns",
    "deprecated_call",
    "catch_warnings",
    "simplefilter",
    "filterwarnings",
    "resetwarnings",
    "_filters_mutated",
    // process environment / cwd
    "chdir",
    "putenv",
    "unsetenv",
    "environ",
    "umask",
    // interpreter knobs
    "setrecursionlimit",
    "setswitchinterval",
    "settrace",
    "setprofile",
    "set_int_max_str_digits",
    "setdlopenflags",
    "setcheckinterval",
    "setlocale",
    "set_wakeup_fd",
    "signal",
    "alarm",
    // stdio replacement
    "setrecursionlimit",
    "reconfigure",
    // global RNG reseeding
    "seed",
    // cryptography-specific global switches
    "_enable_fips",
    "_disable_fips",
    // fixtures whose implementation mutates globals
    "monkeypatch",
    "capsys",
    "capfd",
    "capsysbinary",
    "capfdbinary",
    "recwarn",
];

/// Markers that let a test opt in or out explicitly.
pub const MARK_THREAD_UNSAFE: &[&str] = &["serial", "thread_unsafe", "no_parallel", "forked"];
pub const MARK_THREAD_SAFE: &[&str] = &["thread_safe", "parallel"];

#[derive(Default)]
struct Cache {
    /// keyed by `id(code)`; code objects are kept alive by their owners for the
    /// duration of the run, so the pointer identity is stable.
    seen: FxHashMap<usize, bool>,
}

static CACHE: Mutex<Option<Cache>> = Mutex::new(None);

fn cached_lookup(key: usize) -> Option<bool> {
    let guard = CACHE.lock().ok()?;
    guard.as_ref()?.seen.get(&key).copied()
}

fn cache_store(key: usize, val: bool) {
    if let Ok(mut guard) = CACHE.lock() {
        guard.get_or_insert_with(Cache::default).seen.insert(key, val);
    }
}

/// Maximum call-graph depth followed when a test delegates to module helpers.
const MAX_DEPTH: usize = 4;

/// Analyse a callable, returning `true` if it may touch global state.
pub fn callable_is_thread_hostile(py: Python<'_>, func: &Bound<'_, PyAny>) -> PyResult<bool> {
    let Ok(code) = func.getattr("__code__") else { return Ok(false) };
    let key = code.as_ptr() as usize;
    if let Some(v) = cached_lookup(key) {
        return Ok(v);
    }
    let globals = func.getattr("__globals__").ok().and_then(|g| g.cast_into::<PyDict>().ok());
    let mut visited: FxHashSet<usize> = FxHashSet::default();
    let result = scan_code(py, &code, globals.as_ref(), 0, &mut visited)?;
    cache_store(key, result);
    Ok(result)
}

fn scan_code(
    py: Python<'_>,
    code: &Bound<'_, PyAny>,
    globals: Option<&Bound<'_, PyDict>>,
    depth: usize,
    visited: &mut FxHashSet<usize>,
) -> PyResult<bool> {
    let ptr = code.as_ptr() as usize;
    if !visited.insert(ptr) {
        return Ok(false);
    }
    let names = code.getattr("co_names")?;
    let names = names.cast::<PyTuple>()?;
    let mut referenced: Vec<String> = Vec::with_capacity(names.len());
    for n in names.iter() {
        let s: String = n.extract()?;
        if HOSTILE_NAMES.contains(&s.as_str()) {
            return Ok(true);
        }
        referenced.push(s);
    }

    // Nested code objects: comprehensions, lambdas, inner functions.
    let consts = code.getattr("co_consts")?;
    for c in consts.cast::<PyTuple>()?.iter() {
        if c.getattr("co_names").is_ok() && scan_code(py, &c, globals, depth, visited)? {
            return Ok(true);
        }
    }

    if depth >= MAX_DEPTH {
        return Ok(false);
    }
    // Follow calls to helpers that live in the same module.  Test suites
    // routinely factor `pytest.warns` blocks into shared utilities.
    let Some(globals) = globals else { return Ok(false) };
    for name in referenced {
        let Ok(Some(target)) = globals.get_item(name.as_str()) else { continue };
        if let Ok(inner) = target.getattr("__code__") {
            let inner_globals = target.getattr("__globals__").ok().and_then(|g| g.cast_into::<PyDict>().ok());
            if scan_code(py, &inner, inner_globals.as_ref().or(Some(globals)), depth + 1, visited)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// Reset the analysis cache (used by tests).
pub fn clear_cache() {
    if let Ok(mut guard) = CACHE.lock() {
        *guard = None;
    }
}
