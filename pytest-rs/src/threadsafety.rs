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
use std::sync::{Mutex, OnceLock};

/// Global/attribute names that imply mutation of interpreter-wide state.
const HOSTILE_NAMES: &[&str] = &[
    // process environment / cwd
    "chdir",
    "putenv",
    "unsetenv",
    "umask",
    // interpreter knobs
    "setrecursionlimit",
    "setswitchinterval",
    "settrace",
    "setprofile",
    "set_int_max_str_digits",
    "setdlopenflags",
    "setlocale",
    "set_wakeup_fd",
    "signal",
    "alarm",
    // stdio replacement
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
];

/// Names that are only hazardous when the interpreter's warning filters are
/// process-global.  CPython 3.14 makes `warnings.catch_warnings()` use a
/// context variable (always on for free-threaded builds), at which point these
/// are perfectly safe to run concurrently.
const WARNING_NAMES: &[&str] = &[
    "warns",
    "deprecated_call",
    "catch_warnings",
    "simplefilter",
    "filterwarnings",
    "resetwarnings",
    "_filters_mutated",
    "recwarn",
];

/// Names that are only hazardous when the referencing code also mutates a
/// mapping.  `os.environ` is read far more often than it is written — a bare
/// `os.environ.copy()` is perfectly safe — so flagging every reference would
/// serialise a large slice of a suite for nothing.
const CONDITIONAL_MAPPING_NAMES: &[&str] = &["environ"];

/// Method names that mutate a mapping in place.
const MAPPING_MUTATORS: &[&str] = &["setdefault", "update", "clear", "popitem", "pop", "__setitem__", "__delitem__"];

/// Markers that let a test opt in or out explicitly.
pub const MARK_THREAD_UNSAFE: &[&str] = &["serial", "thread_unsafe", "no_parallel", "forked"];
pub const MARK_THREAD_SAFE: &[&str] = &["thread_safe", "parallel"];

static CONTEXT_AWARE_WARNINGS: OnceLock<bool> = OnceLock::new();

/// Does this interpreter scope `warnings.catch_warnings()` per context?
pub fn warnings_are_context_aware(py: Python<'_>) -> bool {
    *CONTEXT_AWARE_WARNINGS.get_or_init(|| {
        let Ok(sys) = py.import("sys") else { return false };
        let Ok(flags) = sys.getattr("flags") else { return false };
        let aware = flags
            .getattr("context_aware_warnings")
            .and_then(|v| v.is_truthy())
            .unwrap_or(false);
        let inherit = flags
            .getattr("thread_inherit_context")
            .and_then(|v| v.is_truthy())
            .unwrap_or(false);
        aware && inherit
    })
}

#[derive(Default)]
struct Cache {
    /// keyed by `id(code)`; code objects are kept alive by their owners for the
    /// duration of the run, so the pointer identity is stable.
    seen: FxHashMap<usize, Option<String>>,
}

static CACHE: Mutex<Option<Cache>> = Mutex::new(None);

fn cached_lookup(key: usize) -> Option<Option<String>> {
    let guard = CACHE.lock().ok()?;
    guard.as_ref()?.seen.get(&key).cloned()
}

fn cache_store(key: usize, val: Option<String>) {
    if let Ok(mut guard) = CACHE.lock() {
        guard.get_or_insert_with(Cache::default).seen.insert(key, val);
    }
}

/// Maximum call-graph depth followed when a test delegates to module helpers.
const MAX_DEPTH: usize = 4;

/// Analyse a callable.  Returns the name of the first hazardous reference
/// found, or `None` when the callable looks safe to run concurrently.
pub fn thread_hostile_reason(py: Python<'_>, func: &Bound<'_, PyAny>) -> PyResult<Option<String>> {
    let Ok(code) = func.getattr("__code__") else { return Ok(None) };
    let key = code.as_ptr() as usize;
    if let Some(v) = cached_lookup(key) {
        return Ok(v);
    }
    let globals = func.getattr("__globals__").ok().and_then(|g| g.cast_into::<PyDict>().ok());
    let mut visited: FxHashSet<usize> = FxHashSet::default();
    let check_warnings = !warnings_are_context_aware(py);
    let result = scan_code(py, &code, globals.as_ref(), 0, &mut visited, check_warnings)?;
    cache_store(key, result.clone());
    Ok(result)
}

/// Convenience wrapper for callers that only need the yes/no answer.
pub fn callable_is_thread_hostile(py: Python<'_>, func: &Bound<'_, PyAny>) -> PyResult<bool> {
    Ok(thread_hostile_reason(py, func)?.is_some())
}

fn scan_code(
    py: Python<'_>,
    code: &Bound<'_, PyAny>,
    globals: Option<&Bound<'_, PyDict>>,
    depth: usize,
    visited: &mut FxHashSet<usize>,
    check_warnings: bool,
) -> PyResult<Option<String>> {
    let ptr = code.as_ptr() as usize;
    if !visited.insert(ptr) {
        return Ok(None);
    }
    let names = code.getattr("co_names")?;
    let names = names.cast::<PyTuple>()?;
    let mut referenced: Vec<String> = Vec::with_capacity(names.len());
    let mut conditional: Option<String> = None;
    for n in names.iter() {
        let s: String = n.extract()?;
        if HOSTILE_NAMES.contains(&s.as_str()) {
            return Ok(Some(s));
        }
        if check_warnings && WARNING_NAMES.contains(&s.as_str()) {
            return Ok(Some(s));
        }
        if CONDITIONAL_MAPPING_NAMES.contains(&s.as_str()) {
            conditional = Some(s.clone());
        }
        referenced.push(s);
    }
    if let Some(name) = conditional {
        if mutates_via(py, code, &name)? {
            return Ok(Some(name));
        }
    }

    // Nested code objects: comprehensions, lambdas, inner functions.
    let consts = code.getattr("co_consts")?;
    for c in consts.cast::<PyTuple>()?.iter() {
        if c.getattr("co_names").is_ok() {
            if let Some(r) = scan_code(py, &c, globals, depth, visited, check_warnings)? {
                return Ok(Some(r));
            }
        }
    }

    if depth >= MAX_DEPTH {
        return Ok(None);
    }
    // Follow calls to helpers that live in the same module.  Test suites
    // routinely factor `pytest.warns` blocks into shared utilities.
    let Some(globals) = globals else { return Ok(None) };
    for name in referenced {
        let Ok(Some(target)) = globals.get_item(name.as_str()) else { continue };
        if let Ok(inner) = target.getattr("__code__") {
            let inner_globals = target.getattr("__globals__").ok().and_then(|g| g.cast_into::<PyDict>().ok());
            if let Some(r) = scan_code(
                py,
                &inner,
                inner_globals.as_ref().or(Some(globals)),
                depth + 1,
                visited,
                check_warnings,
            )? {
                return Ok(Some(r));
            }
        }
    }
    Ok(None)
}

/// Is `name` used in a way that mutates it, rather than merely read?
///
/// Name-level analysis cannot tell `os.environ.copy()` (safe, and common) from
/// `os.environ["X"] = v` (not safe).  Disassembling closes that gap with a small
/// peephole: find where `name` is loaded, then look at the handful of
/// instructions that consume it.  Writing to a subscript, deleting one, or
/// calling a mutating method right after the load means mutation; anything else
/// is a read.
///
/// Only reached for the few functions that mention a conditionally hazardous
/// name, so the cost of disassembling does not matter.  Anything we cannot
/// analyse is reported as mutating.
fn mutates_via(py: Python<'_>, code: &Bound<'_, PyAny>, name: &str) -> PyResult<bool> {
    const WINDOW: usize = 4;
    let Ok(dis) = py.import("dis") else { return Ok(true) };
    let Ok(instructions) = dis.call_method1("get_instructions", (code,)) else {
        return Ok(true);
    };
    let mut ops: Vec<(String, Option<String>)> = Vec::new();
    for ins in instructions.try_iter()? {
        let ins = ins?;
        let opname: String = ins.getattr("opname")?.extract()?;
        let argval = ins
            .getattr("argval")
            .ok()
            .and_then(|v| v.extract::<String>().ok());
        ops.push((opname, argval));
    }
    for (i, (_, argval)) in ops.iter().enumerate() {
        if argval.as_deref() != Some(name) {
            continue;
        }
        for (opname, next_arg) in ops.iter().skip(i + 1).take(WINDOW) {
            if opname == "STORE_SUBSCR" || opname == "DELETE_SUBSCR" {
                return Ok(true);
            }
            if (opname == "LOAD_METHOD" || opname == "LOAD_ATTR")
                && next_arg
                    .as_deref()
                    .map(|a| MAPPING_MUTATORS.contains(&a))
                    .unwrap_or(false)
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}
