//! `unittest.TestCase` support.
//!
//! unittest insists on running its own test protocol: `TestCase.run()` calls
//! `setUp`, the method, `tearDown` and the registered cleanups itself, and
//! reports what happened to a *result* object rather than by letting exceptions
//! escape.  Reimplementing that protocol would mean tracking CPython's copy of
//! it forever, so instead we hand `TestCase.run()` a result object of our own
//! and translate whatever it records back into the exception the rest of the
//! runner already knows how to classify.
//!
//! Deliberately absent: `addSubTest`.  unittest checks for it with `hasattr`
//! and falls back to letting subtest failures propagate normally, which is the
//! behaviour pytest has without `pytest-subtests` — and the behaviour whose
//! reporting we can actually render.

use pyo3::prelude::*;
use pyo3::types::PyTuple;
use std::sync::Mutex;

/// What the `TestCase` told us about itself.
#[derive(Default)]
enum Recorded {
    #[default]
    Success,
    /// An exception, already unwrapped from its `(type, value, tb)` triple.
    Raised(Py<PyAny>),
    Skipped(String),
    ExpectedFailure(String),
    UnexpectedSuccess(String),
}

#[pyclass]
pub struct Result {
    recorded: Mutex<Recorded>,
}

impl Result {
    fn set(&self, value: Recorded) {
        let mut slot = self.recorded.lock().unwrap();
        // unittest reports setUp, the test body and tearDown separately; the
        // first failure is the interesting one, as in pytest.
        if matches!(*slot, Recorded::Success) {
            *slot = value;
        }
    }
}

/// unittest hands errors over as `sys.exc_info()` triples.  Take the value out
/// and trim the leading frames belonging to unittest itself, so a failure
/// points at the test rather than at `case.py`.
fn from_exc_info(py: Python<'_>, raw: &Bound<'_, PyAny>) -> Option<Py<PyAny>> {
    // twisted.trial wraps the triple; pytest unwraps it the same way.
    let raw = raw.getattr("_rawexcinfo").unwrap_or_else(|_| raw.clone());
    let tup = raw.cast::<PyTuple>().ok()?;
    if tup.len() < 2 {
        return None;
    }
    let value = tup.get_item(1).ok()?;
    if value.is_none() {
        return None;
    }
    let _ = value.getattr("__traceback__").and_then(|tb| {
        let mut cur = tb;
        while !cur.is_none() && frame_is_unittest(&cur) {
            cur = cur.getattr("tb_next")?;
        }
        value.call_method1("with_traceback", (cur,))
    });
    let _ = py;
    Some(value.unbind())
}

fn frame_is_unittest(tb: &Bound<'_, PyAny>) -> bool {
    tb.getattr("tb_frame")
        .and_then(|f| f.getattr("f_globals"))
        .and_then(|g| g.get_item("__unittest"))
        .map(|v| v.is_truthy().unwrap_or(false))
        .unwrap_or(false)
}

// The method names are unittest's protocol, not ours.
#[allow(non_snake_case)]
#[pymethods]
impl Result {
    #[new]
    fn new() -> Self {
        Result { recorded: Mutex::new(Recorded::Success) }
    }

    fn startTest(&self, _test: &Bound<'_, PyAny>) {}
    fn stopTest(&self, _test: &Bound<'_, PyAny>) {}
    fn addSuccess(&self, _test: &Bound<'_, PyAny>) {}

    /// Python 3.12 warns when the result object cannot record durations; we
    /// time tests ourselves, so accepting and discarding is enough.
    fn addDuration(&self, _test: &Bound<'_, PyAny>, _elapsed: f64) {}

    fn addError(&self, py: Python<'_>, _test: &Bound<'_, PyAny>, err: &Bound<'_, PyAny>) {
        if let Some(v) = from_exc_info(py, err) {
            self.set(Recorded::Raised(v));
        }
    }

    fn addFailure(&self, py: Python<'_>, _test: &Bound<'_, PyAny>, err: &Bound<'_, PyAny>) {
        if let Some(v) = from_exc_info(py, err) {
            self.set(Recorded::Raised(v));
        }
    }

    fn addSkip(&self, _test: &Bound<'_, PyAny>, reason: String) {
        self.set(Recorded::Skipped(reason));
    }

    #[pyo3(signature = (test, err, reason=String::new()))]
    fn addExpectedFailure(&self, test: &Bound<'_, PyAny>, err: &Bound<'_, PyAny>, reason: String) {
        let _ = (test, err);
        self.set(Recorded::ExpectedFailure(reason));
    }

    #[pyo3(signature = (test, reason=String::new()))]
    fn addUnexpectedSuccess(&self, test: &Bound<'_, PyAny>, reason: String) {
        let _ = test;
        self.set(Recorded::UnexpectedSuccess(reason));
    }
}

/// Run one `unittest.TestCase` method and re-raise whatever it recorded.
///
/// The translation back into exceptions is what lets the ordinary reporting
/// path handle these tests: a recorded failure becomes the original exception,
/// a skip becomes `Skipped`, `@unittest.expectedFailure` becomes `XFailed`, and
/// an unexpected success becomes a plain failure — the same four outcomes
/// pytest's unittest integration produces.
pub fn run_case<'py>(py: Python<'py>, instance: &Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
    let result = Py::new(py, Result::new())?;
    let kwargs = pyo3::types::PyDict::new(py);
    kwargs.set_item("result", result.bind(py))?;
    instance.call((), Some(&kwargs))?;
    let recorded = std::mem::take(&mut *result.bind(py).borrow().recorded.lock().unwrap());
    match recorded {
        Recorded::Success => Ok(py.None().into_bound(py)),
        Recorded::Raised(v) => Err(PyErr::from_value(v.into_bound(py))),
        Recorded::Skipped(reason) => Err(crate::outcomes::skip_error(py, &reason, false)),
        Recorded::ExpectedFailure(reason) => Err(crate::outcomes::xfail_error(py, &reason)),
        Recorded::UnexpectedSuccess(reason) => {
            let message = match reason.is_empty() {
                true => "Unexpected success".to_string(),
                false => format!("Unexpected success: {reason}"),
            };
            Err(crate::outcomes::fail_error(py, &message, false))
        }
    }
}
