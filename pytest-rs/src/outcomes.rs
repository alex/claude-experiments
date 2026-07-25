//! Test outcome exceptions and the functions that raise them
//! (`pytest.skip`, `pytest.fail`, `pytest.xfail`, `pytest.exit`,
//! `pytest.importorskip`).

use pyo3::create_exception;
use pyo3::exceptions::{PyBaseException, PyException};
use pyo3::prelude::*;
use pyo3::types::{PyTuple, PyType};

create_exception!(pytest, OutcomeException, PyBaseException, "Base for test outcome control flow.");
create_exception!(pytest, Skipped, OutcomeException, "Raised to skip a test.");
create_exception!(pytest, Failed, OutcomeException, "Raised to fail a test explicitly.");
create_exception!(pytest, XFailed, Failed, "Raised to mark a test as expected-to-fail at runtime.");
create_exception!(pytest, Exit, PyBaseException, "Raised to exit the test session.");
create_exception!(pytest, UsageErrorPy, PyException, "Bad configuration or command line.");
create_exception!(pytest, PytestWarningPy, PyException, "Base pytest warning.");

/// Shared state carried on a raised `Skipped`, used by the runner.
pub const ATTR_MSG: &str = "msg";
pub const ATTR_ALLOW_MODULE_LEVEL: &str = "allow_module_level";
pub const ATTR_PYTRACE: &str = "pytrace";
pub const ATTR_RETURNCODE: &str = "returncode";

fn raise_with_attrs(py: Python<'_>, exc: PyErr, attrs: &[(&str, Py<PyAny>)]) -> PyErr {
    let val = exc.value(py);
    for (k, v) in attrs {
        let _ = val.setattr(*k, v);
    }
    exc
}

/// Build the `Skipped` exception `pytest.skip()` raises.
pub fn skip_error(py: Python<'_>, reason: &str, allow_module_level: bool) -> PyErr {
    let err = Skipped::new_err(reason.to_string());
    raise_with_attrs(
        py,
        err,
        &[
            (ATTR_MSG, reason.into_pyobject(py).unwrap().into_any().unbind()),
            (
                ATTR_ALLOW_MODULE_LEVEL,
                allow_module_level.into_pyobject(py).unwrap().to_owned().into_any().unbind(),
            ),
        ],
    )
}

/// `pytest.skip(...)` — implemented as a callable object so that
/// `pytest.skip.Exception` resolves the way user code expects.
#[pyclass(module = "pytest", name = "_SkipCallable", frozen)]
pub struct SkipCallable;

#[pymethods]
impl SkipCallable {
    #[pyo3(signature = (reason="", *, allow_module_level=false, msg=None))]
    fn __call__(
        &self,
        py: Python<'_>,
        reason: &str,
        allow_module_level: bool,
        msg: Option<&str>,
    ) -> PyResult<()> {
        Err(skip_error(py, msg.unwrap_or(reason), allow_module_level))
    }

    #[getter(Exception)]
    fn exception(&self, py: Python<'_>) -> Py<PyType> {
        py.get_type::<Skipped>().unbind()
    }
}

#[pyclass(module = "pytest", name = "_FailCallable", frozen)]
pub struct FailCallable;

/// Build the `Failed` exception `pytest.fail()` raises.
pub fn fail_error(py: Python<'_>, reason: &str, pytrace: bool) -> PyErr {
    let err = Failed::new_err(reason.to_string());
    raise_with_attrs(
        py,
        err,
        &[
            (ATTR_MSG, reason.into_pyobject(py).unwrap().into_any().unbind()),
            (ATTR_PYTRACE, pytrace.into_pyobject(py).unwrap().to_owned().into_any().unbind()),
        ],
    )
}

#[pymethods]
impl FailCallable {
    #[pyo3(signature = (reason="", pytrace=true, msg=None))]
    fn __call__(&self, py: Python<'_>, reason: &str, pytrace: bool, msg: Option<&str>) -> PyResult<()> {
        Err(fail_error(py, msg.unwrap_or(reason), pytrace))
    }

    #[getter(Exception)]
    fn exception(&self, py: Python<'_>) -> Py<PyType> {
        py.get_type::<Failed>().unbind()
    }
}

#[pyclass(module = "pytest", name = "_XfailCallable", frozen)]
pub struct XfailCallable;

#[pymethods]
impl XfailCallable {
    #[pyo3(signature = (reason=""))]
    fn __call__(&self, py: Python<'_>, reason: &str) -> PyResult<()> {
        let err = XFailed::new_err(reason.to_string());
        Err(raise_with_attrs(py, err, &[(ATTR_MSG, reason.into_pyobject(py).unwrap().into_any().unbind())]))
    }

    #[getter(Exception)]
    fn exception(&self, py: Python<'_>) -> Py<PyType> {
        py.get_type::<XFailed>().unbind()
    }
}

#[pyclass(module = "pytest", name = "_ExitCallable", frozen)]
pub struct ExitCallable;

#[pymethods]
impl ExitCallable {
    #[pyo3(signature = (reason="", returncode=None, msg=None))]
    fn __call__(&self, py: Python<'_>, reason: &str, returncode: Option<i32>, msg: Option<&str>) -> PyResult<()> {
        let reason = msg.unwrap_or(reason);
        let err = Exit::new_err(reason.to_string());
        let rc: Py<PyAny> = match returncode {
            Some(v) => v.into_pyobject(py).unwrap().into_any().unbind(),
            None => py.None(),
        };
        Err(raise_with_attrs(
            py,
            err,
            &[(ATTR_MSG, reason.into_pyobject(py).unwrap().into_any().unbind()), (ATTR_RETURNCODE, rc)],
        ))
    }

    #[getter(Exception)]
    fn exception(&self, py: Python<'_>) -> Py<PyType> {
        py.get_type::<Exit>().unbind()
    }
}

/// `pytest.importorskip(modname, minversion=None, reason=None, *, exc_type=None)`
#[pyfunction]
#[pyo3(signature = (modname, minversion=None, reason=None, *, exc_type=None))]
pub fn importorskip<'py>(
    py: Python<'py>,
    modname: &str,
    minversion: Option<&str>,
    reason: Option<String>,
    exc_type: Option<Bound<'py, PyAny>>,
) -> PyResult<Bound<'py, PyAny>> {
    let _ = exc_type;
    let module = match py.import(modname) {
        Ok(m) => m.into_any(),
        Err(e) => {
            if !e.is_instance_of::<pyo3::exceptions::PyImportError>(py) {
                return Err(e);
            }
            let msg = reason.unwrap_or_else(|| format!("could not import {}: {e}", crate::error::py_repr(modname)));
            return Err(skip_error(py, &msg, false));
        }
    };
    if let Some(minv) = minversion {
        let verattr: Option<String> = module.getattr("__version__").ok().and_then(|v| v.extract().ok());
        let ok = match &verattr {
            Some(v) => version_ge(v, minv),
            None => false,
        };
        if !ok {
            let msg = reason.unwrap_or_else(|| {
                format!(
                    "module {} has __version__ {}, required is: {}",
                    crate::error::py_repr(modname),
                    crate::error::py_repr(&verattr.unwrap_or_default()),
                    crate::error::py_repr(minv)
                )
            });
            return Err(skip_error(py, &msg, false));
        }
    }
    Ok(module)
}

/// Compare dotted version strings numerically where possible.
fn version_ge(a: &str, b: &str) -> bool {
    fn parts(s: &str) -> Vec<i64> {
        s.split(|c: char| !c.is_ascii_digit())
            .filter(|p| !p.is_empty())
            .filter_map(|p| p.parse().ok())
            .collect()
    }
    let (pa, pb) = (parts(a), parts(b));
    for i in 0..pa.len().max(pb.len()) {
        let x = pa.get(i).copied().unwrap_or(0);
        let y = pb.get(i).copied().unwrap_or(0);
        if x != y {
            return x > y;
        }
    }
    true
}

/// Classify a caught exception into a pytest outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Passed,
    Failed,
    Skipped,
    XFailed,
    XPassed,
    Error,
}

impl Outcome {
    pub fn letter(self) -> char {
        match self {
            Outcome::Passed => '.',
            Outcome::Failed => 'F',
            Outcome::Skipped => 's',
            Outcome::XFailed => 'x',
            Outcome::XPassed => 'X',
            Outcome::Error => 'E',
        }
    }

    pub fn word(self) -> &'static str {
        match self {
            Outcome::Passed => "PASSED",
            Outcome::Failed => "FAILED",
            Outcome::Skipped => "SKIPPED",
            Outcome::XFailed => "XFAIL",
            Outcome::XPassed => "XPASS",
            Outcome::Error => "ERROR",
        }
    }

    /// The `-r` report character that selects this outcome.
    pub fn report_char(self) -> char {
        match self {
            Outcome::Passed => 'p',
            Outcome::Failed => 'f',
            Outcome::Skipped => 's',
            Outcome::XFailed => 'x',
            Outcome::XPassed => 'X',
            Outcome::Error => 'E',
        }
    }
}

/// Read the `msg` attribute set on outcome exceptions, falling back to `str()`.
pub fn outcome_message(py: Python<'_>, err: &PyErr) -> String {
    let val = err.value(py);
    if let Ok(m) = val.getattr(ATTR_MSG) {
        if let Ok(s) = m.extract::<String>() {
            return s;
        }
    }
    match val.str() {
        Ok(s) => s.to_string(),
        Err(_) => String::new(),
    }
}

/// Register the exception types on a module object.
pub fn add_to_module(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add("OutcomeException", py.get_type::<OutcomeException>())?;
    m.add("Skipped", py.get_type::<Skipped>())?;
    m.add("Failed", py.get_type::<Failed>())?;
    m.add("XFailed", py.get_type::<XFailed>())?;
    m.add("Exit", py.get_type::<Exit>())?;
    m.add("UsageError", py.get_type::<UsageErrorPy>())?;
    m.add("PytestWarning", py.get_type::<PytestWarningPy>())?;
    let _ = PyTuple::empty(py);
    Ok(())
}
