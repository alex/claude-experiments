//! Construction of the synthetic `pytest` module.
//!
//! Test suites and conftest files `import pytest`; rather than shadowing an
//! installed pytest on disk we build the module object here and install it into
//! `sys.modules` before anything is imported.  That keeps a real pytest
//! installation usable in the same environment.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};
use std::sync::{Arc, RwLock};

use crate::marks::{KnownMarkers, MarkGenerator};

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
/// Reported as `pytest.__version__` so version gates in test suites (and the
/// `minversion` ini option) keep working.
pub const COMPAT_PYTEST_VERSION: &str = "8.4.0";

/// No-op stand-ins for pluggy's decorators.
#[pyclass(module = "pytest", name = "_HookMarker", frozen)]
pub struct HookMarker;

#[pymethods]
impl HookMarker {
    #[pyo3(signature = (function=None, **kwargs))]
    fn __call__<'py>(
        &self,
        py: Python<'py>,
        function: Option<Bound<'py, PyAny>>,
        kwargs: Option<&Bound<'py, PyDict>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let _ = kwargs;
        match function {
            Some(f) => Ok(f),
            None => Ok(Py::new(py, HookMarker)?.into_bound(py).into_any()),
        }
    }
}

/// `pytest.Stash` — a plain dict subclass is close enough for plugin code.
#[pyclass(module = "pytest", name = "StashKey", frozen)]
pub struct StashKey;

#[pymethods]
impl StashKey {
    #[new]
    fn new() -> Self {
        StashKey
    }
}

#[pyfunction]
#[pyo3(signature = (*names))]
fn register_assert_rewrite(names: &Bound<'_, PyTuple>) {
    // Assertion introspection is done lazily on failure, so there is nothing
    // to register; accept the call for compatibility.
    let _ = names;
}

#[pyfunction]
fn set_trace(py: Python<'_>) -> PyResult<()> {
    let pdb = py.import("pdb")?;
    pdb.call_method0("set_trace")?;
    Ok(())
}

#[pyfunction]
#[pyo3(signature = (*args, **kwargs))]
fn console_main(py: Python<'_>, args: &Bound<'_, PyTuple>, kwargs: Option<&Bound<'_, PyDict>>) -> PyResult<i32> {
    let _ = (args, kwargs);
    let argv: Vec<String> = py
        .import("sys")?
        .getattr("argv")?
        .try_iter()?
        .filter_map(|a| a.ok().and_then(|a| a.extract::<String>().ok()))
        .skip(1)
        .collect();
    crate::run_main(py, argv)
}

/// Build the module object and install it as `pytest`.
pub fn install(py: Python<'_>, known: Arc<RwLock<KnownMarkers>>) -> PyResult<Bound<'_, PyModule>> {
    let m = PyModule::new(py, "pytest")?;
    m.add("__version__", COMPAT_PYTEST_VERSION)?;
    m.add("__pytest_rs_version__", VERSION)?;
    m.add("version_tuple", (8, 4, 0))?;

    crate::outcomes::add_to_module(py, &m)?;

    m.add_function(wrap_pyfunction!(crate::fixtures::fixture, &m)?)?;
    m.add_function(wrap_pyfunction!(crate::fixtures::yield_fixture, &m)?)?;
    m.add_function(wrap_pyfunction!(crate::marks::param, &m)?)?;
    m.add_function(wrap_pyfunction!(crate::raises::raises, &m)?)?;
    m.add_function(wrap_pyfunction!(crate::raises::warns, &m)?)?;
    m.add_function(wrap_pyfunction!(crate::raises::deprecated_call, &m)?)?;
    m.add_function(wrap_pyfunction!(crate::raises::approx, &m)?)?;
    m.add_function(wrap_pyfunction!(crate::outcomes::importorskip, &m)?)?;
    m.add_function(wrap_pyfunction!(register_assert_rewrite, &m)?)?;
    m.add_function(wrap_pyfunction!(set_trace, &m)?)?;
    m.add_function(wrap_pyfunction!(console_main, &m)?)?;
    m.add("main", m.getattr("console_main")?)?;

    m.add("skip", Py::new(py, crate::outcomes::SkipCallable)?)?;
    m.add("fail", Py::new(py, crate::outcomes::FailCallable)?)?;
    m.add("xfail", Py::new(py, crate::outcomes::XfailCallable)?)?;
    m.add("exit", Py::new(py, crate::outcomes::ExitCallable)?)?;

    m.add("mark", Py::new(py, MarkGenerator { known })?)?;
    m.add("hookimpl", Py::new(py, HookMarker)?)?;
    m.add("hookspec", Py::new(py, HookMarker)?)?;

    m.add_class::<crate::marks::Mark>()?;
    m.add_class::<crate::marks::MarkDecorator>()?;
    m.add_class::<crate::marks::ParameterSet>()?;
    m.add_class::<crate::raises::ExceptionInfo>()?;
    m.add_class::<crate::raises::RaisesContext>()?;
    m.add_class::<crate::raises::WarningsChecker>()?;
    m.add_class::<crate::session::Config>()?;
    m.add_class::<crate::session::ArgParser>()?;
    m.add_class::<crate::session::PyItem>()?;
    m.add_class::<crate::runtime::FixtureRequest>()?;
    m.add_class::<crate::builtins::MonkeyPatch>()?;
    m.add_class::<crate::builtins::TmpPathFactory>()?;
    m.add_class::<crate::builtins::Capture>()?;
    m.add_class::<crate::bench::BenchmarkFixture>()?;
    m.add_class::<StashKey>()?;

    // Aliases used in `isinstance` checks and type annotations.
    let item_cls = m.getattr("Function")?;
    m.add("Item", &item_cls)?;
    m.add("Node", &item_cls)?;
    m.add("Collector", &item_cls)?;
    m.add("Module", &item_cls)?;
    m.add("Class", &item_cls)?;
    m.add("Session", &item_cls)?;
    m.add("File", &item_cls)?;
    m.add("Package", &item_cls)?;
    m.add("FixtureLookupError", py.get_type::<pyo3::exceptions::PyLookupError>())?;
    m.add("PytestDeprecationWarning", py.get_type::<pyo3::exceptions::PyDeprecationWarning>())?;
    m.add("PytestUnraisableExceptionWarning", py.get_type::<pyo3::exceptions::PyRuntimeWarning>())?;
    m.add("PytestUnhandledThreadExceptionWarning", py.get_type::<pyo3::exceptions::PyRuntimeWarning>())?;
    m.add("PytestCollectionWarning", py.get_type::<pyo3::exceptions::PyUserWarning>())?;
    m.add("PytestConfigWarning", py.get_type::<pyo3::exceptions::PyUserWarning>())?;
    m.add("PytestAssertRewriteWarning", py.get_type::<pyo3::exceptions::PyUserWarning>())?;
    m.add("PytestRemovedIn9Warning", py.get_type::<pyo3::exceptions::PyDeprecationWarning>())?;

    let all = PyList::new(
        py,
        [
            "approx",
            "Config",
            "deprecated_call",
            "exit",
            "ExceptionInfo",
            "fail",
            "Failed",
            "fixture",
            "Function",
            "hookimpl",
            "hookspec",
            "importorskip",
            "Item",
            "main",
            "mark",
            "Mark",
            "MarkDecorator",
            "MonkeyPatch",
            "param",
            "Parser",
            "raises",
            "register_assert_rewrite",
            "set_trace",
            "skip",
            "Skipped",
            "UsageError",
            "warns",
            "xfail",
            "yield_fixture",
        ],
    )?;
    m.add("__all__", all)?;

    let sys = py.import("sys")?;
    let modules = sys.getattr("modules")?;
    modules.set_item("pytest", &m)?;
    // A handful of libraries poke at `_pytest.*`; give them something inert.
    let underscore = PyModule::new(py, "_pytest")?;
    underscore.add("__version__", COMPAT_PYTEST_VERSION)?;
    modules.set_item("_pytest", &underscore)?;
    Ok(m)
}
