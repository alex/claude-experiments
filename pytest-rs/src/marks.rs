//! Markers: the `pytest.mark` namespace, `pytest.param`, and evaluation of the
//! built-in `skip`/`skipif`/`xfail`/`parametrize`/`usefixtures` markers.

use pyo3::exceptions::{PyAttributeError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyString, PyTuple};

use std::sync::{Arc, RwLock};

/// A single applied marker.
#[derive(Clone)]
pub struct MarkData {
    pub name: String,
    pub args: Py<PyTuple>,
    pub kwargs: Py<PyDict>,
}

impl MarkData {
    pub fn new(py: Python<'_>, name: &str) -> Self {
        MarkData {
            name: name.to_string(),
            args: PyTuple::empty(py).unbind(),
            kwargs: PyDict::new(py).unbind(),
        }
    }

    pub fn kwarg<'py>(&self, py: Python<'py>, key: &str) -> Option<Bound<'py, PyAny>> {
        self.kwargs.bind(py).get_item(key).ok().flatten()
    }

    pub fn arg<'py>(&self, py: Python<'py>, idx: usize) -> Option<Bound<'py, PyAny>> {
        let t = self.args.bind(py);
        if idx < t.len() {
            t.get_item(idx).ok()
        } else {
            None
        }
    }

    /// Build the Python-visible `Mark` object.
    pub fn to_py(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(
            py,
            Mark {
                name: self.name.clone(),
                args: self.args.clone_ref(py),
                kwargs: self.kwargs.clone_ref(py),
            },
        )?
        .into_any())
    }
}

/// `pytest.Mark` — the immutable record of an applied marker.
#[pyclass(module = "pytest", name = "Mark", frozen, from_py_object)]
#[derive(Clone)]
pub struct Mark {
    #[pyo3(get)]
    pub name: String,
    #[pyo3(get)]
    pub args: Py<PyTuple>,
    #[pyo3(get)]
    pub kwargs: Py<PyDict>,
}

#[pymethods]
impl Mark {
    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "Mark(name={:?}, args={}, kwargs={})",
            self.name,
            self.args.bind(py).repr().map(|r| r.to_string()).unwrap_or_default(),
            self.kwargs.bind(py).repr().map(|r| r.to_string()).unwrap_or_default(),
        )
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>, py: Python<'_>) -> bool {
        let Ok(o) = other.extract::<PyRef<'_, Mark>>() else { return false };
        self.name == o.name
            && self.args.bind(py).eq(o.args.bind(py)).unwrap_or(false)
            && self.kwargs.bind(py).eq(o.kwargs.bind(py)).unwrap_or(false)
    }
}

/// `pytest.MarkDecorator` — callable/appliable marker factory.
#[pyclass(module = "pytest", name = "MarkDecorator", frozen, from_py_object)]
#[derive(Clone)]
pub struct MarkDecorator {
    pub inner: Mark,
}

#[pymethods]
impl MarkDecorator {
    #[getter]
    fn name(&self) -> &str {
        &self.inner.name
    }

    #[getter]
    fn args(&self, py: Python<'_>) -> Py<PyTuple> {
        self.inner.args.clone_ref(py)
    }

    #[getter]
    fn kwargs(&self, py: Python<'_>) -> Py<PyDict> {
        self.inner.kwargs.clone_ref(py)
    }

    #[getter]
    fn mark(&self) -> Mark {
        self.inner.clone()
    }

    #[pyo3(signature = (*args, **kwargs))]
    fn with_args(&self, py: Python<'_>, args: &Bound<'_, PyTuple>, kwargs: Option<&Bound<'_, PyDict>>) -> MarkDecorator {
        MarkDecorator {
            inner: Mark {
                name: self.inner.name.clone(),
                args: args.clone().unbind(),
                kwargs: kwargs.map(|k| k.clone().unbind()).unwrap_or_else(|| PyDict::new(py).unbind()),
            },
        }
    }

    /// Either apply the marker to a single callable/class, or return a new
    /// decorator carrying the supplied arguments.
    #[pyo3(signature = (*args, **kwargs))]
    fn __call__<'py>(
        &self,
        py: Python<'py>,
        args: &Bound<'py, PyTuple>,
        kwargs: Option<&Bound<'py, PyDict>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        // A single positional argument that looks like a test function or a
        // class means "apply me"; anything else builds a new decorator.  This
        // mirrors `MarkDecorator.__call__` in pytest, and in particular it does
        // *not* depend on whether this decorator already carries arguments —
        // `@pytest.mark.skipif(cond, reason=...)` produces a decorator with
        // arguments which is then applied to the function.
        if args.len() == 1 && kwargs.map(|k| k.is_empty()).unwrap_or(true) {
            let obj = args.get_item(0)?;
            if is_test_target(&obj) {
                store_mark(py, &obj, &self.inner)?;
                return Ok(obj);
            }
        }
        let d = self.with_args(py, args, kwargs);
        Ok(Py::new(py, d)?.into_bound(py).into_any())
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!("MarkDecorator({})", self.inner.__repr__(py))
    }
}

/// Would pytest treat this object as something a marker can decorate?
fn is_test_target(obj: &Bound<'_, PyAny>) -> bool {
    if obj.is_instance_of::<pyo3::types::PyType>() {
        return true;
    }
    if !obj.is_callable() {
        return false;
    }
    match obj.getattr("__name__").and_then(|n| n.extract::<String>()) {
        Ok(name) => name != "<lambda>",
        Err(_) => false,
    }
}

/// Attach a mark to a function or class, mirroring pytest's `pytestmark`
/// attribute protocol so that user code inspecting it keeps working.
pub fn store_mark(py: Python<'_>, obj: &Bound<'_, PyAny>, mark: &Mark) -> PyResult<()> {
    let existing = obj.getattr("pytestmark").ok();
    let list = match existing {
        Some(v) if v.is_instance_of::<PyList>() => {
            // A class inheriting `pytestmark` must not mutate the parent's list.
            let own = obj
                .getattr("__dict__")
                .ok()
                .and_then(|d| d.get_item("pytestmark").ok())
                .is_some();
            if own {
                v.cast_into::<PyList>()?
            } else {
                let copy = PyList::empty(py);
                for item in v.try_iter()? {
                    copy.append(item?)?;
                }
                obj.setattr("pytestmark", &copy)?;
                copy
            }
        }
        _ => {
            let l = PyList::empty(py);
            obj.setattr("pytestmark", &l)?;
            l
        }
    };
    list.append(Py::new(py, mark.clone())?)?;
    Ok(())
}

/// `pytest.mark` — attribute access produces `MarkDecorator`s.
#[pyclass(module = "pytest", name = "MarkGenerator")]
pub struct MarkGenerator {
    /// Registered marker names (from the `markers` ini option) used by
    /// `--strict-markers`.
    pub known: Arc<RwLock<KnownMarkers>>,
}

#[derive(Default)]
pub struct KnownMarkers {
    pub names: rustc_hash::FxHashSet<String>,
    pub strict: bool,
}

const BUILTIN_MARKS: &[&str] = &[
    "skip",
    "skipif",
    "xfail",
    "parametrize",
    "usefixtures",
    "filterwarnings",
    "tryfirst",
    "trylast",
    "benchmark",
];

#[pymethods]
impl MarkGenerator {
    fn __getattr__(&self, py: Python<'_>, name: &str) -> PyResult<MarkDecorator> {
        if name.starts_with('_') {
            return Err(PyAttributeError::new_err(name.to_string()));
        }
        if !BUILTIN_MARKS.contains(&name) {
            let guard = self.known.read().unwrap();
            if guard.strict && !guard.names.contains(name) {
                return Err(PyErr::new::<crate::outcomes::UsageErrorPy, _>(format!(
                    "{} not found in `markers` configuration option",
                    crate::error::py_repr(name)
                )));
            }
        }
        Ok(MarkDecorator {
            inner: Mark {
                name: name.to_string(),
                args: PyTuple::empty(py).unbind(),
                kwargs: PyDict::new(py).unbind(),
            },
        })
    }
}

/// `pytest.param(...)` — a parametrisation entry with optional marks and id.
#[pyclass(module = "pytest", name = "ParameterSet", frozen, from_py_object)]
#[derive(Clone)]
pub struct ParameterSet {
    #[pyo3(get)]
    pub values: Py<PyTuple>,
    #[pyo3(get)]
    pub marks: Py<PyTuple>,
    #[pyo3(get)]
    pub id: Option<String>,
}

#[pymethods]
impl ParameterSet {
    #[new]
    #[pyo3(signature = (values, marks, id))]
    fn new(values: Py<PyTuple>, marks: Py<PyTuple>, id: Option<String>) -> Self {
        ParameterSet { values, marks, id }
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "ParameterSet(values={}, marks={}, id={:?})",
            self.values.bind(py).repr().map(|s| s.to_string()).unwrap_or_default(),
            self.marks.bind(py).repr().map(|s| s.to_string()).unwrap_or_default(),
            self.id
        )
    }

    fn __len__(&self, py: Python<'_>) -> usize {
        self.values.bind(py).len()
    }

    fn __getitem__(&self, py: Python<'_>, i: usize) -> PyResult<Py<PyAny>> {
        Ok(self.values.bind(py).get_item(i)?.unbind())
    }
}

#[pyfunction]
#[pyo3(signature = (*values, marks=None, id=None))]
pub fn param(
    py: Python<'_>,
    values: &Bound<'_, PyTuple>,
    marks: Option<&Bound<'_, PyAny>>,
    id: Option<String>,
) -> PyResult<ParameterSet> {
    let marks_tuple = match marks {
        None => PyTuple::empty(py),
        Some(m) => {
            if m.is_instance_of::<PyTuple>() || m.is_instance_of::<PyList>() {
                let mut v = Vec::new();
                for item in m.try_iter()? {
                    v.push(item?);
                }
                PyTuple::new(py, v)?
            } else {
                PyTuple::new(py, [m.clone()])?
            }
        }
    };
    Ok(ParameterSet {
        values: values.clone().unbind(),
        marks: marks_tuple.unbind(),
        id,
    })
}

/// Extract the `MarkData` list attached to an object via `pytestmark`.
pub fn own_marks(py: Python<'_>, obj: &Bound<'_, PyAny>) -> PyResult<Vec<MarkData>> {
    let Ok(attr) = obj.getattr("pytestmark") else { return Ok(Vec::new()) };
    let mut out = Vec::new();
    if attr.is_instance_of::<PyList>() || attr.is_instance_of::<PyTuple>() {
        for item in attr.try_iter()? {
            out.push(mark_from_py(py, &item?)?);
        }
    } else {
        out.push(mark_from_py(py, &attr)?);
    }
    Ok(out)
}

pub fn mark_from_py(py: Python<'_>, obj: &Bound<'_, PyAny>) -> PyResult<MarkData> {
    if let Ok(m) = obj.extract::<Mark>() {
        return Ok(MarkData { name: m.name, args: m.args, kwargs: m.kwargs });
    }
    if let Ok(d) = obj.extract::<MarkDecorator>() {
        return Ok(MarkData {
            name: d.inner.name,
            args: d.inner.args,
            kwargs: d.inner.kwargs,
        });
    }
    // Duck-typed marker (e.g. produced by a helper library).
    let name: String = obj.getattr("name")?.extract()?;
    let args = obj
        .getattr("args")
        .and_then(|a| a.cast_into::<PyTuple>().map_err(PyErr::from))
        .map(|t| t.unbind())
        .unwrap_or_else(|_| PyTuple::empty(py).unbind());
    let kwargs = obj
        .getattr("kwargs")
        .and_then(|a| a.cast_into::<PyDict>().map_err(PyErr::from))
        .map(|t| t.unbind())
        .unwrap_or_else(|_| PyDict::new(py).unbind());
    Ok(MarkData { name, args, kwargs })
}

/// Outcome of evaluating skip/skipif markers.
pub enum SkipDecision {
    Run,
    Skip(String),
}

/// The module a set of markers belongs to.  Held unevaluated because reaching
/// for `__dict__` costs a `getattr` and a shared reference count bump on every
/// test, while only a string `skipif`/`xfail` condition ever needs it.
#[derive(Clone, Copy)]
pub struct MarkScope<'a, 'py> {
    pub module: Option<&'a Bound<'py, PyAny>>,
}

impl<'py> MarkScope<'_, 'py> {
    fn globals(&self, _py: Python<'py>) -> Option<Bound<'py, PyDict>> {
        self.module?.getattr("__dict__").ok()?.cast_into::<PyDict>().ok()
    }

    pub fn none() -> Self {
        MarkScope { module: None }
    }
}

/// Evaluate a `condition` that may be a bool-ish object or a string expression
/// evaluated against the test module's globals (pytest's legacy behaviour).
fn eval_condition(py: Python<'_>, cond: &Bound<'_, PyAny>, scope: MarkScope<'_, '_>) -> PyResult<bool> {
    if let Ok(s) = cond.cast::<PyString>() {
        let src = s.to_str()?;
        let builtins = py.import("builtins")?;
        let g2 = PyDict::new(py);
        if let Some(g) = scope.globals(py) {
            for (k, v) in g.iter() {
                g2.set_item(k, v)?;
            }
        }
        g2.set_item("__builtins__", builtins)?;
        g2.set_item("os", py.import("os")?)?;
        g2.set_item("sys", py.import("sys")?)?;
        g2.set_item("platform", py.import("platform")?)?;
        let code = std::ffi::CString::new(src).map_err(|e| PyValueError::new_err(e.to_string()))?;
        let res = py.eval(&code, Some(&g2), None)?;
        return res.is_truthy();
    }
    cond.is_truthy()
}

/// Apply `skip`/`skipif` markers, returning a skip reason if any fires.
pub fn evaluate_skip(py: Python<'_>, marks: &[MarkData], scope: MarkScope<'_, '_>) -> PyResult<SkipDecision> {
    for m in marks {
        match m.name.as_str() {
            "skip" => {
                let reason = m
                    .kwarg(py, "reason")
                    .and_then(|r| r.extract::<String>().ok())
                    .or_else(|| m.arg(py, 0).and_then(|r| r.extract::<String>().ok()))
                    .unwrap_or_else(|| "unconditional skip".to_string());
                return Ok(SkipDecision::Skip(reason));
            }
            "skipif" => {
                let reason = m.kwarg(py, "reason").and_then(|r| r.extract::<String>().ok());
                let mut conditions: Vec<Bound<'_, PyAny>> = Vec::new();
                for c in m.args.bind(py).iter() {
                    conditions.push(c);
                }
                if let Some(c) = m.kwarg(py, "condition") {
                    conditions.push(c);
                }
                for cond in conditions {
                    if eval_condition(py, &cond, scope)? {
                        let r = reason.clone().unwrap_or_else(|| {
                            format!(
                                "condition: {}",
                                cond.repr().map(|s| s.to_string()).unwrap_or_default()
                            )
                        });
                        return Ok(SkipDecision::Skip(r));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(SkipDecision::Run)
}

/// Resolved `xfail` configuration for an item.
pub struct XfailSpec {
    pub reason: String,
    pub run: bool,
    pub strict: bool,
    pub raises: Option<Py<PyAny>>,
}

pub fn evaluate_xfail(
    py: Python<'_>,
    marks: &[MarkData],
    scope: MarkScope<'_, '_>,
    default_strict: bool,
) -> PyResult<Option<XfailSpec>> {
    for m in marks {
        if m.name != "xfail" {
            continue;
        }
        // `xfail(condition=False, *, reason='', raises=None, run=True,
        // strict=False)`: the only positional is the condition, and a string
        // condition is evaluated against the test module's globals.
        let mut fired = true;
        let args = m.args.bind(py);
        if !args.is_empty() {
            fired = eval_condition(py, &args.get_item(0)?, scope)?;
        }
        if let Some(c) = m.kwarg(py, "condition") {
            fired = eval_condition(py, &c, scope)?;
        }
        if !fired {
            continue;
        }
        let reason = m
            .kwarg(py, "reason")
            .and_then(|r| r.extract::<String>().ok())
            .unwrap_or_default();
        let run = m.kwarg(py, "run").map(|r| r.is_truthy().unwrap_or(true)).unwrap_or(true);
        let strict = m
            .kwarg(py, "strict")
            .map(|r| r.is_truthy().unwrap_or(false))
            .unwrap_or(default_strict);
        let raises = m.kwarg(py, "raises").map(|r| r.unbind());
        return Ok(Some(XfailSpec { reason, run, strict, raises }));
    }
    Ok(None)
}

/// Normalise the `argnames` argument of `parametrize` into a list of names.
pub fn parse_argnames(py: Python<'_>, argnames: &Bound<'_, PyAny>) -> PyResult<Vec<String>> {
    if let Ok(s) = argnames.cast::<PyString>() {
        return Ok(s
            .to_str()?
            .split(',')
            .map(|p| p.trim().to_string())
            .filter(|p| !p.is_empty())
            .collect());
    }
    let mut out = Vec::new();
    for item in argnames.try_iter()? {
        out.push(item?.extract::<String>().map_err(|_| {
            PyTypeError::new_err("parametrize() argnames must be a string or a sequence of strings")
        })?);
    }
    let _ = py;
    Ok(out)
}
