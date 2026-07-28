//! `pytest.raises`, `pytest.warns`, `pytest.deprecated_call`, `pytest.approx`
//! and the `ExceptionInfo` object they hand back.

use pyo3::exceptions::{PyAssertionError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple, PyType};

use crate::outcomes::{fail_error, Failed};

/// `pytest.ExceptionInfo` — a lazily populated wrapper around a caught
/// exception.
#[pyclass(module = "pytest", name = "ExceptionInfo")]
pub struct ExceptionInfo {
    pub excinfo: Option<(Py<PyAny>, Py<PyAny>, Py<PyAny>)>,
    /// Where the raising expression lived, used in error messages.
    pub string_repr: Option<String>,
}

impl ExceptionInfo {
    pub fn empty() -> Self {
        ExceptionInfo { excinfo: None, string_repr: None }
    }

    pub fn from_err(py: Python<'_>, err: &PyErr) -> Self {
        let ty = err.get_type(py).into_any().unbind();
        let val = err.value(py).clone().into_any().unbind();
        let tb = match err.traceback(py) {
            Some(t) => t.into_any().unbind(),
            None => py.None(),
        };
        ExceptionInfo { excinfo: Some((ty, val, tb)), string_repr: None }
    }
}

#[pymethods]
impl ExceptionInfo {
    #[getter]
    fn value(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        match &self.excinfo {
            Some((_, v, _)) => Ok(v.clone_ref(py)),
            None => Err(PyAssertionError::new_err(
                "ExceptionInfo has no exception; the `with` block did not raise",
            )),
        }
    }

    #[getter]
    fn type_(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        self.get_type(py)
    }

    #[getter(r#type)]
    fn get_type(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        match &self.excinfo {
            Some((t, _, _)) => Ok(t.clone_ref(py)),
            None => Err(PyAssertionError::new_err("ExceptionInfo has no exception")),
        }
    }

    #[getter]
    fn tb(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        self.traceback(py)
    }

    #[getter]
    fn traceback(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        match &self.excinfo {
            Some((_, _, tb)) => Ok(tb.clone_ref(py)),
            None => Ok(py.None()),
        }
    }

    #[getter]
    fn typename(&self, py: Python<'_>) -> PyResult<String> {
        let t = self.get_type(py)?;
        Ok(t.bind(py)
            .getattr("__name__")
            .and_then(|n| n.extract::<String>())
            .unwrap_or_else(|_| "?".to_string()))
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        match &self.excinfo {
            Some((_, v, _)) => format!(
                "<ExceptionInfo {} tblen=?>",
                v.bind(py).repr().map(|s| s.to_string()).unwrap_or_default()
            ),
            None => "<ExceptionInfo for raises contextmanager>".to_string(),
        }
    }

    /// `str(excinfo.value)` restricted to the exception line, like pytest.
    fn exconly(&self, py: Python<'_>, tryshort: Option<bool>) -> PyResult<String> {
        let _ = tryshort;
        let ty = self.typename(py)?;
        let v = self.value(py)?;
        let s = v.bind(py).str()?.to_string();
        if s.is_empty() {
            Ok(ty)
        } else {
            Ok(format!("{ty}: {s}"))
        }
    }

    /// `excinfo.match(regexp)` — assert the string form matches.
    fn r#match(&self, py: Python<'_>, regexp: &Bound<'_, PyAny>) -> PyResult<bool> {
        let v = self.value(py)?;
        let s = v.bind(py).str()?.to_string();
        let re = py.import("re")?;
        let found = re.call_method1("search", (regexp, &s))?;
        if found.is_none() {
            let pat = regexp.str()?.to_string();
            return Err(PyAssertionError::new_err(format!(
                "Regex pattern did not match.\n Regex: {pat:?}\n Input: {s:?}"
            )));
        }
        Ok(true)
    }

    fn errisinstance(&self, py: Python<'_>, cls: &Bound<'_, PyAny>) -> PyResult<bool> {
        let v = self.value(py)?;
        v.bind(py).is_instance(cls)
    }

    fn getrepr(&self, py: Python<'_>, _args: &Bound<'_, PyTuple>, _kwargs: Option<&Bound<'_, PyDict>>) -> PyResult<String> {
        self.exconly(py, None)
    }
}

/// Context manager returned by `pytest.raises`.
#[pyclass(module = "pytest", name = "RaisesContext")]
pub struct RaisesContext {
    expected: Py<PyAny>,
    match_expr: Option<Py<PyAny>>,
    info: Option<Py<ExceptionInfo>>,
}

#[pymethods]
impl RaisesContext {
    fn __enter__(&mut self, py: Python<'_>) -> PyResult<Py<ExceptionInfo>> {
        let info = Py::new(py, ExceptionInfo::empty())?;
        self.info = Some(info.clone_ref(py));
        Ok(info)
    }

    #[pyo3(signature = (exc_type, exc_val, tb))]
    fn __exit__(
        &mut self,
        py: Python<'_>,
        exc_type: Option<Bound<'_, PyAny>>,
        exc_val: Option<Bound<'_, PyAny>>,
        tb: Option<Bound<'_, PyAny>>,
    ) -> PyResult<bool> {
        let Some(exc_type) = exc_type.filter(|t| !t.is_none()) else {
            let expected_repr = format_expected(py, self.expected.bind(py))?;
            return Err(fail_error(py, &format!("DID NOT RAISE {expected_repr}"), true));
        };
        let exc_val = exc_val.unwrap_or_else(|| py.None().into_bound(py));
        // Let non-matching exceptions propagate.
        if !exc_type.is_instance_of::<PyType>() {
            return Ok(false);
        }
        let is_expected = exc_val.is_instance(self.expected.bind(py))?;
        if !is_expected {
            return Ok(false);
        }
        if let Some(info) = &self.info {
            let mut borrowed = info.bind(py).borrow_mut();
            borrowed.excinfo = Some((
                exc_type.unbind(),
                exc_val.clone().unbind(),
                tb.map(|t| t.unbind()).unwrap_or_else(|| py.None()),
            ));
        }
        if let Some(m) = &self.match_expr {
            let s = exc_val.str()?.to_string();
            let re = py.import("re")?;
            let found = re.call_method1("search", (m.bind(py), &s))?;
            if found.is_none() {
                let pat = m.bind(py).str()?.to_string();
                return Err(PyAssertionError::new_err(format!(
                    "Regex pattern did not match.\n Regex: {pat:?}\n Input: {s:?}"
                )));
            }
        }
        Ok(true)
    }
}

/// `issubclass` for objects we only hold as `PyAny`.
pub fn is_subclass_of(cls: &Bound<'_, PyAny>, parent: &Bound<'_, PyAny>) -> PyResult<bool> {
    match cls.cast::<PyType>() {
        Ok(t) => t.is_subclass(parent),
        Err(_) => Ok(false),
    }
}

fn format_expected(py: Python<'_>, expected: &Bound<'_, PyAny>) -> PyResult<String> {
    if let Ok(t) = expected.cast::<PyTuple>() {
        let mut names = Vec::new();
        for item in t.iter() {
            names.push(item.repr()?.to_string());
        }
        return Ok(format!("({})", names.join(", ")));
    }
    let _ = py;
    Ok(expected.repr()?.to_string())
}

/// `pytest.raises(expected, ...)`.
#[pyfunction]
#[pyo3(signature = (expected_exception, *args, **kwargs))]
pub fn raises<'py>(
    py: Python<'py>,
    expected_exception: Bound<'py, PyAny>,
    args: &Bound<'py, PyTuple>,
    kwargs: Option<&Bound<'py, PyDict>>,
) -> PyResult<Bound<'py, PyAny>> {
    validate_expected(&expected_exception)?;
    let match_expr = kwargs.and_then(|k| k.get_item("match").ok().flatten()).map(|v| v.unbind());
    let expected_kept = expected_exception.clone();
    if args.is_empty() {
        let ctx = RaisesContext { expected: expected_exception.unbind(), match_expr, info: None };
        return Ok(Py::new(py, ctx)?.into_bound(py).into_any());
    }
    // Callable form: pytest.raises(Exc, func, *args, **kwargs)
    let func = args.get_item(0)?;
    if !func.is_callable() {
        return Err(PyTypeError::new_err(format!(
            "{:?} object (type: {}) must be callable",
            func.repr()?.to_string(),
            func.get_type().name()?
        )));
    }
    let rest = PyTuple::new(py, args.iter().skip(1))?;
    let call_kwargs = PyDict::new(py);
    if let Some(k) = kwargs {
        for (key, v) in k.iter() {
            if key.extract::<String>().map(|s| s == "match").unwrap_or(false) {
                continue;
            }
            call_kwargs.set_item(key, v)?;
        }
    }
    match func.call(rest, Some(&call_kwargs)) {
        Ok(_) => {
            let expected_repr = format_expected(py, &expected_kept)?;
            Err(fail_error(py, &format!("DID NOT RAISE {expected_repr}"), true))
        }
        Err(e) => {
            let val = e.value(py);
            if !val.is_instance(&expected_kept)? {
                return Err(e);
            }
            let info = ExceptionInfo::from_err(py, &e);
            if let Some(m) = &match_expr {
                let s = val.str()?.to_string();
                let re = py.import("re")?;
                if re.call_method1("search", (m.bind(py), &s))?.is_none() {
                    let pat = m.bind(py).str()?.to_string();
                    return Err(PyAssertionError::new_err(format!(
                        "Regex pattern did not match.\n Regex: {pat:?}\n Input: {s:?}"
                    )));
                }
            }
            Ok(Py::new(py, info)?.into_bound(py).into_any())
        }
    }
}

fn validate_expected(expected: &Bound<'_, PyAny>) -> PyResult<()> {
    let check_one = |o: &Bound<'_, PyAny>| -> PyResult<()> {
        let is_class = o.is_instance_of::<PyType>();
        if !is_class {
            return Err(PyTypeError::new_err(format!(
                "expected exception must be a BaseException type, not {}",
                o.get_type().name()?
            )));
        }
        Ok(())
    };
    if let Ok(t) = expected.cast::<PyTuple>() {
        if t.is_empty() {
            return Err(PyValueError::new_err("expected exception must not be empty"));
        }
        for item in t.iter() {
            check_one(&item)?;
        }
        return Ok(());
    }
    check_one(expected)
}

/// Context manager returned by `pytest.warns` / `pytest.deprecated_call`.
#[pyclass(module = "pytest", name = "WarningsChecker")]
pub struct WarningsChecker {
    expected: Option<Py<PyAny>>,
    match_expr: Option<Py<PyAny>>,
    /// The `warnings.catch_warnings` object we entered.
    catcher: Option<Py<PyAny>>,
    #[pyo3(get)]
    list: Py<PyList>,
}

#[pymethods]
impl WarningsChecker {
    fn __enter__<'py>(slf: Bound<'py, Self>, py: Python<'py>) -> PyResult<Bound<'py, Self>> {
        let warnings = py.import("warnings")?;
        let kwargs = PyDict::new(py);
        kwargs.set_item("record", true)?;
        let catcher = warnings.call_method("catch_warnings", (), Some(&kwargs))?;
        let recorded = catcher.call_method0("__enter__")?;
        warnings.call_method1("simplefilter", ("always",))?;
        {
            let mut me = slf.borrow_mut();
            me.catcher = Some(catcher.unbind());
            me.list = recorded.cast_into::<PyList>()?.unbind();
        }
        Ok(slf)
    }

    #[pyo3(signature = (exc_type, exc_val, tb))]
    fn __exit__(
        &mut self,
        py: Python<'_>,
        exc_type: Option<Bound<'_, PyAny>>,
        exc_val: Option<Bound<'_, PyAny>>,
        tb: Option<Bound<'_, PyAny>>,
    ) -> PyResult<bool> {
        if let Some(c) = self.catcher.take() {
            c.bind(py).call_method1(
                "__exit__",
                (
                    exc_type.clone().unwrap_or_else(|| py.None().into_bound(py)),
                    exc_val.unwrap_or_else(|| py.None().into_bound(py)),
                    tb.unwrap_or_else(|| py.None().into_bound(py)),
                ),
            )?;
        }
        // Propagate any in-flight exception; only validate on clean exit.
        if exc_type.map(|t| !t.is_none()).unwrap_or(false) {
            return Ok(false);
        }
        let Some(expected) = &self.expected else { return Ok(false) };
        let items = self.list.bind(py);
        let mut matched = false;
        let mut seen = Vec::new();
        for w in items.iter() {
            let cat = w.getattr("category")?;
            let msg = w.getattr("message")?;
            seen.push(format!(
                "{}(\"{}\")",
                cat.getattr("__name__")?.extract::<String>()?,
                msg.str()?.to_string()
            ));
            if !is_subclass_of(&cat, expected.bind(py))? {
                continue;
            }
            if let Some(m) = &self.match_expr {
                let s = msg.str()?.to_string();
                let re = py.import("re")?;
                if re.call_method1("search", (m.bind(py), &s))?.is_none() {
                    continue;
                }
            }
            matched = true;
            break;
        }
        if !matched {
            let name = expected
                .bind(py)
                .getattr("__name__")
                .and_then(|n| n.extract::<String>())
                .unwrap_or_else(|_| expected.bind(py).str().map(|s| s.to_string()).unwrap_or_default());
            let extra = match &self.match_expr {
                Some(m) => format!(" matching {}", m.bind(py).str()?.to_string()),
                None => String::new(),
            };
            return Err(Failed::new_err(format!(
                "DID NOT WARN. No warnings of type {name}{extra} were emitted.\n Emitted warnings: [{}].",
                seen.join(", ")
            )));
        }
        Ok(false)
    }

    fn pop(&self, py: Python<'_>, cls: Option<Bound<'_, PyAny>>) -> PyResult<Py<PyAny>> {
        let items = self.list.bind(py);
        let target = cls;
        for (i, w) in items.iter().enumerate() {
            let ok = match &target {
                Some(c) => is_subclass_of(&w.getattr("category")?, c)?,
                None => true,
            };
            if ok {
                let obj = items.get_item(i)?;
                items.del_item(i)?;
                return Ok(obj.unbind());
            }
        }
        Err(PyAssertionError::new_err("popping from an empty list of warnings"))
    }

    fn clear(&self, py: Python<'_>) -> PyResult<()> {
        self.list.bind(py).call_method0("clear")?;
        Ok(())
    }

    fn __len__(&self, py: Python<'_>) -> usize {
        self.list.bind(py).len()
    }

    fn __getitem__(&self, py: Python<'_>, i: isize) -> PyResult<Py<PyAny>> {
        Ok(self.list.bind(py).get_item(normalize_index(i, self.list.bind(py).len()))?.unbind())
    }

    fn __iter__(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(self.list.bind(py).try_iter()?.into_any().unbind())
    }
}

fn normalize_index(i: isize, len: usize) -> usize {
    if i < 0 {
        (len as isize + i).max(0) as usize
    } else {
        i as usize
    }
}

#[pyfunction]
#[pyo3(signature = (expected_warning=None, *args, **kwargs))]
pub fn warns<'py>(
    py: Python<'py>,
    expected_warning: Option<Bound<'py, PyAny>>,
    args: &Bound<'py, PyTuple>,
    kwargs: Option<&Bound<'py, PyDict>>,
) -> PyResult<Bound<'py, PyAny>> {
    let match_expr = kwargs.and_then(|k| k.get_item("match").ok().flatten()).map(|v| v.unbind());
    let expected = match expected_warning {
        Some(e) if !e.is_none() => Some(e.unbind()),
        _ => Some(py.get_type::<pyo3::exceptions::PyWarning>().into_any().unbind()),
    };
    let checker = WarningsChecker {
        expected,
        match_expr,
        catcher: None,
        list: PyList::empty(py).unbind(),
    };
    if args.is_empty() {
        return Ok(Py::new(py, checker)?.into_bound(py).into_any());
    }
    // Callable form.
    let bound = Py::new(py, checker)?.into_bound(py);
    let func = args.get_item(0)?;
    let rest = PyTuple::new(py, args.iter().skip(1))?;
    let call_kwargs = PyDict::new(py);
    if let Some(k) = kwargs {
        for (key, v) in k.iter() {
            if key.extract::<String>().map(|s| s == "match").unwrap_or(false) {
                continue;
            }
            call_kwargs.set_item(key, v)?;
        }
    }
    WarningsChecker::__enter__(bound.clone(), py)?;
    let result = func.call(rest, Some(&call_kwargs));
    let none = py.None().into_bound(py);
    match result {
        Ok(v) => {
            bound.borrow_mut().__exit__(py, Some(none.clone()), Some(none.clone()), Some(none))?;
            Ok(v)
        }
        Err(e) => {
            let ty = e.get_type(py).into_any();
            let val = e.value(py).clone().into_any();
            bound.borrow_mut().__exit__(py, Some(ty), Some(val), Some(none))?;
            Err(e)
        }
    }
}

#[pyfunction]
#[pyo3(signature = (*args, **kwargs))]
pub fn deprecated_call<'py>(
    py: Python<'py>,
    args: &Bound<'py, PyTuple>,
    kwargs: Option<&Bound<'py, PyDict>>,
) -> PyResult<Bound<'py, PyAny>> {
    let builtins = py.import("builtins")?;
    let dep = builtins.getattr("DeprecationWarning")?;
    let pending = builtins.getattr("PendingDeprecationWarning")?;
    let both = PyTuple::new(py, [dep, pending])?;
    warns(py, Some(both.into_any()), args, kwargs)
}

/// A small `pytest.approx` implementation covering scalars and sequences.
#[pyclass(module = "pytest", name = "ApproxBase")]
pub struct Approx {
    expected: Py<PyAny>,
    rel: Option<f64>,
    abs: Option<f64>,
    nan_ok: bool,
}

const DEFAULT_REL: f64 = 1e-6;
const DEFAULT_ABS: f64 = 1e-12;

impl Approx {
    fn scalar_eq(&self, actual: f64, expected: f64) -> bool {
        if actual == expected {
            return true;
        }
        if actual.is_nan() || expected.is_nan() {
            return self.nan_ok;
        }
        if actual.is_infinite() || expected.is_infinite() {
            return false;
        }
        let tol = match (self.rel, self.abs) {
            (Some(r), Some(a)) => (r * expected.abs()).max(a),
            (Some(r), None) => (r * expected.abs()).max(DEFAULT_ABS),
            (None, Some(a)) => a,
            (None, None) => (DEFAULT_REL * expected.abs()).max(DEFAULT_ABS),
        };
        (actual - expected).abs() <= tol
    }
}

#[pymethods]
impl Approx {
    fn __eq__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<bool> {
        let exp = self.expected.bind(py);
        if let (Ok(a), Ok(b)) = (other.extract::<f64>(), exp.extract::<f64>()) {
            return Ok(self.scalar_eq(a, b));
        }
        // Sequence / mapping comparison.
        if let (Ok(a), Ok(b)) = (other.try_iter(), exp.try_iter()) {
            let av: Vec<Bound<'_, PyAny>> = a.collect::<PyResult<_>>()?;
            let bv: Vec<Bound<'_, PyAny>> = b.collect::<PyResult<_>>()?;
            if av.len() != bv.len() {
                return Ok(false);
            }
            for (x, y) in av.iter().zip(bv.iter()) {
                let (Ok(xf), Ok(yf)) = (x.extract::<f64>(), y.extract::<f64>()) else {
                    if !x.eq(y)? {
                        return Ok(false);
                    }
                    continue;
                };
                if !self.scalar_eq(xf, yf) {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        other.eq(exp)
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!("approx({})", self.expected.bind(py).repr()?))
    }
}

#[pyfunction]
#[pyo3(signature = (expected, rel=None, abs=None, nan_ok=false))]
pub fn approx(expected: Py<PyAny>, rel: Option<f64>, abs: Option<f64>, nan_ok: bool) -> Approx {
    Approx { expected, rel, abs, nan_ok }
}
