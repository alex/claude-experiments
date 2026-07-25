//! Built-in fixtures implemented natively: `monkeypatch`, `tmp_path`,
//! `capsys`, `capfd`, `recwarn`, `pytestconfig`, `record_property`, `cache`
//! and the `benchmark` fixture (pytest-benchmark's behaviour, built in).

use pyo3::exceptions::{PyAttributeError, PyKeyError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};
use std::sync::{Arc, Mutex};

use crate::fixtures::{Builtin, FixtureDef};
use crate::runtime::{Finalizer, Worker};
use crate::session::{Config, Item};

pub fn make_builtin(
    py: Python<'_>,
    worker: &Worker,
    item: &Arc<Item>,
    def: &Arc<FixtureDef>,
    which: Builtin,
) -> PyResult<Py<PyAny>> {
    match which {
        Builtin::Request => worker.get_fixture(py, item, "request", Some(def)),
        Builtin::PytestConfig => Ok(Py::new(py, Config { data: worker.session.cfg.clone() })?.into_any()),
        Builtin::MonkeyPatch => {
            let mp = Py::new(py, MonkeyPatch::default())?;
            let undo = mp.bind(py).getattr("undo")?;
            worker.add_finalizer_public(crate::fixtures::Scope::Function, Finalizer::Callback(undo.unbind()));
            Ok(mp.into_any())
        }
        Builtin::TmpPath => {
            let base = tmp_root(py, worker)?;
            // Derive the directory from the whole node id, not just the test
            // name: two tests called `test_foo` in different modules would
            // otherwise share a directory, and racing to create it under the
            // thread pool is exactly the kind of bug that shows up once a
            // month.
            let dir = base.call_method1("joinpath", (unique_dir_name(&item.nodeid).as_str(),))?;
            let kwargs = PyDict::new(py);
            kwargs.set_item("parents", true)?;
            kwargs.set_item("exist_ok", true)?;
            dir.call_method("mkdir", (), Some(&kwargs))?;
            Ok(dir.unbind())
        }
        Builtin::TmpPathFactory => {
            let base = tmp_root(py, worker)?;
            Ok(Py::new(py, TmpPathFactory { base: base.unbind() })?.into_any())
        }
        Builtin::CapSys | Builtin::CapFd => {
            // Capturing is already active for this worker thread; the fixture
            // is just a handle onto that thread's buffers.
            crate::capture::start(py)?;
            Ok(Py::new(py, Capture { binary: false })?.into_any())
        }
        Builtin::RecWarn => {
            let warnings = py.import("warnings")?;
            let kwargs = PyDict::new(py);
            kwargs.set_item("record", true)?;
            let catcher = warnings.call_method("catch_warnings", (), Some(&kwargs))?;
            let recorded = catcher.call_method0("__enter__")?;
            warnings.call_method1("simplefilter", ("always",))?;
            let rec = Py::new(
                py,
                RecordedWarnings { list: recorded.cast_into::<PyList>()?.unbind(), catcher: catcher.unbind() },
            )?;
            let close = rec.bind(py).getattr("_close")?;
            worker.add_finalizer_public(crate::fixtures::Scope::Function, Finalizer::Callback(close.unbind()));
            Ok(rec.into_any())
        }
        Builtin::Benchmark => crate::bench::make_fixture(py, worker, item),
        Builtin::RecordProperty => {
            let f = Py::new(py, RecordProperty { entries: Mutex::new(Vec::new()) })?;
            Ok(f.into_any())
        }
        Builtin::Cache => Ok(Py::new(py, CacheFixture { data: Mutex::new(Default::default()) })?.into_any()),
        Builtin::Doctest => Ok(py.None()),
    }
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_alphanumeric() || c == '_' || c == '-' { c } else { '_' })
        .collect::<String>()
        .chars()
        .take(60)
        .collect()
}

/// A readable, collision-free directory name for a node id.
fn unique_dir_name(nodeid: &str) -> String {
    // FNV-1a over the full id keeps the suffix stable across runs while the
    // readable prefix stays useful when poking at the directory by hand.
    let mut hash: u64 = 0xcbf29ce484222325;
    for b in nodeid.as_bytes() {
        hash ^= *b as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    let tail = nodeid.rsplit("::").next().unwrap_or(nodeid);
    format!("{}-{hash:08x}", sanitize(tail))
}

fn tmp_root<'py>(py: Python<'py>, worker: &Worker) -> PyResult<Bound<'py, PyAny>> {
    let cfg = &worker.session.cfg;
    let basetemp = cfg.str_opt("basetemp");
    let pathlib = py.import("pathlib")?;
    if !basetemp.is_empty() {
        let p = pathlib.getattr("Path")?.call1((basetemp.as_str(),))?;
        let kwargs = PyDict::new(py);
        kwargs.set_item("parents", true)?;
        kwargs.set_item("exist_ok", true)?;
        p.call_method("mkdir", (), Some(&kwargs))?;
        return Ok(p);
    }
    let tempfile = py.import("tempfile")?;
    let root = tempfile.getattr("gettempdir")?.call0()?;
    let uid = py.import("os")?.call_method0("getpid")?;
    let p = pathlib
        .getattr("Path")?
        .call1((root,))?
        .call_method1("joinpath", (format!("pytest-rs-{}", uid.str()?),))?;
    let kwargs = PyDict::new(py);
    kwargs.set_item("parents", true)?;
    kwargs.set_item("exist_ok", true)?;
    p.call_method("mkdir", (), Some(&kwargs))?;
    Ok(p)
}

/// `tmp_path_factory`
#[pyclass(module = "pytest", name = "TempPathFactory")]
pub struct TmpPathFactory {
    base: Py<PyAny>,
}

#[pymethods]
impl TmpPathFactory {
    #[pyo3(signature = (basename, numbered=true))]
    fn mktemp(&self, py: Python<'_>, basename: &str, numbered: bool) -> PyResult<Py<PyAny>> {
        let base = self.base.bind(py);
        let mut name = sanitize(basename);
        if numbered {
            for i in 0.. {
                let cand = format!("{name}{i}");
                let p = base.call_method1("joinpath", (cand.as_str(),))?;
                if !p.call_method0("exists")?.is_truthy()? {
                    name = cand;
                    break;
                }
            }
        }
        let p = base.call_method1("joinpath", (name.as_str(),))?;
        let kwargs = PyDict::new(py);
        kwargs.set_item("parents", true)?;
        kwargs.set_item("exist_ok", true)?;
        p.call_method("mkdir", (), Some(&kwargs))?;
        Ok(p.unbind())
    }

    fn getbasetemp(&self, py: Python<'_>) -> Py<PyAny> {
        self.base.clone_ref(py)
    }
}

/// `monkeypatch`
#[pyclass(module = "pytest", name = "MonkeyPatch")]
#[derive(Default)]
pub struct MonkeyPatch {
    setattrs: Mutex<Vec<(Py<PyAny>, String, Option<Py<PyAny>>)>>,
    setitems: Mutex<Vec<(Py<PyAny>, Py<PyAny>, Option<Py<PyAny>>)>>,
    syspath: Mutex<Vec<String>>,
    cwd: Mutex<Option<String>>,
}

#[pymethods]
impl MonkeyPatch {
    #[new]
    fn new() -> Self {
        MonkeyPatch::default()
    }

    #[pyo3(signature = (target, name=None, value=None, raising=true))]
    fn setattr(
        &self,
        py: Python<'_>,
        target: Bound<'_, PyAny>,
        name: Option<Bound<'_, PyAny>>,
        value: Option<Bound<'_, PyAny>>,
        raising: bool,
    ) -> PyResult<()> {
        // String form: monkeypatch.setattr("module.attr", value)
        let (obj, attr, val) = match (&name, &value) {
            (Some(n), Some(v)) if n.extract::<String>().is_ok() => {
                (target.clone(), n.extract::<String>()?, v.clone())
            }
            (Some(v), None) => {
                let dotted: String = target.extract()?;
                let (m, a) = resolve_dotted(py, &dotted)?;
                (m, a, v.clone())
            }
            _ => {
                return Err(pyo3::exceptions::PyTypeError::new_err(
                    "setattr() requires (target, name, value) or (dotted_name, value)",
                ))
            }
        };
        let old = obj.getattr(attr.as_str()).ok();
        if old.is_none() && raising {
            return Err(PyAttributeError::new_err(format!("{} has no attribute {attr:?}", obj.repr()?)));
        }
        self.setattrs
            .lock()
            .unwrap()
            .push((obj.clone().unbind(), attr.clone(), old.map(|o| o.unbind())));
        obj.setattr(attr.as_str(), val)?;
        Ok(())
    }

    #[pyo3(signature = (target, name=None, raising=true))]
    fn delattr(&self, py: Python<'_>, target: Bound<'_, PyAny>, name: Option<String>, raising: bool) -> PyResult<()> {
        let (obj, attr) = match name {
            Some(n) => (target.clone(), n),
            None => {
                let dotted: String = target.extract()?;
                resolve_dotted(py, &dotted)?
            }
        };
        let old = obj.getattr(attr.as_str()).ok();
        if old.is_none() {
            if raising {
                return Err(PyAttributeError::new_err(attr));
            }
            return Ok(());
        }
        self.setattrs
            .lock()
            .unwrap()
            .push((obj.clone().unbind(), attr.clone(), old.map(|o| o.unbind())));
        obj.delattr(attr.as_str())?;
        Ok(())
    }

    fn setitem(&self, dic: Bound<'_, PyAny>, name: Bound<'_, PyAny>, value: Bound<'_, PyAny>) -> PyResult<()> {
        let old = dic.get_item(&name).ok();
        self.setitems
            .lock()
            .unwrap()
            .push((dic.clone().unbind(), name.clone().unbind(), old.map(|o| o.unbind())));
        dic.set_item(name, value)?;
        Ok(())
    }

    #[pyo3(signature = (dic, name, raising=true))]
    fn delitem(&self, dic: Bound<'_, PyAny>, name: Bound<'_, PyAny>, raising: bool) -> PyResult<()> {
        let old = dic.get_item(&name).ok();
        if old.is_none() {
            if raising {
                return Err(PyKeyError::new_err(name.str()?.to_string()));
            }
            return Ok(());
        }
        self.setitems
            .lock()
            .unwrap()
            .push((dic.clone().unbind(), name.clone().unbind(), old.map(|o| o.unbind())));
        dic.del_item(name)?;
        Ok(())
    }

    #[pyo3(signature = (name, value, prepend=None))]
    fn setenv(&self, py: Python<'_>, name: &str, value: Bound<'_, PyAny>, prepend: Option<String>) -> PyResult<()> {
        let os = py.import("os")?;
        let environ = os.getattr("environ")?;
        let mut v = value.str()?.to_string();
        if let Some(sep) = prepend {
            if let Ok(existing) = environ.get_item(name) {
                v = format!("{v}{sep}{}", existing.str()?);
            }
        }
        self.setitem(environ, pyo3::types::PyString::new(py, name).into_any(), pyo3::types::PyString::new(py, &v).into_any())
    }

    #[pyo3(signature = (name, raising=true))]
    fn delenv(&self, py: Python<'_>, name: &str, raising: bool) -> PyResult<()> {
        let os = py.import("os")?;
        let environ = os.getattr("environ")?;
        self.delitem(environ, pyo3::types::PyString::new(py, name).into_any(), raising)
    }

    fn syspath_prepend(&self, py: Python<'_>, path: Bound<'_, PyAny>) -> PyResult<()> {
        let s = path.str()?.to_string();
        let sys = py.import("sys")?;
        sys.getattr("path")?.call_method1("insert", (0, s.as_str()))?;
        self.syspath.lock().unwrap().push(s);
        Ok(())
    }

    fn chdir(&self, py: Python<'_>, path: Bound<'_, PyAny>) -> PyResult<()> {
        let os = py.import("os")?;
        let cur = os.call_method0("getcwd")?.extract::<String>()?;
        if self.cwd.lock().unwrap().is_none() {
            *self.cwd.lock().unwrap() = Some(cur);
        }
        os.call_method1("chdir", (path,))?;
        Ok(())
    }

    fn undo(&self, py: Python<'_>) -> PyResult<()> {
        // Take everything first: restoring an attribute runs Python, and no
        // lock of ours should be held while that happens.
        let attrs: Vec<_> = self.setattrs.lock().unwrap().drain(..).collect();
        let items: Vec<_> = self.setitems.lock().unwrap().drain(..).collect();
        let paths: Vec<_> = self.syspath.lock().unwrap().drain(..).collect();
        for (obj, name, old) in attrs.into_iter().rev() {
            let b = obj.bind(py);
            match old {
                Some(v) => b.setattr(name.as_str(), v.bind(py))?,
                None => {
                    let _ = b.delattr(name.as_str());
                }
            }
        }
        for (dic, key, old) in items.into_iter().rev() {
            let d = dic.bind(py);
            match old {
                Some(v) => d.set_item(key.bind(py), v.bind(py))?,
                None => {
                    let _ = d.del_item(key.bind(py));
                }
            }
        }
        let sys = py.import("sys")?;
        let path = sys.getattr("path")?;
        for p in paths {
            let _ = path.call_method1("remove", (p.as_str(),));
        }
        if let Some(cwd) = self.cwd.lock().unwrap().take() {
            py.import("os")?.call_method1("chdir", (cwd.as_str(),))?;
        }
        Ok(())
    }

    fn context(slf: Py<Self>, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(py, MonkeyPatchContext { mp: slf })?.into_any())
    }
}

#[pyclass(module = "pytest", name = "MonkeyPatchContext")]
pub struct MonkeyPatchContext {
    mp: Py<MonkeyPatch>,
}

#[pymethods]
impl MonkeyPatchContext {
    fn __enter__(&self, py: Python<'_>) -> Py<MonkeyPatch> {
        self.mp.clone_ref(py)
    }

    #[pyo3(signature = (*_args))]
    fn __exit__(&self, py: Python<'_>, _args: &Bound<'_, PyTuple>) -> PyResult<bool> {
        self.mp.bind(py).borrow().undo(py)?;
        Ok(false)
    }
}

fn resolve_dotted<'py>(py: Python<'py>, dotted: &str) -> PyResult<(Bound<'py, PyAny>, String)> {
    let (modname, attr) = dotted
        .rsplit_once('.')
        .ok_or_else(|| pyo3::exceptions::PyValueError::new_err(format!("{dotted:?} must be a dotted import path")))?;
    // Walk down from the longest importable prefix.
    let mut parts: Vec<&str> = modname.split('.').collect();
    let mut trailing: Vec<&str> = Vec::new();
    loop {
        let candidate = parts.join(".");
        match py.import(candidate.as_str()) {
            Ok(m) => {
                let mut obj = m.into_any();
                for t in trailing.iter().rev() {
                    obj = obj.getattr(*t)?;
                }
                return Ok((obj, attr.to_string()));
            }
            Err(_) => {
                if parts.len() <= 1 {
                    return Err(pyo3::exceptions::PyImportError::new_err(format!(
                        "could not import {modname:?}"
                    )));
                }
                trailing.push(parts.pop().unwrap());
            }
        }
    }
}

/// `capsys` / `capfd` — a handle onto the calling thread's capture buffers.
#[pyclass(module = "pytest", name = "CaptureFixture")]
pub struct Capture {
    binary: bool,
}

#[pymethods]
impl Capture {
    fn readouterr(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let (out, err) = crate::capture::read(py)?;
        let collections = py.import("collections")?;
        let nt = collections.getattr("namedtuple")?.call1(("CaptureResult", vec!["out", "err"]))?;
        if self.binary {
            return Ok(nt.call1((out.into_bytes(), err.into_bytes()))?.unbind());
        }
        Ok(nt.call1((out, err))?.unbind())
    }

    fn disabled(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(py, CaptureDisabled { saved: Mutex::new(None) })?.into_any())
    }
}

/// `with capsys.disabled():` — lets a block write straight to the terminal.
#[pyclass(module = "pytest", name = "CaptureDisabled")]
pub struct CaptureDisabled {
    saved: Mutex<Option<(Py<PyAny>, Py<PyAny>)>>,
}

#[pymethods]
impl CaptureDisabled {
    fn __enter__(&self, py: Python<'_>) -> PyResult<()> {
        *self.saved.lock().unwrap() = crate::capture::suspend(py);
        Ok(())
    }

    #[pyo3(signature = (*_args))]
    fn __exit__(&self, _args: &Bound<'_, PyTuple>) -> PyResult<bool> {
        if let Some(saved) = self.saved.lock().unwrap().take() {
            crate::capture::resume(saved);
        }
        Ok(false)
    }
}

/// `recwarn`
#[pyclass(module = "pytest", name = "WarningsRecorder")]
pub struct RecordedWarnings {
    #[pyo3(get)]
    list: Py<PyList>,
    catcher: Py<PyAny>,
}

#[pymethods]
impl RecordedWarnings {
    fn __len__(&self, py: Python<'_>) -> usize {
        self.list.bind(py).len()
    }

    fn __getitem__(&self, py: Python<'_>, i: usize) -> PyResult<Py<PyAny>> {
        Ok(self.list.bind(py).get_item(i)?.unbind())
    }

    fn __iter__(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(self.list.bind(py).try_iter()?.into_any().unbind())
    }

    #[pyo3(signature = (cls=None))]
    fn pop(&self, py: Python<'_>, cls: Option<Bound<'_, PyAny>>) -> PyResult<Py<PyAny>> {
        let items = self.list.bind(py);
        for (i, w) in items.iter().enumerate() {
            let ok = match &cls {
                Some(c) => crate::raises::is_subclass_of(&w.getattr("category")?, &c)?,
                None => true,
            };
            if ok {
                let obj = items.get_item(i)?;
                items.del_item(i)?;
                return Ok(obj.unbind());
            }
        }
        Err(pyo3::exceptions::PyAssertionError::new_err("popping from an empty list of warnings"))
    }

    fn clear(&self, py: Python<'_>) -> PyResult<()> {
        self.list.bind(py).call_method0("clear")?;
        Ok(())
    }

    fn _close(&self, py: Python<'_>) -> PyResult<()> {
        let none = py.None();
        self.catcher
            .bind(py)
            .call_method1("__exit__", (none.clone_ref(py), none.clone_ref(py), none))?;
        Ok(())
    }
}

/// `record_property`
#[pyclass(module = "pytest", name = "RecordProperty")]
pub struct RecordProperty {
    entries: Mutex<Vec<(String, Py<PyAny>)>>,
}

#[pymethods]
impl RecordProperty {
    fn __call__(&self, key: String, value: Bound<'_, PyAny>) {
        self.entries.lock().unwrap().push((key, value.unbind()));
    }
}

/// `cache` — a minimal in-memory stand-in for pytest's cache plugin.
#[pyclass(module = "pytest", name = "Cache")]
pub struct CacheFixture {
    data: Mutex<rustc_hash::FxHashMap<String, Py<PyAny>>>,
}

#[pymethods]
impl CacheFixture {
    fn get(&self, py: Python<'_>, key: &str, default: Bound<'_, PyAny>) -> Py<PyAny> {
        self.data
            .lock()
            .unwrap()
            .get(key)
            .map(|v| v.clone_ref(py))
            .unwrap_or_else(|| default.unbind())
    }

    fn set(&self, key: &str, value: Bound<'_, PyAny>) {
        self.data.lock().unwrap().insert(key.to_string(), value.unbind());
    }

    fn mkdir(&self, py: Python<'_>, name: &str) -> PyResult<Py<PyAny>> {
        let tempfile = py.import("tempfile")?;
        let pathlib = py.import("pathlib")?;
        let root = tempfile.getattr("gettempdir")?.call0()?;
        let p = pathlib.getattr("Path")?.call1((root,))?.call_method1("joinpath", (name,))?;
        let kwargs = PyDict::new(py);
        kwargs.set_item("parents", true)?;
        kwargs.set_item("exist_ok", true)?;
        p.call_method("mkdir", (), Some(&kwargs))?;
        Ok(p.unbind())
    }
}
