//! Session-wide data structures: configuration, collected items, and the
//! Python-visible `Config`/`Parser`/`Item` objects that conftest hooks receive.

use pyo3::exceptions::{PyAttributeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyString, PyTuple};
use rustc_hash::{FxHashMap, FxHashSet};
use std::path::PathBuf;
use std::sync::{Arc, Mutex, RwLock};

use crate::config::{IniType, OptKind, OptType, OptionSpec, Parser as CliParser, Value};
use crate::fixtures::{FixtureClosure, FixtureRegistry, Scope};
use crate::marks::{KnownMarkers, MarkData};
use crate::outcomes::UsageErrorPy;

/// Immutable-after-configure session configuration.
pub struct ConfigData {
    pub rootdir: PathBuf,
    pub invocation_dir: PathBuf,
    pub inifile: Option<PathBuf>,
    /// Full argv as pytest would report it (after addopts splicing).
    pub args: RwLock<Vec<String>>,
    pub opts: RwLock<std::collections::BTreeMap<String, Value>>,
    pub opt2dest: RwLock<std::collections::BTreeMap<String, String>>,
    pub ini: RwLock<std::collections::BTreeMap<String, Value>>,
    pub known_markers: Arc<RwLock<KnownMarkers>>,
    pub stash: Mutex<Option<Py<PyDict>>>,
}

impl ConfigData {
    pub fn get(&self, dest: &str) -> Value {
        self.opts.read().unwrap().get(dest).cloned().unwrap_or(Value::None)
    }

    pub fn set(&self, dest: &str, v: Value) {
        self.opts.write().unwrap().insert(dest.to_string(), v);
    }

    pub fn flag(&self, dest: &str) -> bool {
        self.get(dest).as_bool()
    }

    pub fn str_opt(&self, dest: &str) -> String {
        match self.get(dest) {
            Value::Str(s) => s,
            Value::None => String::new(),
            other => format!("{other:?}"),
        }
    }

    pub fn ini_value(&self, name: &str) -> Value {
        self.ini.read().unwrap().get(name).cloned().unwrap_or(Value::None)
    }

    pub fn ini_list(&self, name: &str) -> Vec<String> {
        self.ini_value(name).str_list()
    }

    pub fn ini_str(&self, name: &str) -> String {
        match self.ini_value(name) {
            Value::Str(s) => s,
            Value::List(l) if !l.is_empty() => l[0].as_str().unwrap_or_default().to_string(),
            _ => String::new(),
        }
    }

    /// Verbosity level, combining `-v` and `-q`.
    pub fn verbosity(&self) -> i64 {
        self.get("verbose").as_int().unwrap_or(0) - self.get("quiet").as_int().unwrap_or(0)
    }
}

/// The parameters bound to one collected test.
#[derive(Default)]
pub struct CallSpec {
    /// argname -> value, in parametrisation order.
    pub params: Vec<(String, Py<PyAny>)>,
    /// Names delivered through a fixture's `request.param` instead of directly.
    pub indirect: FxHashSet<String>,
    /// argname -> index within its parameter list (used for fixture cache keys).
    pub indices: FxHashMap<String, usize>,
    /// The `[...]` suffix of the test id.
    pub id_parts: Vec<String>,
    /// Marks contributed by `pytest.param(marks=...)`.
    pub marks: Vec<MarkData>,
}

impl CallSpec {
    pub fn lookup(&self, name: &str) -> Option<&Py<PyAny>> {
        self.params.iter().find(|(n, _)| n == name).map(|(_, v)| v)
    }

    pub fn id(&self) -> String {
        self.id_parts.join("-")
    }
}

/// A collected test.
pub struct Item {
    pub index: usize,
    pub nodeid: String,
    /// `test_foo[a-b]`
    pub name: String,
    /// `test_foo`
    pub originalname: String,
    pub path: PathBuf,
    /// rootdir-relative, always `/`-separated.
    pub relpath: String,
    pub module: Py<PyAny>,
    pub module_name: String,
    pub cls: Option<Py<PyAny>>,
    pub cls_name: Option<String>,
    pub func: Py<PyAny>,
    /// Markers closest-first (own, then class, then module).
    pub marks: Vec<MarkData>,
    /// Extra marks added at runtime through `item.add_marker`.
    pub extra_marks: Mutex<Vec<MarkData>>,
    pub closure: FixtureClosure,
    pub callspec: CallSpec,
    pub line: usize,
    /// Set when the item may not overlap with other tests.
    pub thread_hostile: bool,
    /// Why the item was serialised, for `-vv` reporting.
    pub hostile_reason: Option<String>,
    /// Whether the test function takes `self`.
    pub in_class: bool,
    /// Keywords used by `-k` matching.
    pub keywords: Vec<String>,
    /// Specs contributed by `@pytest.mark.filterwarnings`, resolved once.
    pub filter_specs: Vec<String>,
}

impl Item {
    pub fn all_marks(&self, extra: bool) -> Vec<MarkData> {
        let mut v = self.marks.clone();
        if extra {
            v.extend(self.extra_marks.lock().unwrap().iter().cloned());
        }
        v
    }

    /// Markers for the runner's own evaluation, avoiding a clone (and the
    /// reference-count traffic that comes with it) in the common case where
    /// nothing was added at runtime.
    pub fn marks_for_eval(&self) -> std::borrow::Cow<'_, [MarkData]> {
        if self.extra_marks.lock().unwrap().is_empty() {
            std::borrow::Cow::Borrowed(&self.marks)
        } else {
            std::borrow::Cow::Owned(self.all_marks(true))
        }
    }

    pub fn location(&self) -> String {
        format!("{}:{}", self.relpath, self.line)
    }

    /// The `scope key` identifying which cached instance of a scoped fixture
    /// this item would use.
    pub fn scope_key(&self, scope: Scope) -> String {
        match scope {
            Scope::Session => String::new(),
            Scope::Package => self
                .path
                .parent()
                .map(|p| p.to_string_lossy().to_string())
                .unwrap_or_default(),
            Scope::Module => self.relpath.clone(),
            Scope::Class => match &self.cls_name {
                Some(c) => format!("{}::{}", self.relpath, c),
                None => self.relpath.clone(),
            },
            Scope::Function => self.nodeid.clone(),
        }
    }
}

/// Registered hook callables discovered in conftest modules and plugins.
#[derive(Default)]
pub struct Hooks {
    pub configure: Vec<Py<PyAny>>,
    pub unconfigure: Vec<Py<PyAny>>,
    pub report_header: Vec<Py<PyAny>>,
    pub collection_modifyitems: Vec<Py<PyAny>>,
    pub runtest_setup: Vec<Py<PyAny>>,
    pub runtest_teardown: Vec<Py<PyAny>>,
    pub runtest_call: Vec<Py<PyAny>>,
    pub generate_tests: Vec<Py<PyAny>>,
    pub sessionstart: Vec<Py<PyAny>>,
    pub sessionfinish: Vec<Py<PyAny>>,
    pub make_parametrize_id: Vec<Py<PyAny>>,
    pub itemcollected: Vec<Py<PyAny>>,
    pub terminal_summary: Vec<Py<PyAny>>,
    pub runtest_makereport: Vec<Py<PyAny>>,
    pub collectstart: Vec<Py<PyAny>>,
    pub ignore_collect: Vec<Py<PyAny>>,
    pub addoption: Vec<Py<PyAny>>,
    pub cmdline_main: Vec<Py<PyAny>>,
    pub plugin_registered: Vec<Py<PyAny>>,
}

/// Everything the runner needs, shared across worker threads.
pub struct Session {
    pub cfg: Arc<ConfigData>,
    pub registry: FixtureRegistry,
    pub items: Vec<Arc<Item>>,
    pub hooks: Hooks,
    /// Number of worker threads.
    pub workers: usize,
    /// Errors captured while importing modules during collection.
    pub collect_errors: Vec<(String, String)>,
    pub start_time: std::time::SystemTime,
    /// The seed used for the built-in test-order randomisation.
    pub seed: u64,
    /// Collected benchmark timings.
    pub bench_store: Arc<crate::bench::BenchStore>,
    /// How per-test output is captured.
    pub capture_mode: crate::capture::Mode,
    /// Failure rendering settings, resolved once instead of per test.
    pub tb_style: String,
    pub showlocals: bool,
    pub term_width: usize,
    pub xfail_strict: bool,
}

/// `pytest.Config` — the object handed to `pytest_configure` and friends.
#[pyclass(module = "pytest", name = "Config")]
pub struct Config {
    pub data: Arc<ConfigData>,
}

#[pymethods]
impl Config {
    #[pyo3(signature = (name, default=None, skip=false))]
    fn getoption(
        &self,
        py: Python<'_>,
        name: &str,
        default: Option<Bound<'_, PyAny>>,
        skip: bool,
    ) -> PyResult<Py<PyAny>> {
        let dest = self
            .data
            .opt2dest
            .read()
            .unwrap()
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.trim_start_matches('-').replace('-', "_"));
        let present = self.data.opts.read().unwrap().contains_key(&dest);
        let val = self.data.get(&dest);
        let missing = !present || (skip && matches!(val, Value::None));
        if missing {
            if let Some(d) = default {
                return Ok(d.unbind());
            }
            if skip {
                return Err(crate::outcomes::skip_error(py, &format!("no {} option found", crate::error::py_repr(&dest)), false));
            }
            return Err(PyValueError::new_err(format!("no option named {}", crate::error::py_repr(name))));
        }
        Ok(value_to_py(py, &val)?)
    }

    #[pyo3(signature = (name, default=None, skip=false))]
    fn getvalue(
        &self,
        py: Python<'_>,
        name: &str,
        default: Option<Bound<'_, PyAny>>,
        skip: bool,
    ) -> PyResult<Py<PyAny>> {
        self.getoption(py, name, default, skip)
    }

    fn getvalueorskip(&self, py: Python<'_>, name: &str) -> PyResult<Py<PyAny>> {
        self.getoption(py, name, None, true)
    }

    fn getini(&self, py: Python<'_>, name: &str) -> PyResult<Py<PyAny>> {
        let v = self.data.ini_value(name);
        if matches!(v, Value::None) {
            return Err(PyValueError::new_err(format!("unknown configuration value: {}", crate::error::py_repr(name))));
        }
        value_to_py(py, &v)
    }

    fn addinivalue_line(&self, name: &str, line: &str) -> PyResult<()> {
        let mut ini = self.data.ini.write().unwrap();
        let entry = ini.entry(name.to_string()).or_insert_with(|| Value::List(Vec::new()));
        let mut list = entry.as_list();
        list.push(Value::Str(line.to_string()));
        *entry = Value::List(list);
        if name == "markers" {
            let marker_name = line.split(['(', ':']).next().unwrap_or(line).trim().to_string();
            self.data.known_markers.write().unwrap().names.insert(marker_name);
        }
        Ok(())
    }

    #[getter]
    fn rootdir(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        path_obj(py, &self.data.rootdir)
    }

    #[getter]
    fn rootpath(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        path_obj(py, &self.data.rootdir)
    }

    #[getter]
    fn inipath(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        match &self.data.inifile {
            Some(p) => path_obj(py, p),
            None => Ok(py.None()),
        }
    }

    #[getter]
    fn inifile(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        self.inipath(py)
    }

    #[getter]
    fn args(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let list = PyList::new(py, self.data.args.read().unwrap().iter().map(|s| s.as_str()))?;
        Ok(list.into_any().unbind())
    }

    #[getter]
    fn invocation_params(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let d = PyDict::new(py);
        d.set_item("args", self.args(py)?)?;
        d.set_item("dir", path_obj(py, &self.data.invocation_dir)?)?;
        Ok(namespace(py, &d)?)
    }

    #[getter]
    fn option(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let d = PyDict::new(py);
        for (k, v) in self.data.opts.read().unwrap().iter() {
            d.set_item(k, value_to_py(py, v)?)?;
        }
        namespace(py, &d)
    }

    #[getter]
    fn stash(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let mut guard = self.data.stash.lock().unwrap();
        if guard.is_none() {
            *guard = Some(PyDict::new(py).unbind());
        }
        Ok(guard.as_ref().unwrap().clone_ref(py).into_any())
    }

    #[getter]
    fn pluginmanager(slf: PyRef<'_, Self>, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(py, PluginManager { data: slf.data.clone() })?.into_any())
    }

    fn getvalue_or_none(&self, py: Python<'_>, name: &str) -> PyResult<Py<PyAny>> {
        self.getoption(py, name, Some(py.None().into_bound(py)), false)
    }

    fn __repr__(&self) -> String {
        format!("<Config rootdir={:?}>", self.data.rootdir)
    }
}

/// Minimal plugin manager stand-in: enough for `config.pluginmanager.getplugin`
/// / `hasplugin` probes that plugins commonly perform.
#[pyclass(module = "pytest", name = "PytestPluginManager")]
pub struct PluginManager {
    pub data: Arc<ConfigData>,
}

#[pymethods]
impl PluginManager {
    fn hasplugin(&self, name: &str) -> bool {
        matches!(name, "benchmark" | "cov" | "randomly" | "python" | "fixtures" | "terminal")
            && !self.disabled(name)
    }

    fn getplugin(&self, py: Python<'_>, _name: &str) -> Py<PyAny> {
        py.None()
    }

    fn get_plugin(&self, py: Python<'_>, name: &str) -> Py<PyAny> {
        self.getplugin(py, name)
    }

    fn is_registered(&self, _plugin: &Bound<'_, PyAny>) -> bool {
        false
    }

    #[pyo3(signature = (plugin, name=None))]
    fn register(&self, py: Python<'_>, plugin: Bound<'_, PyAny>, name: Option<String>) -> PyResult<Py<PyAny>> {
        let _ = (plugin, name);
        Ok(py.None())
    }

    fn unregister(&self, py: Python<'_>, _plugin: Bound<'_, PyAny>) -> Py<PyAny> {
        py.None()
    }

    fn import_plugin(&self, _name: &str) -> PyResult<()> {
        Ok(())
    }
}

impl PluginManager {
    fn disabled(&self, name: &str) -> bool {
        self.data
            .get("plugins")
            .str_list()
            .iter()
            .any(|p| p == &format!("no:{name}"))
    }
}

/// `parser` object passed to `pytest_addoption`.
#[pyclass(module = "pytest", name = "Parser")]
pub struct ArgParser {
    pub specs: Arc<Mutex<Vec<OptionSpec>>>,
    pub inis: Arc<Mutex<Vec<(String, IniType, String)>>>,
}

#[pymethods]
impl ArgParser {
    #[pyo3(signature = (*names, **kwargs))]
    fn addoption(&self, py: Python<'_>, names: &Bound<'_, PyTuple>, kwargs: Option<&Bound<'_, PyDict>>) -> PyResult<()> {
        let name_vec: Vec<String> = names
            .iter()
            .filter_map(|n| n.extract::<String>().ok())
            .collect();
        if name_vec.is_empty() {
            return Err(PyValueError::new_err("addoption() requires at least one option string"));
        }
        let refs: Vec<&str> = name_vec.iter().map(|s| s.as_str()).collect();
        let action = kwargs
            .and_then(|k| k.get_item("action").ok().flatten())
            .and_then(|v| v.extract::<String>().ok())
            .unwrap_or_else(|| "store".to_string());
        let kind = match action.as_str() {
            "store_true" => OptKind::StoreTrue,
            "store_false" => OptKind::StoreFalse,
            "append" => OptKind::Append,
            "count" => OptKind::Count,
            _ => OptKind::Store,
        };
        let mut spec = OptionSpec::new(&refs, kind);
        if let Some(k) = kwargs {
            if let Some(d) = k.get_item("dest").ok().flatten() {
                if let Ok(s) = d.extract::<String>() {
                    spec = spec.dest(&s);
                }
            }
            if let Some(t) = k.get_item("type").ok().flatten() {
                let tyname = t
                    .getattr("__name__")
                    .and_then(|n| n.extract::<String>())
                    .unwrap_or_else(|_| t.str().map(|s| s.to_string()).unwrap_or_default());
                spec = spec.ty(match tyname.as_str() {
                    "int" => OptType::Int,
                    "float" => OptType::Float,
                    "bool" => OptType::Bool,
                    _ => OptType::Str,
                });
            }
            if let Some(d) = k.get_item("default").ok().flatten() {
                spec = spec.default(py_to_value(py, &d)?);
            }
            if let Some(h) = k.get_item("help").ok().flatten() {
                if let Ok(s) = h.extract::<String>() {
                    spec = spec.help(&s);
                }
            }
        }
        self.specs.lock().unwrap().push(spec);
        Ok(())
    }

    #[pyo3(signature = (name, help=None, r#type=None, default=None))]
    fn addini(
        &self,
        py: Python<'_>,
        name: &str,
        help: Option<String>,
        r#type: Option<String>,
        default: Option<Bound<'_, PyAny>>,
    ) -> PyResult<()> {
        let _ = help;
        let ty = match r#type.as_deref() {
            Some("args") => IniType::Args,
            Some("linelist") => IniType::LineList,
            Some("pathlist") => IniType::Paths,
            Some("bool") => IniType::Bool,
            Some("int") => IniType::Int,
            _ => IniType::Str,
        };
        let default_str = match default {
            Some(d) if !d.is_none() => d.str()?.to_string(),
            _ => String::new(),
        };
        let _ = py;
        self.inis.lock().unwrap().push((name.to_string(), ty, default_str));
        Ok(())
    }

    /// Option groups behave like the parser itself for our purposes.
    #[pyo3(signature = (name, description=None, after=None))]
    fn getgroup(slf: PyRef<'_, Self>, py: Python<'_>, name: &str, description: Option<String>, after: Option<String>) -> PyResult<Py<PyAny>> {
        let _ = (name, description, after);
        Ok(Py::new(
            py,
            ArgParser { specs: slf.specs.clone(), inis: slf.inis.clone() },
        )?
        .into_any())
    }

    #[pyo3(signature = (*names, **kwargs))]
    fn addargument(&self, py: Python<'_>, names: &Bound<'_, PyTuple>, kwargs: Option<&Bound<'_, PyDict>>) -> PyResult<()> {
        self.addoption(py, names, kwargs)
    }

    #[getter]
    fn extra_info(&self, py: Python<'_>) -> Py<PyDict> {
        PyDict::new(py).unbind()
    }
}

/// The Python view of a collected test item, also used as `request.node`.
#[pyclass(module = "pytest", name = "Function")]
pub struct PyItem {
    pub item: Arc<Item>,
    pub cfg: Arc<ConfigData>,
}

#[pymethods]
impl PyItem {
    #[getter]
    fn name(&self) -> &str {
        &self.item.name
    }

    #[getter]
    fn nodeid(&self) -> &str {
        &self.item.nodeid
    }

    #[getter]
    fn originalname(&self) -> &str {
        &self.item.originalname
    }

    #[getter]
    fn function(&self, py: Python<'_>) -> Py<PyAny> {
        self.item.func.clone_ref(py)
    }

    #[getter]
    fn obj(&self, py: Python<'_>) -> Py<PyAny> {
        self.item.func.clone_ref(py)
    }

    #[getter]
    fn cls(&self, py: Python<'_>) -> Py<PyAny> {
        match &self.item.cls {
            Some(c) => c.clone_ref(py),
            None => py.None(),
        }
    }

    #[getter]
    fn instance(&self, py: Python<'_>) -> Py<PyAny> {
        py.None()
    }

    #[getter]
    fn module(&self, py: Python<'_>) -> Py<PyAny> {
        self.item.module.clone_ref(py)
    }

    #[getter]
    fn path(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        path_obj(py, &self.item.path)
    }

    #[getter]
    fn fspath(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        path_obj(py, &self.item.path)
    }

    #[getter]
    fn config(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(py, Config { data: self.cfg.clone() })?.into_any())
    }

    #[getter]
    fn session(slf: PyRef<'_, Self>, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(py, PyItem { item: slf.item.clone(), cfg: slf.cfg.clone() })?.into_any())
    }

    #[getter]
    fn parent(&self, py: Python<'_>) -> Py<PyAny> {
        py.None()
    }

    #[getter]
    fn own_markers(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let list = PyList::empty(py);
        for m in self.item.all_marks(true) {
            list.append(m.to_py(py)?)?;
        }
        Ok(list.into_any().unbind())
    }

    #[getter]
    fn keywords(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let d = PyDict::new(py);
        for k in &self.item.keywords {
            d.set_item(k, true)?;
        }
        for m in self.item.all_marks(true) {
            d.set_item(&m.name, true)?;
        }
        Ok(d.into_any().unbind())
    }

    #[getter]
    fn callspec(slf: PyRef<'_, Self>, py: Python<'_>) -> PyResult<Py<PyAny>> {
        if slf.item.callspec.params.is_empty() {
            return Ok(py.None());
        }
        let d = PyDict::new(py);
        let params = PyDict::new(py);
        for (k, v) in &slf.item.callspec.params {
            params.set_item(k, v.bind(py))?;
        }
        d.set_item("params", params)?;
        d.set_item("id", slf.item.callspec.id())?;
        namespace(py, &d)
    }

    #[getter]
    fn location(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let t = PyTuple::new(
            py,
            [
                PyString::new(py, &self.item.relpath).into_any(),
                self.item.line.into_pyobject(py)?.into_any(),
                PyString::new(py, &self.item.name).into_any(),
            ],
        )?;
        Ok(t.into_any().unbind())
    }

    #[getter]
    fn user_properties(&self, py: Python<'_>) -> Py<PyAny> {
        PyList::empty(py).into_any().unbind()
    }

    #[getter]
    fn stash(&self, py: Python<'_>) -> Py<PyAny> {
        PyDict::new(py).into_any().unbind()
    }

    #[getter]
    fn fixturenames(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(PyList::new(py, self.item.closure.names.iter().map(|s| s.as_str()))?.into_any().unbind())
    }

    #[pyo3(signature = (name=None))]
    fn iter_markers(&self, py: Python<'_>, name: Option<&str>) -> PyResult<Py<PyAny>> {
        let list = PyList::empty(py);
        for m in self.item.all_marks(true) {
            if name.map(|n| n == m.name).unwrap_or(true) {
                list.append(m.to_py(py)?)?;
            }
        }
        Ok(list.try_iter()?.into_any().unbind())
    }

    #[pyo3(signature = (name=None))]
    fn iter_markers_with_node(&self, py: Python<'_>, name: Option<&str>) -> PyResult<Py<PyAny>> {
        let list = PyList::empty(py);
        for m in self.item.all_marks(true) {
            if name.map(|n| n == m.name).unwrap_or(true) {
                list.append(PyTuple::new(py, [py.None(), m.to_py(py)?])?)?;
            }
        }
        Ok(list.try_iter()?.into_any().unbind())
    }

    #[pyo3(signature = (name, default=None))]
    fn get_closest_marker(&self, py: Python<'_>, name: &str, default: Option<Bound<'_, PyAny>>) -> PyResult<Py<PyAny>> {
        for m in self.item.all_marks(true) {
            if m.name == name {
                return m.to_py(py);
            }
        }
        Ok(default.map(|d| d.unbind()).unwrap_or_else(|| py.None()))
    }

    fn add_marker(&self, py: Python<'_>, marker: Bound<'_, PyAny>, append: Option<bool>) -> PyResult<()> {
        let m = if let Ok(s) = marker.extract::<String>() {
            MarkData::new(py, &s)
        } else {
            crate::marks::mark_from_py(py, &marker)?
        };
        let mut guard = self.item.extra_marks.lock().unwrap();
        if append.unwrap_or(true) {
            guard.push(m);
        } else {
            guard.insert(0, m);
        }
        Ok(())
    }

    fn addfinalizer(&self, _f: Bound<'_, PyAny>) {}

    fn __repr__(&self) -> String {
        format!("<Function {}>", self.item.name)
    }

    fn __str__(&self) -> String {
        self.item.nodeid.clone()
    }

    fn __getattr__(&self, name: &str) -> PyResult<Py<PyAny>> {
        Err(PyAttributeError::new_err(format!("'Function' object has no attribute {name:?}")))
    }
}

/// Convert an engine `Value` into the Python object argparse would produce.
pub fn value_to_py(py: Python<'_>, v: &Value) -> PyResult<Py<PyAny>> {
    Ok(match v {
        Value::None => py.None(),
        Value::Bool(b) => b.into_pyobject(py)?.to_owned().into_any().unbind(),
        Value::Int(i) => i.into_pyobject(py)?.into_any().unbind(),
        Value::Float(f) => f.into_pyobject(py)?.into_any().unbind(),
        Value::Str(s) => PyString::new(py, s).into_any().unbind(),
        Value::List(l) => {
            let out = PyList::empty(py);
            for item in l {
                out.append(value_to_py(py, item)?)?;
            }
            out.into_any().unbind()
        }
    })
}

pub fn py_to_value(py: Python<'_>, obj: &Bound<'_, PyAny>) -> PyResult<Value> {
    if obj.is_none() {
        return Ok(Value::None);
    }
    if obj.is_instance_of::<pyo3::types::PyBool>() {
        return Ok(Value::Bool(obj.is_truthy()?));
    }
    if let Ok(i) = obj.extract::<i64>() {
        return Ok(Value::Int(i));
    }
    if let Ok(f) = obj.extract::<f64>() {
        return Ok(Value::Float(f));
    }
    if let Ok(s) = obj.extract::<String>() {
        return Ok(Value::Str(s));
    }
    if let Ok(list) = obj.cast::<PyList>() {
        let mut out = Vec::new();
        for item in list.iter() {
            out.push(py_to_value(py, &item)?);
        }
        return Ok(Value::List(out));
    }
    Ok(Value::Str(obj.str()?.to_string()))
}

pub fn path_obj(py: Python<'_>, p: &std::path::Path) -> PyResult<Py<PyAny>> {
    let pathlib = py.import("pathlib")?;
    Ok(pathlib.getattr("Path")?.call1((p.to_string_lossy().as_ref(),))?.unbind())
}

fn namespace(py: Python<'_>, d: &Bound<'_, PyDict>) -> PyResult<Py<PyAny>> {
    let types = py.import("types")?;
    Ok(types.getattr("SimpleNamespace")?.call((), Some(d))?.unbind())
}

/// Apply the option specs collected from `pytest_addoption` to a parser.
pub fn extend_parser(parser: &mut CliParser, specs: &[OptionSpec]) {
    for s in specs {
        parser.add(s.clone());
    }
}

/// Raise pytest's `UsageError`.
pub fn usage_error(msg: impl Into<String>) -> PyErr {
    UsageErrorPy::new_err(msg.into())
}
