//! Fixture execution: scope frames, caching, finalisation, and the `request`
//! object handed to fixtures and tests.
//!
//! Threading model
//! ---------------
//! Each worker thread owns a `Worker` holding a stack of scope frames
//! (package → module → class → function).  Function/class/module/package scoped
//! fixture instances therefore never cross a thread boundary: the scheduler
//! places every test that would share such an instance into the same serial
//! group.
//!
//! Session scoped fixtures are different — serialising every test that shares
//! one would collapse the whole run onto a single thread.  Instead they live in
//! a process-wide cache and are created exactly once under a per-instance lock,
//! which preserves pytest's "runs once per session" contract.  A session
//! fixture whose body is flagged as thread hostile by the static analysis falls
//! back to the grouping behaviour.

use pyo3::exceptions::{PyKeyError, PyRuntimeError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyString, PyTuple};
use rustc_hash::FxHashMap;
use std::sync::{Arc, Mutex};

use crate::fixtures::{Builtin, FixtureDef, Scope};
use crate::outcomes::{Failed, Skipped};
use crate::session::{Config, ConfigData, Item, PyItem, Session};

/// Something that must run when a scope ends.
pub enum Finalizer {
    /// A generator fixture that still needs its post-yield half executed.
    Generator(Py<PyAny>, String),
    /// An explicit `request.addfinalizer()` callback.
    Callback(Py<PyAny>),
}

pub struct ScopeFrame {
    pub scope: Scope,
    pub key: String,
    pub cache: FxHashMap<(u32, usize), Py<PyAny>>,
    pub finalizers: Vec<Finalizer>,
}

/// Shared, cross-thread cache for session scoped fixtures.
#[derive(Default)]
pub struct SessionCache {
    slots: Mutex<FxHashMap<(u32, usize), Arc<Mutex<Option<Py<PyAny>>>>>>,
    finalizers: Mutex<Vec<Finalizer>>,
}

impl SessionCache {
    fn slot(&self, key: (u32, usize)) -> Arc<Mutex<Option<Py<PyAny>>>> {
        let mut guard = self.slots.lock().unwrap();
        guard.entry(key).or_default().clone()
    }

    pub fn add_finalizer(&self, f: Finalizer) {
        self.finalizers.lock().unwrap().push(f);
    }

    /// Run every session finalizer, newest first.
    pub fn teardown(&self, py: Python<'_>) -> Vec<String> {
        let mut errs = Vec::new();
        let mut fins = std::mem::take(&mut *self.finalizers.lock().unwrap());
        while let Some(f) = fins.pop() {
            if let Err(e) = run_finalizer(py, &f) {
                errs.push(crate::traceback::format_exception_only(py, &e));
            }
        }
        self.slots.lock().unwrap().clear();
        errs
    }
}

fn run_finalizer(py: Python<'_>, f: &Finalizer) -> PyResult<()> {
    match f {
        Finalizer::Generator(gen, name) => {
            let g = gen.bind(py);
            match g.call_method0("__next__") {
                Ok(_) => Err(Failed::new_err(format!("fixture {} yielded more than once", crate::error::py_repr(name)))),
                Err(e) if e.is_instance_of::<pyo3::exceptions::PyStopIteration>(py) => Ok(()),
                Err(e) => Err(e),
            }
        }
        Finalizer::Callback(cb) => {
            cb.bind(py).call0()?;
            Ok(())
        }
    }
}

/// Per-thread fixture execution state.
pub struct Worker {
    pub session: Arc<Session>,
    pub session_cache: Arc<SessionCache>,
    pub frames: Mutex<Vec<ScopeFrame>>,
    /// Errors collected while tearing down.
    pub teardown_errors: Mutex<Vec<String>>,
    /// The instance of the test class the current item belongs to, if any.
    pub instance: Mutex<Option<Py<PyAny>>>,
}

const SCOPE_CHAIN: [Scope; 5] = [Scope::Session, Scope::Package, Scope::Module, Scope::Class, Scope::Function];

impl Worker {
    pub fn new(session: Arc<Session>, session_cache: Arc<SessionCache>) -> Self {
        Worker {
            session,
            session_cache,
            frames: Mutex::new(Vec::new()),
            teardown_errors: Mutex::new(Vec::new()),
            instance: Mutex::new(None),
        }
    }

    /// Bring the frame stack in line with `item`, tearing down anything that no
    /// longer applies.
    pub fn enter_item(&self, py: Python<'_>, item: &Arc<Item>) -> Vec<String> {
        let desired: Vec<(Scope, String)> = SCOPE_CHAIN.iter().map(|s| (*s, item.scope_key(*s))).collect();
        let mut errors = Vec::new();
        let divergence = {
            let frames = self.frames.lock().unwrap();
            let mut i = 0usize;
            while i < frames.len() && i < desired.len() {
                if frames[i].scope != desired[i].0 || frames[i].key != desired[i].1 {
                    break;
                }
                i += 1;
            }
            i
        };
        // Pop frames from the deepest one down to `divergence`.
        loop {
            let frame = {
                let mut frames = self.frames.lock().unwrap();
                if frames.len() <= divergence {
                    None
                } else {
                    frames.pop()
                }
            };
            let Some(mut frame) = frame else { break };
            while let Some(f) = frame.finalizers.pop() {
                if let Err(e) = run_finalizer(py, &f) {
                    errors.push(crate::traceback::format_exception_only(py, &e));
                }
            }
        }
        {
            let mut frames = self.frames.lock().unwrap();
            for (scope, key) in desired.into_iter().skip(frames.len()) {
                frames.push(ScopeFrame { scope, key, cache: FxHashMap::default(), finalizers: Vec::new() });
            }
        }
        errors
    }

    /// Tear down the function scope frame after a test completes.
    pub fn exit_item(&self, py: Python<'_>) -> Vec<String> {
        let mut errors = Vec::new();
        let frame = {
            let mut frames = self.frames.lock().unwrap();
            if frames.last().map(|f| f.scope == Scope::Function).unwrap_or(false) {
                frames.pop()
            } else {
                None
            }
        };
        if let Some(mut frame) = frame {
            while let Some(f) = frame.finalizers.pop() {
                if let Err(e) = run_finalizer(py, &f) {
                    errors.push(crate::traceback::format_exception_only(py, &e));
                }
            }
        }
        errors
    }

    /// Tear down every remaining frame (end of a serial group).
    pub fn drain(&self, py: Python<'_>) -> Vec<String> {
        let mut errors = Vec::new();
        loop {
            let frame = self.frames.lock().unwrap().pop();
            let Some(mut frame) = frame else { break };
            while let Some(f) = frame.finalizers.pop() {
                if let Err(e) = run_finalizer(py, &f) {
                    errors.push(crate::traceback::format_exception_only(py, &e));
                }
            }
        }
        errors
    }

    fn cache_get(&self, scope: Scope, key: (u32, usize), py: Python<'_>) -> Option<Py<PyAny>> {
        let frames = self.frames.lock().unwrap();
        frames
            .iter()
            .find(|f| f.scope == scope)
            .and_then(|f| f.cache.get(&key).map(|v| v.clone_ref(py)))
    }

    fn cache_put(&self, scope: Scope, key: (u32, usize), val: Py<PyAny>) {
        let mut frames = self.frames.lock().unwrap();
        if let Some(f) = frames.iter_mut().find(|f| f.scope == scope) {
            f.cache.insert(key, val);
        }
    }

    fn add_finalizer(&self, scope: Scope, f: Finalizer) {
        let mut frames = self.frames.lock().unwrap();
        if let Some(fr) = frames.iter_mut().find(|fr| fr.scope == scope) {
            fr.finalizers.push(f);
        }
    }

    /// Register a finalizer from outside this module (used by the builtin
    /// fixtures, which own their own cleanup).
    pub fn add_finalizer_public(&self, scope: Scope, f: Finalizer) {
        self.add_finalizer(scope, f);
    }

    /// Resolve one fixture value for `item`.
    pub fn get_fixture(
        &self,
        py: Python<'_>,
        item: &Arc<Item>,
        name: &str,
        requester: Option<&Arc<FixtureDef>>,
    ) -> PyResult<Py<PyAny>> {
        if name == "request" {
            return Ok(Py::new(
                py,
                FixtureRequest {
                    worker: self.clone_handle(),
                    item: item.clone(),
                    def: requester.cloned(),
                },
            )?
            .into_any());
        }
        // A direct (non-indirect) parametrised value shadows any fixture.
        if !item.callspec.indirect.contains(name) {
            if let Some(v) = item.callspec.lookup(name) {
                return Ok(v.clone_ref(py));
            }
        }
        // A fixture that requests its own name is overriding a wider-scoped
        // definition, so it must resolve to the one *below* it in the chain —
        // resolving to itself would recurse forever.
        let def = match requester {
            Some(r) if r.argname == name => {
                let chain = self.session.registry.resolve_chain(name, &item.nodeid);
                let pos = chain.iter().position(|d| d.uid == r.uid);
                match pos.and_then(|i| i.checked_sub(1)).and_then(|i| chain.get(i).cloned()) {
                    Some(d) => d,
                    None => {
                        return Err(Failed::new_err(format!(
                            "fixture {} overrides itself but there is no wider definition to fall back on",
                            crate::error::py_repr(name)
                        )))
                    }
                }
            }
            _ => match self.session.registry.resolve(name, &item.nodeid) {
                Some(d) => d,
                None => {
                    return Err(Failed::new_err(format!(
                        "fixture {} not found\n> available fixtures: {}",
                        crate::error::py_repr(name),
                        available_fixtures(&self.session, &item.nodeid).join(", ")
                    )))
                }
            },
        };
        self.get_fixture_def(py, item, &def)
    }

    fn get_fixture_def(&self, py: Python<'_>, item: &Arc<Item>, def: &Arc<FixtureDef>) -> PyResult<Py<PyAny>> {
        let param_index = item.callspec.indices.get(&def.argname).copied().unwrap_or(0);
        let key = (def.uid, param_index);
        let shared_session = def.scope == Scope::Session && !def.thread_hostile && def.builtin.is_none();

        if shared_session {
            let slot = self.session_cache.slot(key);
            let mut guard = slot.lock().unwrap();
            if let Some(v) = guard.as_ref() {
                return Ok(v.clone_ref(py));
            }
            let val = self.create_fixture(py, item, def, true)?;
            *guard = Some(val.clone_ref(py));
            return Ok(val);
        }

        if let Some(v) = self.cache_get(def.scope, key, py) {
            return Ok(v);
        }
        let val = self.create_fixture(py, item, def, false)?;
        self.cache_put(def.scope, key, val.clone_ref(py));
        Ok(val)
    }

    /// Actually invoke a fixture function.
    fn create_fixture(
        &self,
        py: Python<'_>,
        item: &Arc<Item>,
        def: &Arc<FixtureDef>,
        session_shared: bool,
    ) -> PyResult<Py<PyAny>> {
        if let Some(b) = def.builtin {
            return crate::builtins::make_builtin(py, self, item, def, b);
        }
        let Some(func) = &def.func else {
            return Err(PyRuntimeError::new_err(format!("fixture {} has no implementation", def.argname)));
        };
        let kwargs = PyDict::new(py);
        for argname in &def.argnames {
            let v = self.get_fixture(py, item, argname, Some(def))?;
            kwargs.set_item(argname, v.bind(py))?;
        }
        // Fixtures defined inside a test class are plain functions in the
        // class namespace; bind them to the instance pytest would use.
        let mut bound = func.bind(py).clone();
        if def.wants_self {
            let instance = self.instance.lock().unwrap().as_ref().map(|i| i.clone_ref(py));
            if let Some(inst) = instance {
                bound = bound.call_method1("__get__", (inst.bind(py),))?;
            }
        }
        let result = bound.call((), Some(&kwargs))?;
        if def.is_generator {
            let value = match result.call_method0("__next__") {
                Ok(v) => v,
                Err(e) if e.is_instance_of::<pyo3::exceptions::PyStopIteration>(py) => py.None().into_bound(py),
                Err(e) => return Err(e),
            };
            let fin = Finalizer::Generator(result.unbind(), def.argname.clone());
            if session_shared {
                self.session_cache.add_finalizer(fin);
            } else {
                self.add_finalizer(def.scope, fin);
            }
            return Ok(value.unbind());
        }
        Ok(result.unbind())
    }

    /// Build the keyword arguments for a test function.
    pub fn fill_arguments(&self, py: Python<'_>, item: &Arc<Item>) -> PyResult<Py<PyDict>> {
        let kwargs = PyDict::new(py);
        // Autouse and explicitly requested fixtures first, in closure order.
        for def in &item.closure.order {
            if def.builtin == Some(Builtin::Request) {
                continue;
            }
            if !def.autouse && !item.closure.direct.contains(&def.argname) {
                continue;
            }
            let _ = self.get_fixture_def(py, item, def)?;
        }
        for name in &item.closure.direct {
            let v = self.get_fixture(py, item, name, None)?;
            kwargs.set_item(name, v.bind(py))?;
        }
        Ok(kwargs.unbind())
    }

    /// Run every autouse fixture visible to the item.
    pub fn setup_autouse(&self, py: Python<'_>, item: &Arc<Item>) -> PyResult<()> {
        for def in &item.closure.order {
            if def.autouse {
                self.get_fixture_def(py, item, def)?;
            }
        }
        Ok(())
    }

    fn clone_handle(&self) -> Arc<Worker> {
        WORKER_HANDLE.with(|h| h.borrow().clone().expect("worker handle not installed"))
    }
}

thread_local! {
    static WORKER_HANDLE: std::cell::RefCell<Option<Arc<Worker>>> = const { std::cell::RefCell::new(None) };
}

/// Install the current worker so `FixtureRequest` objects can reference it.
pub fn install_worker(w: Arc<Worker>) {
    WORKER_HANDLE.with(|h| *h.borrow_mut() = Some(w));
}

pub fn clear_worker() {
    WORKER_HANDLE.with(|h| *h.borrow_mut() = None);
}

fn available_fixtures(session: &Session, nodeid: &str) -> Vec<String> {
    let mut names: Vec<String> = session
        .registry
        .defs
        .iter()
        .filter(|(_, defs)| defs.iter().any(|d| d.visible_to(nodeid)))
        .map(|(k, _)| k.clone())
        .collect();
    names.sort();
    names
}

/// `request` — the fixture request object.
#[pyclass(module = "pytest", name = "FixtureRequest")]
pub struct FixtureRequest {
    pub worker: Arc<Worker>,
    pub item: Arc<Item>,
    /// The fixture currently being set up, if any.
    pub def: Option<Arc<FixtureDef>>,
}

#[pymethods]
impl FixtureRequest {
    #[getter]
    fn param(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let Some(def) = &self.def else {
            return Err(pyo3::exceptions::PyAttributeError::new_err("param"));
        };
        match self.item.callspec.lookup(&def.argname) {
            Some(v) => Ok(v.clone_ref(py)),
            None => Err(pyo3::exceptions::PyAttributeError::new_err(format!(
                "The requested fixture has no parameter defined for test: {}",
                self.item.nodeid
            ))),
        }
    }

    #[getter]
    fn fixturename(&self) -> Option<String> {
        self.def.as_ref().map(|d| d.argname.clone())
    }

    #[getter]
    fn scope(&self) -> &'static str {
        self.def.as_ref().map(|d| d.scope.name()).unwrap_or("function")
    }

    #[getter]
    fn node(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(py, PyItem { item: self.item.clone(), cfg: self.worker.session.cfg.clone() })?.into_any())
    }

    #[getter]
    fn config(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(Py::new(py, Config { data: self.worker.session.cfg.clone() })?.into_any())
    }

    #[getter]
    fn function(&self, py: Python<'_>) -> Py<PyAny> {
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
        self.worker
            .instance
            .lock()
            .unwrap()
            .as_ref()
            .map(|i| i.clone_ref(py))
            .unwrap_or_else(|| py.None())
    }

    #[getter]
    fn module(&self, py: Python<'_>) -> Py<PyAny> {
        self.item.module.clone_ref(py)
    }

    #[getter]
    fn path(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        crate::session::path_obj(py, &self.item.path)
    }

    #[getter]
    fn fspath(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        crate::session::path_obj(py, &self.item.path)
    }

    #[getter]
    fn keywords(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let d = PyDict::new(py);
        for k in &self.item.keywords {
            d.set_item(k, true)?;
        }
        Ok(d.into_any().unbind())
    }

    #[getter]
    fn fixturenames(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(PyList::new(py, self.item.closure.names.iter().map(|s| s.as_str()))?.into_any().unbind())
    }

    #[getter]
    fn session(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        self.node(py)
    }

    fn getfixturevalue(&self, py: Python<'_>, argname: &str) -> PyResult<Py<PyAny>> {
        self.worker.get_fixture(py, &self.item, argname, self.def.as_ref())
    }

    fn getfuncargvalue(&self, py: Python<'_>, argname: &str) -> PyResult<Py<PyAny>> {
        self.getfixturevalue(py, argname)
    }

    fn addfinalizer(&self, finalizer: Bound<'_, PyAny>) {
        let scope = self.def.as_ref().map(|d| d.scope).unwrap_or(Scope::Function);
        let fin = Finalizer::Callback(finalizer.unbind());
        if scope == Scope::Session {
            self.worker.session_cache.add_finalizer(fin);
        } else {
            self.worker.add_finalizer(scope, fin);
        }
    }

    fn applymarker(&self, py: Python<'_>, marker: Bound<'_, PyAny>) -> PyResult<()> {
        let m = crate::marks::mark_from_py(py, &marker)?;
        self.item.extra_marks.lock().unwrap().push(m);
        Ok(())
    }

    fn raiseerror(&self, msg: Option<String>) -> PyResult<()> {
        Err(Failed::new_err(msg.unwrap_or_default()))
    }

    fn __repr__(&self) -> String {
        format!("<FixtureRequest for <Function {}>>", self.item.name)
    }
}

/// Raise the fixture-not-found error in the shape pytest uses.
pub fn fixture_lookup_error(name: &str, item: &Item) -> PyErr {
    Failed::new_err(format!("fixture {} not found for {}", crate::error::py_repr(name), item.nodeid))
}

/// Helper used by the builtin fixtures to raise a skip.
pub fn skip_err(py: Python<'_>, reason: &str) -> PyErr {
    let e = Skipped::new_err(reason.to_string());
    let _ = e.value(py).setattr(crate::outcomes::ATTR_MSG, reason);
    e
}

#[allow(dead_code)]
fn _keep_imports(py: Python<'_>) {
    let _ = PyString::new(py, "");
    let _ = PyTuple::empty(py);
    let _: PyErr = PyKeyError::new_err("");
    let _ = ConfigData::verbosity;
}
