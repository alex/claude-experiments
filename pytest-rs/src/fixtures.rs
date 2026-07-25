//! Fixture definitions, the visibility-scoped registry, and closure
//! computation.
//!
//! The registry is built once during collection.  Each item's fixture closure
//! (the transitive set of fixtures it needs, in setup order) is computed once
//! at collection time rather than being rediscovered on every test, which is
//! where a large slice of pytest's per-test overhead lives.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyString, PyTuple};
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

use crate::marks::MarkData;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Scope {
    Function = 0,
    Class = 1,
    Module = 2,
    Package = 3,
    Session = 4,
}

impl Scope {
    pub fn parse(s: &str) -> Option<Scope> {
        Some(match s {
            "function" => Scope::Function,
            "class" => Scope::Class,
            "module" => Scope::Module,
            "package" => Scope::Package,
            "session" => Scope::Session,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            Scope::Function => "function",
            Scope::Class => "class",
            Scope::Module => "module",
            Scope::Package => "package",
            Scope::Session => "session",
        }
    }
}

/// Fixtures that the engine provides itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Builtin {
    Request,
    PytestConfig,
    MonkeyPatch,
    TmpPath,
    TmpPathFactory,
    CapSys,
    CapFd,
    RecWarn,
    Benchmark,
    Doctest,
    RecordProperty,
    Cache,
    /// xunit-style `setup_module`/`teardown_module` (and the `setUpModule`
    /// spelling), injected only into modules that define one.
    XunitModule,
    /// `setup_class`/`teardown_class`.
    XunitClass,
    /// `setUpClass`/`tearDownClass` on a `unittest.TestCase`.
    UnittestClass,
    /// `setup_function`/`teardown_function`, for module level tests only.
    XunitFunction,
    /// `setup_method`/`teardown_method` on a test class.
    XunitMethod,
}

/// Interpreter and configuration facts that decide whether a built-in fixture
/// forces its test onto the serialised path.
#[derive(Clone, Copy, Debug)]
pub struct HostilityContext {
    /// `warnings.catch_warnings()` is scoped per context (CPython 3.14+).
    pub context_aware_warnings: bool,
    /// Benchmarks are actually timed rather than run once.
    pub benchmarks_enabled: bool,
}

impl Builtin {
    /// Built-in fixtures that mutate process-global state and therefore force
    /// the owning test onto the serialised execution path.
    pub fn thread_hostile(self, ctx: HostilityContext) -> bool {
        match self {
            // `recwarn` is only hazardous while warning filters are global.
            Builtin::RecWarn => !ctx.context_aware_warnings,
            // A disabled benchmark just calls the function once; there is
            // nothing to protect from the noise of other workers.
            Builtin::Benchmark => ctx.benchmarks_enabled,
            Builtin::MonkeyPatch | Builtin::CapSys | Builtin::CapFd => true,
            _ => false,
        }
    }

    pub fn scope(self) -> Scope {
        match self {
            Builtin::PytestConfig | Builtin::TmpPathFactory | Builtin::Cache => Scope::Session,
            _ => Scope::Function,
        }
    }
}

/// One `@pytest.fixture` definition.
pub struct FixtureDef {
    /// Stable identity used for cache keys.
    pub uid: u32,
    pub argname: String,
    pub func: Option<Py<PyAny>>,
    pub scope: Scope,
    /// Parametrised fixture values, if any.
    pub params: Option<Vec<Py<PyAny>>>,
    pub param_ids: Option<Py<PyAny>>,
    pub autouse: bool,
    pub is_generator: bool,
    /// Argument names the fixture function itself requests.
    pub argnames: Vec<String>,
    /// Node-id prefix this fixture is visible under ("" = everywhere).
    pub baseid: String,
    pub builtin: Option<Builtin>,
    /// Set for fixtures defined inside a test class whose first parameter is
    /// `self`; those must be bound to the test instance before being called.
    pub wants_self: bool,
    /// `True` when the fixture body was flagged as not thread safe.
    pub thread_hostile: bool,
    /// Human readable definition site, used in error messages.
    pub location: String,
}

impl FixtureDef {
    pub fn visible_to(&self, nodeid: &str) -> bool {
        baseid_matches(&self.baseid, nodeid)
    }
}

pub fn baseid_matches(baseid: &str, nodeid: &str) -> bool {
    if baseid.is_empty() {
        return true;
    }
    if !nodeid.starts_with(baseid) {
        return false;
    }
    match nodeid.as_bytes().get(baseid.len()) {
        None => true,
        Some(b'/') => true,
        Some(b':') => nodeid[baseid.len()..].starts_with("::"),
        _ => false,
    }
}

#[derive(Default)]
pub struct FixtureRegistry {
    /// name -> definitions, ordered least to most specific.
    pub defs: FxHashMap<String, Vec<Arc<FixtureDef>>>,
    /// All autouse fixtures, in registration order.
    pub autouse: Vec<Arc<FixtureDef>>,
    next_uid: u32,
}

impl FixtureRegistry {
    pub fn new() -> Self {
        FixtureRegistry::default()
    }

    pub fn alloc_uid(&mut self) -> u32 {
        self.next_uid += 1;
        self.next_uid
    }

    pub fn insert(&mut self, def: Arc<FixtureDef>) {
        if def.autouse {
            self.autouse.push(def.clone());
        }
        self.defs.entry(def.argname.clone()).or_default().push(def);
    }

    /// Most specific visible definition for `name` at `nodeid`.
    pub fn resolve(&self, name: &str, nodeid: &str) -> Option<Arc<FixtureDef>> {
        let candidates = self.defs.get(name)?;
        candidates.iter().rev().find(|d| d.visible_to(nodeid)).cloned()
    }

    /// All visible definitions for `name`, most specific last (used to support
    /// a fixture overriding another of the same name).
    pub fn resolve_chain(&self, name: &str, nodeid: &str) -> Vec<Arc<FixtureDef>> {
        match self.defs.get(name) {
            Some(c) => c.iter().filter(|d| d.visible_to(nodeid)).cloned().collect(),
            None => Vec::new(),
        }
    }

    pub fn autouse_for(&self, nodeid: &str) -> Vec<Arc<FixtureDef>> {
        let mut v: Vec<Arc<FixtureDef>> = self
            .autouse
            .iter()
            .filter(|d| d.visible_to(nodeid))
            .cloned()
            .collect();
        // Higher scopes first so session-level setup runs before per-test setup.
        v.sort_by(|a, b| b.scope.cmp(&a.scope).then(a.uid.cmp(&b.uid)));
        v
    }
}

/// The result of resolving what a test item needs.
#[derive(Default, Clone)]
pub struct FixtureClosure {
    /// Every fixture needed, in setup order (dependencies first).
    pub order: Vec<Arc<FixtureDef>>,
    /// Names the test function itself takes as arguments.
    pub direct: Vec<String>,
    /// Names in the closure, for `request.fixturenames`.
    pub names: Vec<String>,
}

/// Compute the transitive fixture closure for a node.
pub fn build_closure(
    reg: &FixtureRegistry,
    nodeid: &str,
    direct: &[String],
    usefixtures: &[String],
) -> FixtureClosure {
    let mut order: Vec<Arc<FixtureDef>> = Vec::new();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    let mut in_progress: FxHashSet<String> = FxHashSet::default();

    fn visit(
        reg: &FixtureRegistry,
        nodeid: &str,
        name: &str,
        seen: &mut FxHashSet<String>,
        in_progress: &mut FxHashSet<String>,
        order: &mut Vec<Arc<FixtureDef>>,
    ) {
        if seen.contains(name) || in_progress.contains(name) {
            return;
        }
        let Some(def) = reg.resolve(name, nodeid) else {
            // Unknown name: the runner reports this as an error at setup time.
            seen.insert(name.to_string());
            return;
        };
        in_progress.insert(name.to_string());
        for dep in &def.argnames {
            if dep == name {
                // Overriding a same-named fixture from a wider scope: the
                // override will ask for the one below it at run time, so pull
                // the whole chain of shadowed definitions into the closure,
                // widest first.
                let chain = reg.resolve_chain(name, nodeid);
                let Some(idx) = chain.iter().position(|d| d.uid == def.uid) else { continue };
                for ancestor in chain[..idx].iter() {
                    for adep in &ancestor.argnames {
                        if adep != name {
                            visit(reg, nodeid, adep, seen, in_progress, order);
                        }
                    }
                    order.push(ancestor.clone());
                }
                continue;
            }
            visit(reg, nodeid, dep, seen, in_progress, order);
        }
        in_progress.remove(name);
        seen.insert(name.to_string());
        order.push(def);
    }

    for def in reg.autouse_for(nodeid) {
        visit(reg, nodeid, &def.argname, &mut seen, &mut in_progress, &mut order);
    }
    for name in usefixtures {
        visit(reg, nodeid, name, &mut seen, &mut in_progress, &mut order);
    }
    for name in direct {
        visit(reg, nodeid, name, &mut seen, &mut in_progress, &mut order);
    }

    // An override and the definition it shadows share a name, so dedupe for
    // `request.fixturenames`.
    let mut names: Vec<String> = Vec::with_capacity(order.len());
    for d in &order {
        if !names.contains(&d.argname) {
            names.push(d.argname.clone());
        }
    }
    FixtureClosure { order, direct: direct.to_vec(), names }
}

/// Marker object produced by `@pytest.fixture(...)`; attached to the function
/// so that collection can pick it up.
#[pyclass(module = "pytest", name = "FixtureFunctionMarker", frozen, from_py_object)]
#[derive(Clone)]
pub struct FixtureFunctionMarker {
    #[pyo3(get)]
    pub scope: Py<PyAny>,
    #[pyo3(get)]
    pub params: Option<Py<PyAny>>,
    #[pyo3(get)]
    pub autouse: bool,
    #[pyo3(get)]
    pub ids: Option<Py<PyAny>>,
    #[pyo3(get)]
    pub name: Option<String>,
}

#[pymethods]
impl FixtureFunctionMarker {
    fn __call__<'py>(&self, py: Python<'py>, function: Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        function.setattr("_pytestfixturefunction", Py::new(py, self.clone())?)?;
        Ok(function)
    }
}

/// `pytest.fixture(...)` — usable bare or with arguments.
#[pyfunction]
#[pyo3(signature = (fixture_function=None, *, scope=None, params=None, autouse=false, ids=None, name=None))]
pub fn fixture<'py>(
    py: Python<'py>,
    fixture_function: Option<Bound<'py, PyAny>>,
    scope: Option<Bound<'py, PyAny>>,
    params: Option<Bound<'py, PyAny>>,
    autouse: bool,
    ids: Option<Bound<'py, PyAny>>,
    name: Option<String>,
) -> PyResult<Bound<'py, PyAny>> {
    let scope_obj = match scope {
        Some(s) => s.unbind(),
        None => PyString::new(py, "function").into_any().unbind(),
    };
    let marker = FixtureFunctionMarker {
        scope: scope_obj,
        params: params.map(|p| p.unbind()),
        autouse,
        ids: ids.map(|i| i.unbind()),
        name,
    };
    match fixture_function {
        Some(f) => marker.__call__(py, f),
        None => Ok(Py::new(py, marker)?.into_bound(py).into_any()),
    }
}

/// `pytest.yield_fixture` — legacy alias.
#[pyfunction]
#[pyo3(signature = (fixture_function=None, *, scope=None, params=None, autouse=false, ids=None, name=None))]
pub fn yield_fixture<'py>(
    py: Python<'py>,
    fixture_function: Option<Bound<'py, PyAny>>,
    scope: Option<Bound<'py, PyAny>>,
    params: Option<Bound<'py, PyAny>>,
    autouse: bool,
    ids: Option<Bound<'py, PyAny>>,
    name: Option<String>,
) -> PyResult<Bound<'py, PyAny>> {
    fixture(py, fixture_function, scope, params, autouse, ids, name)
}

/// `@pytest.mark.usefixtures(...)` names collected off an object.
pub fn usefixtures_from_marks(py: Python<'_>, marks: &[MarkData]) -> Vec<String> {
    let mut out = Vec::new();
    for m in marks {
        if m.name != "usefixtures" {
            continue;
        }
        for a in m.args.bind(py).iter() {
            if let Ok(s) = a.extract::<String>() {
                out.push(s);
            }
        }
    }
    out
}

/// Introspect a callable's positional parameter names, skipping `self`.
pub fn signature_argnames(py: Python<'_>, func: &Bound<'_, PyAny>, skip_self: bool) -> PyResult<Vec<String>> {
    // `__code__` is dramatically cheaper than `inspect.signature`; fall back to
    // inspect only for wrapped/builtin callables.
    let target = unwrap_partial_and_wrappers(py, func)?;
    if let Ok(code) = target.getattr("__code__") {
        let argcount: usize = code.getattr("co_argcount")?.extract()?;
        let kwonly: usize = code.getattr("co_kwonlyargcount").and_then(|v| v.extract()).unwrap_or(0);
        let varnames = code.getattr("co_varnames")?;
        let tuple = varnames.cast::<PyTuple>()?;
        let mut out = Vec::with_capacity(argcount);
        for i in 0..(argcount + kwonly) {
            let n: String = tuple.get_item(i)?.extract()?;
            if skip_self && i == 0 && (n == "self" || n == "cls") {
                continue;
            }
            out.push(n);
        }
        // Drop parameters that have defaults supplied by functools.partial etc.
        return Ok(out);
    }
    let inspect = py.import("inspect")?;
    let sig = inspect.call_method1("signature", (target,))?;
    let params = sig.getattr("parameters")?;
    let mut out = Vec::new();
    for k in params.call_method0("keys")?.try_iter()? {
        let n: String = k?.extract()?;
        if skip_self && (n == "self" || n == "cls") && out.is_empty() {
            continue;
        }
        out.push(n);
    }
    Ok(out)
}

fn unwrap_partial_and_wrappers<'py>(py: Python<'py>, func: &Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
    let mut cur = func.clone();
    for _ in 0..16 {
        if let Ok(w) = cur.getattr("__wrapped__") {
            cur = w;
            continue;
        }
        if let Ok(f) = cur.getattr("func") {
            if cur.get_type().name().map(|n| n == "partial").unwrap_or(false) {
                cur = f;
                continue;
            }
        }
        break;
    }
    let _ = py;
    Ok(cur)
}

/// Detect generator/async-generator fixture functions.
pub fn is_generator(py: Python<'_>, func: &Bound<'_, PyAny>) -> PyResult<bool> {
    let inspect = py.import("inspect")?;
    let target = unwrap_partial_and_wrappers(py, func)?;
    Ok(inspect
        .call_method1("isgeneratorfunction", (&target,))?
        .is_truthy()?)
}

/// Build a `FixtureDef` from a decorated function found during collection.
#[allow(clippy::too_many_arguments)]
pub fn make_fixturedef(
    py: Python<'_>,
    reg: &mut FixtureRegistry,
    attr_name: &str,
    func: &Bound<'_, PyAny>,
    marker: &FixtureFunctionMarker,
    baseid: &str,
    location: String,
    in_class: bool,
) -> PyResult<Arc<FixtureDef>> {
    let argname = marker.name.clone().unwrap_or_else(|| attr_name.to_string());
    let scope_str: String = {
        let s = marker.scope.bind(py);
        if s.is_callable() && !s.is_instance_of::<PyString>() {
            // Dynamic scope callables: resolve with (fixture_name, config).
            "function".to_string()
        } else {
            s.extract::<String>().unwrap_or_else(|_| "function".to_string())
        }
    };
    let scope = Scope::parse(&scope_str).unwrap_or(Scope::Function);
    let params = match &marker.params {
        None => None,
        Some(p) => {
            let bound = p.bind(py);
            if bound.is_none() {
                None
            } else {
                let mut v = Vec::new();
                for item in bound.try_iter()? {
                    v.push(item?.unbind());
                }
                Some(v)
            }
        }
    };
    // `request` stays in the list: the runtime resolves it to a per-requester
    // object rather than a cached fixture value.
    let raw_argnames = signature_argnames(py, func, false)?;
    let wants_self = in_class && raw_argnames.first().map(|a| a == "self").unwrap_or(false);
    let argnames = if wants_self { raw_argnames[1..].to_vec() } else { raw_argnames };
    let is_gen = is_generator(py, func)?;
    let uid = reg.alloc_uid();
    let thread_hostile = crate::threadsafety::thread_hostile_reason(py, func).unwrap_or(None).is_some();
    Ok(Arc::new(FixtureDef {
        uid,
        argname,
        func: Some(func.clone().unbind()),
        scope,
        params,
        param_ids: marker.ids.as_ref().map(|i| i.clone_ref(py)),
        autouse: marker.autouse,
        is_generator: is_gen,
        argnames,
        baseid: baseid.to_string(),
        builtin: None,
        wants_self,
        thread_hostile,
        location,
    }))
}

/// Register the fixtures the engine implements natively.
pub fn register_builtins(reg: &mut FixtureRegistry, ctx: HostilityContext) {
    let entries: &[(&str, Builtin)] = &[
        ("request", Builtin::Request),
        ("pytestconfig", Builtin::PytestConfig),
        ("monkeypatch", Builtin::MonkeyPatch),
        ("tmp_path", Builtin::TmpPath),
        ("tmp_path_factory", Builtin::TmpPathFactory),
        ("capsys", Builtin::CapSys),
        ("capfd", Builtin::CapFd),
        ("recwarn", Builtin::RecWarn),
        ("benchmark", Builtin::Benchmark),
        ("record_property", Builtin::RecordProperty),
        ("cache", Builtin::Cache),
    ];
    for (name, b) in entries {
        let uid = reg.alloc_uid();
        reg.insert(Arc::new(FixtureDef {
            uid,
            argname: name.to_string(),
            func: None,
            scope: b.scope(),
            params: None,
            param_ids: None,
            autouse: false,
            is_generator: false,
            argnames: Vec::new(),
            baseid: String::new(),
            builtin: Some(*b),
            wants_self: false,
            thread_hostile: b.thread_hostile(ctx),
            location: "<pytest-rs builtin>".to_string(),
        }));
    }
}

/// Register a synthesised autouse fixture standing in for one of the
/// xunit-style `setup_*`/`teardown_*` functions.
///
/// pytest injects an equivalent generator fixture while collecting the module
/// or class, which is what gives those functions their ordering: higher scopes
/// run first, teardown runs in reverse, and a failing setup skips its own
/// teardown.  Reusing the fixture machinery here gets all of that for free —
/// and, more importantly, makes the scheduler aware that every test under a
/// `setup_module` shares state, so they stay on one thread.
///
/// The fixture is only registered when the module or class actually defines
/// one of the functions; otherwise every module would gain a module-scoped
/// fixture and the whole suite would collapse into one serial group.
pub fn insert_xunit(
    reg: &mut FixtureRegistry,
    argname: String,
    scope: Scope,
    baseid: &str,
    builtin: Builtin,
    location: String,
) {
    let uid = reg.alloc_uid();
    reg.insert(Arc::new(FixtureDef {
        uid,
        argname,
        func: None,
        scope,
        params: None,
        param_ids: None,
        autouse: true,
        is_generator: false,
        argnames: Vec::new(),
        baseid: baseid.to_string(),
        builtin: Some(builtin),
        wants_self: false,
        thread_hostile: false,
        location,
    }));
}

/// Scan a module/class namespace for fixture definitions.
pub fn scan_namespace(
    py: Python<'_>,
    reg: &mut FixtureRegistry,
    holder: &Bound<'_, PyAny>,
    baseid: &str,
    display: &str,
    in_class: bool,
) -> PyResult<Vec<Arc<FixtureDef>>> {
    let mut found = Vec::new();
    let dict = match holder.getattr("__dict__") {
        Ok(d) => d,
        Err(_) => return Ok(found),
    };
    let names: Vec<String> = if let Ok(d) = dict.cast::<PyDict>() {
        d.keys().iter().filter_map(|k| k.extract::<String>().ok()).collect()
    } else {
        // mappingproxy for classes
        let keys = dict.call_method0("keys")?;
        let list = PyList::new(py, keys.try_iter()?.collect::<PyResult<Vec<_>>>()?)?;
        list.iter().filter_map(|k| k.extract::<String>().ok()).collect()
    };
    for name in names {
        if name.starts_with("__") {
            continue;
        }
        let Ok(obj) = holder.getattr(name.as_str()) else { continue };
        let Ok(marker_attr) = obj.getattr("_pytestfixturefunction") else { continue };
        let Ok(marker) = marker_attr.extract::<FixtureFunctionMarker>() else { continue };
        let location = format!("{display}::{name}");
        let def = make_fixturedef(py, reg, &name, &obj, &marker, baseid, location, in_class)?;
        reg.insert(def.clone());
        found.push(def);
    }
    Ok(found)
}
