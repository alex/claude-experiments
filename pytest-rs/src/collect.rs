//! Test collection: filesystem discovery, conftest loading, module import,
//! and expansion of parametrised tests into concrete items.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyTuple, PyType};
use rustc_hash::{FxHashMap, FxHashSet};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::config::normalize;
use crate::error::{Error, Result};
use crate::fixtures::{
    build_closure, scan_namespace, signature_argnames, usefixtures_from_marks, FixtureDef, FixtureRegistry,
};
use crate::ids;
use crate::marks::{self, MarkData};
use crate::session::{CallSpec, ConfigData, Hooks, Item};

/// Shell-style glob matching (`*`, `?`, `[...]`) for a single path segment.
pub fn fnmatch(pattern: &str, name: &str) -> bool {
    fn inner(p: &[char], n: &[char]) -> bool {
        if p.is_empty() {
            return n.is_empty();
        }
        match p[0] {
            '*' => {
                for i in 0..=n.len() {
                    if inner(&p[1..], &n[i..]) {
                        return true;
                    }
                }
                false
            }
            '?' => !n.is_empty() && inner(&p[1..], &n[1..]),
            '[' => {
                if n.is_empty() {
                    return false;
                }
                let close = p.iter().position(|&c| c == ']');
                let Some(close) = close else {
                    return n[0] == '[' && inner(&p[1..], &n[1..]);
                };
                let mut set: Vec<char> = p[1..close].to_vec();
                let negate = set.first() == Some(&'!');
                if negate {
                    set.remove(0);
                }
                let mut matched = false;
                let mut i = 0;
                while i < set.len() {
                    if i + 2 < set.len() && set[i + 1] == '-' {
                        if n[0] >= set[i] && n[0] <= set[i + 2] {
                            matched = true;
                        }
                        i += 3;
                    } else {
                        if n[0] == set[i] {
                            matched = true;
                        }
                        i += 1;
                    }
                }
                if matched != negate {
                    inner(&p[close + 1..], &n[1..])
                } else {
                    false
                }
            }
            c => !n.is_empty() && n[0] == c && inner(&p[1..], &n[1..]),
        }
    }
    let p: Vec<char> = pattern.chars().collect();
    let n: Vec<char> = name.chars().collect();
    inner(&p, &n)
}

/// A conftest module that has been imported.
pub struct Conftest {
    pub path: PathBuf,
    pub baseid: String,
    pub module: Py<PyAny>,
}

pub struct Collector<'a> {
    pub cfg: Arc<ConfigData>,
    pub registry: FixtureRegistry,
    pub hooks: Hooks,
    pub items: Vec<Arc<Item>>,
    pub errors: Vec<(String, String)>,
    pub conftests: Vec<Conftest>,
    seen_conftests: FxHashSet<PathBuf>,
    python_files: Vec<String>,
    python_classes: Vec<String>,
    python_functions: Vec<String>,
    norecursedirs: Vec<String>,
    ignore: Vec<PathBuf>,
    /// Cache of `dir -> is package`.
    pkg_cache: FxHashMap<PathBuf, bool>,
    /// `unittest.TestCase`, refreshed after each test module import — like
    /// pytest we never import `unittest` ourselves, we only notice when the
    /// suite has.
    unittest_case: Option<Py<PyAny>>,
    marker: std::marker::PhantomData<&'a ()>,
}

/// What a class-shaped module attribute turned out to be.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ClassKind {
    None,
    Plain,
    UnitTest,
}

/// A single node-id selector from the command line.
#[derive(Debug, Clone)]
pub struct Selector {
    pub path: PathBuf,
    /// `::`-separated parts after the file path.
    pub parts: Vec<String>,
}

impl<'a> Collector<'a> {
    pub fn new(cfg: Arc<ConfigData>, hostility: crate::fixtures::HostilityContext) -> Self {
        let mut registry = FixtureRegistry::new();
        crate::fixtures::register_builtins(&mut registry, hostility);
        let python_files = non_empty(cfg.ini_list("python_files"), vec!["test_*.py".into(), "*_test.py".into()]);
        let python_classes = non_empty(cfg.ini_list("python_classes"), vec!["Test".into()]);
        let python_functions = non_empty(cfg.ini_list("python_functions"), vec!["test".into()]);
        let norecursedirs = non_empty(
            cfg.ini_list("norecursedirs"),
            vec![
                "*.egg".into(),
                ".*".into(),
                "_darcs".into(),
                "build".into(),
                "CVS".into(),
                "dist".into(),
                "node_modules".into(),
                "venv".into(),
                "{arch}".into(),
            ],
        );
        let ignore = cfg
            .get("ignore")
            .str_list()
            .iter()
            .map(|s| crate::config::absolute(Path::new(s)))
            .collect();
        Collector {
            cfg,
            registry,
            hooks: Hooks::default(),
            items: Vec::new(),
            errors: Vec::new(),
            conftests: Vec::new(),
            seen_conftests: FxHashSet::default(),
            python_files,
            python_classes,
            python_functions,
            norecursedirs,
            ignore,
            pkg_cache: FxHashMap::default(),
            unittest_case: None,
            marker: std::marker::PhantomData,
        }
    }

    /// Pick up `unittest.TestCase` if the suite has imported `unittest`.
    fn refresh_unittest(&mut self, py: Python<'_>) {
        if self.unittest_case.is_some() {
            return;
        }
        self.unittest_case = py
            .import("sys")
            .and_then(|s| s.getattr("modules"))
            .and_then(|m| m.get_item("unittest"))
            .and_then(|m| m.getattr("TestCase"))
            .map(|c| c.unbind())
            .ok();
    }

    fn relpath(&self, p: &Path) -> String {
        let rel = p.strip_prefix(&self.cfg.rootdir).unwrap_or(p);
        rel.to_string_lossy().replace('\\', "/")
    }

    fn is_package(&mut self, dir: &Path) -> bool {
        if let Some(v) = self.pkg_cache.get(dir) {
            return *v;
        }
        let v = dir.join("__init__.py").is_file();
        self.pkg_cache.insert(dir.to_path_buf(), v);
        v
    }

    /// Compute (`sys.path` entry, dotted module name) for a source file, using
    /// the "prepend" import mode semantics.
    fn module_name_for(&mut self, path: &Path) -> (PathBuf, String) {
        let stem = path.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
        let mut parts = vec![stem];
        let mut dir = path.parent().map(|p| p.to_path_buf()).unwrap_or_default();
        while self.is_package(&dir) {
            let Some(name) = dir.file_name().map(|s| s.to_string_lossy().to_string()) else { break };
            parts.push(name);
            let Some(parent) = dir.parent() else { break };
            dir = parent.to_path_buf();
        }
        parts.reverse();
        (dir, parts.join("."))
    }

    /// Import a Python source file as a module, inserting its base directory on
    /// `sys.path` the way pytest's prepend import mode does.
    fn import_path(&mut self, py: Python<'_>, path: &Path) -> PyResult<Py<PyAny>> {
        let (basedir, dotted) = self.module_name_for(path);
        let sys = py.import("sys")?;
        let sys_path = sys.getattr("path")?;
        let base_str = basedir.to_string_lossy().to_string();
        let already = sys_path
            .try_iter()?
            .filter_map(|p| p.ok())
            .any(|p| p.extract::<String>().map(|s| s == base_str).unwrap_or(false));
        if !already {
            sys_path.call_method1("insert", (0, base_str.as_str()))?;
        }
        let modules = sys.getattr("modules")?;
        if let Ok(Some(existing)) = modules.cast::<PyDict>()?.get_item(dotted.as_str()) {
            let same = existing
                .getattr("__file__")
                .ok()
                .and_then(|f| f.extract::<String>().ok())
                .map(|f| normalize(Path::new(&f)) == normalize(path))
                .unwrap_or(true);
            if same {
                return Ok(existing.unbind());
            }
            // The name is taken by a different file.  This happens whenever a
            // project has `conftest.py` at more than one level without
            // `__init__.py`: every one of them wants the name `conftest`.
            // Load this file directly so each conftest gets its own module
            // object, and leave the most recently loaded one under the shared
            // name, which is what pytest ends up with too.
            return self.import_by_location(py, path, &dotted);
        }
        let importlib = py.import("importlib")?;
        let module = importlib.call_method1("import_module", (dotted.as_str(),))?;
        Ok(module.unbind())
    }

    /// Import a file by path, bypassing the module-name lookup.
    fn import_by_location(&self, py: Python<'_>, path: &Path, name: &str) -> PyResult<Py<PyAny>> {
        let util = py.import("importlib.util")?;
        let spec = util.call_method1("spec_from_file_location", (name, path.to_string_lossy().as_ref()))?;
        if spec.is_none() {
            return Err(pyo3::exceptions::PyImportError::new_err(format!(
                "could not build an import spec for {}",
                path.display()
            )));
        }
        let module = util.call_method1("module_from_spec", (&spec,))?;
        let sys = py.import("sys")?;
        sys.getattr("modules")?.set_item(name, &module)?;
        let loader = spec.getattr("loader")?;
        if let Err(e) = loader.call_method1("exec_module", (&module,)) {
            let _ = sys.getattr("modules")?.del_item(name);
            return Err(e);
        }
        Ok(module.unbind())
    }

    /// Load `conftest.py` for `dir` and every parent up to rootdir.
    pub fn load_conftests_for(&mut self, py: Python<'_>, dir: &Path) -> Result<()> {
        let mut chain: Vec<PathBuf> = Vec::new();
        let mut cur = Some(dir.to_path_buf());
        while let Some(d) = cur {
            chain.push(d.clone());
            if d == self.cfg.rootdir {
                break;
            }
            match d.parent() {
                Some(p) if p.starts_with(&self.cfg.rootdir) || self.cfg.rootdir.starts_with(p) => {
                    cur = Some(p.to_path_buf())
                }
                _ => break,
            }
        }
        chain.reverse();
        for d in chain {
            let cpath = d.join("conftest.py");
            if !cpath.is_file() || self.seen_conftests.contains(&cpath) {
                continue;
            }
            self.seen_conftests.insert(cpath.clone());
            // A conftest that will not import is a configuration problem, not a
            // test failure: report it the way pytest does and stop.
            let module = self.import_path(py, &cpath).map_err(|e| {
                Error::Usage(crate::traceback::format_import_failure(
                    py,
                    &e,
                    "conftest",
                    &cpath.to_string_lossy(),
                ))
            })?;
            let baseid = {
                let rel = self.relpath(&d);
                if rel == "." || rel.is_empty() {
                    String::new()
                } else {
                    rel
                }
            };
            let bound = module.bind(py);
            self.register_hooks(py, bound)?;
            let display = self.relpath(&cpath);
            scan_namespace(py, &mut self.registry, bound, &baseid, &display, false).map_err(Error::Py)?;
            self.conftests.push(Conftest { path: cpath, baseid, module });
        }
        Ok(())
    }

    /// Record `pytest_*` hook implementations found in a module.
    pub fn register_hooks(&mut self, _py: Python<'_>, module: &Bound<'_, PyAny>) -> Result<()> {
        let table: &[(&str, fn(&mut Hooks) -> &mut Vec<Py<PyAny>>)] = &[
            ("pytest_configure", |h| &mut h.configure),
            ("pytest_unconfigure", |h| &mut h.unconfigure),
            ("pytest_report_header", |h| &mut h.report_header),
            ("pytest_collection_modifyitems", |h| &mut h.collection_modifyitems),
            ("pytest_runtest_setup", |h| &mut h.runtest_setup),
            ("pytest_runtest_teardown", |h| &mut h.runtest_teardown),
            ("pytest_runtest_call", |h| &mut h.runtest_call),
            ("pytest_generate_tests", |h| &mut h.generate_tests),
            ("pytest_sessionstart", |h| &mut h.sessionstart),
            ("pytest_sessionfinish", |h| &mut h.sessionfinish),
            ("pytest_make_parametrize_id", |h| &mut h.make_parametrize_id),
            ("pytest_itemcollected", |h| &mut h.itemcollected),
            ("pytest_terminal_summary", |h| &mut h.terminal_summary),
            ("pytest_runtest_makereport", |h| &mut h.runtest_makereport),
            ("pytest_collectstart", |h| &mut h.collectstart),
            ("pytest_ignore_collect", |h| &mut h.ignore_collect),
            ("pytest_addoption", |h| &mut h.addoption),
            ("pytest_cmdline_main", |h| &mut h.cmdline_main),
        ];
        for (name, slot) in table {
            if let Ok(f) = module.getattr(*name) {
                if f.is_callable() {
                    slot(&mut self.hooks).push(f.unbind());
                }
            }
        }
        Ok(())
    }

    /// Expand the command line arguments into concrete files to collect.
    pub fn resolve_targets(&mut self, args: &[String]) -> Vec<Selector> {
        let mut out = Vec::new();
        let raw: Vec<String> = if args.is_empty() {
            let tp = self.cfg.ini_list("testpaths");
            if tp.is_empty() {
                vec![self.cfg.invocation_dir.to_string_lossy().to_string()]
            } else {
                tp.iter()
                    .map(|p| self.cfg.rootdir.join(p).to_string_lossy().to_string())
                    .collect()
            }
        } else {
            args.to_vec()
        };
        for a in raw {
            let (pathpart, rest) = match a.split_once("::") {
                Some((p, r)) => (p.to_string(), r.split("::").map(|s| s.to_string()).collect()),
                None => (a.clone(), Vec::new()),
            };
            let p = crate::config::absolute(Path::new(&pathpart));
            out.push(Selector { path: p, parts: rest });
        }
        out
    }

    fn should_skip_dir(&self, dir: &Path) -> bool {
        let Some(name) = dir.file_name().map(|n| n.to_string_lossy().to_string()) else {
            return false;
        };
        if name == "__pycache__" {
            return true;
        }
        self.norecursedirs.iter().any(|p| fnmatch(p, &name))
    }

    fn matches_python_file(&self, path: &Path) -> bool {
        let Some(name) = path.file_name().map(|n| n.to_string_lossy().to_string()) else {
            return false;
        };
        self.python_files.iter().any(|p| fnmatch(p, &name))
    }

    /// Walk the selectors, returning the files to import in a stable order.
    pub fn discover_files(&mut self, selectors: &[Selector]) -> Vec<(PathBuf, Vec<String>)> {
        let mut out: Vec<(PathBuf, Vec<String>)> = Vec::new();
        let mut seen: FxHashSet<PathBuf> = FxHashSet::default();
        for sel in selectors {
            if sel.path.is_file() {
                if seen.insert(sel.path.clone()) {
                    out.push((sel.path.clone(), sel.parts.clone()));
                }
                continue;
            }
            let mut stack = vec![sel.path.clone()];
            let mut files: Vec<PathBuf> = Vec::new();
            while let Some(dir) = stack.pop() {
                let Ok(rd) = std::fs::read_dir(&dir) else { continue };
                let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
                entries.sort();
                for p in entries {
                    if self.ignore.iter().any(|i| p == *i) {
                        continue;
                    }
                    if p.is_dir() {
                        if !self.should_skip_dir(&p) {
                            stack.push(p);
                        }
                    } else if self.matches_python_file(&p) {
                        files.push(p);
                    }
                }
            }
            files.sort();
            for f in files {
                if seen.insert(f.clone()) {
                    out.push((f, sel.parts.clone()));
                }
            }
        }
        out
    }

    /// Collect every item from one module file.
    pub fn collect_file(&mut self, py: Python<'_>, path: &Path, parts: &[String]) -> Result<()> {
        if let Some(dir) = path.parent() {
            self.load_conftests_for(py, dir)?;
        }
        let module = match self.import_path(py, path) {
            Ok(m) => m,
            Err(e) => {
                let rel = self.relpath(path);
                let text = crate::traceback::format_import_failure(
                    py,
                    &e,
                    "test module",
                    &path.to_string_lossy(),
                );
                self.errors.push((rel, text));
                return Ok(());
            }
        };
        let bound = module.bind(py);
        let rel = self.relpath(path);
        self.refresh_unittest(py);
        // xunit-style module setup is injected before the module's own
        // fixtures so that it sorts ahead of them, as in pytest.
        self.inject_module_xunit(bound, &rel);
        // Module-level fixtures.
        scan_namespace(py, &mut self.registry, bound, &rel, &rel, false).map_err(Error::Py)?;
        let module_marks = marks::own_marks(py, bound).unwrap_or_default();
        let module_name: String = bound
            .getattr("__name__")
            .and_then(|n| n.extract())
            .unwrap_or_else(|_| rel.clone());

        let names: Vec<String> = match bound.getattr("__dict__").and_then(|d| d.cast_into::<PyDict>().map_err(PyErr::from)) {
            Ok(d) => d.keys().iter().filter_map(|k| k.extract::<String>().ok()).collect(),
            Err(_) => Vec::new(),
        };

        let mut ctx = ModuleCtx {
            path: path.to_path_buf(),
            relpath: rel.clone(),
            module: module.clone_ref(py),
            module_name,
            module_marks,
        };

        for name in names {
            if name.starts_with('_') {
                continue;
            }
            let Ok(obj) = bound.getattr(name.as_str()) else { continue };
            // Only consider objects defined in (or re-exported into) this module.
            let kind = self.class_kind(&obj, &name);
            if kind != ClassKind::None {
                let cls_parts = vec![name.clone()];
                self.collect_class(py, &mut ctx, &obj, &cls_parts, parts, kind)?;
            } else if self.is_test_function(&name, &obj) {
                if !parts.is_empty() && !selector_matches(parts, &[name.clone()]) {
                    continue;
                }
                self.make_items(py, &mut ctx, None, &[], &name, &obj, parts, false)?;
            }
        }
        Ok(())
    }

    /// `setup_module`/`teardown_module` and `setup_function`/`teardown_function`
    /// become autouse fixtures, but only for modules that define them.
    fn inject_module_xunit(&mut self, module: &Bound<'_, PyAny>, rel: &str) {
        let stem = rel.rsplit('/').next().unwrap_or(rel).replace('.', "_");
        if defines_any(module, &["setUpModule", "setup_module", "tearDownModule", "teardown_module"]) {
            crate::fixtures::insert_xunit(
                &mut self.registry,
                format!("_xunit_setup_module_fixture_{stem}"),
                crate::fixtures::Scope::Module,
                rel,
                crate::fixtures::Builtin::XunitModule,
                format!("{rel}::setup_module"),
            );
        }
        if defines_any(module, &["setup_function", "teardown_function"]) {
            crate::fixtures::insert_xunit(
                &mut self.registry,
                format!("_xunit_setup_function_fixture_{stem}"),
                crate::fixtures::Scope::Function,
                rel,
                crate::fixtures::Builtin::XunitFunction,
                format!("{rel}::setup_function"),
            );
        }
    }

    /// The class-level half: `setUpClass`/`tearDownClass` for unittest,
    /// `setup_class`/`teardown_class` and `setup_method`/`teardown_method` for
    /// any test class.
    fn inject_class_xunit(&mut self, cls: &Bound<'_, PyAny>, baseid: &str, kind: ClassKind) {
        let tail = baseid.rsplit("::").next().unwrap_or(baseid).to_string();
        if kind == ClassKind::UnitTest && self.overrides_unittest_hooks(cls) {
            crate::fixtures::insert_xunit(
                &mut self.registry,
                format!("_unittest_setUpClass_fixture_{tail}"),
                crate::fixtures::Scope::Class,
                baseid,
                crate::fixtures::Builtin::UnittestClass,
                format!("{baseid}::setUpClass"),
            );
        }
        if defines_any(cls, &["setup_class", "teardown_class"]) {
            crate::fixtures::insert_xunit(
                &mut self.registry,
                format!("_xunit_setup_class_fixture_{tail}"),
                crate::fixtures::Scope::Class,
                baseid,
                crate::fixtures::Builtin::XunitClass,
                format!("{baseid}::setup_class"),
            );
        }
        if defines_any(cls, &["setup_method", "teardown_method"]) {
            crate::fixtures::insert_xunit(
                &mut self.registry,
                format!("_xunit_setup_method_fixture_{tail}"),
                crate::fixtures::Scope::Function,
                baseid,
                crate::fixtures::Builtin::XunitMethod,
                format!("{baseid}::setup_method"),
            );
        }
    }

    /// Every `TestCase` inherits a no-op `setUpClass`, so asking whether the
    /// attribute exists would put every unittest class into its own serial
    /// group for nothing.  Only a real override counts.
    fn overrides_unittest_hooks(&self, cls: &Bound<'_, PyAny>) -> bool {
        let Some(base) = &self.unittest_case else { return false };
        let base = base.bind(cls.py());
        ["setUpClass", "tearDownClass"].iter().any(|name| {
            let (Ok(own), Ok(inherited)) = (cls.getattr(*name), base.getattr(*name)) else {
                return false;
            };
            let own = own.getattr("__func__").unwrap_or(own);
            let inherited = inherited.getattr("__func__").unwrap_or(inherited);
            !own.is(&inherited)
        })
    }

    fn class_kind(&self, obj: &Bound<'_, PyAny>, name: &str) -> ClassKind {
        if !obj.is_instance_of::<PyType>() {
            return ClassKind::None;
        }
        // `unittest.TestCase` subclasses are collected whatever they are called
        // and despite having a constructor, exactly as pytest does.
        if let Some(base) = &self.unittest_case {
            if crate::raises::is_subclass_of(obj, base.bind(obj.py())).unwrap_or(false) {
                return ClassKind::UnitTest;
            }
        }
        if !self.python_classes.iter().any(|p| starts_or_matches(p, name)) {
            return ClassKind::None;
        }
        // pytest refuses to collect classes with an __init__ constructor.
        let plain_init = obj
            .getattr("__init__")
            .map(|i| {
                i.getattr("__objclass__")
                    .map(|c| c.is(&obj.py().get_type::<pyo3::types::PyAny>()))
                    .unwrap_or(false)
                    || i.getattr("__qualname__")
                        .and_then(|q| q.extract::<String>())
                        .map(|q| q == "object.__init__")
                        .unwrap_or(false)
            })
            .unwrap_or(true);
        match plain_init {
            true => ClassKind::Plain,
            false => ClassKind::None,
        }
    }

    fn is_test_function(&self, name: &str, obj: &Bound<'_, PyAny>) -> bool {
        if !self.python_functions.iter().any(|p| starts_or_matches(p, name)) {
            return false;
        }
        obj.is_callable() && obj.getattr("__code__").is_ok()
    }

    fn collect_class(
        &mut self,
        py: Python<'_>,
        ctx: &mut ModuleCtx,
        cls: &Bound<'_, PyAny>,
        cls_parts: &[String],
        selector: &[String],
        kind: ClassKind,
    ) -> Result<()> {
        if !selector.is_empty() {
            let depth = cls_parts.len().min(selector.len());
            if selector[..depth] != cls_parts[..depth] {
                return Ok(());
            }
        }
        // pytest honours `__test__ = False` on a class by not collecting it.
        if cls
            .getattr("__test__")
            .map(|v| !v.is_truthy().unwrap_or(true))
            .unwrap_or(false)
        {
            return Ok(());
        }
        let baseid = format!("{}::{}", ctx.relpath, cls_parts.join("::"));
        self.inject_class_xunit(cls, &baseid, kind);
        scan_namespace(py, &mut self.registry, cls, &baseid, &baseid, true).map_err(Error::Py)?;
        if kind == ClassKind::UnitTest {
            return self.collect_unittest_methods(py, ctx, cls, cls_parts, selector, &baseid);
        }
        let names: Vec<String> = match cls.getattr("__dict__") {
            Ok(d) => {
                let keys = d.call_method0("keys").map_err(Error::Py)?;
                keys.try_iter()
                    .map_err(Error::Py)?
                    .filter_map(|k| k.ok().and_then(|k| k.extract::<String>().ok()))
                    .collect()
            }
            Err(_) => Vec::new(),
        };
        // Include inherited test methods, like pytest does.
        let mut all_names = names.clone();
        if let Ok(mro) = cls.getattr("__mro__") {
            if let Ok(t) = mro.cast::<PyTuple>() {
                for base in t.iter().skip(1) {
                    if base.getattr("__name__").and_then(|n| n.extract::<String>()).map(|n| n == "object").unwrap_or(false) {
                        continue;
                    }
                    if let Ok(d) = base.getattr("__dict__") {
                        if let Ok(keys) = d.call_method0("keys") {
                            if let Ok(it) = keys.try_iter() {
                                for k in it.flatten() {
                                    if let Ok(s) = k.extract::<String>() {
                                        if !all_names.contains(&s) {
                                            all_names.push(s);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for name in all_names {
            if name.starts_with('_') {
                continue;
            }
            let Ok(obj) = cls.getattr(name.as_str()) else { continue };
            let nested_kind = self.class_kind(&obj, &name);
            if nested_kind != ClassKind::None {
                let mut nested = cls_parts.to_vec();
                nested.push(name.clone());
                self.collect_class(py, ctx, &obj, &nested, selector, nested_kind)?;
            } else if self.is_test_function(&name, &obj) {
                if !selector.is_empty() {
                    let mut full = cls_parts.to_vec();
                    full.push(name.clone());
                    if !selector_matches(selector, &full) {
                        continue;
                    }
                }
                self.make_items(py, ctx, Some(cls), cls_parts, &name, &obj, selector, false)?;
            }
        }
        Ok(())
    }

    /// Method discovery for a `unittest.TestCase`.
    ///
    /// unittest, not `python_functions`, decides what a test is here: names
    /// starting with `test`, in alphabetical order rather than definition
    /// order.  Deferring to `TestLoader` keeps both rules in one place and
    /// picks up a subclass that changed `testMethodPrefix`.
    fn collect_unittest_methods(
        &mut self,
        py: Python<'_>,
        ctx: &mut ModuleCtx,
        cls: &Bound<'_, PyAny>,
        cls_parts: &[String],
        selector: &[String],
        _baseid: &str,
    ) -> Result<()> {
        let loader = py
            .import("unittest")
            .and_then(|m| m.getattr("TestLoader"))
            .and_then(|t| t.call0())
            .map_err(Error::Py)?;
        let names = loader.call_method1("getTestCaseNames", (cls,)).map_err(Error::Py)?;
        let names: Vec<String> = names
            .try_iter()
            .map_err(Error::Py)?
            .filter_map(|n| n.ok().and_then(|n| n.extract::<String>().ok()))
            .collect();
        for name in names {
            let Ok(obj) = cls.getattr(name.as_str()) else { continue };
            if obj.getattr("__test__").map(|v| !v.is_truthy().unwrap_or(true)).unwrap_or(false) {
                continue;
            }
            if !selector.is_empty() {
                let mut full = cls_parts.to_vec();
                full.push(name.clone());
                if !selector_matches(selector, &full) {
                    continue;
                }
            }
            self.make_items(py, ctx, Some(cls), cls_parts, &name, &obj, selector, true)?;
        }
        Ok(())
    }

    /// Build one or more items for a test function, expanding parametrisation.
    #[allow(clippy::too_many_arguments)]
    fn make_items(
        &mut self,
        py: Python<'_>,
        ctx: &mut ModuleCtx,
        cls: Option<&Bound<'_, PyAny>>,
        cls_parts: &[String],
        name: &str,
        func: &Bound<'_, PyAny>,
        selector: &[String],
        unittest: bool,
    ) -> Result<()> {
        let in_class = cls.is_some();
        let mut own = marks::own_marks(py, func).unwrap_or_default();
        let mut class_marks: Vec<MarkData> = Vec::new();
        if let Some(c) = cls {
            class_marks = marks::own_marks(py, c).unwrap_or_default();
        }
        let mut argnames = signature_argnames(py, func, in_class).map_err(Error::Py)?;
        // Arguments with defaults are not treated as fixtures by pytest.
        if let Ok(defaults) = func.getattr("__defaults__") {
            if let Ok(t) = defaults.cast::<PyTuple>() {
                let ndef = t.len();
                if ndef > 0 && ndef <= argnames.len() {
                    argnames.truncate(argnames.len() - ndef);
                }
            }
        }

        let base_nodeid = match cls_parts.is_empty() {
            true => format!("{}::{}", ctx.relpath, name),
            false => format!("{}::{}::{}", ctx.relpath, cls_parts.join("::"), name),
        };

        let mut usefixtures = usefixtures_from_marks(py, &own);
        usefixtures.extend(usefixtures_from_marks(py, &class_marks));
        usefixtures.extend(usefixtures_from_marks(py, &ctx.module_marks));
        usefixtures.extend(self.cfg.ini_list("usefixtures"));
        let closure = build_closure(&self.registry, &base_nodeid, &argnames, &usefixtures);

        // Parametrised fixtures are expanded first: pytest runs the fixture
        // plugin's `pytest_generate_tests` before the one that processes
        // `parametrize` markers, so fixture ids come first in the test id and
        // direct parameters vary fastest.
        let mut callspecs: Vec<CallSpec> = vec![CallSpec::default()];
        let direct_param_names: FxHashSet<String> = own
            .iter()
            .chain(class_marks.iter())
            .chain(ctx.module_marks.iter())
            .filter(|m| m.name == "parametrize")
            .filter_map(|m| m.args.bind(py).get_item(0).ok())
            .flat_map(|a| marks::parse_argnames(py, &a).unwrap_or_default())
            .collect();
        for def in &closure.order {
            let Some(params) = &def.params else { continue };
            if direct_param_names.contains(&def.argname) {
                continue;
            }
            callspecs = self.apply_fixture_params(py, callspecs, def, params)?;
        }

        // Direct parametrisation from marks (function first, then class/module).
        let mut param_marks: Vec<MarkData> = Vec::new();
        for m in own.iter().chain(class_marks.iter()).chain(ctx.module_marks.iter()) {
            if m.name == "parametrize" {
                param_marks.push(m.clone());
            }
        }
        for m in &param_marks {
            callspecs = self.apply_parametrize(py, callspecs, m, &base_nodeid)?;
        }

        let fixture_hostile: Option<String> = closure
            .order
            .iter()
            .find(|d| d.thread_hostile)
            .map(|d| format!("fixture {:?}", d.argname));
        let func_hostile = crate::threadsafety::thread_hostile_reason(py, func)
            .unwrap_or(None)
            .map(|n| format!("references {n:?}"));

        let line = unwrap_func(func)
            .getattr("__code__")
            .and_then(|c| c.getattr("co_firstlineno"))
            .and_then(|l| l.extract::<usize>())
            .unwrap_or(0);

        for cs in callspecs {
            let id = cs.id();
            let item_name = if cs.id_parts.is_empty() {
                name.to_string()
            } else {
                format!("{name}[{id}]")
            };
            let nodeid = match cls_parts.is_empty() {
                true => format!("{}::{}", ctx.relpath, item_name),
                false => format!("{}::{}::{}", ctx.relpath, cls_parts.join("::"), item_name),
            };
            if !selector.is_empty() {
                let mut full = cls_parts.to_vec();
                full.push(item_name.clone());
                if !selector_matches(selector, &full) {
                    // Also allow selecting the unparametrised name.
                    let mut base = cls_parts.to_vec();
                    base.push(name.to_string());
                    if !selector_matches(selector, &base) {
                        continue;
                    }
                }
            }

            let mut all_marks: Vec<MarkData> = Vec::new();
            all_marks.extend(own.iter().cloned());
            all_marks.extend(cs.marks.iter().cloned());
            all_marks.extend(class_marks.iter().cloned());
            all_marks.extend(ctx.module_marks.iter().cloned());

            let mut hostile_reason = fixture_hostile.clone().or_else(|| func_hostile.clone());
            if let Some(m) = all_marks
                .iter()
                .find(|m| crate::threadsafety::MARK_THREAD_UNSAFE.contains(&m.name.as_str()))
            {
                hostile_reason = Some(format!("marked {:?}", m.name));
            }
            // Scoping warning filters to one test needs `catch_warnings`, which
            // swaps a process-global stack unless the interpreter scopes it per
            // context.
            if !crate::threadsafety::warnings_are_context_aware(py)
                && all_marks.iter().any(|m| m.name == "filterwarnings")
            {
                hostile_reason = Some("marked \"filterwarnings\"".to_string());
            }
            if all_marks
                .iter()
                .any(|m| crate::threadsafety::MARK_THREAD_SAFE.contains(&m.name.as_str()))
            {
                hostile_reason = None;
            }
            let hostile = hostile_reason.is_some();

            let mut keywords: Vec<String> = vec![item_name.clone(), name.to_string()];
            keywords.extend(cls_parts.iter().cloned());
            keywords.push(
                ctx.path
                    .file_name()
                    .map(|f| f.to_string_lossy().to_string())
                    .unwrap_or_default(),
            );
            keywords.push(ctx.relpath.clone());
            for m in &all_marks {
                keywords.push(m.name.clone());
            }

            let filter_specs = crate::warnings::marker_specs(py, &all_marks);
            let index = self.items.len();
            self.items.push(Arc::new(Item {
                index,
                nodeid,
                name: item_name,
                originalname: name.to_string(),
                path: ctx.path.clone(),
                relpath: ctx.relpath.clone(),
                module: ctx.module.clone_ref(py),
                module_name: ctx.module_name.clone(),
                cls: cls.map(|c| c.clone().unbind()),
                cls_name: if cls_parts.is_empty() { None } else { Some(cls_parts.join("::")) },
                func: func.clone().unbind(),
                marks: all_marks,
                extra_marks: Mutex::new(Vec::new()),
                closure: closure.clone(),
                callspec: cs,
                line,
                thread_hostile: hostile,
                hostile_reason,
                in_class,
                unittest,
                keywords,
                filter_specs,
            }));
        }
        own.clear();
        Ok(())
    }

    /// Handle one `@pytest.mark.parametrize(...)` marker.
    fn apply_parametrize(
        &mut self,
        py: Python<'_>,
        callspecs: Vec<CallSpec>,
        mark: &MarkData,
        nodeid: &str,
    ) -> Result<Vec<CallSpec>> {
        let args = mark.args.bind(py);
        if args.len() < 2 {
            return Err(Error::usage(format!(
                "In {nodeid}: parametrize() requires argnames and argvalues"
            )));
        }
        let argnames = marks::parse_argnames(py, &args.get_item(0).map_err(Error::Py)?).map_err(Error::Py)?;
        let argvalues = args.get_item(1).map_err(Error::Py)?;
        let indirect = mark.kwarg(py, "indirect");
        let ids_arg = mark.kwarg(py, "ids");

        let mut sets: Vec<ParamSet> = Vec::new();
        for raw in argvalues.try_iter().map_err(Error::Py)? {
            let raw = raw.map_err(Error::Py)?;
            sets.push(ParamSet::from_py(py, &raw, argnames.len()).map_err(Error::Py)?);
        }
        if sets.is_empty() {
            // `empty_parameter_set_mark`: emit a single skipped placeholder.
            let mut ps = ParamSet {
                values: Vec::new(),
                marks: vec![{
                    let mut m = MarkData::new(py, "skip");
                    let kw = PyDict::new(py);
                    kw.set_item("reason", format!("got empty parameter set {argnames:?}, function at {nodeid}"))
                        .map_err(Error::Py)?;
                    m.kwargs = kw.unbind();
                    m
                }],
                id: None,
            };
            for _ in 0..argnames.len() {
                ps.values.push(py.None());
            }
            sets.push(ps);
        }

        let user_ids = resolve_user_ids(py, ids_arg.as_ref(), &sets, &argnames).map_err(Error::Py)?;
        let mut generated: Vec<String> = Vec::with_capacity(sets.len());
        for (i, ps) in sets.iter().enumerate() {
            let bound: Vec<Bound<'_, PyAny>> = ps.values.iter().map(|v| v.bind(py).clone()).collect();
            generated.push(ids::idvalset(
                py,
                &bound,
                &argnames,
                i,
                ps.id.as_deref(),
                user_ids.as_ref().and_then(|u| u.get(i).and_then(|x| x.as_deref())),
            ));
        }
        ids::make_unique(&mut generated);

        let indirect_all = indirect
            .as_ref()
            .map(|i| i.is_truthy().unwrap_or(false) && i.extract::<Vec<String>>().is_err())
            .unwrap_or(false);
        let indirect_names: FxHashSet<String> = match &indirect {
            Some(i) => i.extract::<Vec<String>>().unwrap_or_default().into_iter().collect(),
            None => FxHashSet::default(),
        };

        let mut out = Vec::with_capacity(callspecs.len() * sets.len());
        for cs in &callspecs {
            for (i, ps) in sets.iter().enumerate() {
                let mut new = clone_callspec(py, cs);
                for (j, argname) in argnames.iter().enumerate() {
                    let v = ps.values.get(j).map(|v| v.clone_ref(py)).unwrap_or_else(|| py.None());
                    new.params.push((argname.clone(), v));
                    new.indices.insert(argname.clone(), i);
                    if indirect_all || indirect_names.contains(argname) {
                        new.indirect.insert(argname.clone());
                    }
                }
                new.id_parts.push(generated[i].clone());
                new.marks.extend(ps.marks.iter().cloned());
                out.push(new);
            }
        }
        Ok(out)
    }

    /// Expand a parametrised fixture across the current call specs.
    fn apply_fixture_params(
        &mut self,
        py: Python<'_>,
        callspecs: Vec<CallSpec>,
        def: &Arc<FixtureDef>,
        params: &[Py<PyAny>],
    ) -> Result<Vec<CallSpec>> {
        let argnames = vec![def.argname.clone()];
        let sets: Vec<ParamSet> = params
            .iter()
            .map(|p| ParamSet { values: vec![p.clone_ref(py)], marks: Vec::new(), id: None })
            .collect();
        let bound_ids = def.param_ids.as_ref().map(|i| i.bind(py).clone());
        let user_ids = resolve_user_ids(py, bound_ids.as_ref(), &sets, &argnames)
            .map_err(Error::Py)?;
        let mut generated: Vec<String> = Vec::with_capacity(sets.len());
        for (i, ps) in sets.iter().enumerate() {
            let bound: Vec<Bound<'_, PyAny>> = ps.values.iter().map(|v| v.bind(py).clone()).collect();
            generated.push(ids::idvalset(
                py,
                &bound,
                &argnames,
                i,
                None,
                user_ids.as_ref().and_then(|u| u.get(i).and_then(|x| x.as_deref())),
            ));
        }
        ids::make_unique(&mut generated);

        let mut out = Vec::with_capacity(callspecs.len() * sets.len());
        for cs in &callspecs {
            for (i, ps) in sets.iter().enumerate() {
                let mut new = clone_callspec(py, cs);
                new.params.push((def.argname.clone(), ps.values[0].clone_ref(py)));
                new.indices.insert(def.argname.clone(), i);
                new.indirect.insert(def.argname.clone());
                new.id_parts.push(generated[i].clone());
                out.push(new);
            }
        }
        Ok(out)
    }
}

struct ModuleCtx {
    path: PathBuf,
    relpath: String,
    module: Py<PyAny>,
    module_name: String,
    module_marks: Vec<MarkData>,
}

struct ParamSet {
    values: Vec<Py<PyAny>>,
    marks: Vec<MarkData>,
    id: Option<String>,
}

impl ParamSet {
    fn from_py(py: Python<'_>, obj: &Bound<'_, PyAny>, nargs: usize) -> PyResult<ParamSet> {
        if let Ok(ps) = obj.extract::<marks::ParameterSet>() {
            let mut values = Vec::new();
            for v in ps.values.bind(py).iter() {
                values.push(v.unbind());
            }
            let mut m = Vec::new();
            for mk in ps.marks.bind(py).iter() {
                m.push(marks::mark_from_py(py, &mk)?);
            }
            return Ok(ParamSet { values, marks: m, id: ps.id });
        }
        if nargs == 1 {
            return Ok(ParamSet { values: vec![obj.clone().unbind()], marks: Vec::new(), id: None });
        }
        let mut values = Vec::new();
        for v in obj.try_iter()? {
            values.push(v?.unbind());
        }
        Ok(ParamSet { values, marks: Vec::new(), id: None })
    }
}

fn clone_callspec(py: Python<'_>, cs: &CallSpec) -> CallSpec {
    CallSpec {
        params: cs.params.iter().map(|(k, v)| (k.clone(), v.clone_ref(py))).collect(),
        indirect: cs.indirect.clone(),
        indices: cs.indices.clone(),
        id_parts: cs.id_parts.clone(),
        marks: cs.marks.clone(),
    }
}

/// Normalise the `ids=` argument into per-parameter-set strings.
fn resolve_user_ids(
    py: Python<'_>,
    ids_arg: Option<&Bound<'_, PyAny>>,
    sets: &[ParamSet],
    argnames: &[String],
) -> PyResult<Option<Vec<Option<String>>>> {
    let Some(ids) = ids_arg else { return Ok(None) };
    if ids.is_none() {
        return Ok(None);
    }
    if ids.is_callable() {
        let mut out = Vec::with_capacity(sets.len());
        for ps in sets {
            let mut parts: Vec<String> = Vec::new();
            let mut any = false;
            for (i, v) in ps.values.iter().enumerate() {
                let r = ids.call1((v.bind(py),))?;
                if r.is_none() {
                    let argname = argnames.get(i).cloned().unwrap_or_default();
                    parts.push(
                        ids::idval(py, v.bind(py)).unwrap_or_else(|| format!("{argname}{i}")),
                    );
                } else {
                    any = true;
                    parts.push(r.str()?.to_string());
                }
            }
            out.push(if any { Some(parts.join("-")) } else { None });
        }
        return Ok(Some(out));
    }
    let mut out = Vec::with_capacity(sets.len());
    for item in ids.try_iter()? {
        let item = item?;
        if item.is_none() {
            out.push(None);
        } else {
            out.push(Some(item.str()?.to_string()));
        }
    }
    Ok(Some(out))
}

fn non_empty(v: Vec<String>, fallback: Vec<String>) -> Vec<String> {
    if v.is_empty() {
        fallback
    } else {
        v
    }
}

/// Follow `functools.wraps` chains, as pytest's `get_real_func` does, so that a
/// decorated test reports where it was written rather than where the decorator
/// was.  `@unittest.skip` is the case that makes this visible: it replaces the
/// method with a wrapper defined in `unittest/case.py`.
fn unwrap_func<'py>(func: &Bound<'py, PyAny>) -> Bound<'py, PyAny> {
    let mut cur = func.clone();
    for _ in 0..100 {
        match cur.getattr("__wrapped__") {
            Ok(next) if next.is_callable() => cur = next,
            _ => return cur,
        }
    }
    cur
}

/// Whether a module or class provides any of these as a plain callable.  A
/// `@pytest.fixture` that happens to share the name is a fixture, not an xunit
/// function, and pytest skips it here too.
fn defines_any(holder: &Bound<'_, PyAny>, names: &[&str]) -> bool {
    names.iter().any(|name| {
        holder
            .getattr(*name)
            .map(|f| f.is_callable() && f.getattr("_pytestfixturefunction").is_err())
            .unwrap_or(false)
    })
}

/// `python_classes = Test` matches by prefix; a pattern with glob characters
/// matches with fnmatch.
fn starts_or_matches(pattern: &str, name: &str) -> bool {
    if pattern.contains(['*', '?', '[']) {
        fnmatch(pattern, name)
    } else {
        name.starts_with(pattern)
    }
}

/// Does a `::`-separated selector match this chain of names?
fn selector_matches(selector: &[String], chain: &[String]) -> bool {
    let n = selector.len().min(chain.len());
    selector[..n] == chain[..n]
}

/// Reorder items so that all tests from the same module stay adjacent, which
/// keeps module-scoped fixtures alive for a contiguous run.
pub fn group_by_module(items: &mut [Arc<Item>]) {
    let mut order: FxHashMap<String, usize> = FxHashMap::default();
    let mut next = 0usize;
    for it in items.iter() {
        if !order.contains_key(&it.relpath) {
            order.insert(it.relpath.clone(), next);
            next += 1;
        }
    }
    items.sort_by_key(|i| (order[&i.relpath], i.index));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn glob_matching() {
        assert!(fnmatch("test_*.py", "test_foo.py"));
        assert!(!fnmatch("test_*.py", "foo_test.py"));
        assert!(fnmatch("*_test.py", "foo_test.py"));
        assert!(fnmatch(".*", ".git"));
        assert!(!fnmatch(".*", "src"));
        assert!(fnmatch("*.egg", "thing.egg"));
    }

    #[test]
    fn selectors() {
        assert!(selector_matches(&["TestX".to_string()], &["TestX".to_string(), "test_y".to_string()]));
        assert!(!selector_matches(&["TestY".to_string()], &["TestX".to_string()]));
    }
}

