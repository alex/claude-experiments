//! Scheduling and execution.
//!
//! Work is split into two phases:
//!
//! * a **parallel phase**, where items are partitioned into serial groups —
//!   any two tests that would share a non-session scoped fixture instance land
//!   in the same group — and groups are handed to a pool of worker threads;
//! * a **serial phase**, holding the tests that the thread-safety analysis
//!   flagged as touching process-global state (and benchmarks, which want a
//!   quiet machine).
//!
//! Within a group, items execute in order on one thread, so scope frames and
//! finalisation behave exactly as they do under stock pytest.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyTuple};
use rustc_hash::FxHashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::time::Instant;

use crate::fixtures::Scope;
use crate::marks::{evaluate_skip, evaluate_xfail, SkipDecision};
use crate::outcomes::{outcome_message, Exit, Failed, Outcome, Skipped, XFailed};
use crate::report::{TestReport, When};
use crate::runtime::{SessionCache, Worker};
use crate::session::{ConfigData, Item, PyItem, Session};

/// Call a hook implementation, passing only the arguments it declares.
pub fn call_hook<'py>(
    py: Python<'py>,
    func: &Bound<'py, PyAny>,
    available: &[(&str, Bound<'py, PyAny>)],
) -> PyResult<Bound<'py, PyAny>> {
    let kwargs = PyDict::new(py);
    if let Ok(code) = func.getattr("__code__") {
        let argcount: usize = code.getattr("co_argcount")?.extract()?;
        let varnames = code.getattr("co_varnames")?;
        let t = varnames.cast::<PyTuple>()?;
        for i in 0..argcount {
            let n: String = t.get_item(i)?.extract()?;
            if let Some((_, v)) = available.iter().find(|(k, _)| *k == n) {
                kwargs.set_item(&n, v)?;
            }
        }
    } else {
        for (k, v) in available {
            kwargs.set_item(*k, v)?;
        }
    }
    func.call((), Some(&kwargs))
}

/// Union-find over item indices.
struct Dsu {
    parent: Vec<usize>,
}

impl Dsu {
    fn new(n: usize) -> Self {
        Dsu { parent: (0..n).collect() }
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[rb] = ra;
        }
    }
}

pub struct Plan {
    /// Groups of item indices that can run concurrently with each other.
    pub groups: Vec<Vec<usize>>,
    /// Items that must run alone, in order.
    pub serial: Vec<usize>,
}

/// Partition items into serial groups.
///
/// `durations` holds per-node-id timings recorded by an earlier run; when
/// present, groups are started longest-first (the LPT heuristic), which is what
/// keeps a single expensive group from being picked up last and defining the
/// makespan.
pub fn plan(session: &Session, parallel: bool, durations: &FxHashMap<String, f64>) -> Plan {
    let items = &session.items;
    if !parallel {
        return Plan { groups: Vec::new(), serial: (0..items.len()).collect() };
    }
    let mut dsu = Dsu::new(items.len());
    let mut first_for_key: FxHashMap<String, usize> = FxHashMap::default();
    let mut serial: Vec<usize> = Vec::new();

    for (i, item) in items.iter().enumerate() {
        if item.thread_hostile {
            serial.push(i);
            continue;
        }
        for def in &item.closure.order {
            let shares = match def.scope {
                // Function scoped instances are never shared between tests.
                Scope::Function => false,
                // Session scoped fixtures live in the process-wide cache rather
                // than being grouped.  A thread-hostile one makes every item in
                // its closure hostile, so those items are already on the serial
                // path and never reach here.
                Scope::Session => false,
                _ => true,
            };
            if !shares || def.builtin.is_some() {
                continue;
            }
            let param_index = item.callspec.indices.get(&def.argname).copied().unwrap_or(0);
            let key = format!("{}#{}#{}", def.uid, param_index, item.scope_key(def.scope));
            match first_for_key.get(&key) {
                Some(&j) => dsu.union(j, i),
                None => {
                    first_for_key.insert(key, i);
                }
            }
        }
    }

    let mut buckets: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    let mut order: Vec<usize> = Vec::new();
    for (i, item) in items.iter().enumerate() {
        if item.thread_hostile {
            continue;
        }
        let root = dsu.find(i);
        if !buckets.contains_key(&root) {
            order.push(root);
        }
        buckets.entry(root).or_default().push(i);
    }
    let mut groups: Vec<Vec<usize>> = order.into_iter().filter_map(|r| buckets.remove(&r)).collect();
    // Longest-first keeps the tail of the run from being one slow group.  With
    // no recorded durations, item count is the best proxy available.
    const ASSUMED: f64 = 0.001;
    let weight = |g: &Vec<usize>| -> f64 {
        g.iter()
            .map(|&i| durations.get(&items[i].nodeid).copied().unwrap_or(ASSUMED))
            .sum()
    };
    if durations.is_empty() {
        groups.sort_by_key(|g| std::cmp::Reverse(g.len()));
    } else {
        let mut keyed: Vec<(f64, Vec<usize>)> = groups.into_iter().map(|g| (weight(&g), g)).collect();
        keyed.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
        groups = keyed.into_iter().map(|(_, g)| g).collect();
    }
    Plan { groups, serial }
}

/// Shared mutable run state.
pub struct RunState {
    pub failures: AtomicUsize,
    pub stop: AtomicBool,
    pub maxfail: usize,
    pub exit_message: Mutex<Option<String>>,
}

impl RunState {
    pub fn should_stop(&self) -> bool {
        self.stop.load(Ordering::Relaxed)
    }

    pub fn record_failure(&self) {
        let n = self.failures.fetch_add(1, Ordering::Relaxed) + 1;
        if self.maxfail > 0 && n >= self.maxfail {
            self.stop.store(true, Ordering::Relaxed);
        }
    }
}

/// Execute the whole session, sending reports through `tx`.
pub struct PhaseTimings {
    pub parallel: f64,
    pub serial: f64,
}

pub fn execute(
    session: Arc<Session>,
    session_cache: Arc<SessionCache>,
    plan: Plan,
    state: Arc<RunState>,
    tx: mpsc::Sender<TestReport>,
    workers: usize,
) -> PhaseTimings {
    let mut timings = PhaseTimings { parallel: 0.0, serial: 0.0 };
    let phase_start = Instant::now();
    // Workers pop from the back, so reverse to hand out the heaviest group
    // first.
    let mut ordered = plan.groups;
    ordered.reverse();
    let queue = Arc::new(Mutex::new(ordered));
    let mut handles = Vec::new();
    if workers > 1 {
        for wid in 1..workers {
            let session = session.clone();
            let session_cache = session_cache.clone();
            let queue = queue.clone();
            let state = state.clone();
            let tx = tx.clone();
            handles.push(std::thread::spawn(move || {
                worker_loop(session, session_cache, queue, state, tx, wid);
            }));
        }
    }
    // The invoking thread participates too.
    worker_loop(session.clone(), session_cache.clone(), queue, state.clone(), tx.clone(), 0);
    for h in handles {
        let _ = h.join();
    }
    timings.parallel = phase_start.elapsed().as_secs_f64();

    // Serial phase: thread-hostile items, one at a time.
    let serial_start = Instant::now();
    if !plan.serial.is_empty() && !state.should_stop() {
        let worker = Worker::new(session.clone(), session_cache.clone());
        Python::attach(|py| {
            for (pos, &idx) in plan.serial.iter().enumerate() {
                if state.should_stop() {
                    break;
                }
                let item = session.items[idx].clone();
                let next = plan.serial.get(pos + 1).map(|&n| &session.items[n]);
                let rep = run_one(py, &worker, &item, next, &state, 0);
                let _ = tx.send(rep);
            }
            worker.drain(py);
        });
    }
    timings.serial = serial_start.elapsed().as_secs_f64();
    timings
}

fn worker_loop(
    session: Arc<Session>,
    session_cache: Arc<SessionCache>,
    queue: Arc<Mutex<Vec<Vec<usize>>>>,
    state: Arc<RunState>,
    tx: mpsc::Sender<TestReport>,
    wid: usize,
) {
    let worker = Worker::new(session.clone(), session_cache);
    loop {
        if state.should_stop() {
            break;
        }
        let group = {
            let mut q = queue.lock().unwrap();
            q.pop()
        };
        let Some(group) = group else { break };
        Python::attach(|py| {
            for (pos, &idx) in group.iter().enumerate() {
                if state.should_stop() {
                    break;
                }
                let item = session.items[idx].clone();
                let next = group.get(pos + 1).map(|&n| &session.items[n]);
                let rep = run_one(py, &worker, &item, next, &state, wid);
                let _ = tx.send(rep);
            }
            for e in worker.drain(py) {
                eprintln!("pytest-rs: error during teardown: {e}");
            }
        });
    }
}

/// Run a single test through setup / call / teardown.
///
/// Capturing is started and stopped here rather than inside the body: the body
/// has many early exits, and a thread that leaves its buffer registered would
/// collect the next test's output too.
pub fn run_one(
    py: Python<'_>,
    worker: &Arc<Worker>,
    item: &Arc<Item>,
    next: Option<&Arc<Item>>,
    state: &RunState,
    wid: usize,
) -> TestReport {
    let capturing = worker.session.capture_mode != crate::capture::Mode::No;
    if capturing {
        let _ = crate::capture::start(py);
    }
    let mut rep = run_phases(py, worker, item, next, state, wid);
    if capturing {
        if let Ok((out, err)) = crate::capture::stop(py) {
            rep.captured_out = out;
            rep.captured_err = err;
        }
    }
    rep
}

fn run_phases(
    py: Python<'_>,
    worker: &Arc<Worker>,
    item: &Arc<Item>,
    next: Option<&Arc<Item>>,
    state: &RunState,
    wid: usize,
) -> TestReport {
    let cfg: &ConfigData = &worker.session.cfg;
    let style = crate::traceback::Style {
        tb: &worker.session.tb_style,
        rootdir: &cfg.rootdir,
        showlocals: worker.session.showlocals,
        width: worker.session.term_width,
    };
    let mut rep = TestReport {
        index: item.index,
        nodeid: item.nodeid.clone(),
        relpath: item.relpath.clone(),
        outcome: Outcome::Passed,
        when: When::Call,
        duration: 0.0,
        setup_duration: 0.0,
        teardown_duration: 0.0,
        longrepr: String::new(),
        exconly: String::new(),
        reason: String::new(),
        location: item.location(),
        bench: None,
        worker: wid,
        captured_out: String::new(),
        captured_err: String::new(),
    };
    let t_start = Instant::now();
    let marks = item.marks_for_eval();
    let module = item.module.bind(py);
    let scope = crate::marks::MarkScope { module: Some(module) };

    // --- skip / xfail markers -------------------------------------------
    match evaluate_skip(py, &marks, scope) {
        Ok(SkipDecision::Skip(reason)) => {
            rep.outcome = Outcome::Skipped;
            rep.when = When::Setup;
            rep.reason = reason;
            rep.duration = t_start.elapsed().as_secs_f64();
            return rep;
        }
        Ok(SkipDecision::Run) => {}
        Err(e) => return fail_report(py, rep, &e, When::Setup, &style, state, t_start),
    }
    let xfail = match evaluate_xfail(py, &marks, scope, worker.session.xfail_strict) {
        Ok(x) => x,
        Err(e) => return fail_report(py, rep, &e, When::Setup, &style, state, t_start),
    };
    if let Some(spec) = &xfail {
        if !spec.run {
            rep.outcome = Outcome::XFailed;
            rep.when = When::Setup;
            rep.reason = format!("[NOTRUN] {}", spec.reason);
            rep.duration = t_start.elapsed().as_secs_f64();
            return rep;
        }
    }

    // --- setup ------------------------------------------------------------
    // Only the setup/teardown hooks need the Python-visible item, and most
    // suites have neither.
    let needs_py_item =
        !worker.session.hooks.runtest_setup.is_empty() || !worker.session.hooks.runtest_teardown.is_empty();
    let py_item = if needs_py_item {
        match Py::new(py, PyItem { item: item.clone(), cfg: worker.session.cfg.clone() }) {
            Ok(v) => Some(v.into_bound(py).into_any()),
            Err(e) => return fail_report(py, rep, &e, When::Setup, &style, state, t_start),
        }
    } else {
        None
    };
    for hook in &worker.session.hooks.runtest_setup {
        let arg = py_item.clone().expect("item wrapper");
        if let Err(e) = call_hook(py, hook.bind(py), &[("item", arg)]) {
            return finish_with_error(py, worker, next, rep, e, When::Setup, &style, state, t_start);
        }
    }
    worker.enter_item(py, item);
    // The test class instance must exist before fixtures run: class level
    // fixtures are bound to it, and `request.instance` exposes it.
    if let Some(cls) = &item.cls {
        // A `TestCase` is constructed with the name of the method it will run;
        // everything else takes no arguments.
        let built = match item.unittest {
            true => cls.bind(py).call1((item.originalname.as_str(),)),
            false => cls.bind(py).call0(),
        };
        match built {
            Ok(inst) => *worker.instance.lock().unwrap() = Some(inst.unbind()),
            Err(e) => return finish_with_error(py, worker, next, rep, e, When::Setup, &style, state, t_start),
        }
    }
    let kwargs = match worker.fill_arguments(py, item) {
        Ok(k) => k,
        Err(e) => return finish_with_error(py, worker, next, rep, e, When::Setup, &style, state, t_start),
    };
    rep.setup_duration = t_start.elapsed().as_secs_f64();

    // --- call --------------------------------------------------------------
    let t_call = Instant::now();
    let scoped_filters = crate::warnings::Scoped::enter(py, &item.filter_specs).unwrap_or(None);
    let call_result = invoke(py, worker, item, kwargs.bind(py));
    if let Some(scope) = scoped_filters {
        scope.exit(py);
    }
    let call_elapsed = t_call.elapsed().as_secs_f64();

    match call_result {
        Ok(_) => {
            if let Some(spec) = &xfail {
                if spec.strict {
                    rep.outcome = Outcome::Failed;
                    rep.longrepr = format!("[XPASS(strict)] {}", spec.reason);
                    state.record_failure();
                } else {
                    rep.outcome = Outcome::XPassed;
                    rep.reason = spec.reason.clone();
                }
            }
        }
        Err(e) => {
            classify(py, &mut rep, &e, xfail.as_ref(), &style, state);
        }
    }
    rep.duration = call_elapsed;

    // --- teardown -----------------------------------------------------------
    let t_teardown = Instant::now();
    for hook in &worker.session.hooks.runtest_teardown {
        let arg = py_item.clone().expect("item wrapper");
        if let Err(e) = call_hook(py, hook.bind(py), &[("item", arg)]) {
            if rep.outcome == Outcome::Passed {
                rep.outcome = Outcome::Error;
                rep.when = When::Teardown;
                rep.longrepr = crate::traceback::format_failure(py, &e, &style);
                rep.exconly = crate::traceback::short_description(py, &e, &rep.longrepr);
                state.record_failure();
            }
        }
    }
    let errors = worker.exit_item(py, next);
    if !errors.is_empty() && rep.outcome == Outcome::Passed {
        rep.outcome = Outcome::Error;
        rep.when = When::Teardown;
        rep.longrepr = errors.join("\n");
        rep.exconly = errors[0].lines().next().unwrap_or_default().to_string();
        state.record_failure();
    }
    *worker.instance.lock().unwrap() = None;
    rep.teardown_duration = t_teardown.elapsed().as_secs_f64();
    // Only benchmarks touch the shared result store; taking its lock for every
    // test would serialise the worker pool on a global mutex.
    if item.closure.names.iter().any(|n| n == "benchmark") {
        if let Some(b) = take_bench_result(worker, &item.name) {
            rep.bench = Some(b);
        }
    }
    rep
}

fn take_bench_result(worker: &Arc<Worker>, name: &str) -> Option<crate::bench::BenchResult> {
    let store = worker.session.bench_store.results.lock().unwrap();
    store.iter().rev().find(|r| r.name == name).cloned()
}

/// Invoke the test callable with the resolved arguments.
fn invoke<'py>(
    py: Python<'py>,
    worker: &Arc<Worker>,
    item: &Arc<Item>,
    kwargs: &Bound<'py, PyDict>,
) -> PyResult<Bound<'py, PyAny>> {
    if item.cls.is_none() {
        return item.func.bind(py).call((), Some(kwargs));
    }
    let instance = worker
        .instance
        .lock()
        .unwrap()
        .as_ref()
        .map(|i| i.clone_ref(py))
        .ok_or_else(|| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>("missing test instance"))?;
    let instance = instance.bind(py);
    if item.unittest {
        return crate::unittest::run_case(py, instance);
    }
    let bound = instance.getattr(item.originalname.as_str())?;
    bound.call((), Some(kwargs))
}

#[allow(clippy::too_many_arguments)]
fn classify(
    py: Python<'_>,
    rep: &mut TestReport,
    e: &PyErr,
    xfail: Option<&crate::marks::XfailSpec>,
    style: &crate::traceback::Style<'_>,
    state: &RunState,
) {
    if e.is_instance_of::<Skipped>(py) {
        rep.outcome = Outcome::Skipped;
        rep.reason = outcome_message(py, e);
        if let Some(loc) = raising_location(py, e, style.rootdir) {
            rep.location = loc;
        }
        return;
    }
    if e.is_instance_of::<XFailed>(py) {
        rep.outcome = Outcome::XFailed;
        rep.reason = outcome_message(py, e);
        return;
    }
    if e.is_instance_of::<Exit>(py) {
        rep.outcome = Outcome::Failed;
        rep.longrepr = outcome_message(py, e);
        state.stop.store(true, Ordering::Relaxed);
        *state.exit_message.lock().unwrap() = Some(outcome_message(py, e));
        return;
    }
    // Ctrl-C reaches whichever thread is running Python; stop the whole
    // session rather than recording it as one test's failure.
    if e.is_instance_of::<pyo3::exceptions::PyKeyboardInterrupt>(py) {
        rep.outcome = Outcome::Failed;
        rep.longrepr = "KeyboardInterrupt".to_string();
        rep.exconly = "KeyboardInterrupt".to_string();
        state.stop.store(true, Ordering::Relaxed);
        *state.exit_message.lock().unwrap() = Some("KeyboardInterrupt".to_string());
        return;
    }
    if let Some(spec) = xfail {
        let matches = match &spec.raises {
            None => true,
            Some(r) => e.value(py).is_instance(r.bind(py)).unwrap_or(false),
        };
        if matches {
            rep.outcome = Outcome::XFailed;
            rep.reason = spec.reason.clone();
            return;
        }
    }
    rep.outcome = Outcome::Failed;
    if e.is_instance_of::<Failed>(py) {
        let pytrace = e
            .value(py)
            .getattr(crate::outcomes::ATTR_PYTRACE)
            .ok()
            .map(|v| v.is_truthy().unwrap_or(true))
            .unwrap_or(true);
        if !pytrace {
            let message = outcome_message(py, e);
            rep.longrepr = message.clone();
            // The body loses its traceback, but the one-line summary still
            // names the exception, as `ExceptionInfo.exconly()` does.
            let name = e.get_type(py).name().map(|n| n.to_string()).unwrap_or_else(|_| "Failed".into());
            rep.exconly = format!("{name}: {message}");
            state.record_failure();
            return;
        }
    }
    rep.longrepr = crate::traceback::format_failure(py, e, style);
    rep.exconly = crate::traceback::short_description(py, e, &rep.longrepr);
    state.record_failure();
}

/// Where a `pytest.skip()` call happened, for the `-r s` summary.
fn raising_location(py: Python<'_>, e: &PyErr, rootdir: &std::path::Path) -> Option<String> {
    let mut tb = e.traceback(py)?.into_any();
    let mut best: Option<(String, usize)> = None;
    loop {
        let frame = tb.getattr("tb_frame").ok()?;
        let lineno: usize = tb.getattr("tb_lineno").ok()?.extract().ok()?;
        let filename: String = frame
            .getattr("f_code")
            .ok()?
            .getattr("co_filename")
            .ok()?
            .extract()
            .ok()?;
        if !filename.starts_with('<') {
            best = Some((filename, lineno));
        }
        match tb.getattr("tb_next") {
            Ok(n) if !n.is_none() => tb = n,
            _ => break,
        }
    }
    let (f, l) = best?;
    let display = std::path::Path::new(&f)
        .strip_prefix(rootdir)
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or(f);
    Some(format!("{display}:{l}"))
}

#[allow(clippy::too_many_arguments)]
fn fail_report(
    py: Python<'_>,
    mut rep: TestReport,
    e: &PyErr,
    when: When,
    style: &crate::traceback::Style<'_>,
    state: &RunState,
    t_start: Instant,
) -> TestReport {
    rep.when = when;
    if e.is_instance_of::<Skipped>(py) {
        rep.outcome = Outcome::Skipped;
        rep.reason = outcome_message(py, e);
        if let Some(loc) = raising_location(py, e, style.rootdir) {
            rep.location = loc;
        }
    } else {
        rep.outcome = Outcome::Error;
        rep.longrepr = crate::traceback::format_failure(py, e, style);
        rep.exconly = crate::traceback::short_description(py, e, &rep.longrepr);
        state.record_failure();
    }
    rep.duration = t_start.elapsed().as_secs_f64();
    rep
}

/// Setup failed: make sure whatever was already built gets torn down.
#[allow(clippy::too_many_arguments)]
fn finish_with_error(
    py: Python<'_>,
    worker: &Arc<Worker>,
    next: Option<&Arc<Item>>,
    rep: TestReport,
    e: PyErr,
    when: When,
    style: &crate::traceback::Style<'_>,
    state: &RunState,
    t_start: Instant,
) -> TestReport {
    let out = fail_report(py, rep, &e, when, style, state, t_start);
    let _ = worker.exit_item(py, next);
    out
}


