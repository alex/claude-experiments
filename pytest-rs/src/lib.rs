//! pytest-rs — a pytest-compatible test runner implemented in Rust with pyo3.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::{mpsc, Arc, Mutex, RwLock};
use std::time::Instant;

pub mod bench;
pub mod builtins;
pub mod cache;
pub mod capture;
pub mod collect;
pub mod config;
pub mod cov;
pub mod error;
pub mod expr;
pub mod fixtures;
pub mod ids;
pub mod junit;
pub mod marks;
pub mod outcomes;
pub mod pymod;
pub mod raises;
pub mod report;
pub mod runner;
pub mod runtime;
pub mod session;
pub mod shuffle;
pub mod threadsafety;
pub mod traceback;
pub mod warnings;

use crate::config::{split_ini, IniType, Parser, Value, INI_SPECS};
use crate::marks::KnownMarkers;
use crate::outcomes::Outcome;
use crate::report::{format_duration, outcome_summary, TestReport, Terminal, When};
use crate::runner::{plan, RunState};
use crate::runtime::SessionCache;
use crate::session::{ArgParser, Config, ConfigData, Session};

pub const EXIT_OK: i32 = 0;
pub const EXIT_TESTSFAILED: i32 = 1;
pub const EXIT_INTERRUPTED: i32 = 2;
pub const EXIT_INTERNALERROR: i32 = 3;
pub const EXIT_USAGEERROR: i32 = 4;
pub const EXIT_NOTESTSCOLLECTED: i32 = 5;

/// Entry point: run a full session and return the process exit code.
pub fn run_main(py: Python<'_>, raw_argv: Vec<String>) -> PyResult<i32> {
    match run_session(py, raw_argv) {
        Ok(code) => Ok(code),
        Err(error::Error::Usage(msg)) => {
            eprintln!("ERROR: {msg}");
            Ok(EXIT_USAGEERROR)
        }
        Err(error::Error::Py(e)) => {
            if e.is_instance_of::<outcomes::UsageErrorPy>(py) {
                eprintln!("ERROR: {}", e.value(py));
                return Ok(EXIT_USAGEERROR);
            }
            e.print(py);
            Ok(EXIT_INTERNALERROR)
        }
        Err(other) => {
            eprintln!("INTERNALERROR> {other}");
            Ok(EXIT_INTERNALERROR)
        }
    }
}

fn run_session(py: Python<'_>, raw_argv: Vec<String>) -> error::Result<i32> {
    let wall_start = Instant::now();
    let argv = config::preprocess_argv(&raw_argv);

    // --- phase 1: locate the config file ---------------------------------
    let bootstrap = Parser::new();
    let (pre_opts, pre_args) = bootstrap.parse(&argv, true)?;
    let explicit_ini = pre_opts.get("inifilename").and_then(|v| v.as_str().map(|s| s.to_string()));
    let explicit_root = pre_opts.get("rootdir").and_then(|v| v.as_str().map(|s| s.to_string()));
    let disc = config::discover(&pre_args, explicit_ini.as_deref(), explicit_root.as_deref());

    // --- ini values --------------------------------------------------------
    let mut ini: BTreeMap<String, Value> = BTreeMap::new();
    for spec in INI_SPECS {
        let raw = disc.raw.get(spec.name).cloned().unwrap_or_else(|| spec.default.to_string());
        ini.insert(spec.name.to_string(), split_ini(spec.ty, &raw));
    }
    for (k, v) in &disc.raw {
        if !ini.contains_key(k) {
            ini.insert(k.clone(), split_ini(IniType::Str, v));
        }
    }

    // --- splice addopts ----------------------------------------------------
    let addopts: Vec<String> = ini.get("addopts").map(|v| v.str_list()).unwrap_or_default();
    let mut full_argv: Vec<String> = Vec::with_capacity(addopts.len() + argv.len());
    full_argv.extend(config::preprocess_argv(&addopts));
    full_argv.extend(argv.iter().cloned());
    let (opts0, args0) = bootstrap.parse(&full_argv, true)?;

    let known_markers = Arc::new(RwLock::new(KnownMarkers::default()));
    {
        let mut guard = known_markers.write().unwrap();
        for line in ini.get("markers").map(|v| v.str_list()).unwrap_or_default() {
            let name = line.split(['(', ':']).next().unwrap_or(&line).trim().to_string();
            guard.names.insert(name);
        }
        guard.strict = opts0.get("strict_markers").map(|v| v.as_bool()).unwrap_or(false);
    }

    // The `pytest` module must exist before any conftest or test module runs.
    pymod::install(py, known_markers.clone()).map_err(error::Error::Py)?;

    let cfg = Arc::new(ConfigData {
        rootdir: disc.rootdir.clone(),
        invocation_dir: std::env::current_dir().unwrap_or_default(),
        inifile: disc.inifile.clone(),
        args: RwLock::new(full_argv.clone()),
        opts: RwLock::new(opts0.clone()),
        opt2dest: RwLock::new(bootstrap.opt2dest.clone()),
        ini: RwLock::new(ini.clone()),
        known_markers: known_markers.clone(),
        stash: Mutex::new(None),
        header_lines: Mutex::new(Vec::new()),
    });

    apply_pythonpath(py, &cfg).map_err(error::Error::Py)?;
    warnings::install_session_filters(py, &cfg.ini_list("filterwarnings"), &cfg.get("pythonwarnings").str_list())
        .map_err(error::Error::Py)?;

    // Coverage must be running before test modules are imported so that
    // module level statements are attributed correctly.
    let coverage = cov::Coverage::start(py, &cfg).map_err(error::Error::Py)?;

    // --- phase 2: conftest discovery and option registration ----------------
    let hostility = fixtures::HostilityContext {
        context_aware_warnings: threadsafety::warnings_are_context_aware(py),
        benchmarks_enabled: !bench::BenchOptions::from_config(&cfg).disabled,
    };
    let mut collector = collect::Collector::new(cfg.clone(), hostility);
    let targets = collector.resolve_targets(&args0);
    for t in &targets {
        let dir = if t.path.is_dir() {
            t.path.clone()
        } else {
            t.path.parent().map(|p| p.to_path_buf()).unwrap_or_default()
        };
        collector.load_conftests_for(py, &dir)?;
    }

    let extra_specs = Arc::new(Mutex::new(Vec::new()));
    let extra_inis = Arc::new(Mutex::new(Vec::new()));
    if !collector.hooks.addoption.is_empty() {
        let parser_obj = Py::new(py, ArgParser { specs: extra_specs.clone(), inis: extra_inis.clone() })
            .map_err(error::Error::Py)?
            .into_bound(py)
            .into_any();
        let hooks = std::mem::take(&mut collector.hooks.addoption);
        for hook in &hooks {
            runner::call_hook(
                py,
                hook.bind(py),
                &[("parser", parser_obj.clone()), ("pluginmanager", py.None().into_bound(py))],
            )
            .map_err(error::Error::Py)?;
        }
        collector.hooks.addoption = hooks;
    }

    let mut parser = Parser::new();
    for spec in extra_specs.lock().unwrap().iter() {
        parser.add(spec.clone());
    }
    for (name, ty, default) in extra_inis.lock().unwrap().iter() {
        ini.entry(name.clone()).or_insert_with(|| split_ini(*ty, default));
    }
    let (opts, args) = parser.parse(&full_argv, false)?;
    *cfg.opts.write().unwrap() = opts;
    *cfg.opt2dest.write().unwrap() = parser.opt2dest.clone();
    *cfg.ini.write().unwrap() = ini;
    known_markers.write().unwrap().strict = cfg.flag("strict_markers");

    if cfg.flag("help") {
        print_help(&parser);
        return Ok(EXIT_OK);
    }
    if cfg.get("version").as_int().unwrap_or(0) > 0 {
        println!("pytest-rs {} (pytest {} compatible)", pymod::VERSION, pymod::COMPAT_PYTEST_VERSION);
        return Ok(EXIT_OK);
    }

    // --- pytest_configure ---------------------------------------------------
    let config_obj = Py::new(py, Config { data: cfg.clone() })
        .map_err(error::Error::Py)?
        .into_bound(py)
        .into_any();
    for hook in &collector.hooks.configure {
        runner::call_hook(py, hook.bind(py), &[("config", config_obj.clone())]).map_err(error::Error::Py)?;
    }

    // --- collection ----------------------------------------------------------
    let collect_start = Instant::now();
    let targets = collector.resolve_targets(&args);
    let files = collector.discover_files(&targets);
    for (path, parts) in &files {
        collector.collect_file(py, path, parts)?;
        if py.check_signals().is_err() {
            eprintln!("\n!!!!!!!!!!!!!!!!!!! KeyboardInterrupt !!!!!!!!!!!!!!!!!!!!");
            return Ok(EXIT_INTERRUPTED);
        }
    }
    let collect_time = collect_start.elapsed().as_secs_f64();

    let mut items = std::mem::take(&mut collector.items);
    let total_collected = items.len();

    // --- selection ------------------------------------------------------------
    let mut deselected = 0usize;
    let keyword = cfg.str_opt("keyword");
    if !keyword.is_empty() {
        let e = expr::parse(&keyword, expr::Mode::Keyword)?;
        let before = items.len();
        items.retain(|it| {
            let f = |n: &str| {
                let needle = n.to_lowercase();
                it.keywords.iter().any(|k| k.to_lowercase().contains(&needle))
                    || it.nodeid.to_lowercase().contains(&needle)
            };
            e.eval(&expr::Matcher { name: &f, call: None })
        });
        deselected += before - items.len();
    }
    let markexpr = cfg.str_opt("markexpr");
    if !markexpr.is_empty() {
        let e = expr::parse(&markexpr, expr::Mode::Mark)?;
        let before = items.len();
        items.retain(|it| {
            let all = it.all_marks(true);
            let f = |n: &str| all.iter().any(|m| m.name == n);
            e.eval(&expr::Matcher { name: &f, call: None })
        });
        deselected += before - items.len();
    }
    let deselect_ids = cfg.get("deselect").str_list();
    if !deselect_ids.is_empty() {
        let before = items.len();
        items.retain(|it| !deselect_ids.iter().any(|d| it.nodeid == *d || it.nodeid.starts_with(&format!("{d}::"))));
        deselected += before - items.len();
    }
    if cfg.flag("benchmark_only") {
        let before = items.len();
        items.retain(|it| it.closure.names.iter().any(|n| n == "benchmark"));
        deselected += before - items.len();
    }
    if cfg.flag("benchmark_skip") {
        let before = items.len();
        items.retain(|it| !it.closure.names.iter().any(|n| n == "benchmark"));
        deselected += before - items.len();
    }

    // --- randomisation --------------------------------------------------------
    let randomly_enabled = !cfg
        .get("plugins")
        .str_list()
        .iter()
        .any(|p| p == "no:randomly" || p == "no:random_order");
    let disk_cache = cache::Cache::new(&cfg.rootdir, &cfg.ini_str("cache_dir"));
    let seed = match cfg.str_opt("randomly_seed").as_str() {
        "last" => disk_cache.last_seed().unwrap_or(0),
        other => shuffle::resolve_seed(other),
    };
    if randomly_enabled {
        if cfg.get("randomly_reorganize").as_bool() || matches!(cfg.get("randomly_reorganize"), Value::None) {
            shuffle::reorder(&mut items, seed);
        }
        disk_cache.store_seed(seed);
    } else {
        collect::group_by_module(&mut items);
    }
    let items: Vec<Arc<session::Item>> = items;

    // --- pytest_collection_modifyitems ----------------------------------------
    if !collector.hooks.collection_modifyitems.is_empty() {
        let pylist = PyList::empty(py);
        for it in &items {
            pylist
                .append(Py::new(py, session::PyItem { item: it.clone(), cfg: cfg.clone() }).map_err(error::Error::Py)?)
                .map_err(error::Error::Py)?;
        }
        for hook in &collector.hooks.collection_modifyitems {
            runner::call_hook(
                py,
                hook.bind(py),
                &[
                    ("session", py.None().into_bound(py)),
                    ("config", config_obj.clone()),
                    ("items", pylist.clone().into_any()),
                ],
            )
            .map_err(error::Error::Py)?;
        }
    }

    // --- worker count -----------------------------------------------------------
    let workers = resolve_workers(py, &cfg);
    let parallel = workers > 1;

    // `-s` is a shorthand for `--capture=no`.
    let capture_mode = if cfg.flag("capture_no") {
        capture::Mode::No
    } else {
        capture::Mode::parse(&cfg.str_opt("capture"))
    };
    capture::install(py, capture_mode).map_err(error::Error::Py)?;

    let bench_store = Arc::new(bench::BenchStore::default());
    let session = Arc::new(Session {
        cfg: cfg.clone(),
        registry: std::mem::take(&mut collector.registry),
        items,
        hooks: std::mem::take(&mut collector.hooks),
        workers,
        collect_errors: std::mem::take(&mut collector.errors),
        start_time: std::time::SystemTime::now(),
        seed,
        bench_store: bench_store.clone(),
        capture_mode,
        tb_style: cfg.str_opt("tbstyle"),
        showlocals: cfg.flag("showlocals"),
        term_width: report::terminal_width(),
    });

    // --- header ------------------------------------------------------------------
    // Anything Python wrote while importing conftest and test modules should
    // land before our header rather than after it.
    if let Ok(sys) = py.import("sys") {
        let _ = sys.getattr("stdout").and_then(|s| s.call_method0("flush"));
        let _ = sys.getattr("stderr").and_then(|s| s.call_method0("flush"));
    }
    let mut term = Terminal::new(&cfg, session.items.len(), parallel, capture_mode == capture::Mode::No);
    if !cfg.flag("no_header") {
        term.section("test session starts", '=', true);
        let pyver: String = py
            .import("platform")
            .and_then(|p| p.call_method0("python_version"))
            .and_then(|v| v.extract())
            .unwrap_or_else(|_| "?".into());
        let gil = py
            .import("sys")
            .and_then(|s| s.call_method0("_is_gil_enabled"))
            .and_then(|v| v.extract::<bool>())
            .unwrap_or(true);
        term.line(&format!(
            "platform {} -- Python {}{}, pytest-rs-{} (pytest {} compatible)",
            std::env::consts::OS,
            pyver,
            if gil { "" } else { " free-threaded" },
            pymod::VERSION,
            pymod::COMPAT_PYTEST_VERSION,
        ));
        term.line(&format!("rootdir: {}", cfg.rootdir.display()));
        if let Some(f) = &cfg.inifile {
            let rel = f.strip_prefix(&cfg.rootdir).unwrap_or(f);
            term.line(&format!("configfile: {}", rel.display()));
        }
        if randomly_enabled {
            term.line(&format!("Using --randomly-seed={seed}"));
        }
        term.line(&format!("workers: {workers} thread{}", if workers == 1 { "" } else { "s" }));
        for hook in &session.hooks.report_header {
            let rootpath = session::path_obj(py, &cfg.rootdir).map_err(error::Error::Py)?;
            if let Ok(v) = runner::call_hook(
                py,
                hook.bind(py),
                &[
                    ("config", config_obj.clone()),
                    ("start_path", rootpath.bind(py).clone()),
                    ("startdir", rootpath.bind(py).clone()),
                ],
            ) {
                for line in flatten_strings(&v) {
                    term.line(&line);
                }
            }
        }
    }

    for hook in &session.hooks.sessionstart {
        let _ = runner::call_hook(py, hook.bind(py), &[("session", py.None().into_bound(py))]);
    }

    let plural = if session.items.len() == 1 { "item" } else { "items" };
    if deselected > 0 {
        term.line(&format!(
            "collected {total_collected} {plural} / {deselected} deselected / {} selected",
            session.items.len()
        ));
    } else {
        term.line(&format!("collected {} {plural}", session.items.len()));
    }
    if cfg.verbosity() >= 1 {
        term.line(&format!("collection took {collect_time:.2}s"));
    }
    term.line("");
    term.flush();

    // --- collection errors ---------------------------------------------------------
    if !session.collect_errors.is_empty() {
        term.section("ERRORS", '=', true);
        for (path, msg) in &session.collect_errors {
            term.section(&format!("ERROR collecting {path}"), '_', false);
            term.line(msg);
        }
        if !cfg.flag("continue_on_collection_errors") {
            let n = session.collect_errors.len();
            term.section(
                &format!("{n} error{} during collection", if n == 1 { "" } else { "s" }),
                '!',
                true,
            );
            term.flush();
            return Ok(EXIT_INTERRUPTED);
        }
    }

    if cfg.flag("collectonly") {
        for it in &session.items {
            term.line(&it.nodeid);
        }
        term.line("");
        let n = session.items.len();
        term.line(&format!("{n} test{} collected in {collect_time:.2}s", if n == 1 { "" } else { "s" }));
        let json_path = cfg.str_opt("co_json");
        if !json_path.is_empty() {
            let body: Vec<String> = session.items.iter().map(|i| format!("{:?}", i.nodeid)).collect();
            let _ = std::fs::write(&json_path, format!("[{}]", body.join(",")));
        }
        term.flush();
        return Ok(if session.items.is_empty() { EXIT_NOTESTSCOLLECTED } else { EXIT_OK });
    }

    if session.items.is_empty() {
        term.section("no tests ran", '=', true);
        term.flush();
        return Ok(EXIT_NOTESTSCOLLECTED);
    }

    // --- run ------------------------------------------------------------------------
    let maxfail = if cfg.flag("exitfirst") {
        1
    } else {
        cfg.get("maxfail").as_int().unwrap_or(0).max(0) as usize
    };
    let state = Arc::new(RunState {
        failures: std::sync::atomic::AtomicUsize::new(0),
        stop: std::sync::atomic::AtomicBool::new(false),
        maxfail,
        exit_message: Mutex::new(None),
    });
    let session_cache = Arc::new(SessionCache::default());
    let recorded = disk_cache.durations();
    let the_plan = plan(&session, parallel, &recorded);
    if cfg.verbosity() >= 1 {
        term.line(&format!(
            "scheduling: {} parallel group(s), {} serialised test(s){}",
            the_plan.groups.len(),
            the_plan.serial.len(),
            if recorded.is_empty() { "" } else { ", ordered by recorded durations" }
        ));
    }
    if cfg.verbosity() >= 2 && !the_plan.serial.is_empty() {
        let mut by_reason: BTreeMap<String, usize> = BTreeMap::new();
        for &i in &the_plan.serial {
            let reason = session.items[i].hostile_reason.clone().unwrap_or_else(|| "unknown".into());
            *by_reason.entry(reason).or_insert(0) += 1;
        }
        for (reason, n) in by_reason {
            term.line(&format!("  serialised: {n:>4} test(s) — {reason}"));
        }
    }
    if randomly_enabled && cfg.get("randomly_reset_seed").as_bool() {
        let _ = shuffle::reseed_python(py, seed);
    }

    let (tx, rx) = mpsc::channel::<TestReport>();
    let mut reports: Vec<TestReport> = Vec::with_capacity(session.items.len());
    let mut timings = runner::PhaseTimings { parallel: 0.0, serial: 0.0 };
    let run_start = Instant::now();
    // The terminal moves into the receiving thread so progress is written as
    // results land rather than being buffered until the run ends.  Reporting
    // needs no interpreter state, so this happens with the GIL released.
    let mut term_holder = Some(term);
    {
        let session2 = session.clone();
        let cache2 = session_cache.clone();
        let state2 = state.clone();
        py.detach(|| {
            let mut sink = term_holder.take().expect("terminal");
            let receiver = std::thread::spawn(move || {
                let mut out = Vec::new();
                while let Ok(r) = rx.recv() {
                    sink.report(&r);
                    sink.flush();
                    out.push(r);
                }
                (sink, out)
            });
            timings = runner::execute(session2, cache2, the_plan, state2, tx, workers);
            match receiver.join() {
                Ok((sink, reps)) => {
                    term_holder = Some(sink);
                    reports = reps;
                }
                Err(_) => reports = Vec::new(),
            }
        });
    }
    let mut term = term_holder.expect("terminal returned");
    let run_time = run_start.elapsed().as_secs_f64();
    disk_cache.store_durations(
        reports
            .iter()
            .map(|r| (r.nodeid.clone(), r.duration + r.setup_duration + r.teardown_duration)),
    );

    term.finish_progress();
    // Summaries are emitted in collection order so they read the same way
    // however the scheduler interleaved the work.
    reports.sort_by_key(|r| r.index);

    // --- teardown -----------------------------------------------------------------
    for e in session_cache.teardown(py) {
        term.line(&format!("ERROR during session teardown: {e}"));
    }
    for hook in &session.hooks.sessionfinish {
        let _ = runner::call_hook(py, hook.bind(py), &[("session", py.None().into_bound(py))]);
    }

    // --- summaries -------------------------------------------------------------------
    let failed: Vec<&TestReport> = reports.iter().filter(|r| r.outcome == Outcome::Failed).collect();
    let errored: Vec<&TestReport> = reports.iter().filter(|r| r.outcome == Outcome::Error).collect();
    if !cfg.flag("no_summary") && cfg.str_opt("tbstyle") != "no" {
        if !failed.is_empty() {
            term.section("FAILURES", '=', true);
            for r in &failed {
                term.section(&failure_headline(&r.nodeid), '_', false);
                term.line(r.longrepr.trim_end());
                emit_captured(&mut term, r);
                term.line("");
            }
        }
        if !errored.is_empty() {
            term.section("ERRORS", '=', true);
            for r in &errored {
                term.section(
                    &format!("ERROR at {} of {}", r.when.as_str(), failure_headline(&r.nodeid)),
                    '_',
                    false,
                );
                term.line(r.longrepr.trim_end());
                emit_captured(&mut term, r);
                term.line("");
            }
        }
    }

    let xmlpath = cfg.str_opt("xmlpath");
    if !xmlpath.is_empty() {
        let xml = junit::render(&reports, run_time, "pytest");
        let target = std::path::Path::new(&xmlpath);
        if let Some(parent) = target.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        if let Err(e) = std::fs::write(target, xml) {
            term.line(&format!("could not write {xmlpath}: {e}"));
        } else if cfg.verbosity() >= 1 {
            term.line(&format!("generated xml file: {xmlpath}"));
        }
    }

    emit_short_summary(&mut term, &cfg, &reports);
    emit_durations(&mut term, &cfg, &reports);
    emit_bench_table(&mut term, &cfg, &bench_store);

    for hook in &session.hooks.terminal_summary {
        let _ = runner::call_hook(
            py,
            hook.bind(py),
            &[("config", config_obj.clone()), ("terminalreporter", py.None().into_bound(py))],
        );
    }

    let mut cov_failed = false;
    if let Some(c) = &coverage {
        match c.finish(py, &mut term) {
            Ok(f) => cov_failed = f,
            Err(e) => term.line(&format!("coverage error: {e}")),
        }
    }

    for hook in &session.hooks.unconfigure {
        let _ = runner::call_hook(py, hook.bind(py), &[("config", config_obj.clone())]);
    }

    // --- final line ---------------------------------------------------------------------
    let mut counts: Vec<(Outcome, usize)> = Vec::new();
    for o in [
        Outcome::Passed,
        Outcome::Failed,
        Outcome::Skipped,
        Outcome::XFailed,
        Outcome::XPassed,
        Outcome::Error,
    ] {
        let n = reports.iter().filter(|r| r.outcome == o).count();
        if n > 0 {
            counts.push((o, n));
        }
    }
    let mut parts: Vec<String> = outcome_summary(&counts)
        .into_iter()
        .map(|(text, o)| match o {
            Outcome::Passed => term.colors.green(&text),
            Outcome::Failed | Outcome::Error => term.colors.red(&text),
            _ => term.colors.yellow(&text),
        })
        .collect();
    if deselected > 0 {
        parts.push(format!("{deselected} deselected"));
    }
    let total_wall = wall_start.elapsed().as_secs_f64();
    let summary = format!("{} in {}", parts.join(", "), format_duration(total_wall));
    let any_failed = !failed.is_empty() || !errored.is_empty();
    term.section(&summary, '=', true);
    if cfg.verbosity() >= 1 {
        term.line(&format!(
            "(collection {collect_time:.2}s, parallel phase {:.2}s, serial phase {:.2}s, execution {run_time:.2}s, total {total_wall:.2}s)",
            timings.parallel, timings.serial
        ));
    }
    term.flush();

    if state.should_stop() && maxfail > 0 {
        term.section(&format!("stopping after {maxfail} failures"), '!', true);
    }
    let exit_msg = state.exit_message.lock().unwrap().clone();
    if let Some(msg) = exit_msg {
        term.section(&msg, '!', true);
        term.flush();
        return Ok(EXIT_INTERRUPTED);
    }
    if cov_failed {
        return Ok(EXIT_TESTSFAILED);
    }
    Ok(if any_failed { EXIT_TESTSFAILED } else { EXIT_OK })
}

/// Replay whatever the failing test wrote to stdout/stderr.
fn emit_captured(term: &mut Terminal, r: &TestReport) {
    if !r.captured_out.is_empty() {
        term.section(&format!("Captured stdout {}", r.when.as_str()), '-', false);
        term.line(r.captured_out.trim_end());
    }
    if !r.captured_err.is_empty() {
        term.section(&format!("Captured stderr {}", r.when.as_str()), '-', false);
        term.line(r.captured_err.trim_end());
    }
}

/// pytest titles each failure block with the dotted test path, without the file.
fn failure_headline(nodeid: &str) -> String {
    match nodeid.split_once("::") {
        Some((_, rest)) => rest.replace("::", "."),
        None => nodeid.to_string(),
    }
}

fn emit_short_summary(term: &mut Terminal, cfg: &ConfigData, reports: &[TestReport]) {
    let chars = cfg.str_opt("reportchars");
    if chars.is_empty() || chars == "N" {
        return;
    }
    let want = |o: Outcome| chars.contains('a') || chars.contains('A') || chars.contains(o.report_char());
    let mut lines: Vec<String> = Vec::new();

    if want(Outcome::Skipped) {
        let mut groups: BTreeMap<(String, String), usize> = BTreeMap::new();
        for r in reports.iter().filter(|r| r.outcome == Outcome::Skipped) {
            *groups.entry((r.location.clone(), r.reason.clone())).or_insert(0) += 1;
        }
        for ((loc, reason), n) in groups {
            lines.push(format!("SKIPPED [{n}] {loc}: {reason}"));
        }
    }
    if want(Outcome::XFailed) {
        for r in reports.iter().filter(|r| r.outcome == Outcome::XFailed) {
            lines.push(format!("XFAIL {} - {}", r.nodeid, r.reason));
        }
    }
    if want(Outcome::XPassed) {
        for r in reports.iter().filter(|r| r.outcome == Outcome::XPassed) {
            lines.push(format!("XPASS {} - {}", r.nodeid, r.reason));
        }
    }
    if want(Outcome::Failed) {
        for r in reports.iter().filter(|r| r.outcome == Outcome::Failed) {
            lines.push(format!("FAILED {} - {}", r.nodeid, r.exconly));
        }
    }
    if want(Outcome::Error) {
        for r in reports.iter().filter(|r| r.outcome == Outcome::Error) {
            lines.push(format!("ERROR {} - {}", r.nodeid, r.exconly));
        }
    }
    if chars.contains('p') || chars.contains('P') {
        for r in reports.iter().filter(|r| r.outcome == Outcome::Passed) {
            lines.push(format!("PASSED {}", r.nodeid));
        }
    }
    if lines.is_empty() {
        return;
    }
    term.section("short test summary info", '=', true);
    for l in lines {
        term.line(&l);
    }
}

fn emit_durations(term: &mut Terminal, cfg: &ConfigData, reports: &[TestReport]) {
    let n = cfg.get("durations").as_int().unwrap_or(-1);
    if n < 0 {
        return;
    }
    let min = cfg.get("durations_min").as_f64().unwrap_or(0.005);
    let mut rows: Vec<(f64, &'static str, &TestReport)> = Vec::new();
    for r in reports {
        rows.push((r.duration, "call", r));
        if r.setup_duration > 0.0 {
            rows.push((r.setup_duration, "setup", r));
        }
        if r.teardown_duration > 0.0 {
            rows.push((r.teardown_duration, "teardown", r));
        }
    }
    rows.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    let rows: Vec<_> = rows.into_iter().filter(|(d, _, _)| *d >= min).collect();
    let take = if n == 0 { rows.len() } else { (n as usize).min(rows.len()) };
    if take == 0 {
        return;
    }
    term.section(&format!("slowest {take} durations"), '=', true);
    for (d, when, r) in rows.iter().take(take) {
        term.line(&format!("{d:.2}s {when:<9}{}", r.nodeid));
    }
}

fn emit_bench_table(term: &mut Terminal, cfg: &ConfigData, store: &Arc<bench::BenchStore>) {
    let results = store.results.lock().unwrap();
    if results.is_empty() {
        return;
    }
    let all_times: Vec<f64> = results.iter().flat_map(|r| r.times.clone()).collect();
    let (unit, factor) = bench::scale(&all_times);

    let mut sorted: Vec<&bench::BenchResult> = results.iter().collect();
    let key = cfg.str_opt("benchmark_sort");
    sorted.sort_by(|a, b| {
        let (x, y) = match key.as_str() {
            "max" => (a.max(), b.max()),
            "mean" => (a.mean(), b.mean()),
            "stddev" => (a.stddev(), b.stddev()),
            "median" => (a.median(), b.median()),
            _ => (a.min(), b.min()),
        };
        x.partial_cmp(&y).unwrap_or(std::cmp::Ordering::Equal)
    });

    // Lay the table out to fit its widest entry rather than a fixed guess.
    let cells: Vec<(String, [String; 6])> = sorted
        .iter()
        .map(|r| {
            (
                r.name.clone(),
                [
                    format!("{:.4}", r.min() * factor),
                    format!("{:.4}", r.max() * factor),
                    format!("{:.4}", r.mean() * factor),
                    format!("{:.4}", r.stddev() * factor),
                    format!("{:.4}", r.median() * factor),
                    r.rounds.to_string(),
                ],
            )
        })
        .collect();
    let headers = ["Min", "Max", "Mean", "StdDev", "Median", "Rounds"];
    let name_header = format!("Name (time in {unit})");
    let name_width = cells
        .iter()
        .map(|(n, _)| n.len())
        .chain(std::iter::once(name_header.len()))
        .max()
        .unwrap_or(20)
        .min(60);
    let widths: Vec<usize> = (0..headers.len())
        .map(|i| {
            cells
                .iter()
                .map(|(_, c)| c[i].len())
                .chain(std::iter::once(headers[i].len()))
                .max()
                .unwrap_or(8)
        })
        .collect();
    let total_width: usize = name_width + 2 + widths.iter().map(|w| w + 2).sum::<usize>();

    term.section(&format!("benchmark: {} tests", results.len()), '-', false);
    let mut header = format!("{name_header:<name_width$}");
    for (h, w) in headers.iter().zip(&widths) {
        header.push_str(&format!("  {h:>w$}"));
    }
    term.line(&header);
    term.line(&"-".repeat(total_width));
    for (name, values) in &cells {
        let mut truncated = name.clone();
        if truncated.len() > name_width {
            truncated.truncate(name_width.saturating_sub(1));
            truncated.push('~');
        }
        let mut row = format!("{truncated:<name_width$}");
        for (v, w) in values.iter().zip(&widths) {
            row.push_str(&format!("  {v:>w$}"));
        }
        term.line(&row);
    }
    term.line(&"-".repeat(total_width));
    term.line("Legend: times are per-call; Rounds is how many calls were timed.");
}

fn resolve_workers(py: Python<'_>, cfg: &ConfigData) -> usize {
    if cfg.flag("no_parallel") {
        return 1;
    }
    let raw = cfg.str_opt("numprocesses");
    let cpus = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let requested = match raw.as_str() {
        "" => 1,
        "auto" | "logical" => {
            // Threads only buy wall-clock time when the interpreter can run
            // them concurrently, or when the workload spends its time in
            // GIL-releasing native code.  Default to the CPU count on
            // free-threaded builds and stay serial otherwise.
            let gil = py
                .import("sys")
                .and_then(|s| s.call_method0("_is_gil_enabled"))
                .and_then(|v| v.extract::<bool>())
                .unwrap_or(true);
            if gil {
                1
            } else {
                cpus
            }
        }
        other => other.parse::<usize>().unwrap_or(1),
    };
    requested.clamp(1, 256)
}

fn apply_pythonpath(py: Python<'_>, cfg: &ConfigData) -> PyResult<()> {
    let paths = cfg.ini_list("pythonpath");
    if paths.is_empty() {
        return Ok(());
    }
    let sys = py.import("sys")?;
    let sys_path = sys.getattr("path")?;
    for p in paths.iter().rev() {
        let abs = cfg.rootdir.join(p);
        sys_path.call_method1("insert", (0, abs.to_string_lossy().as_ref()))?;
    }
    Ok(())
}

fn flatten_strings(v: &Bound<'_, PyAny>) -> Vec<String> {
    if v.is_none() {
        return Vec::new();
    }
    if let Ok(s) = v.extract::<String>() {
        return s.lines().map(|l| l.to_string()).collect();
    }
    let mut out = Vec::new();
    if let Ok(iter) = v.try_iter() {
        for item in iter.flatten() {
            out.extend(flatten_strings(&item));
        }
    }
    out
}

fn print_help(parser: &Parser) {
    println!("usage: pytest-rs [options] [file_or_dir] [file_or_dir] [...]\n");
    println!("A pytest-compatible test runner implemented in Rust.\n");
    println!("options:");
    let mut seen = std::collections::BTreeSet::new();
    for spec in &parser.specs {
        if spec.help.is_empty() || !seen.insert(spec.dest.clone()) {
            continue;
        }
        println!("  {:<32} {}", spec.names.join(", "), spec.help);
    }
}

#[pyfunction]
#[pyo3(name = "main")]
fn py_main(py: Python<'_>, argv: Vec<String>) -> PyResult<i32> {
    run_main(py, argv)
}

#[pyfunction]
fn version() -> &'static str {
    pymod::VERSION
}

#[pymodule]
fn _pytest_rs(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(py_main, m)?)?;
    m.add_function(wrap_pyfunction!(version, m)?)?;
    m.add("__version__", pymod::VERSION)?;
    Ok(())
}

#[allow(dead_code)]
fn _unused(py: Python<'_>) {
    let _ = PyDict::new(py);
    let _ = Path::new("");
    let _: Option<When> = None;
}
