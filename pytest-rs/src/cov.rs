//! Coverage measurement — pytest-cov's behaviour, built in.
//!
//! We drive `coverage.py` directly rather than going through a plugin: start
//! before any test module is imported so module level statements are counted,
//! stop after the last test, then emit whichever reports were requested.

use pyo3::prelude::*;
use pyo3::types::PyDict;

use crate::session::ConfigData;

pub struct Coverage {
    obj: Py<PyAny>,
    reports: Vec<String>,
    fail_under: Option<f64>,
}

impl Coverage {
    /// Returns `Ok(None)` when coverage was not requested.
    pub fn start(py: Python<'_>, cfg: &ConfigData) -> PyResult<Option<Coverage>> {
        if cfg.flag("no_cov") {
            return Ok(None);
        }
        let sources: Vec<String> = cfg
            .get("cov_source")
            .str_list()
            .into_iter()
            .filter(|s| !s.is_empty())
            .collect();
        let requested = !cfg.get("cov_source").as_list().is_empty();
        if !requested {
            return Ok(None);
        }
        let coverage = match py.import("coverage") {
            Ok(c) => c,
            Err(_) => {
                eprintln!("pytest-rs: --cov requested but the `coverage` package is not installed");
                return Ok(None);
            }
        };
        let kwargs = PyDict::new(py);
        if !sources.is_empty() {
            kwargs.set_item("source", sources)?;
        }
        if cfg.flag("cov_branch") {
            kwargs.set_item("branch", true)?;
        }
        let config_file = cfg.str_opt("cov_config");
        if !config_file.is_empty() && std::path::Path::new(&config_file).exists() {
            kwargs.set_item("config_file", config_file)?;
        }
        if let Some(ctx) = Some(cfg.str_opt("cov_context")).filter(|s| !s.is_empty()) {
            kwargs.set_item("context", ctx)?;
        }
        // Coverage's thread tracer is installed for threads started after
        // `start()`, which is exactly how our worker pool is created.
        kwargs.set_item("concurrency", vec!["thread"])?;
        let cov = coverage.getattr("Coverage")?.call((), Some(&kwargs))?;
        if cfg.flag("cov_append") {
            cov.call_method0("load")?;
        }
        cov.call_method0("start")?;
        let mut reports: Vec<String> = cfg.get("cov_report").str_list();
        if reports.is_empty() {
            reports.push("term".to_string());
        }
        Ok(Some(Coverage {
            obj: cov.unbind(),
            reports,
            fail_under: cfg.get("cov_fail_under").as_f64(),
        }))
    }

    /// Stop measuring and emit the reports.  Returns `true` when
    /// `--cov-fail-under` was not met.
    pub fn finish(&self, py: Python<'_>, out: &mut crate::report::Terminal) -> PyResult<bool> {
        let cov = self.obj.bind(py);
        cov.call_method0("stop")?;
        cov.call_method0("save")?;
        let mut total: Option<f64> = None;
        for spec in &self.reports {
            let (kind, dest) = match spec.split_once(':') {
                Some((k, d)) => (k, Some(d)),
                None => (spec.as_str(), None),
            };
            let kwargs = PyDict::new(py);
            match kind {
                "term" | "term-missing" | "" => {
                    if kind == "term-missing" {
                        kwargs.set_item("show_missing", true)?;
                    }
                    let io = py.import("io")?;
                    let buf = io.getattr("StringIO")?.call0()?;
                    kwargs.set_item("file", &buf)?;
                    let pct: f64 = cov.call_method("report", (), Some(&kwargs))?.extract()?;
                    total = Some(pct);
                    out.section("coverage", '-', false);
                    let text: String = buf.call_method0("getvalue")?.extract()?;
                    for line in text.lines() {
                        out.line(line);
                    }
                }
                "html" => {
                    if let Some(d) = dest {
                        kwargs.set_item("directory", d)?;
                    }
                    let pct: f64 = cov.call_method("html_report", (), Some(&kwargs))?.extract()?;
                    total.get_or_insert(pct);
                }
                "xml" => {
                    if let Some(d) = dest {
                        kwargs.set_item("outfile", d)?;
                    }
                    let pct: f64 = cov.call_method("xml_report", (), Some(&kwargs))?.extract()?;
                    total.get_or_insert(pct);
                }
                "json" => {
                    if let Some(d) = dest {
                        kwargs.set_item("outfile", d)?;
                    }
                    let pct: f64 = cov.call_method("json_report", (), Some(&kwargs))?.extract()?;
                    total.get_or_insert(pct);
                }
                "annotate" => {
                    if let Some(d) = dest {
                        kwargs.set_item("directory", d)?;
                    }
                    cov.call_method("annotate", (), Some(&kwargs))?;
                }
                other => {
                    out.line(&format!("pytest-rs: unknown coverage report type {other:?}"));
                }
            }
        }
        if let (Some(limit), Some(pct)) = (self.fail_under, total) {
            if pct < limit {
                out.line(&format!("FAIL Required test coverage of {limit}% not reached. Total coverage: {pct:.2}%"));
                return Ok(true);
            }
        }
        Ok(false)
    }
}
