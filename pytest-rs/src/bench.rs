//! The `benchmark` fixture — pytest-benchmark's behaviour, built in.
//!
//! Calibration mirrors pytest-benchmark: grow the per-round iteration count
//! until a round takes at least `--benchmark-min-time`, then run rounds until
//! either `--benchmark-max-time` elapses or `--benchmark-min-rounds` rounds have
//! completed.  Benchmarked tests are always scheduled on the serial path so
//! that timings are not perturbed by other workers.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyTuple};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::runtime::Worker;
use crate::session::Item;

#[derive(Clone, Debug)]
pub struct BenchResult {
    pub name: String,
    pub group: Option<String>,
    pub rounds: usize,
    pub iterations: usize,
    pub times: Vec<f64>,
}

impl BenchResult {
    pub fn min(&self) -> f64 {
        self.times.iter().copied().fold(f64::INFINITY, f64::min)
    }
    pub fn max(&self) -> f64 {
        self.times.iter().copied().fold(f64::NEG_INFINITY, f64::max)
    }
    pub fn mean(&self) -> f64 {
        if self.times.is_empty() {
            return 0.0;
        }
        self.times.iter().sum::<f64>() / self.times.len() as f64
    }
    pub fn stddev(&self) -> f64 {
        if self.times.len() < 2 {
            return 0.0;
        }
        let m = self.mean();
        let var = self.times.iter().map(|t| (t - m) * (t - m)).sum::<f64>() / (self.times.len() - 1) as f64;
        var.sqrt()
    }
    pub fn median(&self) -> f64 {
        if self.times.is_empty() {
            return 0.0;
        }
        let mut s = self.times.clone();
        s.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let n = s.len();
        if n % 2 == 1 {
            s[n / 2]
        } else {
            (s[n / 2 - 1] + s[n / 2]) / 2.0
        }
    }
    pub fn iqr(&self) -> f64 {
        if self.times.len() < 4 {
            return 0.0;
        }
        let mut s = self.times.clone();
        s.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let q1 = s[s.len() / 4];
        let q3 = s[s.len() * 3 / 4];
        q3 - q1
    }
    pub fn ops(&self) -> f64 {
        let m = self.mean();
        if m > 0.0 {
            1.0 / m
        } else {
            0.0
        }
    }
    /// `outliers` in pytest-benchmark's "N;M" form (mild; severe).
    pub fn outliers(&self) -> (usize, usize) {
        let q = self.iqr();
        if q == 0.0 {
            return (0, 0);
        }
        let mut s = self.times.clone();
        s.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let q1 = s[s.len() / 4];
        let q3 = s[s.len() * 3 / 4];
        let mut mild = 0;
        let mut severe = 0;
        for t in &self.times {
            if *t < q1 - 3.0 * q || *t > q3 + 3.0 * q {
                severe += 1;
            } else if *t < q1 - 1.5 * q || *t > q3 + 1.5 * q {
                mild += 1;
            }
        }
        (mild, severe)
    }
}

/// Global collection point for benchmark results.
#[derive(Default)]
pub struct BenchStore {
    pub results: Mutex<Vec<BenchResult>>,
}

pub struct BenchOptions {
    pub disabled: bool,
    pub skip: bool,
    pub only: bool,
    pub min_rounds: usize,
    pub min_time: f64,
    pub max_time: f64,
    pub warmup: bool,
    pub calibration_precision: usize,
    pub disable_gc: bool,
}

impl BenchOptions {
    pub fn from_config(cfg: &crate::session::ConfigData) -> Self {
        let mut disabled = cfg.flag("benchmark_disable");
        if cfg.flag("benchmark_enable") || cfg.flag("benchmark_only") {
            disabled = false;
        }
        let warmup = match cfg.str_opt("benchmark_warmup").as_str() {
            "on" | "true" | "yes" => true,
            "off" | "false" | "no" => false,
            // "auto": warm up only on PyPy, matching pytest-benchmark.
            _ => cfg!(any()) || std::env::var("PYTHONPYPY").is_ok(),
        };
        BenchOptions {
            disabled,
            skip: cfg.flag("benchmark_skip"),
            only: cfg.flag("benchmark_only"),
            min_rounds: cfg.get("benchmark_min_rounds").as_int().unwrap_or(5).max(1) as usize,
            min_time: cfg.get("benchmark_min_time").as_f64().unwrap_or(0.000005),
            max_time: cfg.get("benchmark_max_time").as_f64().unwrap_or(1.0),
            warmup,
            calibration_precision: cfg.get("benchmark_calibration_precision").as_int().unwrap_or(10) as usize,
            disable_gc: cfg.flag("benchmark_disable_gc"),
        }
    }
}

/// The object bound to the `benchmark` fixture argument.
#[pyclass(module = "pytest", name = "BenchmarkFixture")]
pub struct BenchmarkFixture {
    name: String,
    group: Option<String>,
    disabled: bool,
    min_rounds: usize,
    min_time: f64,
    max_time: f64,
    warmup: bool,
    disable_gc: bool,
    store: Arc<BenchStore>,
    #[pyo3(get, set)]
    extra_info: Py<PyDict>,
    used: Mutex<bool>,
}

#[pymethods]
impl BenchmarkFixture {
    #[pyo3(signature = (function_to_benchmark, *args, **kwargs))]
    fn __call__<'py>(
        &self,
        py: Python<'py>,
        function_to_benchmark: Bound<'py, PyAny>,
        args: &Bound<'py, PyTuple>,
        kwargs: Option<&Bound<'py, PyDict>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        *self.used.lock().unwrap() = true;
        if self.disabled {
            return function_to_benchmark.call(args, kwargs);
        }
        self.run(py, &function_to_benchmark, args, kwargs)
    }

    /// pytest-benchmark's `pedantic` entry point.
    #[pyo3(signature = (target, args=None, kwargs=None, setup=None, rounds=5, iterations=1, warmup_rounds=0))]
    #[allow(clippy::too_many_arguments)]
    fn pedantic<'py>(
        &self,
        py: Python<'py>,
        target: Bound<'py, PyAny>,
        args: Option<Bound<'py, PyTuple>>,
        kwargs: Option<Bound<'py, PyDict>>,
        setup: Option<Bound<'py, PyAny>>,
        rounds: usize,
        iterations: usize,
        warmup_rounds: usize,
    ) -> PyResult<Bound<'py, PyAny>> {
        *self.used.lock().unwrap() = true;
        let args = args.unwrap_or_else(|| PyTuple::empty(py));
        let mut last = target.call(&args, kwargs.as_ref())?;
        if self.disabled {
            return Ok(last);
        }
        for _ in 0..warmup_rounds {
            if let Some(s) = &setup {
                s.call0()?;
            }
            last = target.call(&args, kwargs.as_ref())?;
        }
        let mut times = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            if let Some(s) = &setup {
                s.call0()?;
            }
            let start = Instant::now();
            for _ in 0..iterations {
                last = target.call(&args, kwargs.as_ref())?;
            }
            times.push(start.elapsed().as_secs_f64() / iterations as f64);
        }
        self.store.results.lock().unwrap().push(BenchResult {
            name: self.name.clone(),
            group: self.group.clone(),
            rounds,
            iterations,
            times,
        });
        Ok(last)
    }

    #[getter]
    fn stats(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        let results = self.store.results.lock().unwrap();
        let Some(r) = results.iter().rev().find(|r| r.name == self.name) else {
            return Ok(py.None());
        };
        let d = PyDict::new(py);
        d.set_item("min", r.min())?;
        d.set_item("max", r.max())?;
        d.set_item("mean", r.mean())?;
        d.set_item("stddev", r.stddev())?;
        d.set_item("median", r.median())?;
        d.set_item("rounds", r.rounds)?;
        d.set_item("iterations", r.iterations)?;
        Ok(d.into_any().unbind())
    }

    #[getter]
    fn group(&self) -> Option<String> {
        self.group.clone()
    }
}

impl BenchmarkFixture {
    fn run<'py>(
        &self,
        py: Python<'py>,
        func: &Bound<'py, PyAny>,
        args: &Bound<'py, PyTuple>,
        kwargs: Option<&Bound<'py, PyDict>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let gc = py.import("gc")?;
        let gc_was_enabled = gc.call_method0("isenabled")?.is_truthy()?;
        if self.disable_gc {
            gc.call_method0("disable")?;
        }
        // A first call outside of timing gives us the return value and warms
        // up any lazy initialisation inside the callee.
        let result = func.call(args, kwargs)?;
        if self.warmup {
            for _ in 0..3 {
                func.call(args, kwargs)?;
            }
        }
        // Calibrate: find an iteration count whose round exceeds min_time.
        let mut iterations = 1usize;
        loop {
            let start = Instant::now();
            for _ in 0..iterations {
                func.call(args, kwargs)?;
            }
            let elapsed = start.elapsed().as_secs_f64();
            if elapsed >= self.min_time || iterations >= 1_000_000 {
                break;
            }
            let factor = if elapsed > 0.0 {
                ((self.min_time / elapsed).ceil() as usize).clamp(2, 100)
            } else {
                10
            };
            iterations = iterations.saturating_mul(factor);
        }
        let mut times: Vec<f64> = Vec::with_capacity(self.min_rounds);
        let deadline = Instant::now() + std::time::Duration::from_secs_f64(self.max_time);
        let mut rounds = 0usize;
        // Always complete `min_rounds`, then keep going until the time budget
        // runs out (capped so a pathologically fast callee cannot spin).
        while rounds < self.min_rounds || (Instant::now() < deadline && rounds < 100_000) {
            let start = Instant::now();
            for _ in 0..iterations {
                func.call(args, kwargs)?;
            }
            times.push(start.elapsed().as_secs_f64() / iterations as f64);
            rounds += 1;
        }
        if self.disable_gc && gc_was_enabled {
            gc.call_method0("enable")?;
        }
        self.store.results.lock().unwrap().push(BenchResult {
            name: self.name.clone(),
            group: self.group.clone(),
            rounds,
            iterations,
            times,
        });
        Ok(result)
    }
}

pub fn make_fixture(py: Python<'_>, worker: &Worker, item: &Arc<Item>) -> PyResult<Py<PyAny>> {
    let opts = BenchOptions::from_config(&worker.session.cfg);
    if opts.skip {
        return Err(crate::runtime::skip_err(py, "Skipping benchmark (--benchmark-skip active)."));
    }
    let group = item
        .all_marks(true)
        .iter()
        .find(|m| m.name == "benchmark")
        .and_then(|m| m.kwarg(py, "group"))
        .and_then(|g| g.extract::<String>().ok());
    Ok(Py::new(
        py,
        BenchmarkFixture {
            name: item.name.clone(),
            group,
            disabled: opts.disabled,
            min_rounds: opts.min_rounds,
            min_time: opts.min_time,
            max_time: opts.max_time,
            warmup: opts.warmup,
            disable_gc: opts.disable_gc,
            store: worker.session.bench_store.clone(),
            extra_info: PyDict::new(py).unbind(),
            used: Mutex::new(false),
        },
    )?
    .into_any())
}

/// Scale a duration to a human unit, as pytest-benchmark's table does.
pub fn scale(times: &[f64]) -> (&'static str, f64) {
    let m = times.iter().copied().fold(f64::INFINITY, f64::min);
    if m < 1e-6 {
        ("ns", 1e9)
    } else if m < 1e-3 {
        ("us", 1e6)
    } else if m < 1.0 {
        ("ms", 1e3)
    } else {
        ("s", 1.0)
    }
}
