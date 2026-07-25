//! Per-test output capturing.
//!
//! pytest swaps `sys.stdout`/`sys.stderr` (or the underlying file descriptors)
//! for the duration of each test and replays what was written when the test
//! fails.  Neither of those is safe when several tests run at once: they are
//! process-global.
//!
//! Instead we install a proxy object over `sys.stdout`/`sys.stderr` once, for
//! the whole session, and give it a per-thread buffer.  A worker that has
//! capturing active writes into its own buffer; a thread with no active capture
//! falls through to the real stream.  Nothing is swapped while tests run, so
//! capturing composes with the thread pool.
//!
//! File-descriptor level capturing (`--capture=fd`) cannot work this way — a
//! process has one fd 1 — so it degrades to `sys` level capturing, which
//! catches everything written through Python.

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyList;
use rustc_hash::FxHashMap;
use std::sync::{Arc, Mutex, OnceLock};
use std::thread::ThreadId;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// No capturing at all (`--capture=no` / `-s`).
    No,
    /// Replace `sys.stdout` / `sys.stderr`.
    Sys,
    /// Also echo to the real stream (`--capture=tee-sys`).
    TeeSys,
}

impl Mode {
    pub fn parse(s: &str) -> Mode {
        match s {
            "no" => Mode::No,
            "tee-sys" => Mode::TeeSys,
            // `fd` has no per-thread equivalent — a process has one fd 1 — so it
            // behaves as `sys`, which catches everything Python writes.
            _ => Mode::Sys,
        }
    }
}

#[derive(Default)]
struct Buffers {
    out: FxHashMap<ThreadId, Py<PyAny>>,
    err: FxHashMap<ThreadId, Py<PyAny>>,
}

struct State {
    buffers: Mutex<Buffers>,
    tee: bool,
}

static STATE: OnceLock<Arc<State>> = OnceLock::new();

fn state() -> Option<&'static Arc<State>> {
    STATE.get()
}

/// The object installed as `sys.stdout` / `sys.stderr`.
#[pyclass(module = "pytest", name = "CaptureProxy")]
pub struct CaptureProxy {
    /// The stream this proxy stands in for.
    is_stderr: bool,
    /// The stream that was there before, used when nothing is being captured.
    original: Py<PyAny>,
}

#[pymethods]
impl CaptureProxy {
    fn write(&self, py: Python<'_>, data: &Bound<'_, PyAny>) -> PyResult<usize> {
        let text: String = data.extract().unwrap_or_else(|_| data.str().map(|s| s.to_string()).unwrap_or_default());
        let Some(state) = state() else {
            return self.passthrough(py, &text);
        };
        let tid = std::thread::current().id();
        let target = {
            let buffers = state.buffers.lock().unwrap();
            let map = if self.is_stderr { &buffers.err } else { &buffers.out };
            map.get(&tid).map(|b| b.clone_ref(py))
        };
        match target {
            Some(buf) => {
                buf.bind(py).call_method1("write", (text.as_str(),))?;
                if state.tee {
                    self.passthrough(py, &text)?;
                }
                Ok(text.len())
            }
            None => self.passthrough(py, &text),
        }
    }

    fn writelines(&self, py: Python<'_>, lines: &Bound<'_, PyAny>) -> PyResult<()> {
        for line in lines.try_iter()? {
            self.write(py, &line?)?;
        }
        Ok(())
    }

    fn flush(&self, py: Python<'_>) -> PyResult<()> {
        let _ = self.original.bind(py).call_method0("flush");
        Ok(())
    }

    fn isatty(&self) -> bool {
        false
    }

    fn fileno(&self, py: Python<'_>) -> PyResult<i32> {
        // Only meaningful when this thread is not capturing.
        if self.capturing(py) {
            return Err(PyValueError::new_err("redirected stream has no fileno"));
        }
        self.original.bind(py).call_method0("fileno")?.extract()
    }

    fn readable(&self) -> bool {
        false
    }
    fn writable(&self) -> bool {
        true
    }
    fn seekable(&self) -> bool {
        false
    }
    fn close(&self) {}

    #[getter]
    fn closed(&self) -> bool {
        false
    }

    #[getter]
    fn encoding(&self, py: Python<'_>) -> String {
        self.original
            .bind(py)
            .getattr("encoding")
            .and_then(|e| e.extract::<String>())
            .unwrap_or_else(|_| "utf-8".to_string())
    }

    #[getter]
    fn errors(&self, py: Python<'_>) -> String {
        self.original
            .bind(py)
            .getattr("errors")
            .and_then(|e| e.extract::<String>())
            .unwrap_or_else(|_| "strict".to_string())
    }

    #[getter]
    fn name(&self) -> &'static str {
        if self.is_stderr {
            "<pytest-rs stderr>"
        } else {
            "<pytest-rs stdout>"
        }
    }

    #[getter]
    fn mode(&self) -> &'static str {
        "w"
    }

    /// Code that writes bytes reaches for `.buffer`; hand back the original so
    /// binary output still lands somewhere sensible.
    #[getter]
    fn buffer(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        Ok(self.original.bind(py).getattr("buffer")?.unbind())
    }
}

impl CaptureProxy {
    fn passthrough(&self, py: Python<'_>, text: &str) -> PyResult<usize> {
        self.original.bind(py).call_method1("write", (text,))?;
        Ok(text.len())
    }

    fn capturing(&self, py: Python<'_>) -> bool {
        let Some(state) = state() else { return false };
        let tid = std::thread::current().id();
        let buffers = state.buffers.lock().unwrap();
        let map = if self.is_stderr { &buffers.err } else { &buffers.out };
        let _ = py;
        map.contains_key(&tid)
    }
}

/// Install the proxies.  Safe to call once per session; a no-op for `Mode::No`.
pub fn install(py: Python<'_>, mode: Mode) -> PyResult<()> {
    if mode == Mode::No {
        return Ok(());
    }
    if STATE.get().is_some() {
        return Ok(());
    }
    let sys = py.import("sys")?;
    let out = sys.getattr("stdout")?;
    let err = sys.getattr("stderr")?;
    let proxy_out = Py::new(py, CaptureProxy { is_stderr: false, original: out.unbind() })?;
    let proxy_err = Py::new(py, CaptureProxy { is_stderr: true, original: err.unbind() })?;
    sys.setattr("stdout", proxy_out)?;
    sys.setattr("stderr", proxy_err)?;
    let _ = STATE.set(Arc::new(State {
        buffers: Mutex::new(Buffers::default()),
        tee: mode == Mode::TeeSys,
    }));
    Ok(())
}

/// Begin capturing on the calling thread.
pub fn start(py: Python<'_>) -> PyResult<()> {
    let Some(state) = state() else { return Ok(()) };
    let io = py.import("io")?;
    let out = io.getattr("StringIO")?.call0()?;
    let err = io.getattr("StringIO")?.call0()?;
    let tid = std::thread::current().id();
    let mut buffers = state.buffers.lock().unwrap();
    buffers.out.insert(tid, out.unbind());
    buffers.err.insert(tid, err.unbind());
    Ok(())
}

/// Read and clear what this thread has captured so far, leaving capturing on.
pub fn read(py: Python<'_>) -> PyResult<(String, String)> {
    let Some(state) = state() else { return Ok((String::new(), String::new())) };
    let tid = std::thread::current().id();
    let (out, err) = {
        let buffers = state.buffers.lock().unwrap();
        (
            buffers.out.get(&tid).map(|b| b.clone_ref(py)),
            buffers.err.get(&tid).map(|b| b.clone_ref(py)),
        )
    };
    let drain = |b: Option<Py<PyAny>>| -> PyResult<String> {
        let Some(b) = b else { return Ok(String::new()) };
        let bound = b.bind(py);
        let text: String = bound.call_method0("getvalue")?.extract()?;
        bound.call_method1("seek", (0,))?;
        bound.call_method1("truncate", (0,))?;
        Ok(text)
    };
    Ok((drain(out)?, drain(err)?))
}

/// Stop capturing on this thread and return everything written.
pub fn stop(py: Python<'_>) -> PyResult<(String, String)> {
    let Some(state) = state() else { return Ok((String::new(), String::new())) };
    let captured = read(py)?;
    let tid = std::thread::current().id();
    let mut buffers = state.buffers.lock().unwrap();
    buffers.out.remove(&tid);
    buffers.err.remove(&tid);
    Ok(captured)
}

/// Temporarily suspend capturing for the calling thread (used by `capsys`'s
/// `disabled()` context manager).
pub fn suspend(py: Python<'_>) -> Option<(Py<PyAny>, Py<PyAny>)> {
    let state = state()?;
    let tid = std::thread::current().id();
    let mut buffers = state.buffers.lock().unwrap();
    let _ = py;
    match (buffers.out.remove(&tid), buffers.err.remove(&tid)) {
        (Some(o), Some(e)) => Some((o, e)),
        (o, e) => {
            if let Some(o) = o {
                buffers.out.insert(tid, o);
            }
            if let Some(e) = e {
                buffers.err.insert(tid, e);
            }
            None
        }
    }
}

pub fn resume(saved: (Py<PyAny>, Py<PyAny>)) {
    let Some(state) = state() else { return };
    let tid = std::thread::current().id();
    let mut buffers = state.buffers.lock().unwrap();
    buffers.out.insert(tid, saved.0);
    buffers.err.insert(tid, saved.1);
}

#[allow(dead_code)]
fn _keep(py: Python<'_>) {
    let _ = PyList::empty(py);
}
