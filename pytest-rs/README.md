# pytest-rs

A [pytest](https://docs.pytest.org/)-compatible test runner implemented in Rust
with [pyo3](https://pyo3.rs/).

`pytest-rs` reimplements the parts of pytest that real test suites depend on —
collection, parametrisation, fixtures, markers, reporting — with the engine in
Rust and only the test code itself in Python. It is developed against the
[pyca/cryptography](https://github.com/pyca/cryptography) test suite, which it
runs to the same pass/skip counts as stock pytest.

Three things are different by design:

1. **Tests run on threads by default.** Tests are partitioned into serial groups
   so that anything sharing a scoped fixture instance stays on one thread, and a
   static analysis pass moves tests that touch process-global state onto a
   serialised path. No subprocesses, no `execnet`, no pickling of reports.
2. **pytest-benchmark, pytest-cov and pytest-randomly behaviours are built in.**
   They are part of the engine rather than plugins, so their options work out of
   the box and cost nothing when unused.
3. **Assertion introspection is lazy.** pytest rewrites every module's AST at
   import time so failing asserts can show intermediate values. `pytest-rs`
   recovers the same information on demand, by re-evaluating the failing
   expression only when an assertion actually fails.

## Install

```console
$ pip install maturin
$ maturin build --release -o dist
$ pip install dist/pytest_rs-*.whl
```

## Use

```console
$ pytest-rs                      # same defaults as `pytest`
$ pytest-rs tests/unit -k parse  # same selectors
$ pytest-rs -n 8                 # eight worker threads
$ pytest-rs --no-parallel        # everything on the main thread
$ pytest-rs --cov=mypkg --cov-report=term-missing
```

Anything not listed in `--help` is either unsupported or silently accepted for
compatibility; see [docs/COMPATIBILITY.md](docs/COMPATIBILITY.md).

## Threading model

The scheduler makes two passes over the collected items.

*Grouping.* For every item it looks at the fixture closure computed during
collection. Any fixture with class, module or package scope identifies a shared
instance — keyed by `(fixture, parameter index, scope node)` — and all items that
would share an instance are unioned into one group. A group runs start to finish
on a single worker thread, so scope frames, caching and finalisation behave
exactly as they do under pytest.

Session-scoped fixtures are deliberately *not* grouped: serialising every test
that shares one would collapse the run onto a single thread. They live in a
process-wide cache and are created exactly once under a per-instance lock, which
preserves the "runs once per session" contract. A session fixture whose body is
flagged as thread hostile falls back to grouping.

*Thread-safety analysis.* Some test bodies touch state that is global to the
interpreter: the `warnings` filter stack, `os.environ`, the working directory,
the recursion limit. Those cannot overlap with anything else. `pytest-rs` finds
them by walking compiled code objects — `co_names` records every global and
attribute name a function references — following calls into same-module helpers
a few levels deep. Anything that matches, plus anything requesting `monkeypatch`,
`capsys`, `recwarn` or `benchmark`, is moved to a serial phase that runs after
the parallel one. `@pytest.mark.serial` forces a test onto that path;
`@pytest.mark.thread_safe` forces it off.

On a free-threaded (`--disable-gil`) interpreter this produces real parallelism.
On a GIL build threads still overlap GIL-releasing native code and I/O, but the
gain is much smaller, so `-n auto` resolves to one worker there; pass `-n N`
explicitly to override.

## Status

See [docs/COMPATIBILITY.md](docs/COMPATIBILITY.md) for the supported surface and
[docs/BENCHMARKS.md](docs/BENCHMARKS.md) for measurements.
