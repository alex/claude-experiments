# pytest-rs

A [pytest](https://docs.pytest.org/)-compatible test runner implemented in Rust
with [pyo3](https://pyo3.rs/).

The engine — configuration, collection, parametrisation, fixture resolution,
scheduling, reporting — is Rust; only the test code itself runs in Python. It is
developed against the [pyca/cryptography](https://github.com/pyca/cryptography)
test suite, where it collects the same 4662 node ids as stock pytest, byte for
byte, and produces the same outcome for every one of them.

Three things are different by design:

1. **Tests run on threads by default.** Tests are partitioned into serial groups
   so that anything sharing a scoped fixture instance stays on one thread, and a
   static analysis pass moves tests that touch process-global state onto a
   serialised path. No subprocesses, no `execnet`, no pickling of reports.
2. **pytest-benchmark, pytest-cov and pytest-randomly behaviours are built in.**
   They are part of the engine rather than plugins, so their options work with
   nothing installed and cost nothing when unused.
3. **Assertion introspection is lazy.** pytest rewrites every module's AST at
   import time so failing asserts can show intermediate values. `pytest-rs`
   recovers the same information on demand, by re-parsing and re-evaluating the
   failing expression only when an assertion actually fails. Together with
   computing fixture closures once at collection, per-test overhead is 0.017 ms
   against pytest's 0.797 ms.

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

Anything not listed in `--help` is either unsupported or accepted for
compatibility and ignored; see [docs/COMPATIBILITY.md](docs/COMPATIBILITY.md).

## Threading model

The scheduler makes two passes over the collected items.

**Grouping.** For every item it looks at the fixture closure computed during
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

**Thread-safety analysis.** Some test bodies touch state that is global to the
interpreter: the `warnings` filter stack, `os.environ`, the working directory,
the recursion limit. Those cannot overlap with anything else. `pytest-rs` finds
them by walking compiled code objects — `co_names` records every global and
attribute name a function references — following calls into same-module helpers
a few levels deep. Anything that matches, plus anything requesting `monkeypatch`
or `capsys`, is moved to a serial phase that runs after the parallel one.
`@pytest.mark.serial` forces a test onto that path; `@pytest.mark.thread_safe`
forces it off, and `-vv` prints what was serialised and why.

The analysis is deliberately not purely name-based, because that over-serialises.
`os.environ.copy()` is a read and perfectly safe; `os.environ["X"] = v` is not. A
peephole pass over the disassembly tells them apart. Likewise, warning filters
are only global before CPython 3.14 — from 3.14 `catch_warnings()` is
context-scoped (always so on free-threaded builds), so `pytest.warns` stays
parallel there. Those refinements, plus not serialising benchmarks that are
disabled, take cryptography's serialised set from 228 tests to 15; see
[docs/BENCHMARKS.md](docs/BENCHMARKS.md) for the breakdown.

On a free-threaded interpreter this produces real parallelism: cryptography's
suite runs in 7.5 s against stock pytest's 26.1 s and xdist's 11.2 s on four
cores. On a GIL build threads only overlap GIL-releasing native code and I/O —
a help for suites like that one, a 20% loss for pure-Python suites — so
`-n auto` resolves to one worker there; pass `-n N` explicitly to override.

Output capturing is built the same way — a proxy over `sys.stdout`/`sys.stderr`
with a per-thread buffer, rather than swapping the streams — so it composes with
the pool instead of fighting it.

## Status

`unittest.TestCase` classes are collected and run through unittest's own
protocol, and the xunit-style `setup_module`/`setup_class`/`setup_method`
functions work; `doctest` collection and `--pdb` do not.
[docs/COMPATIBILITY.md](docs/COMPATIBILITY.md) has the supported surface and the
deliberate omissions; [docs/BENCHMARKS.md](docs/BENCHMARKS.md) has measurements,
including where the remaining time on cryptography actually goes.

```console
$ python tools/selftest.py              # corpus run under both runners
$ python tools/compare_with_pytest.py /path/to/project
$ python tools/benchmark.py /path/to/project
$ python tools/thread_scaling.py        # does this workload scale at all?
```
