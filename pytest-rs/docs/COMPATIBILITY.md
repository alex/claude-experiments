# Compatibility

`pytest-rs` targets the subset of pytest that real test suites use. The
reference workload is [pyca/cryptography](https://github.com/pyca/cryptography);
`tools/compare_with_pytest.py` runs both runners over a project and diffs
collected node ids and per-test outcomes.

Current status on that suite: **4662 collected, identical node ids, identical
per-test outcomes** (4015 passed / 647 skipped on CPython 3.11 + OpenSSL 3.0.13).

## The `pytest` module

`pytest-rs` does not shadow an installed pytest on disk. It builds a module
object in Rust and installs it as `sys.modules["pytest"]` before any conftest or
test module is imported, so both runners can live in the same environment.

Supported:

| Area | Provided |
| --- | --- |
| Outcomes | `skip`, `fail`, `xfail`, `exit`, `importorskip`, and their `.Exception` attributes |
| Exceptions | `Skipped`, `Failed`, `XFailed`, `Exit`, `OutcomeException`, `UsageError` |
| Assertions | `raises` (context manager and callable form, `match=`), `warns`, `deprecated_call`, `approx` |
| `ExceptionInfo` | `.value`, `.type`, `.typename`, `.traceback`, `.match()`, `.exconly()`, `.errisinstance()` |
| Fixtures | `fixture` (all scopes, `params`, `ids`, `autouse`, `name`), `yield_fixture` |
| Marks | `pytest.mark.*`, `Mark`, `MarkDecorator`, `param` / `ParameterSet` |
| Objects | `Config`, `Parser`, `Function`/`Item`, `FixtureRequest`, `MonkeyPatch` |
| Misc | `hookimpl`, `hookspec`, `register_assert_rewrite`, `set_trace`, `main`, `__version__` |

`pytest.__version__` reports a pytest version (`8.4.0`) so that version gates in
test suites keep working; the real version is `pytest.__pytest_rs_version__`.

## Markers

Built in: `skip`, `skipif`, `xfail` (including `condition`, `reason`, `run`,
`strict`, `raises`), `parametrize` (stacked, `indirect`, `ids` as list or
callable, `pytest.param(marks=..., id=...)`), `usefixtures`, `filterwarnings`.

Custom markers work, including `--strict-markers` validation against the
`markers` ini option and `config.addinivalue_line("markers", ...)`.

Two extra markers control scheduling: `@pytest.mark.serial` forces a test onto
the serialised path, `@pytest.mark.thread_safe` forces it off.

Parametrisation id generation matches pytest's `idmaker` including the escaping
rules for `str` vs `bytes`, `enum`, compiled patterns, objects with `__name__`,
the `argname{index}` fallback, and the duplicate-id disambiguation suffixes.

## Fixtures

* Scopes: function, class, module, package, session.
* Dependency closures are computed once per test at collection time.
* Generator fixtures are finalised in reverse registration order when their
  scope ends; `request.addfinalizer` participates in the same ordering.
* Fixtures defined inside a test class are bound to the test instance, and
  `@staticmethod`-wrapped fixtures are not.
* Fixture parametrisation (`@pytest.fixture(params=...)`) expands items before
  `parametrize` markers, matching pytest's hook ordering and id layout.
* Overriding a fixture of the same name at a narrower scope works at conftest,
  module and class level, including the chaining form where the override
  requests its own name (`def simple(simple)`) — that resolves to the next
  definition down the chain, not to itself. The most specific definition visible
  to a node id wins.

Built-in fixtures: `request`, `pytestconfig`, `monkeypatch`, `tmp_path`,
`tmp_path_factory`, `capsys`, `capfd`, `recwarn`, `benchmark`,
`record_property`, `cache`.

## Output capturing

Capturing is on by default, as in pytest, and output from a failing test is
replayed under `Captured stdout call` / `Captured stderr call`.

The implementation differs because pytest's does not survive concurrency:
swapping `sys.stdout` or dup'ing file descriptors is process-global. Instead a
proxy is installed over `sys.stdout`/`sys.stderr` once for the whole session and
given a per-thread buffer. A worker with capturing active writes into its own
buffer; a thread without one falls through to the real stream. Nothing is
swapped while tests run.

The consequence: `--capture=fd` cannot be honoured literally, because a process
has a single file descriptor 1. It behaves as `--capture=sys`, which catches
everything written through Python but not writes issued directly by C extensions
to fd 1. `--capture=no` / `-s` and `--capture=tee-sys` work as documented, and
`capsys.disabled()` suspends the calling thread's buffer only.

## Warnings

`filterwarnings` (ini), `-W`, and `@pytest.mark.filterwarnings` are supported,
using pytest's `action:message:category:module:lineno` spec with dotted category
paths. pytest's own defaults (`always::DeprecationWarning`,
`always::PendingDeprecationWarning`) are installed first.

A `filterwarnings` marker scopes filters to one test with
`warnings.catch_warnings()`, which swaps a process-global stack on CPython
before 3.14. On those interpreters a marked test is moved to the serialised
path; from 3.14 onwards `catch_warnings` is context-scoped (always so on
free-threaded builds) and the test stays parallel. The same reasoning applies to
`pytest.warns` and the `recwarn` fixture.

## Module import

Files are imported with pytest's `prepend` semantics: walk up while
`__init__.py` exists to find the package root, insert it on `sys.path`, import
by dotted name.

Outside a package every `conftest.py` wants the module name `conftest`. When the
name is already taken by a different file the module is loaded directly from its
path instead, so each conftest gets its own module object and its fixtures and
hooks are all registered. The most recently loaded one keeps the shared name in
`sys.modules`, matching where pytest ends up — which means `from conftest import
X` inside a test module is as unreliable here as it is there.

## conftest hooks

Discovered by name in every `conftest.py` from the rootdir down. Hook
implementations are called with only the parameters they declare.

`pytest_addoption`, `pytest_configure`, `pytest_unconfigure`,
`pytest_report_header`, `pytest_collection_modifyitems`, `pytest_runtest_setup`,
`pytest_runtest_teardown`, `pytest_sessionstart`, `pytest_sessionfinish`,
`pytest_terminal_summary`, `pytest_itemcollected`, `pytest_collectstart`.

`pytest_collection_modifyitems` may reorder or drop entries in `items`; the list
is read back after the hooks run and the changes take effect.

`parser.addoption` / `parser.addini` / `parser.getgroup` are honoured, and
options registered from a conftest are available to `config.getoption`
(including the `skip=True` form).

## Configuration

Discovery follows pytest's order: `pytest.ini`, `.pytest.ini`,
`pyproject.toml` (`[tool.pytest.ini_options]`), `tox.ini` (`[pytest]`),
`setup.cfg` (`[tool:pytest]`), searched upward from the common ancestor of the
arguments.

Recognised ini options: `addopts`, `testpaths`, `python_files`,
`python_classes`, `python_functions`, `norecursedirs`, `markers`,
`filterwarnings`, `console_output_style` (`progress`, `count`, `classic`,
`progress-even-when-capture-no`), `xfail_strict`, `empty_parameter_set_mark`,
`pythonpath`, `usefixtures`, `minversion`, `required_plugins`, `cache_dir`.

`cache_dir` also holds pytest-rs's own cross-run state: the randomisation seed
(so `--randomly-seed=last` works) and per-test durations, which let the scheduler
start the most expensive groups first on subsequent runs.

## Command line

Selection and reporting: `-k`, `-m`, `-x`, `--maxfail`, `-v`, `-q`, `-s`,
`--capture`, `--tb`, `-r`, `--strict-markers`, `--collect-only`, `--durations`,
`--ignore`, `--deselect`, `--no-header`, `--no-summary`, `--color`, `-p no:NAME`,
`--rootdir`, `-c`, `-W`, `-l`/`--showlocals`, `--junitxml`, and node-id
selectors (`path::Class::test[param]`).

Parallelism: `-n` / `--numprocesses` (threads, not processes), `--no-parallel`.

Built-in plugin behaviours:

* **pytest-benchmark** — `--benchmark-disable`, `--benchmark-enable`,
  `--benchmark-only`, `--benchmark-skip`, `--benchmark-min-rounds`,
  `--benchmark-min-time`, `--benchmark-max-time`, `--benchmark-warmup`,
  `--benchmark-sort`, `--benchmark-disable-gc`, plus `benchmark.pedantic()`.
* **pytest-cov** — `--cov`, `--cov-report` (`term`, `term-missing`, `html`,
  `xml`, `json`, `annotate`, each with an optional `:destination`),
  `--cov-branch`, `--cov-append`, `--cov-config`, `--cov-context`,
  `--cov-fail-under`, `--no-cov`. Measurement starts before any test module is
  imported and uses coverage.py's thread concurrency mode.
* **pytest-randomly** — on by default with a per-run seed printed in the header;
  `--randomly-seed=N|last|default`, `--randomly-dont-reorganize`,
  `--randomly-dont-reset-seed`, `-p no:randomly`. Modules are shuffled, then
  classes within a module, then tests within a class, so related tests stay
  adjacent — which also lets module-scoped fixtures live for one contiguous
  span.

  One behaviour is deliberately narrowed: pytest-randomly reseeds Python's
  global RNG before *every* test. That is only meaningful when one test runs at
  a time; several workers reseeding a process-global generator would produce
  neither reproducibility nor isolation. `pytest-rs` seeds once from the session
  seed, which keeps a run reproducible for a given `--randomly-seed` without
  pretending to give per-test isolation that threads cannot deliver.
  `--randomly-dont-reset-seed` skips even that.

Installing the real plugins is unnecessary and their entry points are ignored.

## Deliberately not implemented

* Third-party plugins and the `pluggy` hook system. `config.pluginmanager`
  exists but is inert.
* `unittest.TestCase` and `doctest` collection.
* `--pdb`, `--trace`, `--lf`/`--ff` (accepted, no effect).
* `pytest_runtest_protocol`, `pytest_runtest_makereport`, hook wrappers, and the
  `Node` class hierarchy beyond what `request.node` needs.
* Import modes other than `prepend`.

## Assertion output

pytest rewrites every test module's AST at import time so failing asserts can
report intermediate values. `pytest-rs` does not: when an `AssertionError`
escapes, it walks the traceback, re-parses the failing source line, and
re-evaluates its sub-expressions in the frame that raised. Comparisons get the
same `assert left == right` rendering plus a short structural diff for strings,
bytes, sequences and mappings.

The trade-off: passing assertions cost nothing and no `.pyc` rewriting happens,
but an expression with side effects can render differently than pytest would,
and only the failing line is explained (not a multi-line expression).
