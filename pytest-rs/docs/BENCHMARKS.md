# Benchmarks

Workload: the [pyca/cryptography](https://github.com/pyca/cryptography) test
suite at `50.0.0-dev1` — 4662 collected tests, of which 4015 run and 647 skip on
this machine (OpenSSL 3.0.13, no wycheproof or x509-limbo vectors present).

Machine: 4 vCPU, 15 GiB RAM, Linux 6.18. Stock pytest is 9.1.1 with pytest-xdist
3.8.0. All runs use `-p no:randomly` so ordering matches. Timings are best-of-3
wall clock with warm `__pycache__` — measuring pytest against a cold assertion
rewrite cache would flatter us (its first collection takes 4.0 s rather than
1.1 s). Every number below comes from one uninterrupted run of
`tools/benchmark.py`, so the columns are comparable with each other even though
absolute numbers move with machine load.

Reproduce with `python tools/benchmark.py /path/to/cryptography --repeat 3`.

## Headline

| | 3.11 (GIL) | 3.14t (free-threaded) |
| --- | --- | --- |
| pytest, serial | 25.43 s | 26.08 s |
| pytest + xdist `-n 4` | 10.11 s | 11.22 s |
| pytest-rs, serial | 20.95 s | 22.16 s |
| pytest-rs `-n 4` | 16.11 s | **7.48 s** |

On a free-threaded interpreter the thread pool beats four xdist processes
(7.48 s vs 11.22 s) and stock pytest by 3.5×, while staying in one process — no
`execnet`, no report pickling, and session fixtures genuinely built once rather
than once per worker.

On a GIL build threads still help this suite (16.11 s vs 20.95 s serial), since
much of its time is inside GIL-releasing native code, but processes win.

## Collection

| | pytest | pytest-rs | |
| --- | --- | --- | --- |
| 3.11 | 1.14 s | 0.26 s | 4.4× |
| 3.14t | 1.24 s | 0.32 s | 3.9× |

Both produce the same 4662 node ids, byte for byte. The gap comes from not
rewriting any module's AST, not building a Python object per collected node, and
computing each item's fixture closure once during collection instead of
rediscovering it per test.

## Engine overhead

Collection and per-test overhead are easiest to see on a suite that does no real
work: 5000 trivial tests (50 modules × 100 parametrised cases, each requesting a
two-deep fixture chain).

| | Wall | Per test |
| --- | --- | --- |
| pytest | 3.98 s | 0.797 ms |
| pytest-rs | 0.08 s | 0.017 ms |

48× less overhead per test. On cryptography that accounts for roughly 4 s of the
28 s, which is most of the serial-mode difference; the rest of the run is real
crypto.

Two things a test never needs are no longer done for it: the module's `__dict__`
(only a string `skipif`/`xfail` condition reads it) and the Python-visible item
object (only the `pytest_runtest_setup`/`teardown` hooks take one). Both were
per-test `getattr`s on objects shared between workers, so dropping them helps
the parallel case more than the serial one.

## Worker count

`-v` reports the parallelism the run actually achieved — CPU time across all
threads divided by wall time — which is the number to look at when deciding how
many workers a suite can use. On cryptography, free-threaded 3.14:

| Workers | Wall | Observed parallelism | CPU |
| --- | --- | --- | --- |
| 1 | 21.4 s | 0.85× | 18.2 s |
| 2 | 11.4 s | 1.70× | 19.4 s |
| 4 | 8.9 s | 2.45× | 21.7 s |
| 8 | 7.5 s | 2.77× | 20.8 s |

Observed parallelism plateaus around 2.5–2.8× on four cores, well short of the
worker count: the tests are waiting on something, not computing. (The 0.85× at
one worker is time blocked reading test vectors off disk, which
`time.process_time()` correctly does not count.)

Note that eight workers beat four here, on a four-core machine. That is a
signature of lock-bound rather than CPU-bound work: when a worker is parked
inside libcrypto, an extra runnable thread has a core to use. `-n auto` picks the
core count, which is right for suites that are actually CPU-bound; if `-v` shows
observed parallelism well under the worker count, oversubscribing is worth
trying.

## Why threads stop where they do

Two things bound the parallel numbers, and only one of them is ours.

**The workload's own locking.** `tools/thread_scaling.py --cryptography` builds
AES-GCM ciphers on N threads of a free-threaded interpreter, with no test runner
involved:

| Threads | Wall | Scaling |
| --- | --- | --- |
| 1 | 0.24 s | 1.00× |
| 2 | 0.44 s | 1.10× |
| 4 | 0.82 s | 1.17× |

1.17× on 4 cores. OpenSSL 3.x takes process-global locks when fetching algorithm
implementations, so cipher-heavy tests serialise against each other inside
libcrypto. This is the ceiling on how much any in-process runner can parallelise
this particular suite; xdist sidesteps it by giving each worker its own process
and its own copy of that state.

**The engine is not the limit.** The same tool on pure-Python CPU work:

| Threads | 3.14t | scaling | 3.11 | scaling |
| --- | --- | --- | --- | --- |
| 1 | 0.47 s | 1.00× | 0.42 s | 1.00× |
| 2 | 0.46 s | 2.02× | 0.86 s | 0.97× |
| 4 | 0.46 s | 4.03× | 2.09 s | 0.80× |
| 8 | 0.90 s | 4.14× | — | — |

Linear to the core count on a free-threaded build. The 3.11 column is the same
measurement with a GIL: threads cannot overlap bytecode, and contention makes it
worse than serial.

**Long single tests.** Two cryptography tests loop over thousands of vectors
internally and take about 1.5 s each on their own; no scheduler can split them.
Starting them early matters, which is why per-test durations are cached between
runs and groups are dispatched longest-first.

## Why `-n auto` is 1 on a GIL build

The table above is the whole argument. Threads only overlap when the interpreter
lets them, and for a pure-Python suite on CPython 3.11 four threads are 20%
*slower* than one. Suites like cryptography, which spend their time in native
code that releases the GIL, do gain — 17.23 s against 22.55 s here — but that is
the exception. So `-n auto` resolves to one worker on a GIL build and to the CPU
count on a free-threaded one; pass `-n N` explicitly when the suite is
native-heavy.

## Scheduling

`-vv` reports what the scheduler decided:

```
scheduling: 4587 parallel group(s), 15 serialised test(s), ordered by recorded durations
  serialised:   15 test(s) — fixture "monkeypatch"
(collection 0.27s, parallel phase 14.95s, serial phase 0.04s, ...)
```

15 of 4662 tests need serialising. Getting there took three refinements:

| | Serialised |
| --- | --- |
| first working version | 228 |
| ...after honouring context-scoped warnings (CPython 3.14+) | 124 |
| ...after not serialising disabled benchmarks | 93 |
| ...after telling `os.environ` reads from writes | 15 |

The last one is the clearest: `test_no_circular_imports` is parametrised over 78
modules and calls `os.environ.copy()`. Name-level analysis sees `environ` and
serialises all 78; disassembling the function shows the load is followed by a
`copy` call rather than a `STORE_SUBSCR`, so they all stay parallel.

## A note on measurement

An earlier revision deadlocked when two workers raced for the same session-scoped
fixture on a GIL build: the second blocked on the fixture's lock *while holding
the interpreter*, so the first could never finish. It hung about one `-n 4` run
in three against cryptography, whose `rsa_key_2048` fixture is slow enough to
open the window wide.

It is worth recording because of how it presented: the runs that survived still
finished, just slower, so the benchmark table looked plausible rather than
broken. Wall-clock numbers that are merely disappointing are worth a second look.
