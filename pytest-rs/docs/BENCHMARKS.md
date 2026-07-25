# Benchmarks

Workload: the [pyca/cryptography](https://github.com/pyca/cryptography) test
suite at `50.0.0-dev1` — 4662 collected tests, of which 4015 run and 647 skip on
this machine (OpenSSL 3.0.13, no wycheproof or x509-limbo vectors present).

Machine: 4 vCPU, 15 GiB RAM, Linux 6.18. Stock pytest is 9.1.1 with pytest-xdist
3.8.0. All runs use `-p no:randomly` so ordering matches. Timings are best-of-N
wall clock with warm `__pycache__` — measuring pytest against a cold assertion
rewrite cache would flatter us (its first collection takes 4.0 s rather than
1.5 s).

Reproduce with `python tools/benchmark.py /path/to/cryptography --repeat 3`.

## Headline

| | 3.11 (GIL) | 3.14t (free-threaded) |
| --- | --- | --- |
| pytest, serial | 34.90 s | 35.38 s |
| pytest + xdist `-n 4` | 13.98 s | 16.39 s |
| pytest-rs, serial | 29.71 s | 29.63 s |
| pytest-rs `-n 4` | 24.36 s | **14.50 s** |

On a free-threaded interpreter, threads beat four xdist processes (14.50 s vs
16.39 s) while staying in one process — no `execnet`, no report pickling, and
session fixtures genuinely built once rather than once per worker.

## Collection

| | pytest | pytest-rs | |
| --- | --- | --- | --- |
| 3.11 | 1.51 s | 0.33 s | 4.6× |
| 3.14t | 1.91 s | 0.42 s | 4.5× |

Both produce the same 4662 node ids, byte for byte. The gap comes from not
rewriting any module's AST, not building a Python object per collected node, and
computing each item's fixture closure once during collection instead of
rediscovering it per test.

## Engine overhead

Collection and per-test overhead are easier to see on a suite that does no real
work: 5000 trivial tests (50 modules × 100 parametrised cases, each requesting a
two-deep fixture chain).

| | Wall | Per test |
| --- | --- | --- |
| pytest | 4.59 s | 0.92 ms |
| pytest-rs | 0.12 s | 0.024 ms |

38× less overhead per test. On cryptography that saves roughly 4 s of the 35 s,
which is most of the serial-mode difference; the rest of the run is real crypto.

## Why threads stop where they do

Two things bound the parallel numbers, and only one of them is ours.

**The workload's own locking.** `tools/thread_scaling.py --cryptography` builds
AES-GCM ciphers on N threads of a free-threaded interpreter:

| Threads | Wall | Scaling |
| --- | --- | --- |
| 1 | 0.30 s | 1.00× |
| 2 | 0.58 s | 1.05× |
| 4 | 0.93 s | 1.31× |

1.31× on 4 cores, with no test runner involved: OpenSSL 3.x takes process-global
locks when fetching algorithm implementations, so cipher-heavy tests serialise
against each other inside libcrypto. xdist sidesteps this by giving each worker
its own process and its own copy of that state — which is exactly why the
process-based runner stays competitive on this particular suite despite the
extra machinery.

**The engine itself is not the limit.** The same tool on pure-Python CPU work:

| Threads | Wall | Scaling |
| --- | --- | --- |
| 1 | 1.98 s | 1.00× |
| 2 | 1.02 s | 1.94× |
| 4 | 0.62 s | 3.19× |
| 8 | 0.61 s | 3.25× |

3.2× on 4 cores through the full runner, so the scheduler, fixture cache and
report channel are not what cryptography is waiting on.

**Long single tests.** Two cryptography tests loop over thousands of vectors
internally and take about 1.5 s each on their own; no scheduler can split them.
Starting them early matters, which is why durations are cached between runs and
groups are dispatched longest-first.

## Why `-n auto` is 1 on a GIL build

Threads can only overlap when the interpreter lets them. On CPython 3.11 the
answer depends entirely on how much time the suite spends in GIL-releasing
native code:

| Workload | `-n 1` | `-n 4` | |
| --- | --- | --- | --- |
| cryptography (native-heavy) | 29.71 s | 24.36 s | 1.22× faster |
| pure-Python CPU | 1.91 s | 2.06 s | 8% slower |

Most suites look like the second row, so `-n auto` resolves to one worker on a
GIL build and to the CPU count on a free-threaded one. Pass `-n N` explicitly
when the suite is native-heavy — the gain is real, it just is not a safe default.

## Scheduling

`-vv` reports what the scheduler decided:

```
scheduling: 4587 parallel group(s), 15 serialised test(s), ordered by recorded durations
  serialised:   15 test(s) — fixture "monkeypatch"
(collection 0.27s, parallel phase 14.95s, serial phase 0.04s, ...)
```

15 of 4662 tests need serialising. Getting there took three refinements, each
worth roughly what it cost to find:

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
