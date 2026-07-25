# Benchmarks

Workload: the [pyca/cryptography](https://github.com/pyca/cryptography) test
suite at `50.0.0-dev1` — 4662 collected tests, of which 4015 run and 647 skip on
this machine (OpenSSL 3.0.13, no wycheproof or x509-limbo vectors present).

Machine: 4 vCPU, 15 GiB RAM, Linux 6.18.

All runs use `-p no:randomly` so ordering is identical between runners. Stock
pytest is 9.1.1 with pytest-xdist 3.8.0.

## Collection

Collection is the clearest win: no AST rewriting, no per-node Python objects,
fixture closures computed once.

| Runner | `--collect-only` |
| --- | --- |
| pytest 9.1.1 | 4.01 s |
| pytest-rs | 0.22 s |

Both produce the same 4662 node ids, byte for byte.

## Full run — CPython 3.11 (GIL)

| Runner | Wall |
| --- | --- |
| pytest, serial | 39.9 s |
| pytest-rs, serial | 38.5 s |
| pytest + xdist `-n 4` | 17.2 s |

On a GIL build threads cannot overlap Python bytecode, so `-n auto` resolves to
a single worker and the gain is limited to what we save on collection and
per-test overhead. Pass `-n N` explicitly if the workload is dominated by
GIL-releasing native code.

## Full run — CPython 3.14.6 free-threaded

| Runner | Wall |
| --- | --- |
| pytest, serial | 42.6 s |
| pytest + xdist `-n 4` | 16.7 s |
| pytest-rs `-n 1` | 34.7 s |
| pytest-rs `-n 2` | 28.8 s |
| pytest-rs `-n 4` | 22.0 s |
| pytest-rs `-n 8` | 21.8 s |

## Where the remaining time goes

Two tests dominate the critical path:

```
11.5 s  tests/hazmat/primitives/test_aes_gcm.py::TestAESModeGCM::test_gcm
11.0 s  tests/hazmat/primitives/test_ciphers.py::test_update_auto_chunking
```

Each is a single test that loops over thousands of vectors internally, so no
scheduler can split them. With ~35 s of total work and an 11 s longest job, a
perfect 4-way schedule bottoms out around 12–13 s; the makespan is set by that
job, not by the number of workers. That is also why `-n 8` barely improves on
`-n 4`.

## Engine overhead in isolation

To separate engine scaling from the workload, 400 pure-CPU Python tests spread
over 8 modules:

| Workers | Wall | Speed-up |
| --- | --- | --- |
| 1 | 1.98 s | 1.0× |
| 2 | 1.02 s | 1.9× |
| 4 | 0.62 s | 3.2× |
| 8 | 0.61 s | 3.2× |

3.2× on 4 cores, so the scheduler and per-test overhead are not the limit on the
cryptography suite.

## Reproducing

```console
$ python tools/compare_with_pytest.py /path/to/cryptography     # correctness
$ python tools/benchmark.py /path/to/cryptography               # timings
```
