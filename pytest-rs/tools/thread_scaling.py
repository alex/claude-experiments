#!/usr/bin/env python3
"""Measure how well a workload scales across threads in this interpreter.

Useful for telling "the runner is not parallelising" apart from "the code under
test does not scale" — the two look identical from wall-clock alone.

    python tools/thread_scaling.py                 # pure-Python CPU work
    python tools/thread_scaling.py --cryptography  # AES-GCM through cryptography
"""

from __future__ import annotations

import argparse
import sys
import threading
import time


def cpu_work(n: int) -> None:
    total = 0
    for i in range(n):
        total += i * i % 7


def make_crypto_work():
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

    key = b"\x00" * 32
    iv = b"\x00" * 12
    data = b"x" * 64

    def work(n: int) -> None:
        for _ in range(n):
            enc = Cipher(algorithms.AES(key), modes.GCM(iv)).encryptor()
            enc.update(data)
            enc.finalize()

    return work


def bench(work, nthreads: int, per_thread: int) -> float:
    threads = [threading.Thread(target=work, args=(per_thread,)) for _ in range(nthreads)]
    start = time.perf_counter()
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    return time.perf_counter() - start


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cryptography", action="store_true")
    # Defaults sized so a single thread takes a second or so; a workload that
    # finishes in milliseconds measures scheduler noise, not scaling.
    ap.add_argument("--iterations", type=int, default=0)
    ap.add_argument("--max-threads", type=int, default=8)
    args = ap.parse_args()

    work = make_crypto_work() if args.cryptography else cpu_work
    per_thread = args.iterations or (20_000 if args.cryptography else 8_000_000)

    gil = getattr(sys, "_is_gil_enabled", lambda: True)()
    print(f"python {sys.version.split()[0]}  gil={'on' if gil else 'off'}")
    baseline = bench(work, 1, per_thread)
    print(f"{1:>2} thread   {baseline:6.2f}s   1.00x")
    n = 2
    while n <= args.max_threads:
        elapsed = bench(work, n, per_thread)
        print(f"{n:>2} threads  {elapsed:6.2f}s   {n * baseline / elapsed:.2f}x")
        n *= 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
