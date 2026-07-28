#!/usr/bin/env python3
"""Time pytest-rs against stock pytest (and pytest-xdist) on a project.

    python tools/benchmark.py /path/to/project --repeat 3
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

SUMMARY = re.compile(r"^=+ (.*) in [\d.]+s? =+$")


def timed(cmd: list[str], cwd: Path) -> tuple[float, str]:
    start = time.perf_counter()
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    elapsed = time.perf_counter() - start
    summary = ""
    for line in reversed((proc.stdout + proc.stderr).splitlines()):
        m = SUMMARY.match(line.strip())
        if m:
            summary = m.group(1)
            break
    return elapsed, summary


def best_of(cmd: list[str], cwd: Path, repeat: int) -> tuple[float, str]:
    best = float("inf")
    summary = ""
    for _ in range(repeat):
        elapsed, s = timed(cmd, cwd)
        if elapsed < best:
            best, summary = elapsed, s
    return best, summary


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("project", type=Path)
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--pytest-rs", default="pytest-rs")
    ap.add_argument("--repeat", type=int, default=1)
    ap.add_argument("--threads", default="4")
    args = ap.parse_args()

    quiet = ["-q", "-p", "no:randomly"]
    cases: list[tuple[str, list[str]]] = [
        ("pytest collect", [args.python, "-m", "pytest", "--collect-only", *quiet]),
        ("pytest-rs collect", [args.pytest_rs, "--collect-only", *quiet]),
        ("pytest serial", [args.python, "-m", "pytest", *quiet]),
        (f"pytest xdist -n {args.threads}", [args.python, "-m", "pytest", *quiet, "-n", args.threads]),
        ("pytest-rs serial", [args.pytest_rs, *quiet, "--no-parallel"]),
        (f"pytest-rs -n {args.threads}", [args.pytest_rs, *quiet, "-n", args.threads]),
    ]

    width = max(len(name) for name, _ in cases)
    for name, cmd in cases:
        try:
            elapsed, summary = best_of(cmd, args.project, args.repeat)
        except FileNotFoundError as exc:
            print(f"{name:<{width}}  skipped ({exc})")
            continue
        print(f"{name:<{width}}  {elapsed:6.2f}s   {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
