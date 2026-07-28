#!/usr/bin/env python3
"""Compare pytest-rs against stock pytest on a real test suite.

Runs both runners over the same target with per-test verbose reporting, then
diffs the collected node ids and the per-test outcomes.  Any divergence is a
compatibility bug in pytest-rs.

    python tools/compare_with_pytest.py /path/to/project -- -k something

The pytest interpreter defaults to the one running this script; override with
``--python``.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

# `nodeid OUTCOME [ nn%]`, as printed at verbosity >= 1 by both runners.
LINE = re.compile(r"^(?P<nodeid>\S+::\S*|\S+\.py::\S*)\s+(?P<outcome>[A-Z]+)")
OUTCOME_ALIASES = {"XPASS": "XPASS", "XFAIL": "XFAIL"}


def run(cmd: list[str], cwd: Path) -> str:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.stdout + proc.stderr


def parse_outcomes(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in text.splitlines():
        m = LINE.match(line.strip())
        if not m:
            continue
        outcome = m.group("outcome")
        if outcome not in {"PASSED", "FAILED", "SKIPPED", "ERROR", "XFAIL", "XPASS"}:
            continue
        out[m.group("nodeid")] = OUTCOME_ALIASES.get(outcome, outcome)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("project", type=Path)
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--pytest-rs", default="pytest-rs")
    ap.add_argument("extra", nargs="*", help="extra arguments passed to both runners")
    args = ap.parse_args()

    common = ["-v", "--tb=no", "-p", "no:randomly", *args.extra]

    print("running stock pytest ...", flush=True)
    ref = parse_outcomes(run([args.python, "-m", "pytest", *common], args.project))
    print(f"  {len(ref)} results")

    print("running pytest-rs ...", flush=True)
    ours = parse_outcomes(run([args.pytest_rs, *common], args.project))
    print(f"  {len(ours)} results")

    missing = sorted(set(ref) - set(ours))
    extra = sorted(set(ours) - set(ref))
    differing = sorted(n for n in set(ref) & set(ours) if ref[n] != ours[n])

    if missing:
        print(f"\n{len(missing)} node id(s) collected by pytest but not by pytest-rs:")
        for n in missing[:40]:
            print(f"  - {n}")
    if extra:
        print(f"\n{len(extra)} node id(s) collected by pytest-rs but not by pytest:")
        for n in extra[:40]:
            print(f"  + {n}")
    if differing:
        print(f"\n{len(differing)} outcome mismatch(es):")
        for n in differing[:40]:
            print(f"  ! {n}: pytest={ref[n]} pytest-rs={ours[n]}")

    if not (missing or extra or differing):
        print(f"\nidentical: {len(ref)} tests, same node ids, same outcomes")
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
