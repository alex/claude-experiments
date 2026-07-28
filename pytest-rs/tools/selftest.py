#!/usr/bin/env python3
"""Run the self-test corpus under pytest-rs and, when available, stock pytest.

Every test in ``selftest/`` has a name that declares its expected outcome, so
the harness can check the whole corpus without hard-coding a table:

* ``test_fail*`` / ``*_fails``   -> FAILED
* ``test_skip*`` / ``*_skipped`` -> SKIPPED
* ``*_xfail*``                   -> XFAIL
* ``*_xpass*``                   -> XPASS  (``strict_xpass`` -> FAILED)
* ``test_unknown_fixture``       -> ERROR
* anything else                  -> PASSED

Running the same corpus under stock pytest is what keeps the expectations
honest: if the two runners disagree, the harness says so.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

LINE = re.compile(r"^(?P<nodeid>\S+\.py::\S+)\s+(?P<outcome>[A-Z]+)")
ROOT = Path(__file__).resolve().parent.parent

# Tests that are *meant* to behave differently under the two runners, with the
# reason.  Anything else that diverges is a compatibility bug.
KNOWN_DIVERGENCES = {
    "test_capture.py::test_capture_is_per_thread": (
        "pytest captures process-globally, so a helper thread's output leaks "
        "into the test's buffer; pytest-rs keys buffers by thread"
    ),
}


def expected_outcome(nodeid: str) -> str:
    name = nodeid.rsplit("::", 1)[-1]
    base = name.split("[", 1)[0]
    if base == "test_unknown_fixture":
        return "ERROR"
    if base == "test_strict_xpass":
        return "FAILED"
    if "xfail" in base:
        return "XFAIL"
    if "xpass" in base:
        return "XPASS"
    if "fail" in base:
        return "FAILED"
    if "skip" in base:
        return "SKIPPED"
    # `pytest.param(marks=...)` cases carry their expectation in the id.
    if "[2]" in name and base == "test_param_objects":
        return "SKIPPED"
    if "[3]" in name and base == "test_param_objects":
        return "XFAIL"
    return "PASSED"


def parse(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in text.splitlines():
        m = LINE.match(line.strip())
        if m and m.group("outcome") in {
            "PASSED",
            "FAILED",
            "SKIPPED",
            "ERROR",
            "XFAIL",
            "XPASS",
        }:
            out[m.group("nodeid")] = m.group("outcome")
    return out


def run(cmd: list[str], cwd: Path) -> str:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.stdout + proc.stderr


def check(label: str, results: dict[str, str], reference: bool = False) -> int:
    if not results:
        print(f"{label}: no results parsed", file=sys.stderr)
        return 1
    bad = 0
    for nodeid, outcome in sorted(results.items()):
        want = expected_outcome(nodeid)
        if reference and nodeid in KNOWN_DIVERGENCES:
            continue
        if outcome != want:
            print(f"  ! {nodeid}: expected {want}, got {outcome}")
            bad += 1
    print(f"{label}: {len(results)} tests, {bad} unexpected")
    return 1 if bad else 0


def check_last_failed(pytest_rs: str, corpus: Path) -> int:
    """A full run, then `--lf`, must come back with exactly the failures."""
    common = ["-v", "--tb=no", "-p", "no:randomly"]
    subprocess.run([pytest_rs, *common, "--cache-clear"], cwd=corpus, capture_output=True, text=True)
    first = parse(run([pytest_rs, *common], corpus))
    expected = {n for n, o in first.items() if o in {"FAILED", "ERROR"}}
    second = parse(run([pytest_rs, *common, "--lf"], corpus))
    if set(second) != expected:
        missing = sorted(expected - set(second))
        extra = sorted(set(second) - expected)
        for n in missing:
            print(f"  ! --lf did not rerun {n}")
        for n in extra:
            print(f"  ! --lf reran {n}, which passed")
        return 1
    print(f"--lf      : reran exactly the {len(expected)} failing tests")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pytest-rs", default="pytest-rs")
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--skip-pytest", action="store_true")
    ap.add_argument("--threads", default="0", help="value for -n")
    args = ap.parse_args()

    corpus = ROOT / "selftest" / "basic"
    common = ["-v", "--tb=no", "-p", "no:randomly"]

    status = 0
    rs = parse(run([args.pytest_rs, *common, "-n", args.threads], corpus))
    status |= check("pytest-rs", rs)

    if not args.skip_pytest:
        try:
            ref = parse(run([args.python, "-m", "pytest", *common], corpus))
        except FileNotFoundError:
            ref = {}
        if ref:
            status |= check("pytest   ", ref, reference=True)
            differing = sorted(
                n for n in set(rs) & set(ref) if rs[n] != ref[n] and n not in KNOWN_DIVERGENCES
            )
            expected_divergences = sorted(
                n for n in set(rs) & set(ref) if rs[n] != ref[n] and n in KNOWN_DIVERGENCES
            )
            only_rs = sorted(set(rs) - set(ref))
            only_py = sorted(set(ref) - set(rs))
            for n in expected_divergences:
                print(f"  ~ expected divergence {n}: {KNOWN_DIVERGENCES[n]}")
            for n in differing:
                print(f"  ! divergence {n}: pytest={ref[n]} pytest-rs={rs[n]}")
            for n in only_rs:
                print(f"  + only pytest-rs collected {n}")
            for n in only_py:
                print(f"  - only pytest collected {n}")
            if differing or only_rs or only_py:
                status |= 1
            else:
                print("runners agree on every test")
    status |= check_last_failed(args.pytest_rs, corpus)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
