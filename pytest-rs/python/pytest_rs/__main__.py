"""Console entry point: ``pytest-rs`` and ``python -m pytest_rs``."""

from __future__ import annotations

import sys

from ._pytest_rs import main as _main


def main(argv: list[str] | None = None) -> int:
    if argv is None:
        argv = sys.argv[1:]
    return _main(list(argv))


if __name__ == "__main__":
    raise SystemExit(main())
