"""Output capturing, including under the thread pool.

These run with capturing on (the corpus is invoked without ``-s``), so anything
printed here must land in the per-thread buffer rather than on the terminal.
"""

import sys
import threading

import pytest


def test_capsys_roundtrip(capsys):
    print("to stdout")
    print("to stderr", file=sys.stderr)
    captured = capsys.readouterr()
    assert captured.out == "to stdout\n"
    assert captured.err == "to stderr\n"


def test_capsys_clears_between_reads(capsys):
    print("first")
    assert capsys.readouterr().out == "first\n"
    print("second")
    assert capsys.readouterr().out == "second\n"


def test_capsys_empty(capsys):
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""


def test_capfd_roundtrip(capfd):
    print("through capfd")
    assert capfd.readouterr().out == "through capfd\n"


def test_capsys_disabled(capsys):
    with capsys.disabled():
        pass
    print("after")
    assert capsys.readouterr().out == "after\n"


def test_capture_is_per_thread(capsys):
    # A helper thread writes to stdout while this test is capturing.  Buffers
    # are keyed by thread, so the helper's output must not leak into ours.
    def helper():
        print("from helper thread")

    t = threading.Thread(target=helper)
    t.start()
    t.join()
    print("from test thread")
    assert capsys.readouterr().out == "from test thread\n"


@pytest.mark.parametrize("n", range(8))
def test_capture_under_parallelism(capsys, n):
    # Run under `-n` with several of these in flight at once; each must see
    # only its own output.
    print(f"marker-{n}")
    assert capsys.readouterr().out == f"marker-{n}\n"
