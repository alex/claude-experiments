"""Scheduling invariants that must hold whether or not workers are threaded."""

import threading

import pytest

_CONSTRUCTIONS = {"session": 0, "module": 0}
_LOCK = threading.Lock()


@pytest.fixture(scope="session")
def counted_session():
    with _LOCK:
        _CONSTRUCTIONS["session"] += 1
    return "session-value"


@pytest.fixture(scope="module")
def counted_module():
    with _LOCK:
        _CONSTRUCTIONS["module"] += 1
    return "module-value"


@pytest.mark.parametrize("i", range(12))
def test_session_fixture_built_once(counted_session, i):
    # However many workers pick these up, the session fixture is created under
    # a per-instance lock and therefore exactly once.
    assert counted_session == "session-value"
    assert _CONSTRUCTIONS["session"] == 1


@pytest.mark.parametrize("i", range(12))
def test_module_fixture_shared(counted_module, i):
    # Every test sharing a module scoped instance is placed in one serial
    # group, so they all see the same object and it is built once.
    assert counted_module == "module-value"
    assert _CONSTRUCTIONS["module"] == 1


_SEEN_THREADS = set()


@pytest.mark.parametrize("i", range(20))
def test_thread_affinity(i):
    _SEEN_THREADS.add(threading.get_ident())
    assert True


@pytest.mark.serial
def test_marked_serial():
    assert True


@pytest.mark.thread_safe
def test_marked_thread_safe():
    assert True


class TestClassScoped:
    @pytest.fixture(scope="class")
    def per_class(self):
        return object()

    def test_first(self, per_class):
        type(self)._seen = id(per_class)

    def test_second(self, per_class):
        assert getattr(type(self), "_seen", id(per_class)) == id(per_class)
