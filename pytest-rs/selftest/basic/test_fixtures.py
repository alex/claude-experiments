"""Fixture resolution: scopes, dependencies, finalisation, request API."""

import pytest


def test_simple_fixture(simple):
    assert simple == "simple-value"


def test_dependent_fixture(dependent):
    assert dependent == "SIMPLE-VALUE"


def test_generator_fixture(generator_fixture):
    assert generator_fixture == "gen-value"


def test_renamed_fixture(renamed):
    assert renamed == "renamed-value"


def test_parametrized_fixture(parametrized_fixture):
    assert parametrized_fixture in {"a", "b"}


_module_ids = []


def test_module_scope_first(module_scoped):
    _module_ids.append(id(module_scoped))


def test_module_scope_second(module_scoped):
    _module_ids.append(id(module_scoped))
    assert len(set(_module_ids)) == 1


_session_ids = []


def test_session_scope_first(session_scoped):
    _session_ids.append(id(session_scoped))


def test_session_scope_second(session_scoped):
    _session_ids.append(id(session_scoped))
    assert len(set(_session_ids)) == 1


def test_request_attributes(request):
    assert request.node.name == "test_request_attributes"
    assert request.node.nodeid.endswith("::test_request_attributes")
    assert request.config.getoption("--custom-root") is None
    assert request.function.__name__ == "test_request_attributes"
    assert "simple" in dir(request) or True


def test_getfixturevalue(request):
    assert request.getfixturevalue("simple") == "simple-value"


def test_addfinalizer(request):
    calls = []
    request.addfinalizer(lambda: calls.append(1))
    assert calls == []


def test_pytestconfig(pytestconfig):
    assert pytestconfig.getoption("--custom-root") is None


def test_tmp_path(tmp_path):
    p = tmp_path / "hello.txt"
    p.write_text("hi")
    assert p.read_text() == "hi"


def test_monkeypatch(monkeypatch):
    import os

    monkeypatch.setenv("PYTEST_RS_SELFTEST", "1")
    assert os.environ["PYTEST_RS_SELFTEST"] == "1"


def test_capsys(capsys):
    print("captured output")
    captured = capsys.readouterr()
    assert captured.out == "captured output\n"


def test_recwarn(recwarn):
    import warnings

    warnings.warn("recorded", UserWarning)
    assert len(recwarn) == 1


@pytest.mark.usefixtures("simple")
def test_usefixtures():
    assert True


@pytest.mark.needs_hook
def test_hook_skip():
    raise AssertionError("must not run")


class TestClassFixtures:
    @pytest.fixture
    def bound(self):
        return type(self).__name__

    @pytest.fixture(name="aliased")
    def _aliased(self):
        return "aliased-value"

    @staticmethod
    @pytest.fixture(scope="class", params=[1, 2])
    def static_param(request):
        return request.param

    def test_bound_fixture(self, bound):
        assert bound == "TestClassFixtures"

    def test_aliased_fixture(self, aliased):
        assert aliased == "aliased-value"

    def test_static_param(self, static_param):
        assert static_param in (1, 2)


def test_unknown_fixture(this_fixture_does_not_exist):
    assert False
