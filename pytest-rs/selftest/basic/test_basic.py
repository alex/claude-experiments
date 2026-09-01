"""Core behaviours: outcomes, markers, parametrisation, fixtures."""

import pytest


def test_passes():
    assert 1 + 1 == 2


def test_fails():
    assert 1 + 1 == 3


@pytest.mark.skip(reason="not today")
def test_skipped():
    raise AssertionError("must not run")


@pytest.mark.skipif(True, reason="conditional")
def test_skipped_if():
    raise AssertionError("must not run")


@pytest.mark.skipif(False, reason="conditional")
def test_conditional_false():
    assert True


@pytest.mark.xfail(reason="known bad")
def test_xfails():
    assert False


@pytest.mark.xfail(reason="fixed already")
def test_xpasses():
    assert True


@pytest.mark.xfail(reason="strict", strict=True)
def test_strict_xpass():
    assert True


def test_runtime_skip():
    pytest.skip("skipping at runtime")


def test_runtime_fail():
    pytest.fail("failing at runtime")


def test_runtime_xfail():
    pytest.xfail("xfailing at runtime")


@pytest.mark.parametrize("value", [1, 2, 3])
def test_parametrized(value):
    assert value > 0


@pytest.mark.parametrize("a", [1, 2])
@pytest.mark.parametrize("b", ["x", "y"])
def test_stacked_parametrize(a, b):
    assert a and b


@pytest.mark.parametrize(
    "value",
    [
        pytest.param(1, id="one"),
        pytest.param(2, marks=pytest.mark.skip(reason="param skip")),
        pytest.param(3, marks=pytest.mark.xfail(reason="param xfail")),
    ],
)
def test_param_objects(value):
    assert value != 3


@pytest.mark.parametrize("value", [b"\x00\xff", "text", None, True, 1.5, int])
def test_id_generation(value):
    assert True


class TestClass:
    def test_method(self):
        assert True

    @pytest.mark.parametrize("n", [1, 2])
    def test_method_parametrized(self, n):
        assert n

    class TestNested:
        def test_nested(self):
            assert True


def test_raises_context():
    with pytest.raises(ValueError, match="boom"):
        raise ValueError("boom goes the dynamite")


def test_raises_callable():
    excinfo = pytest.raises(KeyError, lambda: {}["missing"])
    assert excinfo.type is KeyError


def test_raises_did_not_raise():
    with pytest.raises(pytest.fail.Exception):
        with pytest.raises(ValueError):
            pass


def test_warns():
    import warnings

    with pytest.warns(UserWarning, match="careful"):
        warnings.warn("careful now", UserWarning)


def test_missing_module_guard():
    with pytest.raises(pytest.skip.Exception):
        pytest.importorskip("definitely_not_a_real_module_xyz")


def test_approx():
    assert 0.1 + 0.2 == pytest.approx(0.3)
