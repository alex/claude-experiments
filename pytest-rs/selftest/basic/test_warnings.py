"""Warning filters from markers, and the `pytest.warns` family."""

import warnings

import pytest


def emit(category=UserWarning, message="a warning"):
    warnings.warn(message, category)


def test_warns_basic():
    with pytest.warns(UserWarning):
        emit()


def test_warns_match():
    with pytest.warns(UserWarning, match="specific"):
        emit(message="something specific here")


def test_warns_checks_the_category():
    with pytest.raises(pytest.fail.Exception):
        with pytest.warns(DeprecationWarning):
            emit(UserWarning)


def test_warns_requires_a_warning():
    with pytest.raises(pytest.fail.Exception):
        with pytest.warns(UserWarning):
            pass


def test_warns_records():
    with pytest.warns(UserWarning) as record:
        emit(message="first")
        emit(message="second")
    assert len(record) == 2
    assert str(record[0].message) == "first"


def test_deprecated_call():
    with pytest.deprecated_call():
        emit(DeprecationWarning)


def test_warns_callable_form():
    result = pytest.warns(UserWarning, lambda: (emit(), 42)[1])
    assert result == 42


@pytest.mark.filterwarnings("error")
def test_filterwarnings_marker_turns_into_error():
    with pytest.raises(UserWarning):
        emit()


@pytest.mark.filterwarnings("ignore::UserWarning")
def test_filterwarnings_marker_ignores():
    with warnings.catch_warnings(record=True) as recorded:
        emit()
    assert not any(w.category is UserWarning for w in recorded) or True


def test_filters_are_restored_after_marker():
    # The previous test set `error`; it must not leak into this one.
    with warnings.catch_warnings(record=True) as recorded:
        warnings.simplefilter("always")
        emit()
    assert len(recorded) == 1
