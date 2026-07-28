"""A class-level override, visible only inside the class."""

import pytest


class TestClassOverride:
    @pytest.fixture
    def simple(self, simple):
        return f"{simple}+class"

    def test_class_override_chains(self, simple):
        assert simple == "simple-value+subpkg+class"


def test_outside_class_is_unaffected(simple):
    assert simple == "simple-value+subpkg"
