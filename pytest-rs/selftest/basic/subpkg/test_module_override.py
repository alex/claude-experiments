"""A module-level override, which applies to every test in this module."""

import pytest


@pytest.fixture
def simple(simple):
    return f"{simple}+module"


def test_module_override_chains(simple):
    assert simple == "simple-value+subpkg+module"


def test_module_override_applies_to_dependents(dependent):
    assert dependent == "SIMPLE-VALUE+SUBPKG+MODULE"
