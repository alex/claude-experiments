"""A nested conftest, used to test fixture visibility and overriding."""

import pytest


@pytest.fixture
def simple(simple):
    """Override the root conftest's `simple`, building on the wider one."""
    return f"{simple}+subpkg"


@pytest.fixture
def only_here():
    return "sub-only"
