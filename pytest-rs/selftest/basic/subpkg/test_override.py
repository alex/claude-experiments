"""Fixture visibility and overriding: the conftest level."""


def test_conftest_override_chains(simple):
    # `subpkg/conftest.py` overrides `simple` and requests the wider one by the
    # same name; the override must resolve to the definition below it rather
    # than to itself.
    assert simple == "simple-value+subpkg"


def test_nested_conftest_fixture(only_here):
    assert only_here == "sub-only"


def test_root_fixture_still_visible(dependent):
    # `dependent` comes from the root conftest and asks for `simple`, which
    # resolves to the nearest override visible to this node id.
    assert dependent == "SIMPLE-VALUE+SUBPKG"
