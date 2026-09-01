"""`unittest.TestCase` collection and the outcomes unittest reports itself."""

import unittest

import pytest

EVENTS = []


class TestCaseBasics(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        EVENTS.append(("setUpClass", cls.__name__))

    @classmethod
    def tearDownClass(cls):
        EVENTS.append(("tearDownClass", cls.__name__))

    def setUp(self):
        self.value = 21

    def test_assert_method(self):
        self.assertEqual(self.value * 2, 42)

    def test_class_setup_ran(self):
        # `setUpClass` is inherited, so the subclass below records its own name.
        assert ("setUpClass", type(self).__name__) in EVENTS

    def test_cleanup_runs(self):
        self.addCleanup(EVENTS.append, ("cleanup", "test_cleanup_runs"))

    def test_fail_assert_method(self):
        self.assertEqual(1, 2)

    def test_fail_bare_assert(self):
        assert 1 == 2

    def test_fail_error(self):
        raise RuntimeError("boom")

    @unittest.skip("decorated")
    def test_skip_decorator(self):
        raise AssertionError("never runs")

    def test_skip_inline(self):
        self.skipTest("inline")

    @unittest.skipIf(True, "conditional")
    def test_skip_if(self):
        raise AssertionError("never runs")

    @unittest.expectedFailure
    def test_xfail_expected_failure(self):
        assert False

    @unittest.expectedFailure
    def test_fail_unexpected_success(self):
        assert True

    @pytest.mark.skip(reason="pytest markers still apply")
    def test_skip_pytest_marker(self):
        raise AssertionError("never runs")

    def helper_is_not_a_test(self):
        raise AssertionError("never runs")


@unittest.skip("the whole class")
class TestCaseSkippedClass(unittest.TestCase):
    def test_skipped_with_its_class(self):
        raise AssertionError("never runs")


class TestCaseInheritance(TestCaseBasics):
    """Inherited test methods are collected again under the subclass."""

    def test_subclass_sees_setup(self):
        assert self.value == 21


class NotNamedLikeATest(unittest.TestCase):
    """`python_classes` does not apply to TestCase subclasses."""

    def test_collected_anyway(self):
        assert True


class TestCaseWithFixtures(unittest.TestCase):
    """Fixtures reach a TestCase through `usefixtures`, not through arguments."""

    @pytest.fixture(autouse=True)
    def _inject(self, tmp_path):
        self.tmp = tmp_path

    def test_autouse_fixture_ran(self):
        assert self.tmp.is_dir()
