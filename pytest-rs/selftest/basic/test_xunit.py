"""xunit-style setup/teardown at module, function, class and method level.

The assertions are deliberately order-independent: each test checks that *its
own* setup ran last, and each setup checks that every previous setup at the same
level has already been torn down.  That catches a missing teardown without
depending on which order the scheduler picked.
"""

EVENTS = []


def _count(kind):
    return sum(1 for e in EVENTS if e[0] == kind)


def setup_module(module):
    assert module.__name__.endswith("test_xunit")
    EVENTS.append(("setup_module", module.__name__))


def teardown_module():
    EVENTS.append(("teardown_module", None))


def setup_function(function):
    assert _count("setup_function") == _count("teardown_function")
    EVENTS.append(("setup_function", function.__name__))


def teardown_function():
    EVENTS.append(("teardown_function", None))


def test_module_setup_ran_first():
    assert EVENTS[0][0] == "setup_module"


def test_function_setup_is_mine():
    assert EVENTS[-1] == ("setup_function", "test_function_setup_is_mine")


class TestXunitClass:
    @classmethod
    def setup_class(cls):
        EVENTS.append(("setup_class", cls.__name__))

    @classmethod
    def teardown_class(cls):
        EVENTS.append(("teardown_class", cls.__name__))

    def setup_method(self, method):
        assert _count("setup_method") == _count("teardown_method")
        EVENTS.append(("setup_method", method.__name__))

    def teardown_method(self, method):
        EVENTS.append(("teardown_method", method.__name__))

    def test_class_setup_ran(self):
        assert ("setup_class", "TestXunitClass") in EVENTS

    def test_method_setup_is_mine(self):
        assert EVENTS[-1] == ("setup_method", "test_method_setup_is_mine")

    def test_setup_function_does_not_apply_in_a_class(self):
        assert EVENTS[-1][0] == "setup_method"


class TestZeroArgumentForms:
    """pytest passes the module/class/method only if the function asks for it."""

    @classmethod
    def setup_class(cls):
        EVENTS.append(("setup_class", cls.__name__))

    def setup_method(self):
        EVENTS.append(("noargs_setup_method", None))

    def teardown_method(self):
        EVENTS.append(("noargs_teardown_method", None))

    def test_zero_argument_setup_method(self):
        assert EVENTS[-1] == ("noargs_setup_method", None)
