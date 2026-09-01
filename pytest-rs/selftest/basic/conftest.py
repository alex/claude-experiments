import pytest

SETUP_LOG: list[str] = []


def pytest_addoption(parser):
    parser.addoption("--custom-root", default=None)
    parser.addoption("--custom-flag", action="store_true")


def pytest_configure(config):
    SETUP_LOG.append(f"configure:{config.getoption('--custom-flag')}")


def pytest_report_header(config):
    return "selftest: header line"


def pytest_runtest_setup(item):
    for _ in item.iter_markers(name="needs_hook"):
        pytest.skip("skipped by pytest_runtest_setup")


@pytest.fixture
def simple():
    return "simple-value"


@pytest.fixture
def dependent(simple):
    return simple.upper()


@pytest.fixture
def generator_fixture():
    SETUP_LOG.append("gen-setup")
    yield "gen-value"
    SETUP_LOG.append("gen-teardown")


@pytest.fixture(scope="module")
def module_scoped():
    return object()


@pytest.fixture(scope="session")
def session_scoped():
    return object()


@pytest.fixture(params=["a", "b"])
def parametrized_fixture(request):
    return request.param


@pytest.fixture(autouse=True)
def autouse_marker(request):
    request.node.stash if False else None
    return None


@pytest.fixture(name="renamed")
def _renamed_impl():
    return "renamed-value"
