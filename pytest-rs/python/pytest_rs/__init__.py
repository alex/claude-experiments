"""pytest-rs: a pytest-compatible test runner implemented in Rust with pyo3.

Importing this package does not install the ``pytest`` shim; that happens when
a session starts, so that a real pytest installation in the same environment
stays usable.
"""

from ._pytest_rs import __version__, main, version

__all__ = ["__version__", "main", "version"]
