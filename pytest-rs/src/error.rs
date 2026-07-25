//! Error type shared by the non-Python parts of the engine.

use std::fmt;

#[derive(Debug)]
pub enum Error {
    /// Bad command line / configuration; reported like pytest's `UsageError`
    /// and mapped to exit code 4.
    Usage(String),
    /// Something went wrong internally.
    Internal(String),
    /// A Python exception escaped.
    Py(pyo3::PyErr),
}

impl Error {
    pub fn usage(msg: impl Into<String>) -> Self {
        Error::Usage(msg.into())
    }

    pub fn internal(msg: impl Into<String>) -> Self {
        Error::Internal(msg.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Usage(m) => write!(f, "{m}"),
            Error::Internal(m) => write!(f, "internal error: {m}"),
            Error::Py(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<pyo3::PyErr> for Error {
    fn from(e: pyo3::PyErr) -> Self {
        Error::Py(e)
    }
}

impl From<Error> for pyo3::PyErr {
    fn from(e: Error) -> Self {
        match e {
            Error::Py(p) => p,
            other => pyo3::exceptions::PyRuntimeError::new_err(other.to_string()),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;
