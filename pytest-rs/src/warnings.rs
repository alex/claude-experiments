//! Warning filters: the `filterwarnings` ini option, `-W`, and
//! `@pytest.mark.filterwarnings`.
//!
//! pytest's filter spec is argparse's `-W` syntax with a pytest twist: the
//! category may be a dotted import path rather than a builtin name.

use pyo3::prelude::*;
use pyo3::types::PyDict;

/// Filters pytest installs before the user's, so deprecations from the code
/// under test are visible by default.
const DEFAULTS: &[&str] = &["always::DeprecationWarning", "always::PendingDeprecationWarning"];

/// Apply one `action:message:category:module:lineno` spec.
pub fn apply_spec(py: Python<'_>, spec: &str) -> PyResult<()> {
    let warnings = py.import("warnings")?;
    if spec == "error" || spec == "ignore" || spec == "always" || spec == "default" || spec == "module" || spec == "once" {
        warnings.call_method1("simplefilter", (spec,))?;
        return Ok(());
    }
    let parts: Vec<&str> = spec.splitn(5, ':').collect();
    let action = parts.first().copied().unwrap_or("default");
    let message = parts.get(1).copied().unwrap_or("");
    let category_name = parts.get(2).copied().unwrap_or("");
    let module = parts.get(3).copied().unwrap_or("");
    let lineno: i32 = parts.get(4).and_then(|s| s.parse().ok()).unwrap_or(0);

    let category = resolve_category(py, category_name)?;
    let kwargs = PyDict::new(py);
    kwargs.set_item("action", action)?;
    kwargs.set_item("message", message)?;
    kwargs.set_item("category", category)?;
    kwargs.set_item("module", module)?;
    kwargs.set_item("lineno", lineno)?;
    kwargs.set_item("append", true)?;
    warnings.call_method("filterwarnings", (), Some(&kwargs))?;
    Ok(())
}

fn resolve_category<'py>(py: Python<'py>, name: &str) -> PyResult<Bound<'py, PyAny>> {
    let builtins = py.import("builtins")?;
    if name.is_empty() {
        return builtins.getattr("Warning");
    }
    if let Ok(c) = builtins.getattr(name) {
        return Ok(c);
    }
    // Dotted path: `mypkg.warnings.MyWarning`.
    if let Some((modname, attr)) = name.rsplit_once('.') {
        if let Ok(module) = py.import(modname) {
            if let Ok(c) = module.getattr(attr) {
                return Ok(c);
            }
        }
    }
    builtins.getattr("Warning")
}

/// Install the session-wide filters: pytest's defaults, then `filterwarnings`
/// from the ini file, then `-W` from the command line (later wins).
pub fn install_session_filters(py: Python<'_>, ini: &[String], cmdline: &[String]) -> PyResult<()> {
    for spec in DEFAULTS {
        apply_spec(py, spec)?;
    }
    for spec in ini {
        apply_spec(py, spec)?;
    }
    for spec in cmdline {
        apply_spec(py, spec)?;
    }
    Ok(())
}

/// A `warnings.catch_warnings()` block scoped to one test, used to apply
/// `@pytest.mark.filterwarnings`.
pub struct Scoped {
    catcher: Py<PyAny>,
}

impl Scoped {
    pub fn enter(py: Python<'_>, specs: &[String]) -> PyResult<Option<Scoped>> {
        if specs.is_empty() {
            return Ok(None);
        }
        let warnings = py.import("warnings")?;
        let catcher = warnings.call_method0("catch_warnings")?;
        catcher.call_method0("__enter__")?;
        for spec in specs {
            apply_spec(py, spec)?;
        }
        Ok(Some(Scoped { catcher: catcher.unbind() }))
    }

    pub fn exit(self, py: Python<'_>) {
        let none = py.None();
        let _ = self
            .catcher
            .bind(py)
            .call_method1("__exit__", (none.clone_ref(py), none.clone_ref(py), none));
    }
}

/// Collect the specs contributed by `@pytest.mark.filterwarnings` markers.
pub fn marker_specs(py: Python<'_>, marks: &[crate::marks::MarkData]) -> Vec<String> {
    let mut out = Vec::new();
    for m in marks.iter().rev() {
        if m.name != "filterwarnings" {
            continue;
        }
        for a in m.args.bind(py).iter() {
            if let Ok(s) = a.extract::<String>() {
                out.push(s);
            }
        }
    }
    out
}
