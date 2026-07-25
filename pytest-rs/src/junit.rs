//! `--junitxml` report generation.
//!
//! Matches the shape pytest emits (`xunit2`), which is what CI systems parse:
//! one `<testsuite>` holding a `<testcase>` per test, with `<failure>`,
//! `<error>` or `<skipped>` children and the captured output attached.

use std::fmt::Write as _;

use crate::outcomes::Outcome;
use crate::report::TestReport;

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            // XML 1.0 forbids most control characters outright.
            c if (c as u32) < 0x20 && c != '\n' && c != '\r' && c != '\t' => {
                let _ = write!(out, "&#{};", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

/// `tests/foo/test_bar.py::TestX::test_y[p]` -> (`tests.foo.test_bar.TestX`, `test_y[p]`)
fn split_nodeid(nodeid: &str) -> (String, String) {
    let mut parts = nodeid.split("::");
    let file = parts.next().unwrap_or(nodeid);
    let rest: Vec<&str> = parts.collect();
    let module = file.trim_end_matches(".py").replace(['/', '\\'], ".");
    match rest.split_last() {
        Some((name, classes)) if !classes.is_empty() => {
            (format!("{module}.{}", classes.join(".")), (*name).to_string())
        }
        Some((name, _)) => (module, (*name).to_string()),
        None => (module, String::new()),
    }
}

/// Render the whole report set.
pub fn render(reports: &[TestReport], duration: f64, suite_name: &str) -> String {
    let count = |o: Outcome| reports.iter().filter(|r| r.outcome == o).count();
    let failures = count(Outcome::Failed);
    let errors = count(Outcome::Error);
    let skipped = count(Outcome::Skipped) + count(Outcome::XFailed);

    let mut out = String::with_capacity(reports.len() * 160);
    out.push_str("<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<testsuites>\n");
    let _ = write!(
        out,
        "  <testsuite name=\"{}\" errors=\"{errors}\" failures=\"{failures}\" skipped=\"{skipped}\" tests=\"{}\" time=\"{duration:.3}\">\n",
        escape(suite_name),
        reports.len()
    );
    for r in reports {
        let (classname, name) = split_nodeid(&r.nodeid);
        let total = r.setup_duration + r.duration + r.teardown_duration;
        let _ = write!(
            out,
            "    <testcase classname=\"{}\" name=\"{}\" time=\"{total:.3}\"",
            escape(&classname),
            escape(&name)
        );
        let body = child_element(r);
        let captured = captured_elements(r);
        if body.is_empty() && captured.is_empty() {
            out.push_str(" />\n");
            continue;
        }
        out.push_str(">\n");
        out.push_str(&body);
        out.push_str(&captured);
        out.push_str("    </testcase>\n");
    }
    out.push_str("  </testsuite>\n</testsuites>\n");
    out
}

fn child_element(r: &TestReport) -> String {
    match r.outcome {
        Outcome::Passed => String::new(),
        Outcome::Failed => format!(
            "      <failure message=\"{}\">{}</failure>\n",
            escape(&r.exconly),
            escape(&r.longrepr)
        ),
        Outcome::Error => format!(
            "      <error message=\"{}\">{}</error>\n",
            escape(&r.exconly),
            escape(&r.longrepr)
        ),
        Outcome::Skipped => format!(
            "      <skipped type=\"pytest.skip\" message=\"{}\">{}</skipped>\n",
            escape(&r.reason),
            escape(&format!("{}: {}", r.location, r.reason))
        ),
        Outcome::XFailed => format!(
            "      <skipped type=\"pytest.xfail\" message=\"{}\" />\n",
            escape(&r.reason)
        ),
        // An unexpected pass is a pass as far as CI is concerned.
        Outcome::XPassed => String::new(),
    }
}

fn captured_elements(r: &TestReport) -> String {
    let mut out = String::new();
    if !r.captured_out.is_empty() {
        let _ = write!(out, "      <system-out>{}</system-out>\n", escape(&r.captured_out));
    }
    if !r.captured_err.is_empty() {
        let _ = write!(out, "      <system-err>{}</system-err>\n", escape(&r.captured_err));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nodeid_splitting() {
        assert_eq!(
            split_nodeid("tests/foo/test_bar.py::TestX::test_y[p]"),
            ("tests.foo.test_bar.TestX".to_string(), "test_y[p]".to_string())
        );
        assert_eq!(
            split_nodeid("test_bar.py::test_y"),
            ("test_bar".to_string(), "test_y".to_string())
        );
    }

    #[test]
    fn escaping() {
        assert_eq!(escape("a<b&c\"d"), "a&lt;b&amp;c&quot;d");
        assert_eq!(escape("keep\nnewlines"), "keep\nnewlines");
        assert_eq!(escape("bell\x07"), "bell&#7;");
    }
}
