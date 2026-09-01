//! Terminal reporting.

use std::io::{IsTerminal, Write};

use pyo3::prelude::*;

use crate::outcomes::Outcome;
use crate::session::ConfigData;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum When {
    Setup,
    Call,
    Teardown,
}

impl When {
    pub fn as_str(self) -> &'static str {
        match self {
            When::Setup => "setup",
            When::Call => "call",
            When::Teardown => "teardown",
        }
    }
}

#[derive(Clone)]
pub struct TestReport {
    pub index: usize,
    pub nodeid: String,
    pub relpath: String,
    pub outcome: Outcome,
    pub when: When,
    pub duration: f64,
    pub setup_duration: f64,
    pub teardown_duration: f64,
    pub longrepr: String,
    /// One-line description used by the short summary.
    pub exconly: String,
    pub reason: String,
    /// `path:line` used by the `-r s` summary.
    pub location: String,
    pub bench: Option<crate::bench::BenchResult>,
    pub worker: usize,
    /// Output written by the test, replayed when it fails.
    pub captured_out: String,
    pub captured_err: String,
}

pub struct Colors {
    pub enabled: bool,
}

impl Colors {
    pub fn wrap(&self, code: &str, text: &str) -> String {
        if !self.enabled {
            return text.to_string();
        }
        format!("\x1b[{code}m{text}\x1b[0m")
    }
    pub fn green(&self, t: &str) -> String {
        self.wrap("32", t)
    }
    pub fn red(&self, t: &str) -> String {
        self.wrap("31", t)
    }
    pub fn yellow(&self, t: &str) -> String {
        self.wrap("33", t)
    }
    pub fn bold(&self, t: &str) -> String {
        self.wrap("1", t)
    }
}

/// How the per-test progress indicator is rendered.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ProgressStyle {
    None,
    Percent,
    Count,
}

pub struct Terminal {
    pub width: usize,
    pub colors: Colors,
    pub verbosity: i64,
    pub progress: ProgressStyle,
    /// Characters written on the current line.
    col: usize,
    written: usize,
    total: usize,
    out: std::io::Stdout,
    /// Current file prefix in serial mode.
    current_file: Option<String>,
    parallel: bool,
    is_tty: bool,
}

/// Terminal width, in the order `shutil.get_terminal_size` uses.
pub fn terminal_width(py: Python<'_>) -> usize {
    if let Ok(cols) = std::env::var("COLUMNS") {
        if let Ok(n) = cols.parse::<usize>() {
            return n;
        }
    }
    py.import("shutil")
        .and_then(|m| m.call_method0("get_terminal_size"))
        .and_then(|size| size.getattr("columns"))
        .and_then(|c| c.extract::<usize>())
        .unwrap_or(80)
        .clamp(40, 200)
}

impl Terminal {
    pub fn new(cfg: &ConfigData, total: usize, parallel: bool, capture_disabled: bool, width: usize) -> Self {
        let color_opt = cfg.str_opt("color");
        let is_tty = std::io::stdout().is_terminal();
        let enabled = match color_opt.as_str() {
            "yes" | "always" => true,
            "no" | "never" => false,
            _ => is_tty && std::env::var("NO_COLOR").is_err(),
        };
        // pytest hides the percentage when output is not captured, unless the
        // style explicitly opts back in.
        let style = cfg.ini_str("console_output_style");
        let progress = match style.as_str() {
            "classic" => ProgressStyle::None,
            "count" => ProgressStyle::Count,
            "progress-even-when-capture-no" => ProgressStyle::Percent,
            _ if capture_disabled => ProgressStyle::None,
            _ => ProgressStyle::Percent,
        };
        Terminal {
            width,
            colors: Colors { enabled },
            verbosity: cfg.verbosity(),
            progress,
            col: 0,
            written: 0,
            total,
            out: std::io::stdout(),
            current_file: None,
            parallel,
            is_tty,
        }
    }

    pub fn write(&mut self, s: &str) {
        let _ = self.out.write_all(s.as_bytes());
        if let Some(pos) = s.rfind('\n') {
            self.col = s.len() - pos - 1;
        } else {
            self.col += s.len();
        }
    }

    pub fn line(&mut self, s: &str) {
        if self.col > 0 {
            self.write("\n");
        }
        self.write(s);
        self.write("\n");
    }

    pub fn flush(&mut self) {
        let _ = self.out.flush();
    }

    /// Flush only when someone is watching.  Live progress matters on a
    /// terminal; into a pipe it would be one syscall per test for nothing.
    pub fn flush_progress(&mut self) {
        if self.is_tty {
            let _ = self.out.flush();
        }
    }

    /// `====== title ======` centred to the terminal width.
    pub fn section(&mut self, title: &str, sep: char, bold: bool) {
        let text = if title.is_empty() {
            sep.to_string().repeat(self.width)
        } else {
            let deco = format!(" {title} ");
            let n = self.width.saturating_sub(deco.len());
            let left = n / 2;
            let right = n - left;
            format!("{}{}{}", sep.to_string().repeat(left), deco, sep.to_string().repeat(right))
        };
        let text = if bold { self.colors.bold(&text) } else { text };
        self.line(&text);
    }

    fn progress_suffix(&self) -> String {
        if self.total == 0 {
            return String::new();
        }
        match self.progress {
            ProgressStyle::None => String::new(),
            ProgressStyle::Percent => {
                let pct = self.written * 100 / self.total;
                format!(" [{pct:>3}%]")
            }
            ProgressStyle::Count => {
                let width = self.total.to_string().len();
                format!(" [{:>width$}/{}]", self.written, self.total)
            }
        }
    }

    /// Emit the per-test progress indicator.
    pub fn report(&mut self, r: &TestReport) {
        self.written += 1;
        if self.verbosity >= 1 {
            let word = match r.outcome {
                Outcome::Passed => self.colors.green(r.outcome.word()),
                Outcome::Failed | Outcome::Error => self.colors.red(r.outcome.word()),
                _ => self.colors.yellow(r.outcome.word()),
            };
            let suffix = self.progress_suffix();
            let text = format!("{} {}{}", r.nodeid, word, suffix);
            self.line(&text);
            return;
        }
        // Compact mode: one character per test.
        if !self.parallel && self.current_file.as_deref() != Some(r.relpath.as_str()) {
            if self.col > 0 {
                let suffix = self.progress_suffix();
                let pad = self.width.saturating_sub(self.col + suffix.len());
                self.write(&" ".repeat(pad.min(self.width)));
                self.write(&suffix);
                self.write("\n");
            }
            self.current_file = Some(r.relpath.clone());
            self.write(&format!("{} ", r.relpath));
        }
        let ch = r.outcome.letter().to_string();
        let ch = match r.outcome {
            Outcome::Passed => self.colors.green(&ch),
            Outcome::Failed | Outcome::Error => self.colors.red(&ch),
            _ => self.colors.yellow(&ch),
        };
        self.write(&ch);
        let limit = self.width.saturating_sub(8);
        if self.col >= limit {
            let suffix = self.progress_suffix();
            self.write(&suffix);
            self.write("\n");
        }
    }

    pub fn finish_progress(&mut self) {
        if self.col > 0 {
            let suffix = self.progress_suffix();
            let pad = self.width.saturating_sub(self.col + suffix.len());
            self.write(&" ".repeat(pad.min(self.width)));
            self.write(&suffix);
            self.write("\n");
        }
    }
}

/// Format a duration the way pytest does in the final line.
pub fn format_duration(secs: f64) -> String {
    if secs < 60.0 {
        format!("{secs:.2}s")
    } else {
        let mins = (secs / 60.0).floor();
        let rem = secs - mins * 60.0;
        format!("{mins:.0}:{rem:05.2}")
    }
}

/// Build the `4015 passed, 647 skipped` fragment.
pub fn outcome_summary(counts: &[(Outcome, usize)]) -> Vec<(String, Outcome)> {
    let order = [
        Outcome::Failed,
        Outcome::Error,
        Outcome::Passed,
        Outcome::Skipped,
        Outcome::XFailed,
        Outcome::XPassed,
    ];
    let mut parts = Vec::new();
    for o in order {
        let n: usize = counts.iter().filter(|(x, _)| *x == o).map(|(_, c)| *c).sum();
        if n == 0 {
            continue;
        }
        let word = match o {
            Outcome::Passed => "passed",
            Outcome::Failed => "failed",
            Outcome::Skipped => "skipped",
            Outcome::XFailed => "xfailed",
            Outcome::XPassed => "xpassed",
            Outcome::Error => {
                if n == 1 {
                    "error"
                } else {
                    "errors"
                }
            }
        };
        parts.push((format!("{n} {word}"), o));
    }
    parts
}
