//! Cross-run state: the randomisation seed and recorded test durations.
//!
//! Durations are what let the scheduler do longest-processing-time-first
//! ordering.  Without them the first run has to guess (it orders by group size),
//! but every run after that starts the expensive groups first, which is what
//! decides the makespan when a handful of tests dominate.

use rustc_hash::FxHashMap;
use std::path::{Path, PathBuf};

pub struct Cache {
    dir: PathBuf,
}

impl Cache {
    pub fn new(rootdir: &Path, cache_dir: &str) -> Self {
        let base = if cache_dir.is_empty() { ".pytest_cache" } else { cache_dir };
        let dir = if Path::new(base).is_absolute() {
            PathBuf::from(base)
        } else {
            rootdir.join(base)
        };
        Cache { dir: dir.join("pytest-rs") }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.dir.join(name)
    }

    fn write(&self, name: &str, contents: &str) {
        if std::fs::create_dir_all(&self.dir).is_err() {
            return;
        }
        let _ = std::fs::write(self.path(name), contents);
    }

    pub fn last_seed(&self) -> Option<u64> {
        std::fs::read_to_string(self.path("seed")).ok()?.trim().parse().ok()
    }

    pub fn store_seed(&self, seed: u64) {
        self.write("seed", &seed.to_string());
    }

    /// Load `nodeid -> seconds` recorded by a previous run.
    pub fn durations(&self) -> FxHashMap<String, f64> {
        let mut out = FxHashMap::default();
        let Ok(text) = std::fs::read_to_string(self.path("durations")) else { return out };
        for line in text.lines() {
            let Some((secs, nodeid)) = line.split_once('\t') else { continue };
            if let Ok(v) = secs.parse::<f64>() {
                out.insert(nodeid.to_string(), v);
            }
        }
        out
    }

    /// Record durations for the next run.  Only tests slow enough to matter for
    /// scheduling are kept, so the file stays small on large suites.
    pub fn store_durations(&self, entries: impl Iterator<Item = (String, f64)>) {
        const FLOOR: f64 = 0.002;
        let mut body = String::new();
        for (nodeid, secs) in entries {
            if secs < FLOOR {
                continue;
            }
            body.push_str(&format!("{secs:.6}\t{nodeid}\n"));
        }
        self.write("durations", &body);
    }
}
