//! Configuration: rootdir/inifile discovery, ini parsing, and command line parsing.
//!
//! This mirrors the parts of `_pytest.config` that the supported test suites
//! actually exercise: ini discovery from `pyproject.toml`/`pytest.ini`/`tox.ini`/
//! `setup.cfg`, `addopts` splicing, and a two phase argument parser so that
//! `conftest.py`'s `pytest_addoption` hook can register new options before the
//! final parse.

use std::collections::BTreeMap;
use std::path::{Component, Path, PathBuf};

use crate::error::{Error, Result};

/// How an option consumes values from the command line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptKind {
    /// `--flag` — stores `true`.
    StoreTrue,
    /// `--flag` — stores `false`.
    StoreFalse,
    /// `--flag=value` / `--flag value`.
    Store,
    /// `--flag=value`, repeatable, accumulates into a list.
    Append,
    /// `-v` — increments an integer.
    Count,
    /// `--flag[=value]` — value is optional.
    OptionalStore,
}

/// Type coercion applied to a stored value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptType {
    Str,
    Int,
    Float,
    Bool,
}

#[derive(Clone, Debug)]
pub struct OptionSpec {
    pub names: Vec<String>,
    pub dest: String,
    pub kind: OptKind,
    pub ty: OptType,
    pub default: Value,
    /// Value used when an `OptionalStore` option is given without a value.
    pub const_value: Option<Value>,
    pub help: String,
    /// Heading this option appears under in `--help`.
    pub group: &'static str,
    /// Restrict values to this set (argparse `choices`).
    pub choices: Option<Vec<String>>,
}

impl OptionSpec {
    pub fn new(names: &[&str], kind: OptKind) -> Self {
        let dest = default_dest(names);
        OptionSpec {
            names: names.iter().map(|s| s.to_string()).collect(),
            dest,
            kind,
            ty: OptType::Str,
            default: match kind {
                OptKind::StoreTrue => Value::Bool(false),
                OptKind::StoreFalse => Value::Bool(true),
                OptKind::Count => Value::Int(0),
                OptKind::Append => Value::List(Vec::new()),
                _ => Value::None,
            },
            const_value: None,
            help: String::new(),
            group: "general",
            choices: None,
        }
    }

    pub fn group(mut self, g: &'static str) -> Self {
        self.group = g;
        self
    }

    pub fn dest(mut self, dest: &str) -> Self {
        self.dest = dest.to_string();
        self
    }

    pub fn default(mut self, v: Value) -> Self {
        self.default = v;
        self
    }

    pub fn ty(mut self, t: OptType) -> Self {
        self.ty = t;
        self
    }

    pub fn const_value(mut self, v: Value) -> Self {
        self.const_value = Some(v);
        self
    }

    pub fn help(mut self, h: &str) -> Self {
        self.help = h.to_string();
        self
    }
}

/// Derive an argparse-style `dest` from the option strings.
fn default_dest(names: &[&str]) -> String {
    let long = names.iter().find(|n| n.starts_with("--")).or(names.first());
    let n = long.copied().unwrap_or("");
    n.trim_start_matches('-').replace('-', "_")
}

/// A dynamically typed option value.  Mirrors what argparse would hand back to
/// Python code via `config.getoption()`.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    None,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(String),
    List(Vec<Value>),
}

impl Value {
    pub fn as_bool(&self) -> bool {
        match self {
            Value::None => false,
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Float(f) => *f != 0.0,
            Value::Str(s) => !s.is_empty(),
            Value::List(l) => !l.is_empty(),
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(i) => Some(*i),
            Value::Float(f) => Some(*f as i64),
            Value::Str(s) => s.parse().ok(),
            Value::Bool(b) => Some(*b as i64),
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Value::Int(i) => Some(*i as f64),
            Value::Float(f) => Some(*f),
            Value::Str(s) => s.parse().ok(),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Vec<Value> {
        match self {
            Value::List(l) => l.clone(),
            Value::None => Vec::new(),
            other => vec![other.clone()],
        }
    }

    pub fn str_list(&self) -> Vec<String> {
        self.as_list()
            .into_iter()
            .filter_map(|v| match v {
                Value::Str(s) => Some(s),
                Value::None => None,
                other => Some(format!("{other:?}")),
            })
            .collect()
    }
}

fn coerce(ty: OptType, raw: &str) -> Result<Value> {
    Ok(match ty {
        OptType::Str => Value::Str(raw.to_string()),
        OptType::Int => Value::Int(
            raw.parse()
                .map_err(|_| Error::usage(format!("invalid int value: '{raw}'")))?,
        ),
        OptType::Float => Value::Float(
            raw.parse()
                .map_err(|_| Error::usage(format!("invalid float value: '{raw}'")))?,
        ),
        OptType::Bool => Value::Bool(matches!(
            raw.to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "on"
        )),
    })
}

/// The set of ini option declarations we understand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IniType {
    /// Whitespace/newline separated list of strings.
    Args,
    /// Newline separated list of strings (`markers`, `filterwarnings`).
    LineList,
    /// Colon separated list of paths.
    Paths,
    Str,
    Bool,
    Int,
}

pub struct IniSpec {
    pub name: &'static str,
    pub ty: IniType,
    pub default: &'static str,
}

pub const INI_SPECS: &[IniSpec] = &[
    IniSpec { name: "addopts", ty: IniType::Args, default: "" },
    IniSpec { name: "minversion", ty: IniType::Str, default: "" },
    IniSpec { name: "required_plugins", ty: IniType::Args, default: "" },
    IniSpec { name: "testpaths", ty: IniType::Args, default: "" },
    IniSpec { name: "python_files", ty: IniType::Args, default: "test_*.py *_test.py" },
    IniSpec { name: "python_classes", ty: IniType::Args, default: "Test" },
    IniSpec { name: "python_functions", ty: IniType::Args, default: "test" },
    IniSpec {
        name: "norecursedirs",
        ty: IniType::Args,
        default: "*.egg .* _darcs build CVS dist node_modules venv {arch}",
    },
    IniSpec { name: "markers", ty: IniType::LineList, default: "" },
    IniSpec { name: "filterwarnings", ty: IniType::LineList, default: "" },
    IniSpec { name: "console_output_style", ty: IniType::Str, default: "progress" },
    IniSpec { name: "xfail_strict", ty: IniType::Bool, default: "false" },
    IniSpec { name: "empty_parameter_set_mark", ty: IniType::Str, default: "skip" },
    IniSpec { name: "pythonpath", ty: IniType::Args, default: "" },
    IniSpec { name: "usefixtures", ty: IniType::Args, default: "" },
    IniSpec { name: "cache_dir", ty: IniType::Str, default: ".pytest_cache" },
    IniSpec { name: "tmp_path_retention_count", ty: IniType::Int, default: "3" },
    IniSpec { name: "tmp_path_retention_policy", ty: IniType::Str, default: "all" },
];

/// Raw (string) ini values as read from the config file.
pub type RawIni = BTreeMap<String, String>;

/// Result of locating the config file.
pub struct IniDiscovery {
    pub rootdir: PathBuf,
    pub inifile: Option<PathBuf>,
    pub raw: RawIni,
}

/// Normalise a path without touching the filesystem (no symlink resolution),
/// matching how pytest displays rootdir-relative paths.
pub fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                if !out.pop() {
                    out.push("..");
                }
            }
            other => out.push(other.as_os_str()),
        }
    }
    out
}

pub fn absolute(p: &Path) -> PathBuf {
    if p.is_absolute() {
        normalize(p)
    } else {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        normalize(&cwd.join(p))
    }
}

/// Parse an INI file into `section -> key -> value`, handling continuation
/// lines the way configparser does.
fn parse_ini_file(text: &str) -> BTreeMap<String, BTreeMap<String, String>> {
    let mut out: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    let mut section = String::new();
    let mut last_key: Option<String> = None;
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') || trimmed.starts_with(';') {
            continue;
        }
        if line.starts_with([' ', '\t']) {
            // Continuation of the previous key.
            if let (Some(k), Some(sec)) = (last_key.clone(), out.get_mut(&section)) {
                if let Some(v) = sec.get_mut(&k) {
                    v.push('\n');
                    v.push_str(trimmed);
                }
            }
            continue;
        }
        if trimmed.starts_with('[') && trimmed.ends_with(']') {
            section = trimmed[1..trimmed.len() - 1].to_string();
            out.entry(section.clone()).or_default();
            last_key = None;
            continue;
        }
        if let Some(eq) = trimmed.find('=') {
            let key = trimmed[..eq].trim().to_string();
            let val = trimmed[eq + 1..].trim().to_string();
            out.entry(section.clone()).or_default().insert(key.clone(), val);
            last_key = Some(key);
        }
    }
    out
}

/// Extract `[tool.pytest.ini_options]` from a pyproject.toml.
///
/// We deliberately avoid pulling in a full TOML crate: the table we need has a
/// simple, well known shape (strings, bools, ints and arrays of strings), and
/// keeping the parse here means config discovery never touches Python.
fn parse_pyproject(text: &str) -> Option<RawIni> {
    let mut in_table = false;
    let mut out = RawIni::new();
    let mut lines = text.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim();
        if t.starts_with('[') {
            in_table = t == "[tool.pytest.ini_options]";
            continue;
        }
        if !in_table || t.is_empty() || t.starts_with('#') {
            continue;
        }
        let Some(eq) = t.find('=') else { continue };
        let key = t[..eq].trim().trim_matches('"').to_string();
        let mut rhs = t[eq + 1..].trim().to_string();
        // Multi-line arrays.
        if rhs.starts_with('[') && !rhs.contains(']') {
            for cont in lines.by_ref() {
                rhs.push(' ');
                rhs.push_str(cont.trim());
                if cont.contains(']') {
                    break;
                }
            }
        }
        out.insert(key, toml_scalar_to_ini(&rhs));
    }
    if out.is_empty() {
        None
    } else {
        Some(out)
    }
}

/// Convert a TOML scalar/array literal into the newline-joined string form that
/// the rest of the ini machinery consumes.
fn toml_scalar_to_ini(rhs: &str) -> String {
    let rhs = rhs.trim();
    if let Some(inner) = rhs.strip_prefix('[').and_then(|s| s.rsplit_once(']')).map(|(a, _)| a) {
        let mut items = Vec::new();
        for item in split_toml_array(inner) {
            items.push(unquote_toml(item.trim()));
        }
        return items.join("\n");
    }
    unquote_toml(rhs)
}

fn split_toml_array(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let bytes = s.as_bytes();
    let mut start = 0usize;
    let mut quote: Option<u8> = None;
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];
        match quote {
            Some(q) => {
                if b == b'\\' {
                    i += 2;
                    continue;
                }
                if b == q {
                    quote = None;
                }
            }
            None => {
                if b == b'"' || b == b'\'' {
                    quote = Some(b);
                } else if b == b',' {
                    let piece = &s[start..i];
                    if !piece.trim().is_empty() {
                        out.push(piece);
                    }
                    start = i + 1;
                }
            }
        }
        i += 1;
    }
    if start < s.len() && !s[start..].trim().is_empty() {
        out.push(&s[start..]);
    }
    out
}

fn unquote_toml(s: &str) -> String {
    let s = s.trim();
    if s.len() >= 2 {
        let b = s.as_bytes();
        if (b[0] == b'"' && b[s.len() - 1] == b'"') || (b[0] == b'\'' && b[s.len() - 1] == b'\'') {
            let inner = &s[1..s.len() - 1];
            if b[0] == b'\'' {
                return inner.to_string();
            }
            return unescape(inner);
        }
    }
    s.to_string()
}

fn unescape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some(other) => {
                out.push('\\');
                out.push(other);
            }
            None => out.push('\\'),
        }
    }
    out
}

/// Try to read pytest configuration out of a single candidate file.
fn read_candidate(path: &Path) -> Option<RawIni> {
    let text = std::fs::read_to_string(path).ok()?;
    let name = path.file_name()?.to_string_lossy().to_string();
    match name.as_str() {
        "pyproject.toml" => parse_pyproject(&text),
        "pytest.ini" | ".pytest.ini" => {
            let ini = parse_ini_file(&text);
            // pytest.ini always "wins" even when [pytest] is absent.
            Some(ini.get("pytest").cloned().unwrap_or_default())
        }
        "tox.ini" => parse_ini_file(&text).get("pytest").cloned(),
        "setup.cfg" => parse_ini_file(&text).get("tool:pytest").cloned(),
        _ => None,
    }
}

const CANDIDATES: &[&str] = &["pytest.ini", ".pytest.ini", "pyproject.toml", "tox.ini", "setup.cfg"];

/// Locate rootdir and the ini file following pytest's documented algorithm
/// (simplified: we search upwards from the common ancestor of the args).
pub fn discover(args: &[String], explicit_ini: Option<&str>, explicit_root: Option<&str>) -> IniDiscovery {
    if let Some(ini) = explicit_ini {
        let p = absolute(Path::new(ini));
        let raw = read_candidate(&p).unwrap_or_default();
        let rootdir = explicit_root
            .map(|r| absolute(Path::new(r)))
            .unwrap_or_else(|| p.parent().map(|x| x.to_path_buf()).unwrap_or_default());
        return IniDiscovery { rootdir, inifile: Some(p), raw };
    }

    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut ancestors: Vec<PathBuf> = args
        .iter()
        .filter(|a| !a.starts_with('-'))
        .map(|a| {
            // Strip any `::` node id suffix before treating it as a path.
            let base = a.split("::").next().unwrap_or(a);
            absolute(Path::new(base))
        })
        .collect();
    if ancestors.is_empty() {
        ancestors.push(cwd.clone());
    }
    let mut common = common_ancestor(&ancestors);
    if common.is_file() {
        common = common.parent().map(|p| p.to_path_buf()).unwrap_or(common);
    }

    let mut dir = Some(common.as_path());
    while let Some(d) = dir {
        for cand in CANDIDATES {
            let p = d.join(cand);
            if p.is_file() {
                if let Some(raw) = read_candidate(&p) {
                    let rootdir = explicit_root.map(|r| absolute(Path::new(r))).unwrap_or_else(|| d.to_path_buf());
                    return IniDiscovery { rootdir, inifile: Some(p), raw };
                }
            }
        }
        dir = d.parent();
    }
    // No ini anywhere: fall back to the common ancestor (pytest also looks for
    // setup.py, which we approximate here).
    let mut dir = Some(common.as_path());
    while let Some(d) = dir {
        if d.join("setup.py").is_file() {
            return IniDiscovery { rootdir: d.to_path_buf(), inifile: None, raw: RawIni::new() };
        }
        dir = d.parent();
    }
    let rootdir = explicit_root.map(|r| absolute(Path::new(r))).unwrap_or(common);
    IniDiscovery { rootdir, inifile: None, raw: RawIni::new() }
}

fn common_ancestor(paths: &[PathBuf]) -> PathBuf {
    let mut iter = paths.iter();
    let Some(first) = iter.next() else { return PathBuf::from(".") };
    let mut acc: Vec<_> = first.components().map(|c| c.as_os_str().to_owned()).collect();
    for p in iter {
        let other: Vec<_> = p.components().map(|c| c.as_os_str().to_owned()).collect();
        let n = acc.iter().zip(other.iter()).take_while(|(a, b)| a == b).count();
        acc.truncate(n);
    }
    let mut out = PathBuf::new();
    for c in acc {
        out.push(c);
    }
    if out.as_os_str().is_empty() {
        PathBuf::from("/")
    } else {
        out
    }
}

/// Extensible command line parser.
pub struct Parser {
    pub specs: Vec<OptionSpec>,
    /// Maps every option string (`-k`, `--keyword`) to an index into `specs`.
    lookup: BTreeMap<String, usize>,
    /// Maps option string to dest, used by `Config.getoption("--flag")`.
    pub opt2dest: BTreeMap<String, String>,
    /// ini options registered by plugins/conftest via `parser.addini`.
    pub extra_ini: BTreeMap<String, (IniType, String)>,
}

impl Parser {
    pub fn new() -> Self {
        let mut p = Parser {
            specs: Vec::new(),
            lookup: BTreeMap::new(),
            opt2dest: BTreeMap::new(),
            extra_ini: BTreeMap::new(),
        };
        p.add_builtin();
        p
    }

    pub fn add(&mut self, spec: OptionSpec) {
        let idx = self.specs.len();
        for n in &spec.names {
            self.lookup.insert(n.clone(), idx);
            self.opt2dest.insert(n.clone(), spec.dest.clone());
        }
        self.opt2dest.insert(spec.dest.clone(), spec.dest.clone());
        self.specs.push(spec);
    }

    fn add_builtin(&mut self) {
        use OptKind::*;
        use OptType::*;
        let specs = vec![
            OptionSpec::new(&["-k"], Store).dest("keyword").default(Value::Str(String::new()))
                .help("only run tests which match the given substring expression").group("selection"),
            OptionSpec::new(&["-m"], Store).dest("markexpr").default(Value::Str(String::new()))
                .help("only run tests matching given mark expression").group("selection"),
            OptionSpec::new(&["-x", "--exitfirst"], StoreTrue).dest("exitfirst")
                .help("exit instantly on first error or failed test").group("selection"),
            OptionSpec::new(&["--maxfail"], Store).dest("maxfail").ty(Int).default(Value::Int(0))
                .help("exit after first num failures or errors").group("selection"),
            OptionSpec::new(&["-v", "--verbose"], Count).dest("verbose")
                .help("increase verbosity").group("reporting"),
            OptionSpec::new(&["-q", "--quiet"], Count).dest("quiet")
                .help("decrease verbosity").group("reporting"),
            OptionSpec::new(&["--verbosity"], Store).dest("verbose").ty(Int),
            OptionSpec::new(&["-s"], StoreTrue).dest("capture_no")
                .help("shortcut for --capture=no").group("reporting"),
            OptionSpec::new(&["--capture"], Store).dest("capture").default(Value::Str("fd".into()))
                .help("per-test capturing method: one of fd|sys|no|tee-sys").group("reporting"),
            OptionSpec::new(&["--tb"], Store).dest("tbstyle").default(Value::Str("auto".into()))
                .help("traceback print mode (auto/long/short/line/native/no)").group("reporting"),
            OptionSpec::new(&["-r"], Store).dest("reportchars").default(Value::Str("fE".into()))
                .help("show extra test summary info as specified by chars").group("reporting"),
            OptionSpec::new(&["--strict-markers", "--strict"], StoreTrue).dest("strict_markers")
                .help("markers not registered in the `markers` section of the configuration file raise errors").group("collection"),
            OptionSpec::new(&["--strict-config"], StoreTrue).dest("strict_config"),
            OptionSpec::new(&["-p"], Append).dest("plugins")
                .help("early-load given plugin module name or entry point").group("general"),
            OptionSpec::new(&["--collect-only", "--collectonly", "--co"], StoreTrue).dest("collectonly")
                .help("only collect tests, don't execute them").group("collection"),
            OptionSpec::new(&["--rootdir"], Store).dest("rootdir").group("general").help("define the root directory for test paths"),
            OptionSpec::new(&["-c", "--config-file"], Store).dest("inifilename").group("general").help("load configuration from this file instead of searching"),
            OptionSpec::new(&["--durations"], Store).dest("durations").ty(Int).default(Value::Int(-1))
                .help("show N slowest setup/test durations (N=0 for all)").group("reporting"),
            OptionSpec::new(&["--durations-min"], Store).dest("durations_min").ty(Float).default(Value::Float(0.005)).group("reporting").help("minimum duration to report in --durations"),
            OptionSpec::new(&["--no-header"], StoreTrue).dest("no_header").group("reporting").help("disable the session header"),
            OptionSpec::new(&["--no-summary"], StoreTrue).dest("no_summary").group("reporting").help("disable the failure and short summaries"),
            OptionSpec::new(&["--color"], Store).dest("color").default(Value::Str("auto".into())).group("reporting").help("colour the terminal output: auto|yes|no"),
            OptionSpec::new(&["--ignore"], Append).dest("ignore").group("collection").help("ignore this path during collection"),
            OptionSpec::new(&["--ignore-glob"], Append).dest("ignore_glob").group("collection").help("ignore paths matching this glob during collection"),
            OptionSpec::new(&["--deselect"], Append).dest("deselect").group("collection").help("deselect this node id"),
            OptionSpec::new(&["-W", "--pythonwarnings"], Append).dest("pythonwarnings").group("reporting").help("set a warning filter, as `-W` for the interpreter"),
            OptionSpec::new(&["--continue-on-collection-errors"], StoreTrue).dest("continue_on_collection_errors").group("collection").help("run tests even if collection raised somewhere"),
            OptionSpec::new(&["--import-mode"], Store).dest("importmode").default(Value::Str("prepend".into())),
            OptionSpec::new(&["--basetemp"], Store).dest("basetemp").group("general").help("base directory for `tmp_path`"),
            OptionSpec::new(&["--junitxml", "--junit-xml"], Store).dest("xmlpath").group("reporting").help("write an xunit2 XML report to this path"),
            OptionSpec::new(&["--fulltrace", "--full-trace"], StoreTrue).dest("fulltrace"),
            OptionSpec::new(&["-l", "--showlocals"], StoreTrue).dest("showlocals").group("reporting").help("show local variables in tracebacks"),
            OptionSpec::new(&["--co-json"], Store).dest("co_json")
                .help("write the collected node ids to a JSON file"),
            // --- Parallelism (thread based; xdist-compatible spelling) -------
            OptionSpec::new(&["-n", "--numprocesses"], Store).dest("numprocesses").default(Value::Str("auto".into()))
                .group("parallelism")
                .help("worker threads; 'auto' means the CPU count on a free-threaded interpreter and 1 otherwise"),
            OptionSpec::new(&["--dist"], Store).dest("dist").default(Value::Str("load".into())),
            OptionSpec::new(&["--max-worker-restart"], Store).dest("max_worker_restart"),
            OptionSpec::new(&["--threads"], Store).dest("numprocesses"),
            OptionSpec::new(&["--no-parallel"], StoreTrue).dest("no_parallel")
                .group("parallelism").help("run every test on the main thread"),
            OptionSpec::new(&["--tx"], Append).dest("tx"),
            // --- pytest-randomly built-ins -----------------------------------
            OptionSpec::new(&["--randomly-seed"], Store).dest("randomly_seed").default(Value::Str("default".into()))
                .group("randomisation")
                .help("random seed; 'last' reuses the previous run's, 'default' picks a fresh one each run"),
            OptionSpec::new(&["--randomly-dont-reset-seed"], StoreFalse).dest("randomly_reset_seed").group("randomisation").help("do not seed the global RNG from the session seed"),
            OptionSpec::new(&["--randomly-dont-reorganize", "--randomly-dont-shuffle"], StoreFalse)
                .dest("randomly_reorganize").group("randomisation").help("keep the collected order"),
            // --- pytest-benchmark built-ins ----------------------------------
            OptionSpec::new(&["--benchmark-disable"], StoreTrue).dest("benchmark_disable").group("benchmark").help("run benchmarked functions once instead of timing them"),
            OptionSpec::new(&["--benchmark-enable"], StoreTrue).dest("benchmark_enable").group("benchmark").help("time benchmarked functions even if disabled in the config"),
            OptionSpec::new(&["--benchmark-only"], StoreTrue).dest("benchmark_only").group("benchmark").help("run only tests that use the benchmark fixture"),
            OptionSpec::new(&["--benchmark-skip"], StoreTrue).dest("benchmark_skip").group("benchmark").help("skip tests that use the benchmark fixture"),
            OptionSpec::new(&["--benchmark-autosave"], StoreTrue).dest("benchmark_autosave"),
            OptionSpec::new(&["--benchmark-disable-gc"], StoreTrue).dest("benchmark_disable_gc").group("benchmark").help("disable the garbage collector while timing"),
            OptionSpec::new(&["--benchmark-sort"], Store).dest("benchmark_sort").default(Value::Str("min".into())).group("benchmark").help("sort the results table by min|max|mean|stddev|median"),
            OptionSpec::new(&["--benchmark-columns"], Store).dest("benchmark_columns")
                .default(Value::Str("min, max, mean, stddev, median, iqr, outliers, ops, rounds".into())),
            OptionSpec::new(&["--benchmark-min-rounds"], Store).dest("benchmark_min_rounds").ty(Int).default(Value::Int(5)).group("benchmark").help("minimum number of timed rounds"),
            OptionSpec::new(&["--benchmark-max-time"], Store).dest("benchmark_max_time").ty(Float).default(Value::Float(1.0)).group("benchmark").help("time budget per benchmark, in seconds"),
            OptionSpec::new(&["--benchmark-min-time"], Store).dest("benchmark_min_time").ty(Float).default(Value::Float(0.000005)).group("benchmark").help("minimum duration of a single timed round"),
            OptionSpec::new(&["--benchmark-warmup"], Store).dest("benchmark_warmup").default(Value::Str("auto".into())),
            OptionSpec::new(&["--benchmark-warmup-iterations"], Store).dest("benchmark_warmup_iterations").ty(Int)
                .default(Value::Int(100000)),
            OptionSpec::new(&["--benchmark-json"], Store).dest("benchmark_json"),
            OptionSpec::new(&["--benchmark-group-by"], Store).dest("benchmark_group_by").default(Value::Str("group".into())),
            OptionSpec::new(&["--benchmark-timer"], Store).dest("benchmark_timer"),
            OptionSpec::new(&["--benchmark-calibration-precision"], Store).dest("benchmark_calibration_precision")
                .ty(Int).default(Value::Int(10)),
            // --- pytest-cov built-ins ----------------------------------------
            OptionSpec::new(&["--cov"], Append).dest("cov_source")
                .help("measure coverage for the given path or package").group("coverage"),
            OptionSpec::new(&["--cov-report"], Append).dest("cov_report").group("coverage").help("report type: term|term-missing|html|xml|json|annotate[:dest]"),
            OptionSpec::new(&["--cov-config"], Store).dest("cov_config").default(Value::Str(".coveragerc".into())).group("coverage").help("coverage.py configuration file"),
            OptionSpec::new(&["--cov-branch"], StoreTrue).dest("cov_branch").group("coverage").help("measure branch coverage as well as statements"),
            OptionSpec::new(&["--cov-append"], StoreTrue).dest("cov_append").group("coverage").help("add to existing coverage data instead of replacing it"),
            OptionSpec::new(&["--cov-fail-under"], Store).dest("cov_fail_under").ty(Float).group("coverage").help("fail the run if total coverage is below this percentage"),
            OptionSpec::new(&["--cov-context"], Store).dest("cov_context"),
            OptionSpec::new(&["--no-cov"], StoreTrue).dest("no_cov").group("coverage").help("disable coverage even if --cov was given"),
            OptionSpec::new(&["--no-cov-on-fail"], StoreTrue).dest("no_cov_on_fail"),
            // --- Misc compatibility shims ------------------------------------
            OptionSpec::new(&["--version", "-V"], Count).dest("version"),
            OptionSpec::new(&["-h", "--help"], StoreTrue).dest("help"),
            OptionSpec::new(&["--lf", "--last-failed"], StoreTrue).dest("lf").group("selection")
                .help("rerun only the tests that failed in the previous run"),
            OptionSpec::new(&["--ff", "--failed-first"], StoreTrue).dest("ff").group("selection")
                .help("run the tests that failed in the previous run first, then the rest"),
            OptionSpec::new(&["--cache-clear"], StoreTrue).dest("cacheclear").group("general")
                .help("discard the cached seed, durations and last-failed list before running"),
            OptionSpec::new(&["-p", "--plugin"], Append).dest("plugins"),
            OptionSpec::new(&["--assert"], Store).dest("assertmode").default(Value::Str("rewrite".into())),
        ];
        for s in specs {
            self.add(s);
        }
    }

    /// Parse `argv`, returning (values keyed by dest, positional args).
    ///
    /// `tolerant` suppresses errors for unknown options; it is used for the
    /// first pass, before conftest files have registered their own options.
    pub fn parse(&self, argv: &[String], tolerant: bool) -> Result<(BTreeMap<String, Value>, Vec<String>)> {
        let mut values: BTreeMap<String, Value> = BTreeMap::new();
        for s in &self.specs {
            values.entry(s.dest.clone()).or_insert_with(|| s.default.clone());
        }
        let mut positional = Vec::new();
        let mut i = 0usize;
        let mut only_positional = false;
        while i < argv.len() {
            let arg = &argv[i];
            i += 1;
            if only_positional || arg == "-" {
                positional.push(arg.clone());
                continue;
            }
            if arg == "--" {
                only_positional = true;
                continue;
            }
            if !arg.starts_with('-') || arg.len() == 1 {
                positional.push(arg.clone());
                continue;
            }

            // Split `--opt=value` / `-k=value`.
            let (name, inline) = match arg.find('=') {
                Some(pos) if arg.starts_with("--") => (arg[..pos].to_string(), Some(arg[pos + 1..].to_string())),
                _ => (arg.clone(), None),
            };

            if let Some(&idx) = self.lookup.get(&name) {
                self.apply(&self.specs[idx], inline, argv, &mut i, &mut values, &name)?;
                continue;
            }

            // Short option clusters and attached values: `-vv`, `-ktest`, `-n4`.
            if !arg.starts_with("--") && arg.len() > 2 && self.parse_short_cluster(arg, &mut values)? {
                continue;
            }

            if tolerant {
                // Unknown for now; a conftest may register it later.  Remember
                // it so the second pass sees it again.
                continue;
            }
            return Err(Error::usage(format!("unrecognized arguments: {arg}")));
        }
        Ok((values, positional))
    }

    /// Handle `-vv`, `-xvs`, `-n4`, `-kfoo`.  Returns `true` when the whole
    /// cluster was consumed.
    fn parse_short_cluster(&self, arg: &str, values: &mut BTreeMap<String, Value>) -> Result<bool> {
        let chars: Vec<char> = arg[1..].chars().collect();
        let mut consumed_all = true;
        let mut pending: Vec<(usize, Option<String>)> = Vec::new();
        let mut idx = 0usize;
        while idx < chars.len() {
            let name = format!("-{}", chars[idx]);
            let Some(&spec_idx) = self.lookup.get(&name) else {
                consumed_all = false;
                break;
            };
            let spec = &self.specs[spec_idx];
            match spec.kind {
                OptKind::StoreTrue | OptKind::StoreFalse | OptKind::Count => {
                    pending.push((spec_idx, None));
                    idx += 1;
                }
                _ => {
                    let rest: String = chars[idx + 1..].iter().collect();
                    if rest.is_empty() {
                        consumed_all = false;
                        break;
                    }
                    pending.push((spec_idx, Some(rest.trim_start_matches('=').to_string())));
                    idx = chars.len();
                }
            }
        }
        if !consumed_all {
            return Ok(false);
        }
        for (spec_idx, val) in pending {
            let spec = &self.specs[spec_idx];
            match spec.kind {
                OptKind::StoreTrue => {
                    values.insert(spec.dest.clone(), Value::Bool(true));
                }
                OptKind::StoreFalse => {
                    values.insert(spec.dest.clone(), Value::Bool(false));
                }
                OptKind::Count => {
                    let cur = values.get(&spec.dest).and_then(|v| v.as_int()).unwrap_or(0);
                    values.insert(spec.dest.clone(), Value::Int(cur + 1));
                }
                _ => {
                    values.insert(spec.dest.clone(), coerce(spec.ty, &val.unwrap_or_default())?);
                }
            }
        }
        Ok(true)
    }

    fn apply(
        &self,
        spec: &OptionSpec,
        inline: Option<String>,
        argv: &[String],
        i: &mut usize,
        values: &mut BTreeMap<String, Value>,
        name: &str,
    ) -> Result<()> {
        match spec.kind {
            OptKind::StoreTrue => {
                values.insert(spec.dest.clone(), Value::Bool(true));
            }
            OptKind::StoreFalse => {
                values.insert(spec.dest.clone(), Value::Bool(false));
            }
            OptKind::Count => {
                let cur = values.get(&spec.dest).and_then(|v| v.as_int()).unwrap_or(0);
                values.insert(spec.dest.clone(), Value::Int(cur + 1));
            }
            OptKind::OptionalStore => {
                let v = match inline {
                    Some(v) => coerce(spec.ty, &v)?,
                    None => spec.const_value.clone().unwrap_or(Value::None),
                };
                values.insert(spec.dest.clone(), v);
            }
            OptKind::Store | OptKind::Append => {
                let raw = match inline {
                    Some(v) => v,
                    None => {
                        if *i >= argv.len() {
                            // `--cov` with no argument behaves like a flag.
                            if spec.kind == OptKind::Append {
                                String::new()
                            } else {
                                return Err(Error::usage(format!("argument {name}: expected one argument")));
                            }
                        } else {
                            let nxt = argv[*i].clone();
                            *i += 1;
                            nxt
                        }
                    }
                };
                if let Some(choices) = &spec.choices {
                    if !choices.iter().any(|c| c == &raw) {
                        return Err(Error::usage(format!(
                            "argument {name}: invalid choice: '{raw}' (choose from {})",
                            choices.join(", ")
                        )));
                    }
                }
                let v = coerce(spec.ty, &raw)?;
                if spec.kind == OptKind::Append {
                    let mut cur = values.get(&spec.dest).map(|v| v.as_list()).unwrap_or_default();
                    cur.push(v);
                    values.insert(spec.dest.clone(), Value::List(cur));
                } else {
                    values.insert(spec.dest.clone(), v);
                }
            }
        }
        Ok(())
    }
}

/// `--cov` is special: it can appear with or without a value.  Pre-process argv
/// so the generic parser sees a consistent shape.
pub fn preprocess_argv(argv: &[String]) -> Vec<String> {
    let mut out = Vec::with_capacity(argv.len());
    let mut it = argv.iter().peekable();
    while let Some(a) = it.next() {
        if a == "--cov" {
            // A bare `--cov` means "measure everything"; only swallow the next
            // token if it does not look like another option or a test path.
            let takes = it
                .peek()
                .map(|n| !n.starts_with('-') && !n.contains('/') && !n.ends_with(".py") && !Path::new(n).exists())
                .unwrap_or(false);
            if takes {
                let v = it.next().unwrap();
                out.push(format!("--cov={v}"));
            } else {
                out.push("--cov=".to_string());
            }
            continue;
        }
        out.push(a.clone());
    }
    out
}

/// Split an ini value according to its declared type.
pub fn split_ini(ty: IniType, raw: &str) -> Value {
    match ty {
        IniType::Args => Value::List(shlex_split(raw).into_iter().map(Value::Str).collect()),
        IniType::LineList => Value::List(
            raw.lines()
                .map(|l| l.trim())
                .filter(|l| !l.is_empty())
                .map(|l| Value::Str(l.to_string()))
                .collect(),
        ),
        IniType::Paths => Value::List(shlex_split(raw).into_iter().map(Value::Str).collect()),
        IniType::Str => Value::Str(raw.to_string()),
        IniType::Bool => Value::Bool(matches!(raw.trim().to_ascii_lowercase().as_str(), "1" | "true" | "yes" | "on")),
        IniType::Int => Value::Int(raw.trim().parse().unwrap_or(0)),
    }
}

/// A small shell-like splitter: honours single and double quotes, ignores
/// backslash escapes outside quotes (which is what pytest's shlex does).
pub fn shlex_split(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut quote: Option<char> = None;
    let mut has_token = false;
    for c in s.chars() {
        match quote {
            Some(q) => {
                if c == q {
                    quote = None;
                } else {
                    cur.push(c);
                }
            }
            None => {
                if c == '\'' || c == '"' {
                    quote = Some(c);
                    has_token = true;
                } else if c.is_whitespace() {
                    if has_token || !cur.is_empty() {
                        out.push(std::mem::take(&mut cur));
                        has_token = false;
                    }
                } else {
                    cur.push(c);
                    has_token = true;
                }
            }
        }
    }
    if has_token || !cur.is_empty() {
        out.push(cur);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shlex_handles_quotes() {
        assert_eq!(shlex_split("-r s --capture=no"), vec!["-r", "s", "--capture=no"]);
        assert_eq!(shlex_split("-k 'foo and bar'"), vec!["-k", "foo and bar"]);
        assert_eq!(shlex_split(""), Vec::<String>::new());
    }

    #[test]
    fn pyproject_table() {
        let text = r#"
[tool.pytest.ini_options]
addopts = "-r s --capture=no --strict-markers --benchmark-disable"
testpaths = ["tests"]
console_output_style = "progress-even-when-capture-no"
markers = [
    "skip_fips: this test is not executed in FIPS mode",
    "supported: parametrized test requiring only_if and skip_message",
]

[tool.mypy]
strict = true
"#;
        let raw = parse_pyproject(text).unwrap();
        assert_eq!(raw["addopts"], "-r s --capture=no --strict-markers --benchmark-disable");
        assert_eq!(raw["testpaths"], "tests");
        assert!(raw["markers"].contains("skip_fips"));
        assert!(!raw.contains_key("strict"));
    }

    #[test]
    fn short_clusters() {
        let p = Parser::new();
        let argv: Vec<String> = ["-xvs", "-n4", "tests/"].iter().map(|s| s.to_string()).collect();
        let (v, pos) = p.parse(&argv, false).unwrap();
        assert_eq!(v["exitfirst"], Value::Bool(true));
        assert_eq!(v["verbose"], Value::Int(1));
        assert_eq!(v["capture_no"], Value::Bool(true));
        assert_eq!(v["numprocesses"], Value::Str("4".into()));
        assert_eq!(pos, vec!["tests/"]);
    }
}
