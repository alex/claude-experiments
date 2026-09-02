//! Developer tasks for rustlibc.
//!
//! ```text
//! cargo xtask build      # build libc.a and assemble target/sysroot
//! cargo xtask test       # build, then compile and run every tests/c/*.c
//! cargo xtask test NAME  # only tests whose file name contains NAME
//! cargo xtask bench      # run bench/bench.c against rustlibc and glibc
//! cargo xtask bench alloc  # the allocator workloads in bench/alloc.c
//! cargo xtask --aarch64 test  # cross-build with aarch64-linux-gnu-gcc,
//!                             # run under qemu-aarch64
//! cargo xtask --pie test      # link the tests as static PIEs
//! ```
//!
//! Each C test (or C++ test, `*.cpp`, linked with the host toolchain's
//! `libstdc++.a`) is compiled against the sysroot with `-static -nostdlib`
//! and run. A test passes when its exit status matches (0 by default, or
//! the `// expect-exit: N` / `// expect-signal: NAME` directive in the
//! source) and, if a sibling `NAME.stdout` file exists, its standard
//! output matches that file exactly. A `// cflags: ...` line adds
//! compiler flags for that test.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::sync::Mutex;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf()
}

/// The build target: the host, or a cross target with its own toolchain
/// prefix and emulator.
#[derive(Clone, Copy, PartialEq)]
enum Target {
    Host,
    Aarch64,
}

static TARGET: Mutex<Target> = Mutex::new(Target::Host);
/// Link the test programs as static PIEs instead of fixed-address
/// executables.
static PIE: Mutex<bool> = Mutex::new(false);

fn pie() -> bool {
    *PIE.lock().unwrap()
}

fn target() -> Target {
    *TARGET.lock().unwrap()
}

impl Target {
    fn triple(self) -> Option<&'static str> {
        match self {
            Target::Host => None,
            Target::Aarch64 => Some("aarch64-unknown-linux-gnu"),
        }
    }
    /// Prefix of the GNU toolchain binaries.
    fn prefix(self) -> &'static str {
        match self {
            Target::Host => "",
            Target::Aarch64 => "aarch64-linux-gnu-",
        }
    }
    /// Emulator that runs the target's binaries, if not the host.
    fn runner(self) -> Option<&'static str> {
        match self {
            Target::Host => None,
            Target::Aarch64 => Some("qemu-aarch64"),
        }
    }
    fn sysroot_name(self) -> &'static str {
        match self {
            Target::Host => "sysroot",
            Target::Aarch64 => "sysroot-aarch64",
        }
    }
}

fn cc() -> String {
    match target() {
        Target::Host => std::env::var("CC").unwrap_or_else(|_| "cc".to_string()),
        t => format!("{}gcc", t.prefix()),
    }
}

fn ar() -> String {
    format!("{}ar", target().prefix())
}

fn run(cmd: &mut Command) -> bool {
    cmd.status().map(|s| s.success()).unwrap_or(false)
}

fn build(release: bool) -> Result<PathBuf, String> {
    let root = root();
    let mut cargo = Command::new(env!("CARGO"));
    cargo.current_dir(&root).args(["build", "-p", "rustlibc"]);
    if release {
        cargo.arg("--release");
    }
    let mut libdir_parts = root.join("target");
    if let Some(triple) = target().triple() {
        cargo.args(["--target", triple]);
        libdir_parts = libdir_parts.join(triple);
    }
    if !run(&mut cargo) {
        return Err("cargo build failed".into());
    }
    let profile = if release { "release" } else { "debug" };
    let lib = libdir_parts.join(profile).join("libc.a");
    let sysroot = root.join("target").join(target().sysroot_name());
    let libdir = sysroot.join("lib");
    fs::create_dir_all(&libdir).map_err(|e| e.to_string())?;
    fs::copy(&lib, libdir.join("libc.a")).map_err(|e| e.to_string())?;
    // Provide the empty archives that gcc's default link line asks for.
    for name in ["libm.a", "libpthread.a", "librt.a", "libdl.a"] {
        let p = libdir.join(name);
        if !p.exists() && !run(Command::new(ar()).arg("rcs").arg(&p)) {
            return Err(format!("ar failed for {}", p.display()));
        }
    }
    let inc = sysroot.join("include");
    let _ = fs::remove_dir_all(&inc);
    copy_dir(&root.join("include"), &inc).map_err(|e| e.to_string())?;
    Ok(sysroot)
}

fn copy_dir(from: &Path, to: &Path) -> std::io::Result<()> {
    fs::create_dir_all(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let dest = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_dir(&entry.path(), &dest)?;
        } else {
            fs::copy(entry.path(), dest)?;
        }
    }
    Ok(())
}

/// The compiler's own header directory (stdbool.h, float.h, intrinsics).
fn compiler_include_dir() -> String {
    let out = Command::new(cc())
        .arg("-print-file-name=include")
        .output()
        .expect("run cc");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

/// Extra compiler flags requested by a `// cflags: ...` line in the test.
fn parse_cflags(src: &str) -> Vec<String> {
    src.lines()
        .filter_map(|l| l.trim().strip_prefix("// cflags:"))
        .flat_map(|l| l.split_whitespace().map(str::to_string).collect::<Vec<_>>())
        .collect()
}

/// Command line to compile a C program against the sysroot.
fn compile_cmd(sysroot: &Path, src: &Path, out: &Path, extra: &[String]) -> Command {
    let cxx = src.extension().is_some_and(|x| x == "cpp");
    let mut cmd = Command::new(if cxx { cxx_compiler() } else { cc() });
    cmd.args([
        if cxx { "-std=gnu++17" } else { "-std=gnu11" },
        "-O2",
        "-g",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-fstack-protector-strong",
    ]);
    if pie() {
        cmd.args(["-static-pie", "-fPIE"]);
    } else {
        cmd.args(["-static", "-no-pie", "-fno-pie"]);
    }
    cmd.args([
        "-nostdlib",
        "-nostartfiles",
        "-nostdinc",
        // libgcc's unwinder finds frames through PT_GNU_EH_FRAME; gcc only
        // asks the linker for it in dynamic links.
        "-Wl,--eh-frame-hdr",
    ]);
    if cxx {
        // The host's C++ headers, before our C headers.
        cmd.arg("-nostdinc++");
        for dir in cxx_include_dirs() {
            cmd.arg("-isystem").arg(dir);
        }
    }
    cmd.arg("-isystem")
        .arg(sysroot.join("include"))
        .arg("-isystem")
        .arg(compiler_include_dir())
        .args(extra)
        .arg(src)
        .arg("-o")
        .arg(out)
        .arg("-L")
        .arg(sysroot.join("lib"));
    if cxx {
        cmd.arg(print_file_name(&cxx_compiler(), "libstdc++.a"));
        cmd.arg(print_file_name(&cxx_compiler(), "libgcc_eh.a"));
    }
    cmd.args(["-lc", "-lgcc"]);
    cmd
}

fn cxx_compiler() -> String {
    match target() {
        Target::Host => std::env::var("CXX").unwrap_or_else(|_| "c++".to_string()),
        t => format!("{}g++", t.prefix()),
    }
}

/// Whether the target toolchain can build C++ (a cross g++ may be absent).
fn have_cxx() -> bool {
    Command::new(cxx_compiler())
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Asks the compiler where a library file lives.
fn print_file_name(compiler: &str, name: &str) -> String {
    let out = Command::new(compiler)
        .arg(format!("-print-file-name={name}"))
        .output()
        .expect("run compiler");
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// The C++ standard library's include directories, from the compiler's
/// own search list (`-v` output between the "#include <...>" markers).
fn cxx_include_dirs() -> Vec<String> {
    let out = Command::new(cxx_compiler())
        .args(["-x", "c++", "-E", "-v", "-", "-o", "/dev/null"])
        .stdin(Stdio::null())
        .output()
        .expect("run c++");
    let text = String::from_utf8_lossy(&out.stderr);
    let mut dirs = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        if line.starts_with("#include <...> search starts here") {
            inside = true;
        } else if line.starts_with("End of search list") {
            break;
        } else if inside {
            let dir = line.trim();
            if dir.contains("c++") {
                dirs.push(dir.to_string());
            }
        }
    }
    dirs
}

#[derive(Debug, PartialEq)]
enum Expect {
    Exit(i32),
    Signal(&'static str),
}

fn parse_expect(src: &str) -> Expect {
    for line in src.lines() {
        if let Some(rest) = line.trim().strip_prefix("// expect-exit:") {
            return Expect::Exit(rest.trim().parse().expect("bad expect-exit"));
        }
        if let Some(rest) = line.trim().strip_prefix("// expect-signal:") {
            let name = rest.trim();
            let known = [
                "SIGABRT", "SIGSEGV", "SIGILL", "SIGFPE", "SIGKILL", "SIGTERM", "SIGTRAP",
            ];
            return Expect::Signal(
                known
                    .iter()
                    .copied()
                    .find(|k| *k == name)
                    .expect("unknown signal"),
            );
        }
    }
    Expect::Exit(0)
}

fn signal_number(name: &str) -> i32 {
    match name {
        "SIGILL" => 4,
        "SIGTRAP" => 5,
        "SIGABRT" => 6,
        "SIGFPE" => 8,
        "SIGKILL" => 9,
        "SIGSEGV" => 11,
        "SIGTERM" => 15,
        _ => unreachable!(),
    }
}

struct Failure {
    name: String,
    message: String,
}

fn run_test(sysroot: &Path, bindir: &Path, src: &Path) -> Result<(), String> {
    use std::os::unix::process::ExitStatusExt;
    let name = src.file_stem().unwrap().to_string_lossy().to_string();
    let source = fs::read_to_string(src).map_err(|e| e.to_string())?;
    let expect = parse_expect(&source);
    let cflags = parse_cflags(&source);
    let bin = bindir.join(&name);
    let out = compile_cmd(sysroot, src, &bin, &cflags)
        .output()
        .map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(format!(
            "compile failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let mut cmd = match target().runner() {
        Some(runner) => {
            let mut c = Command::new(runner);
            c.arg(&bin);
            c
        }
        None => Command::new(&bin),
    };
    cmd.current_dir(bindir)
        .stdin(Stdio::null())
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("TESTVAR", "value");
    let out = cmd.output().map_err(|e| e.to_string())?;
    let status = out.status;
    let actual = match (status.code(), status.signal()) {
        (Some(c), _) => format!("exit {c}"),
        (None, Some(s)) => format!("signal {s}"),
        _ => "unknown".into(),
    };
    let ok = match expect {
        Expect::Exit(c) => status.code() == Some(c),
        Expect::Signal(s) => status.signal() == Some(signal_number(s)),
    };
    if !ok {
        return Err(format!(
            "expected {expect:?}, got {actual}\n--- stdout ---\n{}\n--- stderr ---\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let expected_stdout = src.with_extension("stdout");
    if expected_stdout.exists() {
        let want = fs::read(&expected_stdout).map_err(|e| e.to_string())?;
        if want != out.stdout {
            return Err(format!(
                "stdout mismatch\n--- expected ---\n{}\n--- actual ---\n{}\n--- stderr ---\n{}",
                String::from_utf8_lossy(&want),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }
    Ok(())
}

fn test(filter: Option<&str>, release: bool) -> ExitCode {
    let sysroot = match build(release) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };
    let root = root();
    let mut bindir = root.join("target").join(match target() {
        Target::Host => "ctests".to_string(),
        t => format!("ctests-{}", t.sysroot_name().trim_start_matches("sysroot-")),
    });
    if pie() {
        bindir.set_file_name(format!("{}-pie", bindir.file_name().unwrap().to_string_lossy()));
    }
    fs::create_dir_all(&bindir).unwrap();
    let cxx_ok = have_cxx();
    if !cxx_ok {
        println!("note: no C++ compiler for this target, skipping *.cpp tests");
    }
    let mut sources: Vec<PathBuf> = fs::read_dir(root.join("tests/c"))
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "c" || (x == "cpp" && cxx_ok)))
        .filter(|p| filter.is_none_or(|f| p.file_name().unwrap().to_string_lossy().contains(f)))
        .collect();
    sources.sort();
    let failures = Mutex::new(Vec::<Failure>::new());
    let passed = std::sync::atomic::AtomicUsize::new(0);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(2);
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(src) = sources.get(i) else { break };
                    let name = src.file_stem().unwrap().to_string_lossy().to_string();
                    match run_test(&sysroot, &bindir, src) {
                        Ok(()) => {
                            println!("PASS {name}");
                            passed.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                        Err(message) => {
                            println!("FAIL {name}");
                            failures.lock().unwrap().push(Failure { name, message });
                        }
                    }
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap();
    for f in &failures {
        eprintln!("\n=== {} ===\n{}", f.name, f.message);
    }
    println!(
        "\n{} passed, {} failed",
        passed.load(std::sync::atomic::Ordering::Relaxed),
        failures.len()
    );
    if failures.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Parses the `name\tvalue\tunit` lines the benchmark prints.
fn parse_bench(out: &str) -> Vec<(String, f64, String)> {
    out.lines()
        .filter_map(|l| {
            let mut it = l.split('\t');
            let name = it.next()?.to_string();
            let value = it.next()?.parse().ok()?;
            let unit = it.next()?.to_string();
            Some((name, value, unit))
        })
        .collect()
}

fn bench(filter: Option<&str>, release: bool) -> ExitCode {
    let sysroot = match build(release) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };
    let root = root();
    let bindir = root.join("target/bench");
    fs::create_dir_all(&bindir).unwrap();
    // "alloc" selects the allocator workload program; anything else is a
    // section filter for the main benchmark.
    let (src, filter) = if filter == Some("alloc") {
        (root.join("bench/alloc.c"), None)
    } else {
        (root.join("bench/bench.c"), filter)
    };
    let ours = bindir.join("bench-rustlibc");
    let theirs = bindir.join("bench-glibc");
    let extra = vec!["-fno-builtin".to_string(), "-pthread".to_string()];
    if !run(&mut compile_cmd(&sysroot, &src, &ours, &extra)) {
        eprintln!("error: compiling the benchmark against rustlibc failed");
        return ExitCode::FAILURE;
    }
    if !run(Command::new(cc())
        .args([
            "-std=gnu11",
            "-O2",
            "-static",
            "-fno-builtin",
            "-pthread",
            "-o",
        ])
        .arg(&theirs)
        .arg(&src))
    {
        eprintln!("error: compiling the benchmark against glibc failed");
        return ExitCode::FAILURE;
    }
    let mut results = Vec::new();
    for bin in [&ours, &theirs] {
        let mut cmd = Command::new(bin);
        if let Some(f) = filter {
            cmd.arg(f);
        }
        match cmd.output() {
            Ok(o) if o.status.success() => {
                results.push(parse_bench(&String::from_utf8_lossy(&o.stdout)))
            }
            Ok(o) => {
                eprintln!(
                    "error: {} failed: {}",
                    bin.display(),
                    String::from_utf8_lossy(&o.stderr)
                );
                return ExitCode::FAILURE;
            }
            Err(e) => {
                eprintln!("error: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    println!(
        "{:<28} {:>12} {:>12} {:>8}",
        "benchmark", "rustlibc", "glibc", "ratio"
    );
    for (o, g) in results[0].iter().zip(results[1].iter()) {
        // Ratio > 1 means rustlibc is better: faster, or (for memory) smaller.
        let ratio = if o.2 == "GB/s" { o.1 / g.1 } else { g.1 / o.1 };
        println!(
            "{:<28} {:>7.2} {:<4} {:>7.2} {:<4} {:>7.2}x",
            o.0, o.1, o.2, g.1, g.2, ratio
        );
    }
    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let release = !args.iter().any(|a| a == "--debug");
    if args.iter().any(|a| a == "--aarch64") {
        *TARGET.lock().unwrap() = Target::Aarch64;
    }
    if args.iter().any(|a| a == "--pie") {
        *PIE.lock().unwrap() = true;
    }
    let args: Vec<&str> = args
        .iter()
        .map(String::as_str)
        .filter(|a| *a != "--debug" && *a != "--aarch64" && *a != "--pie")
        .collect();
    match args.as_slice() {
        ["build"] => match build(release) {
            Ok(s) => {
                println!("sysroot at {}", s.display());
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("error: {e}");
                ExitCode::FAILURE
            }
        },
        ["test"] => test(None, release),
        ["test", filter] => test(Some(filter), release),
        ["bench"] => bench(None, release),
        ["bench", filter] => bench(Some(filter), release),
        _ => {
            eprintln!(
                "usage: cargo xtask [--debug] [--aarch64] [--pie] build | test [FILTER] | bench [mem|malloc|stdlib|alloc]"
            );
            ExitCode::FAILURE
        }
    }
}
