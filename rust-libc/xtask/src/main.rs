//! Developer tasks for rustlibc.
//!
//! ```text
//! cargo xtask build      # build libc.a and assemble target/sysroot
//! cargo xtask test       # build, then compile and run every tests/c/*.c
//! cargo xtask test NAME  # only tests whose file name contains NAME
//! ```
//!
//! Each C test is compiled against the sysroot with `-static -nostdlib`
//! and run. A test passes when its exit status matches (0 by default, or
//! the `// expect-exit: N` / `// expect-signal: NAME` directive in the
//! source) and, if a sibling `NAME.stdout` file exists, its standard
//! output matches that file exactly.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::sync::Mutex;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf()
}

fn cc() -> String {
    std::env::var("CC").unwrap_or_else(|_| "cc".to_string())
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
    if !run(&mut cargo) {
        return Err("cargo build failed".into());
    }
    let profile = if release { "release" } else { "debug" };
    let lib = root.join("target").join(profile).join("libc.a");
    let sysroot = root.join("target/sysroot");
    let libdir = sysroot.join("lib");
    fs::create_dir_all(&libdir).map_err(|e| e.to_string())?;
    fs::copy(&lib, libdir.join("libc.a")).map_err(|e| e.to_string())?;
    // Provide the empty archives that gcc's default link line asks for.
    for name in ["libm.a", "libpthread.a", "librt.a", "libdl.a"] {
        let p = libdir.join(name);
        if !p.exists() {
            if !run(Command::new("ar").arg("rcs").arg(&p)) {
                return Err(format!("ar failed for {}", p.display()));
            }
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
    let out = Command::new(cc()).arg("-print-file-name=include").output().expect("run cc");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

/// Command line to compile a C program against the sysroot.
fn compile_cmd(sysroot: &Path, src: &Path, out: &Path) -> Command {
    let mut cmd = Command::new(cc());
    cmd.args([
        "-std=gnu11",
        "-O2",
        "-g",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-fstack-protector-strong",
        "-static",
        "-no-pie",
        "-fno-pie",
        "-nostdlib",
        "-nostartfiles",
        "-nostdinc",
        "-isystem",
    ])
    .arg(sysroot.join("include"))
    .arg("-isystem")
    .arg(compiler_include_dir())
    .arg(src)
    .arg("-o")
    .arg(out)
    .arg("-L")
    .arg(sysroot.join("lib"))
    .args(["-lc", "-lgcc"]);
    cmd
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
            let known = ["SIGABRT", "SIGSEGV", "SIGILL", "SIGFPE", "SIGKILL", "SIGTERM", "SIGTRAP"];
            return Expect::Signal(known.iter().copied().find(|k| *k == name).expect("unknown signal"));
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
    let bin = bindir.join(&name);
    let out = compile_cmd(sysroot, src, &bin).output().map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(format!("compile failed:\n{}", String::from_utf8_lossy(&out.stderr)));
    }
    let mut cmd = Command::new(&bin);
    cmd.current_dir(bindir).stdin(Stdio::null()).env_clear().env("PATH", "/usr/bin:/bin").env("TESTVAR", "value");
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
    let bindir = root.join("target/ctests");
    fs::create_dir_all(&bindir).unwrap();
    let mut sources: Vec<PathBuf> = fs::read_dir(root.join("tests/c"))
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "c"))
        .filter(|p| filter.is_none_or(|f| p.file_name().unwrap().to_string_lossy().contains(f)))
        .collect();
    sources.sort();
    let failures = Mutex::new(Vec::<Failure>::new());
    let passed = std::sync::atomic::AtomicUsize::new(0);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let workers = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(2);
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
    println!("\n{} passed, {} failed", passed.load(std::sync::atomic::Ordering::Relaxed), failures.len());
    if failures.is_empty() { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let release = !args.iter().any(|a| a == "--debug");
    let args: Vec<&str> = args.iter().map(String::as_str).filter(|a| *a != "--debug").collect();
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
        _ => {
            eprintln!("usage: cargo xtask [--debug] build | test [FILTER]");
            ExitCode::FAILURE
        }
    }
}
