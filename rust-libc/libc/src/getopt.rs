//! `getopt`, `getopt_long` and `getopt_long_only` with GNU semantics
//! (argument permutation unless the option string starts with `+` or
//! `POSIXLY_CORRECT` is set).

use crate::c_char;
use crate::stdio::printf::Sink;
use core::ffi::c_int;
use core::ptr;

/// `optarg`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut optarg: *mut c_char = ptr::null_mut();
/// `optind`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut optind: c_int = 1;
/// `opterr`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut opterr: c_int = 1;
/// `optopt`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut optopt: c_int = 0;
/// `optreset` (BSD): set to 1 to restart scanning.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut optreset: c_int = 0;

/// Position inside a cluster of short options (`-abc`).
static mut OPTPOS: usize = 0;

/// `struct option`.
#[repr(C)]
pub struct LongOption {
    /// Option name.
    pub name: *const c_char,
    /// 0 no argument, 1 required, 2 optional.
    pub has_arg: c_int,
    /// If non-null, receives `val` and 0 is returned.
    pub flag: *mut c_int,
    /// Value to return (or store).
    pub val: c_int,
}

/// Prints a diagnostic on stderr.
fn report(argv0: *const c_char, what: &[u8], opt: &[u8]) {
    // SAFETY: stderr is always valid.
    let mut g = unsafe { crate::stdio::lock(crate::stdio::stderr) };
    let mut out = crate::stdio::printf::Staged::new(&mut g);
    // SAFETY: argv[0] is NUL-terminated.
    let name = unsafe {
        core::slice::from_raw_parts(
            argv0 as *const u8,
            crate::string::search::strlen(argv0 as *const u8),
        )
    };
    out.write(name);
    out.write(b": ");
    out.write(what);
    out.write(opt);
    out.write(b"\n");
    out.finish();
}

/// # Safety
/// `p` must be NUL-terminated.
unsafe fn cstr<'a>(p: *const c_char) -> &'a [u8] {
    // SAFETY: caller contract.
    unsafe {
        core::slice::from_raw_parts(
            p as *const u8,
            crate::string::search::strlen(p as *const u8),
        )
    }
}

/// Moves the option at `argv[from]` down to index `to` (`to < from`),
/// shifting the non-options in between up by one so their order is kept.
///
/// # Safety
/// `argv` must have at least `from + 1` entries.
unsafe fn permute(argv: *mut *mut c_char, from: usize, to: usize) {
    // SAFETY: caller contract.
    unsafe {
        let tmp = *argv.add(from);
        let mut i = from;
        while i > to {
            *argv.add(i) = *argv.add(i - 1);
            i -= 1;
        }
        *argv.add(to) = tmp;
    }
}

/// Core of the `getopt` family.
///
/// # Safety
/// `argv` must hold `argc` NUL-terminated strings; `optstring` must be
/// NUL-terminated; `longopts` null or terminated by an all-zero entry.
unsafe fn getopt_core(
    argc: c_int,
    argv: *mut *mut c_char,
    optstring: *const c_char,
    longopts: *const LongOption,
    longindex: *mut c_int,
    long_only: bool,
) -> c_int {
    // SAFETY: the globals are only touched from here (single threaded by
    // POSIX's contract for getopt).
    unsafe {
        if optreset != 0 || optind == 0 {
            optreset = 0;
            optind = 1;
            OPTPOS = 0;
        }
        optarg = ptr::null_mut();
        if optind < 0 || optind >= argc || (*argv.add(optind as usize)).is_null() {
            return -1;
        }
        let opts = cstr(optstring);
        let posix = match opts.first() {
            Some(b'+') => true,
            Some(b'-') => false, // treated as GNU default
            _ => !crate::stdlib::env::getenv(c"POSIXLY_CORRECT".as_ptr()).is_null(),
        };
        let is_option = |i: usize| {
            let a = cstr(*argv.add(i));
            a.len() >= 2 && a[0] == b'-'
        };
        // GNU permutation: parse the next option wherever it is, then
        // move it (with any argument it consumed) in front of the
        // non-options skipped to reach it. A partially consumed cluster
        // stays where it is until it is finished, so it is found again
        // by the same scan.
        let start = optind as usize;
        let mut resumed = start;
        if !is_option(start) {
            if posix {
                return -1;
            }
            let mut j = start;
            while j < argc as usize && !(*argv.add(j)).is_null() && !is_option(j) {
                j += 1;
            }
            if j >= argc as usize || (*argv.add(j)).is_null() {
                return -1;
            }
            resumed = j;
            optind = j as c_int;
        }
        let ret = getopt_parse(argc, argv, opts, longopts, longindex, long_only);
        if resumed > start {
            let consumed = (optind as usize).saturating_sub(resumed);
            for k in 0..consumed {
                permute(argv, resumed + k, start + k);
            }
            optind = (start + consumed) as c_int;
        }
        ret
    }
}

/// Parses the option at `argv[optind]`, which must be an option (or
/// `--`). Advances `optind` past every argument it consumes.
///
/// # Safety
/// As for [`getopt_core`].
unsafe fn getopt_parse(
    argc: c_int,
    argv: *mut *mut c_char,
    opts: &[u8],
    longopts: *const LongOption,
    longindex: *mut c_int,
    long_only: bool,
) -> c_int {
    // SAFETY: as for `getopt_core`.
    unsafe {
        let opts = match opts.first() {
            Some(b'+') | Some(b'-') => &opts[1..],
            _ => opts,
        };
        let colon_mode = opts.first() == Some(&b':');
        let opts = if colon_mode { &opts[1..] } else { opts };
        let i = optind as usize;
        let arg = cstr(*argv.add(i));
        if OPTPOS >= arg.len() {
            // A position left over from a parse the caller abandoned.
            OPTPOS = 0;
        }
        if arg == b"--" {
            optind += 1;
            return -1;
        }

        // Long options.
        if !longopts.is_null()
            && OPTPOS == 0
            && (arg.starts_with(b"--") || (long_only && arg.len() >= 2))
        {
            let body = if arg.starts_with(b"--") {
                &arg[2..]
            } else {
                &arg[1..]
            };
            let (name, value) = match body.iter().position(|&b| b == b'=') {
                Some(p) => (&body[..p], Some(&body[p + 1..])),
                None => (body, None),
            };
            let mut found: Option<(usize, &LongOption)> = None;
            let mut ambiguous = false;
            let mut idx = 0;
            loop {
                let o = &*longopts.add(idx);
                if o.name.is_null() {
                    break;
                }
                let oname = cstr(o.name);
                if oname == name {
                    found = Some((idx, o));
                    ambiguous = false;
                    break;
                }
                if oname.starts_with(name) && !name.is_empty() {
                    if found.is_some() {
                        ambiguous = true;
                    } else {
                        found = Some((idx, o));
                    }
                }
                idx += 1;
            }
            let short_fallback = long_only
                && !arg.starts_with(b"--")
                && found.is_none()
                && name.len() == 1
                && opts.contains(&name[0]);
            if !short_fallback {
                let argv0 = *argv;
                let Some((idx, o)) = found.filter(|_| !ambiguous) else {
                    optind += 1;
                    optopt = 0;
                    if opterr != 0 && !colon_mode {
                        report(
                            argv0,
                            if ambiguous {
                                b"option is ambiguous: "
                            } else {
                                b"unrecognized option: "
                            },
                            arg,
                        );
                    }
                    return b'?' as c_int;
                };
                optind += 1;
                optarg = ptr::null_mut();
                match (o.has_arg, value) {
                    (0, Some(_)) => {
                        optopt = o.val;
                        if opterr != 0 && !colon_mode {
                            report(argv0, b"option does not take an argument: ", arg);
                        }
                        return b'?' as c_int;
                    }
                    (0, None) => {}
                    (_, Some(v)) => optarg = v.as_ptr() as *mut c_char,
                    (1, None) => {
                        if optind < argc && !(*argv.add(optind as usize)).is_null() {
                            optarg = *argv.add(optind as usize);
                            optind += 1;
                        } else {
                            optopt = o.val;
                            if opterr != 0 && !colon_mode {
                                report(argv0, b"option requires an argument: ", arg);
                            }
                            return if colon_mode {
                                b':' as c_int
                            } else {
                                b'?' as c_int
                            };
                        }
                    }
                    (_, None) => {}
                }
                if !longindex.is_null() {
                    *longindex = idx as c_int;
                }
                if !o.flag.is_null() {
                    *o.flag = o.val;
                    return 0;
                }
                return o.val;
            }
        }

        // Short options.
        if OPTPOS == 0 {
            OPTPOS = 1;
        }
        let c = arg[OPTPOS];
        OPTPOS += 1;
        let rest_empty = OPTPOS >= arg.len();
        let spec = opts.iter().position(|&b| b == c && b != b':');
        let argv0 = *argv;
        let Some(p) = spec else {
            optopt = c as c_int;
            if rest_empty {
                optind += 1;
                OPTPOS = 0;
            }
            if opterr != 0 && !colon_mode {
                report(argv0, b"unrecognized option: -", &[c]);
            }
            return b'?' as c_int;
        };
        let takes_arg = opts.get(p + 1) == Some(&b':');
        let optional = takes_arg && opts.get(p + 2) == Some(&b':');
        optarg = ptr::null_mut();
        if takes_arg {
            if !rest_empty {
                optarg = (*argv.add(i)).add(OPTPOS);
                optind += 1;
                OPTPOS = 0;
            } else if optional {
                optind += 1;
                OPTPOS = 0;
            } else {
                optind += 1;
                OPTPOS = 0;
                if optind < argc && !(*argv.add(optind as usize)).is_null() {
                    optarg = *argv.add(optind as usize);
                    optind += 1;
                } else {
                    optopt = c as c_int;
                    if opterr != 0 && !colon_mode {
                        report(argv0, b"option requires an argument: -", &[c]);
                    }
                    return if colon_mode {
                        b':' as c_int
                    } else {
                        b'?' as c_int
                    };
                }
            }
        } else if rest_empty {
            optind += 1;
            OPTPOS = 0;
        }
        c as c_int
    }
}

/// `getopt(3)`.
///
/// # Safety
/// As for [`getopt_core`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getopt(
    argc: c_int,
    argv: *mut *mut c_char,
    optstring: *const c_char,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { getopt_core(argc, argv, optstring, ptr::null(), ptr::null_mut(), false) }
}

/// `getopt_long(3)`.
///
/// # Safety
/// As for [`getopt_core`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getopt_long(
    argc: c_int,
    argv: *mut *mut c_char,
    optstring: *const c_char,
    longopts: *const LongOption,
    longindex: *mut c_int,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { getopt_core(argc, argv, optstring, longopts, longindex, false) }
}

/// `getopt_long_only(3)`.
///
/// # Safety
/// As for [`getopt_core`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getopt_long_only(
    argc: c_int,
    argv: *mut *mut c_char,
    optstring: *const c_char,
    longopts: *const LongOption,
    longindex: *mut c_int,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { getopt_core(argc, argv, optstring, longopts, longindex, true) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::{CStr, CString};

    /// getopt keeps global state, so its tests must not run concurrently.
    static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn run(args: &[&str], optstring: &str) -> (Vec<(c_int, Option<String>)>, Vec<String>) {
        let owned: Vec<CString> = args.iter().map(|a| CString::new(*a).unwrap()).collect();
        let mut argv: Vec<*mut c_char> = owned.iter().map(|c| c.as_ptr() as *mut c_char).collect();
        argv.push(ptr::null_mut());
        let opts = CString::new(optstring).unwrap();
        let mut out = Vec::new();
        // SAFETY: valid argv; getopt is single-threaded in tests.
        unsafe {
            optind = 1;
            opterr = 0;
            loop {
                let c = getopt(args.len() as c_int, argv.as_mut_ptr(), opts.as_ptr());
                if c == -1 {
                    break;
                }
                let a = if optarg.is_null() {
                    None
                } else {
                    Some(CStr::from_ptr(optarg).to_str().unwrap().to_string())
                };
                out.push((c, a));
            }
            let rest = argv[optind as usize..args.len()]
                .iter()
                .map(|p| CStr::from_ptr(*p).to_str().unwrap().to_string())
                .collect();
            (out, rest)
        }
    }

    #[test]
    fn short_options() {
        let _guard = SERIAL.lock().unwrap();
        let (o, rest) = run(
            &["prog", "-a", "-bval", "-c", "arg", "file", "-d"],
            "ab:c:d",
        );
        assert_eq!(
            o,
            vec![
                (b'a' as c_int, None),
                (b'b' as c_int, Some("val".into())),
                (b'c' as c_int, Some("arg".into())),
                (b'd' as c_int, None)
            ]
        );
        assert_eq!(rest, vec!["file"]);
        let (o, rest) = run(&["prog", "-ab", "x", "--", "-c"], "ab:c");
        assert_eq!(
            o,
            vec![(b'a' as c_int, None), (b'b' as c_int, Some("x".into()))]
        );
        assert_eq!(rest, vec!["-c"]);
        let (o, _) = run(&["prog", "-z"], "ab");
        assert_eq!(o, vec![(b'?' as c_int, None)]);
        let (o, _) = run(&["prog", "-b"], ":ab:");
        assert_eq!(o, vec![(b':' as c_int, None)]);
        let (o, _) = run(&["prog", "-o", "-ofile"], "o::");
        assert_eq!(
            o,
            vec![(b'o' as c_int, None), (b'o' as c_int, Some("file".into()))]
        );
        let (o, rest) = run(&["prog", "file", "-a"], "+a");
        assert_eq!(o, vec![]);
        assert_eq!(rest, vec!["file", "-a"]);
    }

    #[test]
    fn long_options() {
        let _guard = SERIAL.lock().unwrap();
        let names = [c"verbose", c"output", c"level"];
        let mut flag = 0;
        let longopts = [
            LongOption {
                name: names[0].as_ptr(),
                has_arg: 0,
                flag: &mut flag,
                val: 7,
            },
            LongOption {
                name: names[1].as_ptr(),
                has_arg: 1,
                flag: ptr::null_mut(),
                val: b'o' as c_int,
            },
            LongOption {
                name: names[2].as_ptr(),
                has_arg: 2,
                flag: ptr::null_mut(),
                val: b'l' as c_int,
            },
            LongOption {
                name: ptr::null(),
                has_arg: 0,
                flag: ptr::null_mut(),
                val: 0,
            },
        ];
        let args = [
            "prog",
            "--verbose",
            "--output=out.txt",
            "--lev",
            "--out",
            "x",
            "-q",
            "rest",
        ];
        let owned: Vec<CString> = args.iter().map(|a| CString::new(*a).unwrap()).collect();
        let mut argv: Vec<*mut c_char> = owned.iter().map(|c| c.as_ptr() as *mut c_char).collect();
        argv.push(ptr::null_mut());
        let mut got = Vec::new();
        // SAFETY: valid inputs.
        unsafe {
            optind = 1;
            opterr = 0;
            loop {
                let mut idx = -1;
                let c = getopt_long(
                    args.len() as c_int,
                    argv.as_mut_ptr(),
                    c"q".as_ptr(),
                    longopts.as_ptr(),
                    &mut idx,
                );
                if c == -1 {
                    break;
                }
                let a = if optarg.is_null() {
                    None
                } else {
                    Some(CStr::from_ptr(optarg).to_str().unwrap().to_string())
                };
                got.push((c, idx, a));
            }
            assert_eq!(flag, 7);
            assert_eq!(
                got,
                vec![
                    (0, 0, None),
                    (b'o' as c_int, 1, Some("out.txt".into())),
                    (b'l' as c_int, 2, None),
                    (b'o' as c_int, 1, Some("x".into())),
                    (b'q' as c_int, -1, None),
                ]
            );
            assert_eq!(optind as usize, args.len() - 1);
        }
    }
}
