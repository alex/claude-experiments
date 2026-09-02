//! Process creation and control: `fork`, `exec*`, `wait*`, `system`.

use crate::c_char;
use crate::errno::{CReturn, Errno};
use crate::start::environ;
use crate::sys;
use crate::thread::pthread::ATFORK;
use core::ffi::{c_int, c_void};
use core::ptr;

/// `_Fork(3)`: the raw fork, async-signal-safe, no handlers.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn _Fork() -> c_int {
    match sys::fork() {
        Ok(0) => {
            after_fork_child();
            0
        }
        Ok(pid) => pid,
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// Fixes up the calling thread's state in a freshly forked child.
fn after_fork_child() {
    // SAFETY: the TCB is valid; we are the only thread now.
    unsafe {
        (*crate::thread::current())
            .tid
            .store(sys::gettid() as u32, core::sync::atomic::Ordering::Relaxed);
    }
    crate::thread::pthread::after_fork_in_child();
}

/// `fork(2)`: runs the `pthread_atfork` handlers and keeps the
/// allocator and stdio consistent across the fork.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fork() -> c_int {
    ATFORK.lock().run_prepare();
    crate::malloc::prefork();
    crate::thread::pthread::prefork();
    crate::stdio::prefork();
    let r = sys::fork();
    // SAFETY: matched with the prefork calls above.
    unsafe {
        crate::stdio::postfork(r == Ok(0));
        crate::thread::pthread::postfork();
        crate::malloc::postfork();
    }
    match r {
        Ok(0) => {
            after_fork_child();
            // The child is single-threaded; `ATFORK`'s lock may have
            // been held by another thread in the parent.
            ATFORK.raw().force_unlock();
            ATFORK.lock().run_after(true);
            0
        }
        Ok(pid) => {
            ATFORK.lock().run_after(false);
            pid
        }
        Err(e) => {
            ATFORK.lock().run_after(false);
            e.set();
            -1
        }
    }
}

/// `vfork(2)`: implemented as `fork`, which is strictly safer.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn vfork() -> c_int {
    fork()
}

/// `execve(2)`.
///
/// # Safety
/// All pointers must be valid NUL-terminated strings / NULL-terminated
/// arrays.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn execve(
    path: *const c_char,
    argv: *const *const c_char,
    envp: *const *const c_char,
) -> c_int {
    // SAFETY: forwarded.
    unsafe {
        sys::execve(
            path as *const u8,
            argv as *const *const u8,
            envp as *const *const u8,
        )
    }
    .set();
    -1
}

/// `execv(3)`.
///
/// # Safety
/// As for [`execve`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn execv(path: *const c_char, argv: *const *const c_char) -> c_int {
    // SAFETY: forwarded; `environ` is NULL-terminated.
    unsafe { execve(path, argv, environ as *const *const c_char) }
}

/// `fexecve(3)`, via `execveat(fd, "", AT_EMPTY_PATH)`.
///
/// # Safety
/// As for [`execve`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fexecve(
    fd: c_int,
    argv: *const *const c_char,
    envp: *const *const c_char,
) -> c_int {
    const EXECVEAT: usize = 322;
    const AT_EMPTY_PATH: usize = 0x1000;
    // SAFETY: caller contract; the empty path is a literal.
    let r = unsafe {
        crate::arch::syscall5(
            EXECVEAT,
            fd as usize,
            c"".as_ptr() as usize,
            argv as usize,
            envp as usize,
            AT_EMPTY_PATH,
        )
    };
    sys::check(r).map(drop).c_ret()
}

/// `execvpe(3)`: searches `PATH` when `file` contains no slash.
///
/// # Safety
/// As for [`execve`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn execvpe(
    file: *const c_char,
    argv: *const *const c_char,
    envp: *const *const c_char,
) -> c_int {
    // SAFETY: caller contract.
    let name = unsafe {
        core::slice::from_raw_parts(
            file as *const u8,
            crate::string::search::strlen(file as *const u8),
        )
    };
    if name.is_empty() {
        Errno::ENOENT.set();
        return -1;
    }
    if name.contains(&b'/') {
        // SAFETY: forwarded.
        return unsafe { execve(file, argv, envp) };
    }
    // SAFETY: NUL-terminated literal.
    let path = unsafe { crate::stdlib::env::getenv(c"PATH".as_ptr()) };
    let path: &[u8] = if path.is_null() {
        b"/usr/local/bin:/bin:/usr/bin"
    } else {
        // SAFETY: getenv returns NUL-terminated strings.
        unsafe {
            core::slice::from_raw_parts(
                path as *const u8,
                crate::string::search::strlen(path as *const u8),
            )
        }
    };
    let mut seen_eacces = false;
    let mut buf = [0u8; 4096 + 256];
    for dir in path.split(|&b| b == b':') {
        let dir: &[u8] = if dir.is_empty() { b"." } else { dir };
        if dir.len() + 1 + name.len() + 1 > buf.len() {
            continue;
        }
        buf[..dir.len()].copy_from_slice(dir);
        buf[dir.len()] = b'/';
        buf[dir.len() + 1..dir.len() + 1 + name.len()].copy_from_slice(name);
        buf[dir.len() + 1 + name.len()] = 0;
        // SAFETY: `buf` is NUL-terminated; other pointers forwarded.
        let e = unsafe {
            sys::execve(
                buf.as_ptr(),
                argv as *const *const u8,
                envp as *const *const u8,
            )
        };
        match e {
            Errno::EACCES => seen_eacces = true,
            Errno::ENOENT | Errno::ENOTDIR => {}
            e => {
                e.set();
                return -1;
            }
        }
    }
    (if seen_eacces {
        Errno::EACCES
    } else {
        Errno::ENOENT
    })
    .set();
    -1
}

/// `execvp(3)`.
///
/// # Safety
/// As for [`execve`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn execvp(file: *const c_char, argv: *const *const c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe { execvpe(file, argv, environ as *const *const c_char) }
}

/// Collects the NULL-terminated argument list of `execl*` from a
/// `va_list` into `buf`, then calls `f`. Falls back to `malloc` for very
/// long lists.
///
/// # Safety
/// `first` and the variadic arguments must be valid strings ending in
/// NULL; for `execle` the NULL is followed by `envp`.
unsafe fn with_arg_list(
    first: *const c_char,
    ap: &mut crate::arch::va::VaList,
    take_envp: bool,
    f: impl FnOnce(*const *const c_char, *const *const c_char) -> c_int,
) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        let mut probe = core::ptr::read(ap);
        let mut count = 1;
        while !probe.ptr().is_null() {
            count += 1;
        }
        const STACK_ARGS: usize = 128;
        let mut stack = [ptr::null::<c_char>(); STACK_ARGS];
        let heap;
        let args: &mut [*const c_char] = if count < STACK_ARGS {
            &mut stack
        } else {
            heap = crate::malloc::alloc((count + 1) * 8) as *mut *const c_char;
            if heap.is_null() {
                Errno::ENOMEM.set();
                return -1;
            }
            core::slice::from_raw_parts_mut(heap, count + 1)
        };
        args[0] = first;
        for slot in args.iter_mut().take(count).skip(1) {
            *slot = ap.ptr() as *const c_char;
        }
        args[count] = ptr::null();
        let _ = ap.ptr(); // the terminating NULL
        let envp = if take_envp {
            ap.ptr() as *const *const c_char
        } else {
            environ as *const *const c_char
        };
        let r = f(args.as_ptr(), envp);
        if count >= STACK_ARGS {
            crate::malloc::dealloc(args.as_mut_ptr() as *mut u8);
        }
        r
    }
}

/// `execl` implementation behind the variadic stub.
///
/// # Safety
/// As for [`execve`].
pub unsafe extern "C" fn vexecl(
    path: *const c_char,
    arg0: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { with_arg_list(arg0, &mut *ap, false, |argv, envp| execve(path, argv, envp)) }
}

/// `execlp` implementation behind the variadic stub.
///
/// # Safety
/// As for [`execve`].
pub unsafe extern "C" fn vexeclp(
    file: *const c_char,
    arg0: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    // SAFETY: forwarded.
    unsafe {
        with_arg_list(arg0, &mut *ap, false, |argv, envp| {
            execvpe(file, argv, envp)
        })
    }
}

/// `execle` implementation behind the variadic stub.
///
/// # Safety
/// As for [`execve`].
pub unsafe extern "C" fn vexecle(
    path: *const c_char,
    arg0: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { with_arg_list(arg0, &mut *ap, true, |argv, envp| execve(path, argv, envp)) }
}

#[cfg(not(test))]
mod stubs {
    use crate::arch::va::variadic_stub;
    variadic_stub!(execl, 2, "rdx", super::vexecl);
    variadic_stub!(execlp, 2, "rdx", super::vexeclp);
    variadic_stub!(execle, 2, "rdx", super::vexecle);
}

/// `wait4(2)`.
///
/// # Safety
/// `status` and `rusage` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wait4(
    pid: c_int,
    status: *mut c_int,
    options: c_int,
    rusage: *mut c_void,
) -> c_int {
    crate::thread::cancel_point();
    // SAFETY: forwarded.
    unsafe { sys::wait4(pid, status, options, rusage) }.c_ret()
}

/// `waitpid(2)`.
///
/// # Safety
/// `status` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn waitpid(pid: c_int, status: *mut c_int, options: c_int) -> c_int {
    crate::thread::cancel_point();
    // SAFETY: forwarded.
    unsafe { wait4(pid, status, options, ptr::null_mut()) }
}

/// `wait(2)`.
///
/// # Safety
/// `status` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wait(status: *mut c_int) -> c_int {
    // SAFETY: forwarded.
    unsafe { wait4(-1, status, 0, ptr::null_mut()) }
}

/// `waitid(2)`.
///
/// # Safety
/// `info` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn waitid(
    idtype: c_int,
    id: c_int,
    info: *mut c_void,
    options: c_int,
) -> c_int {
    const WAITID: usize = 247;
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall5(
            WAITID,
            idtype as usize,
            id as usize,
            info as usize,
            options as usize,
            0,
        )
    };
    sys::check(r).map(drop).c_ret()
}

/// `system(3)`.
///
/// # Safety
/// `cmd` must be null or NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn system(cmd: *const c_char) -> c_int {
    use crate::signal::{SIG_IGN, SigAction, SigSet, sigaction, sigprocmask};
    if cmd.is_null() {
        // Is a shell available?
        // SAFETY: literal path.
        return unsafe {
            sys::openat(
                sys::AT_FDCWD,
                c"/bin/sh".as_ptr() as *const u8,
                sys::O_RDONLY | sys::O_CLOEXEC,
                0,
            )
        }
        .map(|fd| {
            let _ = sys::close(fd);
            1
        })
        .unwrap_or(0);
    }
    let ignore = SigAction {
        handler: SIG_IGN,
        mask: SigSet::empty(),
        flags: 0,
        restorer: 0,
    };
    let mut old_int = ignore;
    let mut old_quit = ignore;
    let mut old_mask = SigSet::empty();
    let mut block = SigSet::empty();
    // SAFETY: valid pointers.
    unsafe {
        crate::signal::sigaddset(&mut block, sys::SIGCHLD);
        sigaction(sys::SIGINT, &ignore, &mut old_int);
        sigaction(sys::SIGQUIT, &ignore, &mut old_quit);
        sigprocmask(sys::SIG_BLOCK, &block, &mut old_mask);
    }
    let pid = fork();
    if pid == 0 {
        // Child: restore the signal state and run the shell.
        // SAFETY: valid pointers and NUL-terminated strings.
        unsafe {
            sigaction(sys::SIGINT, &old_int, ptr::null_mut());
            sigaction(sys::SIGQUIT, &old_quit, ptr::null_mut());
            sigprocmask(sys::SIG_SETMASK, &old_mask, ptr::null_mut());
            let argv = [c"sh".as_ptr(), c"-c".as_ptr(), cmd, ptr::null()];
            execve(
                c"/bin/sh".as_ptr(),
                argv.as_ptr(),
                environ as *const *const c_char,
            );
            crate::exit::_exit(127);
        }
    }
    let mut status = -1;
    if pid > 0 {
        loop {
            // SAFETY: valid pointer.
            match unsafe { sys::wait4(pid, &mut status, 0, ptr::null_mut()) } {
                Ok(_) => break,
                Err(Errno::EINTR) => {}
                Err(_) => {
                    status = -1;
                    break;
                }
            }
        }
    }
    // SAFETY: valid pointers.
    unsafe {
        sigaction(sys::SIGINT, &old_int, ptr::null_mut());
        sigaction(sys::SIGQUIT, &old_quit, ptr::null_mut());
        sigprocmask(sys::SIG_SETMASK, &old_mask, ptr::null_mut());
    }
    status
}
