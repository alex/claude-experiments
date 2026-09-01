//! x86_64 specific code.

use core::arch::{asm, global_asm};

pub mod cpu;
pub mod nr;
pub mod va;

// The ELF entry point.
//
// The kernel starts us with `rsp` pointing at `argc`, followed by `argv`,
// `envp` and the auxiliary vector. We clear the frame pointer to terminate
// stack walks, pass the initial stack pointer to Rust and align the stack
// as the ABI requires before the first `call`.
#[cfg(not(test))]
global_asm!(
    ".globl _start",
    ".type _start,@function",
    "_start:",
    "xor ebp, ebp",
    "mov rdi, rsp",
    "and rsp, -16",
    "call {start}",
    "ud2",
    ".size _start, .-_start",
    start = sym crate::start::start_c,
);

// Thread creation trampoline (the same design as musl's `__clone`).
//
// `clone_thread(entry, stack, flags, arg, ptid, tls, ctid)`: performs the
// clone syscall; the parent returns the child's tid (or -errno); the child
// starts on `stack` and calls `entry(arg)`, then exits with its return
// value. The child never returns from this function.
#[cfg(not(test))]
global_asm!(
    ".globl __rustlibc_clone",
    ".type __rustlibc_clone,@function",
    "__rustlibc_clone:",
    "mov r11, rdi",       // entry (temporarily)
    "mov rdi, rdx",       // flags
    "mov rdx, r8",        // ptid
    "mov r8, r9",         // tls
    "mov r10, [rsp + 8]", // ctid
    "mov r9, r11",        // entry: r9 survives `syscall`, r11 does not
    "and rsi, -16",       // child stack, aligned
    "sub rsi, 8",
    "mov [rsi], rcx", // push arg on the child stack
    "mov eax, 56",    // SYS_clone
    "syscall",
    "test eax, eax",
    "jnz 1f",
    // Child.
    "xor ebp, ebp",
    "pop rdi",
    "call r9",
    "mov edi, eax",
    "mov eax, 60", // SYS_exit
    "syscall",
    "hlt",
    "1: ret",
    ".size __rustlibc_clone, .-__rustlibc_clone",
);

// Unmaps the calling thread's own stack and exits: after `munmap` there is
// no stack to return to, so both syscalls must be issued from assembly.
#[cfg(not(test))]
global_asm!(
    ".globl __rustlibc_unmapself",
    ".type __rustlibc_unmapself,@function",
    "__rustlibc_unmapself:",
    "mov eax, 11", // SYS_munmap
    "syscall",
    "xor edi, edi",
    "mov eax, 60", // SYS_exit
    "syscall",
    "hlt",
    ".size __rustlibc_unmapself, .-__rustlibc_unmapself",
);

#[cfg(not(test))]
unsafe extern "C" {
    fn __rustlibc_clone(
        entry: extern "C" fn(*mut core::ffi::c_void) -> core::ffi::c_int,
        stack: *mut u8,
        flags: usize,
        arg: *mut core::ffi::c_void,
        ptid: *mut u32,
        tls: *mut u8,
        ctid: *mut u32,
    ) -> isize;
    fn __rustlibc_unmapself(base: *mut u8, len: usize) -> !;
}

/// Creates a thread. See the assembly above.
///
/// # Safety
/// `stack` must be the top of a mapped stack; `tls` a prepared TCB.
#[cfg(not(test))]
pub unsafe fn clone_thread(
    entry: extern "C" fn(*mut core::ffi::c_void) -> core::ffi::c_int,
    stack: *mut u8,
    flags: usize,
    arg: *mut core::ffi::c_void,
    ptid: *mut u32,
    tls: *mut u8,
    ctid: *mut u32,
) -> crate::sys::Result<u32> {
    // SAFETY: caller contract.
    let r = unsafe { __rustlibc_clone(entry, stack, flags, arg, ptid, tls, ctid) };
    crate::sys::check(r as usize).map(|v| v as u32)
}

/// Unmaps `[base, base+len)` (the caller's stack) and exits the thread.
///
/// # Safety
/// Nothing may be used after this call; it does not return.
#[cfg(not(test))]
pub unsafe fn unmap_self_and_exit(base: *mut u8, len: usize) -> ! {
    // SAFETY: caller contract.
    unsafe { __rustlibc_unmapself(base, len) }
}

/// Performs a raw system call with no arguments.
///
/// # Safety
/// The caller is responsible for the semantics of the call.
#[inline(always)]
pub unsafe fn syscall0(n: usize) -> usize {
    let ret: usize;
    // SAFETY: the `syscall` instruction clobbers rcx and r11 and returns in rax.
    unsafe {
        asm!("syscall", inlateout("rax") n => ret, out("rcx") _, out("r11") _, options(nostack));
    }
    ret
}

/// Performs a raw system call with one argument.
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall1(n: usize, a1: usize) -> usize {
    let ret: usize;
    // SAFETY: as in `syscall0`.
    unsafe {
        asm!("syscall", inlateout("rax") n => ret, in("rdi") a1,
             out("rcx") _, out("r11") _, options(nostack));
    }
    ret
}

/// Performs a raw system call with two arguments.
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall2(n: usize, a1: usize, a2: usize) -> usize {
    let ret: usize;
    // SAFETY: as in `syscall0`.
    unsafe {
        asm!("syscall", inlateout("rax") n => ret, in("rdi") a1, in("rsi") a2,
             out("rcx") _, out("r11") _, options(nostack));
    }
    ret
}

/// Performs a raw system call with three arguments.
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall3(n: usize, a1: usize, a2: usize, a3: usize) -> usize {
    let ret: usize;
    // SAFETY: as in `syscall0`.
    unsafe {
        asm!("syscall", inlateout("rax") n => ret, in("rdi") a1, in("rsi") a2, in("rdx") a3,
             out("rcx") _, out("r11") _, options(nostack));
    }
    ret
}

/// Performs a raw system call with four arguments.
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall4(n: usize, a1: usize, a2: usize, a3: usize, a4: usize) -> usize {
    let ret: usize;
    // SAFETY: as in `syscall0`.
    unsafe {
        asm!("syscall", inlateout("rax") n => ret, in("rdi") a1, in("rsi") a2, in("rdx") a3,
             in("r10") a4, out("rcx") _, out("r11") _, options(nostack));
    }
    ret
}

/// Performs a raw system call with five arguments.
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall5(n: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize) -> usize {
    let ret: usize;
    // SAFETY: as in `syscall0`.
    unsafe {
        asm!("syscall", inlateout("rax") n => ret, in("rdi") a1, in("rsi") a2, in("rdx") a3,
             in("r10") a4, in("r8") a5, out("rcx") _, out("r11") _, options(nostack));
    }
    ret
}

/// Performs a raw system call with six arguments.
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall6(
    n: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
    a6: usize,
) -> usize {
    let ret: usize;
    // SAFETY: as in `syscall0`.
    unsafe {
        asm!("syscall", inlateout("rax") n => ret, in("rdi") a1, in("rsi") a2, in("rdx") a3,
             in("r10") a4, in("r8") a5, in("r9") a6, out("rcx") _, out("r11") _, options(nostack));
    }
    ret
}

/// Returns the thread pointer (`%fs` base).
///
/// On x86_64 the first word of the thread control block holds a pointer to
/// itself, so reading `%fs:0` yields the TCB address.
///
/// # Safety
/// The thread pointer must have been set with [`set_thread_pointer`].
#[inline(always)]
pub unsafe fn thread_pointer() -> *mut u8 {
    let tp: *mut u8;
    // SAFETY: reads the self-pointer stored at the start of the TCB.
    unsafe {
        asm!("mov {}, fs:0", out(reg) tp, options(nostack, readonly, preserves_flags));
    }
    tp
}

/// Sets the thread pointer (`%fs` base) for the calling thread.
///
/// # Safety
/// `tp` must point to a valid, self-referencing TCB.
pub unsafe fn set_thread_pointer(tp: *mut u8) -> crate::sys::Result<()> {
    const ARCH_SET_FS: usize = 0x1002;
    // SAFETY: arch_prctl(ARCH_SET_FS) only changes the fs base register.
    unsafe { crate::sys::check(syscall2(nr::ARCH_PRCTL, ARCH_SET_FS, tp as usize)).map(|_| ()) }
}

/// Executes an instruction that reliably kills the process (`ud2`); the
/// last resort in `abort`.
#[inline(always)]
pub fn trap() -> ! {
    // SAFETY: `ud2` raises SIGILL; it never returns.
    unsafe { asm!("ud2", options(noreturn, nostack)) }
}
