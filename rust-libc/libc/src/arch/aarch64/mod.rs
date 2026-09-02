//! AArch64 specific code.

use core::arch::{asm, global_asm};

pub mod cpu;
pub mod fenv;
pub mod nr;
pub mod va;

// The ELF entry point: the kernel starts us with `sp` pointing at `argc`.
// The frame pointer and link register are cleared to terminate stack
// walks; the stack is already 16-byte aligned.
#[cfg(not(test))]
global_asm!(
    ".globl _start",
    ".type _start,%function",
    "_start:",
    "mov x29, #0",
    "mov x30, #0",
    "mov x0, sp",
    "bl {start}",
    "brk #0",
    ".size _start, .-_start",
    start = sym crate::start::start_c,
);

// Thread creation trampoline.
//
// `clone_thread(entry, stack, flags, arg, ptid, tls, ctid)`: the parent
// returns the child's tid (or -errno); the child starts on `stack`, calls
// `entry(arg)` and exits with its return value.
#[cfg(not(test))]
global_asm!(
    ".globl __rustlibc_clone",
    ".type __rustlibc_clone,%function",
    "__rustlibc_clone:",
    // Save entry and arg on the child stack (16-byte aligned).
    "and x1, x1, #-16",
    "stp x0, x3, [x1, #-16]!",
    // clone(flags, stack, ptid, tls, ctid)
    "mov x0, x2",
    "mov x2, x4",
    "mov x3, x5",
    "mov x4, x6",
    "mov x8, #220",
    "svc #0",
    "cbz x0, 1f",
    "ret",
    "1:",
    // Child: pop entry and arg, call, exit with the result.
    "ldp x1, x0, [sp], #16",
    "mov x29, #0",
    "mov x30, #0",
    "blr x1",
    "mov x8, #93",
    "svc #0",
    "brk #0",
    ".size __rustlibc_clone, .-__rustlibc_clone",
);

// Unmaps the calling thread's own stack and exits (no stack to return to
// after `munmap`, so both syscalls are issued from assembly).
#[cfg(not(test))]
global_asm!(
    ".globl __rustlibc_unmapself",
    ".type __rustlibc_unmapself,%function",
    "__rustlibc_unmapself:",
    "mov x8, #215",
    "svc #0",
    "mov x0, #0",
    "mov x8, #93",
    "svc #0",
    "brk #0",
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
/// `stack` must be the top of a mapped stack; `tls` the thread pointer
/// value for the new thread.
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

// Signal return trampoline (`sa_restorer`). The kernel requires the two
// instructions to be exactly these (it recognises the sequence).
#[cfg(not(test))]
global_asm!(
    ".globl __rustlibc_restore_rt",
    ".type __rustlibc_restore_rt,%function",
    "nop",
    "__rustlibc_restore_rt:",
    "mov x8, #139",
    "svc #0",
    ".size __rustlibc_restore_rt, .-__rustlibc_restore_rt",
);

// setjmp / longjmp.
//
// jmp_buf layout (same slot count as x86_64 so the header is shared):
// x19-x28, x29, x30, sp (13 words), d8-d15 (8 words) — 21 words, then a
// spare word at index 21 used by sigsetjmp, and the saved signal mask.
// The C header reserves 8 + 1 + 16 words on x86_64; here the buffer holds
// 21 + 1 + 16 words, see `include/setjmp.h`.
#[cfg(not(test))]
global_asm!(
    ".globl setjmp, _setjmp, longjmp, _longjmp, siglongjmp, sigsetjmp, __sigsetjmp",
    ".type setjmp,%function",
    ".type longjmp,%function",
    ".type sigsetjmp,%function",
    "_setjmp:",
    "setjmp:",
    "stp x19, x20, [x0, #0]",
    "stp x21, x22, [x0, #16]",
    "stp x23, x24, [x0, #32]",
    "stp x25, x26, [x0, #48]",
    "stp x27, x28, [x0, #64]",
    "stp x29, x30, [x0, #80]",
    "mov x2, sp",
    "str x2, [x0, #96]",
    "stp d8, d9, [x0, #104]",
    "stp d10, d11, [x0, #120]",
    "stp d12, d13, [x0, #136]",
    "stp d14, d15, [x0, #152]",
    "mov x0, #0",
    "ret",
    "_longjmp:",
    "longjmp:",
    "siglongjmp:",
    "ldp x19, x20, [x0, #0]",
    "ldp x21, x22, [x0, #16]",
    "ldp x23, x24, [x0, #32]",
    "ldp x25, x26, [x0, #48]",
    "ldp x27, x28, [x0, #64]",
    "ldp x29, x30, [x0, #80]",
    "ldr x2, [x0, #96]",
    "mov sp, x2",
    "ldp d8, d9, [x0, #104]",
    "ldp d10, d11, [x0, #120]",
    "ldp d12, d13, [x0, #136]",
    "ldp d14, d15, [x0, #152]",
    "cmp w1, #0",
    "csinc w0, w1, wzr, ne",
    "ret",
    "__sigsetjmp:",
    "sigsetjmp:",
    "cbz w1, setjmp",
    // Stash our return address and x19 in the spare slots, then call
    // setjmp and continue in the Rust tail (musl's design).
    "str x30, [x0, #168]",
    "str x19, [x0, #176]",
    "mov x19, x0",
    "bl setjmp",
    "mov w1, w0",
    "mov x0, x19",
    "ldr x30, [x19, #168]",
    "ldr x19, [x19, #176]",
    "b {tail}",
    ".size setjmp, .-setjmp",
    tail = sym crate::signal::__sigsetjmp_tail,
);

/// Performs a raw system call with no arguments.
///
/// # Safety
/// The caller is responsible for the semantics of the system call.
#[inline(always)]
pub unsafe fn syscall0(n: usize) -> usize {
    let ret: usize;
    // SAFETY: caller contract.
    unsafe {
        asm!("svc #0", in("x8") n, lateout("x0") ret, options(nostack));
    }
    ret
}

/// Raw system call with one argument. See [`syscall0`].
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall1(n: usize, a1: usize) -> usize {
    let ret: usize;
    // SAFETY: caller contract.
    unsafe {
        asm!("svc #0", in("x8") n, inlateout("x0") a1 => ret, options(nostack));
    }
    ret
}

/// Raw system call with two arguments. See [`syscall0`].
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall2(n: usize, a1: usize, a2: usize) -> usize {
    let ret: usize;
    // SAFETY: caller contract.
    unsafe {
        asm!("svc #0", in("x8") n, inlateout("x0") a1 => ret, in("x1") a2, options(nostack));
    }
    ret
}

/// Raw system call with three arguments. See [`syscall0`].
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall3(n: usize, a1: usize, a2: usize, a3: usize) -> usize {
    let ret: usize;
    // SAFETY: caller contract.
    unsafe {
        asm!("svc #0", in("x8") n, inlateout("x0") a1 => ret, in("x1") a2, in("x2") a3,
             options(nostack));
    }
    ret
}

/// Raw system call with four arguments. See [`syscall0`].
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall4(n: usize, a1: usize, a2: usize, a3: usize, a4: usize) -> usize {
    let ret: usize;
    // SAFETY: caller contract.
    unsafe {
        asm!("svc #0", in("x8") n, inlateout("x0") a1 => ret, in("x1") a2, in("x2") a3,
             in("x3") a4, options(nostack));
    }
    ret
}

/// Raw system call with five arguments. See [`syscall0`].
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall5(n: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize) -> usize {
    let ret: usize;
    // SAFETY: caller contract.
    unsafe {
        asm!("svc #0", in("x8") n, inlateout("x0") a1 => ret, in("x1") a2, in("x2") a3,
             in("x3") a4, in("x4") a5, options(nostack));
    }
    ret
}

/// Raw system call with six arguments. See [`syscall0`].
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
    // SAFETY: caller contract.
    unsafe {
        asm!("svc #0", in("x8") n, inlateout("x0") a1 => ret, in("x1") a2, in("x2") a3,
             in("x3") a4, in("x4") a5, in("x5") a6, options(nostack));
    }
    ret
}

/// Raw system call with up to six arguments from a slice.
///
/// # Safety
/// See [`syscall0`].
#[inline(always)]
pub unsafe fn syscall_n(n: usize, args: &[usize]) -> usize {
    let a = |i: usize| args.get(i).copied().unwrap_or(0);
    // SAFETY: caller contract.
    unsafe {
        match args.len() {
            0 => syscall0(n),
            1 => syscall1(n, a(0)),
            2 => syscall2(n, a(0), a(1)),
            3 => syscall3(n, a(0), a(1), a(2)),
            4 => syscall4(n, a(0), a(1), a(2), a(3)),
            5 => syscall5(n, a(0), a(1), a(2), a(3), a(4)),
            _ => syscall6(n, a(0), a(1), a(2), a(3), a(4), a(5)),
        }
    }
}

/// Reads the thread pointer (`TPIDR_EL0`).
///
/// # Safety
/// The thread pointer must have been set.
#[inline(always)]
pub unsafe fn thread_pointer() -> *mut u8 {
    let tp: *mut u8;
    // SAFETY: reading a system register has no side effects.
    unsafe {
        asm!("mrs {}, tpidr_el0", out(reg) tp, options(nostack, nomem, preserves_flags));
    }
    tp
}

/// Sets the thread pointer of the calling thread.
///
/// # Safety
/// `tp` must point at a prepared TLS area.
pub unsafe fn set_thread_pointer(tp: *mut u8) -> crate::sys::Result<()> {
    // SAFETY: caller contract.
    unsafe {
        asm!("msr tpidr_el0, {}", in(reg) tp, options(nostack, nomem, preserves_flags));
    }
    Ok(())
}

/// Stops the program with an undefined instruction.
#[inline(always)]
pub fn trap() -> ! {
    // SAFETY: `brk` never returns.
    unsafe { asm!("brk #1", options(noreturn, nostack)) }
}
