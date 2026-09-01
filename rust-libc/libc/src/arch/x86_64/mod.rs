//! x86_64 specific code.

use core::arch::{asm, global_asm};

pub mod cpu;
pub mod nr;

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
