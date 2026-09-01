# Design notes

## Goals, in priority order

1. **Correctness and security.** A libc bug is a bug in every program.
2. **Reviewability.** Small modules, obvious control flow, `SAFETY`
   comments on every `unsafe` block, assembly only where unavoidable.
3. **Performance.** SIMD where it pays (string search/compare, copies),
   lock-free fast paths for the allocator and stdio in single-threaded
   programs, no syscalls that can be avoided.
4. **Compatibility** with C11/POSIX programs compiled against our headers.

## Freestanding Rust on a hosted target

The crate is `#![no_std]` and built for `x86_64-unknown-linux-gnu`. The
prebuilt `core` for that target expects a libc to provide `memcpy`,
`memset`, `memmove`, `memcmp`, `bcmp` and `strlen` — which is exactly what
we do. Two consequences:

* `#![no_builtins]` is set on the crate, so LLVM can never "recognise" a
  loop inside our `memcpy` as a memcpy and emit a recursive call.
* `core` is compiled with unwinding and references `rust_eh_personality`.
  We build with `panic = "abort"` and provide a never-called stub.

Rust's C-variadic support is unstable, so `printf`-style entry points are
assembly stubs that spill the argument registers into a SysV `va_list` and
call the `v*` variant, which walks the `va_list` by hand.

## Testing strategy

* `cargo test -p rustlibc` builds the crate *with* `std` under `cfg(test)`.
  In that configuration nothing is exported (`no_mangle` is gated on
  `not(test)`), so the unit tests exercise our `memcpy`, `printf`
  formatting, allocator, etc. without shadowing the host libc.
* `cargo xtask test` links each `tests/c/*.c` against the real `libc.a`
  and runs it. These are the integration tests: startup, TLS, threads,
  signals, stdio and everything else that only makes sense end-to-end.
* `tests/c/abi_layout.c` checks that the C headers and the Rust
  `#[repr(C)]` types agree on sizes and offsets.

## Startup

`_start` (assembly) passes the initial stack pointer to
`start::start_c`, which:

1. splits it into `argc`/`argv`/`envp`/auxv and sets `environ`;
2. finds `PT_TLS` via `AT_PHDR`, maps a region for the main thread's static
   TLS block and TCB, copies the TLS image and installs the thread pointer
   with `arch_prctl(ARCH_SET_FS)`;
3. seeds the stack protector canary from `AT_RANDOM`;
4. detects the SIMD level with `cpuid`;
5. runs `.preinit_array` and `.init_array`, calls `main`, and `exit`s.

## Thread control block

The TCB (`thread::Tcb`) is what the thread pointer addresses. Its first
words follow the x86_64 conventions compilers hard-code: the self pointer
at offset 0 and the stack protector canary at offset 0x28. Our own
per-thread state (`errno`, tid, allocator cache, …) follows. The static
TLS block sits directly below the TCB (TLS variant II), see
`thread/tls.rs` for the exact layout and why it matches what the linker
assumes.

## Error handling

Internally everything returns `sys::Result<T>` (`Result<T, Errno>`).
Only the exported C entry points touch `errno`, through `Errno::set` or
the `CReturn` helper, immediately before returning `-1`.
