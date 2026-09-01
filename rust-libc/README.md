# rustlibc

A Linux libc written from scratch in Rust.

* **Static only.** Programs link `libc.a` and talk directly to the stable
  Linux kernel ABI. There is no dynamic loader.
* **Performance conscious.** SIMD string routines with runtime CPU
  dispatch, a size-class allocator with per-thread caches, buffered stdio.
* **Security conscious.** Stack protector support out of the box, no
  in-band allocator metadata next to user data, no `%n`, every length
  computation is checked.
* **Small and reviewable.** Assembly is confined to `libc/src/arch`, every
  `unsafe` block carries a `SAFETY` comment, and modules map one-to-one to
  C headers.

Currently only `x86_64` is supported.

## Layout

```
libc/            the library crate (builds libc.a)
  src/arch/      all assembly: syscalls, _start, thread pointer, cpuid
  src/sys/       typed syscall wrappers and kernel ABI structs
  src/thread/    TCB, static TLS, pthreads
  src/string/    mem*/str*
include/         the C headers
tests/c/         C programs linked against libc.a, run by `cargo xtask test`
xtask/           build/test driver
docs/DESIGN.md   design notes
```

## Building and testing

```
cargo xtask build        # builds target/sysroot/{include,lib/libc.a}
cargo xtask test         # builds, then compiles and runs tests/c/*.c
cargo test -p rustlibc   # host unit tests of the pure Rust code
```

To compile a program against it:

```
cc -static -nostdlib -nostartfiles -nostdinc \
   -isystem target/sysroot/include -isystem "$(cc -print-file-name=include)" \
   hello.c -Ltarget/sysroot/lib -lc -lgcc
```

## Dependencies

* [`fearless_simd`](https://crates.io/crates/fearless_simd) – safe,
  multi-versioned SIMD kernels for the string routines.
* [`libm`](https://crates.io/crates/libm) (pulled in by `fearless_simd`
  under `no_std`) – the Rust port of musl's math library. It also backs
  `<math.h>`; a correctly rounded libm is a project of its own.

Everything else — startup, TLS, threads, the allocator, stdio, printf,
strtod, time, signals, … — is implemented here.
