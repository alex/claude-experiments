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
* `tests/c/abi.c` checks that the C headers and the Rust
  `#[repr(C)]` types agree on sizes and offsets (the Rust side has
  matching compile-time assertions in `lib.rs`).
* `cargo xtask bench` compiles `bench/bench.c` twice, against rustlibc and
  the host glibc, and prints both results with their ratio.

## Startup

`_start` (assembly) passes the initial stack pointer to
`start::start_c`, which:

1. splits it into `argc`/`argv`/`envp`/auxv and sets `environ`;
2. finds `PT_TLS` via `AT_PHDR`, maps a region for the main thread's static
   TLS block and TCB, copies the TLS image and installs the thread pointer
   with `arch_prctl(ARCH_SET_FS)`;
3. seeds the stack protector canary from `AT_RANDOM`;
4. detects the SIMD level (SSE2, AVX2 or AVX-512BW) with `cpuid`;
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

## SIMD string kernels

`string/lanes.rs` is a deliberately tiny abstraction: a `Lanes` trait
(load, store, splat, equality to a mask, unsigned min, xor, and
"keep where equal") with SSE2, AVX2 and AVX-512BW backends, and a `Mask`
type that stays in whatever form the backend produces (a byte vector or a
`k` register) until one integer bitmask is needed. The kernels in
`string/search.rs` and `string/mem.rs` are written once, generic over
`Lanes`, and `dispatch_fn!` instantiates each in its own
`#[target_feature]` function taking the arguments in registers; the
exported C function is then a load of the cached CPU level and a tail
call, much like an ifunc.

Three lessons that shaped this:

* Closures do not inherit the enclosing function's target features, so a
  closure inside a kernel turns every intrinsic it uses into an
  out-of-line call. Kernels therefore use `#[inline(always)]` helper
  functions, never closures, and dispatch passes plain arguments rather
  than a closure environment.
* 64-byte vectors are a clear win for read-only scans (`memchr`,
  `strlen`, `memcmp`, …) but a 64-byte store cannot forward to the
  narrower loads that usually follow a copy, which halves the throughput
  of `memcpy` for data that is used immediately. Copies and fills stop at
  32-byte vectors (`dispatch_fn_ymm!`).
* Over-reads are confined to two provably safe forms: whole aligned
  vectors (which never cross a page) for NUL-terminated strings, and
  unaligned vectors that a page-offset check shows stay inside the current
  page. Bytes outside the input are masked off before they can influence
  a result.

`memmem`/`strstr` scan for windows whose first and last bytes match and
verify candidates with a budget proportional to the haystack; when a
pathological needle exhausts it, Two-Way takes over from that offset, so
the total stays linear.

## Allocator

Sixteen-mebibyte aligned segments are carved into 256 KiB units; spans of
one or four units hold blocks of one of 48 size classes (16-byte steps to
128 bytes, then four classes per power of two up to 128 KiB). Metadata
lives in the segment header, never next to user data. Each thread owns a
heap with per-class lists of spans; blocks freed by another thread go on
the span's lock-free remote stack and are collected by the owner.

Security measures on the fast path: free-list links are XOR-encoded with
a per-process key and the slot address and validated when popped; an
allocation bitmap per span makes double frees, interior frees and frees of
foreign pointers abort. Larger requests are direct mappings with a
header page; freed mappings are cached (eight, at most 64 MiB each) so
that programs which repeatedly allocate large buffers do not pay for
`mmap`, page faults and `munmap` every time. `calloc` zeroes recycled
mappings explicitly.

## printf floats

Digit generation is `core::fmt`'s. Its exact-precision mode is
correctly rounded but slow for values with short decimal expansions, so
`%e`, `%f` and `%g` first take the *shortest* round-trip digits and round
them by hand. That is exact whenever no rounding boundary lies within half
an ulp of the shortest value: with at most 15 significant digits a unit of
the last digit already exceeds that distance, so only an exact tie is
undecidable; with 16 or 17 digits a margin of 25 units is required. Any
other case, and any request for more than 15 digits, uses the exact mode.

## Other performance notes

* Mutexes skip the atomic read-modify-write while the process has one
  thread (the flag flips before `clone`); stdio locks do the same.
* `pthread_join` keeps the finished thread's stack mapping for the next
  `pthread_create`.
* `qsort` is an introsort with three-way partitioning, so equal keys and
  presorted input are cheap and the worst case is `O(n log n)`.
* `memcpy` above 256 bytes uses `rep movsb` (ERMS), which is faster than
  any vector loop on current CPUs and does not pollute the cache; nearby
  overlapping moves, where `rep movsb` is slow, use destination-aligned
  vector loops.
