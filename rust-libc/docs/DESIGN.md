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

The crate is `#![no_std]` and built for `x86_64-unknown-linux-gnu` or
`aarch64-unknown-linux-gnu`. The
prebuilt `core` for those targets expects a libc to provide `memcpy`,
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

0. relocates the executable if it is a static PIE (`reloc.rs`): the
   load bias is the runtime address of the ELF header (`__ehdr_start`,
   PC-relative) minus the link-time address of the segment holding it;
   the `PT_DYNAMIC` entry then leads to the `DT_RELA`/`DT_RELR` tables
   whose `R_*_RELATIVE` entries get the bias added. Until that is done
   nothing may touch a pointer stored in data (statics, the GOT that
   x86_64 Rust calls go through), so this step is inlined and uses only
   its stack. Afterwards the RELRO segment is made read-only, for
   fixed-address executables too;
1. splits it into `argc`/`argv`/`envp`/auxv and sets `environ`;
2. finds `PT_TLS` via `AT_PHDR`, maps a region for the main thread's static
   TLS block and TCB, copies the TLS image and installs the thread pointer
   (`arch_prctl(ARCH_SET_FS)` on x86_64, `TPIDR_EL0` on AArch64);
3. seeds the stack protector canary from `AT_RANDOM` (into the TCB on
   x86_64, into the exported `__stack_chk_guard` on AArch64, where gcc
   reads it from);
4. locates the vDSO from `AT_SYSINFO_EHDR` and detects the SIMD level
   (SSE2, AVX2 or AVX-512BW with `cpuid`; NEON is the AArch64 baseline);
5. runs `.preinit_array` and `.init_array`, calls `main`, and `exit`s.

## Thread control block

The TCB (`thread::Tcb`) holds the per-thread state (`errno`, tid,
allocator cache, keys, …). On x86_64 the thread pointer addresses it and
its first words follow the conventions compilers hard-code: the self
pointer at offset 0 and the stack protector canary at offset 0x28; the
static TLS block sits directly below (TLS variant II). On AArch64 the
thread pointer addresses a 16-byte header with the TLS block after it
(variant I), and the TCB sits right below the thread pointer. See
`thread/tls.rs` for both layouts and why they match what the linker
assumes; `tls::thread_pointer_of`/`tcb_of` hide the difference.

## Architectures

Everything architecture specific is under `arch/<name>/` and reached
through one interface (`arch/mod.rs` lists it): raw syscalls, `_start`,
thread creation and exit, the signal trampoline, `setjmp`, the thread
pointer, `va_list` access, the variadic and `long double` stubs, fenv,
the syscall table and a few constants (the jmp_buf mask slot, vDSO
symbol names). Generic code never spells a syscall number and only uses
calls that exist everywhere (`openat`, `ppoll`, `clone`, `dup3`,
`renameat2`, …). Kernel structures whose layout differs (`struct stat`,
`epoll_event`, the `O_*` flags, `wchar_t`) are conditional in both the
Rust code and the headers, and `tests/c/abi.c` checks the header side.

The page size is not a constant: AArch64 kernels are built with 4, 16 or
64 KiB pages. `sys::page_size()` holds the value of `AT_PAGESZ` and is
what every page-granular kernel interface uses (guard pages, `mprotect`,
`madvise`, RELRO, `sysconf`); `MIN_PAGE_SIZE` (4 KiB) remains where only
a lower bound matters, such as the string kernels' rule that an aligned
vector load never crosses a page. `cargo xtask --aarch64
--pagesize=65536 test` runs the suite with qemu emulating such a kernel.

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
one, four or eight units hold blocks of one of 60 size classes (16-byte
steps to 128 bytes, then four classes per power of two up to 1 MiB, the
same territory glibc's dynamic mmap threshold covers). Metadata lives in
the segment header, never next to user data. Each thread owns a heap
with per-class lists of spans; blocks freed by another thread go on the
span's lock-free remote stack and are collected by the owner.

Security measures on the fast path: free-list links (local and remote)
are XOR-encoded with a per-process key and the slot address and validated
when popped; an allocation bitmap per span makes double and interior
frees abort; a bitmap of live 16 MiB-aligned mappings (2 MiB of `.bss`,
touched lazily) is consulted before any header is read, so a pointer
that never came from the allocator, or one into the middle of a block
larger than a segment, is rejected instead of having user data
interpreted as metadata.

Larger requests are direct mappings with a header page, resized with
`mremap` (in place when the address space allows, otherwise into a fresh
aligned reservation with `MREMAP_FIXED`) rather than copied; freed
mappings are cached (eight, at most 64 MiB each, 32 MiB of them kept
resident) so that programs which repeatedly allocate large buffers do
not pay for `mmap`, page faults and `munmap` every time. `calloc` zeroes
recycled mappings explicitly.

Memory goes back to the kernel deliberately, because `MADV_DONTNEED`
costs a TLB shootdown and the next use faults the pages in again: a
heap keeps one empty single-unit span per class (the only span of a
class is always kept, so a block freed and reallocated in a loop never
faults); larger spans are returned as soon as they are empty; a thread
that exits hands its empty spans to the orphan lists for the next
thread, one per class; and single-unit spans returned to a segment keep
their pages until three quarters of the segment is free, when they are
returned in bulk. An entirely free segment is unmapped unless it is the
last one.

## Security review

Four independent reviews of the code base (string and stdio, allocator
and threads, files and processes, network and time) were run after the
functionality was complete; every confirmed finding was fixed and has a
regression test in `tests/c/audit.c`. The classes of problem found are
worth knowing when reviewing new code:

* over-reads by SIMD kernels when a bounded compare was given the
  wrong bound (`getenv` compared entries with the *name's* length);
* assembly stubs whose register or slot conventions drifted from the
  Rust side (`sigsetjmp` stashed a register in the word the signal mask
  overwrote; the fortified `printf` stubs miscounted their fixed
  arguments), now covered by tests that would have caught them;
* lock-order and lock-lifetime mistakes around `fork`, thread exit and
  `exit` (the stream list walk without its lock);
* trusting memory as metadata because of its address (the allocator
  header registry above);
* the long tail of C library corner cases: exact-fit `strftime`,
  `printf` with a literal `$`, `getopt` permutation with option
  arguments, hostnames from DNS replies used verbatim, `pthread_key`
  reuse, timed rwlock writers giving up.

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

## glibc compatibility

Static libraries shipped by distributions are compiled against glibc's
headers and reference glibc-only symbols. `compat.rs` provides the ones
that matter in practice, so that `libstdc++.a` and similar libraries
link and work: the `_FORTIFY_SOURCE` `__*_chk` functions (which really
check and abort), the `__isoc99_`/`__isoc23_` aliases, the `*_l` locale
variants (there is only the C locale), `__ctype_b_loc` and friends with
glibc's bit layout, a `locale_t` object with glibc's `struct
__locale_struct` layout (libstdc++ reads the ctype tables out of it),
`__libc_single_threaded`, `_dl_find_object` for libgcc's unwinder, the
`*64` file names, `gettext` and `arc4random`. `tests/c/cxx.cpp` exercises
exceptions, iostreams and `std::thread` through this path.

## Resolver

`resolv.rs` is a stub resolver in the musl style: every lookup re-reads
`/etc/resolv.conf`, sends the A and AAAA queries to all nameservers at
once over UDP with random IDs, takes the first valid reply per type,
retries after the timeout and re-asks over TCP when a reply is
truncated. A reply counts only if it comes from a configured server,
carries an outstanding ID and echoes the question; records count only
along the CNAME chain from the queried name; name decompression bounds
its pointer chase. `getaddrinfo` consults `/etc/hosts` first, then the
resolver with the search list and `ndots` rule; `getnameinfo` and
`gethostbyaddr` do PTR lookups.

## Time zones

`time/tz.rs` resolves `TZ` (a zone name under `/usr/share/zoneinfo`, a
`:path`, `/etc/localtime` when unset, or a POSIX rule string) into a
transition table and a rule for later years, cached until `TZ` changes.
TZif parsing is bounds-checked and keeps the most recent 2048
transitions; zone names may not escape the zoneinfo directory.

## Cancellation

`pthread_cancel` sets a flag in the target's TCB and sends it an internal
signal (33, reserved from user masks and handlers) so that a blocking
system call returns. Deferred cancellation is acted on at cancellation
points (`thread::cancel_point`, called at the entry and exit of the
blocking calls POSIX lists); asynchronous cancellation acts in the
signal handler. Either way the thread exits through the normal
`pthread_exit` path with `PTHREAD_CANCELED`, running cleanup handlers.
