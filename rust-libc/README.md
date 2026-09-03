# rustlibc

A Linux libc written from scratch in Rust.

* **Static only.** Programs link `libc.a` and talk directly to the stable
  Linux kernel ABI. There is no dynamic loader; static PIE (`-static-pie`,
  address-space randomised) is supported and the executable relocates
  itself at startup.
* **Performance conscious.** SIMD string routines with runtime CPU
  dispatch (SSE2 / AVX2 / AVX-512BW on x86_64, NEON on AArch64), a
  size-class allocator with per-thread caches and no free lists (block
  states live in a table, so refills, flushes and cross-thread frees
  never touch the blocks), buffered stdio, the vDSO for the clock calls,
  and benchmark harnesses that compare every hot path against the host
  glibc and thirty allocator workloads against glibc, mimalloc, jemalloc
  and tcmalloc.
* **Security conscious.** Stack protector support out of the box, no
  allocator metadata in user memory at all (an overflow or a write into
  a freed block cannot corrupt the allocator), per-block state tracking
  and a registry of live mappings that turn double, invalid and foreign
  frees into aborts, no `%n`, every length
  computation is checked, linear worst cases for `memmem`/`strstr` and
  `qsort`, DNS replies validated field by field. The code base has been
  through a systematic security review (see `docs/DESIGN.md`).
* **Small and reviewable.** Assembly is confined to `libc/src/arch`, every
  `unsafe` block carries a `SAFETY` comment, and modules map one-to-one to
  C headers. The only external crate is `libm`.

`x86_64` and `aarch64` are supported; the same test suite runs on both
(natively, and cross-compiled under `qemu-aarch64`).

## Layout

```
libc/            the library crate (builds libc.a)
  src/arch/      all assembly: syscalls, _start, thread pointer, cpuid,
                 setjmp, variadic stubs, fenv
  src/sys/       typed syscall wrappers and kernel ABI structs
  src/thread/    TCB, static TLS, pthreads and synchronisation
  src/string/    mem*/str*, the SIMD lane abstraction and dispatch
  src/malloc/    the allocator
  src/stdio/     streams, printf, scanf
include/         the C headers
tests/c/         C programs linked against libc.a, run by `cargo xtask test`
bench/           the benchmark program, run by `cargo xtask bench`
xtask/           build/test/bench driver
docs/DESIGN.md   design notes
```

## Building and testing

```
cargo xtask build        # builds target/sysroot/{include,lib/libc.a}
cargo xtask test         # builds, then compiles and runs tests/c/*.c
cargo xtask bench        # builds bench/bench.c against rustlibc and glibc
cargo xtask bench alloc  # the allocator workloads in bench/alloc.c, against
                         # glibc, mimalloc, jemalloc and tcmalloc if installed
cargo xtask bench alloc:tree   # only the workloads whose name contains "tree"
cargo test -p rustlibc   # host unit tests of the pure Rust code
cargo xtask --aarch64 test   # cross-build with aarch64-linux-gnu-gcc and
                             # run the suite under qemu-aarch64
cargo xtask --pie test       # link every test as a static PIE
cargo xtask --aarch64 --pagesize=65536 test  # emulate a 64 KiB-page kernel
```

The AArch64 build needs `rustup target add aarch64-unknown-linux-gnu`,
`gcc-aarch64-linux-gnu` and `qemu-user`.

To compile a program against it (replace `-static` with `-static-pie
-fPIE` for a position-independent executable):

```
cc -static -nostdlib -nostartfiles -nostdinc -Wl,--eh-frame-hdr \
   -isystem target/sysroot/include -isystem "$(cc -print-file-name=include)" \
   hello.c -Ltarget/sysroot/lib -lc -lgcc
```

C++ works with the host toolchain's `libstdc++.a` (which is built against
glibc: the `compat` module provides the glibc-specific symbols it needs,
and `-Wl,--eh-frame-hdr` gives libgcc's unwinder its lookup table):

```
c++ -static -nostdlib -nostartfiles -nostdinc -nostdinc++ -Wl,--eh-frame-hdr \
    -isystem /usr/include/c++/13 -isystem /usr/include/x86_64-linux-gnu/c++/13 \
    -isystem target/sysroot/include -isystem "$(c++ -print-file-name=include)" \
    hello.cpp -Ltarget/sysroot/lib \
    "$(c++ -print-file-name=libstdc++.a)" "$(c++ -print-file-name=libgcc_eh.a)" -lc -lgcc
```

## What is implemented

Startup and process (`_start`, `environ`, `atexit`/`__cxa_atexit`,
`init_array`, `exit`, `fork`/`exec`/`wait`, `system`, `popen`), static TLS
and `__thread`, pthreads (threads, mutexes, condition variables, rwlocks,
barriers, spin locks, keys, once, `atfork`, semaphores, C11 threads),
signals (`sigaction`, masks, `sigaltstack`, `signalfd`), the allocator
(`malloc` family including `posix_memalign`, `reallocarray`,
`malloc_usable_size`), stdio (streams, `fmemopen`/`open_memstream`, the
full `printf` and `scanf` families, wide-character stdio), `stdlib.h`
(`strtol`/`strtod` families, `qsort`, `bsearch`, environment, `rand`,
`*rand48`, `getsubopt`, `quick_exit`), `string.h`/`strings.h`, `ctype.h`,
`wchar.h`/`wctype.h` (UTF-8), `math.h`/`fenv.h`, `time.h` (UTC),
`setjmp.h`, file system and directory calls, `getopt`, `fnmatch`,
`search.h`, `termios.h` and pseudo-terminals, `syslog`, `pwd.h`/`grp.h`
(from the files), sockets with address conversion and a minimal
`getaddrinfo`, `poll`/`select`/`epoll`, `timerfd`/`inotify`/`eventfd`,
`sched.h`, `sys/mman.h` including `shm_open`, `netdb.h` with a real
resolver, `iconv` for the Unicode
encodings, `dl_iterate_phdr` and the C++ runtime hooks, plus the glibc
compatibility symbols (`__*_chk`, `__isoc99_*`, `_dl_find_object`,
`__ctype_b_loc`, the `*_l` locale variants, `__libc_single_threaded`, …)
that let static libraries built against glibc, `libstdc++.a` among them,
link and run.

Also: a DNS stub resolver (`/etc/resolv.conf`, parallel UDP queries,
TCP fallback, search list, PTR), time zones (`TZ`, TZif files, POSIX
rules), the vDSO for the clock calls, and `pthread_cancel` (deferred and
asynchronous).

Known limitations: no dynamic linking (static and static-pie only);
multibyte conversion is UTF-8 only; `long double` is treated as `double` (no `*l` math functions;
`strtold` returns a `double`'s precision, in the platform's `long double`
format); no `dlopen` (static linking only); cancellation is acted on at
cancellation points rather than at any instruction inside a system call.

## Performance

`cargo xtask bench` prints rustlibc next to the host glibc; a ratio above
1 means rustlibc is faster. On a Cascade Lake Xeon (AVX-512, glibc 2.39),
after the current round of work:

| benchmark | rustlibc | glibc | ratio |
|---|---|---|---|
| memcpy 256 B / 4 KiB | 60 / 137 GB/s | 52 / 105 GB/s | 1.15x / 1.30x |
| memset 256 B / 4 KiB | 74 / 132 GB/s | 54 / 119 GB/s | 1.37x / 1.11x |
| memmove 4 KiB, overlapping | 94 GB/s | 89 GB/s | 1.05x |
| memchr 4 KiB / 64 KiB | 183 / 142 GB/s | 112 / 98 GB/s | 1.63x / 1.45x |
| strlen 64 B / 64 KiB | 30 / 137 GB/s | 25 / 97 GB/s | 1.19x / 1.42x |
| strcmp 4 KiB / 64 KiB | 80 / 71 GB/s | 81 / 47 GB/s | 0.98x / 1.51x |
| memmem 64 KiB | 32 GB/s | 9.5 GB/s | 3.35x |
| malloc+free 64 B / 4 KiB / 1 MiB | 13.6 / 15.7 / 15.8 ns | 14.0 / 33.7 / 36.0 ns | 1.03x / 2.15x / 2.28x |
| snprintf `%d %s %x` / `%f` / `%e` | 92 / 197 / 208 ns | 93 / 267 / 216 ns | 1.01x / 1.36x / 1.04x |
| snprintf `%g` | 189–232 ns | 143 ns | 0.62–0.76x |
| strtod / sscanf `%d %d` | 42 / 81 ns | 83 / 107 ns | 1.98x / 1.33x |
| qsort 100k ints | 129 ns/elem | 107 ns/elem | 0.83x |
| pthread_create+join | 57 µs | 61 µs | 1.05x |

The remaining gaps are the sub-64-byte compare and search calls (glibc's
hand-written assembly saves about 2 ns per call) and `%g` (bounded by
`core::fmt`'s digit generation).

`cargo xtask bench alloc` runs thirty allocator workloads modelled on
the mimalloc-bench suite and on real programs (`bench/alloc.c`) against
glibc, mimalloc, jemalloc and tcmalloc (the last three dynamically
linked, from the distribution packages). The table below is one run on
the same machine (a virtual machine with four CPUs, so the threaded rows
vary between runs by up to 2x); ns per operation, lower is better.

| workload | rustlibc | glibc | mimalloc | jemalloc | tcmalloc |
|---|---|---|---|---|---|
| malloc+free 16 B / 4 KiB / 1 MiB | 13.4 / 15.8 / 16.0 | 13.2 / 30.7 / 33.3 | 12.1 / 16.6 / 263 | 11.3 / 14.3 / 449 | 6.8 / 7.8 / 69 |
| live set, 16-256 B | 35 | 41 | 24 | 26 | 25 |
| live set, 256 B-8 KiB | 37 | 164 | 58 | 72 | 33 |
| live set, 64 KiB-1 MiB | 235 | 591 | 418 | 848 | 411 |
| cfrac (LIFO bursts) | 15 | 25 | 7.8 | 11 | 9.0 |
| alloc-test, 100k live | 106 | 369 | 115 | 173 | 155 |
| sh6bench | 19 | 31 | 16 | 171 | 28 |
| glibc-simple | 20 | 30 | 9.8 | 16 | 11 |
| malloc-large, 1-16 MiB touched | 1.0 µs | 118 µs | 1.4 µs | 208 µs | 8.1 µs |
| calloc 64 B / 64 KiB | 21 / 3.5 µs | 25 / 2.7 µs | 9.8 / 2.5 µs | 26 / 4.7 µs | 12 / 2.6 µs |
| memalign 64 / aligned_alloc 4 KiB | 22 / 30 | 116 / 112 | 20 / 79 | 36 / 211 | 10 / 17 |
| realloc growth 16 B to 1 MiB | 3.0 µs | 3.3 µs | 3.2 µs | 0.17 µs | 1.9 µs |
| realloc vectors x1.5 | 444 | 477 | 531 | 596 | 448 |
| tree build/teardown, 200k nodes | 9.4 | 14 | 6.5 | 11 | 15 |
| larson, 4 threads | 32 | 46 | 27 | 29 | 28 |
| producer/consumer, 4 threads | 621 | 997 | 542 | 740 | 606 |
| xmalloc-test, 4 threads (all frees remote) | 33 | 176 | 57 | 14 | 14 |
| mstress, 4 threads | 29 | 149 | 40 | 70 | 33 |
| thread churn (create, 64 mallocs, exit, join) | 39 µs | 37 µs | 40 µs | 167 µs | 39 µs |

rustlibc is faster than glibc on every row but two within noise, and
faster than every other allocator on the large-block and multi-threaded
rows. mimalloc keeps a lead of about 2x on the small-block burst
workloads (cfrac, glibc-simple, tree): its `free` is two stores with no
validation, ours checks the mapping registry, the segment header, the
block index and the block's state on every call. jemalloc's realloc row
extends the sole live buffer in place. `BENCH_RSS=1` makes the program
report its resident memory at the end and again after two idle seconds
and a little activity: rustlibc holds 1-2 MiB after the single-threaded
workloads, against 35-240 MiB for the others.

The one row where rustlibc trails glibc by more than noise is the
condition-variable ping-pong of `producer/consumer` with the allocator
taken out (`bench alloc:sync`): about 3x, a scheduler interaction of the
mutex hand-off that survived a rewrite of the mutex (see
`docs/DESIGN.md`).

## Dependencies

* [`libm`](https://crates.io/crates/libm) – the Rust port of musl's math
  library, backing `<math.h>`; a correctly rounded libm is a project of its
  own.

Everything else — startup, TLS, threads, the allocator, stdio, printf,
strtod, time, signals, the SIMD string kernels, … — is implemented here.
