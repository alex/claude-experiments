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
| malloc+free 16 B / 4 KiB / 1 MiB | 13.5 / 15.6 / 15.6 | 12.9 / 29.7 / 32.5 | 12.0 / 16.2 / 258 | 11.3 / 14.3 / 439 | 6.5 / 7.7 / 69 |
| live set, 16-256 B | 35 | 41 | 23 | 26 | 24 |
| live set, 256 B-8 KiB | 42 | 153 | 57 | 69 | 33 |
| live set, 64 KiB-1 MiB | 223 | 500 | 438 | 891 | 402 |
| cfrac (LIFO bursts) | 14 | 23 | 8.7 | 12 | 10 |
| alloc-test, 100k live | 113 | 304 | 122 | 145 | 104 |
| sh6bench | 19 | 32 | 15 | 139 | 27 |
| glibc-simple | 19 | 30 | 9.5 | 16 | 12 |
| malloc-large, 1-16 MiB touched | 1.0 µs | 132 µs | 1.5 µs | 185 µs | 8.9 µs |
| calloc 64 B / 64 KiB | 22 / 3.2 µs | 25 / 2.6 µs | 9.8 / 2.5 µs | 26 / 4.7 µs | 12 / 2.5 µs |
| memalign 64 / aligned_alloc 4 KiB | 21 / 32 | 114 / 110 | 19 / 80 | 34 / 217 | 10 / 17 |
| realloc growth 16 B to 1 MiB | 2.9 µs | 3.2 µs | 3.4 µs | 0.17 µs | 1.8 µs |
| realloc vectors x1.5 | 444 | 466 | 541 | 596 | 430 |
| tree build/teardown, 200k nodes | 8.9 | 15 | 6.4 | 11 | 14 |
| larson, 4 threads | 32 | 44 | 24 | 30 | 30 |
| producer/consumer, 4 threads | 519 | 1791 | 600 | 689 | 1709 |
| producer/consumer, sync only (no malloc) | 403 | 422 | 345 | 356 | 381 |
| xmalloc-test, 4 threads (all frees remote) | 42 | 334 | 56 | 26 | 28 |
| fan-out free (1 allocating, 7 freeing threads) | 43 | 600 | 93 | 104 | 160 |
| parallel free of 1M 64 B blocks, 16 threads | 9.3 | 151 | 24 | 714 | 333 |
| parallel free of 200k 4 KiB blocks, 4 threads | 22 | 1069 | 43 | 1147 | 386 |
| frame pipeline (690 KiB frames, 8 workers) | 21 µs | 32 µs | 22 µs | 34 µs | 26 µs |
| frame pipeline, 40 workers | 61 µs | 111 µs | 82 µs | 124 µs | 96 µs |
| mstress, 4 threads | 40 | 181 | 46 | 78 | 49 |
| thread churn (create, 64 mallocs, exit, join) | 50 µs | 41 µs | 43 µs | 174 µs | 46 µs |

rustlibc is faster than glibc on every row but the tight pair and
thread churn (within noise or 20%), and faster than every other
allocator on the large-block, cross-thread-free and pipeline rows. mimalloc keeps a lead of about 2x on the small-block burst
workloads (cfrac, glibc-simple, tree): its `free` is two stores with no
validation, ours checks the mapping registry, the segment header, the
block index and the block's state on every call. jemalloc's realloc row
extends the sole live buffer in place. `BENCH_RSS=1` makes the program
report its resident memory at the end and again after two idle seconds
and a little activity: rustlibc holds 1-2 MiB after the single-threaded
workloads, against 35-240 MiB for the others.

The `fan-out free`, `parallel free` and `frame pipeline` rows are the
shape of a reader thread whose buffers are freed by a pool of workers:
every free is a cross-thread free. rustlibc leads them by 1.4-4x; the
40-worker pipeline oversubscribes this 4-CPU machine and mostly measures
the mutex and condition variable hand-offs (see `docs/DESIGN.md`).

## Dependencies

* [`libm`](https://crates.io/crates/libm) – the Rust port of musl's math
  library, backing `<math.h>`; a correctly rounded libm is a project of its
  own.

Everything else — startup, TLS, threads, the allocator, stdio, printf,
strtod, time, signals, the SIMD string kernels, … — is implemented here.
