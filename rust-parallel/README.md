# filament

A high-performance data-parallelism library for Rust with rayon-style
ergonomics: parallel iterators over standard library types, a
work-stealing `join` primitive, and extension traits so any type can
provide its own parallel iterator implementations.

```rust
use filament::prelude::*;

let sum: u64 = (0..1_000_000u64).into_par_iter().map(|i| i * i).sum();
```

## Design

- **Lean work-stealing core**: LIFO Chase-Lev deques per worker,
  allocation-free `join` (the stolen half lives on the caller's stack),
  targeted per-worker park/unpark wakeups instead of broadcast condvars.
- **Producer/Consumer plumbing**: parallel iterator adapters compile down
  to plain sequential loops at the leaves of the splitting tree, so LLVM
  can autovectorize them; splitting is adaptive (splits deepen only when
  jobs are actually stolen).

## Benchmarks

See `benches/compare.rs` for a head-to-head comparison harness against
rayon across a range of workloads.
