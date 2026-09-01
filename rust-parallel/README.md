# filament

A high-performance data-parallelism library for Rust with rayon-style
ergonomics: parallel iterators over standard library types, a
work-stealing `join` primitive, `scope`/`spawn`, parallel sorts, and
extension traits so any type can provide its own parallel iterator
implementations.

```rust
use filament::prelude::*;

let sum: u64 = (0..1_000_000u64).into_par_iter().map(|i| i * i).sum();

let mut v = vec![9, 1, 8, 2, 7];
v.par_sort_unstable();

let words: Vec<&str> = "some big text".par_split_whitespace().collect();
```

## API surface

- **Traits**: `ParallelIterator`, `IndexedParallelIterator`,
  `IntoParallelIterator` (+ `par_iter()` / `par_iter_mut()` forms),
  `FromParallelIterator`, `ParallelExtend`, `ParallelSlice`,
  `ParallelSliceMut`, `ParallelString`.
- **Adapters**: `map`, `filter`, `filter_map`, `flat_map`,
  `flat_map_iter`, `flatten`, `flatten_iter`, `inspect`, `cloned`,
  `copied`, `chain`, `zip`, `zip_eq`, `enumerate`, `rev`, `skip`,
  `take`, `fold`, `fold_with`, `with_min_len`, `with_max_len`.
- **Reductions**: `for_each`, `sum`, `product`, `reduce`, `reduce_with`,
  `count`, `min`/`max` (+ `_by`, `_by_key`), `find_any`, `any`, `all`,
  `position_any`, `collect`, `collect_into_vec`.
- **Sources**: slices (+`par_chunks{,_exact,_mut}`, `par_windows`),
  `Vec` (by value), all integer `Range`/`RangeInclusive` (including
  exact-size `u64`/`i64` ranges, which rayon leaves unindexed),
  `Option`, `Result`, arrays, `VecDeque` (zero-copy), `BinaryHeap`,
  `HashMap`, `HashSet`, `BTreeMap`, `BTreeSet`, `LinkedList`, and
  strings (`par_chars`, `par_char_indices`, `par_bytes`, `par_lines`,
  `par_split_whitespace`).
- **Sorting**: `par_sort{,_by,_by_key}` (stable, parallel merges) and
  `par_sort_unstable{,_by,_by_key}` (parallel pdqsort-style with
  branchless block partitioning).
- **Task parallelism**: `join`, `join_context`, `scope`, `spawn`,
  `ThreadPool`/`ThreadPoolBuilder`.

## Design notes

The iterator architecture follows rayon's proven producer/consumer
model -- it is what lets adapter chains compile into a single
internally-iterated loop per leaf of the work-splitting tree (and hence
autovectorize). The performance work is concentrated in the execution
core and in leaf codegen:

- **Allocation-free `join`**: the stolen half lives on the caller's
  stack; the unstolen fast path is one deque-emptiness check, a push
  and a pop -- no fences, no latch traffic, no shared-counter reads.
- **Best-effort wakeups instead of hot-path synchronization**: pushers
  check for sleepers only when their deque becomes non-empty; thieves
  pay the wakeup forward when their victim has work left; idle workers
  spin, then yield (~100us, so consecutive operations reuse hot
  workers), then park with bounded timeouts that backstop any missed
  signal.
- **Adaptive splitting**: split budget of `2 * threads`, replenished
  when a piece is observed stolen (idle threads exist), bounded by
  `with_min_len`/`with_max_len`.
- **In-place parallel collect**: exact-length iterators write directly
  into the target `Vec`'s spare capacity through a panic-safe
  guard-tracked cursor that stays in a register for non-panicking
  sources.
- **External callers adapt**: short operations spin (saving a futex
  round trip -- the dominant cost of a small parallel call), long
  operations block immediately (a spinning caller competes with the
  workers for cores).

## Benchmarks

`cargo bench --bench compare` runs a head-to-head suite against rayon
(interleaved A/B sampling, median-of-rounds) and prints a markdown
table. Highlights on a 4-core machine: 3-10x faster dispatch on
small/medium inputs, 5x+ faster string iteration and `find_any`,
~1.3x faster sorts, parity on large memory-bound workloads.
