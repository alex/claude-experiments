//! Head-to-head benchmark: filament vs rayon (vs sequential).
//!
//! Custom harness (no criterion): auto-calibrated inner iteration counts,
//! median-of-samples reporting, and a markdown table on stdout.
//!
//! Run with: `cargo bench --bench compare`
//! Filter:   `cargo bench --bench compare -- sum`

use std::hint::black_box;
use std::time::Instant;

// ---------------------------------------------------------------------
// Timing harness

const TARGET_SAMPLE_MS: f64 = 20.0;
const ROUNDS: usize = 9;

/// Measure median ns/iteration of two competing implementations with
/// *interleaved* sample batches (ABAB...), so drift in machine load
/// (shared vCPUs, frequency scaling) hits both sides equally instead of
/// whichever ran second.
fn measure_pair<RA, RB>(mut fa: impl FnMut() -> RA, mut fb: impl FnMut() -> RB) -> (f64, f64) {
    fn calibrate<R>(f: &mut impl FnMut() -> R) -> u64 {
        let mut iters_done = 0u64;
        let start = Instant::now();
        while start.elapsed().as_millis() < 60 || iters_done < 3 {
            black_box(f());
            iters_done += 1;
        }
        let mean_ns = start.elapsed().as_nanos() as f64 / iters_done as f64;
        ((TARGET_SAMPLE_MS * 1e6 / mean_ns).ceil() as u64).max(1)
    }
    fn sample<R>(f: &mut impl FnMut() -> R, inner: u64) -> f64 {
        let t = Instant::now();
        for _ in 0..inner {
            black_box(f());
        }
        t.elapsed().as_nanos() as f64 / inner as f64
    }

    let inner_a = calibrate(&mut fa);
    let inner_b = calibrate(&mut fb);
    let mut samples_a = Vec::with_capacity(ROUNDS);
    let mut samples_b = Vec::with_capacity(ROUNDS);
    for _ in 0..ROUNDS {
        samples_a.push(sample(&mut fa, inner_a));
        samples_b.push(sample(&mut fb, inner_b));
    }
    samples_a.sort_by(|a, b| a.partial_cmp(b).unwrap());
    samples_b.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (samples_a[ROUNDS / 2], samples_b[ROUNDS / 2])
}

/// Single-implementation measurement (sequential baselines).
fn measure<R>(mut f: impl FnMut() -> R) -> f64 {
    let mut iters_done = 0u64;
    let start = Instant::now();
    while start.elapsed().as_millis() < 60 || iters_done < 3 {
        black_box(f());
        iters_done += 1;
    }
    let mean_ns = start.elapsed().as_nanos() as f64 / iters_done as f64;
    let inner = ((TARGET_SAMPLE_MS * 1e6 / mean_ns).ceil() as u64).max(1);
    let mut samples: Vec<f64> = (0..ROUNDS)
        .map(|_| {
            let t = Instant::now();
            for _ in 0..inner {
                black_box(f());
            }
            t.elapsed().as_nanos() as f64 / inner as f64
        })
        .collect();
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    samples[ROUNDS / 2]
}

struct Row {
    name: &'static str,
    seq_ns: Option<f64>,
    filament_ns: f64,
    rayon_ns: f64,
}

fn fmt_time(ns: f64) -> String {
    if ns >= 1e9 {
        format!("{:.2} s", ns / 1e9)
    } else if ns >= 1e6 {
        format!("{:.2} ms", ns / 1e6)
    } else if ns >= 1e3 {
        format!("{:.2} µs", ns / 1e3)
    } else {
        format!("{:.0} ns", ns)
    }
}

// ---------------------------------------------------------------------
// Workloads

fn main() {
    // Skip flags cargo passes (e.g. `--bench`); first non-flag arg filters.
    let filter = std::env::args()
        .skip(1)
        .find(|a| !a.starts_with('-'))
        .unwrap_or_default();

    // Force both pools up before timing anything.
    let _ = filament::current_num_threads();
    filament::join(|| (), || ());
    rayon::join(|| (), || ());
    eprintln!(
        "threads: filament={}, rayon={}",
        filament::current_num_threads(),
        rayon::current_num_threads()
    );

    let mut rows: Vec<Row> = Vec::new();

    macro_rules! bench {
        ($name:literal, seq $seq:expr, fil $fil:expr, ray $ray:expr) => {
            if $name.contains(&filter) {
                eprintln!("running: {}", $name);
                let (fil, ray) = measure_pair(|| $fil, || $ray);
                let seq = Some(measure(|| $seq));
                rows.push(Row {
                    name: $name,
                    seq_ns: seq,
                    filament_ns: fil,
                    rayon_ns: ray,
                });
            }
        };
        ($name:literal, fil $fil:expr, ray $ray:expr) => {
            if $name.contains(&filter) {
                eprintln!("running: {}", $name);
                let (fil, ray) = measure_pair(|| $fil, || $ray);
                rows.push(Row {
                    name: $name,
                    seq_ns: None,
                    filament_ns: fil,
                    rayon_ns: ray,
                });
            }
        };
    }

    // --- sum over ranges ---
    {
        bench!("sum_range_10M",
            seq (0..10_000_000usize).sum::<usize>(),
            fil {
                use filament::prelude::*;
                (0..10_000_000usize).into_par_iter().sum::<usize>()
            },
            ray {
                use rayon::prelude::*;
                (0..10_000_000usize).into_par_iter().sum::<usize>()
            });
    }

    // --- sum over slices (memory-bound) ---
    {
        use filament::prelude::*;
        let v: Vec<u64> = (0..10_000_000).collect();
        {
            use rayon::prelude::*;
            let vr = &v;
            bench!("sum_slice_10M_u64",
                seq vr.iter().sum::<u64>(),
                fil filament::prelude::IntoParallelRefIterator::par_iter(vr).sum::<u64>(),
                ray rayon::prelude::IntoParallelRefIterator::par_iter(vr).sum::<u64>());
        }
    }

    // --- small inputs: fixed overhead test ---
    {
        let v: Vec<u64> = (0..10_000).collect();
        let vr = &v;
        bench!("sum_slice_10k_u64",
            seq vr.iter().sum::<u64>(),
            fil {
                use filament::prelude::*;
                vr.par_iter().sum::<u64>()
            },
            ray {
                use rayon::prelude::*;
                vr.par_iter().sum::<u64>()
            });
    }
    {
        let v: Vec<u64> = (0..100_000).collect();
        let vr = &v;
        bench!("sum_slice_100k_u64",
            seq vr.iter().sum::<u64>(),
            fil {
                use filament::prelude::*;
                vr.par_iter().sum::<u64>()
            },
            ray {
                use rayon::prelude::*;
                vr.par_iter().sum::<u64>()
            });
    }

    // --- map + sum, compute-light (tests fusion/vectorization) ---
    {
        let v: Vec<u64> = (0..10_000_000).collect();
        let vr = &v;
        bench!("map_sum_slice_10M",
            seq vr.iter().map(|&x| x.wrapping_mul(31).wrapping_add(7)).sum::<u64>(),
            fil {
                use filament::prelude::*;
                vr.par_iter().map(|&x| x.wrapping_mul(31).wrapping_add(7)).sum::<u64>()
            },
            ray {
                use rayon::prelude::*;
                vr.par_iter().map(|&x| x.wrapping_mul(31).wrapping_add(7)).sum::<u64>()
            });
    }

    // --- map + sum, compute-heavy per item ---
    {
        #[inline]
        fn heavy(x: u64) -> u64 {
            // ~100ns of integer mixing per item
            let mut h = x;
            for _ in 0..64 {
                h ^= h >> 33;
                h = h.wrapping_mul(0xff51afd7ed558ccd);
                h ^= h >> 29;
            }
            h
        }
        bench!("heavy_map_sum_100k",
            seq (0..100_000u64).map(heavy).sum::<u64>(),
            fil {
                use filament::prelude::*;
                (0..100_000u64).into_par_iter().map(heavy).sum::<u64>()
            },
            ray {
                use rayon::prelude::*;
                (0..100_000u64).into_par_iter().map(heavy).sum::<u64>()
            });
    }

    // --- collect (indexed, in-place) ---
    {
        bench!("collect_map_10M",
            seq (0..10_000_000usize).map(|i| i.wrapping_mul(31)).collect::<Vec<_>>(),
            fil {
                use filament::prelude::*;
                (0..10_000_000usize).into_par_iter().map(|i| i.wrapping_mul(31)).collect::<Vec<_>>()
            },
            ray {
                use rayon::prelude::*;
                (0..10_000_000usize).into_par_iter().map(|i| i.wrapping_mul(31)).collect::<Vec<_>>()
            });
    }

    // --- collect_into_vec (no allocation) ---
    {
        let mut fil_target: Vec<usize> = Vec::new();
        let mut ray_target: Vec<usize> = Vec::new();
        let mut seq_target: Vec<usize> = Vec::new();
        bench!("collect_into_vec_10M",
            seq {
                seq_target.clear();
                seq_target.extend((0..10_000_000usize).map(|i| i ^ 0xabcd));
                seq_target.len()
            },
            fil {
                use filament::prelude::*;
                (0..10_000_000usize).into_par_iter().map(|i| i ^ 0xabcd).collect_into_vec(&mut fil_target);
                fil_target.len()
            },
            ray {
                use rayon::prelude::*;
                (0..10_000_000usize).into_par_iter().map(|i| i ^ 0xabcd).collect_into_vec(&mut ray_target);
                ray_target.len()
            });
    }

    // --- for_each over mutable slice ---
    {
        let mut v1 = vec![0u64; 5_000_000];
        let mut v2 = vec![0u64; 5_000_000];
        let mut v3 = vec![0u64; 5_000_000];
        bench!("write_slice_5M",
            seq v3.iter_mut().enumerate().for_each(|(i, x)| *x = i as u64 * 3),
            fil {
                use filament::prelude::*;
                v1.par_iter_mut().for_each(|x| *x = 3);
            },
            ray {
                use rayon::prelude::*;
                v2.par_iter_mut().for_each(|x| *x = 3);
            });
    }

    // --- par_chunks ---
    {
        let v: Vec<u64> = (0..10_000_000).collect();
        let vr = &v;
        bench!("chunks_4k_sum_10M",
            seq vr.chunks(4096).map(|c| c.iter().sum::<u64>()).sum::<u64>(),
            fil {
                use filament::prelude::*;
                vr.par_chunks(4096).map(|c| c.iter().sum::<u64>()).sum::<u64>()
            },
            ray {
                use rayon::prelude::*;
                vr.par_chunks(4096).map(|c| c.iter().sum::<u64>()).sum::<u64>()
            });
    }

    // --- raw join overhead: parallel fib ---
    {
        fn fib_fil(n: u32) -> u64 {
            if n < 2 {
                return n as u64;
            }
            if n < 12 {
                return fib_seq(n);
            }
            let (a, b) = filament::join(|| fib_fil(n - 1), || fib_fil(n - 2));
            a + b
        }
        fn fib_ray(n: u32) -> u64 {
            if n < 2 {
                return n as u64;
            }
            if n < 12 {
                return fib_seq(n);
            }
            let (a, b) = rayon::join(|| fib_ray(n - 1), || fib_ray(n - 2));
            a + b
        }
        fn fib_seq(n: u32) -> u64 {
            if n < 2 {
                return n as u64;
            }
            fib_seq(n - 1) + fib_seq(n - 2)
        }
        bench!("fib_30_join_cutoff12",
            seq fib_seq(30),
            fil fib_fil(30),
            ray fib_ray(30));

        // No sequential cutoff: pure join overhead stress.
        fn fib_fil_raw(n: u32) -> u64 {
            if n < 2 {
                return n as u64;
            }
            let (a, b) = filament::join(|| fib_fil_raw(n - 1), || fib_fil_raw(n - 2));
            a + b
        }
        fn fib_ray_raw(n: u32) -> u64 {
            if n < 2 {
                return n as u64;
            }
            let (a, b) = rayon::join(|| fib_ray_raw(n - 1), || fib_ray_raw(n - 2));
            a + b
        }
        bench!("fib_20_join_every_level",
            seq fib_seq(20),
            fil fib_fil_raw(20),
            ray fib_ray_raw(20));
    }

    // --- tiny input: is parallel dispatch cheap when there's no win? ---
    {
        let v: Vec<u64> = (0..1000).collect();
        let vr = &v;
        bench!("sum_slice_1k_u64",
            seq vr.iter().sum::<u64>(),
            fil {
                use filament::prelude::*;
                vr.par_iter().sum::<u64>()
            },
            ray {
                use rayon::prelude::*;
                vr.par_iter().sum::<u64>()
            });
    }

    // --- filter + sum (unindexed consumer path) ---
    {
        let v: Vec<u64> = (0..10_000_000).collect();
        let vr = &v;
        bench!("filter_sum_10M",
            seq vr.iter().filter(|&&x| x % 3 == 0).sum::<u64>(),
            fil {
                use filament::prelude::*;
                vr.par_iter().filter(|&&x| x % 3 == 0).sum::<u64>()
            },
            ray {
                use rayon::prelude::*;
                vr.par_iter().filter(|&&x| x % 3 == 0).sum::<u64>()
            });
    }

    // --- filter + collect (unindexed collect: per-leaf vecs + gather) ---
    {
        let v: Vec<u64> = (0..2_000_000).collect();
        let vr = &v;
        bench!("filter_collect_2M",
            seq vr.iter().copied().filter(|&x| x % 3 == 0).collect::<Vec<_>>(),
            fil {
                use filament::prelude::*;
                vr.par_iter().copied().filter(|&x| x % 3 == 0).collect::<Vec<_>>()
            },
            ray {
                use rayon::prelude::*;
                vr.par_iter().copied().filter(|&x| x % 3 == 0).collect::<Vec<_>>()
            });
    }

    // --- zip: dot product ---
    {
        let a: Vec<f64> = (0..10_000_000).map(|i| (i as f64) * 0.5).collect();
        let b: Vec<f64> = (0..10_000_000).map(|i| (i as f64) * 0.25).collect();
        let (ar, br) = (&a, &b);
        bench!("dot_product_10M_f64",
            seq ar.iter().zip(br.iter()).map(|(x, y)| x * y).sum::<f64>(),
            fil {
                use filament::prelude::*;
                ar.par_iter().zip(br.par_iter()).map(|(x, y)| x * y).sum::<f64>()
            },
            ray {
                use rayon::prelude::*;
                ar.par_iter().zip(br.par_iter()).map(|(x, y)| x * y).sum::<f64>()
            });
    }

    // --- fold: byte histogram ---
    {
        let data: Vec<u8> = (0..16_000_000usize).map(|i| (i.wrapping_mul(2654435761) >> 13) as u8).collect();
        let dr = &data;
        bench!("histogram_16M_bytes",
            seq {
                let mut h = [0u32; 256];
                for &b in dr.iter() { h[b as usize] += 1; }
                h[0]
            },
            fil {
                use filament::prelude::*;
                let h = dr.par_iter().fold(|| vec![0u32; 256], |mut h, &b| { h[b as usize] += 1; h })
                    .reduce(|| vec![0u32; 256], |mut a, b| { for i in 0..256 { a[i] += b[i]; } a });
                h[0]
            },
            ray {
                use rayon::prelude::*;
                let h = dr.par_iter().fold(|| vec![0u32; 256], |mut h, &b| { h[b as usize] += 1; h })
                    .reduce(|| vec![0u32; 256], |mut a, b| { for i in 0..256 { a[i] += b[i]; } a });
                h[0]
            });
    }

    // --- find_any: needle midway ---
    {
        let v: Vec<u64> = (0..10_000_000).collect();
        let vr = &v;
        bench!("find_any_10M_mid",
            seq vr.iter().find(|&&x| x == 5_000_000).copied(),
            fil {
                use filament::prelude::*;
                vr.par_iter().find_any(|&&x| x == 5_000_000).copied()
            },
            ray {
                use rayon::prelude::*;
                vr.par_iter().find_any(|&&x| x == 5_000_000).copied()
            });
    }

    // --- sorts ---
    {
        fn lcg_vec(n: usize, m: u64) -> Vec<u64> {
            let mut s = 0x243F6A8885A308D3u64;
            (0..n).map(|_| {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                (s >> 33) % m
            }).collect()
        }
        let base = lcg_vec(5_000_000, u64::MAX);
        {
            let mut vs = base.clone(); let mut vf = base.clone(); let mut vr2 = base.clone();
            bench!("par_sort_unstable_5M",
                seq { vs.copy_from_slice(&base); vs.sort_unstable(); vs[0] },
                fil {
                    use filament::prelude::*;
                    vf.copy_from_slice(&base); vf.par_sort_unstable(); vf[0]
                },
                ray {
                    use rayon::prelude::*;
                    vr2.copy_from_slice(&base); vr2.par_sort_unstable(); vr2[0]
                });
        }
        {
            let mut vs = base.clone(); let mut vf = base.clone(); let mut vr2 = base.clone();
            bench!("par_sort_stable_5M",
                seq { vs.copy_from_slice(&base); vs.sort(); vs[0] },
                fil {
                    use filament::prelude::*;
                    vf.copy_from_slice(&base); vf.par_sort(); vf[0]
                },
                ray {
                    use rayon::prelude::*;
                    vr2.copy_from_slice(&base); vr2.par_sort(); vr2[0]
                });
        }
        {
            let dups = lcg_vec(5_000_000, 100);
            let mut vs = dups.clone(); let mut vf = dups.clone(); let mut vr2 = dups.clone();
            bench!("par_sort_unstable_5M_dups100",
                seq { vs.copy_from_slice(&dups); vs.sort_unstable(); vs[0] },
                fil {
                    use filament::prelude::*;
                    vf.copy_from_slice(&dups); vf.par_sort_unstable(); vf[0]
                },
                ray {
                    use rayon::prelude::*;
                    vr2.copy_from_slice(&dups); vr2.par_sort_unstable(); vr2[0]
                });
        }
    }

    // --- strings: char count over multibyte text ---
    {
        let text: String = "the quick brown fox jümps over the lazy dög 漢字テキスト🦀 ".repeat(200_000);
        let tr: &str = &text;
        bench!("count_chars_11M",
            seq tr.chars().count(),
            fil {
                use filament::prelude::*;
                tr.par_chars().count()
            },
            ray {
                use rayon::prelude::*;
                tr.par_chars().count()
            });
    }

    // ---------------------------------------------------------------
    // Report

    println!();
    println!(
        "| benchmark | sequential | rayon | filament | filament vs rayon |"
    );
    println!("|---|---:|---:|---:|---:|");
    for row in &rows {
        let ratio = row.rayon_ns / row.filament_ns;
        let vs = if ratio >= 1.0 {
            format!("**{:.2}x faster**", ratio)
        } else {
            format!("{:.2}x slower", 1.0 / ratio)
        };
        println!(
            "| {} | {} | {} | {} | {} |",
            row.name,
            row.seq_ns.map(fmt_time).unwrap_or_else(|| "-".into()),
            fmt_time(row.rayon_ns),
            fmt_time(row.filament_ns),
            vs
        );
    }
}
