//! Profiling helper: run one workload in a loop under perf.
//! Usage: profile <fil|ray> <workload> [iters]

use std::hint::black_box;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let lib = args.get(1).map(String::as_str).unwrap_or("fil");
    let work = args.get(2).map(String::as_str).unwrap_or("sum10m");
    let iters: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(200);

    // warm pools
    filament::join(|| (), || ());
    rayon::join(|| (), || ());

    match (lib, work) {
        (l, "sum10m") => {
            let v: Vec<u64> = (0..10_000_000).collect();
            for _ in 0..iters {
                let s = if l == "fil" {
                    use filament::prelude::*;
                    v.par_iter().sum::<u64>()
                } else {
                    use rayon::prelude::*;
                    v.par_iter().sum::<u64>()
                };
                black_box(s);
            }
        }
        (l, "collect10m") => {
            for _ in 0..iters {
                let s = if l == "fil" {
                    use filament::prelude::*;
                    (0..10_000_000usize)
                        .into_par_iter()
                        .map(|i| i.wrapping_mul(31))
                        .collect::<Vec<_>>()
                } else {
                    use rayon::prelude::*;
                    (0..10_000_000usize)
                        .into_par_iter()
                        .map(|i| i.wrapping_mul(31))
                        .collect::<Vec<_>>()
                };
                black_box(s.len());
            }
        }
        (l, "fib30") => {
            fn fib_seq(n: u32) -> u64 {
                if n < 2 {
                    return n as u64;
                }
                fib_seq(n - 1) + fib_seq(n - 2)
            }
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
            for _ in 0..iters {
                let s = if l == "fil" { fib_fil(30) } else { fib_ray(30) };
                black_box(s);
            }
        }
        _ => eprintln!("unknown workload"),
    }

    // Aggregate per-thread stats: minflt (field 10), utime (14), stime (15).
    let mut minflt = 0u64;
    let mut utime = 0u64;
    let mut stime = 0u64;
    for entry in std::fs::read_dir("/proc/self/task").unwrap() {
        let stat = std::fs::read_to_string(entry.unwrap().path().join("stat")).unwrap();
        // skip past the comm field, which is parenthesized
        let rest = stat.rsplit(") ").next().unwrap();
        let fields: Vec<&str> = rest.split(' ').collect();
        minflt += fields[7].parse::<u64>().unwrap_or(0); // field 10 overall
        utime += fields[11].parse::<u64>().unwrap_or(0); // field 14
        stime += fields[12].parse::<u64>().unwrap_or(0); // field 15
    }
    eprintln!("minflt={minflt} utime_ticks={utime} stime_ticks={stime}");
}

// (ctx-switch reporting appended)
