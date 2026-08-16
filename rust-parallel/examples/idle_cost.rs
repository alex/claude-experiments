//! Measures CPU burned by an idle pool: run one trivial op, then sit
//! quiet for 10 seconds and read per-thread utime/stime + ctx switches.

fn thread_stats(prefix: &str) -> (u64, u64) {
    // (cpu_ticks, nonvoluntary+voluntary ctx switches) summed over workers
    let pid = std::process::id().to_string();
    let mut ticks = 0u64;
    let mut switches = 0u64;
    for entry in std::fs::read_dir("/proc/self/task").unwrap() {
        let path = entry.unwrap().path();
        let tid = path.file_name().unwrap().to_string_lossy().to_string();
        if tid == pid { continue; }
        let stat = std::fs::read_to_string(path.join("stat")).unwrap_or_default();
        let comm_end = stat.rfind(')').unwrap_or(0);
        let name = &stat[stat.find('(').map(|i| i + 1).unwrap_or(0)..comm_end];
        if !name.starts_with(prefix) { continue; }
        let rest: Vec<&str> = stat[comm_end + 2..].split(' ').collect();
        ticks += rest[11].parse::<u64>().unwrap_or(0) + rest[12].parse::<u64>().unwrap_or(0);
        let status = std::fs::read_to_string(path.join("status")).unwrap_or_default();
        for line in status.lines() {
            if line.starts_with("voluntary_ctxt_switches") || line.starts_with("nonvoluntary_ctxt_switches") {
                switches += line.split_whitespace().last().unwrap().parse::<u64>().unwrap_or(0);
            }
        }
    }
    (ticks, switches)
}

fn main() {
    let mode = std::env::args().nth(2).unwrap_or_else(|| "idle".into());
    let which = std::env::args().nth(1).unwrap_or_else(|| "fil".into());
    let (prefix, op): (&str, Box<dyn Fn()>) = if which == "fil" {
        ("filament-worker", Box::new(|| { filament::join(|| (), || ()); }))
    } else {
        ("idle_cost", Box::new(|| { rayon::join(|| (), || ()); })) // rayon threads inherit binary name
    };
    op(); // force pool creation + one op

    if mode == "trickle" {
        // Intermittent load: a small op every 10ms (the scenario from
        // rayon PR #1314, where all idle workers spin per wakeup).
        std::thread::sleep(std::time::Duration::from_millis(300));
        let (t0, s0) = thread_stats(prefix);
        let window = std::time::Duration::from_secs(5);
        let start = std::time::Instant::now();
        let mut ops = 0u64;
        while start.elapsed() < window {
            op();
            ops += 1;
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        let (t1, s1) = thread_stats(prefix);
        let cpu_ms = (t1 - t0) as f64 * 10.0;
        println!(
            "{which} trickle: {} tiny ops over {}s: {:.0}ms worker CPU ({:.2}% of one core), {} ctx switches ({:.0}/sec)",
            ops, window.as_secs(), cpu_ms, 100.0 * cpu_ms / 1000.0 / window.as_secs_f64(),
            s1 - s0, (s1 - s0) as f64 / window.as_secs_f64()
        );
        return;
    }

    std::thread::sleep(std::time::Duration::from_millis(300)); // let workers settle
    let (t0, s0) = thread_stats(prefix);
    let quiet = std::time::Duration::from_secs(10);
    std::thread::sleep(quiet);
    let (t1, s1) = thread_stats(prefix);
    let cpu_ms = (t1 - t0) as f64 * 10.0; // CLK_TCK=100
    println!(
        "{which}: 16 idle workers over {}s quiet: {:.0}ms CPU total ({:.3}% of one core), {} ctx switches ({:.0}/sec)",
        quiet.as_secs(), cpu_ms, 100.0 * cpu_ms / 1000.0 / quiet.as_secs_f64(),
        s1 - s0, (s1 - s0) as f64 / quiet.as_secs_f64()
    );
}
