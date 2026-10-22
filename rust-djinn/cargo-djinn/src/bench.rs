//! `cargo djinn bench`: time the crate's performance workload.
//!
//! The workload is a `pub fn workload()` in the crate, named by
//! `[package.metadata.djinn] bench = "bench::workload"`. A generated runner
//! crate under `target/djinn/bench/` depends on the crate by path, is built
//! in release mode, calibrates how many iterations take at least
//! `min_time / batches` seconds, then runs `batches` batches and reports
//! nanoseconds per iteration. The median is the measurement and the spread
//! between batches (the interquartile range, robust to a batch disturbed by
//! load) the noise.

use crate::config::Config;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// One measured point of the workload: a level, say. Sizes are exact; times have noise.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Point {
    pub id: u64,
    pub ns_per_iter: Vec<f64>,
    pub median_ns: f64,
    pub min_ns: f64,
    pub max_ns: f64,
    pub iters_per_batch: u64,
    /// what the workload returned: a size to be minimised (`None` for a plain `workload()`)
    pub size: Option<u64>,
}

/// The relative spread of batch timings: the interquartile range over the
/// median (the full range for fewer than four batches). One batch slowed by
/// load does not move it, so it does not hide a real gain.
pub fn spread(ns: &[f64]) -> f64 {
    let mut v: Vec<f64> = ns.iter().copied().filter(|x| x.is_finite()).collect();
    if v.len() < 2 {
        return 0.0;
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = v.len();
    let med = v[n / 2];
    if med <= 0.0 {
        return 0.0;
    }
    let (lo, hi) = if n < 4 { (v[0], v[n - 1]) } else { (v[n / 4], v[(3 * n) / 4]) };
    (hi - lo) / med
}

impl Point {
    pub fn noise(&self) -> f64 {
        spread(&self.ns_per_iter)
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Measurement {
    pub ns_per_iter: Vec<f64>,
    /// the sum over the points (the single point's, for a plain workload)
    pub median_ns: f64,
    pub min_ns: f64,
    pub max_ns: f64,
    pub iters_per_batch: u64,
    pub total_secs: f64,
    #[serde(default)]
    pub points: Vec<Point>,
}

impl Measurement {
    /// Relative spread between batches (`spread`): the worst point's.
    pub fn noise(&self) -> f64 {
        self.points.iter().map(|p| p.noise()).fold(spread(&self.ns_per_iter), f64::max)
    }
    /// Several points whose sizes do not trade off against time (all absent
    /// or all equal): each point is judged on its own.
    pub fn independent_points(&self) -> bool {
        self.points.len() > 1 && self.points.windows(2).all(|w| w[0].size == w[1].size)
    }
    /// Several points with sizes: the frontier rule applies.
    pub fn is_multi(&self) -> bool {
        self.points.len() > 1 || self.points.iter().any(|p| p.size.is_some())
    }
    pub fn line(&self) -> String {
        if self.is_multi() {
            return format!(
                "{} per iteration over {} points (median of {} batches each; worst spread {:.1}%)",
                fmt_ns(self.median_ns),
                self.points.len(),
                self.ns_per_iter.len().max(self.points.first().map(|p| p.ns_per_iter.len()).unwrap_or(0)),
                self.noise() * 100.0
            );
        }
        format!(
            "{} per iteration (median of {} batches × {} iterations; spread {:.1}%)",
            fmt_ns(self.median_ns),
            self.ns_per_iter.len(),
            self.iters_per_batch,
            self.noise() * 100.0
        )
    }
    /// The per-point table: id, size, time, spread.
    pub fn table(&self) -> String {
        let mut s = String::from("point        size      time/iter   spread\n");
        for p in &self.points {
            s.push_str(&format!(
                "{:<5} {:>11} {:>14} {:>7.1}%\n",
                p.id,
                p.size.map(|z| z.to_string()).unwrap_or_else(|| "—".into()),
                fmt_ns(p.median_ns),
                p.noise() * 100.0
            ));
        }
        s
    }
}

pub fn fmt_ns(ns: f64) -> String {
    if ns >= 1e9 {
        format!("{:.3} s", ns / 1e9)
    } else if ns >= 1e6 {
        format!("{:.3} ms", ns / 1e6)
    } else if ns >= 1e3 {
        format!("{:.2} µs", ns / 1e3)
    } else {
        format!("{:.0} ns", ns)
    }
}

/// The workload's Rust path, e.g. `bench::workload`, and the crate's identifier.
pub fn workload_path(cfg: &Config) -> Result<(String, String), String> {
    let w = cfg.bench.clone().ok_or("no workload configured: set [package.metadata.djinn] bench = \"bench::workload\" (a `pub fn workload()` in the crate)")?;
    let krate = cfg.crate_name.replace('-', "_");
    Ok((krate, w.trim_start_matches("crate::").to_string()))
}

/// Source text of the module holding the workload, for the agent's prompt.
pub fn workload_source(cfg: &Config) -> Option<String> {
    let (_, w) = workload_path(cfg).ok()?;
    let module = w.rsplit_once("::").map(|(m, _)| m.to_string()).unwrap_or_default();
    let candidates = if module.is_empty() {
        vec![cfg.crate_dir.join("src").join("lib.rs")]
    } else {
        let rel = module.replace("::", "/");
        vec![cfg.crate_dir.join("src").join(format!("{rel}.rs")), cfg.crate_dir.join("src").join(&rel).join("mod.rs")]
    };
    candidates.into_iter().find_map(|p| fs::read_to_string(p).ok())
}

fn runner_dir(cfg: &Config) -> PathBuf {
    cfg.state_dir().join("bench")
}

fn write_runner(cfg: &Config) -> Result<PathBuf, String> {
    let (krate, w) = workload_path(cfg)?;
    let dir = runner_dir(cfg);
    // a plain `workload()` is one point (id 0) returning no size; with points
    // the workload takes the point and returns a size
    let (points, call) = match &cfg.bench_points {
        Some(ps) if !ps.is_empty() => (ps.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(", "), format!("Some({krate}::{w}(id as usize) as u64)")),
        _ => ("0".to_string(), format!("{{ {krate}::{w}(); None }}")),
    };
    fs::create_dir_all(dir.join("src")).map_err(|e| e.to_string())?;
    let manifest = format!(
        "[package]\nname = \"djinn-bench-runner\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[dependencies]\n{} = {{ path = \"{}\" }}\n\n[profile.release]\n{}\n[workspace]\n",
        cfg.crate_name,
        cfg.crate_dir.display(),
        // the crate's own release profile, so the runner measures what `cargo build --release` ships
        cfg.release_profile.clone().unwrap_or_else(|| "opt-level = 3\ndebug = false\n".into())
    );
    fs::write(dir.join("Cargo.toml"), manifest).map_err(|e| e.to_string())?;
    let main = format!(
        r#"// generated by `cargo djinn bench`; times {krate}::{w} at the points [{points}],
// `jobs` points at a time (each on its own thread)
use std::hint::black_box;
use std::sync::{{Arc, Mutex}};
use std::time::Instant;

fn run(id: u64) -> Option<u64> {{
    black_box({call})
}}

fn measure(id: u64, per_batch: f64, batches: usize) -> (u64, Vec<f64>, Option<u64>) {{
    let size = run(id);
    // calibrate: double until one batch takes at least per_batch seconds
    let mut iters: u64 = 1;
    loop {{
        let t = Instant::now();
        for _ in 0..iters {{
            run(id);
        }}
        let el = t.elapsed().as_secs_f64();
        if el >= per_batch || iters >= 1u64 << 40 {{
            break;
        }}
        let factor = if el > 0.0 {{ (per_batch / el * 1.2).ceil() as u64 }} else {{ 10 }};
        iters = iters.saturating_mul(factor.max(2));
    }}
    let mut ns = Vec::new();
    for _ in 0..batches {{
        let t = Instant::now();
        for _ in 0..iters {{
            run(id);
        }}
        ns.push(t.elapsed().as_nanos() as f64 / iters as f64);
    }}
    (iters, ns, size)
}}

fn main() {{
    let args: Vec<String> = std::env::args().collect();
    let min_secs: f64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(5.0);
    let batches: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5);
    let jobs: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(1).max(1);
    let per_batch = min_secs / batches as f64;
    let points: Vec<u64> = vec![{points}];
    let start = Instant::now();
    let queue = Arc::new(Mutex::new(points.clone()));
    let results = Arc::new(Mutex::new(Vec::new()));
    let mut handles = Vec::new();
    for _ in 0..jobs.min(points.len()) {{
        let queue = queue.clone();
        let results = results.clone();
        handles.push(std::thread::spawn(move || loop {{
            let id = {{ let mut q = queue.lock().unwrap(); if q.is_empty() {{ return; }} q.remove(0) }};
            let (iters, ns, size) = measure(id, per_batch, batches);
            results.lock().unwrap().push((id, iters, ns, size));
        }}));
    }}
    for h in handles {{
        h.join().unwrap();
    }}
    let total = start.elapsed().as_secs_f64();
    let mut results = results.lock().unwrap().clone();
    results.sort_by_key(|r| r.0);
    let items: Vec<String> = results
        .iter()
        .map(|(id, iters, ns, size)| {{
            let list: Vec<String> = ns.iter().map(|x| format!("{{x}}")).collect();
            format!("{{{{\"id\":{{id}},\"iters\":{{iters}},\"ns_per_iter\":[{{}}],\"size\":{{}}}}}}", list.join(","), size.map(|z| z.to_string()).unwrap_or("null".into()))
        }})
        .collect();
    println!("{{{{\"points\":[{{}}],\"total_secs\":{{total}}}}}}", items.join(","));
}}
"#
    );
    fs::write(dir.join("src").join("main.rs"), main).map_err(|e| e.to_string())?;
    Ok(dir)
}

/// Build the runner in release mode and run it: `jobs` points at a time.
pub fn measure(cfg: &Config, min_time: f64, batches: usize, jobs: usize, log: &mut dyn FnMut(&str)) -> Result<Measurement, String> {
    // no batches would make a batch infinitely long (the runner calibrates to
    // min_time / batches)
    let batches = batches.max(1);
    let dir = write_runner(cfg)?;
    log("== bench: building the workload runner (release)");
    let out = Command::new("cargo")
        .args(["build", "--release", "--quiet"])
        .current_dir(&dir)
        .output()
        .map_err(|e| format!("cargo: {e}"))?;
    if !out.status.success() {
        let text = String::from_utf8_lossy(&out.stderr);
        let tail: Vec<&str> = text.lines().rev().take(30).collect::<Vec<_>>().into_iter().rev().collect();
        return Err(format!("bench runner failed to build:\n{}", tail.join("\n")));
    }
    let npoints = cfg.bench_points.as_ref().map(|p| p.len()).unwrap_or(1);
    log(&format!(
        "== bench: running the workload for at least {min_time:.0} s ({batches} batches){}",
        if npoints > 1 { format!(" at each of {npoints} points, {} at a time", jobs.min(npoints)) } else { String::new() }
    ));
    let exe = dir.join("target").join("release").join("djinn-bench-runner");
    let out = Command::new(&exe)
        .arg(format!("{min_time}"))
        .arg(format!("{batches}"))
        .arg(format!("{jobs}"))
        .output()
        .map_err(|e| format!("runner: {e}"))?;
    if !out.status.success() {
        return Err(format!("the workload runner failed: {}", String::from_utf8_lossy(&out.stderr)));
    }
    let text = String::from_utf8_lossy(&out.stdout);
    // the report is the runner's last line: the workload may print too
    let last = text.lines().rev().find(|l| !l.trim().is_empty()).unwrap_or("");
    let json: serde_json::Value = serde_json::from_str(last.trim()).map_err(|e| format!("runner output: {e}: {text}"))?;
    let mut points = Vec::new();
    for pj in json["points"].as_array().into_iter().flatten() {
        let ns: Vec<f64> = pj["ns_per_iter"].as_array().into_iter().flatten().filter_map(|v| v.as_f64()).collect();
        if ns.is_empty() {
            return Err("runner produced no timings".into());
        }
        let mut sorted = ns.clone();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
        points.push(Point {
            id: pj["id"].as_u64().unwrap_or(0),
            median_ns: sorted[sorted.len() / 2],
            min_ns: sorted[0],
            max_ns: sorted[sorted.len() - 1],
            iters_per_batch: pj["iters"].as_u64().unwrap_or(0),
            size: pj["size"].as_u64(),
            ns_per_iter: ns,
        });
    }
    if points.is_empty() {
        return Err("runner produced no timings".into());
    }
    let single = points.len() == 1 && points[0].size.is_none();
    let m = Measurement {
        median_ns: points.iter().map(|p| p.median_ns).sum(),
        min_ns: points.iter().map(|p| p.min_ns).sum(),
        max_ns: points.iter().map(|p| p.max_ns).sum(),
        iters_per_batch: points[0].iters_per_batch,
        total_secs: json["total_secs"].as_f64().unwrap_or(0.0),
        ns_per_iter: if single { points[0].ns_per_iter.clone() } else { Vec::new() },
        points: if single { Vec::new() } else { points },
    };
    log(&format!("== bench: {}", m.line()));
    if m.is_multi() {
        for l in m.table().lines() {
            log(&format!("   {l}"));
        }
    }
    Ok(m)
}
