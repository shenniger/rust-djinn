//! `cargo djinn optimize`: hill-climb on performance with an LLM, under the
//! verifier.
//!
//! 1. `verify` must pass (there is nothing to optimize otherwise).
//! 2. Baseline: time the workload (`bench`).
//! 3. Per cycle: checkpoint the verified solution and proofs; run an agent in
//!    a jail with the workload, the current timing, the acceptance rule and
//!    the history of earlier attempts; then `verify` — a failure reverts —
//!    and re-measure — not faster beyond noise and threshold reverts (noise:
//!    the batches' interquartile spread; a result better than the threshold
//!    but not the noise is re-measured with twice the batches first). Points
//!    with sizes are judged by their trade-off curve; points without (or all
//!    of one size) one by one: faster at some, slower at none. An accepted
//!    attempt becomes the new baseline and checkpoint.
//! 4. Stop after `--cycles`, when the estimated spend reaches `--limit`, when
//!    the agent stops on an API error (a usage limit: exit status 5, with the
//!    error printed), or on Ctrl-C, which kills the agent and restores the
//!    last known-good checkpoint.
//!
//! The history (`.djinnscratch/optimize.json`: the baseline, every attempt
//! and its verdict, the spend) survives a restart: a new run resumes it,
//! continues the cycle numbering, and counts `--cycles` and `--limit` over
//! all runs, so restarts never exceed the budget. A cycle the agent could not
//! work on (an API error) does not count. The crate as it is — it must
//! verify — is the starting point, re-measured; `implement -B` and `clean`
//! archive the history with the implementation it belongs to.

use crate::agent::{self, Opts};
use crate::bench::{self, fmt_ns, Measurement};
use crate::config::*;
use crate::status;
use crate::verify::{self, Log};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

pub struct OptOpts {
    pub cycles: Option<usize>,
    pub min_time: f64,
    pub batches: usize,
    /// points measured concurrently (multi-point workloads)
    pub jobs: usize,
    /// required relative improvement, e.g. 0.03
    pub threshold: f64,
    pub agent: Opts,
}

/// The verdict of a cycle whose agent stopped on an API error.
const API_ERROR_VERDICT: &str = "agent stopped on an API error";

/// Exit status of `optimize` when the agent stopped on an API error.
pub const EXIT_API_ERROR: u8 = 5;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Attempt {
    pub cycle: usize,
    pub job: String,
    /// accepted | not faster | did not verify (<stage>) | interrupted | agent failed
    pub verdict: String,
    pub ns: Option<f64>,
    /// multi-point workloads: (point, size, median ns) per point
    #[serde(default)]
    pub points: Vec<(u64, Option<u64>, f64)>,
    pub summary: String,
    pub cost_usd: Option<f64>,
    pub cost_is_estimate: bool,
    pub tokens_in: u64,
    pub tokens_out: u64,
    pub elapsed_secs: u64,
}

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct OptimizeLog {
    pub started: u64,
    pub finished: Option<u64>,
    pub baseline_ns: f64,
    pub current_ns: f64,
    #[serde(default)]
    pub baseline_points: Vec<(u64, Option<u64>, f64)>,
    #[serde(default)]
    pub current_points: Vec<(u64, Option<u64>, f64)>,
    pub attempts: Vec<Attempt>,
    pub accepted: usize,
    pub spent_usd: f64,
    pub interrupted: bool,
}

impl OptimizeLog {
    pub fn path(cfg: &Config) -> PathBuf {
        cfg.state_dir().join("optimize.json")
    }
    pub fn load(cfg: &Config) -> Option<OptimizeLog> {
        serde_json::from_str(&fs::read_to_string(Self::path(cfg)).ok()?).ok()
    }
    fn save(&self, cfg: &Config) {
        let _ = fs::create_dir_all(cfg.state_dir());
        if let Ok(s) = serde_json::to_string_pretty(self) {
            let _ = fs::write(Self::path(cfg), s);
        }
    }
    pub fn speedup(&self) -> f64 {
        if self.current_ns > 0.0 {
            self.baseline_ns / self.current_ns
        } else {
            1.0
        }
    }
    /// The cycles that count toward `--cycles`: every attempt but those the
    /// agent could not work on (it stopped on an API error).
    pub fn cycles_done(&self) -> usize {
        self.attempts.iter().filter(|a| a.verdict != API_ERROR_VERDICT).count()
    }
    /// The number of the next cycle: numbering continues across restarts.
    fn next_cycle(&self) -> usize {
        self.attempts.iter().map(|a| a.cycle).max().unwrap_or(0) + 1
    }
    /// The history of an earlier run, to continue: open again.
    fn resumed(mut self) -> OptimizeLog {
        self.finished = None;
        self.interrupted = false;
        self
    }
    pub fn summary_line(&self) -> String {
        format!(
            "optimize: {} → {} per iteration ({:.2}×), {} attempt(s), {} accepted, spent ~${:.2}{}",
            fmt_ns(self.baseline_ns),
            fmt_ns(self.current_ns),
            self.speedup(),
            self.attempts.len(),
            self.accepted,
            self.spent_usd,
            if self.interrupted { ", interrupted" } else { "" }
        )
    }
}

// ------------------------------------------------------------- frontier
//
// A multi-point workload (a compression level per point) is judged as lean-zip
// judges codecs: by the trade-off curve, not by any one point. Each point is
// (size, time); the achievable frontier is the lower convex hull — blending
// two adjacent points reaches every point on the segment between them — and
// a version is better when its frontier is nowhere above the old one and
// below it somewhere. Point labels carry no meaning: a level may change what
// it does, as long as the curve improves.

/// The lower-left convex hull of (size, time) points, sorted by size: the
/// trade-off curve, with dominated points dropped.
pub fn frontier(points: &[(f64, f64)]) -> Vec<(f64, f64)> {
    let mut ps: Vec<(f64, f64)> = points.iter().copied().filter(|p| p.0.is_finite() && p.1.is_finite()).collect();
    ps.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().then(a.1.partial_cmp(&b.1).unwrap()));
    // dominated: not strictly faster than a smaller-or-equal point
    let mut best = f64::INFINITY;
    let mut kept = Vec::new();
    for p in ps {
        if p.1 < best {
            best = p.1;
            kept.push(p);
        }
    }
    // lower hull (monotone chain)
    let cross = |o: (f64, f64), a: (f64, f64), b: (f64, f64)| (a.0 - o.0) * (b.1 - o.1) - (a.1 - o.1) * (b.0 - o.0);
    let mut hull: Vec<(f64, f64)> = Vec::new();
    for p in kept {
        while hull.len() >= 2 && cross(hull[hull.len() - 2], hull[hull.len() - 1], p) <= 0.0 {
            hull.pop();
        }
        hull.push(p);
    }
    hull
}

/// The frontier's time at a size: interpolated between vertices; its last
/// time beyond the largest size; `None` below the smallest (unreachable).
pub fn time_at(hull: &[(f64, f64)], size: f64) -> Option<f64> {
    let first = hull.first()?;
    if size < first.0 {
        return None;
    }
    for w in hull.windows(2) {
        if size <= w[1].0 {
            let t = if w[1].0 > w[0].0 { (size - w[0].0) / (w[1].0 - w[0].0) } else { 1.0 };
            return Some(w[0].1 + t * (w[1].1 - w[0].1));
        }
    }
    hull.last().map(|p| p.1)
}

/// The frontier's size at a time, by the same interpolation; `None` if no
/// point is that fast.
pub fn size_at(hull: &[(f64, f64)], time: f64) -> Option<f64> {
    let last = hull.last()?;
    if time < last.1 {
        return None;
    }
    for w in hull.windows(2) {
        if time >= w[1].1 {
            let t = if w[0].1 > w[1].1 { (w[0].1 - time) / (w[0].1 - w[1].1) } else { 0.0 };
            return Some(w[0].0 + t.clamp(0.0, 1.0) * (w[1].0 - w[0].0));
        }
    }
    hull.first().map(|p| p.0)
}

/// The verdict on a new measurement against the current one, by the frontier
/// rule: `Ok(improvement)` (the largest relative gain at a matched size or a
/// matched time, at least `required`), or `Err(why)`.
pub fn frontier_verdict(old: &Measurement, new: &Measurement, required: f64, size_required: f64) -> Result<f64, String> {
    let pts = |m: &Measurement| m.points.iter().map(|p| (p.size.unwrap_or(0) as f64, p.median_ns)).collect::<Vec<_>>();
    let (oh, nh) = (frontier(&pts(old)), frontier(&pts(new)));
    let (Some(of), Some(nf)) = (oh.first(), nh.first()) else { return Err("no points".into()) };
    if nf.0 > of.0 {
        return Err(format!("the densest point grew: {} → {} bytes (the frontier must still reach the old smallest size)", of.0, nf.0));
    }
    let mut best = f64::NEG_INFINITY;
    for &(s, t) in &oh {
        let nt = time_at(&nh, s).unwrap_or(f64::INFINITY);
        if nt > t * (1.0 + required) {
            return Err(format!("slower at size {}: {} → {} ({:+.1}%)", s, fmt_ns(t), fmt_ns(nt), (nt / t - 1.0) * 100.0));
        }
        best = best.max(1.0 - nt / t);
        if let Some(ns) = size_at(&nh, t) {
            // sizes are exact: a density gain needs only the threshold, not the noise
            let gain = 1.0 - ns / s;
            if gain >= size_required {
                best = best.max(gain.max(required));
            }
        }
    }
    // the new fastest point must not be slower than the old fastest
    if let (Some(ol), Some(nl)) = (oh.last(), nh.last()) {
        if nl.1 > ol.1 * (1.0 + required) {
            return Err(format!("the fastest point slowed: {} → {}", fmt_ns(ol.1), fmt_ns(nl.1)));
        }
    }
    if best >= required {
        Ok(best)
    } else {
        Err(format!("not better: best gain at a matched size or time {:+.1}%, needed {:.1}%", best * 100.0, required * 100.0))
    }
}

/// The verdict for independent points (`Measurement::independent_points`:
/// no sizes, or all equal — a frontier would collapse to the fastest point):
/// no point slower beyond its bar, and some point faster by at least its bar.
/// A point's bar is `threshold`, or the spread of its batches in either
/// measurement if larger (with `noisy`; without, the threshold alone).
pub fn points_verdict(old: &Measurement, new: &Measurement, threshold: f64, noisy: bool) -> Result<f64, String> {
    let mut best: Option<f64> = None;
    for op in &old.points {
        let Some(np) = new.points.iter().find(|p| p.id == op.id) else { return Err(format!("point {} is missing", op.id)) };
        let bar = if noisy { threshold.max(op.noise()).max(np.noise()) } else { threshold };
        let gain = 1.0 - np.median_ns / op.median_ns;
        if gain < -bar {
            return Err(format!("slower at point {}: {} → {} ({:+.1}%, allowed {:.1}%)", op.id, fmt_ns(op.median_ns), fmt_ns(np.median_ns), -gain * 100.0, bar * 100.0));
        }
        if gain >= bar {
            best = Some(best.map_or(gain, |b: f64| b.max(gain)));
        }
    }
    best.ok_or_else(|| "not faster beyond noise and threshold at any point".to_string())
}

/// The verdict on `new` against `current`: `Ok(improvement)` or `Err(why)`.
/// With `noisy`, the bar is the threshold or the batches' spread if larger;
/// without, the threshold alone (to tell a borderline result, which is
/// re-measured rather than rejected).
pub fn judge(current: &Measurement, new: &Measurement, threshold: f64, size_required: f64, noisy: bool) -> Result<f64, String> {
    if current.independent_points() && new.independent_points() {
        return points_verdict(current, new, threshold, noisy);
    }
    let required = if noisy { threshold.max(current.noise()).max(new.noise()) } else { threshold };
    if new.is_multi() {
        frontier_verdict(current, new, required, size_required)
    } else {
        let improvement = 1.0 - new.median_ns / current.median_ns;
        if improvement >= required {
            Ok(improvement)
        } else {
            Err(format!("not faster ({:+.1}%, needed {:.1}%)", improvement * 100.0, required * 100.0))
        }
    }
}

fn point_list(m: &Measurement) -> Vec<(u64, Option<u64>, f64)> {
    m.points.iter().map(|p| (p.id, p.size, p.median_ns)).collect()
}

#[cfg(test)]
mod frontier_tests {
    use super::*;
    use crate::bench::Point;
    fn m(pts: &[(u64, u64, f64)]) -> Measurement {
        let points: Vec<Point> = pts.iter().map(|&(id, size, ns)| Point { id, ns_per_iter: vec![ns], median_ns: ns, min_ns: ns, max_ns: ns, iters_per_batch: 1, size: Some(size) }).collect();
        Measurement { ns_per_iter: vec![], median_ns: points.iter().map(|p| p.median_ns).sum(), min_ns: 0.0, max_ns: 0.0, iters_per_batch: 1, total_secs: 0.0, points }
    }
    #[test]
    fn hull_drops_dominated() {
        let h = frontier(&[(100.0, 10.0), (90.0, 20.0), (95.0, 25.0), (80.0, 40.0)]);
        assert_eq!(h, vec![(80.0, 40.0), (90.0, 20.0), (100.0, 10.0)]);
    }
    #[test]
    fn faster_everywhere_is_accepted() {
        let old = m(&[(1, 100, 10.0), (2, 90, 20.0), (3, 80, 40.0)]);
        let new = m(&[(1, 100, 9.0), (2, 90, 18.0), (3, 80, 36.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).unwrap() > 0.09);
    }
    #[test]
    fn relabelled_levels_are_fine() {
        let old = m(&[(1, 100, 10.0), (2, 90, 20.0), (3, 80, 40.0)]);
        let new = m(&[(3, 100, 9.0), (1, 90, 18.0), (2, 80, 36.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_ok());
    }
    #[test]
    fn losing_density_is_rejected() {
        let old = m(&[(1, 100, 10.0), (2, 80, 40.0)]);
        let new = m(&[(1, 100, 5.0), (2, 85, 20.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_err());
    }
    #[test]
    fn slower_at_matched_size_is_rejected() {
        let old = m(&[(1, 100, 10.0), (2, 90, 20.0), (3, 80, 40.0)]);
        let new = m(&[(1, 100, 10.0), (2, 90, 30.0), (3, 80, 40.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_err());
    }
    #[test]
    fn denser_at_same_speed_is_accepted() {
        let old = m(&[(1, 100, 10.0), (2, 80, 40.0)]);
        let new = m(&[(1, 98, 10.0), (2, 78, 40.0)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_ok());
    }
    #[test]
    fn noise_level_change_is_rejected() {
        let old = m(&[(1, 100, 10.0), (2, 80, 40.0)]);
        let new = m(&[(1, 100, 9.9), (2, 80, 39.8)]);
        assert!(frontier_verdict(&old, &new, 0.03, 0.005).is_err());
    }
}

// ----------------------------------------------------------- checkpoints

fn checkpoint_dir(cfg: &Config) -> PathBuf {
    cfg.state_dir().join("optimize").join("checkpoint")
}

fn copy_tree(src: &Path, dst: &Path) -> Result<(), String> {
    if src.is_dir() {
        fs::create_dir_all(dst).map_err(|e| e.to_string())?;
        for e in fs::read_dir(src).map_err(|e| e.to_string())?.flatten() {
            copy_tree(&e.path(), &dst.join(e.file_name()))?;
        }
    } else {
        if let Some(p) = dst.parent() {
            fs::create_dir_all(p).map_err(|e| e.to_string())?;
        }
        fs::copy(src, dst).map_err(|e| format!("{}: {e}", src.display()))?;
    }
    Ok(())
}

/// Save the (verified) solution and proofs as the last known-good state.
fn checkpoint(cfg: &Config) -> Result<(), String> {
    let d = checkpoint_dir(cfg);
    let _ = fs::remove_dir_all(&d);
    copy_tree(&cfg.solution_dir(), &d.join("solution"))?;
    let proofs = cfg.lean_dir();
    copy_tree(&proofs.join("Proofs.lean"), &d.join("Proofs.lean"))?;
    if proofs.join("Proofs").is_dir() {
        copy_tree(&proofs.join("Proofs"), &d.join("Proofs"))?;
    }
    Ok(())
}

/// Do the solution and proofs match the last checkpoint?
fn same_as_checkpoint(cfg: &Config) -> bool {
    let d = checkpoint_dir(cfg);
    let proofs = cfg.lean_dir();
    same_tree(&cfg.solution_dir(), &d.join("solution")) && same_tree(&proofs.join("Proofs.lean"), &d.join("Proofs.lean")) && same_tree(&proofs.join("Proofs"), &d.join("Proofs"))
}

/// Two files or directory trees with the same names and contents (both
/// absent counts as the same).
fn same_tree(a: &Path, b: &Path) -> bool {
    match (a.is_dir(), b.is_dir()) {
        (true, true) => {
            let names = |p: &Path| -> Vec<std::ffi::OsString> {
                let mut v: Vec<_> = fs::read_dir(p).into_iter().flatten().flatten().map(|e| e.file_name()).collect();
                v.sort();
                v
            };
            let (na, nb) = (names(a), names(b));
            na == nb && na.iter().all(|n| same_tree(&a.join(n), &b.join(n)))
        }
        (false, false) => match (fs::read(a), fs::read(b)) {
            (Ok(x), Ok(y)) => x == y,
            (Err(_), Err(_)) => !a.exists() && !b.exists(),
            _ => false,
        },
        _ => false,
    }
}

/// Restore the last known-good state and re-run the verifier so the report
/// and the generated code match it again.
fn revert(cfg: &Config, why: &str) -> Result<(), String> {
    eprintln!("== reverting to the last known-good checkpoint ({why})");
    let d = checkpoint_dir(cfg);
    if !d.join("solution").exists() {
        return Err("no checkpoint to revert to".into());
    }
    let _ = fs::remove_dir_all(cfg.solution_dir());
    copy_tree(&d.join("solution"), &cfg.solution_dir())?;
    let proofs = cfg.lean_dir();
    copy_tree(&d.join("Proofs.lean"), &proofs.join("Proofs.lean"))?;
    let _ = fs::remove_dir_all(proofs.join("Proofs"));
    if d.join("Proofs").is_dir() {
        copy_tree(&d.join("Proofs"), &proofs.join("Proofs"))?;
    }
    let r = verify::verify(cfg, None, &mut Log::new(false));
    if !r.pass {
        return Err(format!("the restored checkpoint no longer verifies (stage {}) — this should not happen", r.stage));
    }
    Ok(())
}

// ------------------------------------------------------------------ prompt

fn prompt(cfg: &Config, opts: &OptOpts, current: &Measurement, log: &OptimizeLog, extra: Option<&str>) -> String {
    let (_, w) = bench::workload_path(cfg).unwrap_or_default();
    let source = bench::workload_source(cfg).unwrap_or_else(|| "(source not found)".into());
    let required = opts.threshold.max(current.noise());
    let size_required = size_threshold(opts);
    let mut p = format!(
        "You are the OPTIMIZER in a Djinn-on-Aeneas project. The implementation in `{sol}/` is \
already verified against the specification in `{spec}` (read-only). Your job is to make it {goal} on \
the performance workload below while keeping it verified. Nothing else counts.\n\n\
Read `GUIDE.md` (in this directory) first; the editing rules are the same as for implementing: edit only \
`{sol}/` and `{proofs}/{ns}/Proofs.lean` (helpers under `{proofs}/{ns}/Proofs/`). The specification, \
`Cargo.toml`, and the workload are read-only; edits to them are discarded.\n\n\
## The workload (`{w}`)\n\n```rust\n{source}\n```\n\n\
## Current timing\n\n{timing}\n\n\
## Acceptance\n\n\
Your version is kept only if (1) the `verify` tool prints PASS — so when you change the Rust, re-prove \
`impl_correct` for whatever changed (the Aeneas model of your new code appears in `{proofs}/{ns}/Code/` \
after a `verify`) — and (2) {rule} Otherwise your \
changes are reverted. Measure your jail copy with `./bench` (same method: release build, at least \
{min:.0} s of iterations per point){tableinfo}.\n\n\
Approach: profile mentally first — what dominates the workload? Prefer algorithmic improvements \
(better complexity, fewer passes, no redundant work) over micro-tuning; keep to safe Rust that Aeneas \
can model (index loops, scalars; see the guide's Rust section). A faster algorithm usually needs a new \
loop invariant: budget for the proof.\n\n\
When `verify` prints PASS and `./bench` shows a gain, stop. Your FINAL message must summarize exactly what \
you changed and why, and the timing you observed: it becomes the history shown to later attempts.\n",
        spec = cfg.specs_display(),
        ns = cfg.ns,
        sol = cfg.sol_rel(),
        proofs = cfg.proofs_rel(),
        goal = if current.independent_points() { "FASTER — at some point of the workload, and slower at none" } else if current.is_multi() { "BETTER — faster at every compression ratio, or denser at every speed" } else { "FASTER" },
        timing = if current.is_multi() { format!("{}\n\n```\n{}```", current.line(), current.table()) } else { current.line() },
        rule = if current.independent_points() {
            format!(
                "every point is judged on its own (the points' sizes do not trade off against time): no point \
runs more than {pct:.1}% slower (or its measured noise, if larger) and at least one point runs at least \
{pct:.1}% faster (or its noise, if larger) on a re-measurement by the harness ({thr:.0}% threshold).",
                pct = opts.threshold * 100.0,
                thr = opts.threshold * 100.0
            )
        } else if current.is_multi() {
            format!(
                "the trade-off curve improves, judged as lean-zip judges codecs: every point is (size, time); \
the achievable frontier is the lower convex hull of the points (mixing two adjacent points reaches the \
segment between them); your frontier must be nowhere above the current one — at every current size, your \
time at that size (interpolated) is not more than {pct:.1}% worse, the smallest size is still reached, the \
fastest point is not slower — and better somewhere: at least {pct:.1}% faster at some current size, or at \
least {spct:.1}% smaller at some current time. Sizes are exact; times carry noise ({thr:.0}% threshold, or \
the measured noise if larger). The point labels mean nothing to the rule: a level may change what it does, \
as long as the curve improves. Making a level faster by compressing less is accepted only if the curve as \
a whole does not suffer.",
                pct = required * 100.0,
                spct = size_required * 100.0,
                thr = opts.threshold * 100.0
            )
        } else {
            format!(
                "the workload runs at least {pct:.1}% faster than the current timing on a re-measurement by the \
harness ({thr:.0}% threshold, or the measured noise if larger).",
                pct = required * 100.0,
                thr = opts.threshold * 100.0
            )
        },
        tableinfo = if current.is_multi() { "; it prints the per-point table (size and time per point)" } else { "; it prints nanoseconds per workload iteration" },
        min = opts.min_time,
    );
    if log.cycles_done() > 0 {
        p.push_str("\n## Earlier attempts (do not repeat what failed)\n\n");
        for a in log.attempts.iter().filter(|a| a.verdict != API_ERROR_VERDICT) {
            let t = a.ns.map(|n| format!(" — measured {}", fmt_ns(n))).unwrap_or_default();
            p.push_str(&format!("- attempt {}: {}{}\n  tried: {}\n", a.cycle, a.verdict, t, a.summary.replace('\n', " ")));
        }
        p.push_str(&format!("\nBaseline before any attempt: {}.\n", fmt_ns(log.baseline_ns)));
    }
    if let Some(e) = extra {
        p.push_str("\nAdditional instructions from the human:\n");
        p.push_str(e);
        p.push('\n');
    }
    p
}

/// The relative size gain that counts as an improvement on its own: sizes are
/// exact, so a sixth of the time threshold (0.5% at the default 3%).
fn size_threshold(opts: &OptOpts) -> f64 {
    (opts.threshold / 6.0).max(0.001)
}

// -------------------------------------------------------------------- loop

/// Exit status: 0 some attempt (in this run or an earlier one of the same
/// history) was accepted, 1 none was, `EXIT_API_ERROR` the agent stopped on
/// an API error (a usage limit, say).
pub fn optimize(cfg: &Config, opts: OptOpts, bin: &Path) -> Result<u8, String> {
    crate::agent::ensure_no_running_job(cfg)?;
    bench::workload_path(cfg)?;
    if opts.cycles.is_none() && opts.agent.limit_usd.is_none() {
        return Err("give --cycles N and/or --limit USD".into());
    }
    let prev = OptimizeLog::load(cfg).map(OptimizeLog::resumed);
    if let Some(p) = &prev {
        eprintln!(
            "== optimize: resuming the history in {} — {} cycle(s) so far, {} accepted, {} → {}, spent ~${:.2}",
            cfg.rel(&OptimizeLog::path(cfg)),
            p.cycles_done(),
            p.accepted,
            fmt_ns(p.baseline_ns),
            fmt_ns(p.current_ns),
            p.spent_usd
        );
        if let Some(n) = opts.cycles {
            if p.cycles_done() >= n {
                eprintln!("== all {n} cycle(s) already ran (`--cycles` counts every run of this history): give a larger --cycles to continue");
                return Ok(if p.accepted > 0 { 0 } else { 1 });
            }
        }
        if let Some(limit) = opts.agent.limit_usd {
            if p.spent_usd >= limit {
                eprintln!("== spending limit already reached (${:.2} of ${limit:.2}, over every run of this history)", p.spent_usd);
                return Ok(if p.accepted > 0 { 0 } else { 1 });
            }
        }
    }
    // Ctrl-C: stop the agent, restore the checkpoint
    let stop = Arc::new(AtomicBool::new(false));
    {
        let stop = stop.clone();
        ctrlc::set_handler(move || {
            eprintln!("\n^C — finishing the current step, then reverting to the last known-good checkpoint");
            stop.store(true, Ordering::SeqCst);
        })
        .map_err(|e| format!("cannot install the Ctrl-C handler: {e}"))?;
    }
    let mut say = |s: &str| eprintln!("{s}");

    // 1. the gate
    eprintln!("== optimize: confirming the implementation and proofs");
    let r = verify::verify(cfg, None, &mut Log::new(false));
    if !r.pass {
        return Err(format!("nothing to optimize: verify FAILs at {} — run `cargo djinn implement` first", r.stage));
    }
    if prev.is_some() && checkpoint_dir(cfg).join("solution").exists() && !same_as_checkpoint(cfg) {
        eprintln!("note: the solution or proofs differ from the last checkpoint (a cycle cut short, or a manual edit); continuing from the crate as it is — it verifies");
    }
    checkpoint(cfg)?;
    // 2. baseline (resuming: the current state, re-measured; the history
    // keeps the original baseline)
    let measured = bench::measure(cfg, opts.min_time, opts.batches, opts.jobs, &mut say)?;
    let mut log = match prev {
        Some(mut p) => {
            p.current_ns = measured.median_ns;
            p.current_points = point_list(&measured);
            p
        }
        None => OptimizeLog {
            started: now(),
            baseline_ns: measured.median_ns,
            current_ns: measured.median_ns,
            baseline_points: point_list(&measured),
            current_points: point_list(&measured),
            ..Default::default()
        },
    };
    log.save(cfg);
    let mut current = measured;
    eprintln!("{}: {}", if log.attempts.is_empty() { "baseline" } else { "current (re-measured)" }, current.line());

    let mut api_stop = false;
    loop {
        if stop.load(Ordering::SeqCst) {
            log.interrupted = true;
            break;
        }
        if let Some(n) = opts.cycles {
            if log.cycles_done() >= n {
                break;
            }
        }
        if let Some(limit) = opts.agent.limit_usd {
            if log.spent_usd >= limit {
                eprintln!("== spending limit reached (${:.2} of ${limit:.2})", log.spent_usd);
                break;
            }
        }
        let cycle = log.next_cycle();
        eprintln!("\n== cycle {cycle}{}: current {}", opts.cycles.map(|n| format!(" ({} of {n})", log.cycles_done() + 1)).unwrap_or_default(), fmt_ns(current.median_ns));
        let mut agent_opts = Opts {
            agent: opts.agent.agent,
            model: opts.agent.model.clone(),
            yolo: opts.agent.yolo,
            background: false,
            extra_prompt: None,
            max_budget_usd: None,
            effort: opts.agent.effort.clone(),
            extra_args: opts.agent.extra_args.clone(),
            limit_usd: opts.agent.limit_usd.map(|l| (l - log.spent_usd).max(0.5)),
            from_scratch: false,
        };
        if agent_opts.limit_usd.is_some() {
            agent_opts.max_budget_usd = agent_opts.limit_usd.map(|l| format!("{l:.2}"));
        }
        let text = prompt(cfg, &opts, &current, &log, opts.agent.extra_prompt.as_deref());
        let run = agent::run_foreground(cfg, &agent_opts, &text, bin, &stop, &format!("opt{cycle}"))?;
        let cost = run.usage.cost_usd.or(run.usage.est_cost_usd);
        log.spent_usd += cost.unwrap_or(0.0);
        let mut attempt = Attempt {
            cycle,
            job: run.job.id.clone(),
            verdict: String::new(),
            ns: None,
            points: Vec::new(),
            summary: run.usage.last_message.chars().take(1200).collect(),
            cost_usd: cost,
            cost_is_estimate: run.usage.cost_usd.is_none(),
            tokens_in: run.usage.input_tokens,
            tokens_out: run.usage.output_tokens,
            elapsed_secs: status::job_elapsed(&run.job),
        };
        if run.interrupted {
            attempt.verdict = "interrupted".into();
            log.attempts.push(attempt);
            log.interrupted = true;
            log.save(cfg);
            revert(cfg, "interrupted")?;
            break;
        }
        // an API error (a usage limit, say): every further cycle would end the
        // same way. The text stays visible for wrappers that retry on it.
        if let Some(e) = &run.usage.api_error {
            eprintln!("cycle {cycle}: the agent stopped on an API error: {e}");
            attempt.verdict = API_ERROR_VERDICT.into();
            log.attempts.push(attempt);
            log.save(cfg);
            revert(cfg, "the agent stopped on an API error")?;
            api_stop = true;
            break;
        }
        // (1) it must verify, with the agent's files synced from its jail
        let r = verify::verify(cfg, Some(&run.job.jail), &mut Log::new(false));
        if !r.pass {
            attempt.verdict = format!("did not verify (stage: {})", r.stage);
            eprintln!("cycle {cycle}: {}", attempt.verdict);
            log.attempts.push(attempt);
            log.save(cfg);
            revert(cfg, "verification failed")?;
            continue;
        }
        // (2) it must be better beyond noise and threshold: faster, for a
        // multi-point workload a better trade-off curve, for independent
        // points faster somewhere and slower nowhere
        let mut m = bench::measure(cfg, opts.min_time, opts.batches, opts.jobs, &mut say)?;
        let mut verdict = judge(&current, &m, opts.threshold, size_threshold(&opts), true);
        if verdict.is_err() && judge(&current, &m, opts.threshold, size_threshold(&opts), false).is_ok() {
            // better than the threshold, not than the noise: measure again,
            // longer, instead of rejecting a gain that load blurred
            eprintln!("cycle {cycle}: borderline ({}) — re-measuring with twice the batches", verdict.as_ref().unwrap_err());
            m = bench::measure(cfg, opts.min_time * 2.0, opts.batches * 2, opts.jobs, &mut say)?;
            verdict = judge(&current, &m, opts.threshold, size_threshold(&opts), true);
        }
        attempt.ns = Some(m.median_ns);
        attempt.points = point_list(&m);
        match verdict {
            Ok(improvement) => {
                attempt.verdict = format!("accepted ({:.1}% better)", improvement * 100.0);
                eprintln!("cycle {cycle}: ACCEPTED — {} → {} ({:.1}% better)", fmt_ns(current.median_ns), fmt_ns(m.median_ns), improvement * 100.0);
                current = m;
                log.current_ns = current.median_ns;
                log.current_points = point_list(&current);
                log.accepted += 1;
                log.attempts.push(attempt);
                log.save(cfg);
                checkpoint(cfg)?;
            }
            Err(why) => {
                attempt.verdict = why;
                eprintln!("cycle {cycle}: {} — reverting", attempt.verdict);
                log.attempts.push(attempt);
                log.save(cfg);
                revert(cfg, "not better")?;
            }
        }
    }
    log.finished = Some(now());
    log.save(cfg);
    // report
    eprintln!("\n{:<6} {:<34} {:>12} {:>9} {:>10} {:>8}", "cycle", "verdict", "time/iter", "speedup", "cost", "wall");
    for a in &log.attempts {
        eprintln!(
            "{:<6} {:<34} {:>12} {:>9} {:>10} {:>8}",
            a.cycle,
            a.verdict.chars().take(34).collect::<String>(),
            a.ns.map(fmt_ns).unwrap_or("—".into()),
            a.ns.map(|n| format!("{:.2}×", log.baseline_ns / n)).unwrap_or("—".into()),
            a.cost_usd.map(|c| format!("{}${c:.2}", if a.cost_is_estimate { "~" } else { "" })).unwrap_or("n/a".into()),
            format!("{}m{:02}s", a.elapsed_secs / 60, a.elapsed_secs % 60)
        );
    }
    eprintln!("{}", log.summary_line());
    if api_stop {
        eprintln!("optimize: stopped because the agent hit an API error (see above); run again to resume this history");
        return Ok(EXIT_API_ERROR);
    }
    Ok(if log.accepted > 0 { 0 } else { 1 })
}

#[cfg(test)]
mod resume_tests {
    use super::*;
    fn attempt(cycle: usize, verdict: &str) -> Attempt {
        Attempt { cycle, job: String::new(), verdict: verdict.into(), ns: None, points: vec![], summary: String::new(), cost_usd: Some(1.0), cost_is_estimate: false, tokens_in: 0, tokens_out: 0, elapsed_secs: 0 }
    }

    #[test]
    fn a_restart_continues_the_history() {
        let log = OptimizeLog {
            started: 1,
            finished: Some(2),
            baseline_ns: 100.0,
            current_ns: 80.0,
            attempts: vec![attempt(1, "accepted (20.0% better)"), attempt(2, "not faster (+1.0%, needed 3.0%)"), attempt(3, API_ERROR_VERDICT)],
            accepted: 1,
            spent_usd: 3.0,
            interrupted: true,
            ..Default::default()
        };
        // through the file, as a restarted run sees it
        let back: OptimizeLog = serde_json::from_str(&serde_json::to_string(&log).unwrap()).unwrap();
        let r = back.resumed();
        assert_eq!((r.finished, r.interrupted), (None, false));
        assert_eq!((r.baseline_ns, r.accepted, r.spent_usd), (100.0, 1, 3.0));
        // the API-error cycle does not count toward --cycles; numbering goes on
        assert_eq!(r.cycles_done(), 2);
        assert_eq!(r.next_cycle(), 4);
        assert_eq!(OptimizeLog::default().next_cycle(), 1);
    }

    #[test]
    fn a_usage_limit_is_an_api_error() {
        let dir = std::env::temp_dir().join(format!("djinn-opt-test-{}", std::process::id()));
        let _ = fs::create_dir_all(&dir);
        let log = dir.join("agent.log");
        fs::write(&log, "{\"type\":\"result\",\"subtype\":\"success\",\"is_error\":true,\"result\":\"You've hit your limit · resets 3pm\",\"total_cost_usd\":0}\n").unwrap();
        let u = status::summarize_log(&log, None);
        assert_eq!(u.api_error.as_deref(), Some("You've hit your limit · resets 3pm"));
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn trees_compare_by_content() {
        let dir = std::env::temp_dir().join(format!("djinn-opt-tree-{}", std::process::id()));
        let (a, b) = (dir.join("a"), dir.join("b"));
        for d in [&a, &b] {
            fs::create_dir_all(d.join("sub")).unwrap();
            fs::write(d.join("sub").join("f.rs"), "x").unwrap();
        }
        assert!(same_tree(&a, &b));
        assert!(same_tree(&dir.join("none1"), &dir.join("none2")));
        fs::write(b.join("sub").join("f.rs"), "y").unwrap();
        assert!(!same_tree(&a, &b));
        fs::write(b.join("sub").join("f.rs"), "x").unwrap();
        fs::write(b.join("g.rs"), "").unwrap();
        assert!(!same_tree(&a, &b));
        let _ = fs::remove_dir_all(&dir);
    }
}

#[cfg(test)]
mod verdict_tests {
    use super::*;
    use crate::bench::Point;
    /// points (id, size, batch timings)
    fn m(pts: &[(u64, Option<u64>, &[f64])]) -> Measurement {
        let points: Vec<Point> = pts
            .iter()
            .map(|&(id, size, ns)| {
                let mut s = ns.to_vec();
                s.sort_by(|a, b| a.partial_cmp(b).unwrap());
                Point { id, ns_per_iter: ns.to_vec(), median_ns: s[s.len() / 2], min_ns: s[0], max_ns: s[s.len() - 1], iters_per_batch: 1, size }
            })
            .collect();
        Measurement { ns_per_iter: vec![], median_ns: points.iter().map(|p| p.median_ns).sum(), min_ns: 0.0, max_ns: 0.0, iters_per_batch: 1, total_secs: 0.0, points }
    }

    #[test]
    fn equal_sizes_judge_every_point() {
        // the frontier of equal sizes is the fastest point alone: a slower
        // other point must still reject
        let old = m(&[(1, Some(0), &[10.0; 5]), (2, Some(0), &[100.0; 5])]);
        let new = m(&[(1, Some(0), &[8.0; 5]), (2, Some(0), &[150.0; 5])]);
        assert!(old.independent_points());
        assert!(judge(&old, &new, 0.03, 0.005, true).unwrap_err().contains("slower at point 2"));
        let new = m(&[(1, None, &[8.0; 5]), (2, None, &[100.5; 5])]);
        let old = m(&[(1, None, &[10.0; 5]), (2, None, &[100.0; 5])]);
        assert!((judge(&old, &new, 0.03, 0.005, true).unwrap() - 0.2).abs() < 1e-9);
        // nothing faster beyond the threshold
        let new = m(&[(1, None, &[9.9; 5]), (2, None, &[99.0; 5])]);
        assert!(judge(&old, &new, 0.03, 0.005, true).is_err());
    }

    #[test]
    fn one_disturbed_batch_does_not_raise_the_bar() {
        // a 20% gain; one batch of five slowed 3x by load
        let old = m(&[(1, None, &[100.0, 101.0, 99.0, 300.0, 100.0])]);
        let new = m(&[(1, None, &[80.0, 81.0, 79.0, 80.0, 250.0])]);
        assert!(old.noise() < 0.05, "{}", old.noise());
        assert!(judge(&old, &new, 0.03, 0.005, true).is_ok());
        // a plain workload likewise
        let single = |ns: &[f64]| Measurement { ns_per_iter: ns.to_vec(), median_ns: { let mut s = ns.to_vec(); s.sort_by(|a, b| a.partial_cmp(b).unwrap()); s[s.len() / 2] }, min_ns: 0.0, max_ns: 0.0, iters_per_batch: 1, total_secs: 0.0, points: vec![] };
        assert!(judge(&single(&[100.0, 101.0, 99.0, 300.0, 100.0]), &single(&[80.0, 81.0, 79.0, 80.0, 250.0]), 0.03, 0.005, true).is_ok());
    }

    #[test]
    fn a_borderline_result_is_told_apart() {
        // 10% faster, but the batches spread 20%: rejected with the noise,
        // accepted on the threshold alone — so it is re-measured
        let old = m(&[(1, None, &[100.0; 5])]);
        let new = m(&[(1, None, &[80.0, 85.0, 90.0, 100.0, 105.0])]);
        assert!(judge(&old, &new, 0.03, 0.005, true).is_err());
        assert!(judge(&old, &new, 0.03, 0.005, false).is_ok());
    }

    #[test]
    fn sized_points_keep_the_frontier_rule() {
        let old = m(&[(1, Some(100), &[10.0; 5]), (2, Some(80), &[40.0; 5])]);
        assert!(!old.independent_points());
        let new = m(&[(1, Some(100), &[9.0; 5]), (2, Some(80), &[36.0; 5])]);
        assert!(judge(&old, &new, 0.03, 0.005, true).is_ok());
    }
}
