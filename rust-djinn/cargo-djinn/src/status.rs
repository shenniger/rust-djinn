//! `cargo djinn status`: declarations implemented and proved, and the
//! background agent jobs.

use crate::config::*;
use crate::verify::Report;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Job {
    pub id: String,
    pub agent: String,
    pub pid: u32,
    pub started: u64,
    pub jail: PathBuf,
    pub log: PathBuf,
    pub background: bool,
    #[serde(default)]
    pub model: Option<String>,
    #[serde(default)]
    pub limit_usd: Option<f64>,
}

/// USD per million tokens: (input, cached input, output). List prices as of
/// the writing; override with `[package.metadata.djinn.prices]` in Cargo.toml,
/// e.g. `"claude-opus" = [15.0, 1.5, 75.0]` (matched as a substring).
pub fn price(model: &str) -> Option<(f64, f64, f64)> {
    let m = model.to_lowercase();
    let table: &[(&str, (f64, f64, f64))] = &[
        ("haiku", (1.0, 0.1, 5.0)),
        ("sonnet", (3.0, 0.3, 15.0)),
        ("opus", (15.0, 1.5, 75.0)),
        ("fable", (15.0, 1.5, 75.0)),
        ("gpt-5-mini", (0.25, 0.025, 2.0)),
        ("gpt-5-nano", (0.05, 0.005, 0.4)),
        ("gpt-5", (1.25, 0.125, 10.0)),
        ("o3", (2.0, 0.5, 8.0)),
        ("codex", (1.25, 0.125, 10.0)),
    ];
    if let Some(over) = price_overrides() {
        for (k, v) in over {
            if m.contains(&k.to_lowercase()) {
                return Some(v);
            }
        }
    }
    if let Some(v) = table.iter().find(|(k, _)| m.contains(k)).map(|(_, v)| *v) {
        return Some(v);
    }
    // unknown model: price it as the family's flagship (shown as approximate)
    if m.contains("gpt") || m.starts_with('o') {
        Some((1.25, 0.125, 10.0))
    } else if m.contains("claude") {
        Some((15.0, 1.5, 75.0))
    } else {
        None
    }
}

/// Whether the model has an entry in the table (as opposed to the family fallback).
pub fn price_known(model: &str) -> bool {
    let m = model.to_lowercase();
    ["haiku", "sonnet", "opus", "fable", "gpt-5", "o3", "codex"].iter().any(|k| m.contains(k))
        || price_overrides().map(|o| o.iter().any(|(k, _)| m.contains(&k.to_lowercase()))).unwrap_or(false)
}

fn price_overrides() -> Option<Vec<(String, (f64, f64, f64))>> {
    let text = fs::read_to_string("Cargo.toml").ok()?;
    let doc: toml::Value = toml::from_str(&text).ok()?;
    let t = doc.get("package")?.get("metadata")?.get("djinn")?.get("prices")?.as_table()?;
    Some(
        t.iter()
            .filter_map(|(k, v)| {
                let a = v.as_array()?;
                Some((k.clone(), (a.first()?.as_float()?, a.get(1)?.as_float()?, a.get(2)?.as_float()?)))
            })
            .collect(),
    )
}

pub fn jobs_dir(cfg: &Config) -> PathBuf {
    cfg.state_dir().join("jobs")
}

pub fn save_job(cfg: &Config, job: &Job) -> Result<(), String> {
    fs::create_dir_all(jobs_dir(cfg)).map_err(|e| e.to_string())?;
    fs::write(jobs_dir(cfg).join(format!("{}.json", job.id)), serde_json::to_string_pretty(job).unwrap()).map_err(|e| e.to_string())
}

pub fn load_jobs(cfg: &Config) -> Vec<Job> {
    let mut v: Vec<Job> = fs::read_dir(jobs_dir(cfg))
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|e| fs::read_to_string(e.path()).ok())
        .filter_map(|t| serde_json::from_str(&t).ok())
        .collect();
    v.sort_by_key(|j| j.started);
    v
}

pub enum JobState {
    Running,
    Finished(i32),
    Gone,
}

pub fn job_state(job: &Job) -> JobState {
    if let Ok(code) = fs::read_to_string(job.jail.join("exit-code")) {
        let c = code.trim();
        return JobState::Finished(if c == "limit" || c == "interrupted" || c == "driver-died" { 0 } else { c.parse().unwrap_or(-1) });
    }
    let alive = Command::new("kill").args(["-0", &job.pid.to_string()]).output().map(|o| o.status.success()).unwrap_or(false);
    if alive {
        JobState::Running
    } else {
        JobState::Gone
    }
}

/// What an agent run cost, from its JSON log.
#[derive(Default, Clone, Debug)]
pub struct Usage {
    pub tool_calls: usize,
    pub verifies: usize,
    pub turns: usize,
    pub input_tokens: u64,
    pub cached_tokens: u64,
    pub output_tokens: u64,
    /// Reported by the agent CLI (Claude Code's `total_cost_usd`); `None` for Codex.
    pub cost_usd: Option<f64>,
    /// Estimated from the token counts and the price table, when the model is known.
    pub est_cost_usd: Option<f64>,
    /// The estimate used a family fallback price because the model is not in the table.
    pub est_approx: bool,
    pub model: Option<String>,
    pub last_message: String,
    /// The API error a Claude run ended on (a usage limit, say): the text of
    /// the last `result` that carried `api_error` or `is_error`.
    pub api_error: Option<String>,
    /// The agent reached the end of its turn (Claude's `result`, Codex's
    /// `turn.completed`); false for a log cut short by a signal or a crash.
    pub ended_turn: bool,
}

impl Usage {
    pub fn line(&self) -> String {
        format!(
            "tokens in {} (cached {}) / out {}, cost {}, tool calls {}, verifies {}",
            self.input_tokens,
            self.cached_tokens,
            self.output_tokens,
            match (self.cost_usd, self.est_cost_usd) {
                (Some(c), _) => format!("${c:.2}"),
                (None, Some(e)) => format!("est.{} ${e:.2}", if self.est_approx { "≈" } else { "" }),
                (None, None) => "n/a".into(),
            },
            self.tool_calls,
            self.verifies
        )
    }
}

/// Usage and the last assistant text, from an agent log. `model_hint` is the
/// model given on the command line (Codex logs do not name the model).
pub fn summarize_log(path: &PathBuf, model_hint: Option<&str>) -> Usage {
    let mut u = Usage::default();
    u.model = model_hint.map(|s| s.to_string());
    let Ok(text) = fs::read_to_string(path) else { return u };
    let verifies = &mut u.verifies;
    let tool_calls = &mut u.tool_calls;
    let last = &mut u.last_message;
    // per-message usage, summed while a Claude run is still going
    let (mut acc_in, mut acc_cached, mut acc_out) = (0u64, 0u64, 0u64);
    let mut have_result = false;
    let mut codex_thread: Option<String> = None;
    for line in text.lines() {
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else { continue };
        if v["type"] == "thread.started" {
            if let Some(t) = v["thread_id"].as_str() {
                codex_thread = Some(t.to_string());
            }
        }
        // Claude Code stream-json
        if v["type"] == "system" && v["subtype"] == "init" {
            if let Some(m) = v["model"].as_str() {
                u.model = Some(m.to_string());
            }
            // a new run (a resumed session appends to the same log): an
            // earlier run's API error is history
            u.api_error = None;
        }
        if v["type"] == "assistant" {
            if let Some(m) = v["message"]["model"].as_str() {
                u.model = Some(m.to_string());
            }
            let us = &v["message"]["usage"];
            acc_in += us["input_tokens"].as_u64().unwrap_or(0)
                + us["cache_read_input_tokens"].as_u64().unwrap_or(0)
                + us["cache_creation_input_tokens"].as_u64().unwrap_or(0);
            acc_cached += us["cache_read_input_tokens"].as_u64().unwrap_or(0);
            acc_out += us["output_tokens"].as_u64().unwrap_or(0);
            for c in v["message"]["content"].as_array().into_iter().flatten() {
                if c["type"] == "tool_use" {
                    *tool_calls += 1;
                    let n = c["name"].as_str().unwrap_or("");
                    if n.contains("verify") || c["input"]["command"].as_str().map(|s| s.contains("verify")).unwrap_or(false) {
                        *verifies += 1;
                    }
                } else if c["type"] == "text" {
                    if let Some(t) = c["text"].as_str() {
                        *last = t.to_string();
                    }
                }
            }
        }
        if v["type"] == "result" {
            u.ended_turn = true;
            have_result = true;
            // a run can end on several results (one per background task that
            // finished late): an empty one must not hide the text, the error or
            // the usage of an earlier one
            let text = v["result"].as_str().unwrap_or("");
            if !text.is_empty() {
                *last = text.to_string();
            }
            if (!v["api_error"].is_null() || v["is_error"] == true) && !text.is_empty() {
                u.api_error = Some(text.to_string());
            } else if !text.is_empty() {
                // a later result that succeeded: the run recovered
                u.api_error = None;
            }
            if let Some(c) = v["total_cost_usd"].as_f64() {
                if c > 0.0 || u.cost_usd.is_none() {
                    u.cost_usd = Some(c);
                }
            }
            if let Some(n) = v["num_turns"].as_u64() {
                if n > 0 {
                    u.turns = n as usize;
                }
            }
            let us = &v["usage"];
            let input = us["input_tokens"].as_u64().unwrap_or(0) + us["cache_read_input_tokens"].as_u64().unwrap_or(0) + us["cache_creation_input_tokens"].as_u64().unwrap_or(0);
            if input > 0 {
                u.input_tokens = input;
                u.cached_tokens = us["cache_read_input_tokens"].as_u64().unwrap_or(0);
                u.output_tokens = us["output_tokens"].as_u64().unwrap_or(0);
            }
        }
        // Codex JSONL
        if v["type"] == "item.completed" || v["type"] == "item.started" {
            let it = &v["item"];
            match it["type"].as_str().unwrap_or("") {
                "mcp_tool_call" | "command_execution" => {
                    if v["type"] == "item.completed" {
                        *tool_calls += 1;
                        // the tool's name or the command line — not its output,
                        // which mentions `verify` whenever the guide is read
                        let name = it["tool"].as_str().or_else(|| it["name"].as_str()).unwrap_or("");
                        let cmd = it["command"].as_str().unwrap_or("");
                        if name.contains("verify") || cmd.contains("verify") {
                            *verifies += 1;
                        }
                    }
                }
                "agent_message" => {
                    if let Some(t) = it["text"].as_str() {
                        *last = t.to_string();
                    }
                }
                _ => {}
            }
        }
        if v["type"] == "turn.completed" {
            u.ended_turn = true;
            u.turns += 1;
            let us = &v["usage"];
            u.input_tokens += us["input_tokens"].as_u64().unwrap_or(0);
            u.cached_tokens += us["cached_input_tokens"].as_u64().unwrap_or(0);
            u.output_tokens += us["output_tokens"].as_u64().unwrap_or(0);
        }
    }
    if !have_result && u.input_tokens == 0 && acc_in > 0 {
        u.input_tokens = acc_in;
        u.cached_tokens = acc_cached;
        u.output_tokens = acc_out;
    }
    if let Some(t) = &codex_thread {
        if let Some((i, c, o, m)) = codex_rollout_usage(t) {
            if i >= u.input_tokens {
                u.input_tokens = i;
                u.cached_tokens = c;
                u.output_tokens = o;
            }
            if u.model.is_none() {
                u.model = m;
            }
        }
    }
    let model = u.model.clone().unwrap_or_else(|| if path.to_string_lossy().contains("codex") { "gpt-5".into() } else { String::new() });
    if let Some((pi, pc, po)) = price(&model) {
        let uncached = u.input_tokens.saturating_sub(u.cached_tokens) as f64;
        u.est_cost_usd = Some((uncached * pi + u.cached_tokens as f64 * pc + u.output_tokens as f64 * po) / 1e6);
        u.est_approx = !price_known(&model);
    }
    u
}

/// Live usage from Codex's own rollout log (`~/.codex/sessions/**/rollout-*-<thread>.jsonl`),
/// which records cumulative token counts after every model response — unlike
/// the `--json` stream, which reports usage only when a turn completes.
fn codex_rollout_usage(thread_id: &str) -> Option<(u64, u64, u64, Option<String>)> {
    let home = std::env::var("HOME").ok()?;
    let root = PathBuf::from(home).join(".codex").join("sessions");
    fn find(dir: &Path, needle: &str, depth: usize) -> Option<PathBuf> {
        for e in fs::read_dir(dir).ok()?.flatten() {
            let p = e.path();
            if p.is_dir() {
                if depth < 4 {
                    if let Some(f) = find(&p, needle, depth + 1) {
                        return Some(f);
                    }
                }
            } else if p.file_name().map(|n| n.to_string_lossy().contains(needle)).unwrap_or(false) {
                return Some(p);
            }
        }
        None
    }
    let file = find(&root, thread_id, 0)?;
    let text = fs::read_to_string(file).ok()?;
    let mut totals = None;
    let mut model = None;
    for line in text.lines() {
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else { continue };
        let p = &v["payload"];
        if v["type"] == "turn_context" {
            if let Some(m) = p["model"].as_str() {
                model = Some(m.to_string());
            }
        }
        if v["type"] == "event_msg" && p["type"] == "token_count" {
            let t = &p["info"]["total_token_usage"];
            if t.is_object() {
                totals = Some((
                    t["input_tokens"].as_u64().unwrap_or(0),
                    t["cached_input_tokens"].as_u64().unwrap_or(0),
                    t["output_tokens"].as_u64().unwrap_or(0),
                ));
            }
        }
    }
    let (i, c, o) = totals?;
    Some((i, c, o, model))
}

/// Wall-clock seconds of a job: from its start to its end file, or to now.
pub fn job_elapsed(job: &Job) -> u64 {
    let end = fs::read_to_string(job.jail.join("ended")).ok().and_then(|t| t.trim().parse::<u64>().ok()).unwrap_or_else(now);
    end.saturating_sub(job.started)
}

/// What we know about one obligation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ObState {
    /// proved and audited by the last `verify`
    Verified,
    /// elaborates without errors or `sorry` in a local type-check (not yet verified)
    Local,
    /// a theorem exists but has errors or a `sorry`
    Drafted,
    /// no theorem of that name
    Missing,
    Unknown,
}

impl ObState {
    fn sym(self) -> &'static str {
        match self {
            ObState::Verified => "✓",
            ObState::Local => "✓·",
            ObState::Drafted => "~",
            ObState::Missing => "–",
            ObState::Unknown => "?",
        }
    }
}

/// Type-check a `Proofs.lean` and classify every theorem in it.
/// Returns `None` if Lean could not be run.
pub fn local_states(ns: &str, proofs: &Path, timeout_secs: u64) -> Option<std::collections::HashMap<String, ObState>> {
    let file = proofs.join(ns).join("Proofs.lean");
    let text = fs::read_to_string(&file).ok()?;
    // theorem name → (first line, last line), 1-based
    let mut spans: Vec<(String, usize, usize)> = Vec::new();
    let starts_decl = |l: &str| {
        let t = l.trim_start();
        !l.starts_with(' ') && (t.starts_with("theorem ") || t.starts_with("def ") || t.starts_with("lemma ") || t.starts_with("@[") || t.starts_with("end ") || t.starts_with("namespace ") || t.starts_with("instance ") || t.starts_with("abbrev "))
    };
    let lines: Vec<&str> = text.lines().collect();
    for (i, l) in lines.iter().enumerate() {
        if let Some(rest) = l.strip_prefix("theorem ") {
            let name: String = rest.trim_start().chars().take_while(|c| !c.is_whitespace() && *c != ':').collect();
            let mut end = lines.len();
            for (j, m) in lines.iter().enumerate().skip(i + 1) {
                if starts_decl(m) {
                    end = j;
                    break;
                }
            }
            spans.push((name, i + 1, end));
        }
    }
    let mut child = Command::new("lake")
        .args(["env", "lean"])
        .arg(format!("{ns}/Proofs.lean"))
        .current_dir(proofs)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .ok()?;
    let start = std::time::Instant::now();
    let out = loop {
        if let Ok(Some(_)) = child.try_wait() {
            break child.wait_with_output().ok()?;
        }
        if start.elapsed().as_secs() > timeout_secs {
            let _ = child.kill();
            return None;
        }
        std::thread::sleep(std::time::Duration::from_millis(300));
    };
    let output = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    let mut bad_lines: Vec<usize> = Vec::new();
    for l in output.lines() {
        // <path>:<line>:<col>: error: … | warning: declaration uses 'sorry'
        if l.contains(": error") || l.contains("declaration uses 'sorry'") || l.contains("declaration uses `sorry`") {
            let mut parts = l.splitn(4, ':');
            let _file = parts.next();
            if let Some(n) = parts.next().and_then(|x| x.trim().parse::<usize>().ok()) {
                bad_lines.push(n);
            }
        }
    }
    let mut m = std::collections::HashMap::new();
    for (name, a, b) in spans {
        let body = lines[a - 1..b].join("\n");
        let has_sorry = body.contains("sorry");
        let has_err = bad_lines.iter().any(|&n| n >= a && n <= b);
        m.insert(name, if has_sorry || has_err { ObState::Drafted } else { ObState::Local });
    }
    Some(m)
}

#[derive(Clone, Debug)]
pub struct DeclView {
    pub name: String,
    pub kind: String,
    pub implemented: bool,
    /// (short obligation name, state)
    pub obs: Vec<(String, ObState)>,
    /// the specification of this declaration (or of something it uses) changed
    /// semantically since the last verify: verified states are stale
    pub changed: bool,
    /// `#[weakly_specified]`: the implementer made choices here — review them
    pub weak: bool,
}

impl DeclView {
    pub fn get(&self, short: &str) -> ObState {
        self.obs.iter().find(|(n, _)| n == short).map(|(_, s)| *s).unwrap_or(ObState::Unknown)
    }
    pub fn all_verified(&self) -> bool {
        !self.obs.is_empty() && self.obs.iter().all(|(_, s)| *s == ObState::Verified)
    }
    pub fn phase(&self) -> String {
        if self.changed {
            return "CHANGED since verification — re-run verify".into();
        }
        let ok = |s: ObState| matches!(s, ObState::Verified | ObState::Local);
        if self.kind == "ambient" {
            return "trusted Rust of the specification file (not verified)".into();
        }
        if self.kind == "rel" {
            // a rel is never implemented, so there is nothing to verify: it
            // only owes proofs (wf, ensures, exists of a total rel), if any
            return if self.obs.is_empty() {
                "nothing to prove".into()
            } else if self.all_verified() {
                "ok".into()
            } else if self.obs.iter().all(|(_, s)| ok(*s)) {
                "proved locally (verify not run yet)".into()
            } else {
                "proving".into()
            };
        }
        let un = self.get("unambiguous");
        let ic = self.get("impl_correct");
        if !ok(un) {
            "proving unambiguity".into()
        } else if !self.implemented {
            "unambiguous; no implementation yet".into()
        } else if self.all_verified() {
            "ok".into()
        } else if ok(ic) {
            "impl drafted, proofs check locally (not yet verified)".into()
        } else {
            "impl drafted, impl_correct pending".into()
        }
    }
    pub fn line(&self) -> String {
        let sym = |s: ObState| if self.changed && s == ObState::Verified { "✓?" } else { s.sym() };
        let others: Vec<String> = self
            .obs
            .iter()
            .filter(|(n, _)| n != "unambiguous" && n != "impl_correct")
            .map(|(n, s)| format!("{n} {}", sym(*s)))
            .collect();
        if self.kind == "rel" || self.kind == "ambient" {
            return format!("  {:4} {:16} [{}]   → {}\n", self.kind, self.name, others.join(", "), self.phase());
        }
        format!(
            "  {:4} {:16} unambiguous {:3} impl {:9} impl_correct {:3} [{}]   → {}{}\n",
            self.kind,
            self.name,
            sym(self.get("unambiguous")),
            if self.implemented { "drafted" } else { "–" },
            if self.obs.iter().any(|(n, _)| n == "impl_correct") { sym(self.get("impl_correct")) } else { "–" },
            others.join(", "),
            self.phase(),
            if self.weak { "  (weakly specified — review the choices)" } else { "" }
        )
    }
}

/// Declaration views from the last verify report, optionally overlaid with
/// a local assessment (a solution directory and a type-checked Proofs.lean).
pub fn views(cfg: &Config, report: Option<&Report>, local: Option<(&Path, &Path)>) -> Vec<DeclView> {
    let texts: Vec<String> = cfg.spec_texts().unwrap_or_default().into_iter().map(|(_, t)| t).collect();
    views_text(cfg, report, local, &texts)
}

/// Like `views`, comparing the report against given specification texts
/// (with the editor's buffer in place of its file) to detect semantic
/// changes since the last verify.
pub fn views_text(cfg: &Config, report: Option<&Report>, local: Option<(&Path, &Path)>, spec_texts: &[String]) -> Vec<DeclView> {
    let current: HashMap<String, djinn_syntax::project::Entry> = djinn_syntax::project::index_texts(spec_texts).into_iter().map(|e| (e.name.clone(), e)).collect();
    let recorded: HashMap<String, djinn_syntax::project::Entry> = report
        .map(|r| {
            r.declarations
                .iter()
                .map(|d| {
                    (d.name.clone(), djinn_syntax::project::Entry { name: d.name.clone(), kind: d.kind.clone(), tokens: d.tokens.clone(), uses: d.uses.clone() })
                })
                .collect()
        })
        .unwrap_or_default();
    let decls: Vec<crate::verify::DeclStatus> = match report {
        Some(r) if local.is_none() => r.declarations.clone(),
        _ => match crate::verify::lower_spec(cfg) {
            Ok(l) => crate::verify::decl_statuses(cfg, &l, &crate::verify::impl_names(cfg)),
            Err(_) => report.map(|r| r.declarations.clone()).unwrap_or_default(),
        },
    };
    let local_fns = local.map(|(sol, _)| crate::verify::solution_fns_in(sol));
    let local_obs = local.and_then(|(_, proofs)| local_states(&cfg.ns, proofs, 180));
    decls
        .into_iter()
        .map(|d| {
            let implemented = match &local_fns {
                Some(f) => d.kind == "rel" || f.contains(&d.name),
                None => d.implemented,
            };
            let obs: Vec<(String, ObState)> = d
                .obligations
                .iter()
                .map(|o| {
                    let short = o.rsplit('.').next().unwrap_or(o).to_string();
                    let verified = report.and_then(|r| r.obligations.get(o)).map(|v| v == "proved").unwrap_or(false);
                    let st = match &local_obs {
                        Some(m) => match m.get(o) {
                            Some(ObState::Local) if verified => ObState::Verified,
                            Some(s) => *s,
                            None => ObState::Missing,
                        },
                        None => {
                            if verified {
                                ObState::Verified
                            } else {
                                match report.and_then(|r| r.obligations.get(o)).map(|s| s.as_str()) {
                                    Some("sorry") | Some("error") => ObState::Drafted,
                                    Some(_) => ObState::Unknown,
                                    None => ObState::Unknown,
                                }
                            }
                        }
                    };
                    (short, st)
                })
                .collect();
            // a func's `exists` is proved by the generator from `impl_correct`
            let obs = if d.kind == "func" {
                let ic = obs.iter().find(|(n, _)| n == "impl_correct").map(|(_, s)| *s).unwrap_or(ObState::Unknown);
                obs.into_iter().map(|(n, s)| if n == "exists" && local_obs.is_some() { (n, ic) } else { (n, s) }).collect()
            } else {
                obs
            };
            // changed since the report: its tokens, or a used declaration's,
            // differ (the same test the `djinn!` macro applies)
            let changed = report.is_some()
                && current.contains_key(&d.name)
                && (!recorded.contains_key(&d.name) || djinn_syntax::project::stale(&d.name, &recorded, &current).is_some());
            DeclView { name: d.name, kind: d.kind, implemented, obs, changed, weak: d.weak }
        })
        .collect()
}

pub fn render(views: &[DeclView]) -> String {
    let mut s = String::new();
    for v in views {
        s.push_str(&v.line());
    }
    let funcs = views.iter().filter(|v| v.kind == "func").count();
    let done = views.iter().filter(|v| v.kind == "func" && v.implemented && v.all_verified() && !v.changed).count();
    s.push_str(&format!("  funcs implemented and fully verified: {done}/{funcs}\n"));
    s
}

/// A report's verdict as `cargo djinn verify` prints it: `PASS`, `FAIL`, or —
/// every obligation proved but some `fn` without an implementation, which the
/// build gate still refuses — `SPECIFICATION VERIFIED`.
pub fn verdict(r: &Report) -> String {
    let missing = r.unimplemented();
    if !r.pass {
        "FAIL".into()
    } else if missing.is_empty() {
        "PASS".into()
    } else {
        format!("SPECIFICATION VERIFIED (not implemented yet: {})", missing.join(", "))
    }
}

/// The solution and proof files on disk against the report's fingerprint
/// (what the build gate checks).
pub fn evidence_check(cfg: &Config, r: &Report) -> djinn_syntax::project::EvidenceCheck {
    let current = djinn_syntax::project::evidence(&cfg.crate_dir, &cfg.solution_dir(), &cfg.proofs, &cfg.ns);
    djinn_syntax::project::check_evidence(&r.evidence, &current)
}

pub fn status_text(cfg: &Config) -> String {
    let mut s = String::new();
    let report = Report::load(cfg);
    s.push_str(&format!("{} ({})\n", cfg.crate_name, cfg.specs_display()));
    s.push_str("legend: ✓ ok (accepted by verify)   ✓· checks locally, not yet verified   ~ drafted (sorry or error)   – missing   ✓? verified before a change\n");
    match &report {
        Some(r) => {
            s.push_str(&format!(
                "verified state — last verify {} at {} UTC ({} s){}:\n",
                verdict(r),
                fmt_time(r.time),
                r.duration_secs,
                if r.pass { String::new() } else { format!(", stage: {}", r.stage) }
            ));
            if let Some(m) = evidence_check(cfg, r).message() {
                s.push_str(&format!("  {m}\n"));
            }
            s.push_str(&render(&views(cfg, Some(r), None)));
            for e in r.errors.iter().take(6) {
                s.push_str(&format!("    {e}\n"));
            }
        }
        None => {
            s.push_str("verified state: none yet (run `cargo djinn verify`); local assessment of the crate:\n");
            s.push_str(&render(&views(cfg, None, Some((&cfg.solution_dir(), &cfg.proofs)))));
        }
    }
    if let Some(o) = crate::optimize::OptimizeLog::load(cfg) {
        s.push_str(&format!("{}\n", o.summary_line()));
    }
    let jobs = load_jobs(cfg);
    if jobs.is_empty() {
        s.push_str("agent jobs: none\n");
        return s;
    }
    s.push_str("agent jobs:\n");
    for j in &jobs {
        let state = match job_state(j) {
            JobState::Running => "running".to_string(),
            JobState::Finished(0) if fs::read_to_string(j.jail.join("exit-code")).map(|t| t.trim() == "limit").unwrap_or(false) => "stopped by the spending limit".to_string(),
            JobState::Finished(0) if fs::read_to_string(j.jail.join("exit-code")).map(|t| t.trim() == "interrupted").unwrap_or(false) => "interrupted (Ctrl-C)".to_string(),
            JobState::Finished(0) if fs::read_to_string(j.jail.join("exit-code")).map(|t| t.trim() == "driver-died").unwrap_or(false) => "stopped by the watchdog (the driver died)".to_string(),
            JobState::Finished(0) if !summarize_log(&j.log, j.model.as_deref()).ended_turn => "exited WITHOUT finishing its turn (signal, crash or CLI error)".to_string(),
            JobState::Finished(0) => "finished".to_string(),
            JobState::Finished(c) => format!("finished (exit {c})"),
            JobState::Gone => "gone (no exit code; killed?)".to_string(),
        };
        let u = summarize_log(&j.log, j.model.as_deref());
        let el = job_elapsed(j);
        s.push_str(&format!(
            "  {}  {}  {}  pid {}  started {} UTC  elapsed {}m{:02}s{}\n    {}{}\n    jail: {}\n",
            j.id,
            j.agent,
            state,
            j.pid,
            fmt_time(j.started),
            el / 60,
            el % 60,
            match j.limit_usd {
                Some(l) => format!("  limit ${l:.2}"),
                None => String::new(),
            },
            u.line(),
            match &u.model {
                Some(m) if !m.is_empty() => format!(", model {m}"),
                _ => String::new(),
            },
            j.jail.display(),
        ));
        if !u.last_message.is_empty() {
            let one: String = u.last_message.lines().collect::<Vec<_>>().join(" ");
            let short: String = one.chars().take(220).collect();
            s.push_str(&format!("    last message: {short}{}\n", if one.chars().count() > 220 { "…" } else { "" }));
        }
        if matches!(job_state(j), JobState::Running) && crate::jail::proofs_in(cfg, &j.jail).exists() {
            s.push_str("    current work in the jail (type-checked just now):\n");
            let v = views(cfg, report.as_ref(), Some((&crate::jail::sol_in(cfg, &j.jail), &crate::jail::proofs_in(cfg, &j.jail))));
            for line in render(&v).lines() {
                s.push_str(&format!("  {line}\n"));
            }
        }
    }
    s
}

/// Human name of an obligation for progress messages.
pub fn ob_label(short: &str) -> String {
    match short {
        "unambiguous" => "unambiguity proof".into(),
        "impl_correct" => "implementation-correctness proof".into(),
        "wf" => "well-formedness proof".into(),
        "exists" => "existence proof".into(),
        s if s.starts_with("ens_") => format!("ensures-clause {} proof", &s[4..]),
        s => format!("{s} proof"),
    }
}

/// What changed between two snapshots, as progress lines.
pub fn diff_views(old: &[DeclView], new: &[DeclView]) -> Vec<String> {
    let mut out = Vec::new();
    for n in new {
        let o = old.iter().find(|d| d.name == n.name);
        let was_impl = o.map(|d| d.implemented).unwrap_or(false);
        if n.implemented && !was_impl && n.kind == "func" {
            out.push(format!("{}: implementation drafted", n.name));
        }
        for (ob, st) in &n.obs {
            let prev = o.and_then(|d| d.obs.iter().find(|(x, _)| x == ob)).map(|(_, s)| *s).unwrap_or(ObState::Missing);
            if prev == *st {
                continue;
            }
            let label = ob_label(ob);
            let msg = match (prev, *st) {
                (_, ObState::Verified) => format!("{}: {label} ok", n.name),
                (_, ObState::Local) => format!("{}: {label} now passing (local check, not yet verified)", n.name),
                (ObState::Missing | ObState::Unknown, ObState::Drafted) => format!("{}: {label} drafted (sorry or errors remain)", n.name),
                (ObState::Local | ObState::Verified, ObState::Drafted) => format!("{}: {label} BROKEN (errors or sorry)", n.name),
                (_, ObState::Missing) => format!("{}: {label} removed", n.name),
                _ => continue,
            };
            out.push(msg);
        }
        if let Some(o) = o {
            if o.phase() != n.phase() {
                out.push(format!("{}: → {}", n.name, n.phase()));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn api_error_cleared_by_a_later_run() {
        let dir = std::env::temp_dir().join(format!("djinn-status-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let log = dir.join("log.jsonl");
        let failed = r#"{"type":"system","subtype":"init","model":"claude-x"}
{"type":"result","result":"usage limit reached","is_error":true}"#;
        fs::write(&log, failed).unwrap();
        assert_eq!(summarize_log(&log, None).api_error.as_deref(), Some("usage limit reached"));
        // resumed in the same log and finished
        fs::write(&log, format!("{failed}\n{}", r#"{"type":"system","subtype":"init","model":"claude-x"}
{"type":"result","result":"done","is_error":false}"#)).unwrap();
        assert_eq!(summarize_log(&log, None).api_error, None);
        // an empty late result keeps the error
        fs::write(&log, format!("{failed}\n{}", r#"{"type":"result","result":""}"#)).unwrap();
        assert_eq!(summarize_log(&log, None).api_error.as_deref(), Some("usage limit reached"));
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn spec_only_verdict() {
        let d = |name: &str, implemented: bool| crate::verify::DeclStatus { name: name.into(), kind: "func".into(), implemented, obligations: vec![], tokens: String::new(), uses: vec![], ok: implemented, weak: false };
        let mut r = Report { time: 0, duration_secs: 0, pass: true, stage: "done".into(), obligations: Default::default(), declarations: vec![d("f", true), d("g", false)], errors: vec![], log_tail: vec![], evidence: String::new() };
        assert_eq!(verdict(&r), "SPECIFICATION VERIFIED (not implemented yet: g)");
        r.declarations.pop();
        assert_eq!(verdict(&r), "PASS");
        r.pass = false;
        assert_eq!(verdict(&r), "FAIL");
    }
}
