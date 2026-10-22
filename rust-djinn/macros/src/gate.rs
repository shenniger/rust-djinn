//! The compile-time gate: a `fn` of the specification compiles only if the
//! verifier's report (`<work_dir>/report.toml`) says it is implemented and
//! every obligation of it and of what it uses is proved, and if its tokens
//! (and those of what it uses) are the ones that were verified. Otherwise
//! the expansion carries a `compile_error!` at the function's name.
//!
//! Exempt: the verifier's own build (`DJINN_VERIFYING`), builds inside a
//! jail (`in_jail` in the crate metadata), Clippy (`CLIPPY_ARGS`), and
//! anything run with `DJINN_GATE=off` (the shipped rust-analyzer configs).

use djinn_syntax::project::{index, stale, Entry};
use djinn_syntax::{Decl, Kind};
use quote::{quote, quote_spanned};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

pub(crate) struct Project {
    /// The specification files (see `djinn_syntax::project::spec_files`).
    pub(crate) specs: Vec<PathBuf>,
    pub(crate) solution: PathBuf,
    /// The crate directory, the Lean project and the namespace: where the
    /// proof files the report's fingerprint covers live.
    dir: PathBuf,
    proofs: PathBuf,
    ns: String,
    report: PathBuf,
    report_rel: String,
    in_jail: bool,
}

pub(crate) fn project() -> Option<Project> {
    let dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").ok()?);
    let text = fs::read_to_string(dir.join("Cargo.toml")).ok()?;
    let toml: toml::Value = toml::from_str(&text).ok()?;
    let meta = toml.get("package").and_then(|p| p.get("metadata")).and_then(|m| m.get("djinn")).cloned().unwrap_or(toml::Value::Table(Default::default()));
    let get = |k: &str| meta.get(k).and_then(|v| v.as_str()).map(|s| s.to_string());
    let work = get("work_dir").unwrap_or_else(|| "djinn".into());
    let manual: Option<Vec<String>> = match meta.get("spec") {
        Some(toml::Value::String(p)) => Some(vec![p.clone()]),
        Some(toml::Value::Array(a)) => Some(a.iter().filter_map(|x| x.as_str().map(|s| s.to_string())).collect()),
        _ => None,
    };
    let proofs = match get("proofs") {
        Some(p) => dir.join(p),
        None => dir.join(&work).join("proofs"),
    };
    let name = toml.get("package").and_then(|p| p.get("name")).and_then(|v| v.as_str()).unwrap_or_default();
    let ns = djinn_syntax::project::namespace(get("namespace").as_deref(), name);
    Some(Project {
        proofs,
        ns,
        dir: dir.clone(),
        specs: djinn_syntax::project::spec_files(&dir, manual.as_deref()).into_iter().map(|f| f.path).collect(),
        solution: dir.join(&work).join("solution"),
        report: dir.join(&work).join("report.toml"),
        report_rel: format!("{work}/report.toml"),
        in_jail: meta.get("in_jail").and_then(|v| v.as_bool()).unwrap_or(false),
    })
}

impl Project {
    /// The specification files' texts (`None` if one cannot be read).
    pub(crate) fn texts(&self) -> Option<Vec<String>> {
        self.specs.iter().map(|p| fs::read_to_string(p).ok()).collect()
    }
}

fn gate_off(p: &Project) -> bool {
    let off = |k: &str| std::env::var(k).map(|v| matches!(v.as_str(), "off" | "0" | "false")).unwrap_or(false);
    p.in_jail || off("DJINN_GATE") || std::env::var_os("DJINN_VERIFYING").is_some() || std::env::var_os("CLIPPY_ARGS").is_some()
}

/// The report's entries, and per declaration its `ok` verdict with the
/// reasons it is not ok.
fn read_report(p: &Project) -> Option<(HashMap<String, Entry>, HashMap<String, (bool, Vec<String>)>)> {
    let text = fs::read_to_string(&p.report).ok()?;
    let v: toml::Value = toml::from_str(&text).ok()?;
    let mut entries = HashMap::new();
    let mut verdicts = HashMap::new();
    let evidence = v.get("run").and_then(|r| r.get("evidence")).and_then(|x| x.as_str()).unwrap_or("").to_string();
    verdicts.insert(EVIDENCE.to_string(), (true, vec![evidence]));
    for d in v.get("decl").and_then(|d| d.as_array()).into_iter().flatten() {
        let name = d.get("name").and_then(|x| x.as_str()).unwrap_or("").to_string();
        let kind = d.get("kind").and_then(|x| x.as_str()).unwrap_or("func").to_string();
        let tokens = d.get("tokens").and_then(|x| x.as_str()).unwrap_or("").to_string();
        let uses: Vec<String> = d.get("uses").and_then(|x| x.as_array()).into_iter().flatten().filter_map(|x| x.as_str().map(|s| s.to_string())).collect();
        let ok = d.get("ok").and_then(|x| x.as_bool()).unwrap_or(false);
        let implemented = d.get("implemented").and_then(|x| x.as_bool()).unwrap_or(false);
        let mut problems = Vec::new();
        if !implemented {
            problems.push("not implemented".to_string());
        }
        if let Some(obs) = d.get("obligations").and_then(|x| x.as_table()) {
            let mut keys: Vec<&String> = obs.keys().collect();
            keys.sort();
            for k in keys {
                let st = obs[k].as_str().unwrap_or("?");
                if st != "proved" {
                    problems.push(format!("{name}.{k}: {st}"));
                }
            }
        }
        entries.insert(name.clone(), Entry { name: name.clone(), kind, tokens, uses });
        verdicts.insert(name, (ok, problems));
    }
    Some((entries, verdicts))
}

/// The verdicts map's entry for the report's fingerprint (no declaration has this name).
const EVIDENCE: &str = " evidence";

/// Tokens to prepend to a block's expansion: dependency trackers, and one
/// `compile_error!` per `fn` that may not be compiled.
pub fn check(decls: &[Decl], project: Option<&Project>) -> proc_macro2::TokenStream {
    let mut out = proc_macro2::TokenStream::new();
    // Charon's rustc pass (`CHARON_*` in its environment) must see only the
    // stubs: the trackers below would become Lean constants holding the whole
    // report as a byte array. Charon's build is fingerprinted separately
    // (it runs through a rustc wrapper), so omitting them there is safe.
    if std::env::vars_os().any(|(k, _)| k.to_string_lossy().starts_with("CHARON_")) {
        return out;
    }
    let Some(p) = project else { return out };
    // cargo re-expands when these change: the report, and the gate's environment
    if p.report.exists() {
        let path = p.report.to_string_lossy().into_owned();
        out.extend(quote! { const _: &[u8] = include_bytes!(#path); });
    }
    out.extend(quote! {
        const _: (Option<&str>, Option<&str>, Option<&str>) = (option_env!("DJINN_GATE"), option_env!("DJINN_VERIFYING"), option_env!("CLIPPY_ARGS"));
    });
    // and when a solution or proof file changes — every file the fingerprint
    // covers, not only the modules rustc reads (a stray or backup file counts
    // too). A file added without any tracked file changing is seen at the
    // next rebuild; `cargo djinn status` and the editor see it at once.
    let evidence = djinn_syntax::project::evidence(&p.dir, &p.solution, &p.proofs, &p.ns);
    for f in evidence.iter().flat_map(|e| e.files.iter()) {
        let path = f.to_string_lossy().into_owned();
        out.extend(quote! { const _: &[u8] = include_bytes!(#path); });
    }
    if gate_off(p) {
        return out;
    }
    let report = read_report(p);
    // the solution and proof files must be the ones the report's verify checked
    let changed: Option<String> = report.as_ref().and_then(|(_, v)| {
        let recorded = v.get(EVIDENCE).and_then(|(_, e)| e.first()).map(|e| e.as_str()).unwrap_or("");
        match djinn_syntax::project::check_evidence(recorded, &evidence) {
            djinn_syntax::project::EvidenceCheck::Same => None,
            djinn_syntax::project::EvidenceCheck::Unrecorded => Some(format!("no evidence fingerprint recorded in {}: run `cargo djinn verify`", p.report_rel)),
            djinn_syntax::project::EvidenceCheck::Outdated => Some(format!("the evidence fingerprint in {} is of an older `cargo djinn`: run `cargo djinn verify`", p.report_rel)),
            djinn_syntax::project::EvidenceCheck::Changed(d) => {
                let which = if d.is_empty() { String::new() } else { format!(": {}", d.iter().take(8).cloned().collect::<Vec<_>>().join(", ") + if d.len() > 8 { ", …" } else { "" }) };
                Some(format!("the solution or proof files changed since the last `cargo djinn verify` ({} records what was verified){which}; run `cargo djinn verify` (an editor backup or other stray file counts: delete it)", p.report_rel))
            }
            djinn_syntax::project::EvidenceCheck::Invalid(e) => Some(format!("the solution or proof files cannot be fingerprinted: {e}")),
        }
    });
    // the current declarations: the whole specification when it parses
    // (a used declaration may live in another block), else this block
    let current: HashMap<String, Entry> = {
        let all = p.texts().map(|t| djinn_syntax::project::index_texts(&t)).unwrap_or_default();
        let v = if all.is_empty() { index(decls) } else { all };
        v.into_iter().map(|e| (e.name.clone(), e)).collect()
    };
    // implementations of functions the specification no longer declares: live,
    // unverifiable code until `translate` archives them — unless other solution
    // code calls them (then they are helpers of verified functions)
    if let Some((entries, _)) = &report {
        let implemented = djinn_syntax::project::solution_fns_in(&p.solution);
        let mut orphans: Vec<String> = entries
            .iter()
            .filter(|(n, e)| e.kind == "func" && !current.contains_key(*n))
            .map(|(n, _)| n.clone())
            .filter(|f| implemented.contains(f) && !djinn_syntax::project::rust_fn_referenced(&p.solution, f))
            .collect();
        orphans.sort();
        for n in orphans {
            let msg = format!("djinn: `solution::{n}` implements a function the specification no longer declares, so nothing verifies it; run `cargo djinn translate` to archive it");
            out.extend(quote! { compile_error!(#msg); });
        }
    }
    for d in decls.iter().filter(|d| d.kind == Kind::Func) {
        let name = &d.name;
        let word = d.kind.word();
        let msg = match &report {
            None => format!("djinn {word} `{name}`: the crate has not been verified (no {}); run `cargo djinn implement`", p.report_rel),
            Some((entries, verdicts)) => match verdicts.get(name) {
                None => format!("djinn {word} `{name}` was never attempted (not in {}); run `cargo djinn implement`", p.report_rel),
                Some((ok, problems)) => {
                    if let Some(which) = stale(name, entries, &current) {
                        if &which == name {
                            format!("djinn {word} `{name}` changed since it was verified; run `cargo djinn implement`")
                        } else {
                            format!("djinn {word} `{name}` uses `{which}`, which changed since `{name}` was verified; run `cargo djinn implement`")
                        }
                    } else if let (true, Some(why)) = (*ok, &changed) {
                        format!("djinn {word} `{name}`: {why}")
                    } else if *ok {
                        continue;
                    } else {
                        // own problems, then those of the declarations it uses
                        let uses_map: HashMap<String, Vec<String>> = entries.iter().map(|(k, e)| (k.clone(), e.uses.clone())).collect();
                        let mut all = problems.clone();
                        for u in djinn_syntax::project::closure(name, &[&uses_map]).iter().skip(1) {
                            if let Some((_, ps)) = verdicts.get(u) {
                                all.extend(ps.iter().filter(|x| *x != "not implemented").cloned());
                            }
                        }
                        if all.is_empty() {
                            all.push("not verified".into());
                        }
                        format!("djinn {word} `{name}` is not verified ({}); run `cargo djinn implement`", all.join(", "))
                    }
                }
            },
        };
        out.extend(quote_spanned! { d.name_span => compile_error!(#msg); });
    }
    out
}
