//! `translate` and `verify`, producing a machine-readable report.

use crate::config::*;
use crate::jail;
use djinn_syntax::emit::{self, EmitCx};
use djinn_syntax::lower::Lowered;
use djinn_syntax::project::SpecFile;
use djinn_syntax::types::TypeNames;
use djinn_syntax::project::Backend;
use djinn_syntax::{Kind, Program};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::Path;
use std::process::Command;


/// Collects the verifier's output; echoes to stderr when running from a terminal.
pub struct Log {
    pub text: String,
    pub echo: bool,
}

impl Log {
    pub fn new(echo: bool) -> Self {
        Log { text: String::new(), echo }
    }
    pub fn line(&mut self, s: &str) {
        if self.echo {
            eprintln!("{s}");
        }
        self.text.push_str(s);
        self.text.push('\n');
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct DeclStatus {
    pub name: String,
    pub kind: String,
    pub implemented: bool,
    /// Full obligation names (`f.unambiguous`, …).
    pub obligations: Vec<String>,
    /// The declaration's tokens as verified (canonical text, see `project::canonical`).
    pub tokens: String,
    /// Declarations it mentions.
    pub uses: Vec<String>,
    /// Implemented (if a func) and every obligation of it and of what it uses proved.
    pub ok: bool,
    /// `#[weakly_specified]`: leaves choices to the implementer (or inherits
    /// them from a callee) — flagged for human review.
    #[serde(default)]
    pub weak: bool,
}

pub use djinn_syntax::project::solution_fns_in;

/// Names of functions defined in the crate's solution directory.
pub fn solution_fns(cfg: &Config) -> Vec<String> {
    solution_fns_in(&cfg.solution_dir())
}

/// The report file as written: `[run]` plus one `[[decl]]` per declaration.
#[derive(Serialize, Deserialize)]
struct ReportFile {
    run: RunEntry,
    #[serde(default)]
    decl: Vec<DeclEntry>,
}

#[derive(Serialize, Deserialize)]
struct RunEntry {
    time: String,
    unix_time: u64,
    duration_secs: u64,
    pass: bool,
    stage: String,
    #[serde(default)]
    errors: Vec<String>,
    /// The fingerprint of the solution and proof files verified (see
    /// `djinn_syntax::project::evidence`): the build gate refuses the crate
    /// when the files on disk no longer match it.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    evidence: String,
    /// The verifier the proofs are for (`lean`, `verus`); absent in reports
    /// written before backends existed (Lean).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    backend: String,
}

#[derive(Serialize, Deserialize)]
struct DeclEntry {
    name: String,
    kind: String,
    implemented: bool,
    ok: bool,
    uses: Vec<String>,
    tokens: String,
    /// short obligation name → status
    obligations: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    weakly_specified: bool,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Report {
    pub time: u64,
    pub duration_secs: u64,
    pub pass: bool,
    /// The stage that failed, or "done".
    pub stage: String,
    /// obligation name → proved | sorry | axiom:<name> | error | unverified
    pub obligations: BTreeMap<String, String>,
    pub declarations: Vec<DeclStatus>,
    pub errors: Vec<String>,
    pub log_tail: Vec<String>,
    /// The fingerprint of the solution and proof files this verify checked.
    pub evidence: String,
    /// The backend that wrote the report.
    #[serde(skip)]
    pub backend: Backend,
}

impl Report {
    /// `<work_dir>/report.toml` (Lean) or `<verus_dir>/report.toml` (Verus):
    /// next to the solution and proofs it certifies; committed with them. The
    /// `djinn!` macro reads it.
    pub fn path(cfg: &Config) -> std::path::PathBuf {
        cfg.report_path()
    }
    pub fn log_path(cfg: &Config) -> std::path::PathBuf {
        cfg.state_dir().join("verify.log")
    }
    pub fn load(cfg: &Config) -> Option<Report> {
        let t = fs::read_to_string(Report::path(cfg)).ok()?;
        let f: ReportFile = toml::from_str(&t).ok()?;
        let mut obligations = BTreeMap::new();
        let mut declarations = Vec::new();
        for d in f.decl {
            let mut names = Vec::new();
            for (short, st) in d.obligations {
                let full = format!("{}.{short}", d.name);
                obligations.insert(full.clone(), st);
                names.push(full);
            }
            declarations.push(DeclStatus { name: d.name, kind: d.kind, implemented: d.implemented, obligations: names, tokens: d.tokens, uses: d.uses, ok: d.ok, weak: d.weakly_specified });
        }
        let log_tail = fs::read_to_string(Report::log_path(cfg)).map(|t| t.lines().map(|s| s.to_string()).collect()).unwrap_or_default();
        let backend = Backend::parse(&f.run.backend).unwrap_or(Backend::Lean);
        Some(Report { time: f.run.unix_time, duration_secs: f.run.duration_secs, pass: f.run.pass, stage: f.run.stage, obligations, declarations, errors: f.run.errors, log_tail, evidence: f.run.evidence, backend })
    }
    /// Decide `ok` per declaration: implemented (funcs), and every obligation
    /// of it and of the declarations it uses, transitively, proved.
    pub fn finalize(&mut self) {
        let uses: HashMap<String, Vec<String>> = self.declarations.iter().map(|d| (d.name.clone(), d.uses.clone())).collect();
        let by_name: HashMap<String, DeclStatus> = self.declarations.iter().map(|d| (d.name.clone(), d.clone())).collect();
        let proved = |d: &DeclStatus| d.obligations.iter().all(|o| self.obligations.get(o).map(|s| s == "proved").unwrap_or(false));
        let oks: Vec<bool> = self
            .declarations
            .iter()
            .map(|d| d.implemented && djinn_syntax::project::closure(&d.name, &[&uses]).iter().all(|n| by_name.get(n).map(|x| proved(x)).unwrap_or(false)))
            .collect();
        for (d, ok) in self.declarations.iter_mut().zip(oks) {
            // an ambient function of the Verus backend is right when its mirror
            // verifies against its translation, which only a passing run shows
            d.ok = if d.kind == "ambient" && self.backend == Backend::Verus { self.pass } else { ok };
        }
    }
    pub fn save(&self, cfg: &Config) {
        let _ = fs::create_dir_all(cfg.state_dir());
        let _ = fs::create_dir_all(&cfg.work_dir);
        let decl = self
            .declarations
            .iter()
            .map(|d| DeclEntry {
                name: d.name.clone(),
                kind: d.kind.clone(),
                implemented: d.implemented,
                ok: d.ok,
                uses: d.uses.clone(),
                tokens: d.tokens.clone(),
                obligations: d
                    .obligations
                    .iter()
                    .map(|o| (o.rsplit('.').next().unwrap_or(o).to_string(), self.obligations.get(o).cloned().unwrap_or_else(|| "unverified".into())))
                    .collect(),
                weakly_specified: d.weak,
            })
            .collect();
        let f = ReportFile {
            run: RunEntry { time: format!("{} UTC", fmt_time(self.time)), unix_time: self.time, duration_secs: self.duration_secs, pass: self.pass, stage: self.stage.clone(), errors: self.errors.clone(), evidence: self.evidence.clone(), backend: self.backend.name().to_string() },
            decl,
        };
        if let Ok(s) = toml::to_string_pretty(&f) {
            let header = "# Written by `cargo djinn` after every verify. Per declaration: its tokens as\n# verified, what it uses, and the status of each obligation. The `djinn!`\n# macro refuses to compile a `fn` that is not `ok` here or whose tokens (or a\n# used declaration's) differ from this file, and the whole crate when the\n# solution or proof files differ from `run.evidence` (edit them, verify again).\n# Commit it with solution/ and proofs/.\n\n";
            let _ = fs::write(Report::path(cfg), format!("{header}{s}"));
        }
        let _ = fs::write(Report::log_path(cfg), self.log_tail.join("\n"));
    }
    /// The `fn`s of the specification without an implementation.
    pub fn unimplemented(&self) -> Vec<String> {
        self.declarations.iter().filter(|d| d.kind == "func" && !d.implemented).map(|d| d.name.clone()).collect()
    }
    /// One-paragraph summary for humans and agents.
    pub fn summary(&self) -> String {
        let mut s = String::new();
        let missing = self.unimplemented();
        if self.pass && !missing.is_empty() {
            // the specification's obligations hold, but the crate does not build:
            // a `fn` without an implementation has no `impl_correct` yet
            s.push_str(&format!("PASS (specification only): every obligation so far is proved, but {} fn(s) are not implemented: {}. `cargo djinn implement` continues from here.\n", missing.len(), missing.join(", ")));
        } else if self.pass && self.backend == Backend::Verus {
            s.push_str("PASS: every obligation is proved (Verus verified the whole project with no cheating).\n");
        } else if self.pass {
            s.push_str("PASS: every obligation is proved and the axiom audit is clean.\n");
        } else {
            s.push_str(&format!("FAIL at stage: {}\n", self.stage));
        }
        let proved = self.obligations.values().filter(|v| v.as_str() == "proved").count();
        s.push_str(&format!("obligations proved: {proved}/{}\n", self.obligations.len()));
        for (k, v) in &self.obligations {
            if v != "proved" {
                s.push_str(&format!("  {k}: {v}\n"));
            }
        }
        if !self.errors.is_empty() {
            s.push_str("errors:\n");
            for e in self.errors.iter().take(30) {
                s.push_str(&format!("  {e}\n"));
            }
        }
        s
    }
}

pub(crate) fn fail_at(cfg: &Config, e: djinn_syntax::Error) -> String {
    let s = e.span.start();
    let file = cfg.specs().get(e.file).map(|f| f.path.display().to_string()).unwrap_or_else(|| cfg.specs_display());
    format!("{file}:{}:{}: error: {}", s.line, s.column + 1, e.msg)
}

/// The Rust module (`a::b`; `None` at the crate root) of a name of the
/// specification: the module of the file defining it.
pub fn module_of(specs: &[SpecFile], prog: &Program, name: &str) -> Option<String> {
    prog.origin.get(name).and_then(|&i| specs.get(i)).and_then(|f| f.module.clone())
}

/// Rust name → Lean name, from Aeneas's `translation.json` when present,
/// otherwise predicted from the module the stubs live in.
pub fn impl_names(cfg: &Config) -> HashMap<String, String> {
    if cfg.is_verus() {
        return crate::verify_verus::impl_names(cfg);
    }
    let mut m = impl_names_from_json(cfg);
    // without any Aeneas output there is no implementation to name: the
    // `impl_correct` obligations appear after the first verify
    if !cfg.lean_dir().join("Code").join("Funs.lean").exists() {
        return m;
    }
    // an unimplemented func compiles to a panicking stub, which Aeneas models
    // too; its `impl_correct` would be unprovable noise, so only implemented
    // funcs get the implementation-dependent obligations
    let implemented = solution_fns(cfg);
    m.retain(|name, _| implemented.contains(name));
    let specs = cfg.specs();
    if let Ok(prog) = parse_spec(cfg) {
        for d in prog.decls.iter().filter(|d| d.kind == Kind::Func && implemented.contains(&d.name)) {
            m.entry(d.name.clone()).or_insert_with(|| cfg.lean_name(module_of(&specs, &prog, &d.name).as_deref(), &d.name));
        }
    }
    m
}

/// Rust type name → Lean name of its Aeneas inductive: from `translation.json`
/// when Aeneas has run, else predicted from the namespace and the spec module
/// (`Lz77.spec.Token`).
pub fn type_names(cfg: &Config, prog: &Program) -> TypeNames {
    if cfg.is_verus() {
        return crate::verify_verus::type_names(cfg, prog);
    }
    let mut m = TypeNames::new();
    let specs = cfg.specs();
    let predict = |n: &str| cfg.lean_name(module_of(&specs, prog, n).as_deref(), n);
    for n in prog.types.enums.keys().chain(prog.types.structs.keys()) {
        m.insert(n.clone(), predict(n));
    }
    // ambient functions: `fn:<name>` → the Lean name of their Aeneas model
    for n in prog.types.ambient.keys() {
        m.insert(format!("fn:{n}"), predict(n));
    }
    if let Ok(text) = fs::read_to_string(cfg.translation_path()) {
        if let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) {
            for t in json["types"].as_array().into_iter().flatten() {
                if let (Some(rust), Some(lean)) = (t["rust_name"].as_str(), t["lean_name"].as_str()) {
                    let short = rust.rsplit("::").next().unwrap_or(rust);
                    if m.contains_key(short) {
                        m.insert(short.to_string(), lean.to_string());
                    }
                }
            }
            let paths = rust_paths(cfg, &specs, prog);
            for f in json["functions"].as_array().into_iter().flatten() {
                if f.get("loop").is_some() {
                    continue;
                }
                if let (Some(rust), Some(lean)) = (f["rust_name"].as_str(), f["lean_name"].as_str()) {
                    if let Some(short) = paths.get(rust) {
                        if prog.types.ambient.contains_key(short) {
                            m.insert(format!("fn:{short}"), lean.to_string());
                        }
                    }
                }
            }
        }
    }
    m
}

/// The tables of the specification files, sorted by name.
pub fn spec_tables(prog: &Program) -> Vec<emit::Table> {
    table_names(prog)
        .into_iter()
        .map(|n| {
            let c = &prog.types.consts[&n];
            emit::Table { name: n.clone(), ty: c.ty.clone(), elems: c.table.clone().unwrap_or_default() }
        })
        .collect()
}

/// The models of the tables' Rust constants, which Charon keeps opaque:
/// Aeneas's name pattern (`crate::module::NAME` with the crate's name) and the
/// Lean definition.
fn table_models(cfg: &Config, prog: &Program) -> Vec<(String, String)> {
    let specs = cfg.specs();
    let krate = cfg.crate_name.replace('-', "_");
    spec_tables(prog)
        .iter()
        .map(|t| {
            let module = module_of(&specs, prog, &t.name);
            let pattern = format!("{}::{}", cfg.rust_module(&krate, module.as_deref()), t.name);
            let lean = match &module {
                Some(m) => format!("{}.{}", m.replace("::", "."), t.name),
                None => t.name.clone(),
            };
            (pattern, emit::table_model(&cfg.ns, &lean, t))
        })
        .collect()
}

/// The array constants of the specification files (tables), sorted.
pub fn table_names(prog: &Program) -> Vec<String> {
    let mut v: Vec<String> = prog.types.consts.iter().filter(|(_, c)| c.table.is_some()).map(|(n, _)| n.clone()).collect();
    v.sort();
    v
}

/// The ambient functions the specification's constraints call.
pub fn ambient_used(prog: &Program) -> Vec<String> {
    let mut v: Vec<String> = prog.types.ambient.keys().filter(|f| prog.decls.iter().any(|d| d.requires.iter().chain(d.ensures.iter()).chain(d.decreases.iter()).any(|e| e.calls(f)) || d.body.iter().any(|s| s.calls(f)))).cloned().collect();
    v.sort();
    v
}

/// Has Aeneas translated every ambient function the specification calls?
pub fn ambient_available(cfg: &Config, prog: &Program) -> bool {
    let used = ambient_used(prog);
    if used.is_empty() {
        return true;
    }
    let Ok(text) = fs::read_to_string(cfg.translation_path()) else { return false };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else { return false };
    let paths = rust_paths(cfg, &cfg.specs(), prog);
    let have: Vec<String> = json["functions"].as_array().into_iter().flatten().filter_map(|f| f["rust_name"].as_str()).filter_map(|r| paths.get(r)).cloned().collect();
    used.iter().all(|f| have.contains(f)) && cfg.lean_dir().join("Code").join("Funs.lean").exists()
}

fn impl_names_from_json(cfg: &Config) -> HashMap<String, String> {
    let mut m = HashMap::new();
    let p = cfg.translation_path();
    let Ok(text) = fs::read_to_string(&p) else { return m };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else { return m };
    let Ok(prog) = parse_spec(cfg) else { return m };
    let paths = rust_paths(cfg, &cfg.specs(), &prog);
    for f in json["functions"].as_array().into_iter().flatten() {
        if f.get("loop").is_some() {
            continue;
        }
        let (Some(rust), Some(lean)) = (f["rust_name"].as_str(), f["lean_name"].as_str()) else { continue };
        if let Some(short) = paths.get(rust) {
            m.insert(short.clone(), lean.to_string());
        }
    }
    m
}

/// `translation.json`'s Rust path (`my_crate::a::b::f`) of every name of
/// the specification → the name.
fn rust_paths(cfg: &Config, specs: &[SpecFile], prog: &Program) -> HashMap<String, String> {
    let krate = cfg.crate_name.replace('-', "_");
    prog.origin.keys().map(|n| (format!("{}::{n}", cfg.rust_module(&krate, module_of(specs, prog, n).as_deref())), n.clone())).collect()
}

/// Parse the specification files into one program.
pub fn parse_spec(cfg: &Config) -> Result<Program, String> {
    let texts = cfg.spec_texts()?;
    let srcs: Vec<String> = texts.into_iter().map(|(_, t)| t).collect();
    let prog = djinn_syntax::parse_sources(&srcs).map_err(|e| fail_at(cfg, e))?;
    if prog.decls.is_empty() {
        return Err(format!("{}: no `djinn! {{ … }}` declarations found", cfg.specs_display()));
    }
    Ok(prog)
}

/// The report's entries of the specification (empty if it does not parse).
pub fn spec_entries(cfg: &Config) -> Vec<djinn_syntax::project::Entry> {
    cfg.spec_texts().map(|t| djinn_syntax::project::index_texts(&t.into_iter().map(|(_, s)| s).collect::<Vec<_>>())).unwrap_or_default()
}

/// Parse and lower the specification.
pub fn lower_spec(cfg: &Config) -> Result<Vec<Lowered>, String> {
    let prog = parse_spec(cfg)?;
    let names = type_names(cfg, &prog);
    if cfg.is_verus() {
        return djinn_syntax::lower_verus::lower_program(&prog, &names).map_err(|e| fail_at(cfg, e));
    }
    djinn_syntax::lower_program_named(&prog, &names).map_err(|e| fail_at(cfg, e))
}

/// The emitter's context for this crate.
pub fn emit_cx<'a>(cfg: &'a Config, lowered: &[Lowered], impl_names: &'a HashMap<String, String>, type_names: &'a TypeNames) -> EmitCx<'a> {
    EmitCx {
        ns: &cfg.ns,
        impl_names,
        type_names,
        has_types: cfg.lean_dir().join("Code").join("Types.lean").exists(),
        has_funs: cfg.lean_dir().join("Code").join("Funs.lean").exists(),
        unfoldable: lowered
            .iter()
            .flat_map(|d| {
                let mut v = vec![format!("{}_pre", d.name)];
                // `_spec` of a declaration with choices is a non-recursive
                // wrapper of `_body`; `_body` recurses when the declaration does
                if d.decreases.is_empty() || !d.choices.is_empty() {
                    v.push(format!("{}_spec", d.name));
                }
                if d.decreases.is_empty() && !d.choices.is_empty() {
                    v.push(format!("{}_body", d.name));
                }
                v
            })
            .collect(),
    }
}

/// Was `Code/` translated from the specification's current types and ambient
/// functions? `aeneas_pipeline` records what it translated (`types_record`)
/// in the scratch space; anything else — another field, variant, module or
/// ambient body, or no record — needs Charon and Aeneas again.
pub fn types_available(cfg: &Config, prog: &Program) -> bool {
    if !cfg.lean_dir().join("Code").join("Types.lean").exists() {
        return false;
    }
    let user_ok = types_recorded(cfg, prog);
    // a `HashMap` in a signature needs the modeled type from `TypesExternal.lean`
    let uses_map = prog.decls.iter().any(|d| d.params.iter().any(|p| has_map(&p.ty)) || d.ret.as_ref().map(|(_, t)| has_map(t)).unwrap_or(false));
    let map_ok = !uses_map || fs::read_to_string(cfg.lean_dir().join("Code").join("TypesExternal.lean")).map(|t| t.contains("structure std.collections.hash.map.HashMap")).unwrap_or(false);
    user_ok && map_ok
}

/// Is `Code/` recorded as the translation of the current types and ambient functions?
fn types_recorded(cfg: &Config, prog: &Program) -> bool {
    fs::read_to_string(types_record_path(cfg)).ok().as_deref() == Some(types_record(cfg, prog).as_str())
}

fn types_record_path(cfg: &Config) -> std::path::PathBuf {
    cfg.state_dir().join("types.translated")
}

/// The specification's user types and ambient functions, canonically: each
/// with its module, its definition (fields, variants and their types in
/// order) or source, sorted by name.
fn types_record(cfg: &Config, prog: &Program) -> String {
    let specs = cfg.specs();
    let mut lines: Vec<String> = Vec::new();
    for (n, e) in &prog.types.enums {
        lines.push(format!("enum {n} in {:?}: {:?}", module_of(&specs, prog, n), e.variants));
    }
    for (n, s) in &prog.types.structs {
        lines.push(format!("struct {n} in {:?}: {:?}", module_of(&specs, prog, n), s.fields));
    }
    for (n, a) in &prog.types.ambient {
        lines.push(format!("fn {n} in {:?}: {}", module_of(&specs, prog, n), a.source));
    }
    lines.sort();
    lines.join("\n")
}

fn has_map(t: &djinn_syntax::RType) -> bool {
    use djinn_syntax::RType;
    match t {
        RType::Map(..) => true,
        RType::Seq(e, _) | RType::Option(e) => has_map(e),
        RType::Result(a, b) => has_map(a) || has_map(b),
        _ => false,
    }
}

/// Does the specification need Aeneas's `Types` module (user types)?
pub fn needs_types(lowered: &[Lowered]) -> bool {
    lowered.iter().any(|d| d.uses_types)
}


pub fn decl_statuses(cfg: &Config, lowered: &[Lowered], names: &HashMap<String, String>) -> Vec<DeclStatus> {
    if cfg.is_verus() {
        return crate::verify_verus::decl_statuses(cfg, lowered, names);
    }
    let fns = solution_fns(cfg);
    let tn = parse_spec(cfg).map(|p| type_names(cfg, &p)).unwrap_or_default();
    let cx = emit_cx(cfg, lowered, names, &tn);
    let entries: HashMap<String, djinn_syntax::project::Entry> = spec_entries(cfg)
        .into_iter()
        .map(|e| (e.name.clone(), e))
        .collect();
    let mut v: Vec<DeclStatus> = lowered
        .iter()
        .map(|d| DeclStatus {
            name: d.name.clone(),
            kind: d.kind.word().into(),
            implemented: d.kind == Kind::Rel || fns.contains(&d.name),
            obligations: emit::obligations(&cx, d).into_iter().map(|o| o.name).collect(),
            tokens: entries.get(&d.name).map(|e| e.tokens.clone()).unwrap_or_default(),
            uses: entries.get(&d.name).map(|e| e.uses.clone()).unwrap_or_default(),
            ok: false,
            weak: d.weakly_specified,
        })
        .collect();
    // the ambient functions the constraints call: trusted, no obligations,
    // recorded so that editing one marks its callers as changed
    let mut ambient: Vec<&djinn_syntax::project::Entry> = entries.values().filter(|e| e.kind == "ambient" && lowered.iter().any(|d| d.ambient_calls.contains(&e.name))).collect();
    ambient.sort_by(|a, b| a.name.cmp(&b.name));
    for e in ambient {
        v.push(DeclStatus { name: e.name.clone(), kind: "ambient".into(), implemented: true, obligations: vec![], tokens: e.tokens.clone(), uses: e.uses.clone(), ok: true, weak: false });
    }
    v
}


/// Does a Lean segment (a top-level command with its attributes and doc
/// comment) concern one of the removed declarations: is it named after it
/// (`name`, `name.…`, `name_…`), or does it mention its definitions
/// (`name_spec`, `name_pre`, `name_body` and their lemmas `name_spec.…`), one of
/// its obligations (`name.unambiguous`, …, exactly), or its Aeneas model
/// (`<module>.name`, `<module>.name_loop…`, for a module of the solution's
/// translation in `modules`, with or without the namespace `ns`)? Other words
/// that merely start with the name (`min_le_left` for a removed `min`) do not
/// count.
fn mentions(segment: &str, removed: &[String], ns: &str, modules: &[String]) -> Option<String> {
    let declared = declared_name(segment);
    let strip = |w: &str| -> String {
        let w = w.strip_prefix(&format!("{ns}.")).unwrap_or(w);
        ["Spec.", "Proofs.", "Obligations."].iter().find_map(|p| w.strip_prefix(p)).unwrap_or(w).to_string()
    };
    for n in removed {
        if let Some(d) = &declared {
            let d = strip(d);
            if d == *n || d.starts_with(&format!("{n}.")) || d.starts_with(&format!("{n}_")) {
                return Some(n.clone());
            }
        }
    }
    for word in segment.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\'' || c == '«' || c == '»')) {
        let w = strip(word.trim_matches('.'));
        for n in removed {
            let own = ["_spec", "_pre", "_body"].iter().any(|s| w == format!("{n}{s}") || w.starts_with(&format!("{n}{s}.")));
            let obligation = w.strip_prefix(&format!("{n}.")).is_some_and(emit::is_obligation_kind);
            let model = model_of(&w, n, modules).is_some();
            if own || obligation || model {
                return Some(n.clone());
            }
        }
    }
    None
}

/// The name a segment's command declares (`theorem x`, `private lemma x`, …).
fn declared_name(segment: &str) -> Option<String> {
    const KW: &[&str] = &["theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive", "opaque", "axiom"];
    const MODS: &[&str] = &["private", "protected", "noncomputable", "partial", "nonrec", "unsafe"];
    for l in segment.lines() {
        let mut ws = l.split_whitespace().skip_while(|w| MODS.contains(w));
        if let Some(k) = ws.next() {
            if KW.contains(&k) {
                return ws.next().map(|n| n.trim_end_matches(':').to_string());
            }
        }
    }
    None
}

/// The Lean module paths (without the namespace) of the solution's Aeneas
/// translation: `solution`, `spec`, `solution.sub`, … — what models of
/// functions are named under.
fn model_modules(cfg: &Config) -> Vec<String> {
    let mut v: Vec<String> = Vec::new();
    for lean in model_names(cfg) {
        if let Some((m, _)) = lean.rsplit_once('.') {
            if !v.iter().any(|x| x == m) {
                v.push(m.to_string());
            }
        }
    }
    v
}

/// The Lean names (without the namespace) of every function of the
/// solution's Aeneas translation, loops included.
fn model_names(cfg: &Config) -> Vec<String> {
    let mut v: Vec<String> = Vec::new();
    let Ok(text) = fs::read_to_string(cfg.translation_path()) else { return v };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else { return v };
    for f in json["functions"].as_array().into_iter().flatten() {
        if let Some(lean) = f["lean_name"].as_str() {
            v.push(lean.strip_prefix(&format!("{}.", cfg.ns)).unwrap_or(lean).to_string());
        }
    }
    v
}

/// Does a segment mention the Aeneas model of one of `funcs` (`<module>.f`,
/// `<module>.f_loop…`) that the current translation no longer has: a lemma
/// about an implementation that was removed?
fn mentions_gone_model(segment: &str, funcs: &[String], ns: &str, modules: &[String], models: &[String]) -> Option<String> {
    for word in segment.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\'' || c == '«' || c == '»')) {
        let w = word.trim_matches('.');
        let w = w.strip_prefix(&format!("{ns}.")).unwrap_or(w);
        for f in funcs {
            if let Some(model) = model_of(w, f, modules) {
                if !models.iter().any(|x| *x == model) {
                    return Some(f.clone());
                }
            }
        }
    }
    None
}

/// The model of `f` a word names (`<module>.f`, `<module>.f_loop…`, or a
/// constant of one, `<module>.f_loop.body`), for a module of `modules`.
fn model_of(w: &str, f: &str, modules: &[String]) -> Option<String> {
    for m in modules {
        let Some(rest) = w.strip_prefix(m.as_str()).and_then(|r| r.strip_prefix('.')) else { continue };
        let first = rest.split('.').next().unwrap_or("");
        if first == f || first.strip_prefix(&format!("{f}_loop")).is_some_and(|r| r.bytes().all(|b| b.is_ascii_digit())) {
            return Some(format!("{m}.{first}"));
        }
    }
    None
}

/// Split a Lean file into top-level segments: each command (`theorem`, `def`,
/// …) with the attributes and doc comment that precede it. `import`, `open`,
/// `namespace`, `end`, `set_option` and comments form segments of their own.
pub(crate) fn lean_segments(text: &str) -> Vec<String> {
    const STARTS: &[&str] = &["theorem ", "lemma ", "def ", "abbrev ", "instance ", "example ", "noncomputable ", "private ", "protected ", "structure ", "inductive ", "@[", "/--", "/-!", "/-", "import ", "open ", "namespace ", "end ", "section ", "set_option ", "attribute ", "variable ", "#"];
    const PREFIX: &[&str] = &["@[", "/--"];
    let mut segs: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut cur_is_prefix_only = false;
    for line in text.split_inclusive('\n') {
        let starts = STARTS.iter().any(|k| line.starts_with(k));
        if starts && !cur.is_empty() && !cur_is_prefix_only {
            segs.push(std::mem::take(&mut cur));
        }
        if starts {
            // an attribute or a doc comment opens a segment that the next command completes
            cur_is_prefix_only = PREFIX.iter().any(|k| line.starts_with(k));
        }
        cur.push_str(line);
    }
    if !cur.is_empty() {
        segs.push(cur);
    }
    segs
}

fn removable(segment: &str) -> bool {
    let first_cmd = segment.lines().find(|l| !(l.starts_with("@[") || l.starts_with("/--") || l.trim().is_empty() || l.starts_with("    ") || l.starts_with("--") || l.starts_with(" ")));
    matches!(first_cmd, Some(l) if ["theorem ", "lemma ", "def ", "abbrev ", "instance ", "example ", "noncomputable ", "private ", "protected ", "structure ", "inductive "].iter().any(|k| l.starts_with(k)))
}

/// Declarations that left the specification since the last report, and
/// obligations that no longer exist: move their theorems (and helper lemmas
/// mentioning them) and their Rust implementations out of the way into
/// `.djinnscratch/backup/<time>-stale/`, so the crate keeps building.
fn archive_stale(cfg: &Config, lowered: &[Lowered], cx: &EmitCx, log: &mut Log, archive_rust: bool) -> Result<(), String> {
    let current: std::collections::HashSet<&str> = lowered.iter().map(|d| d.name.as_str()).collect();
    let report = Report::load(cfg);
    // removed declarations: known to the last report but gone, or — if the
    // report was already rewritten — still owning obligation theorems
    // (`name.unambiguous`, `name.impl_correct`, …) in Proofs.lean
    let mut removed: Vec<String> = Vec::new();
    let mut removed_funcs: Vec<String> = Vec::new();
    if let Some(r) = &report {
        for d in &r.declarations {
            // ambient functions are recorded for change detection only; they
            // are not declarations and own nothing in the Lean files
            if d.kind == "ambient" {
                continue;
            }
            if !current.contains(d.name.as_str()) {
                removed.push(d.name.clone());
                if d.kind == "func" {
                    removed_funcs.push(d.name.clone());
                }
            }
        }
    }
    let proofs_path = cfg.lean_dir().join("Proofs.lean");
    if let Ok(text) = fs::read_to_string(&proofs_path) {
        for l in text.lines() {
            if let Some(rest) = l.strip_prefix("theorem ") {
                let name = rest.split(|c: char| c.is_whitespace() || c == ':').next().unwrap_or("");
                if let Some((decl, ob)) = name.rsplit_once('.') {
                    let known = emit::is_obligation_kind(ob);
                    if known && !current.contains(decl) && !removed.iter().any(|r| r == decl) {
                        removed.push(decl.to_string());
                        if ob == "impl_correct" || ob == "unambiguous" {
                            removed_funcs.push(decl.to_string());
                        }
                    }
                }
            }
        }
    }
    // obligations that vanished from declarations that remain (a `wf` with nothing left to
    // check, say) are archived too, even when no declaration was removed
    let current_obligations: std::collections::HashSet<String> = lowered.iter().flat_map(|d| emit::obligations(cx, d).into_iter().map(|o| o.name)).collect();
    let modules = model_modules(cfg);
    let models = model_names(cfg);
    // funcs of the specification without an implementation (any more), once
    // Aeneas has run: lemmas about their old models cannot elaborate
    let unimplemented: Vec<String> = if cx.has_funs { lowered.iter().filter(|d| d.kind == Kind::Func && !cx.impl_names.contains_key(&d.name)).map(|d| d.name.clone()).collect() } else { Vec::new() };
    let mut stale_lean = String::new();
    let mut stale_rust = String::new();
    let mut notes = Vec::new();
    // Lean: segments about removed declarations, and theorems of vanished obligations
    if let Ok(text) = fs::read_to_string(&proofs_path) {
        let mut kept = String::new();
        let mut n_removed = 0usize;
        let mut n_vanished = 0usize;
        for seg in lean_segments(&text) {
            let mut drop = false;
            if removable(&seg) {
                if let Some(n) = mentions(&seg, &removed, &cfg.ns, &modules) {
                    drop = true;
                    n_removed += 1;
                    stale_lean.push_str(&format!("-- stale: mentions removed declaration `{n}`\n"));
                } else if let Some(f) = mentions_gone_model(&seg, &unimplemented, &cfg.ns, &modules, &models) {
                    drop = true;
                    n_vanished += 1;
                    stale_lean.push_str(&format!("-- stale: mentions the Aeneas model of `{f}`, which is no longer implemented\n"));
                } else if let Some(name) = seg.lines().find_map(|l| l.strip_prefix("theorem ").map(|r| r.split(|c: char| c.is_whitespace() || c == ':').next().unwrap_or("").to_string())) {
                    // an obligation theorem (`decl.kind`) for a declaration that still exists
                    if let Some((decl, ob)) = name.rsplit_once('.') {
                        let known = emit::is_obligation_kind(ob);
                        // `impl_correct` and `exists` are obligations only once the Aeneas
                        // model exists: their proofs are not stale before Aeneas has run
                        // at all. Once it has, a func without them has no implementation
                        // (any more): a proof about the one that was is stale
                        let model_pending = matches!(ob, "impl_correct" | "exists") && !cx.has_funs;
                        if known && current.contains(decl) && !current_obligations.contains(&name) && !model_pending {
                            drop = true;
                            n_vanished += 1;
                            stale_lean.push_str(&format!("-- stale: obligation `{name}` no longer exists\n"));
                        }
                    }
                }
            }
            if drop {
                stale_lean.push_str(&seg);
                stale_lean.push('\n');
            } else {
                kept.push_str(&seg);
            }
        }
        if n_removed + n_vanished > 0 {
            fs::write(&proofs_path, kept).map_err(|e| e.to_string())?;
            if n_removed > 0 {
                notes.push(format!("{n_removed} Lean declaration(s) about removed {}", removed.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")));
            }
            if n_vanished > 0 {
                notes.push(format!("{n_vanished} theorem(s) of obligations that no longer exist or about implementations that do not"));
            }
        }
    }
    // Rust: `pub fn` items of removed funcs
    let (removed_funcs, cut) = archive_rust_fns(cfg, removed_funcs, log, archive_rust)?;
    stale_rust.push_str(&cut);
    if !removed_funcs.is_empty() && !cut.is_empty() {
        notes.push(format!("{} Rust function(s) implementing removed {}", removed_funcs.len(), removed_funcs.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")));
    }
    if notes.is_empty() {
        return Ok(());
    }
    let dir = cfg.state_dir().join("backup").join(format!("{}-stale", id_time(now())));
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    if !stale_lean.is_empty() {
        fs::write(dir.join("Proofs.stale.lean"), format!("-- Removed from Proofs.lean by `cargo djinn translate` because the specification\n-- no longer has the declarations or obligations they concern.\n\n{stale_lean}")).map_err(|e| e.to_string())?;
    }
    if !stale_rust.is_empty() {
        fs::write(dir.join("solution.stale.rs"), format!("//! Removed from the solution by `cargo djinn translate`: implementations of\n//! functions the specification no longer declares.\n\n{stale_rust}")).map_err(|e| e.to_string())?;
    }
    log.line(&format!("archived to {}: {}", cfg.rel(&dir), notes.join("; ")));
    Ok(())
}

/// The implementations of removed `fn`s, cut out of the solution — unless
/// other solution code still calls them, in which case they have become
/// helpers and stay (said in the log). Returns the names actually cut and
/// the text removed (for the backup); with `archive_rust` off nothing is
/// cut (a jail would push the function back on its next verify).
pub(crate) fn archive_rust_fns(cfg: &Config, removed_funcs: Vec<String>, log: &mut Log, archive_rust: bool) -> Result<(Vec<String>, String), String> {
    let (removed_funcs, kept): (Vec<String>, Vec<String>) = removed_funcs.into_iter().partition(|n| !djinn_syntax::project::rust_fn_referenced(&cfg.solution_dir(), n));
    for k in &kept {
        log.line(&format!("kept `{k}` in the solution as a helper: the specification no longer declares it, but other solution code calls it"));
    }
    let mut stale_rust = String::new();
    if removed_funcs.is_empty() || !archive_rust {
        return Ok((removed_funcs, stale_rust));
    }
    for file in rust_files(&cfg.solution_dir()) {
        let Ok(src) = fs::read_to_string(&file) else { continue };
        let Ok(ast) = syn::parse_file(&src) else { continue };
        let mut cut: Vec<(usize, usize)> = Vec::new(); // 1-based inclusive line ranges
        for item in &ast.items {
            if let syn::Item::Fn(f) = item {
                if removed_funcs.contains(&f.sig.ident.to_string()) {
                    use syn::spanned::Spanned;
                    let sp = item.span();
                    cut.push((sp.start().line, sp.end().line));
                }
            }
        }
        if cut.is_empty() {
            continue;
        }
        let lines: Vec<&str> = src.split_inclusive('\n').collect();
        let mut kept = String::new();
        for (i, l) in lines.iter().enumerate() {
            let ln = i + 1;
            if cut.iter().any(|(a, b)| ln >= *a && ln <= *b) {
                stale_rust.push_str(l);
            } else {
                kept.push_str(l);
            }
        }
        stale_rust.push('\n');
        fs::write(&file, kept).map_err(|e| e.to_string())?;
    }
    Ok((removed_funcs, stale_rust))
}

/// The solution is safe Rust: `src/lib.rs` (or `main.rs`) includes it as a
/// module under `#[forbid(unsafe_code)]` (or forbids it crate-wide), and no
/// solution file contains the `unsafe` keyword. Neither verifier reasons
/// about unsafe code (Aeneas models safe Rust only; Verus requires
/// unsafe blocks to be marked `external`, which the audit bans), so this is
/// what makes "the verifier never sees `unsafe`" true. Every regular file
/// under the solution directory counts, whatever its name: rustc compiles a
/// `#[path = "impl.txt"]` module too, so a file that is not Rust is refused
/// (`audit_file`), and a `#[path]`/`include!` target must be an `.rs` file
/// inside the solution directory (`solution_escapes`).
pub fn check_safe(cfg: &Config) -> Result<(), String> {
    use quote::ToTokens;
    fn forbids(attrs: &[syn::Attribute]) -> bool {
        attrs.iter().any(|a| a.path().is_ident("forbid") && a.meta.to_token_stream().to_string().contains("unsafe_code"))
    }
    let root = ["src/lib.rs", "src/main.rs"].iter().map(|f| cfg.crate_dir.join(f)).find(|p| p.exists()).ok_or("no src/lib.rs or src/main.rs")?;
    let src = fs::read_to_string(&root).map_err(|e| format!("{}: {e}", root.display()))?;
    let file = syn::parse_file(&src).map_err(|e| format!("{}: {e}", root.display()))?;
    let crate_wide = forbids(&file.attrs);
    // `djinn::solution!();` expands to the module under `#[forbid(unsafe_code)]`,
    // read from this backend's solution directory
    let by_macro = file.items.iter().any(|it| matches!(it, syn::Item::Macro(m) if m.mac.path.segments.last().is_some_and(|s| s.ident == "solution")));
    // a written-out module must name this backend's solution: a crate holding
    // one solution per backend would otherwise compile the other one
    let path_of = |m: &syn::ItemMod| -> Option<String> {
        m.attrs.iter().find(|a| a.path().is_ident("path")).and_then(|a| match &a.meta {
            syn::Meta::NameValue(nv) => match &nv.value {
                syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(l), .. }) => Some(l.value()),
                _ => None,
            },
            _ => None,
        })
    };
    let want = cfg.solution_dir().join("mod.rs");
    let mut wrong_path = None;
    for it in &file.items {
        if let syn::Item::Mod(m) = it {
            if m.ident == "solution" {
                if let Some(p) = path_of(m) {
                    let at = root.parent().unwrap_or(&cfg.crate_dir).join(&p);
                    if at.canonicalize().ok() != want.canonicalize().ok() {
                        wrong_path = Some(p);
                    }
                }
            }
        }
    }
    if let Some(p) = wrong_path {
        return Err(format!(
            "FAIL: {} includes the solution from `{p}`, not from this backend's `{}`: write `djinn::solution!();` (it picks the backend's solution directory)",
            cfg.rel(&root),
            cfg.rel(&want)
        ));
    }
    let module_level = file.items.iter().any(|it| matches!(it, syn::Item::Mod(m) if m.ident == "solution" && forbids(&m.attrs)));
    if !crate_wide && !module_level && !by_macro {
        return Err(format!(
            "FAIL: {} must include the solution under `#[forbid(unsafe_code)]`: write `djinn::solution!();` (or\n  #[forbid(unsafe_code)]\n  #[path = \"../{}/mod.rs\"]\n  pub mod solution;\nor forbid unsafe_code crate-wide with `#![forbid(unsafe_code)]`)",
            cfg.rel(&root),
            cfg.sol_rel()
        ));
    }
    fn has_unsafe(ts: proc_macro2::TokenStream) -> bool {
        ts.into_iter().any(|t| match t {
            proc_macro2::TokenTree::Ident(i) => i == "unsafe",
            proc_macro2::TokenTree::Group(g) => has_unsafe(g.stream()),
            _ => false,
        })
    }
    let sol = cfg.solution_dir();
    for f in all_files(&sol) {
        let bytes = fs::read(&f).map_err(|e| format!("FAIL: {}: {e}", cfg.rel(&f)))?;
        let ts = audit_file(cfg, &f, &bytes, &[&sol])?;
        djinn_syntax::project::solution_escapes(&sol, &f, &bytes).map_err(|e| format!("FAIL: {}", e.replace(&format!("{}/", cfg.crate_dir.display()), "")))?;
        if has_unsafe(ts) {
            return Err(format!("FAIL: {} contains `unsafe`; the solution must be safe Rust (the verifier reasons about safe code only)", cfg.rel(&f)));
        }
    }
    Ok(())
}

/// A file of the implementer's as Rust tokens. Every regular file under the
/// implementer's directories must be Rust: rustc compiles whatever a
/// `#[path = "…"]` names, whatever its extension, and the audits are what
/// keep the verified code and the compiled code the same file — so a file
/// that does not tokenize as Rust (a note, a data file, a stray editor
/// backup) is refused rather than skipped.
pub(crate) fn audit_file(cfg: &Config, f: &Path, bytes: &[u8], dirs: &[&Path]) -> Result<proc_macro2::TokenStream, String> {
    let where_ = dirs.iter().map(|d| cfg.rel(d)).collect::<Vec<_>>().join(", ");
    let src = std::str::from_utf8(bytes).map_err(|_| format!("FAIL: {} is not UTF-8 text; every file under {where_} is compiled or audited as Rust source (keep notes and data elsewhere)", cfg.rel(f)))?;
    src.parse::<proc_macro2::TokenStream>().map_err(|_| format!("FAIL: {} cannot be read as Rust tokens; every file under {where_} is compiled or audited as Rust source, whatever its name (keep notes and data elsewhere)", cfg.rel(f)))
}

/// Every Rust source (`.rs`) under `dir`, for the tools that parse items
/// (`syn`); the audits use `all_files`, which skips nothing.
pub(crate) fn rust_files(dir: &Path) -> Vec<std::path::PathBuf> {
    all_files(dir).into_iter().filter(|p| p.extension().map(|x| x == "rs").unwrap_or(false)).collect()
}

/// Every regular file under `dir`, whatever its name or extension (what the
/// evidence fingerprint covers, and so what the audits must cover).
pub(crate) fn all_files(dir: &Path) -> Vec<std::path::PathBuf> {
    let mut v = Vec::new();
    fn walk(d: &Path, v: &mut Vec<std::path::PathBuf>) {
        for e in fs::read_dir(d).into_iter().flatten().flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, v);
            } else {
                v.push(p);
            }
        }
    }
    walk(dir, &mut v);
    v.sort();
    v
}

/// Emit the trusted Lean files (and the proof skeleton / project scaffolding once).
pub fn translate(cfg: &Config, log: &mut Log) -> Result<Vec<Lowered>, String> {
    translate_opts(cfg, log, true)
}

/// Does the implementer's proof file hold more than the skeleton (a proof
/// begun)?
pub fn proofs_started(cfg: &Config) -> bool {
    let text = fs::read_to_string(cfg.proof_main()).unwrap_or_default();
    match cfg.backend {
        Backend::Lean => text.matches("theorem ").count() > text.matches(":= by\n  sorry").count(),
        Backend::Verus => text.matches("proof fn ").count() > text.matches(djinn_syntax::emit_verus::TODO).count(),
    }
}

/// `archive_rust = false` while verifying from a jail: the jail would push the
/// removed function back on its next verify, so the human's own `translate`
/// does that archiving.
/// A crate-root `build.rs` that reruns when anything under the solution or the
/// proofs changes: the build gate (`djinn!`) tracks the files it knew of, and
/// stable proc macros cannot track a directory, so a newly added file would
/// otherwise reach the gate only with the next rebuild. Written once; a crate
/// with a build script of its own is told what to add.
pub(crate) fn gate_build_script(cfg: &Config, log: &mut Log) -> Result<(), String> {
    // the implementer's proof files of the backend: `<proofs>/<NS>/` (Lean),
    // `<verus>/src/` (Verus: `proofs.rs` and `proofs/`)
    // — this backend's, and the other's too once it has a solution (a crate
    // may hold one implementation per backend); a missing path would rerun
    // the script on every build, so only existing ones are listed. The
    // backend itself (`DJINN_BACKEND`) picks the solution `djinn::solution!`
    // compiles.
    let mut dirs = Vec::new();
    for b in [cfg.backend, if cfg.is_verus() { Backend::Lean } else { Backend::Verus }] {
        let sol = b.solution_dir(&cfg.work_dir, &cfg.verus_dir);
        if b != cfg.backend && !sol.is_dir() {
            continue;
        }
        let proof_dir = match b {
            Backend::Lean => cfg.lean_dir(),
            Backend::Verus => cfg.verus_src(),
        };
        dirs.push(cfg.rel(&sol));
        dirs.push(cfg.rel(&proof_dir));
    }
    let mut lines: Vec<String> = dirs.iter().map(|d| d.replace('\\', "/")).map(|d| format!("cargo:rerun-if-changed={d}")).collect();
    lines.push("cargo:rerun-if-env-changed=DJINN_BACKEND".into());
    let path = cfg.crate_dir.join("build.rs");
    let manifest = fs::read_to_string(cfg.crate_dir.join("Cargo.toml")).unwrap_or_default();
    let own = manifest.lines().any(|l| l.trim_start().starts_with("build") && l.contains('='));
    const HEADER: &str = "// Written by `cargo djinn translate`: rebuild (and so rerun the djinn build\n// gate) when a file is added under the solution or the proofs.\n";
    let write = |log: &mut Log, what: &str| -> Result<(), String> {
        let body: String = lines.iter().map(|l| format!("    println!(\"{l}\");\n")).collect();
        fs::write(&path, format!("{HEADER}fn main() {{\n{body}}}\n")).map_err(|e| format!("build.rs: {e}"))?;
        log.line(what);
        Ok(())
    };
    match fs::read_to_string(&path) {
        Ok(t) if lines.iter().all(|l| t.contains(l.as_str())) => Ok(()),
        // ours, for the other backend (or an older layout): rewritten
        Ok(t) if t.starts_with(HEADER) && !own => write(log, "rewrote build.rs for this backend's proof directory"),
        Err(_) if !own => write(log, "wrote build.rs (reruns the build gate when files are added)"),
        _ => {
            log.line(&format!("note: the crate has a build script of its own; add `{}` to it so the build gate sees newly added files", lines.join("`, `")));
            Ok(())
        }
    }
}

pub fn translate_opts(cfg: &Config, log: &mut Log, archive_rust: bool) -> Result<Vec<Lowered>, String> {
    if cfg.is_verus() {
        return crate::verify_verus::translate_opts(cfg, log, archive_rust);
    }
    let prog = parse_spec(cfg)?;
    let tn = type_names(cfg, &prog);
    let lowered = djinn_syntax::lower_program_named(&prog, &tn).map_err(|e| fail_at(cfg, e))?;
    let dir = cfg.lean_dir();
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    // the work directory: a placeholder solution so the crate builds and the
    // layout is visible
    fs::create_dir_all(cfg.solution_dir()).map_err(|e| e.to_string())?;
    if !cfg.solution_dir().join("mod.rs").exists() {
        fs::write(cfg.solution_dir().join("mod.rs"), "//! LLM-owned: the implementation of the `func`s of the specification.\n").map_err(|e| e.to_string())?;
    }
    gate_build_script(cfg, log)?;
    // user types are Rust enums and structs, and ambient functions are Rust
    // code: `Spec.lean` needs their Aeneas translation, so the pipeline runs
    // once before the first translate
    let ambient_stale = !ambient_used(&prog).is_empty() && !types_recorded(cfg, &prog);
    if (needs_types(&lowered) && !types_available(cfg, &prog)) || !ambient_available(cfg, &prog) || ambient_stale {
        log.line("the specification mentions user types or ambient functions whose Lean translation Aeneas has not produced yet: running Charon and Aeneas once");
        aeneas_pipeline(cfg, log).map_err(|(_, e)| e)?;
    }
    let tn = type_names(cfg, &prog);
    let lowered = djinn_syntax::lower_program_named(&prog, &tn).map_err(|e| fail_at(cfg, e))?;
    let names = impl_names(cfg);
    let cx = emit_cx(cfg, &lowered, &names, &tn);
    archive_stale(cfg, &lowered, &cx, log, archive_rust)?;
    let w = |name: &str, text: String| -> Result<(), String> {
        fs::write(dir.join(name), text).map_err(|e| format!("{name}: {e}"))
    };
    w("Vocab.lean", emit::vocab_lean())?;
    let tables = spec_tables(&prog);
    if tables.is_empty() {
        let _ = fs::remove_file(dir.join("Tables.lean"));
    } else {
        w("Tables.lean", emit::tables_lean(&cfg.ns, &tables))?;
    }
    w("Spec.lean", emit::spec_lean(&cx, &lowered))?;
    w("Obligations.lean", emit::obligations_lean(&cx, &lowered))?;
    w("Statements.lean", emit::statements_lean(&cx, &lowered))?;
    w("Audit.lean", emit::audit_lean(&cx, &lowered))?;
    if !dir.join("Proofs.lean").exists() {
        w("Proofs.lean", emit::proofs_skeleton(&cx, &lowered))?;
        log.line(&format!("wrote initial {}/Proofs.lean (never overwritten)", dir.display()));
    } else {
        // the specification may have grown: append stubs for obligations
        // that have no theorem yet, so existing work is reused
        let path = dir.join("Proofs.lean");
        let mut text = fs::read_to_string(&path).map_err(|e| e.to_string())?;
        // the Aeneas model has appeared since the skeleton was written
        let ci = emit::code_import(&cx);
        if !ci.is_empty() && !text.contains(ci.trim_end()) {
            let spec_import = format!("import {}.Spec\n", cfg.ns);
            text = match text.find(&spec_import) {
                Some(i) => format!("{}{}{}", &text[..i + spec_import.len()], ci, &text[i + spec_import.len()..]),
                None => format!("{ci}{text}"),
            };
            fs::write(&path, &text).map_err(|e| e.to_string())?;
            log.line(&format!("added `{}` to Proofs.lean", ci.trim_end()));
        }
        // a stub still as generated (`sorry`, nothing else) whose statement is
        // no longer the obligation's: the specification changed under it;
        // the current stub replaces it (a theorem with any proof stays)
        let current: HashMap<String, String> = lowered.iter().flat_map(|d| emit::obligations(&cx, d)).filter(|o| o.generated_proof.is_none()).map(|o| (o.name.clone(), emit::stub_text(&o))).collect();
        let mut refreshed = Vec::new();
        let mut rebuilt = String::new();
        for seg in lean_segments(&text) {
            let name = seg.strip_prefix("theorem ").and_then(|r| r.split(|c: char| c.is_whitespace() || c == ':').next()).unwrap_or("");
            match current.get(name) {
                Some(stub) if seg.trim_end().ends_with(":= by\n  sorry") && seg.matches(":= by").count() == 1 && seg.trim_end() != stub.trim_end() => {
                    refreshed.push(name.to_string());
                    rebuilt.push_str(stub);
                }
                _ => rebuilt.push_str(&seg),
            }
        }
        if !refreshed.is_empty() {
            text = rebuilt;
            fs::write(&path, &text).map_err(|e| e.to_string())?;
            log.line(&format!("refreshed {} untouched stub(s) in Proofs.lean whose statement changed: {}", refreshed.len(), refreshed.join(", ")));
        }
        let mut missing = Vec::new();
        for d in &lowered {
            for o in emit::obligations(&cx, d) {
                if o.generated_proof.is_some() {
                    continue;
                }
                let decl = format!("theorem {} ", o.name);
                let decl2 = format!("theorem {}\n", o.name);
                if !text.contains(&decl) && !text.contains(&decl2) {
                    missing.push(o);
                }
            }
        }
        if !missing.is_empty() {
            let end_marker = format!("end {}.Proofs", cfg.ns);
            let mut add = String::new();
            add.push_str("/-! ## obligations added by a later `translate` (specification changed) -/\n\n");
            for o in &missing {
                add.push_str(&emit::stub_text(o));
            }
            let new_text = if let Some(i) = text.rfind(&end_marker) {
                format!("{}{}{}", &text[..i], add, &text[i..])
            } else {
                format!("{text}\n{add}")
            };
            fs::write(&path, new_text).map_err(|e| e.to_string())?;
            log.line(&format!("added {} stub(s) to Proofs.lean for new obligations: {}", missing.len(), missing.iter().map(|o| o.name.clone()).collect::<Vec<_>>().join(", ")));
        }
    }
    let root = cfg.proofs.join(format!("{}.lean", cfg.ns));
    if !root.exists() {
        fs::write(&root, format!("import {0}.Spec\nimport {0}.Obligations\n", cfg.ns)).map_err(|e| e.to_string())?;
    }
    // an initial report, so that `cargo build` can say "never attempted"
    // precisely and the macro has a file to track
    if !Report::path(cfg).exists() {
        let mut r = Report { time: now(), duration_secs: 0, pass: false, stage: "not run".into(), obligations: BTreeMap::new(), declarations: decl_statuses(cfg, &lowered, &names), errors: Vec::new(), log_tail: Vec::new(), evidence: String::new(), backend: cfg.backend };
        for d in &r.declarations {
            for o in &d.obligations {
                r.obligations.insert(o.clone(), "unverified".into());
            }
        }
        r.save(cfg);
        log.line(&format!("wrote initial {}", cfg.rel(&Report::path(cfg))));
    }
    // the shared Lean package cache
    let pk = cfg.proofs.join(".lake").join("packages");
    // a dangling link (a crate copied from another machine) counts as missing
    let dangling = fs::symlink_metadata(&pk).map(|m| m.file_type().is_symlink()).unwrap_or(false) && !pk.exists();
    if dangling {
        let _ = fs::remove_file(&pk);
    }
    if !pk.exists() && cfg.lake_packages.is_dir() {
        fs::create_dir_all(cfg.proofs.join(".lake")).map_err(|e| e.to_string())?;
        let _ = std::os::unix::fs::symlink(&cfg.lake_packages, &pk);
        log.line(&format!("linked {} to the shared package cache {}", cfg.rel(&pk), cfg.lake_packages.display()));
    }
    let lakefile = cfg.proofs.join("lakefile.lean");
    if !lakefile.exists() {
        let aeneas_lean = cfg.aeneas_lean.clone().ok_or(
            "no lakefile.lean yet and no Aeneas Lean backend path: set [package.metadata.djinn] aeneas_lean or DJINN_AENEAS_LEAN",
        )?;
        fs::write(
            &lakefile,
            format!(
                "import Lake\nopen Lake DSL\n\nrequire aeneas from \"{aeneas_lean}\"\n\npackage «{0}» {{}}\n\n@[default_target] lean_lib «{1}» {{}}\n",
                cfg.crate_name, cfg.ns
            ),
        )
        .map_err(|e| e.to_string())?;
        let tc = cfg.proofs.join(&aeneas_lean).join("lean-toolchain");
        if let Ok(t) = fs::read_to_string(&tc) {
            fs::write(cfg.proofs.join("lean-toolchain"), t).map_err(|e| e.to_string())?;
        }
    }
    sync_lake_files(cfg, log)?;
    // the harness guide, always refreshed (the scratch directory may not exist yet on a crate
    // that has never been run)
    fs::create_dir_all(cfg.state_dir()).map_err(|e| format!("{}: {e}", cfg.state_dir().display()))?;
    fs::write(cfg.guide_path(), crate::guide::guide(cfg, &lowered, &names)).map_err(|e| format!("{}: {e}", cfg.guide_path().display()))?;
    log.line(&format!("translated {} declarations into {}", lowered.len(), dir.display()));
    Ok(lowered)
}

/// The Aeneas Lean backend the proofs build against: the `require aeneas
/// from "…"` of the lakefile, as written and resolved from the proofs
/// directory.
fn aeneas_backend(cfg: &Config) -> Option<(String, std::path::PathBuf)> {
    let lakefile = fs::read_to_string(cfg.proofs.join("lakefile.lean")).ok()?;
    let line = lakefile.lines().find(|l| l.trim_start().starts_with("require aeneas from"))?;
    let path = line.split('"').nth(1)?;
    Some((path.to_string(), cfg.proofs.join(path)))
}

/// `lean-toolchain` and `lake-manifest.json` follow the Aeneas backend: the
/// toolchain is the backend's, and the manifest is the backend's with the
/// backend itself as the first (path) package. The root manifest is the one
/// Lake trusts, so a stale one would build the backend against the Mathlib
/// it pins, not the one the backend wants. When Mathlib's revision changes,
/// its prebuilt oleans are fetched (`lake exe cache get`): Lake would
/// otherwise compile Mathlib.
fn sync_lake_files(cfg: &Config, log: &mut Log) -> Result<(), String> {
    let Some((require, backend)) = aeneas_backend(cfg) else { return Ok(()) };
    if let Ok(t) = fs::read_to_string(backend.join("lean-toolchain")) {
        let own = cfg.proofs.join("lean-toolchain");
        if fs::read_to_string(&own).ok().map(|s| s.trim().to_string()).as_deref() != Some(t.trim()) {
            fs::write(&own, &t).map_err(|e| e.to_string())?;
            log.line(&format!("lean-toolchain updated to {}", t.trim()));
        }
    }
    let Ok(bm) = fs::read_to_string(backend.join("lake-manifest.json")) else { return Ok(()) };
    let mut expected: serde_json::Value = serde_json::from_str(&bm).map_err(|e| format!("{}: {e}", backend.join("lake-manifest.json").display()))?;
    if let Some(pk) = expected.get_mut("packages").and_then(|p| p.as_array_mut()) {
        for p in pk.iter_mut() {
            if let Some(o) = p.as_object_mut() {
                o.insert("inherited".into(), true.into());
            }
        }
        pk.insert(0, serde_json::json!({"type": "path", "scope": "", "name": "aeneas", "manifestFile": "lake-manifest.json", "inherited": false, "dir": require, "configFile": "lakefile.lean"}));
    }
    // the lakefile's `package «name»`
    let lakefile = fs::read_to_string(cfg.proofs.join("lakefile.lean")).unwrap_or_default();
    // (Lake reads the manifest's `name` as a Lean `Name`: a name that is not a
    // plain identifier, such as `lz4-compress`, keeps its «» there)
    let name = lakefile.lines().find_map(|l| l.trim_start().strip_prefix("package «")).and_then(|r| r.split('»').next()).unwrap_or(&cfg.crate_name).to_string();
    let plain = name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    expected["name"] = if plain { name } else { format!("«{name}»") }.into();
    let own = cfg.proofs.join("lake-manifest.json");
    let pins = |m: &serde_json::Value| -> BTreeMap<String, String> {
        m["packages"].as_array().into_iter().flatten().map(|p| (p["name"].as_str().unwrap_or("").to_string(), p["rev"].as_str().or(p["dir"].as_str()).unwrap_or("").to_string())).collect()
    };
    let own_manifest = fs::read_to_string(&own).ok().and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok());
    let have = own_manifest.as_ref().map(pins).unwrap_or_default();
    let want = pins(&expected);
    if have == want && own_manifest.as_ref().map(|m| m["name"] == expected["name"]).unwrap_or(false) {
        return Ok(());
    }
    fs::write(&own, serde_json::to_string_pretty(&expected).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    let short = |s: Option<&String>| s.map(|s| s.chars().take(8).collect::<String>()).unwrap_or_else(|| "none".into());
    let changed: Vec<String> = want.iter().filter(|(k, v)| have.get(*k) != Some(v)).map(|(k, v)| format!("{k} {} → {}", short(have.get(k)), short(Some(v)))).collect();
    log.line(&format!("lake-manifest.json updated to the Aeneas backend's: {}", changed.join(", ")));
    if have.get("mathlib") != want.get("mathlib") {
        // Mathlib's oleans for the new revision (Lake moves the checkout first)
        let out = run(Command::new("lake").args(["exe", "cache", "get"]).current_dir(&cfg.proofs), "lake exe cache get", log)?;
        if let Some(l) = out.lines().rev().find(|l| !l.trim().is_empty()) {
            log.line(l);
        }
    }
    Ok(())
}

/// Charon or Aeneas with a memory limit (`DJINN_TOOL_MEM_GB`, default 40; 0: none) that dies with
/// its parent: a run that blows up fails on its own, and none outlives the verify that started it.
fn guarded_tool(tool: &str) -> Command {
    let gb: u64 = std::env::var("DJINN_TOOL_MEM_GB").ok().and_then(|v| v.parse().ok()).unwrap_or(40);
    if gb == 0 {
        return Command::new(tool);
    }
    // real memory in a cgroup, not address space (`prlimit --as` stops runtimes that reserve
    // large thread stacks); `setpriv --pdeathsig` ends it with its parent
    // no user session bus (an MCP server started by an agent's sandbox): the run's own cgroup,
    // when the wrapper set one, still bounds it, and the tool still dies with its parent
    let bus = std::env::var_os("XDG_RUNTIME_DIR").map(|d| std::path::Path::new(&d).join("bus").exists()).unwrap_or(false);
    if !bus {
        let mut c = Command::new("setpriv");
        c.args(["--pdeathsig", "KILL"]).arg(tool);
        return c;
    }
    let mut c = Command::new("systemd-run");
    c.args(["--user", "--scope", "-q", "-p"]).arg(format!("MemoryMax={gb}G")).args(["-p", "MemorySwapMax=0", "setpriv", "--pdeathsig", "KILL"]).arg(tool);
    c
}

pub(crate) fn run(cmd: &mut Command, what: &str, log: &mut Log) -> Result<String, String> {
    log.line(&format!("== {what}"));
    let out = cmd.output().map_err(|e| format!("{what}: cannot run: {e}"))?;
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    if !out.status.success() {
        let tail: Vec<&str> = text.lines().rev().take(60).collect::<Vec<_>>().into_iter().rev().collect();
        return Err(format!("FAIL: {what}\n{}", tail.join("\n")));
    }
    Ok(text)
}

fn noise(line: &str) -> bool {
    line.starts_with('⚠')
        || line.contains("linter")
        || line.starts_with("Note:")
        || line.trim().is_empty()
        || line.contains("unusedVariables")
        || line.contains("binding can be removed")
        || line.contains("not explicitly referenced")
        || line.contains("dupNamespace")
        || line.contains("duplicated in the declaration")
        || line.starts_with("trace:")
        || line.starts_with("  • ")
}

/// The whole gate. With `jail`, the LLM-owned files are first synced back
/// from the jail into the crate, and the trusted files are pushed to the jail
/// afterwards.
pub fn verify(cfg: &Config, jail: Option<&Path>, log: &mut Log) -> Report {
    let start = now();
    let mut report = Report {
        time: start,
        duration_secs: 0,
        pass: false,
        stage: String::new(),
        obligations: BTreeMap::new(),
        declarations: Vec::new(),
        errors: Vec::new(),
        log_tail: Vec::new(),
        evidence: String::new(),
        backend: cfg.backend,
    };
    if cfg.is_verus() {
        return crate::verify_verus::verify(cfg, jail, log, report);
    }
    let result = verify_inner(cfg, jail, log, &mut report);
    match result {
        Ok(()) => {
            report.pass = true;
            report.stage = "done".into();
            let missing = report.unimplemented();
            if missing.is_empty() {
                log.line("PASS");
            } else {
                // not the crate's PASS: the gate refuses it until every `fn` is implemented
                log.line(&format!("SPECIFICATION VERIFIED: every obligation so far is proved; not implemented yet: {} (run `cargo djinn implement`)", missing.join(", ")));
            }
        }
        Err((stage, msg)) => {
            report.pass = false;
            report.stage = stage;
            for l in msg.lines() {
                log.line(l);
            }
            if report.errors.is_empty() {
                report.errors = msg.lines().filter(|l| l.contains("error")).map(|s| s.to_string()).collect();
            }
        }
    }
    report.duration_secs = now() - start;
    report.log_tail = log.text.lines().rev().take(80).map(|s| s.to_string()).collect::<Vec<_>>().into_iter().rev().collect();
    report.finalize();
    report.save(cfg);
    if let Some(j) = jail {
        if let Err(e) = jail::sync_forward(cfg, j) {
            log.line(&format!("warning: could not refresh the jail: {e}"));
        }
    }
    report
}

/// Stages 1–4 of the gate: `cargo build`, the safe-Rust check, Charon, Aeneas
/// (regenerating `Code/`), and the audit of `translation.json`.
pub fn aeneas_pipeline(cfg: &Config, log: &mut Log) -> Result<(), (String, String)> {
    let stage = |s: &str, e: String| (s.to_string(), e);
    // 1. the crate builds: signatures of spec and solution agree
    // the verifier is the one party allowed to compile an unverified crate
    run(Command::new("cargo").args(["build", "--quiet"]).env("DJINN_VERIFYING", "1").current_dir(&cfg.crate_dir), "cargo build", log)
        .map_err(|e| stage("cargo build", e))?;
    // 1b. only safe Rust: the solution must be included under
    // `#[forbid(unsafe_code)]`, and must not spell `unsafe` at all
    check_safe(cfg).map_err(|e| stage("unsafe", e))?;
    // 2. charon
    // Charon's intermediate output belongs to the disposable state, not the crate root
    let _ = fs::create_dir_all(cfg.state_dir());
    let llbc = cfg.state_dir().join(format!("{}.llbc", cfg.crate_name));
    let mut charon = guarded_tool(&cfg.charon);
    charon.args(["cargo", "--preset=aeneas", "--dest-file"]).arg(&llbc).env("DJINN_VERIFYING", "1").current_dir(&cfg.crate_dir);
    // the verified program is what the specification names: translation
    // starts from the `fn` stubs and follows their calls (the solution and its
    // helpers); drivers, the workload and any other module of the crate are
    // never seen
    let prog = parse_spec(cfg).map_err(|e| stage("specification", e))?;
    let specs = cfg.specs();
    let path = |n: &str| format!("--start-from={}::{n}", cfg.rust_module("crate", module_of(&specs, &prog, n).as_deref()));
    for d in prog.decls.iter().filter(|d| d.kind == Kind::Func) {
        charon.arg(path(&d.name));
    }
    // and the ambient functions the constraints call: their Aeneas model is
    // their meaning in `Spec.lean`
    for f in ambient_used(&prog) {
        charon.arg(path(&f));
    }
    // and the specification's own types: a `struct` or `enum` that only the
    // relations mention is reached by no `fn`, yet `Spec.lean` names its
    // Aeneas inductive
    for t in prog.types.enums.keys().chain(prog.types.structs.keys()) {
        charon.arg(path(t));
    }
    // the specification's tables stay opaque: Aeneas would spell each as a
    // list of scalar literals, which Lean cannot elaborate at the sizes codecs
    // need; the model library defines them from `Spec.lean`'s packed form
    for n in table_names(&prog) {
        charon.arg(format!("--opaque={}::{n}", cfg.rust_module("crate", module_of(&specs, &prog, &n).as_deref())));
    }
    // and only the library target: binaries (`src/main.rs`, `src/bin/`) are
    // drivers, which Charon must not even compile
    charon.args(["--", "--lib"]);
    run(&mut charon, "charon", log).map_err(|e| stage("charon", e))?;
    // 2b. what Aeneas has no Lean form for (byte strings, floats), and what it
    // would print into a Lean comment (source paths, names), must not be there
    let llbc_text = fs::read_to_string(&llbc).map_err(|e| stage("charon", format!("{}: {e}", llbc.display())))?;
    let llbc_json: serde_json::Value = serde_json::from_str(&llbc_text).map_err(|e| stage("charon", format!("{}: {e}", llbc.display())))?;
    if let Some(bad) = unprintable_literals(&llbc_json).into_iter().next() {
        return Err(stage("literals", format!("FAIL: {bad}")));
    }
    // 3. aeneas, regenerating Code/ from scratch
    let code_dir = cfg.lean_dir().join("Code");
    let _ = fs::remove_dir_all(&code_dir);
    let _ = fs::remove_file(types_record_path(cfg));
    run(
        guarded_tool(&cfg.aeneas)
            .args(["-backend", "lean"])
            .arg(&llbc)
            .arg("-dest")
            .arg(&cfg.proofs)
            .args(["-subdir", &format!("{}/Code", cfg.ns), "-split-files", "-namespace", &cfg.ns, "-emit-json"]),
        "aeneas",
        log,
    )
    .map_err(|e| stage("aeneas", e))?;
    // 3b. the literals Aeneas printed, read back with Lean's lexical rules,
    // must be the program's: an Aeneas printing a `"` raw could not pass
    let mut code_files = Vec::new();
    for e in fs::read_dir(&code_dir).into_iter().flatten().flatten() {
        let p = e.path();
        if p.extension().is_some_and(|x| x == "lean") && !p.file_name().is_some_and(|n| n.to_string_lossy().contains("_Template")) {
            let name = format!("Code/{}", p.file_name().unwrap_or_default().to_string_lossy());
            let bytes = fs::read(&p).map_err(|e| stage("aeneas", format!("{}: {e}", p.display())))?;
            // (an Aeneas printing a non-ASCII char byte-wise writes no UTF-8)
            let text = String::from_utf8(bytes).map_err(|_| stage("literals", format!("FAIL: {name} is not UTF-8: Aeneas printed a literal byte by byte")))?;
            code_files.push((name, text));
        }
    }
    check_code_literals(&code_files, &llbc_json).map_err(|e| stage("literals", format!("FAIL: {e}")))?;
    // 4. audit translation.json: no local opaque items, no unknown externals
    // (Aeneas writes it next to its output; it belongs to the scratch space)
    let _ = fs::rename(cfg.proofs.join("translation.json"), cfg.translation_path());
    let tj = fs::read_to_string(cfg.translation_path()).map_err(|e| stage("aeneas", format!("translation.json: {e}")))?;
    let json: serde_json::Value = serde_json::from_str(&tj).map_err(|e| stage("aeneas", e.to_string()))?;
    for f in json["functions"].as_array().into_iter().flatten() {
        if f["is_local"].as_bool() == Some(true) && f["is_opaque"].as_bool() == Some(true) {
            return Err(stage("escape hatch", format!("FAIL: local function {} is opaque (no escape hatches)", f["rust_name"])));
        }
    }
    // Rust string literals: Aeneas proves `toStr`'s length bound with
    // `decide +native`, an axiom the audit rejects; the same bound by kernel
    // reduction instead (the `Str` is the same — only the proof differs)
    for e in fs::read_dir(&code_dir).into_iter().flatten().flatten() {
        let p = e.path();
        if p.extension().is_some_and(|x| x == "lean") && !p.file_name().is_some_and(|n| n.to_string_lossy().contains("_Template")) {
            if let Ok(text) = fs::read_to_string(&p) {
                let fixed = kernel_str_literals(&text);
                if fixed != text {
                    fs::write(&p, fixed).map_err(|e| stage("aeneas", e.to_string()))?;
                }
            }
        }
    }
    if code_dir.join("FunsExternal_Template.lean").exists() || code_dir.join("TypesExternal_Template.lean").exists() {
        // externals with a model in the library are written as definitions
        // (trusted); any other is a failure with an explanation
        let patterns = external_patterns(&code_dir);
        match crate::models::cover(&cfg.ns, &patterns, &table_models(cfg, &prog)) {
            Ok((funs, types)) => {
                fs::write(code_dir.join("FunsExternal.lean"), funs).map_err(|e| stage("externals", e.to_string()))?;
                fs::write(code_dir.join("TypesExternal.lean"), types).map_err(|e| stage("externals", e.to_string()))?;
                log.line(&format!("modeled {} item(s) the solution uses (standard-library methods and types, the specification's tables), from the trusted model library", patterns.len()));
            }
            Err(uncovered) => return Err(stage("externals", explain_externals(cfg, &uncovered))),
        }
    }
    // what `Code/` now translates (see `types_available`)
    fs::write(types_record_path(cfg), types_record(cfg, &prog)).map_err(|e| stage("aeneas", e.to_string()))?;
    Ok(())
}

/// Text in Charon's output that Aeneas cannot print faithfully into `Code/`:
/// byte-string and float literals (Aeneas writes `sorry` for them), and `/-`
/// or `-/` in a name or source path (printed into a Lean comment, which they
/// would close early). String and char literals may hold anything: Aeneas
/// escapes them, and `check_code_literals` reads them back.
fn unprintable_literals(v: &serde_json::Value) -> Vec<String> {
    fn walk(v: &serde_json::Value, out: &mut Vec<String>) {
        match v {
            serde_json::Value::Object(m) => {
                for (k, x) in m {
                    match (k.as_str(), x) {
                        // Charon's own options (its output path) and the files'
                        // source text: not printed by Aeneas
                        ("options" | "contents", _) => {}
                        ("Str" | "Char", serde_json::Value::String(_)) => {}
                        ("ByteStr", serde_json::Value::Array(_)) => out.push("a byte string literal (`b\"…\"`) in the solution cannot be translated: Aeneas has no Lean form for it. Use an array of `u8`".into()),
                        ("Float", serde_json::Value::Object(_)) => out.push("a float literal in the solution cannot be translated: Aeneas has no Lean form for it".into()),
                        (_, serde_json::Value::String(s)) if s.contains("/-") || s.contains("-/") => out.push(format!("{s:?} (a name or source path in the translated program) holds `/-` or `-/`, which Aeneas would print into a Lean comment: rename it")),
                        _ => walk(x, out),
                    }
                }
            }
            serde_json::Value::Array(a) => a.iter().for_each(|x| walk(x, out)),
            serde_json::Value::String(s) if s.contains("/-") || s.contains("-/") => out.push(format!("{s:?} (a name or source path in the translated program) holds `/-` or `-/`, which Aeneas would print into a Lean comment: rename it")),
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(v, &mut out);
    out
}

/// A token of Aeneas's Lean output.
#[derive(Debug, Clone, PartialEq)]
enum LeanTok {
    Ident(String),
    /// a string literal, decoded
    Str(String),
    /// a char literal, decoded
    Char(char),
    /// any other character (punctuation, digits)
    Other(char),
}

/// Lean's lexical rules, as far as reading literals back needs them: comments
/// (`--`, nested `/- -/`) are skipped; an identifier (also `«…»`, and with
/// `'`, `!`, `?` or subscripts inside) is one token, so its `'` is not a
/// char; `"…"` and `'…'` are decoded with Lean's escapes (`\\ \" \' \n \t \r
/// \xHH \uHHHH`). Anything else after a `\`, a malformed char and an
/// unterminated literal or comment are errors. Each token comes with its
/// byte range.
fn lean_tokens(text: &str) -> Result<Vec<(LeanTok, usize, usize)>, String> {
    let cs: Vec<(usize, char)> = text.char_indices().collect();
    let n = cs.len();
    let at = |k: usize| cs.get(k).map(|x| x.1);
    let end = |k: usize| if k < n { cs[k].0 } else { text.len() };
    let line = |k: usize| text[..end(k)].matches('\n').count() + 1;
    let ident_rest = |c: char| c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?') || ('\u{2080}'..='\u{209C}').contains(&c);
    // the escape after a `\` at `j`: its char and the index after it
    let escape = |j: usize| -> Result<(char, usize), String> {
        let hex = |from: usize, len: usize| -> Result<char, String> {
            let digits: String = (from..from + len).filter_map(at).collect();
            if digits.chars().count() == len && digits.chars().all(|c| c.is_ascii_hexdigit()) {
                u32::from_str_radix(&digits, 16).ok().and_then(char::from_u32).ok_or_else(|| format!("line {}: `\\x`/`\\u` escape is not a character", line(from)))
            } else {
                Err(format!("line {}: `\\x`/`\\u` escape needs exactly {len} hex digits", line(from)))
            }
        };
        Ok(match at(j) {
            Some('\\') => ('\\', j + 1),
            Some('"') => ('"', j + 1),
            Some('\'') => ('\'', j + 1),
            Some('n') => ('\n', j + 1),
            Some('t') => ('\t', j + 1),
            Some('r') => ('\r', j + 1),
            Some('x') => (hex(j + 1, 2)?, j + 3),
            Some('u') => (hex(j + 1, 4)?, j + 5),
            Some(c) => return Err(format!("line {}: `\\{c}` is not a Lean escape", line(j))),
            None => return Err(format!("line {}: unterminated literal", line(j))),
        })
    };
    let mut toks = Vec::new();
    let mut i = 0;
    while i < n {
        let (pos, c) = cs[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '-' && at(i + 1) == Some('-') {
            while i < n && cs[i].1 != '\n' {
                i += 1;
            }
        } else if c == '/' && at(i + 1) == Some('-') {
            let (mut j, mut depth) = (i + 2, 1);
            while j < n && depth > 0 {
                if cs[j].1 == '/' && at(j + 1) == Some('-') {
                    depth += 1;
                    j += 2;
                } else if cs[j].1 == '-' && at(j + 1) == Some('/') {
                    depth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            if depth > 0 {
                return Err(format!("line {}: unterminated comment", line(i)));
            }
            i = j;
        } else if c == '«' {
            let mut j = i + 1;
            while j < n && cs[j].1 != '»' {
                j += 1;
            }
            if j >= n {
                return Err(format!("line {}: unterminated «name»", line(i)));
            }
            toks.push((LeanTok::Ident(text[pos..end(j + 1)].to_string()), pos, end(j + 1)));
            i = j + 1;
        } else if c.is_alphabetic() || c == '_' {
            let mut j = i + 1;
            while j < n && ident_rest(cs[j].1) {
                j += 1;
            }
            toks.push((LeanTok::Ident(text[pos..end(j)].to_string()), pos, end(j)));
            i = j;
        } else if c == '"' {
            let mut s = String::new();
            let mut j = i + 1;
            loop {
                match at(j) {
                    None => return Err(format!("line {}: unterminated string literal", line(i))),
                    Some('"') => break,
                    Some('\\') => {
                        let (ch, k) = escape(j + 1)?;
                        s.push(ch);
                        j = k;
                    }
                    Some(ch) => {
                        s.push(ch);
                        j += 1;
                    }
                }
            }
            toks.push((LeanTok::Str(s), pos, end(j + 1)));
            i = j + 1;
        } else if c == '\'' {
            // Lean does not read `''` as the start of a char literal
            let (ch, j) = match at(i + 1) {
                Some('\\') => escape(i + 2)?,
                Some(ch) if ch != '\'' => (ch, i + 2),
                _ => return Err(format!("line {}: malformed char literal", line(i))),
            };
            if at(j) != Some('\'') {
                return Err(format!("line {}: malformed char literal", line(i)));
            }
            toks.push((LeanTok::Char(ch), pos, end(j + 1)));
            i = j + 1;
        } else {
            toks.push((LeanTok::Other(c), pos, end(i + 1)));
            i += 1;
        }
    }
    Ok(toks)
}

/// The literals in Charon's output: the `Str` and `Char` values, skipping
/// what Aeneas never prints. Sets, not multisets: Charon interns constants (a
/// second use of a literal is a reference to the first), and Aeneas drops
/// some (the messages of `panic!`/`assert!`, which become `massert`/`fail`).
fn llbc_literals(v: &serde_json::Value, strs: &mut std::collections::BTreeSet<String>, chars: &mut std::collections::BTreeSet<char>) {
    match v {
        serde_json::Value::Object(m) => {
            for (k, x) in m {
                match (k.as_str(), x) {
                    ("options" | "contents", _) => {}
                    ("Str", serde_json::Value::String(s)) => {
                        strs.insert(s.clone());
                    }
                    ("Char", serde_json::Value::String(s)) if s.chars().count() == 1 => {
                        chars.insert(s.chars().next().unwrap());
                    }
                    _ => llbc_literals(x, strs, chars),
                }
            }
        }
        serde_json::Value::Array(a) => a.iter().for_each(|x| llbc_literals(x, strs, chars)),
        _ => {}
    }
}

/// The literals Aeneas printed into `Code/`, read back with Lean's lexical
/// rules, against the program's (the LLBC): a defence in depth against an
/// Aeneas that prints a `"` or a `'` raw, where the rest of the literal
/// would be Lean code. Every `toStr "…"` of `Code/` must be a `Str` literal
/// of the program and every char literal a `Char`. The raw `"` would end the
/// literal early, so what Lean reads is a prefix of the program's literal,
/// which is not one of its literals (unless the solution also holds that
/// prefix: the escaping Aeneas is the first line of defence, the axiom audit
/// the last). Other string literals are Aeneas's own (attribute arguments
/// such as `@[rust_fun "…"]`, target names): lexed, so that they cannot hide
/// anything, but not from the program. `files` are the `Code/*.lean` texts.
fn check_code_literals(files: &[(String, String)], llbc: &serde_json::Value) -> Result<(), String> {
    let (mut strs, mut chars) = (std::collections::BTreeSet::new(), std::collections::BTreeSet::new());
    llbc_literals(llbc, &mut strs, &mut chars);
    for (name, text) in files {
        let toks = lean_tokens(text).map_err(|e| format!("{name} is not well-formed Lean: {e}"))?;
        for (k, (tok, _, _)) in toks.iter().enumerate() {
            match tok {
                LeanTok::Str(s) if matches!(toks.get(k.wrapping_sub(1)), Some((LeanTok::Ident(id), _, _)) if id == "toStr") => {
                    if !strs.contains(s) {
                        return Err(format!("{name} holds the string literal {s:?} (as `toStr`'s argument), which is not a string literal of the translated program"));
                    }
                }
                LeanTok::Char(c) => {
                    if !chars.contains(c) {
                        return Err(format!("{name} holds the char literal {c:?}, which is not a char literal of the translated program"));
                    }
                }
                _ => {}
            }
        }
    }
    Ok(())
}

/// The proof of `toStr`'s bound (`s.toByteArray.size ≤ U32.max`) given to every
/// `toStr "…"` of Aeneas's output: `U32.max` is irreducible, so it is rewritten
/// to its numeral first; the literal's size then reduces in the kernel.
const STR_BOUND: &str = "(by rw [show Aeneas.Std.U32.max = 4294967295 by scalar_tac]; decide +kernel)";

/// `toStr "…"` → `toStr "…" STR_BOUND`, for each call without an explicit
/// proof (`(by …)`). The literal is found by `lean_tokens`, so a `"` inside
/// it (escaped) does not end it; text that does not lex is left alone
/// (`check_code_literals` has refused it).
fn kernel_str_literals(text: &str) -> String {
    let Ok(toks) = lean_tokens(text) else { return text.to_string() };
    let mut out = String::with_capacity(text.len());
    let mut last = 0;
    for (k, (tok, _, end)) in toks.iter().enumerate() {
        let after_to_str = matches!(toks.get(k.wrapping_sub(1)), Some((LeanTok::Ident(id), _, _)) if id == "toStr");
        if !(matches!(tok, LeanTok::Str(_)) && after_to_str) {
            continue;
        }
        let has_proof = matches!(toks.get(k + 1), Some((LeanTok::Other('('), _, _))) && matches!(toks.get(k + 2), Some((LeanTok::Ident(by), _, _)) if by == "by");
        if has_proof {
            continue;
        }
        out.push_str(&text[last..*end]);
        out.push(' ');
        out.push_str(STR_BOUND);
        last = *end;
    }
    out.push_str(&text[last..]);
    out
}

/// The `Name pattern`s of the items Aeneas could not model.
fn external_patterns(code_dir: &Path) -> Vec<String> {
    let mut patterns: Vec<String> = Vec::new();
    for f in ["TypesExternal_Template.lean", "FunsExternal_Template.lean"] {
        if let Ok(text) = fs::read_to_string(code_dir.join(f)) {
            // each item's doc comment opens `/-- [path]`; functions and types
            // also name a `Name pattern`, globals (the opaque tables) do not
            let mut header: Option<String> = None;
            let push = |pat: String, patterns: &mut Vec<String>| {
                if !patterns.contains(&pat) {
                    patterns.push(pat);
                }
            };
            for l in text.lines() {
                let l = l.trim();
                if let Some(rest) = l.strip_prefix("/-- [") {
                    if let Some(h) = header.take() {
                        push(h, &mut patterns);
                    }
                    header = rest.split(']').next().map(|h| h.to_string());
                } else if let Some(rest) = l.strip_prefix("Name pattern: [") {
                    header = None;
                    push(rest.trim_end_matches(']').to_string(), &mut patterns);
                }
            }
            if let Some(h) = header {
                push(h, &mut patterns);
            }
        }
    }
    patterns
}

/// What the solution used that Aeneas has no model for, read from the
/// `*External_Template.lean` files Aeneas writes (one `Name pattern` per
/// missing item), grouped by what it is about, each with the places in the
/// solution that use it and a hint. Only safe, modeled Rust can be verified;
/// anything else belongs in a driver (DESIGN.md §7).
fn explain_externals(cfg: &Config, patterns: &[String]) -> String {
    let patterns: Vec<String> = patterns.to_vec();
    // (what to look for in the pattern, the words that betray it in the solution, the hint)
    const GROUPS: &[(&[&str], &[&str], &str, &str)] = &[
        (&["core::fmt", "std::io", "_print", "alloc::fmt::format", "core::hint::must_use"], &["println!", "print!", "eprintln!", "eprint!", "format!", "write!", "writeln!", "dbg!", "std::io", "to_string"], "printing and formatting", "there is no model of I/O or formatting: return data from the function and print it in a driver (DESIGN.md §7)"),
        (&["alloc::string", "str::"], &["String", "to_string", "to_owned", "&str", "as_str", "chars()"], "strings", "`String` is modeled for `new`, `push`, `push_str`, `len`, `is_empty`, `as_bytes`, `as_str`, `into_bytes`, `from_utf8`, `from(&str)`, `clone` and `==`; this method is not: work on the bytes (`as_bytes`) or with `Vec<u8>`"),
        (&["std::collections", "alloc::collections", "core::hash", "hashbrown"], &["HashMap", "HashSet", "BTreeMap", "BTreeSet", "VecDeque", "BinaryHeap", "collections::"], "collections", "`HashMap` is modeled for `new`, `insert`, `get`, `contains_key`, `remove`, `len` and `is_empty` with scalar keys; other collections and methods are not: use those, or a `Vec`"),
        (&["f32", "f64", "core::f32", "core::f64"], &["f32", "f64"], "floating point", "Aeneas has no model of floats; use integers"),
        (&["alloc::rc", "alloc::sync", "core::cell", "alloc::boxed::Box<dyn"], &["Rc<", "Arc<", "RefCell", "Cell<", "Box<dyn", "dyn "], "shared ownership and trait objects", "no model: use plain values and `&`/`&mut`"),
        (&["core::iter", "core::slice::iter"], &["iter()", ".map(", ".filter(", ".fold(", ".sum()", ".collect", "for_each", "into_iter"], "iterator adaptors", "iterate with an index and a `while`/`for` over `0..len` instead"),
        (&["core::slice::{", "alloc::slice", "sort"], &[".sort", ".swap(", ".reverse(", ".contains(", ".binary_search"], "slice methods without a model", "write the loop yourself with index reads and writes"),
    ];
    let mut out = String::from("FAIL: the solution uses Rust that Aeneas cannot model, so it cannot be verified:\n");
    let sol_files = rust_files(&cfg.solution_dir());
    let sources: Vec<(String, String)> = sol_files.iter().filter_map(|f| fs::read_to_string(f).ok().map(|t| (cfg.rel(f), t))).collect();
    let mut used: Vec<usize> = Vec::new();
    let mut explained: Vec<&String> = Vec::new();
    for (gi, (keys, words, what, hint)) in GROUPS.iter().enumerate() {
        let hits: Vec<&String> = patterns.iter().filter(|p| keys.iter().any(|k| p.contains(k))).collect();
        if hits.is_empty() {
            continue;
        }
        used.push(gi);
        explained.extend(hits.iter().copied());
        let mut where_: Vec<String> = Vec::new();
        for (name, text) in &sources {
            for (i, l) in text.lines().enumerate() {
                if words.iter().any(|w| l.contains(w)) {
                    where_.push(format!("{name}:{}: {}", i + 1, l.trim()));
                }
            }
        }
        out.push_str(&format!("  * {what} — {hint}\n"));
        for h in hits.iter().take(4) {
            out.push_str(&format!("      missing model: {h}\n"));
        }
        for w in where_.iter().take(6) {
            out.push_str(&format!("      used at {w}\n"));
        }
    }
    let rest: Vec<&String> = patterns.iter().filter(|p| !explained.contains(p)).collect();
    if !rest.is_empty() {
        out.push_str("  * other items without a model — avoid them, or move the work to a driver:\n");
        for p in rest.iter().take(8) {
            out.push_str(&format!("      {p}\n"));
        }
    }
    out.push_str("  (the full list is in the *External_Template.lean files under the generated Code/ directory)");
    out
}

fn verify_inner(cfg: &Config, jail: Option<&Path>, log: &mut Log, report: &mut Report) -> Result<(), (String, String)> {
    let stage = |s: &str, e: String| (s.to_string(), e);
    // 0. the specification itself, so the report can list declarations
    let lowered = lower_spec(cfg).map_err(|e| stage("specification", e))?;
    report.declarations = decl_statuses(cfg, &lowered, &impl_names(cfg));
    for d in &report.declarations {
        for o in &d.obligations {
            report.obligations.insert(o.clone(), "unverified".into());
        }
    }
    // jail: take the LLM-owned files
    if let Some(j) = jail {
        for note in jail::sync_back(cfg, j).map_err(|e| stage("jail sync", e))? {
            log.line(&note);
        }
        report.declarations = decl_statuses(cfg, &lowered, &impl_names(cfg));
    }
    // what Charon reads (the crate's sources, the solution): snapshotted
    // first, so that the evidence attests the very bytes translated
    let mut sources = source_snapshot(cfg);
    // 1–4. build, Charon, Aeneas, audit
    aeneas_pipeline(cfg, log)?;
    // 5. regenerate the trusted files
    let mut lowered = translate_opts(cfg, log, jail.is_none()).map_err(|e| stage("translate", e))?;
    if source_snapshot(cfg) != sources {
        // translate archived the implementations of removed declarations:
        // Charon read the solution before that, so once more on what is left
        log.line("the solution changed during translate (archived functions): translating it again");
        sources = source_snapshot(cfg);
        aeneas_pipeline(cfg, log)?;
        lowered = translate_opts(cfg, log, jail.is_none()).map_err(|e| stage("translate", e))?;
        if source_snapshot(cfg) != sources {
            return Err(stage("evidence", "FAIL: the crate's sources changed while they were being verified; verify again".into()));
        }
    }
    let names = impl_names(cfg);
    report.declarations = decl_statuses(cfg, &lowered, &names);
    report.obligations.clear();
    for d in &report.declarations {
        for o in &d.obligations {
            report.obligations.insert(o.clone(), "unverified".into());
        }
    }
    // what this verify attests: the solution and proof files as they are now,
    // after translate has added or refreshed stubs (an edit from here on makes
    // the build gate refuse the crate until the next verify)
    report.evidence = evidence(cfg);
    if let Some(why) = report.evidence.strip_prefix("invalid: ") {
        return Err(stage("evidence", format!("FAIL: the solution and proof files cannot be fingerprinted: {why}")));
    }
    // the audit program as translated now (written again right before it
    // runs: nothing the build does to the file counts)
    let prog = parse_spec(cfg).map_err(|e| stage("specification", e))?;
    let tn = type_names(cfg, &prog);
    let cx = emit_cx(cfg, &lowered, &names, &tn);
    let audit_text = emit::audit_lean(&cx, &lowered);
    let short: Vec<String> = lowered.iter().flat_map(|d| emit::obligations(&cx, d)).map(|o| o.name).collect();
    // 6. lake build, and the statements elaborated without the proofs
    let built = run(Command::new("lake").arg("build").current_dir(&cfg.proofs), "lake build", log)
        .and_then(|text| run(Command::new("lake").args(["build", &format!("{}.Statements", cfg.ns)]).current_dir(&cfg.proofs), "lake build (statements)", log).map(|t| text + &t));
    match built {
        Ok(text) => {
            if text.contains("declaration uses 'sorry'") || text.contains("declaration uses `sorry`") {
                log.line("note: proofs still contain sorry (the axiom audit will reject them)");
            }
        }
        Err(e) => {
            report.errors = e.lines().filter(|l| l.starts_with("error:") && !noise(l)).map(|s| s.to_string()).collect();
            for o in report.obligations.values_mut() {
                *o = "error".into();
            }
            return Err(stage("lake build", e));
        }
    }
    // 7. axiom audit
    let audit_rel = format!("{}/Audit.lean", cfg.ns);
    fs::write(cfg.proofs.join(&audit_rel), &audit_text).map_err(|e| stage("axiom audit", format!("{audit_rel}: {e}")))?;
    // two processes: each imports the Mathlib-based library once (a second
    // `importModules` in one process copies every olean into the heap, and
    // the audit then needs more memory than many hosts allow a user)
    let mut audit = String::new();
    for phase in ["statements", "replay"] {
        let out = run(Command::new("lake").args(["env", "lean", AUDIT_TSTACK, "--run"]).arg(&audit_rel).arg(phase).current_dir(&cfg.proofs), &format!("axiom audit ({phase})"), log).map_err(|e| stage("axiom audit", e))?;
        audit.push_str(&out);
        if !audit.ends_with('\n') {
            audit.push('\n');
        }
    }
    let verdicts = parse_audit(&audit, &short).map_err(|e| {
        for o in report.obligations.values_mut() {
            *o = "error".into();
        }
        stage("axiom audit", format!("FAIL: axiom audit: {e}\n{}", audit.lines().take(40).collect::<Vec<_>>().join("\n")))
    })?;
    let mut bad = Vec::new();
    for (n, v) in short.iter().zip(&verdicts) {
        let status = match v {
            AuditVerdict::Ok => "proved".to_string(),
            AuditVerdict::Sorry => {
                bad.push(format!("{n} uses sorryAx"));
                "sorry".into()
            }
            AuditVerdict::Axioms(a) => {
                // `native_decide` / `decide +native` trust compiled code: say how to avoid it
                let hint = if a.contains("_native") {
                    format!(" — `decide +native`/`native_decide` (also the default proof of `toStr \"…\"` written in a proof): use `decide +kernel`, and give `toStr \"…\"` the bound explicitly: `toStr \"…\" {STR_BOUND}`")
                } else {
                    String::new()
                };
                bad.push(format!("{n} uses {a}{hint}"));
                format!("axiom:{a}")
            }
            AuditVerdict::Statement(why) => {
                bad.push(format!("{n}: {why}"));
                "error".into()
            }
            AuditVerdict::Replay(why) => {
                // one rejection fails every obligation that reaches it: said once
                let msg = format!("the kernel rejects what the obligations depend on: {why}");
                if !bad.contains(&msg) {
                    bad.push(msg);
                }
                "error".into()
            }
        };
        report.obligations.insert(n.clone(), status);
    }
    if !bad.is_empty() {
        return Err(stage("axiom audit", format!("FAIL: axiom audit\n  {}", bad.join("\n  "))));
    }
    // 8. the files verified are still the files on disk (Lake may have written
    // its manifest: what it built with is what counts)
    let after = evidence(cfg);
    if after != report.evidence {
        let manifest = format!(" {}", cfg.rel(&cfg.proofs.join("lake-manifest.json")));
        let body = |r: &str| -> Vec<String> { r.lines().skip(1).filter(|l| !l.ends_with(&manifest)).map(|s| s.to_string()).collect() };
        if body(&after) == body(&report.evidence) && !after.starts_with("invalid: ") {
            report.evidence = after;
        } else {
            return Err(stage("evidence", "FAIL: the solution or proof files changed while they were being verified; verify again".into()));
        }
    }
    if source_snapshot(cfg) != sources {
        return Err(stage("evidence", "FAIL: the crate's sources changed while they were being verified; verify again".into()));
    }
    Ok(())
}

/// The bytes of everything Charon and the specification parser read: the
/// manifest, `src/` and the solution directory.
pub(crate) fn source_snapshot(cfg: &Config) -> BTreeMap<std::path::PathBuf, Vec<u8>> {
    fn walk(d: &Path, out: &mut BTreeMap<std::path::PathBuf, Vec<u8>>) {
        for e in fs::read_dir(d).into_iter().flatten().flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else {
                out.insert(p.clone(), fs::read(&p).unwrap_or_default());
            }
        }
    }
    let mut m = BTreeMap::new();
    let manifest = cfg.crate_dir.join("Cargo.toml");
    m.insert(manifest.clone(), fs::read(&manifest).unwrap_or_default());
    walk(&cfg.crate_dir.join("src"), &mut m);
    walk(&cfg.solution_dir(), &mut m);
    m
}

/// The fingerprint of the crate's solution and proof files (see the build gate).
pub fn evidence(cfg: &Config) -> String {
    djinn_syntax::project::evidence_record(&cfg.crate_dir, &cfg.solution_dir(), &cfg.proof_root(), &cfg.ns, cfg.backend)
}

/// The audit replays proofs in the kernel on a thread of this stack size (in
/// KiB; address space reserved, not memory used): the kernel recurses as deep
/// as a proof term is, and gzip-sized proofs overflow a default 8 MiB stack.
const AUDIT_TSTACK: &str = "--tstack=1048576";

/// The audit's judgement of one obligation (see `emit::audit_lean`).
#[derive(Debug, PartialEq)]
enum AuditVerdict {
    Ok,
    Sorry,
    /// The axioms beyond the allowed ones, for the message.
    Axioms(String),
    /// Its statement is not the specification's.
    Statement(String),
    /// The kernel rejected a constant the obligations reach.
    Replay(String),
}

/// Read `Audit.lean`'s output: one verdict per obligation, in order. Only its
/// own records count, each exactly once, and the replay and the end marker
/// must be there; anything else — a missing, repeated or unknown record, any
/// other output — fails the audit.
fn parse_audit(out: &str, obligations: &[String]) -> Result<Vec<AuditVerdict>, String> {
    let mut v: Vec<Option<AuditVerdict>> = obligations.iter().map(|_| None).collect();
    let mut replay: Option<Result<(), String>> = None;
    let mut ended = false;
    for line in out.lines() {
        if line.trim().is_empty() {
            continue;
        }
        if ended {
            return Err(format!("output after the end of the audit: {line}"));
        }
        let rest = line.strip_prefix("djinn-audit ").ok_or_else(|| format!("unexpected output: {line}"))?;
        let (head, tail) = rest.split_once(' ').unwrap_or((rest, ""));
        match head {
            "replay" if replay.is_none() => {
                replay = Some(if tail.starts_with("ok ") { Ok(()) } else { Err(tail.strip_prefix("fail ").ok_or_else(|| format!("unexpected output: {line}"))?.to_string()) });
            }
            "end" if tail == obligations.len().to_string() && replay.is_some() => ended = true,
            _ => {
                let i: usize = head.parse().map_err(|_| format!("unexpected output: {line}"))?;
                let slot = v.get_mut(i).ok_or_else(|| format!("no obligation {i}: {line}"))?;
                if slot.is_some() || replay.is_some() {
                    return Err(format!("unexpected record: {line}"));
                }
                let (kind, arg) = tail.split_once(' ').unwrap_or((tail, ""));
                *slot = Some(match (kind, arg) {
                    ("ok", "") => AuditVerdict::Ok,
                    ("sorry", "") => AuditVerdict::Sorry,
                    ("axioms", a) if !a.is_empty() => AuditVerdict::Axioms(a.to_string()),
                    ("statement", w) if !w.is_empty() => AuditVerdict::Statement(w.to_string()),
                    _ => return Err(format!("unexpected record: {line}")),
                });
            }
        }
    }
    if !ended {
        return Err("the audit did not finish".into());
    }
    let replay = replay.unwrap_or_else(|| Err("no replay".into()));
    v.into_iter()
        .enumerate()
        .map(|(i, x)| {
            let x = x.ok_or_else(|| format!("no verdict for {}", obligations[i]))?;
            Ok(match (&replay, x) {
                (Err(why), AuditVerdict::Ok) => AuditVerdict::Replay(why.clone()),
                (_, x) => x,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    #[test]
    fn every_file_is_enumerated() {
        use super::*;
        let d = std::env::temp_dir().join(format!("djinn-files-{}", std::process::id()));
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(d.join("sub")).unwrap();
        for f in ["mod.rs", "impl.txt", "sub/a.rs", "sub/note", ".hidden"] {
            fs::write(d.join(f), "x").unwrap();
        }
        let names = |v: Vec<std::path::PathBuf>| v.iter().map(|p| p.strip_prefix(&d).unwrap().to_string_lossy().into_owned()).collect::<Vec<_>>();
        assert_eq!(names(all_files(&d)), [".hidden", "impl.txt", "mod.rs", "sub/a.rs", "sub/note"]);
        assert_eq!(names(rust_files(&d)), ["mod.rs", "sub/a.rs"]);
        let _ = fs::remove_dir_all(&d);
    }

    #[test]
    fn string_literals_get_a_kernel_proof() {
        let s = "let s ← f (toStr\n        \"div \\\"by\\\" zero\")\n  ok (toStr \"x\" (by decide))\n  myToStr \"y\"";
        let r = super::kernel_str_literals(s);
        assert!(r.contains("(toStr\n        \"div \\\"by\\\" zero\" (by rw [show"), "{r}");
        assert_eq!(r.matches("decide +kernel").count(), 1, "{r}");
        assert!(r.contains("myToStr \"y\""), "{r}");
        // a `"` or `'` inside the literal does not end it; `(by` after it is a proof
        let r = super::kernel_str_literals("f (toStr \"q\\\"'\") (toStr \"a\" (by simp)) (toStr\n  \"\\u00e9\")");
        assert_eq!(r, format!("f (toStr \"q\\\"'\" {0}) (toStr \"a\" (by simp)) (toStr\n  \"\\u00e9\" {0})", super::STR_BOUND));
    }

    #[test]
    fn audit_records_are_exact() {
        use super::AuditVerdict as V;
        let obs = vec!["f.unambiguous".to_string(), "f.ens_0".to_string()];
        let good = "djinn-audit 0 ok\ndjinn-audit 1 axioms NS.Proofs.evil\ndjinn-audit replay ok 7\ndjinn-audit end 2\n";
        assert_eq!(super::parse_audit(good, &obs).unwrap(), vec![V::Ok, V::Axioms("NS.Proofs.evil".into())]);
        // the old forgery: an axiom named like Lean's clean verdict is just an axiom
        let named = "djinn-audit 0 axioms «x does not depend on any axioms»\ndjinn-audit 1 ok\ndjinn-audit replay ok 7\ndjinn-audit end 2\n";
        assert!(matches!(&super::parse_audit(named, &obs).unwrap()[0], V::Axioms(_)));
        // a kernel rejection fails every obligation that looked proved
        let replay = "djinn-audit 0 ok\ndjinn-audit 1 sorry\ndjinn-audit replay fail bad\ndjinn-audit end 2\n";
        assert_eq!(super::parse_audit(replay, &obs).unwrap(), vec![V::Replay("bad".into()), V::Sorry]);
        // anything unexpected fails closed
        for bad in [
            "djinn-audit 0 ok\ndjinn-audit replay ok 7\ndjinn-audit end 2\n",                                         // missing
            "djinn-audit 0 ok\ndjinn-audit 0 ok\ndjinn-audit 1 ok\ndjinn-audit replay ok 7\ndjinn-audit end 2\n",   // twice
            "djinn-audit 0 ok\ndjinn-audit 1 ok\ndjinn-audit replay ok 7\n",                                          // unfinished
            "djinn-audit 0 ok\ndjinn-audit 1 ok\ndjinn-audit end 2\n",                                                // no replay
            "'NS.Obligations.f.ens_0' does not depend on any axioms\ndjinn-audit 0 ok\ndjinn-audit 1 ok\ndjinn-audit replay ok 7\ndjinn-audit end 2\n",
            "djinn-audit 0 ok\ndjinn-audit 1 ok\ndjinn-audit 2 ok\ndjinn-audit replay ok 7\ndjinn-audit end 2\n",
            "djinn-audit 0 ok\ndjinn-audit 1 fine\ndjinn-audit replay ok 7\ndjinn-audit end 2\n",
        ] {
            assert!(super::parse_audit(bad, &obs).is_err(), "{bad}");
        }
    }

    #[test]
    fn stale_segments_are_matched_by_exact_names() {
        let removed = vec!["min".to_string()];
        let modules = vec!["solution".to_string(), "spec".to_string()];
        let m = |s: &str| super::mentions(s, &removed, "NS", &modules);
        // a lemma that merely uses a Mathlib name starting with `min_` stays
        assert_eq!(m("theorem clamp.helper : a ≤ b := by\n  exact min_le_left a b\n"), None);
        assert_eq!(m("theorem foo : Nat.min 1 2 = 1 := rfl\n"), None);
        assert_eq!(m("theorem foo : min.ens_bound := x\n"), None);
        // its definitions, obligations, model, and helpers named after it go
        for s in [
            "theorem x : min_spec a b r := h\n",
            "theorem x : True := by simp [NS.Spec.min_pre]\n",
            "theorem x := min.unambiguous\n",
            "theorem x : solution.min a b = ok r := h\n",
            "theorem x : NS.solution.min_loop0 a = ok r := h\n",
            "private theorem min_aux : True := trivial\n",
            "@[simp]\ntheorem min.ens_0 : True := trivial\n",
        ] {
            assert_eq!(m(s), Some("min".to_string()), "{s}");
        }
    }

    #[test]
    fn lemmas_about_a_removed_implementation_are_found() {
        let modules = vec!["solution".to_string(), "spec".to_string()];
        let models = vec!["spec.f".to_string(), "solution.g".to_string()];
        let m = |s: &str| super::mentions_gone_model(s, &["f".to_string()], "NS", &modules, &models);
        assert_eq!(m("theorem body : NS.solution.f_loop.body x = y := h\n"), Some("f".into()));
        assert_eq!(m("theorem x : solution.f a = ok r := h\n"), Some("f".into()));
        // the panicking stub `spec.f` is still translated; `solution.ff` is another function
        assert_eq!(m("theorem x : spec.f a = fail e := h\n"), None);
        assert_eq!(m("theorem x : solution.ff a = ok r := h\n"), None);
    }

    #[test]
    fn literals_aeneas_cannot_print_are_refused() {
        let j = |s: &str| serde_json::from_str::<serde_json::Value>(s).unwrap();
        // strings and chars are escaped by Aeneas now: anything goes
        assert!(super::unprintable_literals(&j(r#"{"options": {"dest_file": "/tmp/-x/-/a"}, "files": [{"name": {"Local": "src/lib.rs"}, "contents": "a /- b"}], "v": {"Value": {"Str": "q\" axiom evil : False -/"}}, "w": {"Value": {"Str": "é\n\\"}}, "c": {"Value": {"Char": "'"}}, "d": {"Value": {"Char": "\\"}}, "t": {"Float": "F64"}}"#)).is_empty());
        for bad in [r#"{"Value": {"ByteStr": [1, 2]}}"#, r#"{"Value": {"Float": {"value": "1.5", "ty": "F64"}}}"#, r#"{"files": [{"name": {"Local": "src/a-/b.rs"}}]}"#, r#"{"name": "x /- y"}"#] {
            assert_eq!(super::unprintable_literals(&j(bad)).len(), 1, "{bad}");
        }
    }

    #[test]
    fn lean_literals_are_read_with_leans_escapes() {
        use super::LeanTok::*;
        let toks = |s: &str| super::lean_tokens(s).unwrap().into_iter().map(|t| t.0).collect::<Vec<_>>();
        assert_eq!(
            toks("toStr \"tab\\tnl\\nq\\\"bs\\\\\\u00e9\\u20ac😀\\x7f\" -- \"not\" 'x'\n/- 'a /- nested -/ -/ x' h'' «a b'» 'é' '\\'' '\\\\' '\\n' '\"' 3#i32"),
            vec![Ident("toStr".into()), Str("tab\tnl\nq\"bs\\é€😀\x7f".into()), Ident("x'".into()), Ident("h''".into()), Ident("«a b'»".into()), Char('é'), Char('\''), Char('\\'), Char('\n'), Char('"'), Other('3'), Other('#'), Ident("i32".into())]
        );
        // the unpatched Aeneas's output: the literal ends at the raw `"`
        assert_eq!(toks("toStr \"x\" axiom evil : False --\"")[..3], [Ident("toStr".into()), Str("x".into()), Ident("axiom".into())]);
        for bad in ["\"abc", "'ab'", "'''", "'\\", "\"\\q\"", "\"\\x4\"", "\"\\u{e9}\"", "/- open", "\"a\\\nb\""] {
            assert!(super::lean_tokens(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn code_literals_must_be_the_programs() {
        let llbc = serde_json::from_str::<serde_json::Value>(r#"{"options": {"dest_file": "\"zz\""}, "a": {"Str": "x\" axiom evil : False --"}, "b": {"Str": "é"}, "c": {"Str": "é"}, "d": {"Char": "'"}, "e": {"Char": "\n"}, "targets": ["x86_64-apple-darwin"]}"#).unwrap();
        let ok = |code: &str| super::check_code_literals(&[("Code/Funs.lean".into(), code.into())], &llbc);
        assert_eq!(ok("def f := toStr \"x\\\" axiom evil : False --\"\ndef g := (toStr \"\\u00e9\", toStr \"é\", '\\'', '\\n')\nif tgt = \"x86_64-apple-darwin\" then 1 else 0"), Ok(()));
        // the injection: `"x"` is not a literal of the program, and the long one is missing
        let e = ok("def f := toStr \"x\" axiom evil : False --\"\ndef g := (toStr \"é\", toStr \"é\", '\\'', '\\n')").unwrap_err();
        assert!(e.contains("Code/Funs.lean holds the string literal \"x\"") && e.contains("not a string literal of the translated program"), "{e}");
        // chars printed raw: `'\'` and `'''` are not Lean (`'<newline>'` is)
        assert!(ok("def g := ('\\', '\\n')").unwrap_err().contains("not well-formed Lean"));
        assert!(ok("def g := (''', '\\n')").unwrap_err().contains("not well-formed Lean"));
        assert_eq!(ok("def g := ('\n', '\\'')"), Ok(()));
        // a literal the program does not have; Aeneas's own strings are free
        assert!(ok("toStr \"é\" '\\'' 'x'").unwrap_err().contains("'x'"));
        assert!(ok("toStr \"x\\\" axiom evil : False -- \"").unwrap_err().contains("not a string literal of"));
        assert_eq!(ok("@[rust_fun \"core::str::{str}::len\"] toStr \"é\""), Ok(()));
    }

    #[test]
    fn external_patterns_include_globals() {
        let dir = std::env::temp_dir().join(format!("djinn-ext-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("FunsExternal_Template.lean"),
            "/-- [core::num::{u64}::count_ones]:\n    Source: x\n    Name pattern: [core::num::{u64}::count_ones]\n    Visibility: public -/\naxiom core.num.U64.count_ones : Std.U64 → Result Std.U32\n\n/-- [bits::spec::K]\n    Source: y\n    Visibility: public -/\naxiom spec.K : Result (Slice Std.U32)\n",
        )
        .unwrap();
        let p = super::external_patterns(&dir);
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(p, vec!["core::num::{u64}::count_ones".to_string(), "bits::spec::K".to_string()]);
    }
}
