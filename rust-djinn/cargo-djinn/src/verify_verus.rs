//! The Verus backend's `translate` and `verify`.
//!
//! Where the Lean backend translates the Rust to Lean (Charon, Aeneas) and
//! has Lean check proofs about the model, this backend has Verus verify the
//! Rust itself, inside a generated *verification crate* under
//! `<work_dir>/verus/`:
//!
//! ```text
//! src/lib.rs           generated: the module tree, `#[path]` to the solution
//! src/vocab.rs         generated: helpers the relations use
//! src/relations.rs     generated: `f_pre`, `f_spec` (the specification, lowered)
//! src/obligations.rs   generated: the proof obligations, pinned (see emit_verus)
//! src/<spec>.rs        generated: a mirror of each specification module — its
//!                      types and constants verbatim, and one stub per
//!                      implemented `fn` carrying the relation as its contract
//! src/proofs.rs        the implementer's: one `proof fn` per obligation
//! src/proofs/          the implementer's helper modules
//! ```
//!
//! The solution (`<work_dir>/solution/`) is the same file in both crates: the
//! real crate compiles it, the verification crate verifies it, and the
//! mirrored modules give it the same environment (`crate::spec::Token`,
//! `crate::spec::K`, `crate::spec::other_fn` with its contract).
//!
//! What makes a PASS trustworthy here: the trusted files are regenerated
//! from the specification on every verify; Verus runs with `--no-cheating`
//! (no `assume`, `admit`, `external_body`, `assume_specification`) and its
//! result must be `0 errors` for the whole crate; the implementer's files are
//! audited for everything else that could make the verified code differ from
//! the compiled code or weaken the check (`#[cfg]`, `include!`, `unsafe`,
//! `#[verifier::external]`, `exec_allows_no_decreases_clause`, …); and the
//! fingerprint of the solution and proof files the build gate checks covers
//! exactly the files Verus read.

use crate::config::*;
use crate::jail;
use crate::verify::{DeclStatus, Log, Report};
use djinn_syntax::ambient_verus::Translated;
use djinn_syntax::emit_verus::{self, EmitCx, How, Obligation};
use djinn_syntax::lower::Lowered;
use djinn_syntax::project::SpecFile;
use djinn_syntax::types::TypeNames;
use djinn_syntax::{Kind, Program};
use quote::ToTokens;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Module names the verification crate reserves; a specification file of
/// that module name cannot be mirrored.
const RESERVED_MODULES: &[&str] = &["vocab", "relations", "obligations", "proofs", "solution", "lib"];

/// The path of a specification module in the verification crate.
fn module_path(module: Option<&str>) -> String {
    match module {
        Some(m) => format!("crate::{m}"),
        None => "crate".to_string(),
    }
}

/// Rust type name → its path in the verification crate; `const:K` → the
/// table's path.
pub fn type_names(cfg: &Config, prog: &Program) -> TypeNames {
    let mut m = TypeNames::new();
    let specs = cfg.specs();
    let path = |n: &str| format!("{}::{n}", module_path(crate::verify::module_of(&specs, prog, n).as_deref()));
    for n in prog.types.enums.keys().chain(prog.types.structs.keys()) {
        m.insert(n.clone(), path(n));
    }
    // every constant the mirror defines: tables (arrays, slices, byte strings)
    // and the literal constants an ambient function may name
    for n in prog.types.consts.keys() {
        m.insert(format!("const:{n}"), path(n));
    }
    m
}

/// Rust function name → the path of its contract-carrying stub, for the
/// implemented `fn`s (an unimplemented one has no stub, and so no
/// `impl_correct` obligation yet).
pub fn impl_names(cfg: &Config) -> HashMap<String, String> {
    let mut m = HashMap::new();
    let implemented = crate::verify::solution_fns(cfg);
    let specs = cfg.specs();
    if let Ok(prog) = crate::verify::parse_spec(cfg) {
        for d in prog.decls.iter().filter(|d| d.kind == Kind::Func && implemented.contains(&d.name)) {
            m.insert(d.name.clone(), format!("{}::{}", module_path(crate::verify::module_of(&specs, &prog, &d.name).as_deref()), d.name));
        }
    }
    m
}

pub fn decl_statuses(cfg: &Config, lowered: &[Lowered], names: &HashMap<String, String>) -> Vec<DeclStatus> {
    let fns = crate::verify::solution_fns(cfg);
    let tn = crate::verify::parse_spec(cfg).map(|p| type_names(cfg, &p)).unwrap_or_default();
    let cx = EmitCx { names: &tn, impl_names: names };
    let entries: HashMap<String, djinn_syntax::project::Entry> = crate::verify::spec_entries(cfg).into_iter().map(|e| (e.name.clone(), e)).collect();
    let mut v: Vec<DeclStatus> = lowered
        .iter()
        .map(|d| DeclStatus {
            name: d.name.clone(),
            kind: d.kind.word().into(),
            implemented: d.kind == Kind::Rel || fns.contains(&d.name),
            obligations: emit_verus::obligations(&cx, d).into_iter().map(|o| o.name).collect(),
            tokens: entries.get(&d.name).map(|e| e.tokens.clone()).unwrap_or_default(),
            uses: entries.get(&d.name).map(|e| e.uses.clone()).unwrap_or_default(),
            ok: false,
            weak: d.weakly_specified,
        })
        .collect();
    let mut ambient: Vec<&djinn_syntax::project::Entry> = entries.values().filter(|e| e.kind == "ambient" && lowered.iter().any(|d| d.ambient_calls.contains(&e.name))).collect();
    ambient.sort_by(|a, b| a.name.cmp(&b.name));
    for e in ambient {
        // `ok` is set by `Report::finalize` from the run's verdict: the mirror
        // of an ambient function verifies only with the whole crate
        v.push(DeclStatus { name: e.name.clone(), kind: "ambient".into(), implemented: true, obligations: vec![], tokens: e.tokens.clone(), uses: e.uses.clone(), ok: false, weak: false });
    }
    v
}

/// Lower the specification for Verus.
fn lower(cfg: &Config, prog: &Program) -> Result<(TypeNames, Vec<Lowered>), String> {
    let tn = type_names(cfg, prog);
    let lowered = djinn_syntax::lower_verus::lower_program(prog, &tn).map_err(|e| crate::verify::fail_at(cfg, e))?;
    Ok((tn, lowered))
}

/// The real crate must depend on `vstd` (which brings the `verus!` macro, so
/// that the solution — written inside `verus! { … }` — compiles with its
/// ghost code erased).
fn check_manifest(cfg: &Config) -> Result<(), String> {
    let text = fs::read_to_string(cfg.crate_dir.join("Cargo.toml")).map_err(|e| e.to_string())?;
    let toml: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    let has = toml.get("dependencies").and_then(|d| d.get("vstd")).is_some();
    if !has {
        return Err(format!(
            "the Verus backend needs the crate to depend on `vstd`, so that the solution (written inside `verus! {{ … }}`) compiles with its ghost code erased. Add to {}:\n\n[dependencies]\nvstd = \"{VSTD_VERSION}\"\n\n(the version the installed Verus ships with; `cargo verus toolchain list` shows it)",
            cfg.rel(&cfg.crate_dir.join("Cargo.toml"))
        ));
    }
    Ok(())
}

/// The `vstd` crates.io version matching the Verus release the backend was
/// developed against.
pub const VSTD_VERSION: &str = "=0.0.0-2026-10-25-0158";

/// One mirrored specification module: its Rust items (verbatim), the stubs,
/// and what it exports.
struct Mirror {
    module: Option<String>,
    file: PathBuf,
    /// Lines of the file (the stubs' line ranges are recorded in `stubs`).
    text: String,
    /// obligation name → (first line, last line), 1-based, of its stub
    stubs: Vec<(String, usize, usize)>,
    /// The names the module defines: types, constants, implemented fns.
    names: Vec<String>,
}

/// What a specification file contributes to its mirror.
struct MirrorItems {
    /// `struct`s, `enum`s (with their attributes) and constants, inside `verus! { }`.
    items: Vec<String>,
    /// The names the module defines.
    names: Vec<String>,
    /// The ambient functions the constraints call: (name, the function with
    /// its translation as its contract).
    ambient: Vec<(String, String)>,
    /// The `use` items of the file (an ambient function's body may need them).
    uses: Vec<String>,
}

/// The items of a specification file the mirror copies: `struct`s, `enum`s
/// (with their attributes), the constants the specification may use, and the
/// ambient functions the constraints call (verbatim, with their translation
/// as their contract: `ambient_verus`). A table that is a slice constant
/// (`&[u8]`, `b"…"`) is mirrored as the array of its elements: Verus has no
/// slice constants, and `K[i]`, `K.len()`, `&K[..]` read the same either way
/// (a solution using it otherwise fails to compile in one of the two crates,
/// which is safe).
fn mirror_items(cfg: &Config, f: &SpecFile, prog: &Program, ambient: &[Translated]) -> Result<MirrorItems, String> {
    let src = fs::read_to_string(&f.path).map_err(|e| format!("{}: {e}", f.path.display()))?;
    let file: syn::File = syn::parse_str(&src).map_err(|e| format!("{}: {e}", cfg.rel(&f.path)))?;
    let mut out = MirrorItems { items: Vec::new(), names: Vec::new(), ambient: Vec::new(), uses: Vec::new() };
    for item in &file.items {
        match item {
            syn::Item::Struct(st) if prog.types.structs.contains_key(&st.ident.to_string()) => {
                out.items.push(item.to_token_stream().to_string());
                out.names.push(st.ident.to_string());
            }
            syn::Item::Enum(e) if prog.types.enums.contains_key(&e.ident.to_string()) => {
                out.items.push(item.to_token_stream().to_string());
                out.names.push(e.ident.to_string());
            }
            syn::Item::Const(c) => {
                let name = c.ident.to_string();
                let Some(k) = prog.types.consts.get(&name) else { continue };
                if let djinn_syntax::RType::Seq(e, kind) = &k.ty {
                    // a table: its elements as an array constant
                    let elems: Vec<String> = match (&k.table, &k.value.kind) {
                        (Some(t), _) => t.clone(),
                        (None, djinn_syntax::ExprKind::Str(b)) => b.iter().map(|x| x.to_string()).collect(),
                        _ => continue,
                    };
                    let elem = djinn_syntax::types::rust_type(e);
                    if matches!(kind, djinn_syntax::SeqKind::Array(_)) {
                        out.items.push(item.to_token_stream().to_string());
                    } else {
                        out.items.push(format!("{} const {name}: [{elem}; {}] = [{}];", c.vis.to_token_stream(), elems.len(), elems.join(", ")));
                    }
                    out.names.push(name);
                    continue;
                }
                out.items.push(item.to_token_stream().to_string());
                out.names.push(name);
            }
            syn::Item::Fn(func) => {
                let name = func.sig.ident.to_string();
                if let Some(t) = ambient.iter().find(|t| t.name == name) {
                    out.ambient.push((name.clone(), t.exec_fn.clone()));
                    out.names.push(name);
                }
            }
            syn::Item::Use(u) => {
                // every `use` of the file (an ambient function's body may name
                // what it imports: `use self::Kind::*`, `use std::cmp::min`), except
                // the specification macro's crate, which the verification crate does
                // not have (its `djinn!` blocks are lowered, not mirrored). A `use`
                // of a module the mirror does not copy fails to compile there, which
                // is the safe side.
                let first = match &u.tree {
                    syn::UseTree::Path(p) => p.ident.to_string(),
                    _ => String::new(),
                };
                if first != "djinn" {
                    out.uses.push(item.to_token_stream().to_string());
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

/// The mirrored specification modules and the root items.
fn mirrors(cfg: &Config, prog: &Program, lowered: &[Lowered], cx: &EmitCx, ambient: &[Translated]) -> Result<Vec<Mirror>, String> {
    let specs = cfg.specs();
    let mut out = Vec::new();
    for f in &specs {
        if let Some(m) = &f.module {
            if let Some(first) = m.split("::").next() {
                if RESERVED_MODULES.contains(&first) {
                    return Err(format!("{}: the module name `{first}` is reserved by the Verus backend's verification crate; rename the specification file", cfg.rel(&f.path)));
                }
            }
        }
        let MirrorItems { items, mut names, ambient: ambient_fns, uses } = mirror_items(cfg, f, prog, ambient)?;
        let mut stub_texts: Vec<(String, String)> = Vec::new();
        // the ambient functions first: their contracts are what the stubs'
        // relations refer to (any order works for Verus; this reads better)
        for (name, text) in ambient_fns {
            stub_texts.push((format!("ambient:{name}"), text));
        }
        for d in lowered.iter().filter(|d| prog.origin.get(&d.name).and_then(|&i| specs.get(i)) == Some(f)) {
            if d.kind != Kind::Func {
                continue;
            }
            match emit_verus::impl_stub(cx, d) {
                Some(t) => {
                    names.push(d.name.clone());
                    stub_texts.push((format!("{}.impl_correct", d.name), t));
                }
                None => stub_texts.push((String::new(), emit_verus::missing_stub(d))),
            }
        }
        let mut text = String::new();
        let children = child_modules(&specs, f.module.as_deref());
        let header = format!(
            "//! Mirror of `{}` (generated by `cargo djinn`, Verus backend). TRUSTED: do not edit.\n//! The specification's types and constants, verbatim, and one stub per implemented\n//! `fn`: the `fn` with its relation as its contract, delegating to the solution.\n//! The solution sees here what it sees in the real crate.\n",
            cfg.rel(&f.path)
        );
        text.push_str(&header);
        text.push_str("#![allow(unused_imports, dead_code, non_upper_case_globals, non_camel_case_types, unused_variables)]\nuse vstd::prelude::*;\n");
        for u in &uses {
            text.push_str(u);
            text.push('\n');
        }
        text.push_str(&children);
        text.push_str("\nverus! {\n\n");
        for it in &items {
            text.push_str(it);
            text.push_str("\n\n");
        }
        let mut stubs = Vec::new();
        for (ob, t) in &stub_texts {
            let start = text.lines().count() + 1;
            text.push_str(t);
            let end = text.lines().count();
            if !ob.is_empty() {
                stubs.push((ob.clone(), start, end));
            }
            text.push('\n');
        }
        text.push_str("} // verus!\n");
        let file = match &f.module {
            Some(m) => cfg.verus_src().join(format!("{}.rs", m.replace("::", "/"))),
            None => cfg.verus_src().join("lib.rs"),
        };
        out.push(Mirror { module: f.module.clone(), file, text, stubs, names });
    }
    Ok(out)
}

/// `pub mod child;` lines (and inline intermediate modules) for the
/// specification modules directly below `module`.
fn child_modules(specs: &[SpecFile], module: Option<&str>) -> String {
    let prefix = module.map(|m| format!("{m}::")).unwrap_or_default();
    // the relative paths of the spec modules below this one
    let below: Vec<Vec<String>> = specs
        .iter()
        .filter_map(|f| f.module.as_ref())
        .filter(|m| m.starts_with(&prefix) && m.len() > prefix.len())
        .map(|m| m[prefix.len()..].split("::").map(|s| s.to_string()).collect())
        .collect();
    fn render(below: &[Vec<String>], depth: usize, indent: &str) -> String {
        let mut out = String::new();
        let mut heads: Vec<String> = below.iter().filter_map(|p| p.get(depth).cloned()).collect();
        heads.sort();
        heads.dedup();
        for h in heads {
            let is_leaf = below.iter().any(|p| p.len() == depth + 1 && p[depth] == h);
            let deeper: Vec<Vec<String>> = below.iter().filter(|p| p.len() > depth + 1 && p[depth] == h).cloned().collect();
            if is_leaf {
                // the file declares its own children
                out.push_str(&format!("{indent}pub mod {h};\n"));
            } else {
                out.push_str(&format!("{indent}pub mod {h} {{\n{}{indent}}}\n", render(&deeper, depth + 1, &format!("{indent}    "))));
            }
        }
        out
    }
    render(&below, 0, "")
}

/// The real root's `pub use` items of specification modules, restricted to
/// names the mirrors define (a driver re-exported beside the `fn`s is not
/// mirrored).
fn root_reexports(cfg: &Config, mirrors: &[Mirror]) -> String {
    let root = ["src/lib.rs", "src/main.rs"].iter().map(|f| cfg.crate_dir.join(f)).find(|p| p.exists());
    let Some(root) = root else { return String::new() };
    let Ok(src) = fs::read_to_string(&root) else { return String::new() };
    let Ok(file) = syn::parse_file(&src) else { return String::new() };
    let known: HashMap<String, Vec<String>> = mirrors.iter().filter_map(|m| m.module.clone().map(|mm| (mm, m.names.clone()))).collect();
    let mut out = String::new();
    for item in &file.items {
        let syn::Item::Use(u) = item else { continue };
        if !matches!(u.vis, syn::Visibility::Public(_)) {
            continue;
        }
        // `pub use spec::X;`, `pub use spec::{a, b};`, `pub use spec::*;` (also `self::`/`crate::` first)
        let mut tree = &u.tree;
        let mut path: Vec<String> = Vec::new();
        loop {
            match tree {
                syn::UseTree::Path(p) => {
                    let seg = p.ident.to_string();
                    if !(path.is_empty() && (seg == "self" || seg == "crate")) {
                        path.push(seg);
                    }
                    tree = &p.tree;
                }
                _ => break,
            }
        }
        let module = path.join("::");
        let Some(names) = known.get(&module) else { continue };
        let leaves: Vec<String> = match tree {
            syn::UseTree::Glob(_) => vec!["*".into()],
            syn::UseTree::Name(n) if names.contains(&n.ident.to_string()) => vec![n.ident.to_string()],
            syn::UseTree::Rename(r) if names.contains(&r.ident.to_string()) => vec![format!("{} as {}", r.ident, r.rename)],
            syn::UseTree::Group(g) => g
                .items
                .iter()
                .filter_map(|t| match t {
                    syn::UseTree::Name(n) if names.contains(&n.ident.to_string()) => Some(n.ident.to_string()),
                    syn::UseTree::Rename(r) if names.contains(&r.ident.to_string()) => Some(format!("{} as {}", r.ident, r.rename)),
                    syn::UseTree::Glob(_) => Some("*".into()),
                    _ => None,
                })
                .collect(),
            _ => vec![],
        };
        if leaves.is_empty() {
            continue;
        }
        out.push_str(&format!("pub use {module}::{{{}}};\n", leaves.join(", ")));
    }
    out
}

/// `lib.rs` of the verification crate.
fn lib_rs(cfg: &Config, mirrors: &[Mirror], root_mirror: Option<&Mirror>) -> String {
    let mut s = String::new();
    s.push_str("//! The verification crate — generated by `cargo djinn` (Verus backend). TRUSTED: do not edit.\n");
    s.push_str("//! Regenerated on every `cargo djinn verify`. Verus verifies this crate: the solution\n//! (included from the real crate's work directory) against the relations, through the\n//! stubs of the mirrored specification modules, and the implementer's proofs against\n//! the pinned obligations.\n");
    s.push_str("#![allow(unused_imports, dead_code, unused_variables, unused_parens, non_snake_case, non_upper_case_globals, non_camel_case_types)]\n\n");
    s.push_str("use vstd::prelude::*;\n\n");
    s.push_str("pub mod vocab;\npub mod relations;\npub mod obligations;\n");
    let specs = cfg.specs();
    s.push_str(&child_modules(&specs, None));
    let sol = pathdiff(&cfg.solution_dir().join("mod.rs"), &cfg.verus_src());
    s.push_str(&format!("\n/// The implementer's Rust: the very file the real crate compiles.\n#[forbid(unsafe_code)]\n#[path = \"{sol}\"]\npub mod solution;\n\n/// The implementer's proofs.\npub mod proofs;\n\n"));
    s.push_str(&root_reexports(cfg, mirrors));
    if let Some(m) = root_mirror {
        // a specification in the crate root: its mirror is this file
        s.push_str("\n// ---- the specification items of the crate root\n");
        s.push_str(&m.text.lines().skip_while(|l| l.starts_with("//!") || l.starts_with("#![") || l.starts_with("use vstd")).collect::<Vec<_>>().join("\n"));
        s.push('\n');
    }
    s
}

/// A relative path from `dir` to `target` with `/` separators.
fn pathdiff(target: &Path, dir: &Path) -> String {
    let t: Vec<_> = target.components().collect();
    let d: Vec<_> = dir.components().collect();
    let common = t.iter().zip(d.iter()).take_while(|(a, b)| a == b).count();
    let mut parts: Vec<String> = (common..d.len()).map(|_| "..".to_string()).collect();
    parts.extend(t[common..].iter().map(|c| c.as_os_str().to_string_lossy().into_owned()));
    parts.join("/")
}

/// The generated files, as `translate` wrote them: file → (obligation name,
/// first line, last line) of every pinned obligation in it.
struct Generated {
    ranges: Vec<(PathBuf, String, usize, usize)>,
}

/// Emit the trusted files; the proof skeleton once. Returns the lowered
/// declarations and where each obligation lives.
fn write_trusted(cfg: &Config, prog: &Program, lowered: &[Lowered], names: &HashMap<String, String>, tn: &TypeNames, log: &mut Log) -> Result<Generated, String> {
    let cx = EmitCx { names: tn, impl_names: names };
    let src = cfg.verus_src();
    fs::create_dir_all(&src).map_err(|e| format!("{}: {e}", src.display()))?;
    let w = |p: &Path, text: &str| -> Result<(), String> {
        if let Some(d) = p.parent() {
            fs::create_dir_all(d).map_err(|e| format!("{}: {e}", d.display()))?;
        }
        fs::write(p, text).map_err(|e| format!("{}: {e}", p.display()))
    };
    let mut ranges = Vec::new();
    w(&src.join("vocab.rs"), &emit_verus::vocab_rs())?;
    // the ambient functions the constraints call, translated (and checked
    // against themselves in the mirrored modules)
    let mut used: Vec<String> = lowered.iter().flat_map(|d| d.ambient_calls.iter().cloned()).collect();
    used.sort();
    used.dedup();
    let ambient = djinn_syntax::ambient_verus::translate_all(&prog.types, &used, tn).map_err(|e| crate::verify::fail_at(cfg, e))?;
    w(&src.join("relations.rs"), &emit_verus::relations_rs_with(&cx, lowered, &ambient))?;
    // obligations.rs, with the line of every pinned proof fn
    let ob = emit_verus::obligations_rs(&cx, lowered);
    for d in lowered {
        for o in emit_verus::obligations(&cx, d) {
            if o.how != How::Proof {
                continue;
            }
            let decl = format!("pub proof fn {}(", o.fn_name);
            if let Some(i) = ob.find(&decl) {
                let start = ob[..i].lines().count() + 1;
                // to the closing brace of the body (the first `\n}` after the signature)
                let end = ob[i..].find("\n}").map(|j| ob[..i + j + 2].lines().count()).unwrap_or(start);
                ranges.push((src.join("obligations.rs"), o.name.clone(), start, end));
            }
        }
    }
    w(&src.join("obligations.rs"), &ob)?;
    // the mirrored specification modules
    let ms = mirrors(cfg, prog, lowered, &cx, &ambient)?;
    let root = ms.iter().find(|m| m.module.is_none());
    // stale mirrors (a specification file removed or renamed) are deleted
    // from `src/`: anything there that is neither generated now nor the
    // implementer's
    let keep: Vec<PathBuf> = ms.iter().map(|m| m.file.clone()).chain(["vocab.rs", "relations.rs", "obligations.rs", "lib.rs", "proofs.rs"].iter().map(|f| src.join(f))).collect();
    for f in crate::verify::rust_files(&src) {
        if !keep.contains(&f) && !f.starts_with(src.join("proofs")) {
            let _ = fs::remove_file(&f);
            log.line(&format!("removed the stale generated file {}", cfg.rel(&f)));
        }
    }
    for m in &ms {
        if m.module.is_none() {
            continue;
        }
        for (ob, a, b) in &m.stubs {
            ranges.push((m.file.clone(), ob.clone(), *a, *b));
        }
        w(&m.file, &m.text)?;
    }
    let lib = lib_rs(cfg, &ms, root);
    if let Some(m) = root {
        // the root mirror's stubs are at the end of lib.rs: find each
        for (ob, _, _) in &m.stubs {
            let fname = ob.trim_end_matches(".impl_correct").trim_start_matches("ambient:");
            let decl = if ob.starts_with("ambient:") { format!("fn {fname}(") } else { format!("pub fn {fname}(") };
            if let Some(i) = lib.find(&decl) {
                let start = lib[..i].lines().count() + 1;
                let end = lib[i..].find("\n}").map(|j| lib[..i + j + 2].lines().count()).unwrap_or(start);
                ranges.push((src.join("lib.rs"), ob.clone(), start, end));
            }
        }
    }
    w(&src.join("lib.rs"), &lib)?;
    // the implementer's file: the skeleton once, then stubs for new
    // obligations and refreshed untouched stubs
    let proofs = cfg.proof_main();
    if !proofs.exists() {
        w(&proofs, &emit_verus::proofs_skeleton(&cx, lowered))?;
        log.line(&format!("wrote initial {} (never overwritten)", cfg.rel(&proofs)));
    } else {
        let text0 = fs::read_to_string(&proofs).map_err(|e| e.to_string())?;
        let current: Vec<Obligation> = lowered.iter().flat_map(|d| emit_verus::obligations(&cx, d)).filter(|o| o.how == How::Proof).collect();
        let (mut text, refreshed, missing) = refresh_stubs(&text0, &current);
        if !refreshed.is_empty() {
            log.line(&format!("refreshed {} untouched stub(s) in {} whose statement changed: {}", refreshed.len(), cfg.rel(&proofs), refreshed.join(", ")));
        }
        if !missing.is_empty() {
            let mut add = String::from("// ---- obligations added by a later `translate` (specification changed)\n\n");
            for o in &missing {
                add.push_str(&emit_verus::stub_text(o));
            }
            text = match text.rfind(emit_verus::END_MARKER) {
                Some(i) => format!("{}{}{}", &text[..i], add, &text[i..]),
                None => format!("{text}\nverus! {{\n\n{add}{}", emit_verus::END_MARKER),
            };
            log.line(&format!("added {} stub(s) to {} for new obligations: {}", missing.len(), cfg.rel(&proofs), missing.iter().map(|o| o.name.clone()).collect::<Vec<_>>().join(", ")));
        }
        if !refreshed.is_empty() || !missing.is_empty() {
            w(&proofs, &text)?;
        }
    }
    Ok(Generated { ranges })
}

/// The implementer's proof file against the current obligations: a stub still
/// untouched (its whole body the skeleton's TODO marker, `body_is_todo`) whose
/// statement is no longer the obligation's is replaced by the current stub; an
/// obligation without a `proof fn` gets one appended. A function with any
/// proof in it is never touched. Returns the new text, the names of the
/// refreshed functions and the obligations added.
fn refresh_stubs<'a>(text: &str, current: &'a [Obligation]) -> (String, Vec<String>, Vec<&'a Obligation>) {
    let items = fn_items(text);
    let mut refreshed = Vec::new();
    let mut missing: Vec<&'a Obligation> = Vec::new();
    // (byte range, replacement), applied from the back so offsets stay valid
    let mut edits: Vec<(usize, usize, String)> = Vec::new();
    for o in current {
        match items.get(&o.fn_name) {
            None => missing.push(o),
            Some(it) => {
                let old = &text[it.start..it.end];
                let stub = emit_verus::stub_text(o);
                if body_is_todo(old) && old.trim_end() != stub.trim_end() {
                    edits.push((it.start, it.end, stub));
                    refreshed.push(o.fn_name.clone());
                }
            }
        }
    }
    let mut text = text.to_string();
    edits.sort_by_key(|e| std::cmp::Reverse(e.0));
    for (a, b, new) in edits {
        text.replace_range(a..b, &new);
    }
    (text, refreshed, missing)
}

/// Is a function item's whole body the skeleton's TODO marker — no proof
/// begun? The body is the last balanced brace group of the item (a
/// `requires`/`ensures` clause may hold braces of its own).
fn body_is_todo(item: &str) -> bool {
    let t = item.trim_end();
    if !t.ends_with('}') {
        return false;
    }
    let bytes = t.as_bytes();
    let mut depth = 0i32;
    let mut i = bytes.len();
    let mut open = None;
    while i > 0 {
        i -= 1;
        match bytes[i] {
            b'}' => depth += 1,
            b'{' => {
                depth -= 1;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    match open {
        Some(i) => t[i + 1..t.len() - 1].trim() == emit_verus::TODO,
        None => false,
    }
}

/// One `fn`/`proof fn` item of a Verus file: its byte range from the
/// declaration line (after any doc comments and attributes) to the end of its
/// segment, and its 1-based line span (the whole segment).
#[derive(Clone, Copy, Debug)]
struct FnItem {
    start: usize,
    end: usize,
    line_start: usize,
    line_end: usize,
}

/// fn name → its item, for every `proof fn`/`fn` of a file, by its segments
/// (`verus_segments`).
fn fn_items(text: &str) -> HashMap<String, FnItem> {
    let mut m = HashMap::new();
    let mut line = 1usize;
    let mut off = 0usize;
    for seg in verus_segments(text) {
        let n = seg.lines().count();
        let mut local = 0usize;
        for l in seg.split_inclusive('\n') {
            if let Some(rest) = l.trim_start().strip_prefix("pub proof fn ").or_else(|| l.trim_start().strip_prefix("proof fn ")).or_else(|| l.trim_start().strip_prefix("pub fn ")).or_else(|| l.trim_start().strip_prefix("fn ")) {
                let name = rest.split(|c: char| c == '(' || c == '<' || c.is_whitespace()).next().unwrap_or("").to_string();
                m.insert(name, FnItem { start: off + local, end: off + seg.len(), line_start: line, line_end: line + n.saturating_sub(1) });
                break;
            }
            local += l.len();
        }
        line += n;
        off += seg.len();
    }
    m
}

/// Declarations that left the specification: their proof functions (and
/// helpers mentioning them) move to `.djinnscratch/backup/<time>-stale/`, so
/// the crate keeps verifying; so do their Rust implementations.
fn archive_stale(cfg: &Config, lowered: &[Lowered], log: &mut Log, archive_rust: bool) -> Result<(), String> {
    let current: std::collections::HashSet<&str> = lowered.iter().map(|d| d.name.as_str()).collect();
    let mut removed: Vec<String> = Vec::new();
    let mut removed_funcs: Vec<String> = Vec::new();
    if let Some(r) = Report::load(cfg) {
        for d in &r.declarations {
            if d.kind != "ambient" && !current.contains(d.name.as_str()) {
                removed.push(d.name.clone());
                if d.kind == "func" {
                    removed_funcs.push(d.name.clone());
                }
            }
        }
    }
    // (the names come from the previous report only: a helper the implementer
    // named `lemma_wf` or `index_unambiguous` is not an obligation of a
    // declaration `lemma` or `index`)
    let proofs = cfg.proof_main();
    let text = fs::read_to_string(&proofs).unwrap_or_default();
    let prefixes = path_prefixes(cfg);
    let mut stale_rs = String::new();
    let mut notes = Vec::new();
    if !removed.is_empty() && !text.is_empty() {
        let (kept, stale, n) = split_stale(&text, &removed, &prefixes);
        stale_rs = stale;
        if n > 0 {
            fs::write(&proofs, kept).map_err(|e| e.to_string())?;
            notes.push(format!("{n} item(s) of {} about removed {}", cfg.rel(&proofs), removed.iter().map(|r| format!("`{r}`")).collect::<Vec<_>>().join(", ")));
        }
    }
    let (removed_funcs, cut) = crate::verify::archive_rust_fns(cfg, removed_funcs, log, archive_rust)?;
    if !cut.is_empty() {
        notes.push(format!("{} Rust function(s) implementing removed {}", removed_funcs.len(), removed_funcs.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")));
    }
    if notes.is_empty() {
        return Ok(());
    }
    let dir = cfg.state_dir().join("backup").join(format!("{}-stale", id_time(now())));
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    if !stale_rs.is_empty() {
        fs::write(dir.join("proofs.stale.rs"), format!("// Removed from proofs.rs by `cargo djinn translate` because the specification\n// no longer has the declarations they concern.\n\n{stale_rs}")).map_err(|e| e.to_string())?;
    }
    if !cut.is_empty() {
        fs::write(dir.join("solution.stale.rs"), format!("//! Removed from the solution by `cargo djinn translate`: implementations of\n//! functions the specification no longer declares.\n\n{cut}")).map_err(|e| e.to_string())?;
    }
    log.line(&format!("archived to {}: {}", cfg.rel(&dir), notes.join("; ")));
    Ok(())
}

/// Split a Verus file into top-level segments: each item (`proof fn`, `fn`,
/// `spec fn`, `impl`, …) with the attributes and doc comments before it.
fn verus_segments(text: &str) -> Vec<String> {
    const STARTS: &[&str] = &["pub ", "fn ", "proof ", "spec ", "exec ", "open ", "closed ", "broadcast ", "uninterp ", "impl", "struct ", "enum ", "const ", "static ", "type ", "trait ", "mod ", "use ", "#[", "#![", "///", "//!", "//", "verus!", "} // verus!", "macro_rules", "global "];
    const PREFIX: &[&str] = &["#[", "///", "//"];
    let mut segs: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut prefix_only = false;
    for line in text.split_inclusive('\n') {
        let starts = !line.starts_with(' ') && !line.starts_with('\t') && STARTS.iter().any(|k| line.starts_with(k));
        if starts && !cur.is_empty() && !prefix_only {
            segs.push(std::mem::take(&mut cur));
        }
        if starts {
            prefix_only = PREFIX.iter().any(|k| line.starts_with(k));
        }
        cur.push_str(line);
    }
    if !cur.is_empty() {
        segs.push(cur);
    }
    segs
}

/// A segment holding a function, type or impl (not a `use`, a comment, or the
/// `verus!` brackets).
fn removable(seg: &str) -> bool {
    let first = seg.lines().find(|l| !(l.starts_with("#[") || l.starts_with("///") || l.starts_with("//") || l.trim().is_empty()));
    matches!(first, Some(l) if ["pub ", "fn ", "proof ", "spec ", "exec ", "open ", "closed ", "broadcast ", "uninterp ", "impl", "struct ", "enum ", "const ", "type ", "trait "].iter().any(|k| l.starts_with(k)))
}

/// The paths under which a declaration's implementation and stub live:
/// `crate::solution::`, and the mirrored specification modules
/// (`crate::spec::`, `crate::` for a specification in the crate root).
fn path_prefixes(cfg: &Config) -> Vec<String> {
    let mut v = vec!["crate::solution::".to_string()];
    for f in cfg.specs() {
        v.push(format!("{}::", module_path(f.module.as_deref())));
    }
    v.sort();
    v.dedup();
    v
}

/// The segments of the proof file about removed declarations, taken out:
/// (what stays, what was removed with a note each, how many).
fn split_stale(text: &str, removed: &[String], prefixes: &[String]) -> (String, String, usize) {
    let mut kept = String::new();
    let mut stale = String::new();
    let mut n = 0usize;
    for seg in verus_segments(text) {
        match mentions(&seg, removed, prefixes) {
            Some(name) if removable(&seg) => {
                n += 1;
                stale.push_str(&format!("// stale: mentions removed declaration `{name}`\n{seg}\n"));
            }
            _ => kept.push_str(&seg),
        }
    }
    (kept, stale, n)
}

/// Does a segment concern one of the removed declarations: declare or
/// mention `name_spec`, `name_pre`, `name_body`, an obligation of it, or its
/// stub or implementation by path (`crate::solution::name`,
/// `crate::spec::name`: one of `prefixes`; `vstd::math::min` is not a
/// mention of a removed `min`)?
fn mentions(seg: &str, removed: &[String], prefixes: &[String]) -> Option<String> {
    for word in seg.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == ':')) {
        let full = word.trim_matches(':');
        let w = full.rsplit("::").next().unwrap_or(full);
        for n in removed {
            let own = ["_spec", "_pre", "_body", "_unambiguous", "_wf", "_exists"].iter().any(|s| w == format!("{n}{s}"));
            let ens = w.strip_prefix(&format!("{n}_ens_")).is_some_and(|i| !i.is_empty() && i.bytes().all(|b| b.is_ascii_digit()));
            let path = full.contains("::") && prefixes.iter().any(|p| full == format!("{p}{n}"));
            if own || ens || path {
                return Some(n.clone());
            }
        }
    }
    None
}

/// Emit the trusted Verus files (and the proof skeleton once).
pub fn translate_opts(cfg: &Config, log: &mut Log, archive_rust: bool) -> Result<Vec<Lowered>, String> {
    let prog = crate::verify::parse_spec(cfg)?;
    let (tn, lowered) = lower(cfg, &prog)?;
    // before anything is written: a crate without `vstd` cannot use the backend
    check_manifest(cfg)?;
    fs::create_dir_all(cfg.solution_dir()).map_err(|e| e.to_string())?;
    if !cfg.solution_dir().join("mod.rs").exists() {
        fs::write(cfg.solution_dir().join("mod.rs"), "//! LLM-owned: the implementation of the `func`s of the specification, inside `verus! { … }`.\nuse vstd::prelude::*;\n\nverus! {\n\n} // verus!\n").map_err(|e| e.to_string())?;
    }
    crate::verify::gate_build_script(cfg, log)?;
    archive_stale(cfg, &lowered, log, archive_rust)?;
    let names = impl_names(cfg);
    write_trusted(cfg, &prog, &lowered, &names, &tn, log)?;
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
    fs::create_dir_all(cfg.state_dir()).map_err(|e| format!("{}: {e}", cfg.state_dir().display()))?;
    fs::write(cfg.guide_path(), crate::guide_verus::guide(cfg, &lowered, &names)).map_err(|e| format!("{}: {e}", cfg.guide_path().display()))?;
    log.line(&format!("translated {} declarations into {}", lowered.len(), cfg.rel(&cfg.verus_src())));
    Ok(lowered)
}

// ------------------------------------------------------------------ the audit

/// Identifiers the implementer's files may not contain: ways to make the
/// verified code differ from the compiled code (`cfg`, `include!`, …), to
/// take items out of Verus's sight (`external*`), to weaken what it checks
/// (`exec_allows_no_decreases_clause`, `trusted`, `accept_recursive_types`,
/// `when_used_as_spec`), or to assume (`assume`, `admit`, `axiom`,
/// `assume_specification`: also refused by `--no-cheating`).
const BANNED_IDENTS: &[&str] = &[
    "unsafe", "assume", "admit", "axiom", "assume_specification", "external", "external_body", "external_fn_specification", "external_type_specification", "external_trait_specification", "external_trait_blanket", "external_trait_extension", "external_derive",
    "exec_allows_no_decreases_clause", "assume_termination", "trusted", "accept_recursive_types", "when_used_as_spec", "inline_air_stmt", "macro_rules", "macro_export", "cfg", "cfg_attr", "extern", "no_mangle", "link_section", "export_name", "link_name",
    "global_allocator", "panic_handler", "no_std", "no_core", "feature",
    // global mutable state: Verus accepts `exec static X: AtomicU32 …` with
    // vstd's atomic specs, a side effect no relation constrains (the
    // lifetime `'static` is a different token and stays allowed)
    "static",
    // a destructor: code that runs at a point no relation constrains, and —
    // written outside `verus! { }` for a type declared inside it — code Verus
    // never sees (it can print, write files, …)
    "Drop",
    // `vstd::pervasive::print_u64` is an `external_body` function that prints,
    // callable from verified code; `pervasive` also holds `unreached`, …
    "pervasive", "print_u64",
];

/// Macros whose expansion depends on where and how the file is compiled.
const BANNED_MACROS: &[&str] = &["include", "include_str", "include_bytes", "env", "option_env", "cfg", "file", "line", "column", "module_path", "concat", "stringify", "compile_error"];

/// Refuse the implementer's files that use an escape hatch (see `BANNED_IDENTS`).
/// Every regular file under the solution directory, `proofs.rs` and `proofs/`
/// is read, whatever its name: rustc (and Verus) compile a `#[path =
/// "impl.txt"]` module too, so a file that is not Rust fails the audit
/// (`verify::audit_file`), and a `#[path]`/`include!` target must be an
/// `.rs` file inside these directories (`project::solution_escapes`).
pub fn audit_sources(cfg: &Config) -> Result<(), String> {
    let sol = cfg.solution_dir();
    let main = cfg.proof_main();
    let helpers = cfg.proof_helpers();
    let src = cfg.verus_src();
    let mut files = crate::verify::all_files(&sol);
    if main.exists() {
        files.push(main.clone());
    }
    files.extend(crate::verify::all_files(&helpers));
    let dirs: [&Path; 3] = [&sol, &main, &helpers];
    for f in files {
        let bytes = fs::read(&f).map_err(|e| format!("FAIL: {}: {e}", cfg.rel(&f)))?;
        let ts = crate::verify::audit_file(cfg, &f, &bytes, &dirs)?;
        // the proof files resolve `mod helper;` and `#[path]` inside `src/`
        let root = if f.starts_with(&sol) { &sol } else { &src };
        djinn_syntax::project::solution_escapes(root, &f, &bytes).map_err(|e| format!("FAIL: {}", e.replace(&format!("{}/", cfg.crate_dir.display()), "")))?;
        if let Some(why) = banned(ts) {
            return Err(format!("FAIL: {} uses {why}, which the Verus backend does not allow in the implementer's files (it could change what is verified or what is compiled)", cfg.rel(&f)));
        }
    }
    Ok(())
}

fn banned(ts: proc_macro2::TokenStream) -> Option<String> {
    use proc_macro2::TokenTree;
    let trees: Vec<TokenTree> = ts.into_iter().collect();
    for (i, t) in trees.iter().enumerate() {
        match t {
            TokenTree::Ident(id) => {
                let name = id.to_string();
                let name = name.strip_prefix("r#").unwrap_or(&name).to_string();
                // the lifetime `'static` is a `'` punct then the ident `static`
                let lifetime = i > 0 && matches!(&trees[i - 1], TokenTree::Punct(p) if p.as_char() == '\'');
                if BANNED_IDENTS.contains(&name.as_str()) && !lifetime {
                    return Some(match name.as_str() {
                        "static" => "a `static` item (global state is a side effect no relation constrains)".to_string(),
                        "Drop" => "`Drop` (a destructor runs at a point no relation constrains, and an `impl Drop` outside `verus! { }` is code Verus never verifies: it could print or write files from a verified function)".to_string(),
                        "pervasive" | "print_u64" => format!("`{name}` (`vstd::pervasive::print_u64` prints from verified code; nothing in `vstd::pervasive` is for the implementer)"),
                        _ => format!("`{name}`"),
                    });
                }
                let next_bang = matches!(trees.get(i + 1), Some(TokenTree::Punct(p)) if p.as_char() == '!');
                if next_bang && BANNED_MACROS.contains(&name.as_str()) {
                    return Some(format!("`{name}!`"));
                }
                if name == "global" {
                    if let Some(TokenTree::Ident(n)) = trees.get(i + 1) {
                        if n == "size_of" || n == "layout" || n == "align_of" {
                            return Some("a `global` layout directive".into());
                        }
                    }
                }
            }
            TokenTree::Group(g) => {
                if let Some(w) = banned(g.stream()) {
                    return Some(w);
                }
            }
            _ => {}
        }
    }
    None
}

// ------------------------------------------------------------------ verify

/// A cap on each Z3 instance's memory (MiB): a runaway query (one took
/// 9.5 GiB twice over in example/utf8) fails as an error instead of taking
/// the machine's memory from every other run. It only ever turns a result
/// into an error, never an error into a PASS.
pub(crate) const Z3_MEMORY: [&str; 2] = ["--smt-option", "memory_max_size=6144"];

/// Run Verus on the verification crate.
fn run_verus(cfg: &Config, log: &mut Log) -> Result<String, (String, String)> {
    let mut cmd = Command::new(&cfg.verus);
    cmd.arg("--crate-type=lib")
        .arg("src/lib.rs")
        .arg(format!("--edition={}", cfg.edition))
        .arg("--crate-name")
        .arg(format!("{}_verus", cfg.crate_name.replace('-', "_")))
        .args(["--no-cheating", "--multiple-errors", "4", "--triggers-mode", "silent", "--no-report-long-running"])
        .args(Z3_MEMORY)
        .current_dir(&cfg.verus_dir);
    // `verus` runs `rustup`, which lives beside `cargo`
    if let Some(home) = std::env::var_os("HOME") {
        let cargo_bin = Path::new(&home).join(".cargo").join("bin");
        if cargo_bin.is_dir() {
            let mut path = cargo_bin.into_os_string();
            if let Some(p) = std::env::var_os("PATH") {
                path.push(":");
                path.push(p);
            }
            cmd.env("PATH", path);
        }
    }
    log.line(&format!("== verus ({} src/lib.rs)", cfg.rel(&cfg.verus_dir)));
    let out = cmd.output().map_err(|e| ("verus".to_string(), format!("verus: cannot run `{}`: {e}\n(set [package.metadata.djinn] verus = \"path/to/verus\", or DJINN_VERUS, or put `verus` on PATH)", cfg.verus)))?;
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    Ok(format!("{}\n@@exit {}", text, out.status.code().unwrap_or(-1)))
}

/// Verus's output, read strictly: the `verification results:: N verified, M
/// errors` line must be there, with `M == 0`, `N` at least the number of
/// functions we rely on, and the exit status 0. Anything else fails.
struct Verdict {
    ok: bool,
    verified: usize,
    errors: usize,
    /// (file, line) of each error's primary location, with its message
    located: Vec<(PathBuf, usize, String)>,
    /// Error blocks without a location
    other: Vec<String>,
}

fn parse_verus(out: &str, cwd: &Path) -> Verdict {
    let mut verified = None;
    let mut errors = None;
    let mut exit: i32 = -1;
    let mut located = Vec::new();
    let mut other = Vec::new();
    let lines: Vec<&str> = out.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let l = lines[i];
        if let Some(rest) = l.strip_prefix("verification results:: ") {
            // `N verified, M errors` (maybe followed by a note)
            let mut it = rest.split(|c: char| !c.is_ascii_digit()).filter(|s| !s.is_empty());
            verified = it.next().and_then(|n| n.parse().ok());
            errors = it.next().and_then(|n| n.parse().ok());
        } else if let Some(rest) = l.strip_prefix("@@exit ") {
            exit = rest.trim().parse().unwrap_or(-1);
        } else if l.starts_with("error") && !l.starts_with("error: aborting due to") {
            // the message, then the location on the next `-->` line (if any)
            let msg = l.to_string();
            let mut j = i + 1;
            let mut loc = None;
            // (a `warning:` block between the message and its `-->` — rustc
            // diagnostics are not always contiguous — does not end the block
            // before the location is found)
            while j < lines.len() && !lines[j].starts_with("error") && !(lines[j].starts_with("warning") && loc.is_some()) && !lines[j].starts_with("verification results") {
                if let Some(arrow) = lines[j].trim_start().strip_prefix("--> ") {
                    if loc.is_none() {
                        let mut parts = arrow.rsplitn(3, ':');
                        let _col = parts.next();
                        let line = parts.next().and_then(|n| n.parse::<usize>().ok());
                        let file = parts.next().map(|f| cwd.join(f));
                        if let (Some(f), Some(n)) = (file, line) {
                            loc = Some((f, n));
                        }
                    }
                }
                j += 1;
            }
            // the full block, for the report
            let block = lines[i..j].join("\n");
            match loc {
                Some((f, n)) => located.push((f, n, block)),
                None => other.push(msg),
            }
            i = j;
            continue;
        }
        i += 1;
    }
    let ok = exit == 0 && errors == Some(0) && verified.is_some() && located.is_empty() && other.is_empty();
    Verdict { ok, verified: verified.unwrap_or(0), errors: errors.unwrap_or(usize::MAX), located, other }
}

pub fn verify(cfg: &Config, jail: Option<&Path>, log: &mut Log, mut report: Report) -> Report {
    let start = now();
    let result = verify_inner(cfg, jail, log, &mut report);
    match result {
        Ok(()) => {
            report.pass = true;
            report.stage = "done".into();
            let missing = report.unimplemented();
            if missing.is_empty() {
                log.line("PASS");
            } else {
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

fn verify_inner(cfg: &Config, jail: Option<&Path>, log: &mut Log, report: &mut Report) -> Result<(), (String, String)> {
    let stage = |s: &str, e: String| (s.to_string(), e);
    // 0. the specification itself
    let lowered = crate::verify::lower_spec(cfg).map_err(|e| stage("specification", e))?;
    report.declarations = decl_statuses(cfg, &lowered, &impl_names(cfg));
    for d in &report.declarations {
        for o in &d.obligations {
            report.obligations.insert(o.clone(), "unverified".into());
        }
    }
    if let Some(j) = jail {
        for note in jail::sync_back(cfg, j).map_err(|e| stage("jail sync", e))? {
            log.line(&note);
        }
        report.declarations = decl_statuses(cfg, &lowered, &impl_names(cfg));
    }
    let sources = crate::verify::source_snapshot(cfg);
    // 1. the real crate builds: the signatures of spec and solution agree, and
    // the solution compiles with its ghost code erased
    crate::verify::run(Command::new("cargo").args(["build", "--quiet"]).env("DJINN_VERIFYING", "1").current_dir(&cfg.crate_dir), "cargo build", log).map_err(|e| stage("cargo build", e))?;
    // 1b. only safe Rust, and no escape hatch in the implementer's files
    crate::verify::check_safe(cfg).map_err(|e| stage("unsafe", e))?;
    audit_sources(cfg).map_err(|e| stage("escape hatch", e))?;
    // 2. regenerate the trusted files
    let prog = crate::verify::parse_spec(cfg).map_err(|e| stage("specification", e))?;
    let (tn, lowered) = lower(cfg, &prog).map_err(|e| stage("specification", e))?;
    check_manifest(cfg).map_err(|e| stage("translate", e))?;
    fs::create_dir_all(cfg.solution_dir()).map_err(|e| stage("translate", e.to_string()))?;
    crate::verify::gate_build_script(cfg, log).map_err(|e| stage("translate", e))?;
    archive_stale(cfg, &lowered, log, jail.is_none()).map_err(|e| stage("translate", e))?;
    if crate::verify::source_snapshot(cfg) != sources {
        return Err(stage("translate", "the solution changed during translate (archived functions): verify again".into()));
    }
    let names = impl_names(cfg);
    let generated = write_trusted(cfg, &prog, &lowered, &names, &tn, log).map_err(|e| stage("translate", e))?;
    fs::write(cfg.guide_path(), crate::guide_verus::guide(cfg, &lowered, &names)).map_err(|e| stage("translate", e.to_string()))?;
    report.declarations = decl_statuses(cfg, &lowered, &names);
    report.obligations.clear();
    for d in &report.declarations {
        for o in &d.obligations {
            report.obligations.insert(o.clone(), "unverified".into());
        }
    }
    // 3. what this verify attests
    report.evidence = crate::verify::evidence(cfg);
    if let Some(why) = report.evidence.strip_prefix("invalid: ") {
        return Err(stage("evidence", format!("FAIL: the solution and proof files cannot be fingerprinted: {why}")));
    }
    // 4. verus
    let out = run_verus(cfg, log)?;
    let v = parse_verus(&out, &cfg.verus_dir);
    let cx = EmitCx { names: &tn, impl_names: &names };
    let expected: usize = lowered.iter().flat_map(|d| emit_verus::obligations(&cx, d)).filter(|o| matches!(o.how, How::Proof | How::Impl)).count();
    if v.ok && v.verified < expected {
        return Err(stage("verus", format!("FAIL: verus reports {} verified functions, fewer than the {expected} obligations: the verification crate is not what translate wrote", v.verified)));
    }
    if v.ok {
        for o in report.obligations.values_mut() {
            *o = "proved".into();
        }
        log.line(&format!("verus: {} verified, 0 errors", v.verified));
    } else {
        // which obligations the errors fall on: a pinned wrapper or stub (by the
        // generated ranges), or the implementer's own `proof fn` of an obligation
        // in proofs.rs (by its item span, as `local_states` does)
        let mut hit: Vec<String> = Vec::new();
        let mut ambient_hit: Vec<String> = Vec::new();
        // an error in obligations.rs/relations.rs/vocab.rs outside every range
        let mut trusted_hit = false;
        // an error in a mirrored specification module (`src/<spec>.rs`, `lib.rs`)
        let mut mirror_hit = false;
        // an unresolved name in the solution: likely something the mirror does not copy
        let mut unresolved_in_solution = false;
        let canon = |p: &Path| p.canonicalize().unwrap_or(p.to_path_buf());
        let proofs_text = fs::read_to_string(cfg.proof_main()).unwrap_or_default();
        let items = fn_items(&proofs_text);
        let by_fn: HashMap<String, String> = lowered.iter().flat_map(|d| emit_verus::obligations(&cx, d)).filter(|o| o.how == How::Proof).map(|o| (o.fn_name.clone(), o.name.clone())).collect();
        let src = canon(&cfg.verus_src());
        let own = canon(&cfg.proof_main());
        let helpers = canon(&cfg.proof_helpers());
        let sol = canon(&cfg.solution_dir());
        let core: Vec<PathBuf> = ["obligations.rs", "relations.rs", "vocab.rs"].iter().map(|f| canon(&cfg.verus_src().join(f))).collect();
        for (f, line, block) in &v.located {
            let fc = canon(f);
            let mut found = false;
            for (gf, ob, a, b) in &generated.ranges {
                if canon(gf) == fc && *line >= *a && *line <= *b {
                    if let Some(name) = ob.strip_prefix("ambient:") {
                        ambient_hit.push(name.to_string());
                    } else {
                        hit.push(ob.clone());
                    }
                    found = true;
                }
            }
            if !found && fc == own {
                if let Some((name, _)) = items.iter().find(|(_, it)| *line >= it.line_start && *line <= it.line_end) {
                    if let Some(ob) = by_fn.get(name) {
                        hit.push(ob.clone());
                        found = true;
                    }
                }
            }
            if !found && fc.starts_with(&src) && fc != own && !fc.starts_with(&helpers) && !fc.starts_with(&sol) {
                if core.contains(&fc) {
                    trusted_hit = true;
                } else {
                    mirror_hit = true;
                }
            }
            if fc.starts_with(&sol) && ["cannot find", "unresolved import", "failed to resolve", "no function or associated item", "no method named", "not found in"].iter().any(|k| block.contains(k)) {
                unresolved_in_solution = true;
            }
        }
        for (name, st) in report.obligations.iter_mut() {
            if hit.contains(name) {
                *st = "error".into();
            }
        }
        let shown: Vec<String> = v.located.iter().map(|(_, _, b)| b.clone()).chain(v.other.iter().cloned()).collect();
        report.errors = shown.iter().flat_map(|b| b.lines().filter(|l| l.starts_with("error")).map(|s| s.to_string())).collect();
        let body = shown.iter().take(12).cloned().collect::<Vec<_>>().join("\n\n");
        let summary = if v.errors == usize::MAX { "verus did not finish (no `verification results` line)".to_string() } else { format!("verus: {} verified, {} errors", v.verified, v.errors) };
        let mut hint = String::new();
        if trusted_hit {
            hint.push_str("\n(an error in a generated file: the Verus backend could not state this specification — report it)");
        }
        if mirror_hit || unresolved_in_solution {
            hint.push_str(&format!(
                "\n({}the mirror of a specification module in the verification crate copies only its `struct`s, `enum`s, `const`s, `use` items and the ambient functions the constraints call, plus one stub per implemented `fn`; a solution that calls an `impl` method, a type alias, a trait, a macro or another module of the specification file compiles in the real crate but not here. Keep what the solution needs in the solution, or make it one of those items)",
                if mirror_hit { "an error in a mirrored specification module: " } else { "an unresolved name in the solution: " }
            ));
        }
        ambient_hit.sort();
        ambient_hit.dedup();
        for name in &ambient_hit {
            hint.push_str(&format!("\n(the ambient function `{name}` of the specification file does not verify: Verus must prove that it terminates, never panics — no overflow, no division by zero, no `unwrap` of `None` — and returns what its translation `{}` says, for every input. Fix the function in the specification file; the solution is not at fault)", djinn_syntax::lower_verus::ambient_spec_name(name)));
        }
        return Err(stage("verus", format!("FAIL: {summary}{hint}\n{body}\n{}", out.lines().filter(|l| l.starts_with("verification results")).collect::<Vec<_>>().join("\n"))));
    }
    // 5. the files verified are still the files on disk
    let after = crate::verify::evidence(cfg);
    if after != report.evidence {
        return Err(stage("evidence", "FAIL: the solution or proof files changed while they were being verified; verify again".into()));
    }
    if crate::verify::source_snapshot(cfg) != sources {
        return Err(stage("evidence", "FAIL: the crate's sources changed while they were being verified; verify again".into()));
    }
    Ok(())
}

/// The local assessment `status` shows between verifies: Verus run on the
/// project as it is (no cargo build, no sync), each proof obligation
/// classified. `None` if Verus could not be run.
pub fn local_states(cfg: &Config, proofs_root: &Path, timeout_secs: u64) -> Option<HashMap<String, crate::status::ObState>> {
    use crate::status::ObState;
    let text = fs::read_to_string(proofs_root.join("src").join("proofs.rs")).ok()?;
    let lowered = crate::verify::lower_spec(cfg).ok()?;
    let names = impl_names(cfg);
    let tn = crate::verify::parse_spec(cfg).map(|p| type_names(cfg, &p)).ok()?;
    let cx = EmitCx { names: &tn, impl_names: &names };
    let mut cmd = Command::new(&cfg.verus);
    cmd.arg("--crate-type=lib").arg("src/lib.rs").arg(format!("--edition={}", cfg.edition)).args(["--no-cheating", "--multiple-errors", "2", "--triggers-mode", "silent", "--no-report-long-running"]).args(Z3_MEMORY).current_dir(proofs_root).stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped());
    if let Some(home) = std::env::var_os("HOME") {
        let cargo_bin = Path::new(&home).join(".cargo").join("bin");
        let mut path = cargo_bin.into_os_string();
        if let Some(p) = std::env::var_os("PATH") {
            path.push(":");
            path.push(p);
        }
        cmd.env("PATH", path);
    }
    let mut child = cmd.spawn().ok()?;
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
    let output = format!("{}{}\n@@exit {}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr), out.status.code().unwrap_or(-1));
    let v = parse_verus(&output, proofs_root);
    let canon = |p: &Path| p.canonicalize().unwrap_or(p.to_path_buf());
    let own = canon(&proofs_root.join("src").join("proofs.rs"));
    let helpers = canon(&proofs_root.join("src").join("proofs"));
    let obligations_file = canon(&proofs_root.join("src").join("obligations.rs"));
    let ob_text = fs::read_to_string(&obligations_file).unwrap_or_default();
    // errors in proofs.rs are attributed to the proof fn they fall in (by line)
    let items = fn_items(&text);
    let mut m = HashMap::new();
    let any_impl_error = v.located.iter().any(|(f, _, _)| {
        let fc = canon(f);
        !(fc == own || fc.starts_with(&helpers) || fc == obligations_file)
    });
    for d in &lowered {
        for o in emit_verus::obligations(&cx, d) {
            let st = match o.how {
                How::Proof => {
                    let Some(it) = items.get(&o.fn_name) else { m.insert(o.name.clone(), ObState::Missing); continue };
                    {
                        // the same test as the stub refresh: the whole body is the TODO marker
                        let stub_todo = body_is_todo(&text[it.start..it.end]);
                        let span = Some((it.line_start, it.line_end));
                        let err_here = v.located.iter().any(|(f, line, _)| {
                            let fc = canon(f);
                            (fc == own && span.map(|(a, b)| *line >= a && *line <= b).unwrap_or(false)) || (fc == obligations_file && ob_text.lines().nth(line.saturating_sub(1)).is_some_and(|_| ob_range(&ob_text, &o.fn_name).map(|(a, b)| *line >= a && *line <= b).unwrap_or(false)))
                        });
                        if stub_todo || err_here {
                            ObState::Drafted
                        } else {
                            ObState::Local
                        }
                    }
                }
                How::Impl => {
                    if any_impl_error || !v.other.is_empty() {
                        ObState::Drafted
                    } else {
                        ObState::Local
                    }
                }
                How::Derived => continue,
            };
            m.insert(o.name.clone(), st);
        }
    }
    Some(m)
}

fn ob_range(text: &str, fn_name: &str) -> Option<(usize, usize)> {
    let decl = format!("pub proof fn {fn_name}(");
    let i = text.find(&decl)?;
    let start = text[..i].lines().count() + 1;
    let end = text[i..].find("\n}").map(|j| text[..i + j + 2].lines().count()).unwrap_or(start);
    Some((start, end))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verus_output_is_read_strictly() {
        let good = "verification results:: 7 verified, 0 errors\n@@exit 0\n";
        let v = parse_verus(good, Path::new("/x"));
        assert!(v.ok && v.verified == 7);
        let bad = "error: postcondition not satisfied\n  --> src/obligations.rs:12:9\n   |\n12 |   o1 == o2,\n\nverification results:: 2 verified, 1 errors\nerror: aborting due to 1 previous error\n@@exit 1\n";
        let v = parse_verus(bad, Path::new("/x"));
        assert!(!v.ok && v.errors == 1);
        assert_eq!(v.located.len(), 1);
        assert_eq!(v.located[0].0, PathBuf::from("/x/src/obligations.rs"));
        assert_eq!(v.located[0].1, 12);
        // no results line: not ok, whatever the exit status says
        assert!(!parse_verus("@@exit 0\n", Path::new("/x")).ok);
        assert!(!parse_verus("verification results:: 3 verified, 0 errors\n@@exit 1\n", Path::new("/x")).ok);
        // an error without a location fails too
        assert!(!parse_verus("error: something odd\nverification results:: 3 verified, 0 errors\n@@exit 0\n", Path::new("/x")).ok);
        // a rustc-style error, with a note, between warnings
        let rustc = "warning: unused variable: `x`\n  --> src/proofs.rs:3:9\n   |\n3  |     let x = 1;\n   |         ^\n   = note: `#[warn(unused_variables)]` on by default\n\nerror[E0425]: cannot find function `helper` in module `crate::spec`\n  --> ../../solution/mod.rs:9:18\n   |\n9  |     crate::spec::helper(x)\n   |                  ^^^^^^ not found in `crate::spec`\n   = note: the mirror does not copy it\n\nwarning: unused import\n  --> src/proofs.rs:2:5\n\nerror: aborting due to 1 previous error; 2 warnings emitted\n@@exit 1\n";
        let v = parse_verus(rustc, Path::new("/x"));
        assert!(!v.ok && v.located.len() == 1 && v.other.is_empty(), "{:?} {:?}", v.located, v.other);
        assert_eq!(v.located[0].0, PathBuf::from("/x/../../solution/mod.rs"));
        assert_eq!(v.located[0].1, 9);
        assert!(v.located[0].2.contains("cannot find function") && v.located[0].2.contains("not found in") && !v.located[0].2.contains("unused import"));
        // a warning block between an error line and its `-->` does not lose the location
        let split = "error: postcondition not satisfied\nwarning: something incidental\n  --> src/proofs.rs:12:9\n   |\n12 |   o1 == o2,\n\nverification results:: 2 verified, 1 errors\n@@exit 1\n";
        let v = parse_verus(split, Path::new("/x"));
        assert_eq!(v.located.len(), 1, "{:?}", v.other);
        assert_eq!((v.located[0].0.clone(), v.located[0].1), (PathBuf::from("/x/src/proofs.rs"), 12));
        // two errors, the second's location is its own
        let two = "error: a\n  --> src/proofs.rs:1:1\nerror: b\n  --> src/proofs.rs:7:1\nverification results:: 0 verified, 2 errors\n@@exit 1\n";
        let v = parse_verus(two, Path::new("/x"));
        assert_eq!(v.located.iter().map(|l| l.1).collect::<Vec<_>>(), vec![1, 7]);
    }

    fn lowered(src: &str) -> Vec<Lowered> {
        let p = djinn_syntax::parse_program(src).unwrap();
        djinn_syntax::lower_verus::lower_program(&p, &TypeNames::new()).unwrap()
    }

    fn proof_obligations(l: &[Lowered]) -> Vec<Obligation> {
        let tn = TypeNames::new();
        let names = HashMap::new();
        let cx = EmitCx { names: &tn, impl_names: &names };
        l.iter().flat_map(|d| emit_verus::obligations(&cx, d)).filter(|o| o.how == How::Proof).collect()
    }

    #[test]
    fn stub_refresh_keeps_filled_proofs() {
        let l = lowered("djinn! { pub fn f(x: u32) -> y: u32 { y == x; }\npub fn g(x: u32) -> y: u32 { y == x; } }");
        let tn = TypeNames::new();
        let names = HashMap::new();
        let cx = EmitCx { names: &tn, impl_names: &names };
        let skeleton = emit_verus::proofs_skeleton(&cx, &l);
        let obs = proof_obligations(&l);
        assert!(obs.iter().any(|o| o.fn_name == "f_unambiguous") && obs.iter().any(|o| o.fn_name == "g_unambiguous"), "{:?}", obs.iter().map(|o| &o.fn_name).collect::<Vec<_>>());
        // the first stub filled, the second untouched: nothing to refresh, nothing missing
        let filled = skeleton.replacen(emit_verus::TODO, "assert(o1 == o2);", 1);
        let (text, refreshed, missing) = refresh_stubs(&filled, &obs);
        assert!(refreshed.is_empty() && missing.is_empty(), "{refreshed:?} {:?}", missing.iter().map(|o| &o.name).collect::<Vec<_>>());
        assert_eq!(text, filled);
        // the second obligation's statement changes (`g` now takes a `u64`): only
        // its (untouched) stub is replaced
        let l2 = lowered("djinn! { pub fn f(x: u32) -> y: u32 { y == x; }\npub fn g(x: u64) -> y: u64 { y == x; } }");
        let obs2 = proof_obligations(&l2);
        let (text, refreshed, missing) = refresh_stubs(&filled, &obs2);
        assert_eq!(refreshed, vec!["g_unambiguous".to_string()]);
        assert!(missing.is_empty());
        assert!(text.contains("assert(o1 == o2);"), "{text}");
        let g = obs2.iter().find(|o| o.fn_name == "g_unambiguous").unwrap();
        assert!(text.contains(emit_verus::stub_text(g).trim_end()), "{text}");
        assert_eq!(text.matches("proof fn ").count(), 2);
        // a stub with an attribute and a filled body is a proof: never touched
        let items = fn_items(&text);
        assert!(!body_is_todo(&text[items["f_unambiguous"].start..items["f_unambiguous"].end]));
        assert!(body_is_todo(&text[items["g_unambiguous"].start..items["g_unambiguous"].end]));
        let todo = emit_verus::TODO;
        assert!(body_is_todo(&format!("pub proof fn h(x: int)\n    ensures\n        (if x > 0 {{ x }} else {{ 0 }}) >= 0,\n{{\n    {todo}\n}}\n\n")));
        assert!(!body_is_todo(&format!("pub proof fn h(x: int)\n{{\n    {todo}\n    assert(true);\n}}\n")));
        // a renamed obligation is missing, and appended by the caller
        let l3 = lowered("djinn! { pub fn f(x: u32) -> y: u32 { y == x; }\npub fn h(x: u32) -> y: u32 { y == x; } }");
        let obs3 = proof_obligations(&l3);
        let (_, refreshed, missing) = refresh_stubs(&filled, &obs3);
        assert!(refreshed.is_empty());
        assert_eq!(missing.iter().map(|o| o.fn_name.clone()).collect::<Vec<_>>(), vec!["h_unambiguous".to_string()]);
    }

    #[test]
    fn escape_hatches_are_found() {
        let bad = [
            "fn f() { unsafe { } }",
            "#[verifier::external_body] fn f() {}",
            "verus! { proof fn f() { assume(false); } }",
            "#[cfg(verus_keep_ghost)] fn f() {}",
            "fn f() -> &'static str { file!() }",
            "fn f() { let x = option_env!(\"A\"); }",
            "#[verifier::exec_allows_no_decreases_clause] fn f() { loop {} }",
            "verus! { global size_of usize == 8; }",
            "macro_rules! m { () => {} }",
            "extern crate foo;",
            "#[verifier::when_used_as_spec(g)] fn f() {}",
            "verus! { pub axiom fn f() ensures false; }",
            "verus! { exec static COUNTER: std::sync::atomic::AtomicU32 ensures true { std::sync::atomic::AtomicU32::new(0) } }",
            "static X: u32 = 1;",
        ];
        for b in bad {
            assert!(banned(b.parse().unwrap()).is_some(), "{b}");
        }
        let good = [
            "verus! { fn f(line: u32) -> (r: u32) ensures r == line { let global = 1; let file = 2; line } }",
            "verus! { proof fn p() { assert(true); } }",
            "#[verifier::opaque] spec fn s() -> bool { true }",
            // the lifetime is not the keyword
            "verus! { fn f() -> (r: &'static [u8]) ensures r@.len() == 1 { let s: &'static [u8] = &[1u8]; s } }",
        ];
        for g in good {
            assert!(banned(g.parse().unwrap()).is_none(), "{g}");
        }
    }

    #[test]
    fn stale_segments_mention_removed_names() {
        let removed = vec!["min".to_string()];
        let prefixes = vec!["crate::solution::".to_string(), "crate::spec::".to_string()];
        assert_eq!(mentions("pub proof fn min_unambiguous(a: i32) {}\n", &removed, &prefixes), Some("min".into()));
        assert_eq!(mentions("proof fn helper(a: i32) requires min_spec(a, 1, 2) {}\n", &removed, &prefixes), Some("min".into()));
        assert_eq!(mentions("fn x() { crate::solution::min(1, 2); }\n", &removed, &prefixes), Some("min".into()));
        assert_eq!(mentions("fn x() { crate::spec::min(1, 2); }\n", &removed, &prefixes), Some("min".into()));
        assert_eq!(mentions("proof fn minimal_lemma(a: i32) {}\n", &removed, &prefixes), None);
        // a library function of the same name is not the removed declaration
        assert_eq!(mentions("proof fn l() { vstd::math::min(1, 2); }\n", &removed, &prefixes), None);
        assert_eq!(mentions("proof fn l() { crate::vocab::min(1, 2); }\n", &removed, &prefixes), None);
        // the implementer's helpers whose names end like obligation functions stay
        let text = "use vstd::prelude::*;\nverus! {\n\nproof fn lemma_wf(a: int) {}\n\nproof fn witness_exists(a: int) {}\n\nproof fn index_unambiguous(a: int) {}\n\nproof fn bits_ens_0(a: int) {}\n\npub proof fn min_unambiguous(a: i32) {}\n\n} // verus!\n";
        let (kept, stale, n) = split_stale(text, &removed, &prefixes);
        assert_eq!(n, 1, "{stale}");
        assert!(stale.contains("min_unambiguous") && !kept.contains("min_unambiguous"));
        for h in ["lemma_wf", "witness_exists", "index_unambiguous", "bits_ens_0"] {
            assert!(kept.contains(h), "{h} was archived:\n{stale}");
        }
        // nothing removed: nothing archived, whatever the names
        assert_eq!(split_stale(text, &[], &prefixes).2, 0);
        let segs = verus_segments("use vstd::prelude::*;\nverus! {\n\n/// doc\npub proof fn a()\n    ensures true,\n{\n}\n\nproof fn b() {}\n} // verus!\n");
        assert_eq!(segs.len(), 5, "{segs:?}");
        assert!(segs[2].starts_with("/// doc\npub proof fn a()"));
    }

    #[test]
    fn child_modules_nest() {
        let specs = vec![
            SpecFile { path: PathBuf::from("/c/src/spec.rs"), module: Some("spec".into()) },
            SpecFile { path: PathBuf::from("/c/src/a/b.rs"), module: Some("a::b".into()) },
            SpecFile { path: PathBuf::from("/c/src/a/b/c.rs"), module: Some("a::b::c".into()) },
        ];
        assert_eq!(child_modules(&specs, None), "pub mod a {\n    pub mod b;\n}\npub mod spec;\n");
        assert_eq!(child_modules(&specs, Some("a::b")), "pub mod c;\n");
        assert_eq!(pathdiff(Path::new("/c/djinn/solution/mod.rs"), Path::new("/c/djinn/verus/src")), "../../solution/mod.rs");
    }
}
