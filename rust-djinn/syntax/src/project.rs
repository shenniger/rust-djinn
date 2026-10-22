//! Facts about a Djinn project shared by `cargo-djinn` (which writes the
//! report) and the `djinn!` macro (which reads it): the canonical text of a
//! declaration's tokens, which declarations it mentions, whether a declaration
//! is stale with respect to a report, and the functions present in a
//! solution directory.

use crate::ast::{Decl, Program};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

/// Tokens as one canonical line: every token separated by a single space,
/// groups with their delimiters. Independent of the token source (the
/// compiler's tokens inside the macro, or `syn`'s when the driver parses the
/// file) and of whitespace and comments in the source.
pub fn canonical(ts: &TokenStream) -> String {
    let trees: Vec<TokenTree> = ts.clone().into_iter().collect();
    canonical_trees(&trees)
}

pub fn canonical_trees(trees: &[TokenTree]) -> String {
    let mut out = Vec::new();
    for t in trees {
        match t {
            TokenTree::Group(g) => {
                let (o, c) = match g.delimiter() {
                    Delimiter::Parenthesis => ("(", ")"),
                    Delimiter::Brace => ("{", "}"),
                    Delimiter::Bracket => ("[", "]"),
                    Delimiter::None => ("", ""),
                };
                let inner = canonical(&g.stream());
                if inner.is_empty() {
                    out.push(format!("{o}{c}"));
                } else {
                    out.push(format!("{o} {inner} {c}"));
                }
            }
            TokenTree::Ident(i) => out.push(i.to_string()),
            TokenTree::Punct(p) => out.push(p.as_char().to_string()),
            TokenTree::Literal(l) => out.push(l.to_string()),
        }
    }
    out.join(" ")
}

/// What the report records per declaration, computed from the parsed spec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub name: String,
    /// `func`, `rel`, or `ambient` (an ordinary function of the file that
    /// constraints call).
    pub kind: String,
    pub tokens: String,
    /// Other declarations mentioned in the tokens, in order of first mention.
    pub uses: Vec<String>,
}

/// Entries for the declarations of a block (no ambient functions known).
pub fn index(decls: &[Decl]) -> Vec<Entry> {
    index_with(decls, &[])
}

fn index_with(decls: &[Decl], ambient: &[(String, String)]) -> Vec<Entry> {
    let names: HashSet<&str> = decls.iter().map(|d| d.name.as_str()).chain(ambient.iter().map(|(n, _)| n.as_str())).collect();
    let uses_of = |me: &str, source: &str| {
        let mut uses = Vec::new();
        for w in source.split(' ') {
            if w != me && names.contains(w) && !uses.iter().any(|u| u == w) {
                uses.push(w.to_string());
            }
        }
        uses
    };
    decls
        .iter()
        .map(|d| Entry { name: d.name.clone(), kind: d.kind.word().into(), tokens: d.source.clone(), uses: uses_of(&d.name, &d.source) })
        .chain(ambient.iter().map(|(n, src)| Entry { name: n.clone(), kind: "ambient".into(), tokens: src.clone(), uses: uses_of(n, src) }))
        .collect()
}

/// Entries for a parsed program: its declarations and its ambient functions.
pub fn index_program(prog: &Program) -> Vec<Entry> {
    let mut ambient: Vec<(String, String)> = prog.types.ambient.values().map(|a| (a.name.clone(), a.source.clone())).collect();
    ambient.sort();
    index_with(&prog.decls, &ambient)
}

/// Entries for a specification source text (empty if it does not parse).
pub fn index_text(src: &str) -> Vec<Entry> {
    crate::parse_program(src).map(|p| index_program(&p)).unwrap_or_default()
}

/// `name` and every declaration it depends on, transitively, following
/// `uses` in every given map (the report's and the current one), so that a
/// newly added mention counts as well as a removed one.
pub fn closure(name: &str, uses_maps: &[&HashMap<String, Vec<String>>]) -> Vec<String> {
    let mut out: Vec<String> = vec![name.to_string()];
    let mut i = 0;
    while i < out.len() {
        let n = out[i].clone();
        for m in uses_maps {
            for u in m.get(&n).into_iter().flatten() {
                if !out.contains(u) {
                    out.push(u.clone());
                }
            }
        }
        i += 1;
    }
    out
}

/// Is `name` stale with respect to a report? `Some(decl)` names the first
/// declaration in its closure whose tokens differ from the report (or that
/// the report does not know).
pub fn stale(name: &str, report: &HashMap<String, Entry>, current: &HashMap<String, Entry>) -> Option<String> {
    let ru: HashMap<String, Vec<String>> = report.iter().map(|(k, e)| (k.clone(), e.uses.clone())).collect();
    let cu: HashMap<String, Vec<String>> = current.iter().map(|(k, e)| (k.clone(), e.uses.clone())).collect();
    for d in closure(name, &[&ru, &cu]) {
        match (report.get(&d), current.get(&d)) {
            (Some(r), Some(c)) if r.tokens == c.tokens && r.kind == c.kind => {}
            _ => return Some(d),
        }
    }
    None
}

/// Does solution code other than the definition of `name` itself mention the
/// identifier `name`? Then a function the specification no longer declares is
/// a helper that verified code depends on, and must stay.
pub fn rust_fn_referenced(dir: &Path, name: &str) -> bool {
    use quote::ToTokens;
    fn has_ident(ts: TokenStream, name: &str) -> bool {
        ts.into_iter().any(|t| match t {
            TokenTree::Ident(i) => i == name,
            TokenTree::Group(g) => has_ident(g.stream(), name),
            _ => false,
        })
    }
    fn scan(items: &[syn::Item], name: &str) -> bool {
        items.iter().any(|it| match it {
            syn::Item::Fn(f) if f.sig.ident == name => false,
            syn::Item::Mod(m) => m.content.as_ref().map(|(_, items)| scan(items, name)).unwrap_or(false),
            other => has_ident(other.to_token_stream(), name),
        })
    }
    let mut files = Vec::new();
    fn walk(d: &Path, v: &mut Vec<std::path::PathBuf>) {
        for e in fs::read_dir(d).into_iter().flatten().flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, v);
            } else if p.extension().map(|x| x == "rs").unwrap_or(false) {
                v.push(p);
            }
        }
    }
    walk(dir, &mut files);
    files.iter().any(|f| fs::read_to_string(f).ok().and_then(|s| syn::parse_file(&s).ok()).map(|ast| scan(&ast.items, name)).unwrap_or(false))
}

/// Names of functions defined in a solution directory (every `.rs` file,
/// recursively, including inline modules).
pub fn solution_fns_in(dir: &Path) -> Vec<String> {
    let mut out = Vec::new();
    fn walk(dir: &Path, out: &mut Vec<String>) {
        let Ok(rd) = fs::read_dir(dir) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().map(|x| x == "rs").unwrap_or(false) {
                if let Ok(src) = fs::read_to_string(&p) {
                    if let Ok(file) = syn::parse_file(&src) {
                        collect(&file.items, out);
                    }
                }
            }
        }
    }
    fn collect(items: &[syn::Item], out: &mut Vec<String>) {
        for it in items {
            match it {
                syn::Item::Fn(f) => out.push(f.sig.ident.to_string()),
                syn::Item::Mod(m) => {
                    if let Some((_, items)) = &m.content {
                        collect(items, out);
                    }
                }
                _ => {}
            }
        }
    }
    walk(dir, &mut out);
    out
}

/// A file of the specification, and the Rust module it is (`a::b`; `None`
/// for the crate root).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecFile {
    pub path: std::path::PathBuf,
    pub module: Option<String>,
}

/// The specification files of a crate. `manual` is the `spec` setting
/// (`spec = "src/spec.rs"` or `spec = ["src/a.rs", "src/b.rs"]`), taken as
/// given; without it, every `.rs` file under `src/` with a top-level
/// `djinn!` block, except `src/bin/` (other crates than the library), in
/// path order.
pub fn spec_files(crate_dir: &Path, manual: Option<&[String]>) -> Vec<SpecFile> {
    let paths: Vec<std::path::PathBuf> = match manual {
        Some(v) => v.iter().map(|p| crate_dir.join(p)).collect(),
        None => {
            fn walk(d: &Path, v: &mut Vec<std::path::PathBuf>) {
                for e in fs::read_dir(d).into_iter().flatten().flatten() {
                    let p = e.path();
                    if p.is_dir() {
                        walk(&p, v);
                    } else if p.extension().is_some_and(|x| x == "rs") {
                        v.push(p);
                    }
                }
            }
            let src = crate_dir.join("src");
            let mut v = Vec::new();
            for e in fs::read_dir(&src).into_iter().flatten().flatten() {
                let p = e.path();
                if p.is_dir() && p.file_name().is_some_and(|n| n != "bin") {
                    walk(&p, &mut v);
                } else if p.extension().is_some_and(|x| x == "rs") {
                    // a binary's root next to a library belongs to another crate
                    if !(p.file_name().is_some_and(|n| n == "main.rs") && src.join("lib.rs").exists()) {
                        v.push(p);
                    }
                }
            }
            v.sort();
            v.into_iter().filter(|p| fs::read_to_string(p).is_ok_and(|s| has_djinn(&s))).collect()
        }
    };
    paths.into_iter().map(|path| SpecFile { module: module_of(crate_dir, &path), path }).collect()
}

/// The Rust module of a source file, from its place under `src/`:
/// `src/a/b.rs` and `src/a/b/mod.rs` are `a::b`, `src/lib.rs` and
/// `src/main.rs` the crate root. A file outside `src/` is named by its stem.
pub fn module_of(crate_dir: &Path, path: &Path) -> Option<String> {
    let rel = path.strip_prefix(crate_dir.join("src")).ok();
    let Some(rel) = rel else {
        let stem = path.file_stem()?.to_string_lossy().into_owned();
        return (stem != "lib" && stem != "main").then_some(stem);
    };
    let mut parts: Vec<String> = rel.with_extension("").iter().map(|c| c.to_string_lossy().into_owned()).collect();
    if parts.last().is_some_and(|l| l == "mod") || (parts.len() == 1 && (parts[0] == "lib" || parts[0] == "main")) {
        parts.pop();
    }
    (!parts.is_empty()).then(|| parts.join("::"))
}

/// Does a source text have a top-level `djinn!` block (or the older
/// `func!`/`rel!` forms)? A text that does not parse counts if it mentions
/// `djinn!`, so that its error is reported rather than the file ignored.
pub fn has_djinn(src: &str) -> bool {
    if !(src.contains("djinn!") || src.contains("func!") || src.contains("rel!")) {
        return false;
    }
    match syn::parse_file(src) {
        Ok(f) => f.items.iter().any(|it| match it {
            syn::Item::Macro(m) => m.mac.path.segments.last().is_some_and(|s| matches!(s.ident.to_string().as_str(), "djinn" | "func" | "rel")),
            _ => false,
        }),
        Err(_) => src.contains("djinn!"),
    }
}

/// The program of several specification files' texts (see
/// `crate::parse_sources`), indexed.
pub fn index_texts(srcs: &[String]) -> Vec<Entry> {
    crate::parse_sources(srcs).map(|p| index_program(&p)).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn modules() {
        let c = Path::new("/c");
        assert_eq!(module_of(c, Path::new("/c/src/lib.rs")), None);
        assert_eq!(module_of(c, Path::new("/c/src/spec.rs")), Some("spec".into()));
        assert_eq!(module_of(c, Path::new("/c/src/a/b.rs")), Some("a::b".into()));
        assert_eq!(module_of(c, Path::new("/c/src/a/mod.rs")), Some("a".into()));
        assert_eq!(module_of(c, Path::new("/c/spec/x.rs")), Some("x".into()));
    }
    #[test]
    fn merged() {
        let a = "djinn! { pub fn f(x: u32) -> y: u32 { y == g(x); } }".to_string();
        let b = "djinn! { pub fn g(x: u32) -> y: u32 { y == x; } }".to_string();
        let p = crate::parse_sources(&[a.clone(), b.clone()]).unwrap();
        assert_eq!(p.origin["f"], 0);
        assert_eq!(p.origin["g"], 1);
        // `g` is lowered before its caller `f`, though it comes later
        let order: Vec<&str> = crate::dependency_order(&p.decls).iter().map(|d| d.name.as_str()).collect();
        assert_eq!(order, ["g", "f"]);
        assert!(crate::lower_program(&p).is_ok());
        let e = crate::parse_sources(&[a.clone(), a]).unwrap_err();
        assert_eq!(e.file, 1);
    }
}

/// The Lean namespace of a crate: `[package.metadata.djinn] namespace`, else
/// the crate's name with its first letter upper-cased and `-` as `_`. Shared
/// by `cargo djinn` and the build gate, which must agree on where the proofs are.
pub fn namespace(configured: Option<&str>, crate_name: &str) -> String {
    if let Some(ns) = configured {
        return ns.to_string();
    }
    let mut c = crate_name.chars();
    match c.next() {
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
    .replace('-', "_")
}

/// The files a verification attests, besides the specification, and their
/// fingerprint (see `evidence`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evidence {
    /// The files, sorted by `rel`.
    pub files: Vec<std::path::PathBuf>,
    /// What `report.toml` records as `run.evidence`: the line
    /// `fnv1a64v2:<hash of everything>:<count>`, then one line per file,
    /// `<hash of its bytes> <path relative to the crate, with '/'>`.
    pub record: String,
}

/// The Lean files `cargo djinn translate` regenerates in `<proofs>/<ns>/`.
pub const GENERATED_LEAN: &[&str] = &["Spec.lean", "Obligations.lean", "Statements.lean", "Audit.lean", "Vocab.lean", "Tables.lean"];

/// The evidence of a crate: every file under the solution directory, and every
/// file of the Lean project `proofs` (lakefile, toolchain, manifest, root
/// module, the implementer's proofs) except Lake's `.lake/` and what `cargo
/// djinn` regenerates (`<ns>/Code/` and `GENERATED_LEAN` in `<ns>/`). No file
/// is skipped for its name (dotfiles and editor backups count). An error —
/// and so a refused build — for a symbolic link or other non-regular file, a
/// path that is not UTF-8 or holds a newline, an unreadable file, and solution
/// sources that pull in files from outside the solution directory
/// (`#[path]`, `include!`, `include_str!`, `include_bytes!`; see
/// `solution_escapes`).
pub fn evidence(crate_dir: &Path, solution: &Path, proofs: &Path, ns: &str) -> Result<Evidence, String> {
    // paths in messages relative to the crate, as in the fingerprint
    evidence_abs(crate_dir, solution, proofs, ns).map_err(|e| e.replace(&format!("{}/", crate_dir.display()), ""))
}

fn evidence_abs(crate_dir: &Path, solution: &Path, proofs: &Path, ns: &str) -> Result<Evidence, String> {
    fn walk(d: &Path, skip: &dyn Fn(&Path) -> bool, out: &mut Vec<std::path::PathBuf>) -> Result<(), String> {
        let rd = match fs::read_dir(d) {
            Ok(rd) => rd,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(e) => return Err(format!("{}: {e}", d.display())),
        };
        for e in rd {
            let e = e.map_err(|e| format!("{}: {e}", d.display()))?;
            let p = e.path();
            if skip(&p) {
                continue;
            }
            // the entry itself, never what a link points to: no cycles, and
            // nothing outside the tree counts as inside it
            let t = e.file_type().map_err(|e| format!("{}: {e}", p.display()))?;
            if t.is_symlink() {
                return Err(format!("{} is a symbolic link; the verified files must be ordinary files", p.display()));
            } else if t.is_dir() {
                walk(&p, skip, out)?;
            } else if t.is_file() {
                out.push(p);
            } else {
                return Err(format!("{} is not an ordinary file", p.display()));
            }
        }
        Ok(())
    }
    // a link as the directory itself is refused too
    for d in [solution, proofs] {
        if fs::symlink_metadata(d).is_ok_and(|m| m.file_type().is_symlink()) {
            return Err(format!("{} is a symbolic link; the verified files must be ordinary files", d.display()));
        }
    }
    let mut files = Vec::new();
    walk(solution, &|_| false, &mut files)?;
    let lean = proofs.join(ns);
    let (lake, code) = (proofs.join(".lake"), lean.join("Code"));
    // the solution may lie inside the Lean project (a `proofs` setting): not twice
    walk(
        proofs,
        &|p: &Path| p == lake || p == code || p == solution || (p.parent() == Some(lean.as_path()) && GENERATED_LEAN.iter().any(|g| p.file_name().is_some_and(|n| n == *g))),
        &mut files,
    )?;
    let mut rel: Vec<(String, std::path::PathBuf)> = Vec::new();
    for f in files {
        let r = rel_slash(f.strip_prefix(crate_dir).unwrap_or(&f)).ok_or_else(|| format!("{}: the path is not UTF-8 or holds a newline", f.display()))?;
        rel.push((r, f));
    }
    rel.sort();
    rel.dedup();
    let mut record_lines = Vec::new();
    let mut h = Fnv::new();
    for (r, f) in &rel {
        let bytes = fs::read(f).map_err(|e| format!("{}: {e}", f.display()))?;
        if f.starts_with(solution) && f.extension().is_some_and(|x| x == "rs") {
            solution_escapes(solution, f, &bytes)?;
        }
        h.eat(r.as_bytes());
        h.eat(&[0]);
        h.eat(&bytes);
        h.eat(&[0xff]);
        let mut one = Fnv::new();
        one.eat(&bytes);
        record_lines.push(format!("{:016x} {r}", one.0));
    }
    let mut record = format!("fnv1a64v2:{:016x}:{}", h.0, rel.len());
    for l in record_lines {
        record.push('\n');
        record.push_str(&l);
    }
    Ok(Evidence { files: rel.into_iter().map(|(_, f)| f).collect(), record })
}

/// `evidence`'s record, or `invalid: <why>` (which no recomputation matches).
pub fn evidence_record(crate_dir: &Path, solution: &Path, proofs: &Path, ns: &str) -> String {
    match evidence(crate_dir, solution, proofs, ns) {
        Ok(e) => e.record,
        Err(e) => format!("invalid: {e}"),
    }
}

/// A relative path as `a/b/c` whatever the platform's separator.
fn rel_slash(p: &Path) -> Option<String> {
    let parts: Option<Vec<&str>> = p.components().map(|c| c.as_os_str().to_str()).collect();
    let s = parts?.join("/");
    (!s.contains('\n') && !s.contains('\r')).then_some(s)
}

struct Fnv(u64);

impl Fnv {
    fn new() -> Self {
        Fnv(0xcbf29ce484222325)
    }
    fn eat(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 ^= *b as u64;
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }
}

/// Does a solution source pull in a file from outside the solution directory?
/// rustc resolves `#[path = "…"]` and `include!("…")` (`include_str!`,
/// `include_bytes!`) against the file's directory — or a directory below it,
/// for a module inside inline modules — so a relative path that never climbs
/// above `solution` from the file's directory stays inside on every reading.
/// Fail closed: an absolute path, a path that is not a string literal (built
/// by a macro, say), a renamed `include` (`use std::include as inc`) and a
/// file that does not lex are refused.
pub fn solution_escapes(solution: &Path, file: &Path, bytes: &[u8]) -> Result<(), String> {
    let shown = file.display();
    let src = std::str::from_utf8(bytes).map_err(|_| format!("{shown}: not UTF-8"))?;
    let ts: TokenStream = src.parse().map_err(|_| format!("{shown}: cannot be read as Rust tokens"))?;
    let depth = file.parent().and_then(|d| d.strip_prefix(solution).ok()).map(|d| d.components().count() as i64).ok_or_else(|| format!("{shown}: not in {}", solution.display()))?;
    let inside = |lit: Option<&TokenTree>, what: &str| -> Result<(), String> {
        let value = lit.and_then(|t| match t {
            TokenTree::Literal(l) => syn::parse_str::<syn::LitStr>(&l.to_string()).ok().map(|s| s.value()),
            _ => None,
        });
        let Some(v) = value else {
            return Err(format!("{shown}: {what} without a string literal path; the solution may only use files inside {}", solution.display()));
        };
        let mut d = depth;
        for c in Path::new(&v).components() {
            match c {
                std::path::Component::Normal(_) => d += 1,
                std::path::Component::CurDir => {}
                std::path::Component::ParentDir => d -= 1,
                _ => d = -1,
            }
            if d < 0 {
                return Err(format!("{shown}: {what} \"{v}\" reaches outside {}; the verified solution must be self-contained", solution.display()));
            }
        }
        Ok(())
    };
    fn scan(ts: TokenStream, in_attr: bool, inside: &dyn Fn(Option<&TokenTree>, &str) -> Result<(), String>) -> Result<(), String> {
        let trees: Vec<TokenTree> = ts.into_iter().collect();
        for (i, t) in trees.iter().enumerate() {
            let next = |k: usize| trees.get(i + k);
            let is_punct = |t: Option<&TokenTree>, c: char| matches!(t, Some(TokenTree::Punct(p)) if p.as_char() == c);
            match t {
                TokenTree::Ident(id) if id == "include" || id == "include_str" || id == "include_bytes" => {
                    let what = format!("`{id}!`");
                    let args: Option<Vec<TokenTree>> = match (is_punct(next(1), '!'), next(2)) {
                        (true, Some(TokenTree::Group(g))) => Some(g.stream().into_iter().collect()),
                        _ => None,
                    };
                    match args {
                        Some(a) if a.len() == 1 || (a.len() == 2 && is_punct(a.get(1), ',')) => inside(a.first(), &what)?,
                        _ => inside(None, &what)?,
                    }
                }
                TokenTree::Ident(id) if in_attr && id == "path" && is_punct(next(1), '=') => inside(next(2), "`#[path]`")?,
                TokenTree::Group(g) => {
                    // `#[…]` and `#![…]`: an attribute
                    let attr = g.delimiter() == Delimiter::Bracket && i >= 1 && (is_punct(trees.get(i - 1), '#') || (i >= 2 && is_punct(trees.get(i - 1), '!') && is_punct(trees.get(i - 2), '#')));
                    scan(g.stream(), in_attr || attr, inside)?;
                }
                _ => {}
            }
        }
        Ok(())
    }
    scan(ts, false, &inside)
}

/// How the files on disk compare with a report's `run.evidence`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvidenceCheck {
    Same,
    /// The report records no fingerprint (written before fingerprints existed,
    /// or by a verify that stopped early).
    Unrecorded,
    /// The report's fingerprint is of an older definition (`fnv1a64:…`).
    Outdated,
    /// The files differ: per file `changed: …` / `added: …` / `removed: …`
    /// (empty when the recorded fingerprint has no per-file lines).
    Changed(Vec<String>),
    /// The files cannot be fingerprinted (see `evidence`).
    Invalid(String),
}

pub fn check_evidence(recorded: &str, current: &Result<Evidence, String>) -> EvidenceCheck {
    let cur = match current {
        Ok(e) => e,
        Err(e) => return EvidenceCheck::Invalid(e.clone()),
    };
    if recorded.trim().is_empty() {
        return EvidenceCheck::Unrecorded;
    }
    if recorded == cur.record {
        return EvidenceCheck::Same;
    }
    if !recorded.starts_with("fnv1a64v2:") {
        return EvidenceCheck::Outdated;
    }
    let files = |r: &str| -> std::collections::BTreeMap<String, String> { r.lines().skip(1).filter_map(|l| l.split_once(' ')).map(|(h, p)| (p.to_string(), h.to_string())).collect() };
    let (old, new) = (files(recorded), files(&cur.record));
    let mut diff = Vec::new();
    if recorded.lines().count() > 1 {
        for (p, h) in &new {
            match old.get(p) {
                None => diff.push(format!("added: {p}")),
                Some(o) if o != h => diff.push(format!("changed: {p}")),
                _ => {}
            }
        }
        diff.extend(old.keys().filter(|p| !new.contains_key(*p)).map(|p| format!("removed: {p}")));
    }
    EvidenceCheck::Changed(diff)
}

impl EvidenceCheck {
    /// One line for humans; `None` when the files are the verified ones.
    pub fn message(&self) -> Option<String> {
        match self {
            EvidenceCheck::Same => None,
            EvidenceCheck::Unrecorded => Some("no evidence fingerprint recorded: run `cargo djinn verify`".into()),
            EvidenceCheck::Outdated => Some("the evidence fingerprint is of an older `cargo djinn`: run `cargo djinn verify`".into()),
            EvidenceCheck::Changed(d) if d.is_empty() => Some("stale: solution/proofs changed since verify".into()),
            EvidenceCheck::Changed(d) => {
                let more = if d.len() > 8 { format!(", and {} more", d.len() - 8) } else { String::new() };
                Some(format!("stale: solution/proofs changed since verify ({}{more})", d.iter().take(8).cloned().collect::<Vec<_>>().join(", ")))
            }
            EvidenceCheck::Invalid(e) => Some(format!("the solution/proofs cannot be fingerprinted: {e}")),
        }
    }
}

#[cfg(test)]
mod evidence_tests {
    use super::*;
    use std::path::PathBuf;

    fn tmp(name: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("djinn-evidence-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(d.join("djinn/solution")).unwrap();
        fs::create_dir_all(d.join("djinn/proofs/NS/Code")).unwrap();
        fs::create_dir_all(d.join("djinn/proofs/.lake/build")).unwrap();
        fs::write(d.join("djinn/solution/mod.rs"), "pub fn f() {}\n").unwrap();
        fs::write(d.join("djinn/proofs/NS/Proofs.lean"), "-- p\n").unwrap();
        fs::write(d.join("djinn/proofs/NS/Spec.lean"), "-- generated\n").unwrap();
        fs::write(d.join("djinn/proofs/NS/Code/Funs.lean"), "-- generated\n").unwrap();
        fs::write(d.join("djinn/proofs/.lake/build/x.olean"), "o").unwrap();
        fs::write(d.join("djinn/proofs/lakefile.lean"), "import Lake\n").unwrap();
        d
    }
    fn ev(d: &Path) -> Result<Evidence, String> {
        evidence(d, &d.join("djinn/solution"), &d.join("djinn/proofs"), "NS")
    }
    fn rels(e: &Evidence) -> Vec<String> {
        e.record.lines().skip(1).map(|l| l.split_once(' ').unwrap().1.to_string()).collect()
    }

    #[test]
    fn covered_files() {
        let d = tmp("covered");
        let e = ev(&d).unwrap();
        // the lakefile counts; generated files, Code/ and .lake/ do not
        assert_eq!(rels(&e), ["djinn/proofs/NS/Proofs.lean", "djinn/proofs/lakefile.lean", "djinn/solution/mod.rs"]);
        for (f, what) in [("djinn/solution/.hidden.rs", "dotfile"), ("djinn/solution/mod.rs~", "backup"), ("djinn/proofs/lean-toolchain", "toolchain"), ("djinn/proofs/lake-manifest.json", "manifest"), ("djinn/proofs/NS.lean", "root module"), ("djinn/proofs/NS/.Proofs.lean.swp", "swap file")] {
            let before = ev(&d).unwrap();
            fs::write(d.join(f), "x").unwrap();
            let after = ev(&d).unwrap();
            assert_ne!(before.record, after.record, "{what}");
            assert_eq!(check_evidence(&before.record, &Ok(after)), EvidenceCheck::Changed(vec![format!("added: {f}")]), "{what}");
        }
        let before = ev(&d).unwrap();
        fs::write(d.join("djinn/proofs/lakefile.lean"), "import Lake -- changed\n").unwrap();
        assert_eq!(check_evidence(&before.record, &ev(&d)), EvidenceCheck::Changed(vec!["changed: djinn/proofs/lakefile.lean".into()]));
        // regenerated files do not
        let before = ev(&d).unwrap();
        fs::write(d.join("djinn/proofs/NS/Spec.lean"), "-- regenerated\n").unwrap();
        fs::write(d.join("djinn/proofs/NS/Code/Funs.lean"), "-- regenerated\n").unwrap();
        assert_eq!(check_evidence(&before.record, &ev(&d)), EvidenceCheck::Same);
        assert_eq!(check_evidence("", &ev(&d)), EvidenceCheck::Unrecorded);
        // an old-format fingerprint
        assert_eq!(check_evidence("fnv1a64:0123456789abcdef:2", &ev(&d)), EvidenceCheck::Outdated);
        let _ = fs::remove_dir_all(&d);
    }

    #[test]
    fn symlinks_refused() {
        let d = tmp("links");
        std::os::unix::fs::symlink(d.join("djinn"), d.join("djinn/solution/loop")).unwrap();
        assert!(ev(&d).unwrap_err().contains("symbolic link"));
        let _ = fs::remove_dir_all(&d);
        let d = tmp("links2");
        std::os::unix::fs::symlink("/etc/hostname", d.join("djinn/proofs/NS/Extra.lean")).unwrap();
        assert!(ev(&d).unwrap_err().contains("symbolic link"));
        let _ = fs::remove_dir_all(&d);
    }

    #[test]
    fn escapes() {
        let sol = Path::new("/c/djinn/solution");
        let ok = |f: &str, src: &str| solution_escapes(sol, &sol.join(f), src.as_bytes());
        assert!(ok("mod.rs", "#[path = \"a/b.rs\"] mod b; const X: &str = include_str!(\"t.txt\");").is_ok());
        assert!(ok("sub/mod.rs", "#[path = \"../x.rs\"] mod x; const T: &[u8] = include_bytes!(\"../t.bin\",);").is_ok());
        assert!(ok("mod.rs", "fn f(path: u32) { let path = 1; }").is_ok());
        for (f, src) in [
            ("mod.rs", "#[path = \"../outside.rs\"] mod o;"),
            ("mod.rs", "#[cfg_attr(all(), path = \"../../src/x.rs\")] mod o;"),
            ("sub/a.rs", "mod m { #[path = \"../../x.rs\"] mod o; }"),
            ("mod.rs", "#[path = \"/etc/x.rs\"] mod o;"),
            ("mod.rs", "include!(\"../x.rs\");"),
            ("mod.rs", "const S: &str = include_str!(concat!(env!(\"HOME\"), \"/x\"));"),
            ("mod.rs", "#[doc = include_str!(\"../../README.md\")] pub fn f() {}"),
            ("mod.rs", "use core::include as inc;"),
            ("mod.rs", "macro_rules! m { ($p:literal) => { std::include!($p) } }"),
            ("mod.rs", "#![path = \"../x\"]"),
        ] {
            assert!(ok(f, src).is_err(), "{src}");
        }
    }

    #[test]
    fn escape_refuses_the_fingerprint() {
        let d = tmp("escape");
        fs::write(d.join("djinn/solution/mod.rs"), "#[path = \"../../outside.rs\"] mod outside;\n").unwrap();
        assert!(ev(&d).unwrap_err().contains("reaches outside"));
        let _ = fs::remove_dir_all(&d);
    }

    #[test]
    fn namespaces() {
        assert_eq!(namespace(None, "my-crate"), "My_crate");
        assert_eq!(namespace(Some("X"), "my-crate"), "X");
    }
}
