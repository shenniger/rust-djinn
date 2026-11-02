//! The jail: a working copy of the crate for an agent, in which only the
//! LLM-owned paths are ever taken back into the real crate.
//!
//! Owned paths: `<work_dir>/solution/**`, the implementer's proof file and
//! helper directory (`<proofs>/<NS>/Proofs.lean` and `<proofs>/<NS>/Proofs/**`
//! for Lean; `<verus>/src/proofs.rs` and `<verus>/src/proofs/**` for Verus).
//! The jail mirrors the crate's layout (so that
//! `#[path = "../djinn/solution/mod.rs"]` resolves in it too). Everything
//! else in the jail is a convenience copy;
//! the verifier regenerates the trusted files from the real specification and
//! pushes them into the jail after every run.

use crate::config::*;
use std::fs;
use std::path::{Path, PathBuf};

pub fn jails_dir(cfg: &Config) -> PathBuf {
    cfg.state_dir().join("jails")
}

/// The jail's copy of the solution directory (same relative path as in the crate).
pub fn sol_in(cfg: &Config, jail: &Path) -> PathBuf {
    jail.join(cfg.sol_rel())
}

/// The jail's copy of the proof project (the Lean project, or the Verus crate).
pub fn proofs_in(cfg: &Config, jail: &Path) -> PathBuf {
    jail.join(cfg.proof_root_rel())
}

fn copy_dir(src: &Path, dst: &Path) -> Result<(), String> {
    fs::create_dir_all(dst).map_err(|e| format!("{}: {e}", dst.display()))?;
    for e in fs::read_dir(src).map_err(|e| format!("{}: {e}", src.display()))?.flatten() {
        let p = e.path();
        let name = e.file_name();
        if name == ".lake" || name == "target" || name == ".djinn" || name == ".verus-log" {
            continue;
        }
        let d = dst.join(&name);
        if p.is_dir() {
            copy_dir(&p, &d)?;
        } else {
            fs::copy(&p, &d).map_err(|e| format!("{}: {e}", p.display()))?;
        }
    }
    Ok(())
}

fn set_readonly(p: &Path, ro: bool) {
    if let Ok(md) = fs::metadata(p) {
        let mut perm = md.permissions();
        perm.set_readonly(ro);
        let _ = fs::set_permissions(p, perm);
    }
}

fn set_readonly_tree(p: &Path, ro: bool) {
    if p.is_dir() {
        for e in fs::read_dir(p).into_iter().flatten().flatten() {
            set_readonly_tree(&e.path(), ro);
        }
    } else {
        set_readonly(p, ro);
    }
}

/// Cargo.toml for the jail: path dependencies and tool paths made absolute.
fn jail_cargo_toml(cfg: &Config) -> Result<String, String> {
    let text = fs::read_to_string(cfg.crate_dir.join("Cargo.toml")).map_err(|e| e.to_string())?;
    let mut doc: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    fn absolutize(v: &mut toml::Value, base: &Path) {
        if let Some(s) = v.as_str() {
            if !s.starts_with('/') {
                if let Ok(p) = base.join(s).canonicalize() {
                    *v = toml::Value::String(p.to_string_lossy().into_owned());
                }
            }
        } else if let Some(a) = v.as_array_mut() {
            // `spec = ["src/a.rs", …]`
            a.iter_mut().for_each(|x| absolutize(x, base));
        }
    }
    for sec in ["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(deps) = doc.get_mut(sec).and_then(|d| d.as_table_mut()) {
            for (_, dep) in deps.iter_mut() {
                if let Some(p) = dep.get_mut("path") {
                    absolutize(p, &cfg.crate_dir);
                }
            }
        }
    }
    if let Some(meta) = doc.get_mut("package").and_then(|p| p.get_mut("metadata")).and_then(|m| m.get_mut("djinn")).and_then(|d| d.as_table_mut()) {
        for k in ["charon", "aeneas", "spec", "lake_packages", "verus"] {
            if let Some(v) = meta.get_mut(k) {
                absolutize(v, &cfg.crate_dir);
            }
        }
        if let Some(v) = meta.get_mut("aeneas_lean") {
            absolutize(v, &cfg.proofs);
        }
        // the agent's own `cargo build` is exempt from the compile-time gate
        meta.insert("in_jail".into(), toml::Value::Boolean(true));
    }
    toml::to_string(&doc).map_err(|e| e.to_string())
}

/// Create a fresh jail for an agent run. Returns its directory.
pub fn create(cfg: &Config, id: &str, bin: &Path) -> Result<PathBuf, String> {
    let dir = jails_dir(cfg).join(id);
    if dir.exists() {
        return Err(format!("jail {} already exists", dir.display()));
    }
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    // Rust side: the crate's layout, with the solution directory in place
    fs::write(dir.join("Cargo.toml"), jail_cargo_toml(cfg)?).map_err(|e| e.to_string())?;
    copy_dir(&cfg.crate_dir.join("src"), &dir.join("src"))?;
    // the benchmark data (`<crate>/bench-data`, mostly links into the shortlist's
    // corpora) is shared, not copied, so that `env!("CARGO_MANIFEST_DIR")/bench-data`
    // resolves in the jail too
    if let Ok(real) = cfg.crate_dir.join("bench-data").canonicalize() {
        let _ = std::os::unix::fs::symlink(&real, dir.join("bench-data"));
    }
    let jsol = sol_in(cfg, &dir);
    if cfg.solution_dir().is_dir() {
        copy_dir(&cfg.solution_dir(), &jsol)?;
    }
    fs::create_dir_all(&jsol).map_err(|e| e.to_string())?;
    // the proof project (without its build cache)
    let jproofs = proofs_in(cfg, &dir);
    if cfg.proof_root().is_dir() {
        copy_dir(&cfg.proof_root(), &jproofs)?;
    }
    if !cfg.is_verus() {
        // Lean: packages shared read-only through a symlink
        let pk = cfg.proofs.join(".lake").join("packages");
        if let Ok(real) = pk.canonicalize() {
            let jl = jproofs.join(".lake");
            fs::create_dir_all(&jl).map_err(|e| e.to_string())?;
            let _ = std::os::unix::fs::symlink(&real, jl.join("packages"));
        }
        // the project's own build artifacts (Spec, Code, Obligations oleans), so
        // that `lake env lean` works before the first `lake build`; Lake's trace
        // hashes make it rebuild whatever differs
        let bd = cfg.proofs.join(".lake").join("build");
        if bd.is_dir() {
            copy_dir(&bd, &jproofs.join(".lake").join("build"))?;
        }
        // the lakefile's `require aeneas from "<relative>"` (and the manifest's copy
        // of that path) must resolve from the jail
        if let Some(al) = &cfg.aeneas_lean {
            if let Ok(abs) = cfg.proofs.join(al).canonicalize() {
                for f in ["lakefile.lean", "lake-manifest.json"] {
                    let lf = jproofs.join(f);
                    if let Ok(t) = fs::read_to_string(&lf) {
                        let _ = fs::write(&lf, t.replace(&format!("\"{al}\""), &format!("\"{}\"", abs.display())));
                    }
                }
            }
        }
    }
    // the guide and Aeneas's name table, at the jail's root
    if cfg.guide_path().exists() {
        fs::copy(cfg.guide_path(), dir.join("GUIDE.md")).map_err(|e| e.to_string())?;
    }
    if cfg.translation_path().exists() {
        let _ = fs::copy(cfg.translation_path(), dir.join("translation.json"));
    }
    // tools for the agent
    let bin = bin.canonicalize().map_err(|e| e.to_string())?;
    let manifest = cfg.crate_dir.join("Cargo.toml");
    let script = |cmd: &str| {
        format!(
            "#!/bin/sh\n# {cmd} the real crate from this jail (only the solution directory and {} are taken back).\nexec '{}' {cmd} --backend {} --jail '{}' --manifest-path '{}' \"$@\"\n",
            cfg.proof_main_rel(),
            bin.display(),
            cfg.backend.name(),
            dir.display(),
            manifest.display()
        )
    };
    for (name, cmd) in [("verify", "verify"), ("status", "status")] {
        let p = dir.join(name);
        fs::write(&p, script(cmd)).map_err(|e| e.to_string())?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = fs::set_permissions(&p, fs::Permissions::from_mode(0o755));
        }
    }
    // `./bench` times the jail's own copy (its Cargo.toml has absolute paths)
    // the optimizer's DJINN_BENCH_TIMEOUT holds for the agent's runs too
    let limit = crate::bench::timeout().map(|l| format!("DJINN_BENCH_TIMEOUT={l} ")).unwrap_or_default();
    let bench = format!("#!/bin/sh\n# time the performance workload of this jail's copy of the crate\n{limit}exec '{}' bench --backend {} --manifest-path '{}/Cargo.toml' \"$@\"\n", bin.display(), cfg.backend.name(), dir.display());
    fs::write(dir.join("bench"), bench).map_err(|e| e.to_string())?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = fs::set_permissions(dir.join("bench"), fs::Permissions::from_mode(0o755));
    }
    if cfg.is_verus() {
        // `./verus-check`: Verus on the jail's copy of the verification crate, as it is
        let check = format!(
            "#!/bin/sh\n# run Verus on this jail's copy of the verification crate (nothing synced, nothing compiled); 1-5 min on a large spec; narrow with --verify-only-module proofs [--verify-function 'lemma_*']\nexport PATH=\"$HOME/.cargo/bin:$PATH\"\ncd '{}' && exec '{}' --crate-type=lib src/lib.rs --edition={} --no-cheating --multiple-errors 4 --triggers-mode silent --smt-option memory_max_size=6144 \"$@\"\n",
            jproofs.display(),
            cfg.verus,
            cfg.edition
        );
        fs::write(dir.join("verus-check"), check).map_err(|e| e.to_string())?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = fs::set_permissions(dir.join("verus-check"), fs::Permissions::from_mode(0o755));
        }
    }
    let mcp = serde_json::json!({
        "mcpServers": {
            "djinn": {
                "command": bin.to_string_lossy(),
                "args": ["mcp", "--backend", cfg.backend.name(), "--jail", dir.to_string_lossy(), "--manifest-path", manifest.to_string_lossy()]
            }
        }
    });
    fs::write(dir.join(".mcp.json"), serde_json::to_string_pretty(&mcp).unwrap()).map_err(|e| e.to_string())?;
    let pointer = format!(
        "# Djinn jail\n\nRead `GUIDE.md` (this directory) before doing anything else. You may edit only\n`{sol}/` and `{p}` (plus helper files under\n`{h}/`). Everything else is regenerated by the verifier and\nedits to it are discarded. Judge your work with the `verify` tool\n(MCP server `djinn`), or `./verify` from this directory.\n",
        sol = cfg.sol_rel(),
        p = cfg.proof_main_rel(),
        h = cfg.proof_helpers_rel()
    );
    fs::write(dir.join("CLAUDE.md"), &pointer).map_err(|e| e.to_string())?;
    fs::write(dir.join("AGENTS.md"), &pointer).map_err(|e| e.to_string())?;
    protect(cfg, &dir);
    Ok(dir)
}

/// Mark the non-owned files read-only (a reminder, not a security boundary).
fn protect(cfg: &Config, jail: &Path) {
    for f in cfg.specs() {
        set_readonly_tree(&jail.join(cfg.rel(&f.path)), true);
    }
    let jp = proofs_in(cfg, jail);
    if cfg.is_verus() {
        for f in generated_verus(&jp) {
            set_readonly(&f, true);
        }
    } else {
        let ld = jp.join(&cfg.ns);
        for f in ["Spec.lean", "Obligations.lean", "Audit.lean"] {
            set_readonly(&ld.join(f), true);
        }
        set_readonly_tree(&ld.join("Code"), true);
    }
    set_readonly(&jail.join("GUIDE.md"), true);
}

/// The generated files of a Verus project: everything under `src/` except the
/// implementer's `proofs.rs` and `proofs/`.
fn generated_verus(root: &Path) -> Vec<PathBuf> {
    let src = root.join("src");
    let mut v = Vec::new();
    fn walk(d: &Path, skip: &Path, skip_dir: &Path, v: &mut Vec<PathBuf>) {
        for e in fs::read_dir(d).into_iter().flatten().flatten() {
            let p = e.path();
            if p == skip || p.starts_with(skip_dir) {
                continue;
            }
            if p.is_dir() {
                walk(&p, skip, skip_dir, v);
            } else {
                v.push(p);
            }
        }
    }
    walk(&src, &src.join("proofs.rs"), &src.join("proofs"), &mut v);
    v
}

/// Take the LLM-owned paths from the jail into the real crate.
pub fn sync_back(cfg: &Config, jail: &Path) -> Result<Vec<String>, String> {
    let mut notes = Vec::new();
    // the solution directory: mirror
    let js = sol_in(cfg, jail);
    let rs = cfg.solution_dir();
    if js.exists() {
        let _ = fs::remove_dir_all(&rs);
        copy_dir(&js, &rs)?;
        notes.push(format!("synced {} from the jail", cfg.sol_rel()));
    }
    // the implementer's proof file and helper directory
    let jmain = jail.join(cfg.proof_main_rel());
    let jhelpers = jail.join(cfg.proof_helpers_rel());
    if let Some(d) = cfg.proof_main().parent() {
        fs::create_dir_all(d).map_err(|e| e.to_string())?;
    }
    if jmain.exists() {
        fs::copy(&jmain, cfg.proof_main()).map_err(|e| e.to_string())?;
        notes.push(format!("synced {} from the jail", cfg.proof_main_rel()));
    }
    if jhelpers.is_dir() {
        let _ = fs::remove_dir_all(cfg.proof_helpers());
        copy_dir(&jhelpers, &cfg.proof_helpers())?;
        notes.push(format!("synced {}/ from the jail", cfg.proof_helpers_rel()));
    }
    // anything else the agent touched is ignored; say so for the spec
    let specs = cfg.specs();
    for f in &specs {
        if let (Ok(a), Ok(b)) = (fs::read(jail.join(cfg.rel(&f.path))), fs::read(&f.path)) {
            if a != b {
                notes.push(format!("WARNING: the specification file {} in the jail was modified; the change is ignored and the file restored", cfg.rel(&f.path)));
            }
        }
    }
    let rels: Vec<String> = specs.iter().map(|f| cfg.rel(&f.path)).collect();
    for f in djinn_syntax::project::spec_files(jail, cfg.spec_manual.as_deref()) {
        let rel = f.path.strip_prefix(jail).unwrap_or(&f.path).to_string_lossy().into_owned();
        if !rels.contains(&rel) {
            notes.push(format!("WARNING: {rel} in the jail gained a `djinn!` block; the change is ignored"));
        }
    }
    Ok(notes)
}

/// Push the trusted, regenerated files into the jail.
pub fn sync_forward(cfg: &Config, jail: &Path) -> Result<(), String> {
    let ld = cfg.lean_dir();
    let jproofs = proofs_in(cfg, jail);
    let jd = jproofs.join(&cfg.ns);
    let unprotect_copy = |src: &Path, dst: &Path| -> Result<(), String> {
        if let Some(d) = dst.parent() {
            fs::create_dir_all(d).map_err(|e| e.to_string())?;
        }
        set_readonly(dst, false);
        fs::copy(src, dst).map(|_| ()).map_err(|e| format!("{}: {e}", src.display()))?;
        set_readonly(dst, true);
        Ok(())
    };
    if cfg.is_verus() {
        // every generated file of the verification crate, at the same relative path
        for f in generated_verus(&cfg.proof_root()) {
            let rel = f.strip_prefix(&cfg.proof_root()).unwrap_or(&f);
            unprotect_copy(&f, &jproofs.join(rel))?;
        }
    } else {
        fs::create_dir_all(&jd).map_err(|e| e.to_string())?;
        for f in ["Spec.lean", "Obligations.lean", "Audit.lean"] {
            if ld.join(f).exists() {
                unprotect_copy(&ld.join(f), &jd.join(f))?;
            }
        }
        if ld.join("Code").is_dir() {
            set_readonly_tree(&jd.join("Code"), false);
            let _ = fs::remove_dir_all(jd.join("Code"));
            copy_dir(&ld.join("Code"), &jd.join("Code"))?;
            set_readonly_tree(&jd.join("Code"), true);
        }
    }
    // the guide and Aeneas's name table live at the jail's root, not in the Lean project
    if cfg.guide_path().exists() {
        unprotect_copy(&cfg.guide_path(), &jail.join("GUIDE.md"))?;
    }
    if cfg.translation_path().exists() {
        let _ = fs::copy(cfg.translation_path(), jail.join("translation.json"));
    } else {
        let _ = fs::remove_file(jail.join("translation.json"));
    }
    // the build artifacts of the trusted modules, so that the agent's next
    // `lake env lean` does not have to recompile Spec/Code/Obligations
    let bd = cfg.proofs.join(".lake").join("build");
    if !cfg.is_verus() && bd.is_dir() {
        let _ = copy_dir(&bd, &jproofs.join(".lake").join("build"));
    }
    // the specification, restored
    for f in cfg.specs() {
        unprotect_copy(&f.path, &jail.join(cfg.rel(&f.path)))?;
    }
    Ok(())
}
