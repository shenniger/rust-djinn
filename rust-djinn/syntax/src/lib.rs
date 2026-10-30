//! djinn-syntax: the specification language shared by the `djinn` macros
//! (which only parse and check) and `cargo-djinn` (which also lowers to Lean).

pub mod ambient_verus;
pub mod ast;
pub mod check;
pub mod emit;
pub mod emit_verus;
pub mod lower;
pub mod lower_verus;
pub mod parse;
pub mod project;
pub mod types;

pub use ast::*;
pub use parse::{parse_block, parse_decl};

use std::collections::HashMap;

/// Parse a Rust source file: every `djinn! { … }` block (and the older
/// `func!`/`rel!` forms), plus the `struct`, `enum` and literal `const`
/// items the specifications may mention.
pub fn parse_program(src: &str) -> Result<Program> {
    let file: syn::File = syn::parse_str(src).map_err(|e| Error::new(e.span(), format!("{e}")))?;
    let types = parse::collect_types(&file)?;
    let mut decls = Vec::new();
    for item in file.items {
        if let syn::Item::Macro(m) = item {
            let name = m.mac.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
            match name.as_str() {
                "djinn" => decls.extend(parse_block(m.mac.tokens.clone())?),
                "func" => decls.push(parse_decl(Kind::Func, m.mac.tokens.clone())?),
                "rel" => decls.push(parse_decl(Kind::Rel, m.mac.tokens.clone())?),
                _ => continue,
            }
        }
    }
    let mut origin = HashMap::new();
    for n in decls.iter().map(|d| &d.name).chain(types.enums.keys()).chain(types.structs.keys()).chain(types.consts.keys()).chain(types.ambient.keys()) {
        origin.insert(n.clone(), 0);
    }
    Ok(Program { decls, types, origin })
}

const SEVERAL: &str = "it is defined in several specification files";

/// Parse several specification files into one program. Declarations,
/// types, constants and ambient functions share one namespace across the
/// files (every `fn` delegates to `crate::solution::<name>`); `origin` and
/// `Decl::file` record which file each comes from, `Error::file` where an
/// error is.
pub fn parse_sources(srcs: &[String]) -> Result<Program> {
    let mut all = Program { decls: Vec::new(), types: Default::default(), origin: HashMap::new() };
    for (i, src) in srcs.iter().enumerate() {
        let p = parse_program(src).map_err(|e| e.in_file(i))?;
        let (types, decls) = (p.types, p.decls);
        let mut claim = |n: &str, span: proc_macro2::Span| -> Result<()> {
            match all.origin.insert(n.to_string(), i) {
                Some(j) if j != i => Err(Error::new(span, format!("`{n}` is also defined in another specification file; the specification's names are shared across the crate")).in_file(i)),
                _ => Ok(()),
            }
        };
        for d in &decls {
            claim(&d.name, d.name_span)?;
        }
        for n in types.enums.keys().chain(types.structs.keys()).chain(types.consts.keys()) {
            claim(n, proc_macro2::Span::call_site())?;
        }
        // an ordinary function of the same name in two files is fine for
        // Rust; a constraint just cannot call it by that name
        for (n, a) in types.ambient {
            if all.types.ambient.remove(&n).is_some() || all.types.ambient_errors.get(&n).is_some_and(|r| r == SEVERAL) {
                all.types.ambient_errors.insert(n, SEVERAL.into());
            } else {
                all.origin.insert(n.clone(), i);
                all.types.ambient.insert(n, a);
            }
        }
        all.decls.extend(decls.into_iter().map(|mut d| {
            d.file = i;
            d
        }));
        all.types.enums.extend(types.enums);
        all.types.structs.extend(types.structs);
        all.types.consts.extend(types.consts);
        all.types.structural.extend(types.structural);
        for (n, r) in types.ambient_errors {
            all.types.ambient_errors.entry(n).or_insert(r);
        }
    }
    Ok(all)
}

/// The declarations in dependency order: every callee before its callers,
/// otherwise as in the source (so a program already in that order keeps it).
/// Within a cycle of mutual recursion the source order stands.
pub fn dependency_order(decls: &[Decl]) -> Vec<&Decl> {
    let index: HashMap<&str, usize> = decls.iter().enumerate().map(|(i, d)| (d.name.as_str(), i)).collect();
    fn visit<'a>(i: usize, decls: &'a [Decl], index: &HashMap<&str, usize>, state: &mut Vec<u8>, out: &mut Vec<&'a Decl>) {
        if state[i] != 0 {
            return;
        }
        state[i] = 1;
        for c in decls[i].callees() {
            if let Some(&j) = index.get(c.as_str()) {
                visit(j, decls, index, state, out);
            }
        }
        state[i] = 2;
        out.push(&decls[i]);
    }
    let mut state = vec![0u8; decls.len()];
    let mut out = Vec::with_capacity(decls.len());
    for i in 0..decls.len() {
        visit(i, decls, &index, &mut state, &mut out);
    }
    out
}

/// The declarations of a source file (see `parse_program`).
pub fn parse_file(src: &str) -> Result<Vec<Decl>> {
    parse_program(src).map(|p| p.decls)
}

/// Lower a whole program.
pub fn lower_program(prog: &Program) -> Result<Vec<lower::Lowered>> {
    lower_program_named(prog, &types::TypeNames::new())
}

/// Lower a whole program, naming user types by their Lean names.
pub fn lower_program_named(prog: &Program, names: &types::TypeNames) -> Result<Vec<lower::Lowered>> {
    let mut infos = HashMap::new();
    for d in &prog.decls {
        if infos.insert(d.name.clone(), lower::decl_info(d)).is_some() {
            return Err(Error::new(d.name_span, format!("duplicate declaration `{}`", d.name)).in_file(d.file));
        }
    }
    // callees first: a weakly specified callee's choices, known once it is
    // lowered, are lifted into its callers; and `Spec.lean` defines each
    // relation before its users
    let mut out = Vec::with_capacity(prog.decls.len());
    for d in dependency_order(&prog.decls) {
        let l = lower::lower_with(d, &infos, &prog.types, names).map_err(|e| e.in_file(d.file))?;
        if let Some(i) = infos.get_mut(&d.name) {
            i.choices = l.choices.clone();
        }
        out.push(l);
    }
    Ok(out)
}
