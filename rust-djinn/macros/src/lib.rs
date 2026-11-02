//! The `djinn!` block macro (and the older `djinn::func!` / `djinn::rel!`).
//!
//! Why function-like rather than attribute macros: rustc parses the item an
//! attribute macro is attached to *before* the macro runs, so the body would
//! have to be valid Rust. A function-like macro receives raw tokens, which
//! keeps the constraint language free (`r in list;`, `some x: T { … }`, …).
//!
//! What the items expand to:
//! - `fn`: a delegation stub `pub fn f(..) { crate::solution::f(..) }` — or,
//!   while the solution has no `f` yet, a stub that panics, so that the crate
//!   (and so Charon) builds before the implementation exists;
//! - `rel`: nothing.

use djinn_syntax::{parse_block, parse_decl, Decl, Kind};
use proc_macro::TokenStream;
use quote::{quote, quote_spanned};

mod gate;

/// `djinn! { … }`: any number of `fn` / `rel` items.
#[proc_macro]
pub fn djinn(input: TokenStream) -> TokenStream {
    let tokens: proc_macro2::TokenStream = input.into();
    match parse_block(tokens) {
        Ok(decls) => expand_all(&decls).into(),
        Err(e) => {
            let msg = e.msg;
            quote_spanned! { e.span => compile_error!(#msg); }.into()
        }
    }
}

/// `djinn::solution!();` in `src/lib.rs`: the `solution` module, read from
/// the solution directory of the backend the build is for (`djinn/solution`
/// for Lean, `djinn/verus/solution` for Verus; `Backend::resolve`), with
/// `#[forbid(unsafe_code)]`. `DJINN_BACKEND` is also read through
/// `option_env!`, so that changing it recompiles the crate.
#[proc_macro]
pub fn solution(_input: TokenStream) -> TokenStream {
    let dir = match gate::project() {
        Some(p) => p.solution,
        None => std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default()).join("djinn").join("solution"),
    };
    let path = dir.join("mod.rs").to_string_lossy().into_owned();
    quote! {
        #[forbid(unsafe_code)]
        #[path = #path]
        pub mod solution;
        const _: Option<&str> = option_env!("DJINN_BACKEND");
    }
    .into()
}

#[proc_macro]
pub fn func(input: TokenStream) -> TokenStream {
    expand(Kind::Func, input)
}

#[proc_macro]
pub fn rel(input: TokenStream) -> TokenStream {
    expand(Kind::Rel, input)
}

fn expand(kind: Kind, input: TokenStream) -> TokenStream {
    let tokens: proc_macro2::TokenStream = input.into();
    match parse_decl(kind, tokens) {
        Ok(d) => expand_all(std::slice::from_ref(&d)).into(),
        Err(e) => {
            let msg = e.msg;
            quote_spanned! { e.span => compile_error!(#msg); }.into()
        }
    }
}

/// Calls to names the specification does not declare are the commonest way
/// to reach for ordinary Rust inside a constraint: report them at the call,
/// at `cargo build`, with the whole file's declarations as the reference.
fn check_calls(decls: &[Decl], project: Option<&gate::Project>) -> Option<djinn_syntax::Error> {
    let mut names: Vec<String> = decls.iter().map(|d| d.name.clone()).collect();
    // the whole specification: its other blocks and files and its ambient
    // functions; without it
    // (no project metadata) only the block's own declarations are known, and
    // a call to anything else is left to the driver to judge
    let reasons: std::collections::HashMap<String, String> = match project.and_then(|p| p.texts()).and_then(|t| djinn_syntax::parse_sources(&t).ok()) {
        Some(prog) => {
            names.extend(prog.decls.iter().map(|d| d.name.clone()));
            names.extend(prog.types.ambient.keys().cloned());
            prog.types.ambient_errors.clone()
        }
        None => return None,
    };
    fn walk_e(e: &djinn_syntax::Expr, names: &[String], reasons: &std::collections::HashMap<String, String>) -> Option<djinn_syntax::Error> {
        use djinn_syntax::ExprKind as K;
        let rec = |x: &djinn_syntax::Expr| walk_e(x, names, reasons);
        match &e.kind {
            K::Call(f, args) => {
                if !names.iter().any(|n| n == f) {
                    return Some(djinn_syntax::Error::new(e.span, djinn_syntax::lower::undeclared_call(f, reasons.get(f).map(|s| s.as_str()))));
                }
                args.iter().find_map(rec)
            }
            K::Int(_) | K::Bool(_) | K::Char(_) | K::Str(_) | K::Var(_) | K::Old(_) => None,
            K::Bin(_, l, r) | K::In(l, r) | K::Index(l, r) => rec(l).or_else(|| rec(r)),
            K::Not(x) | K::Neg(x) | K::Cast(x, _) | K::InRange(x, _) | K::InDomain(x, _) | K::Field(x, _) => rec(x),
            K::Ctor(_, a) => a.iter().find_map(rec),
            K::Variant { fields, .. } => fields.iter().find_map(|(_, x)| rec(x)),
            K::Slice(a, b, c) | K::IfVal(a, b, c) => rec(a).or_else(|| rec(b)).or_else(|| rec(c)),
            K::Method(m) => m.children().into_iter().find_map(rec),
        }
    }
    fn walk_s(s: &djinn_syntax::Stmt, names: &[String], reasons: &std::collections::HashMap<String, String>) -> Option<djinn_syntax::Error> {
        use djinn_syntax::StmtKind as S;
        let we = |e: &djinn_syntax::Expr| walk_e(e, names, reasons);
        let ws = |x: &djinn_syntax::Stmt| walk_s(x, names, reasons);
        match &s.kind {
            S::Constraint(e) => we(e),
            S::ForIn { seq, body, .. } => we(seq).or_else(|| body.iter().find_map(ws)),
            S::ForRange { lo, hi, body, .. } => we(lo).or_else(|| we(hi)).or_else(|| body.iter().find_map(ws)),
            S::Some { body, .. } => body.iter().find_map(ws),
            S::Any { wherec, .. } => we(wherec),
            S::Cases(v) => v.iter().find_map(ws),
            S::If { cond, then, els } => we(cond).or_else(|| then.iter().find_map(ws)).or_else(|| els.iter().flatten().find_map(ws)),
            S::Implies(c, b) => we(c).or_else(|| ws(b)),
            S::Match { scrutinee, arms } => we(scrutinee).or_else(|| arms.iter().find_map(|a| a.body.iter().find_map(ws))),
        }
    }
    for d in decls {
        if let Some(e) = d.requires.iter().chain(d.ensures.iter()).chain(d.decreases.iter()).find_map(|e| walk_e(e, &names, &reasons)).or_else(|| d.body.iter().find_map(|s| walk_s(s, &names, &reasons))) {
            return Some(e);
        }
    }
    None
}

fn expand_all(decls: &[Decl]) -> proc_macro2::TokenStream {
    let project = gate::project();
    if let Some(e) = check_calls(decls, project.as_ref()) {
        let msg = e.msg;
        return quote_spanned! { e.span => compile_error!(#msg); };
    }
    let mut out = gate::check(decls, project.as_ref());
    // `None` when the project layout is unknown (no Cargo.toml metadata): then
    // every `fn` delegates, as it always did
    let implemented: Option<Vec<String>> = project.as_ref().map(|p| djinn_syntax::project::solution_fns_in(&p.solution));
    for d in decls {
        out.extend(stub(d, &implemented));
    }
    out
}

/// What a declaration expands to. A relation is never executable: nothing.
/// A func becomes a delegation stub; the solution module must provide a
/// function with exactly this signature or the crate does not build. Until
/// it exists, a stub that panics keeps the crate buildable (the gate still
/// refuses to compile it outside the verifier and the jails).
fn stub(decl: &Decl, implemented: &Option<Vec<String>>) -> proc_macro2::TokenStream {
    match decl.kind {
        Kind::Rel => proc_macro2::TokenStream::new(),
        Kind::Func => {
            let vis = &decl.vis_tokens;
            let name = proc_macro2::Ident::new(&decl.name, decl.name_span);
            let params = &decl.params_tokens;
            let ret = match &decl.ret_tokens {
                Some(t) => quote! { -> #t },
                None => quote! {},
            };
            let args: Vec<proc_macro2::Ident> = decl.params.iter().map(|p| proc_macro2::Ident::new(&p.name, p.span)).collect();
            if implemented.as_ref().map(|v| v.iter().any(|f| f == &decl.name)).unwrap_or(true) {
                let doc = format!("djinn fn `{}` — implemented in `crate::solution`; relation in the generated `Spec.lean`.", decl.name);
                quote! {
                    #[doc = #doc]
                    #vis fn #name(#params) #ret {
                        crate::solution::#name(#(#args),*)
                    }
                }
            } else {
                let doc = format!("djinn fn `{}` — NOT IMPLEMENTED YET: `crate::solution::{}` does not exist, so this stub panics.", decl.name, decl.name);
                let msg = format!("djinn fn `{}` is not implemented", decl.name);
                quote! {
                    #[doc = #doc]
                    #[allow(unused_variables)]
                    #vis fn #name(#params) #ret {
                        panic!(#msg)
                    }
                }
            }
        }
    }
}
