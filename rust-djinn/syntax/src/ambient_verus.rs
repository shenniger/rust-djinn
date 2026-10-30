//! Ambient functions for the Verus backend.
//!
//! An ambient function is an ordinary Rust function of the specification
//! file that a constraint calls (`r == bump(k)`). The Lean backend denotes it
//! by its Aeneas model; Verus has no denotation of exec code in spec code, so
//! this module *translates* the function's body into a `spec fn`
//! (`djinn_amb_bump`, in `relations.rs`) and has Verus check the translation
//! against the function itself: the mirrored specification module carries
//! the function verbatim with the contract
//!
//! ```text
//! pub fn bump(x: u32) -> (djinn_r: u32)
//!     ensures djinn_r == crate::relations::djinn_amb_bump(x),
//! { <the body, verbatim> }
//! ```
//!
//! which Verus verifies like any function: the body must terminate, never
//! panic (no overflow, no division by zero, no `unwrap` of `None`) and
//! return exactly what the translation says. A translation mistake, or a
//! function Verus cannot verify, is an error in a trusted file and fails the
//! run; it can never make a wrong relation pass. (The Lean backend lets a
//! panicking ambient call make the constraint false; here an ambient
//! function must be total on all its inputs.)
//!
//! The translation covers pure, loop-free, non-recursive bodies over the
//! ambient types (scalars, `bool`, `char`, `Option`s, the file's `struct`s
//! and `enum`s): literals, parameters, `let`, `if`/`else`, `if let`, `match`,
//! (with literal, constant and range patterns), arithmetic, comparisons,
//! `&& ||`, bit operations, `as` casts and `T::from`/`.into()` between
//! integer types, `Some`/`None`/`Ok`/`Err`, struct literals and field access,
//! enum variants, calls of other ambient functions, `std::cmp::min`/`max`,
//! and the methods `min`, `max`, `is_some`, `is_none`, `unwrap`, `unwrap_or`,
//! `wrapping_add/sub/mul`, and on unsigned integers `saturating_add/sub/mul`,
//! `checked_add/sub/mul/div/rem` (what vstd specifies). Machine arithmetic is
//! written `(a + b) as T`: in a specification `+` is exact, and the cast is
//! the identity wherever the function does not overflow — which Verus proves
//! of the function. `==` on a user type needs `#[derive(Structural)]` on it
//! (vstd's marker), or Verus could not relate the exec comparison to the
//! specification's equality. Anything not provably equal in Verus is refused
//! with a message at the construct, never guessed.

use crate::ast::*;
use crate::lower_verus::{ambient_spec_name, exec_type, verus_ident};
use crate::types::TypeNames;
use proc_macro2::Span;
use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use syn::spanned::Spanned;

/// An ambient function translated for Verus.
#[derive(Debug, Clone)]
pub struct Translated {
    pub name: String,
    /// The `spec fn djinn_amb_<name>` for `relations.rs`.
    pub spec_fn: String,
    /// The function, verbatim, with the translation as its contract, for
    /// the mirrored specification module.
    pub exec_fn: String,
    /// The ambient functions the body calls.
    pub calls: Vec<String>,
}

/// Translate the ambient functions `used` (and, transitively, those they
/// call), sorted by name. Recursion among them is refused: Verus would need
/// a `decreases`, and the translation would not be a definition.
pub fn translate_all(types: &TypeDefs, used: &[String], names: &TypeNames) -> Result<Vec<Translated>> {
    let mut done: HashMap<String, Translated> = HashMap::new();
    let mut todo: Vec<String> = used.to_vec();
    while let Some(f) = todo.pop() {
        if done.contains_key(&f) {
            continue;
        }
        let a = types.ambient.get(&f).ok_or_else(|| Error::new(Span::call_site(), format!("`{f}` is not an ambient function")))?;
        let t = translate(a, types, names)?;
        for g in &t.calls {
            if !done.contains_key(g) {
                todo.push(g.clone());
            }
        }
        done.insert(f, t);
    }
    // no cycles (a call graph over the translated functions)
    for start in done.keys() {
        let mut stack = vec![start.clone()];
        let mut seen: HashSet<String> = HashSet::new();
        while let Some(f) = stack.pop() {
            for g in &done[&f].calls {
                if g == start {
                    let a = &types.ambient[start];
                    return Err(Error::new(a.span, format!("the ambient function `{start}` is recursive (through `{f}`); the Verus backend translates only non-recursive ambient functions (a recursive definition would need a termination measure). Write it as a `rel`")));
                }
                if seen.insert(g.clone()) {
                    stack.push(g.clone());
                }
            }
        }
    }
    let mut v: Vec<Translated> = done.into_values().collect();
    v.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(v)
}

/// The name of the result in the mirrored function's contract.
const RESULT_NAME: &str = "djinn_r";

/// Why a name cannot be a variable of an ambient function, if it cannot: the
/// function is mirrored verbatim inside `verus! { }`, where Verus's keywords
/// (`int`, `nat`, `spec`, …) are not identifiers, and names beginning with
/// `djinn` are the generator's.
fn bad_binder(n: &str) -> Option<String> {
    if n.starts_with("djinn") {
        return Some(format!("the name `{n}`: names beginning with `djinn` are reserved for generated identifiers (`{RESULT_NAME}` is the result in the mirrored function's contract); rename it"));
    }
    if verus_ident(n) != n {
        return Some(format!("the name `{n}`, a Verus keyword (`int` and `nat` are types inside `verus! {{ }}`): the function is mirrored verbatim into a Verus crate, where it would not parse; rename it"));
    }
    None
}

/// Translate one ambient function.
pub fn translate(a: &Ambient, types: &TypeDefs, names: &TypeNames) -> Result<Translated> {
    // the spanned tokens, so that an error points at the construct; the
    // printed tokens if a caller built the record without them
    let item: syn::ItemFn = if a.item.is_empty() {
        syn::parse_str(&a.tokens).map_err(|e| Error::new(a.span, format!("the ambient function `{}` could not be re-parsed: {e}", a.name)))?
    } else {
        syn::parse2(a.item.clone()).map_err(|e| Error::new(a.span, format!("the ambient function `{}` could not be re-parsed: {e}", a.name)))?
    };
    let mut tr = Tr { types, names, env: a.params.clone(), calls: Vec::new(), fname: a.name.clone(), cur: a.span };
    for (arg, (n, _)) in item.sig.inputs.iter().zip(&a.params) {
        if let Some(why) = bad_binder(n) {
            tr.cur = arg.span();
            return tr.err(&why);
        }
    }
    let body = tr.block(&item.block, Some(&a.ret))?;
    tr.cur = item.block.span();
    let body = tr.coerce(body, &a.ret)?;
    let params: Vec<String> = a.params.iter().map(|(n, t)| format!("{}: {}", verus_ident(n), exec_type(t, names))).collect();
    let args: Vec<String> = a.params.iter().map(|(n, _)| verus_ident(n)).collect();
    let spec_fn = format!(
        "/// The ambient function `{0}` of the specification file, as a specification: its\n/// body, translated. Verus checks `{0}` itself against this (the mirrored module\n/// states `{0}`'s result to be `{1}(…)`).\npub open spec fn {1}({2}) -> {3} {{\n    {4}\n}}\n",
        a.name,
        ambient_spec_name(&a.name),
        params.join(", "),
        exec_type(&a.ret, names),
        body.text
    );
    // the function itself, verbatim, with the translation as its contract
    let vis = item.vis.to_token_stream().to_string();
    let vis = if vis.is_empty() { String::new() } else { format!("{vis} ") };
    let inputs = item.sig.inputs.to_token_stream().to_string();
    let ret = item.sig.output.to_token_stream().to_string();
    let ret = ret.trim_start_matches("->").trim();
    let exec_fn = format!(
        "/// The specification file's `{0}`, verbatim, with its translation as its contract:\n/// Verus verifies that `{0}` terminates, never panics and returns `{1}(…)`.\n{2}fn {0}({3}) -> ({7}: {4})\n    ensures\n        {7} == crate::relations::{1}({5}),\n{6}\n",
        a.name,
        ambient_spec_name(&a.name),
        vis,
        inputs,
        ret,
        args.join(", "),
        item.block.to_token_stream(),
        RESULT_NAME
    );
    let mut calls = tr.calls;
    calls.sort();
    calls.dedup();
    Ok(Translated { name: a.name.clone(), spec_fn, exec_fn, calls })
}

/// A translated expression: its Verus text and its exec type. `MathInt`
/// stands for an integer literal whose type the context decides.
struct T {
    text: String,
    ty: RType,
}

struct Tr<'a> {
    types: &'a TypeDefs,
    names: &'a TypeNames,
    /// The variables in scope (parameters, then `let`s), innermost last.
    env: Vec<(String, RType)>,
    calls: Vec<String>,
    fname: String,
    /// The span of the construct being translated: where an error points.
    cur: Span,
}

fn is_int(t: &RType) -> bool {
    matches!(t, RType::Int { .. })
}

fn suffix(t: &RType) -> String {
    match t {
        RType::Int { signed, bits } => format!("{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() }),
        _ => String::new(),
    }
}

const ACCEPTED: &str = "literals, parameters, `let`, `if`/`else`, `if let`, `match` (literal, constant and range patterns), arithmetic, comparisons, `&&`/`||`, bit operations, `as`, `T::from`/`.into()` between integer types, `Some`/`None`/`Ok`/`Err`, struct literals and fields, enum variants, calls of other ambient functions, `std::cmp::min`/`max`, `min`/`max`/`is_some`/`is_none`/`unwrap`/`unwrap_or`/`wrapping_*`, and on unsigned integers `saturating_*`/`checked_*`";

impl<'a> Tr<'a> {
    fn err<X>(&self, what: &str) -> Result<X> {
        Err(Error::new(self.cur, format!("the ambient function `{}` uses {what}, which the Verus backend does not translate (ambient functions it accepts are pure, loop-free and non-recursive: {ACCEPTED}). Write the rest as a `rel`, or use the Lean backend", self.fname)))
    }

    /// An error that is not a refused construct: a type mismatch.
    fn fail<X>(&self, what: &str) -> Result<X> {
        Err(Error::new(self.cur, format!("in the ambient function `{}`: {what}", self.fname)))
    }

    fn rtype(&mut self, ty: &syn::Type) -> Result<RType> {
        self.cur = ty.span();
        let (t, is_ref) = crate::parse::convert_type(ty).map_err(|e| Error::new(self.cur, format!("in the ambient function `{}`: {}", self.fname, e.msg)))?;
        if is_ref {
            return self.err("a reference type");
        }
        Ok(t)
    }

    /// `t` at the type `want`: a literal takes the type; anything else must
    /// already have it.
    fn coerce(&self, t: T, want: &RType) -> Result<T> {
        if t.ty == *want {
            return Ok(t);
        }
        match (&t.ty, want) {
            (RType::MathInt, RType::Int { .. }) => {
                let digits = t.text.trim_start_matches('-');
                let text = if digits.chars().all(|c| c.is_ascii_digit() || c == '_') && !digits.is_empty() { format!("{}{}", t.text, suffix(want)) } else { format!("(({}) as {})", t.text, suffix(want)) };
                Ok(T { text, ty: want.clone() })
            }
            // `None`, `Some(1)`: the literal inside takes the type
            (RType::Option(a), RType::Option(b)) if **a == RType::Unit || **a == RType::MathInt => {
                if t.text == "Option::None" {
                    return Ok(T { text: t.text, ty: want.clone() });
                }
                if let Some(inner) = t.text.strip_prefix("Option::Some(").and_then(|s| s.strip_suffix(')')) {
                    let i = self.coerce(T { text: inner.to_string(), ty: (**a).clone() }, b)?;
                    return Ok(T { text: format!("Option::Some({})", i.text), ty: want.clone() });
                }
                self.err("a value whose type it cannot infer (annotate it: `let x: u32 = …`, `5u32`)")
            }
            (RType::Result(a, b), RType::Result(c, d)) if (**a == RType::MathInt || **a == RType::Unit) && (**b == RType::MathInt || **b == RType::Unit) => {
                if let Some(inner) = t.text.strip_prefix("Result::Ok(").and_then(|s| s.strip_suffix(')')) {
                    let i = self.coerce(T { text: inner.to_string(), ty: (**a).clone() }, c)?;
                    return Ok(T { text: format!("Result::Ok({})", i.text), ty: want.clone() });
                }
                if let Some(inner) = t.text.strip_prefix("Result::Err(").and_then(|s| s.strip_suffix(')')) {
                    let i = self.coerce(T { text: inner.to_string(), ty: (**b).clone() }, d)?;
                    return Ok(T { text: format!("Result::Err({})", i.text), ty: want.clone() });
                }
                self.err("a value whose type it cannot infer")
            }
            _ => self.fail(&format!("`{}` has type `{}` where `{}` is expected", t.text, crate::types::rust_type(&t.ty), crate::types::rust_type(want))),
        }
    }

    /// Two operands at one type (a literal takes the other's).
    fn unify(&self, a: T, b: T) -> Result<(T, T, RType)> {
        if a.ty == b.ty {
            let ty = a.ty.clone();
            return Ok((a, b, ty));
        }
        if a.ty == RType::MathInt && b.ty != RType::MathInt {
            let ty = b.ty.clone();
            return Ok((self.coerce(a, &ty)?, b, ty));
        }
        if b.ty == RType::MathInt && a.ty != RType::MathInt {
            let ty = a.ty.clone();
            return Ok((a, self.coerce(b, &ty)?, ty));
        }
        if matches!(a.ty, RType::Option(_) | RType::Result(..)) || matches!(b.ty, RType::Option(_) | RType::Result(..)) {
            // `x == None`: the literal side takes the other's type
            if let Ok(b2) = self.coerce(T { text: b.text.clone(), ty: b.ty.clone() }, &a.ty) {
                let ty = a.ty.clone();
                return Ok((a, b2, ty));
            }
            if let Ok(a2) = self.coerce(T { text: a.text.clone(), ty: a.ty.clone() }, &b.ty) {
                let ty = b.ty.clone();
                return Ok((a2, b, ty));
            }
        }
        self.fail(&format!("`{}` (`{}`) and `{}` (`{}`) have different types", a.text, crate::types::rust_type(&a.ty), b.text, crate::types::rust_type(&b.ty)))
    }

    /// A user type inside `t` (through `Option`/`Result`) that does not derive
    /// `Structural`, if any: `==` on it could not be related to the
    /// specification's equality.
    fn non_structural(&self, t: &RType) -> Option<String> {
        match t {
            RType::Named(n) if !self.types.structural.contains(n) => Some(n.clone()),
            RType::Named(_) => None,
            RType::Option(a) => self.non_structural(a),
            RType::Result(a, b) => self.non_structural(a).or_else(|| self.non_structural(b)),
            _ => None,
        }
    }

    fn block(&mut self, b: &syn::Block, want: Option<&RType>) -> Result<T> {
        let depth = self.env.len();
        let mut lets = Vec::new();
        let n = b.stmts.len();
        let mut tail: Option<T> = None;
        for (i, s) in b.stmts.iter().enumerate() {
            let last = i + 1 == n;
            self.cur = s.span();
            match s {
                syn::Stmt::Local(l) => {
                    if l.init.is_none() {
                        return self.err("a `let` without a value");
                    }
                    let init = l.init.as_ref().unwrap();
                    if init.diverge.is_some() {
                        return self.err("`let … else`");
                    }
                    let (name, ann) = match &l.pat {
                        syn::Pat::Ident(p) if p.by_ref.is_none() && p.subpat.is_none() => {
                            if p.mutability.is_some() {
                                return self.err("`let mut` (a mutable variable)");
                            }
                            (p.ident.to_string(), None)
                        }
                        syn::Pat::Type(pt) => match &*pt.pat {
                            syn::Pat::Ident(p) if p.by_ref.is_none() && p.subpat.is_none() && p.mutability.is_none() => (p.ident.to_string(), Some(self.rtype(&pt.ty)?)),
                            _ => return self.err("a `let` with a pattern"),
                        },
                        _ => return self.err("a `let` with a pattern"),
                    };
                    if let Some(why) = bad_binder(&name) {
                        self.cur = l.pat.span();
                        return self.err(&why);
                    }
                    let v = self.expr(&init.expr, ann.as_ref())?;
                    self.cur = s.span();
                    let v = match &ann {
                        Some(t) => self.coerce(v, t)?,
                        None if v.ty == RType::MathInt => return self.err(&format!("the untyped literal `{}` in a `let` (write `let {name}: u32 = …` or `{}u32`)", v.text, v.text)),
                        None => v,
                    };
                    lets.push(format!("let {}: {} = {};", verus_ident(&name), exec_type(&v.ty, self.names), v.text));
                    self.env.push((name, v.ty));
                }
                syn::Stmt::Expr(e, semi) => {
                    if !last {
                        return self.err("a statement before the final expression that is not a `let` (an `if` with an early `return`, an assignment, a bare expression): write the body as one expression, `if c { a } else { b }`, whose value is the result");
                    }
                    let e = match e {
                        syn::Expr::Return(r) => match &r.expr {
                            Some(x) => &**x,
                            None => return self.err("`return` without a value"),
                        },
                        _ if semi.is_some() => return self.err("a block that ends with a statement (no value)"),
                        _ => e,
                    };
                    tail = Some(self.expr(e, want)?);
                }
                syn::Stmt::Item(_) => return self.err("an item inside the body"),
                syn::Stmt::Macro(_) => return self.err("a macro"),
            }
        }
        self.env.truncate(depth);
        let Some(t) = tail else {
            self.cur = b.span();
            return self.err("a block without a final value");
        };
        if lets.is_empty() {
            Ok(t)
        } else {
            Ok(T { text: format!("({{ {} {} }})", lets.join(" "), t.text), ty: t.ty })
        }
    }

    fn lookup(&self, n: &str) -> Option<RType> {
        self.env.iter().rev().find(|(v, _)| v == n).map(|(_, t)| t.clone())
    }

    /// The Verus path of a user type.
    fn tpath(&self, n: &str) -> String {
        self.names.get(n).cloned().unwrap_or_else(|| n.to_string())
    }

    /// The Verus path of a constant.
    fn cpath(&self, n: &str) -> String {
        self.names.get(&format!("const:{n}")).cloned().unwrap_or_else(|| n.to_string())
    }

    /// Translate an expression; an error points at it (or inside it).
    fn expr(&mut self, e: &syn::Expr, want: Option<&RType>) -> Result<T> {
        let saved = self.cur;
        self.cur = e.span();
        let r = self.expr_inner(e, want);
        if r.is_ok() {
            self.cur = saved;
        }
        r
    }

    fn expr_inner(&mut self, e: &syn::Expr, want: Option<&RType>) -> Result<T> {
        use syn::Expr as E;
        match e {
            E::Paren(p) => self.expr(&p.expr, want),
            E::Group(g) => self.expr(&g.expr, want),
            E::Block(b) => {
                if b.label.is_some() {
                    return self.err("a labelled block");
                }
                self.block(&b.block, want)
            }
            E::Lit(l) => match &l.lit {
                syn::Lit::Int(i) => {
                    let digits = i.base10_digits().to_string();
                    if i.suffix().is_empty() {
                        match want {
                            Some(t) if is_int(t) => Ok(T { text: format!("{digits}{}", suffix(t)), ty: t.clone() }),
                            _ => Ok(T { text: digits, ty: RType::MathInt }),
                        }
                    } else {
                        let ty = match i.suffix() {
                            "usize" => RType::Int { signed: false, bits: 0 },
                            "isize" => RType::Int { signed: true, bits: 0 },
                            s => {
                                let signed = s.starts_with('i');
                                let bits: u32 = s[1..].parse().map_err(|_| Error::new(self.cur, format!("in the ambient function `{}`: the literal suffix `{s}`", self.fname)))?;
                                RType::Int { signed, bits }
                            }
                        };
                        Ok(T { text: format!("{digits}{}", i.suffix()), ty })
                    }
                }
                syn::Lit::Bool(b) => Ok(T { text: b.value.to_string(), ty: RType::Bool }),
                syn::Lit::Char(c) => Ok(T { text: format!("{:?}", c.value()), ty: RType::Char }),
                syn::Lit::Byte(b) => Ok(T { text: format!("{}u8", b.value()), ty: RType::Int { signed: false, bits: 8 } }),
                _ => self.err("a string or float literal"),
            },
            E::Path(p) => self.path(&p.path, want),
            E::Unary(u) => {
                let x = self.expr(&u.expr, want)?;
                match u.op {
                    syn::UnOp::Neg(_) => match &x.ty {
                        RType::MathInt => Ok(T { text: format!("-{}", x.text), ty: RType::MathInt }),
                        RType::Int { signed: true, .. } => Ok(T { text: format!("((-{}) as {})", x.text, suffix(&x.ty)), ty: x.ty.clone() }),
                        _ => self.err("`-` on something not a signed integer"),
                    },
                    syn::UnOp::Not(_) => match &x.ty {
                        RType::Bool => Ok(T { text: format!("(!{})", x.text), ty: RType::Bool }),
                        RType::Int { .. } => Ok(T { text: format!("((!{}) as {})", x.text, suffix(&x.ty)), ty: x.ty.clone() }),
                        RType::MathInt => self.err(&format!("`!` on the untyped literal `{0}`, whose width it cannot know: give it a suffix (`!{0}u32`) or annotate the `let`", x.text)),
                        _ => self.err("`!` on something not a boolean or an integer"),
                    },
                    _ => self.err("`*` (a dereference)"),
                }
            }
            E::Binary(b) => self.binary(b, want),
            E::Cast(c) => {
                let to = self.rtype(&c.ty)?;
                let x = self.expr(&c.expr, None)?;
                self.cur = e.span();
                self.cast(x, &to)
            }
            E::If(i) => {
                if let E::Let(l) = &*i.cond {
                    // `if let pat = e { a } else { b }` is a match
                    let Some((_, els)) = &i.else_branch else { return self.err("`if let` without `else`") };
                    let scrut = self.expr(&l.expr, None)?;
                    let depth = self.env.len();
                    let pat = self.pattern(&l.pat, &scrut.ty)?;
                    let a = self.block(&i.then_branch, want)?;
                    self.env.truncate(depth);
                    let b = self.expr(els, want.or(Some(&a.ty)).filter(|t| **t != RType::MathInt))?;
                    self.cur = e.span();
                    let (a, b, ty) = self.unify(a, b)?;
                    return Ok(T { text: format!("(match {} {{ {pat} => {}, _ => {} }})", scrut.text, a.text, b.text), ty });
                }
                let c = self.expr(&i.cond, Some(&RType::Bool))?;
                if c.ty != RType::Bool {
                    self.cur = i.cond.span();
                    return self.err("an `if` whose condition is not a boolean");
                }
                let Some((_, els)) = &i.else_branch else { return self.err("an `if` without `else` (no value; an `if c { return a; }` before the rest of the body is an early return: write `if c { a } else { … }`)") };
                let a = self.block(&i.then_branch, want)?;
                let b = self.expr(els, want.or(Some(&a.ty)).filter(|t| **t != RType::MathInt))?;
                self.cur = e.span();
                let (a, b, ty) = self.unify(a, b)?;
                Ok(T { text: format!("(if {} {{ {} }} else {{ {} }})", c.text, a.text, b.text), ty })
            }
            E::Match(m) => {
                let scrut = self.expr(&m.expr, None)?;
                if scrut.ty == RType::MathInt {
                    self.cur = m.expr.span();
                    return self.err("a `match` on an untyped literal (give it a suffix)");
                }
                let mut arms = Vec::new();
                let mut ty: Option<RType> = want.cloned();
                for arm in &m.arms {
                    if arm.guard.is_some() {
                        self.cur = arm.span();
                        return self.err("a `match` arm with an `if` guard");
                    }
                    let depth = self.env.len();
                    let pat = self.pattern(&arm.pat, &scrut.ty)?;
                    let body = self.expr(&arm.body, ty.as_ref())?;
                    self.env.truncate(depth);
                    self.cur = arm.body.span();
                    let body = match &ty {
                        Some(t) => self.coerce(body, t)?,
                        None => body,
                    };
                    if body.ty != RType::MathInt {
                        ty = Some(body.ty.clone());
                    }
                    arms.push((pat, body));
                }
                self.cur = e.span();
                let Some(ty) = ty else { return self.err("a `match` whose arms are all untyped literals (annotate one: `5u32`)") };
                let mut texts = Vec::new();
                for (pat, body) in arms {
                    let body = self.coerce(body, &ty)?;
                    texts.push(format!("{pat} => {}", body.text));
                }
                Ok(T { text: format!("(match {} {{ {} }})", scrut.text, texts.join(", ")), ty })
            }
            E::Call(c) => self.call(c, want),
            E::Struct(s) => {
                if s.rest.is_some() {
                    return self.err("a struct literal with `..`");
                }
                let name = s.path.segments.last().map(|x| x.ident.to_string()).unwrap_or_default();
                if s.path.segments.len() == 2 {
                    // `Enum::Variant { f: e }`
                    let en = s.path.segments[0].ident.to_string();
                    if let Some(ed) = self.types.enums.get(&en).cloned() {
                        let Some(vd) = ed.variants.iter().find(|v| v.name == name) else { return self.err(&format!("the unknown variant `{en}::{name}`")) };
                        let mut fs = Vec::new();
                        for f in &s.fields {
                            self.cur = f.span();
                            let fname = match &f.member {
                                syn::Member::Named(i) => i.to_string(),
                                _ => return self.err("a tuple-struct literal"),
                            };
                            let Some((_, fty)) = vd.fields.iter().find(|(n, _)| n.as_deref() == Some(fname.as_str())) else { return self.err(&format!("the unknown field `{fname}` of `{en}::{name}`")) };
                            let fty = fty.clone();
                            let v = self.expr(&f.expr, Some(&fty))?;
                            let v = self.coerce(v, &fty)?;
                            fs.push(format!("{}: {}", verus_ident(&fname), v.text));
                        }
                        return Ok(T { text: format!("{}::{name} {{ {} }}", self.tpath(&en), fs.join(", ")), ty: RType::Named(en) });
                    }
                }
                let Some(sd) = self.types.structs.get(&name).cloned() else { return self.err(&format!("the struct literal `{name}` (not a struct of the specification file)")) };
                let mut fs = Vec::new();
                for f in &s.fields {
                    self.cur = f.span();
                    let fname = match &f.member {
                        syn::Member::Named(i) => i.to_string(),
                        _ => return self.err("a tuple-struct literal"),
                    };
                    let Some((_, fty)) = sd.fields.iter().find(|(n, _)| *n == fname) else { return self.err(&format!("the unknown field `{fname}` of `{name}`")) };
                    let fty = fty.clone();
                    let v = self.expr(&f.expr, Some(&fty))?;
                    let v = self.coerce(v, &fty)?;
                    fs.push(format!("{}: {}", verus_ident(&fname), v.text));
                }
                Ok(T { text: format!("{} {{ {} }}", self.tpath(&name), fs.join(", ")), ty: RType::Named(name) })
            }
            E::Field(f) => {
                let x = self.expr(&f.base, None)?;
                self.cur = e.span();
                let RType::Named(sn) = &x.ty else { return self.err("a field access on something not a struct") };
                let Some(sd) = self.types.structs.get(sn) else { return self.err(&format!("a field access on `{sn}`, which is not a struct of the specification file")) };
                let fname = match &f.member {
                    syn::Member::Named(i) => i.to_string(),
                    _ => return self.err("a tuple field"),
                };
                let Some((_, fty)) = sd.fields.iter().find(|(n, _)| *n == fname) else { return self.err(&format!("the unknown field `{fname}` of `{sn}`")) };
                Ok(T { text: format!("{}.{}", paren(&x.text), verus_ident(&fname)), ty: fty.clone() })
            }
            E::MethodCall(m) => self.method(m, want),
            E::Return(_) => self.err("an early `return` (one that is not the last statement of the body): write the body as one expression, `if c { a } else { b }`, whose value is the result"),
            E::Reference(_) => self.err("a reference (`&x`)"),
            E::Tuple(_) => self.err("a tuple"),
            E::Index(_) => self.err("indexing"),
            E::Array(_) | E::Repeat(_) => self.err("an array"),
            E::Closure(_) => self.err("a closure"),
            E::Loop(_) | E::While(_) | E::ForLoop(_) => self.err("a loop"),
            E::Assign(_) => self.err("an assignment"),
            E::Macro(_) => self.err("a macro"),
            E::Range(_) => self.err("a range"),
            E::Try(_) => self.err("`?`"),
            E::Let(_) => self.err("`let` in a condition (only `if let … else …`)"),
            _ => self.err("an expression form it does not know"),
        }
    }

    /// `x as to`, also for `T::from(x)` and `x.into()` between integer types
    /// (Rust implements `From` only for lossless conversions, so they are
    /// the cast).
    fn cast(&self, x: T, to: &RType) -> Result<T> {
        match (&x.ty, to) {
            (RType::MathInt, RType::Int { .. }) => self.coerce(x, to),
            (RType::Int { .. } | RType::Bool | RType::Char, RType::Int { .. }) | (RType::Int { signed: false, bits: 8 }, RType::Char) => Ok(T { text: format!("(({}) as {})", x.text, exec_type(to, self.names)), ty: to.clone() }),
            _ => self.err(&format!("the cast `as {}` of a `{}`", crate::types::rust_type(to), crate::types::rust_type(&x.ty))),
        }
    }

    fn path(&mut self, p: &syn::Path, want: Option<&RType>) -> Result<T> {
        let segs: Vec<String> = p.segments.iter().map(|s| s.ident.to_string()).collect();
        if segs.len() == 1 {
            let n = &segs[0];
            if let Some(t) = self.lookup(n) {
                return Ok(T { text: verus_ident(n), ty: t });
            }
            return match n.as_str() {
                "true" | "false" => Ok(T { text: n.clone(), ty: RType::Bool }),
                "None" => Ok(T { text: "Option::None".into(), ty: want.cloned().filter(|t| matches!(t, RType::Option(_))).unwrap_or(RType::Option(Box::new(RType::Unit))) }),
                _ => {
                    if let Some(c) = self.types.consts.get(n) {
                        if c.table.is_some() || matches!(c.ty, RType::Seq(..)) {
                            return self.err(&format!("the sequence constant `{n}`"));
                        }
                        return Ok(T { text: self.cpath(n), ty: c.ty.clone() });
                    }
                    self.err(&format!("the name `{n}` (not a parameter, a `let`, or a literal constant of the specification file)"))
                }
            };
        }
        if segs.len() == 2 {
            let (a, b) = (&segs[0], &segs[1]);
            if let Some(ed) = self.types.enums.get(a) {
                let Some(vd) = ed.variants.iter().find(|v| &v.name == b) else { return self.err(&format!("the unknown variant `{a}::{b}`")) };
                if !vd.fields.is_empty() {
                    return self.err(&format!("the variant `{a}::{b}` without its fields"));
                }
                return Ok(T { text: format!("{}::{b}", self.tpath(a)), ty: RType::Named(a.clone()) });
            }
            if let Some(t) = int_type(a) {
                return match b.as_str() {
                    "MAX" | "MIN" => Ok(T { text: format!("{a}::{b}"), ty: t }),
                    "BITS" => Ok(T { text: format!("{a}::BITS"), ty: RType::Int { signed: false, bits: 32 } }),
                    _ => self.err(&format!("`{a}::{b}`")),
                };
            }
            if a == "Option" && b == "None" {
                return Ok(T { text: "Option::None".into(), ty: want.cloned().filter(|t| matches!(t, RType::Option(_))).unwrap_or(RType::Option(Box::new(RType::Unit))) });
            }
        }
        self.err(&format!("the path `{}`", segs.join("::")))
    }

    fn binary(&mut self, b: &syn::ExprBinary, want: Option<&RType>) -> Result<T> {
        use syn::BinOp as O;
        let arith = matches!(b.op, O::Add(_) | O::Sub(_) | O::Mul(_) | O::Div(_) | O::Rem(_) | O::BitAnd(_) | O::BitOr(_) | O::BitXor(_));
        let shift = matches!(b.op, O::Shl(_) | O::Shr(_));
        // the result has the operands' type (a shift's: its left operand's)
        let hint = if arith || shift { want.filter(|t| is_int(t)) } else { None };
        let l = self.expr(&b.left, hint)?;
        let r = self.expr(&b.right, if shift { None } else { hint.or(Some(&l.ty)).filter(|t| **t != RType::MathInt) })?;
        let span = b.span();
        self.cur = span;
        match b.op {
            O::Add(_) | O::Sub(_) | O::Mul(_) | O::Div(_) | O::Rem(_) => {
                let sym = match b.op {
                    O::Add(_) => "+",
                    O::Sub(_) => "-",
                    O::Mul(_) => "*",
                    O::Div(_) => "/",
                    _ => "%",
                };
                let (l, r, ty) = self.unify(l, r)?;
                match &ty {
                    RType::MathInt => Ok(T { text: format!("({} {sym} {})", l.text, r.text), ty }),
                    RType::Int { signed, .. } => {
                        if *signed && matches!(b.op, O::Div(_) | O::Rem(_)) {
                            return self.err("`/` or `%` on signed integers (Rust truncates toward zero, a specification's division rounds down)");
                        }
                        Ok(T { text: format!("(({} {sym} {}) as {})", l.text, r.text, suffix(&ty)), ty })
                    }
                    _ => self.err(&format!("`{sym}` on something not an integer")),
                }
            }
            O::BitAnd(_) | O::BitOr(_) | O::BitXor(_) => {
                let sym = match b.op {
                    O::BitAnd(_) => "&",
                    O::BitOr(_) => "|",
                    _ => "^",
                };
                let (l, r, ty) = self.unify(l, r)?;
                match &ty {
                    RType::Int { .. } => Ok(T { text: format!("({} {sym} {})", l.text, r.text), ty }),
                    // on booleans `&`, `|`, `^` are the (strict) connectives; a
                    // specification writes them as `&&`, `||`, `!=`
                    RType::Bool => Ok(T { text: format!("({} {} {})", l.text, if sym == "^" { "!=" } else if sym == "&" { "&&" } else { "||" }, r.text), ty }),
                    RType::MathInt => self.err(&format!("`{sym}` between two untyped literals: give one a suffix (`{}u32 {sym} {}`)", l.text, r.text)),
                    _ => self.err(&format!("`{sym}` on something not an integer or a boolean")),
                }
            }
            O::Shl(_) | O::Shr(_) => {
                let sym = if matches!(b.op, O::Shl(_)) { "<<" } else { ">>" };
                if l.ty == RType::MathInt {
                    return self.err(&format!("`{sym}` with the untyped literal `{0}` on the left, whose width it cannot know: give it a suffix (`{0}u32 {sym} …`) or annotate the `let`", l.text));
                }
                let RType::Int { .. } = &l.ty else { return self.err(&format!("`{sym}` on something not a machine integer")) };
                let ty = l.ty.clone();
                let r = match &r.ty {
                    RType::MathInt => self.coerce(r, &ty)?,
                    RType::Int { .. } => T { text: format!("(({}) as {})", r.text, suffix(&ty)), ty: ty.clone() },
                    _ => return self.err("a shift by something not an integer"),
                };
                Ok(T { text: format!("({} {sym} {})", l.text, r.text), ty })
            }
            O::Eq(_) | O::Ne(_) | O::Lt(_) | O::Le(_) | O::Gt(_) | O::Ge(_) => {
                let sym = match b.op {
                    O::Eq(_) => "==",
                    O::Ne(_) => "!=",
                    O::Lt(_) => "<",
                    O::Le(_) => "<=",
                    O::Gt(_) => ">",
                    _ => ">=",
                };
                let (l, r, ty) = self.unify(l, r)?;
                if ty == RType::MathInt {
                    return self.err("a comparison of two untyped literals");
                }
                if matches!(ty, RType::Named(_) | RType::Option(_) | RType::Result(..)) && sym != "==" && sym != "!=" {
                    return self.err("an ordering of values that are not numbers or chars");
                }
                if let Some(n) = self.non_structural(&ty) {
                    return self.fail(&format!("`{sym}` on `{n}`, which does not derive `Structural`. Verus relates an exec `==` to the specification's equality only for types marked `#[derive(Structural)]` (the marker comes with `vstd::prelude`; the type needs `PartialEq` too, and every user type inside it must derive both as well). Add `Structural` to `{n}`'s derive list, or compare field by field"));
                }
                Ok(T { text: format!("({} {sym} {})", l.text, r.text), ty: RType::Bool })
            }
            O::And(_) | O::Or(_) => {
                if l.ty != RType::Bool || r.ty != RType::Bool {
                    return self.err("`&&`/`||` on something not boolean");
                }
                Ok(T { text: format!("({} {} {})", l.text, if matches!(b.op, O::And(_)) { "&&" } else { "||" }, r.text), ty: RType::Bool })
            }
            _ => self.err("a compound assignment"),
        }
    }

    /// `a.min(b)`, `std::cmp::min(a, b)`: vstd's `math::min` on `int`.
    fn minmax(&mut self, name: &str, recv: T, arg: &syn::Expr) -> Result<T> {
        let x = self.expr(arg, Some(&recv.ty).filter(|t| **t != RType::MathInt))?;
        let (a, b, ty) = self.unify(recv, x)?;
        let RType::Int { .. } = &ty else { return self.err(&format!("`{name}` on something not an integer")) };
        Ok(T { text: format!("(vstd::math::{name}({} as int, {} as int) as {})", a.text, b.text, suffix(&ty)), ty })
    }

    fn call(&mut self, c: &syn::ExprCall, want: Option<&RType>) -> Result<T> {
        let syn::Expr::Path(p) = &*c.func else { return self.err("a call of something not a function name") };
        let segs: Vec<String> = p.path.segments.iter().map(|s| s.ident.to_string()).collect();
        let name = segs.join("::");
        let one = |me: &mut Self, want_inner: Option<&RType>| -> Result<T> {
            if c.args.len() != 1 {
                return me.err(&format!("`{name}` with {} arguments", c.args.len()));
            }
            me.expr(&c.args[0], want_inner)
        };
        match name.as_str() {
            "Some" | "Option::Some" => {
                let inner = match want {
                    Some(RType::Option(t)) => Some((**t).clone()),
                    _ => None,
                };
                let x = one(self, inner.as_ref())?;
                let x = match &inner {
                    Some(t) => self.coerce(x, t)?,
                    None => x,
                };
                Ok(T { ty: RType::Option(Box::new(x.ty.clone())), text: format!("Option::Some({})", x.text) })
            }
            "Ok" | "Result::Ok" | "Err" | "Result::Err" => {
                let is_ok = name.ends_with("Ok");
                let (want_a, want_b) = match want {
                    Some(RType::Result(a, b)) => (Some((**a).clone()), Some((**b).clone())),
                    _ => (None, None),
                };
                let x = one(self, if is_ok { want_a.as_ref() } else { want_b.as_ref() })?;
                let x = match if is_ok { &want_a } else { &want_b } {
                    Some(t) => self.coerce(x, t)?,
                    None => x,
                };
                let other = if is_ok { want_b.clone() } else { want_a.clone() }.unwrap_or(RType::Unit);
                let ty = if is_ok { RType::Result(Box::new(x.ty.clone()), Box::new(other)) } else { RType::Result(Box::new(other), Box::new(x.ty.clone())) };
                Ok(T { text: format!("Result::{}({})", if is_ok { "Ok" } else { "Err" }, x.text), ty })
            }
            "std::cmp::max" | "std::cmp::min" | "core::cmp::max" | "core::cmp::min" | "cmp::max" | "cmp::min" => {
                if c.args.len() != 2 {
                    return self.err(&format!("`{name}` with {} arguments", c.args.len()));
                }
                let a = self.expr(&c.args[0], want.filter(|t| is_int(t)))?;
                let mm = segs.last().cloned().unwrap_or_default();
                self.minmax(&mm, a, &c.args[1])
            }
            _ => {
                if segs.len() == 2 {
                    // `Enum::Variant(a, b)`
                    let (en, vn) = (&segs[0], &segs[1]);
                    if let Some(ed) = self.types.enums.get(en).cloned() {
                        let Some(vd) = ed.variants.iter().find(|v| &v.name == vn) else { return self.err(&format!("the unknown variant `{en}::{vn}`")) };
                        if vd.fields.len() != c.args.len() || vd.fields.iter().any(|(n, _)| n.is_some()) {
                            return self.err(&format!("`{en}::{vn}` with the wrong number of fields"));
                        }
                        let mut xs = Vec::new();
                        for (a, (_, t)) in c.args.iter().zip(&vd.fields) {
                            let x = self.expr(a, Some(t))?;
                            xs.push(self.coerce(x, t)?.text);
                        }
                        return Ok(T { text: format!("{}::{vn}({})", self.tpath(en), xs.join(", ")), ty: RType::Named(en.clone()) });
                    }
                    // `u32::from(x)`: a lossless integer conversion, the cast
                    if let (Some(to), "from") = (int_type(en), vn.as_str()) {
                        let x = one(self, None)?;
                        self.cur = c.span();
                        if !is_int(&x.ty) {
                            return self.err(&format!("`{name}` of a `{}` (vstd specifies `From` only between integer types; write `as`)", crate::types::rust_type(&x.ty)));
                        }
                        return self.cast(x, &to);
                    }
                }
                if segs.len() == 1 {
                    if let Some(a) = self.types.ambient.get(&segs[0]).cloned() {
                        if a.params.len() != c.args.len() {
                            return self.err(&format!("a call of `{}` with {} arguments", a.name, c.args.len()));
                        }
                        let mut xs = Vec::new();
                        for (arg, (_, t)) in c.args.iter().zip(&a.params) {
                            let x = self.expr(arg, Some(t))?;
                            xs.push(self.coerce(x, t)?.text);
                        }
                        self.calls.push(a.name.clone());
                        return Ok(T { text: format!("crate::relations::{}({})", ambient_spec_name(&a.name), xs.join(", ")), ty: a.ret.clone() });
                    }
                    if let Some(why) = self.types.ambient_errors.get(&segs[0]) {
                        return self.err(&format!("a call of `{}`, which is not an ambient function ({why})", segs[0]));
                    }
                }
                self.err(&format!("a call of `{name}`"))
            }
        }
    }

    fn method(&mut self, m: &syn::ExprMethodCall, want: Option<&RType>) -> Result<T> {
        let name = m.method.to_string();
        if m.turbofish.is_some() {
            return self.err("a method call with explicit type arguments");
        }
        let recv_hint = want.filter(|_| matches!(name.as_str(), "min" | "max" | "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "saturating_add" | "saturating_sub" | "saturating_mul"));
        let recv = self.expr(&m.receiver, recv_hint)?;
        let args: Vec<&syn::Expr> = m.args.iter().collect();
        let span = m.span();
        self.cur = span;
        // the receiver and the argument at one machine type
        let two = |me: &mut Self, recv: T, arg: &syn::Expr| -> Result<(T, T, RType)> {
            let x = me.expr(arg, Some(&recv.ty).filter(|t| **t != RType::MathInt))?;
            me.cur = span;
            let (a, b, ty) = me.unify(recv, x)?;
            if ty == RType::MathInt {
                return me.err(&format!("`.{name}()` between two untyped literals (give one a suffix: `{}u32`)", a.text));
            }
            let RType::Int { .. } = &ty else { return me.err(&format!("`.{name}()` on something not an integer")) };
            Ok((a, b, ty))
        };
        match (name.as_str(), args.len()) {
            ("min" | "max", 1) => {
                if recv.ty == RType::MathInt {
                    // `3.max(x)`: the literal takes the argument's type
                    let x = self.expr(args[0], want.filter(|t| is_int(t)))?;
                    self.cur = span;
                    if !is_int(&x.ty) {
                        return self.err(&format!("`.{name}()` on the untyped literal `{}` (give it a suffix: `{}u32`)", recv.text, recv.text));
                    }
                    let recv = self.coerce(recv, &x.ty)?;
                    let ty = x.ty.clone();
                    return Ok(T { text: format!("(vstd::math::{name}({} as int, {} as int) as {})", recv.text, x.text, suffix(&ty)), ty });
                }
                self.minmax(&name, recv, args[0])
            }
            ("abs", 0) => self.err("`.abs()` (vstd gives Verus no specification of it; write `if x < 0 { -x } else { x }`)"),
            ("rem_euclid", 1) | ("div_euclid", 1) => self.err(&format!("`.{name}()` (vstd gives Verus no specification of it; on unsigned integers `%` and `/` are already Euclidean)")),
            ("pow", 1) => self.err("`.pow()` (vstd gives Verus no specification of it; multiply out, or write a `rel`)"),
            ("count_ones", 0) | ("count_zeros", 0) | ("leading_zeros", 0) | ("trailing_zeros", 0) | ("leading_ones", 0) | ("trailing_ones", 0) | ("rotate_left", 1) | ("rotate_right", 1) | ("swap_bytes", 0) | ("reverse_bits", 0) => self.err(&format!("`.{name}()` (the specification language states it through `vocab.rs`; in an ambient function Verus would have to relate it to that definition). Use it in a constraint instead")),
            ("wrapping_add" | "wrapping_sub" | "wrapping_mul", 1) => {
                let (a, b, ty) = two(self, recv, args[0])?;
                Ok(T { text: format!("vstd::wrapping::{}_specs::{name}({}, {})", suffix(&ty), a.text, b.text), ty })
            }
            ("saturating_add" | "saturating_sub" | "saturating_mul", 1) => {
                let (a, b, ty) = two(self, recv, args[0])?;
                let RType::Int { signed, .. } = &ty else { unreachable!() };
                if *signed {
                    return self.err(&format!("`.{name}()` on signed integers (vstd specifies saturating arithmetic only on unsigned integers)"));
                }
                let (s, op) = (suffix(&ty), match name.as_str() {
                    "saturating_add" => "+",
                    "saturating_sub" => "-",
                    _ => "*",
                });
                // vstd's spec: `if x + y > MAX { MAX } else { (x + y) as T }`
                let text = if op == "-" { format!("(if ({} - {}) < 0 {{ 0{s} }} else {{ (({} - {}) as {s}) }})", a.text, b.text, a.text, b.text) } else { format!("(if ({0} {op} {1}) > {s}::MAX {{ {s}::MAX }} else {{ (({0} {op} {1}) as {s}) }})", a.text, b.text) };
                Ok(T { text, ty })
            }
            ("checked_add" | "checked_sub" | "checked_mul" | "checked_div" | "checked_rem", 1) => {
                let (a, b, ty) = two(self, recv, args[0])?;
                let RType::Int { signed, .. } = &ty else { unreachable!() };
                if *signed {
                    return self.err(&format!("`.{name}()` on signed integers (the translation covers vstd's specifications of `checked_*` on unsigned integers)"));
                }
                let s = suffix(&ty);
                let text = match name.as_str() {
                    "checked_add" => format!("(if ({0} + {1}) > {s}::MAX {{ Option::None }} else {{ Option::Some((({0} + {1}) as {s})) }})", a.text, b.text),
                    "checked_mul" => format!("(if ({0} * {1}) > {s}::MAX {{ Option::None }} else {{ Option::Some((({0} * {1}) as {s})) }})", a.text, b.text),
                    "checked_sub" => format!("(if ({0} - {1}) < 0 {{ Option::None }} else {{ Option::Some((({0} - {1}) as {s})) }})", a.text, b.text),
                    "checked_div" => format!("(if {1} == 0 {{ Option::None }} else {{ Option::Some((({0} / {1}) as {s})) }})", a.text, b.text),
                    _ => format!("(if {1} == 0 {{ Option::None }} else {{ Option::Some((({0} % {1}) as {s})) }})", a.text, b.text),
                };
                Ok(T { text, ty: RType::Option(Box::new(ty)) })
            }
            ("into", 0) => {
                let Some(to) = want.filter(|t| is_int(t)).cloned() else { return self.err("`.into()` whose target type it cannot see (annotate: `let y: u32 = x.into()`, or write `as`)") };
                if !is_int(&recv.ty) {
                    return self.err(&format!("`.into()` of a `{}` (vstd specifies `From`/`Into` only between integer types; write `as`)", crate::types::rust_type(&recv.ty)));
                }
                self.cast(recv, &to)
            }
            ("is_some" | "is_none", 0) => {
                let RType::Option(_) = &recv.ty else { return self.err(&format!("`.{name}()` on something not an `Option`")) };
                Ok(T { text: format!("({} is {})", recv.text, if name == "is_some" { "Some" } else { "None" }), ty: RType::Bool })
            }
            ("unwrap", 0) => {
                let RType::Option(t) = &recv.ty else { return self.err("`.unwrap()` on something not an `Option`") };
                if **t == RType::MathInt {
                    return self.err(&format!("`.unwrap()` on `{}`, whose literal has no type (give it a suffix: `Some(5u32)`)", recv.text));
                }
                Ok(T { text: format!("{}.unwrap()", paren(&recv.text)), ty: (**t).clone() })
            }
            ("unwrap_or", 1) => {
                let RType::Option(t) = &recv.ty.clone() else { return self.err("`.unwrap_or()` on something not an `Option`") };
                let (recv, t) = if **t == RType::MathInt {
                    // `Some(3).unwrap_or(x)`: the literal takes the default's type
                    let d = self.expr(args[0], want.filter(|t| is_int(t)))?;
                    self.cur = span;
                    if !is_int(&d.ty) {
                        return self.err(&format!("`.unwrap_or()` on `{}`, whose literal has no type (give it a suffix: `Some(5u32)`)", recv.text));
                    }
                    let ty = RType::Option(Box::new(d.ty.clone()));
                    let recv = self.coerce(recv, &ty)?;
                    return Ok(T { text: format!("(if {} is Some {{ {}.unwrap() }} else {{ {} }})", recv.text, paren(&recv.text), d.text), ty: d.ty });
                } else {
                    (recv, (**t).clone())
                };
                let d = self.expr(args[0], Some(&t))?;
                self.cur = span;
                let d = self.coerce(d, &t)?;
                Ok(T { text: format!("(if {} is Some {{ {}.unwrap() }} else {{ {} }})", recv.text, paren(&recv.text), d.text), ty: t })
            }
            _ => self.err(&format!("the method `.{name}()`")),
        }
    }

    /// A pattern against a value of type `ty`: its Verus text; the names it
    /// binds are pushed on `env`.
    fn pattern(&mut self, p: &syn::Pat, ty: &RType) -> Result<String> {
        let saved = self.cur;
        self.cur = p.span();
        let r = self.pattern_inner(p, ty);
        if r.is_ok() {
            self.cur = saved;
        }
        r
    }

    /// The bound of a range pattern: a literal (possibly negative) or a
    /// constant, at the scrutinee's type.
    fn range_bound(&mut self, e: &syn::Expr, ty: &RType) -> Result<String> {
        let v = self.expr(e, Some(ty))?;
        match (&v.ty, ty) {
            (RType::MathInt, RType::Int { .. }) | (RType::Char, RType::Char) => Ok(self.coerce(v, ty)?.text),
            (a, b) if a == b && is_int(a) => Ok(v.text),
            _ => self.err("a range pattern whose bounds are not literals (or constants) of the scrutinee's integer or `char` type"),
        }
    }

    fn pattern_inner(&mut self, p: &syn::Pat, ty: &RType) -> Result<String> {
        use syn::Pat as P;
        match p {
            P::Wild(_) => Ok("_".into()),
            P::Ident(i) => {
                if i.by_ref.is_some() || i.mutability.is_some() || i.subpat.is_some() {
                    return self.err("a `ref`/`mut`/`@` pattern");
                }
                let n = i.ident.to_string();
                // a unit variant or `None` written without a path
                if n == "None" {
                    if !matches!(ty, RType::Option(_)) {
                        return self.err("`None` matched against something not an `Option`");
                    }
                    return Ok("Option::None".into());
                }
                if let RType::Named(en) = ty {
                    if let Some(ed) = self.types.enums.get(en) {
                        if ed.variants.iter().any(|v| v.name == n && v.fields.is_empty()) {
                            return Ok(format!("{}::{n}", self.tpath(en)));
                        }
                    }
                }
                // a constant: Rust matches its value, not a fresh binding
                if let Some(c) = self.types.consts.get(&n) {
                    if c.table.is_some() || matches!(c.ty, RType::Seq(..)) {
                        return self.err(&format!("the sequence constant `{n}` as a pattern"));
                    }
                    if c.ty != *ty {
                        return self.fail(&format!("the constant `{n}` (`{}`) is matched against a `{}`", crate::types::rust_type(&c.ty), crate::types::rust_type(ty)));
                    }
                    return Ok(self.cpath(&n));
                }
                if let Some(why) = bad_binder(&n) {
                    return self.err(&why);
                }
                self.env.push((n.clone(), ty.clone()));
                Ok(verus_ident(&n))
            }
            P::Lit(l) => {
                let v = self.expr(&syn::Expr::Lit(l.clone()), Some(ty))?;
                let v = self.coerce(v, ty)?;
                Ok(v.text)
            }
            P::Range(r) => {
                if !matches!(ty, RType::Int { .. } | RType::Char) {
                    return self.err("a range pattern on something not an integer or a `char`");
                }
                let (Some(lo), Some(hi)) = (&r.start, &r.end) else { return self.err("a half-open range pattern (`lo..` or `..=hi`): write both bounds") };
                let lo = self.range_bound(lo, ty)?;
                let hi = self.range_bound(hi, ty)?;
                let dots = match r.limits {
                    syn::RangeLimits::Closed(_) => "..=",
                    syn::RangeLimits::HalfOpen(_) => "..",
                };
                Ok(format!("{lo}{dots}{hi}"))
            }
            P::Or(o) => {
                let mut parts = Vec::new();
                for c in &o.cases {
                    parts.push(self.pattern(c, ty)?);
                }
                Ok(parts.join(" | "))
            }
            P::Paren(pp) => self.pattern(&pp.pat, ty),
            P::Path(pp) => {
                let segs: Vec<String> = pp.path.segments.iter().map(|s| s.ident.to_string()).collect();
                match (segs.len(), ty) {
                    (_, RType::Option(_)) if segs.last().map(|s| s == "None").unwrap_or(false) => Ok("Option::None".into()),
                    (2, RType::Named(en)) if &segs[0] == en => {
                        let Some(ed) = self.types.enums.get(en) else { return self.err(&format!("the pattern `{}`", segs.join("::"))) };
                        if !ed.variants.iter().any(|v| v.name == segs[1] && v.fields.is_empty()) {
                            return self.err(&format!("the pattern `{}` (not a unit variant)", segs.join("::")));
                        }
                        Ok(format!("{}::{}", self.tpath(en), segs[1]))
                    }
                    _ => self.err(&format!("the pattern `{}`", segs.join("::"))),
                }
            }
            P::TupleStruct(ts) => {
                let segs: Vec<String> = ts.path.segments.iter().map(|s| s.ident.to_string()).collect();
                let last = segs.last().cloned().unwrap_or_default();
                match ty {
                    RType::Option(inner) if last == "Some" && ts.elems.len() == 1 => {
                        let inner = (**inner).clone();
                        Ok(format!("Option::Some({})", self.pattern(&ts.elems[0], &inner)?))
                    }
                    RType::Result(a, b) if (last == "Ok" || last == "Err") && ts.elems.len() == 1 => {
                        let t = if last == "Ok" { (**a).clone() } else { (**b).clone() };
                        Ok(format!("Result::{last}({})", self.pattern(&ts.elems[0], &t)?))
                    }
                    RType::Named(en) if segs.len() == 2 && &segs[0] == en => {
                        let Some(ed) = self.types.enums.get(en).cloned() else { return self.err(&format!("the pattern `{}`", segs.join("::"))) };
                        let Some(vd) = ed.variants.iter().find(|v| v.name == last) else { return self.err(&format!("the unknown variant `{}`", segs.join("::"))) };
                        if vd.fields.iter().any(|(n, _)| n.is_some()) {
                            return self.err(&format!("the pattern `{}(…)` on a variant with named fields", segs.join("::")));
                        }
                        // `V(a, .., z)`: the `..` stands for the fields in between
                        let rest = ts.elems.iter().position(|e| matches!(e, P::Rest(_)));
                        let elems: Vec<&P> = ts.elems.iter().collect();
                        let (before, after): (Vec<&P>, Vec<&P>) = match rest {
                            Some(k) => (elems[..k].to_vec(), elems[k + 1..].to_vec()),
                            None => (elems.clone(), Vec::new()),
                        };
                        if after.iter().any(|e| matches!(e, P::Rest(_))) {
                            return self.err("a pattern with two `..`");
                        }
                        let n = vd.fields.len();
                        if (rest.is_none() && before.len() != n) || before.len() + after.len() > n {
                            return self.err(&format!("the pattern `{}(…)` with the wrong number of fields", segs.join("::")));
                        }
                        let mut subs = Vec::new();
                        for (e, (_, t)) in before.iter().zip(&vd.fields) {
                            subs.push(self.pattern(e, t)?);
                        }
                        if rest.is_some() {
                            subs.push("..".into());
                            for (e, (_, t)) in after.iter().zip(&vd.fields[n - after.len()..]) {
                                subs.push(self.pattern(e, t)?);
                            }
                        }
                        Ok(format!("{}::{last}({})", self.tpath(en), subs.join(", ")))
                    }
                    _ => self.err(&format!("the pattern `{}(…)`", segs.join("::"))),
                }
            }
            P::Struct(ps) => {
                let segs: Vec<String> = ps.path.segments.iter().map(|s| s.ident.to_string()).collect();
                let (en, vn) = match (segs.len(), ty) {
                    (2, RType::Named(en)) if &segs[0] == en => (en.clone(), segs[1].clone()),
                    _ => return self.err(&format!("the pattern `{} {{ … }}`", segs.join("::"))),
                };
                let Some(ed) = self.types.enums.get(&en).cloned() else { return self.err(&format!("the pattern `{}`", segs.join("::"))) };
                let Some(vd) = ed.variants.iter().find(|v| v.name == vn) else { return self.err(&format!("the unknown variant `{en}::{vn}`")) };
                let mut subs = Vec::new();
                for f in &ps.fields {
                    self.cur = f.span();
                    let fname = match &f.member {
                        syn::Member::Named(i) => i.to_string(),
                        _ => return self.err("a tuple field in a pattern"),
                    };
                    let Some((_, fty)) = vd.fields.iter().find(|(n, _)| n.as_deref() == Some(fname.as_str())) else { return self.err(&format!("the unknown field `{fname}` of `{en}::{vn}`")) };
                    let fty = fty.clone();
                    let sub = self.pattern(&f.pat, &fty)?;
                    // `Variant { x }` binds `x` (the shorthand stays a shorthand)
                    subs.push(if sub == verus_ident(&fname) { sub } else { format!("{}: {sub}", verus_ident(&fname)) });
                }
                if ps.rest.is_some() {
                    subs.push("..".into());
                }
                Ok(format!("{}::{vn} {{ {} }}", self.tpath(&en), subs.join(", ")))
            }
            P::Rest(_) => self.err("`..` outside a tuple-variant pattern"),
            _ => self.err("a pattern form it does not know (references, slices, tuples)"),
        }
    }
}

/// The machine integer type named `s`, if it is one.
fn int_type(s: &str) -> Option<RType> {
    Some(match s {
        "usize" => RType::Int { signed: false, bits: 0 },
        "isize" => RType::Int { signed: true, bits: 0 },
        "u8" | "u16" | "u32" | "u64" | "u128" | "i8" | "i16" | "i32" | "i64" | "i128" => RType::Int { signed: s.starts_with('i'), bits: s[1..].parse().ok()? },
        _ => return None,
    })
}

fn paren(t: &str) -> String {
    if t.chars().all(|c| c.is_alphanumeric() || c == '_' || c == ':' || c == '#') {
        t.to_string()
    } else {
        format!("({t})")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tr(src: &str) -> Result<Vec<Translated>> {
        let p = crate::parse_program(src).unwrap();
        let used: Vec<String> = p.types.ambient.keys().cloned().collect();
        let mut names = TypeNames::new();
        for n in p.types.enums.keys().chain(p.types.structs.keys()) {
            names.insert(n.clone(), format!("crate::spec::{n}"));
        }
        for n in p.types.consts.keys() {
            names.insert(format!("const:{n}"), format!("crate::spec::{n}"));
        }
        translate_all(&p.types, &used, &names)
    }

    /// The spec fn of `f` in a translation of `src` that calls `f` from `t`.
    fn spec(src: &str, f: &str) -> String {
        let t = tr(src).unwrap();
        t.iter().find(|x| x.name == f).unwrap_or_else(|| panic!("no `{f}` in {:?}", t.iter().map(|x| &x.name).collect::<Vec<_>>())).spec_fn.clone()
    }

    const PRELUDE: &str = "use vstd::prelude::Structural;\npub const LIMIT: u32 = 1000;\n#[derive(Clone, Copy, PartialEq, Eq, Structural)] pub enum Kind { Small, Big(u8), Named { x: u32, y: bool }, Three(u8, u16, u32) }\n#[derive(Clone, Copy)] pub struct Pair { pub a: u32, pub b: u8 }\n#[derive(Clone, Copy, PartialEq, Eq, Structural)] pub struct SP { pub a: u32 }\n";

    #[test]
    fn bump_translates_with_a_cast() {
        let t = tr("pub fn bump(x: u32) -> u32 { if x < 1_000_000 { x + 1 } else { x } }\ndjinn! { pub fn f(k: u32) -> r: u32 { r == bump(k); } }").unwrap();
        assert_eq!(t.len(), 1);
        assert!(t[0].spec_fn.contains("pub open spec fn djinn_amb_bump(x: u32) -> u32 {\n    (if (x < 1000000u32) { ((x + 1u32) as u32) } else { x })\n}"), "{}", t[0].spec_fn);
        assert!(t[0].exec_fn.contains("pub fn bump(x : u32) -> (djinn_r: u32)\n    ensures\n        djinn_r == crate::relations::djinn_amb_bump(x),\n"), "{}", t[0].exec_fn);
    }

    #[test]
    fn enums_options_lets_and_calls() {
        let src = "#[derive(Clone, Copy, PartialEq, Eq)] pub enum Tok { A, B(u8), C { x: u32 } }\npub struct P { pub a: u32 }\n\
            pub fn g(t: Tok, p: P) -> Option<u32> { match t { Tok::A => None, Tok::B(b) => Some(b as u32 * 2), Tok::C { x } => { let y: u32 = x / 2; Some(y + p.a) } } }\n\
            pub fn h(t: Tok, p: P) -> u32 { if let Some(v) = g(t, p) { v.min(7) } else { 0 } }\n\
            djinn! { pub fn f(t: Tok, p: P) -> r: u32 { r == h(t, p); } }";
        let t = tr(src).unwrap();
        let g = t.iter().find(|x| x.name == "g").unwrap();
        assert!(g.spec_fn.contains("(match t { crate::spec::Tok::A => Option::None, crate::spec::Tok::B(b) => Option::Some(((((b) as u32) * 2u32) as u32)), crate::spec::Tok::C { x } => ({ let y: u32 = ((x / 2u32) as u32); Option::Some(((y + p.a) as u32)) }) })"), "{}", g.spec_fn);
        let h = t.iter().find(|x| x.name == "h").unwrap();
        assert!(h.spec_fn.contains("(match crate::relations::djinn_amb_g(t, p) { Option::Some(v) => (vstd::math::min(v as int, 7u32 as int) as u32), _ => 0u32 })"), "{}", h.spec_fn);
        assert_eq!(h.calls, vec!["g".to_string()]);
    }

    #[test]
    fn refused_forms_name_the_construct() {
        let e = tr("pub fn w(x: u32) -> u32 { let mut s = 0; while s < x { s += 1; } s }\ndjinn! { pub fn f(k: u32) -> r: u32 { r == w(k); } }").unwrap_err();
        assert!(e.msg.contains("`let mut`"), "{}", e.msg);
        let e = tr("pub fn rec(x: u32) -> u32 { if x == 0 { 0 } else { rec(x - 1) } }\ndjinn! { pub fn f(k: u32) -> r: u32 { r == rec(k); } }").unwrap_err();
        assert!(e.msg.contains("recursive"), "{}", e.msg);
        let e = tr("pub fn d(x: i32) -> i32 { x / 2 }\ndjinn! { pub fn f(k: i32) -> r: i32 { r == d(k); } }").unwrap_err();
        assert!(e.msg.contains("signed"), "{}", e.msg);
    }

    #[test]
    fn bool_bit_operators_are_the_connectives() {
        let s = spec("pub fn b(a: bool, b: bool, c: bool) -> bool { ((a & b) | c) ^ (a & c) }\ndjinn! { pub fn f(a: bool, b: bool, c: bool) -> r: bool { r == b(a, b, c); } }", "b");
        assert!(s.contains("(((a && b) || c) != (a && c))"), "{s}");
    }

    #[test]
    fn a_constant_in_a_pattern_is_its_value_not_a_binding() {
        let s = spec(&format!("{PRELUDE}pub fn cp(x: u32) -> u32 {{ match x {{ LIMIT => 1, 0 | 7 => 2, _ => 3 }} }}\ndjinn! {{ pub fn f(x: u32) -> r: u32 {{ r == cp(x); }} }}"), "cp");
        assert!(s.contains("(match x { crate::spec::LIMIT => 1u32, 0u32 | 7u32 => 2u32, _ => 3u32 })"), "{s}");
        // a name that is neither a constant nor a variant still binds
        let s = spec(&format!("{PRELUDE}pub fn bind(x: u32) -> u32 {{ match x {{ 0 => 1, n => n }} }}\ndjinn! {{ pub fn f(x: u32) -> r: u32 {{ r == bind(x); }} }}"), "bind");
        assert!(s.contains("(match x { 0u32 => 1u32, n => n })"), "{s}");
        let e = tr(&format!("{PRELUDE}pub fn cp(x: u8) -> u32 {{ match x {{ LIMIT => 1, _ => 3 }} }}\ndjinn! {{ pub fn f(x: u8) -> r: u32 {{ r == cp(x); }} }}")).unwrap_err();
        assert!(e.msg.contains("constant `LIMIT`") && e.msg.contains("`u8`"), "{}", e.msg);
    }

    #[test]
    fn verus_keywords_and_generated_names_cannot_be_variables() {
        let e = tr("pub fn f1(int: u32) -> u32 { int }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == f1(x); } }").unwrap_err();
        assert!(e.msg.contains("`int`") && e.msg.contains("keyword"), "{}", e.msg);
        let e = tr("pub fn f1(x: u32) -> u32 { let nat = x; nat }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == f1(x); } }").unwrap_err();
        assert!(e.msg.contains("`nat`") && e.msg.contains("keyword"), "{}", e.msg);
        let e = tr("pub fn f1(djinn_r: u32) -> u32 { djinn_r }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == f1(x); } }").unwrap_err();
        assert!(e.msg.contains("`djinn_r`") && e.msg.contains("reserved"), "{}", e.msg);
        let e = tr("pub fn f1(o: Option<u32>) -> u32 { match o { Some(spec) => spec, None => 0 } }\ndjinn! { pub fn f(x: Option<u32>) -> r: u32 { r == f1(x); } }").unwrap_err();
        assert!(e.msg.contains("`spec`"), "{}", e.msg);
    }

    #[test]
    fn equality_on_user_types_needs_structural() {
        let e = tr(&format!("{PRELUDE}pub fn pe(p: Pair, q: Pair) -> bool {{ p == q }}\ndjinn! {{ pub fn f(p: Pair, q: Pair) -> r: bool {{ r == pe(p, q); }} }}")).unwrap_err();
        assert!(e.msg.contains("`Pair`") && e.msg.contains("Structural"), "{}", e.msg);
        let e = tr(&format!("{PRELUDE}pub fn pe(p: Option<Pair>) -> bool {{ p != None }}\ndjinn! {{ pub fn f(p: Option<Pair>) -> r: bool {{ r == pe(p); }} }}")).unwrap_err();
        assert!(e.msg.contains("`Pair`") && e.msg.contains("Structural"), "{}", e.msg);
        let s = spec(&format!("{PRELUDE}pub fn ke(k: Kind, s: SP) -> bool {{ k != Kind::Small && Kind::Big(2) == k && s == SP {{ a: 1 }} }}\ndjinn! {{ pub fn f(k: Kind, s: SP) -> r: bool {{ r == ke(k, s); }} }}"), "ke");
        assert!(s.contains("(((k != crate::spec::Kind::Small) && (crate::spec::Kind::Big(2u8) == k)) && (s == crate::spec::SP { a: 1u32 }))"), "{s}");
    }

    #[test]
    fn errors_point_at_the_construct() {
        // the refused `return` is on line 4 of the source
        let src = "pub fn er(x: u32) -> u32 {\n    if x > 3 {\n        return 1;\n    }\n    x\n}\ndjinn! { pub fn f(x: u32) -> r: u32 { r == er(x); } }";
        let e = tr(src).unwrap_err();
        assert!(e.msg.contains("early `return`"), "{}", e.msg);
        assert_eq!(e.span.start().line, 2, "{}", e.msg);
        let src = "pub fn er(x: u32) -> u32 {\n    let y: u32 = x + 1;\n    y.abs()\n}\ndjinn! { pub fn f(x: u32) -> r: u32 { r == er(x); } }";
        let e = tr(src).unwrap_err();
        assert!(e.msg.contains("`.abs()`"), "{}", e.msg);
        assert_eq!(e.span.start().line, 3, "{}", e.msg);
    }

    #[test]
    fn untyped_literals_get_a_suffix_hint() {
        let e = tr("pub fn n(x: u32) -> u32 { let y = !1; y & x }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == n(x); } }").unwrap_err();
        assert!(e.msg.contains("`!1u32`"), "{}", e.msg);
        let e = tr("pub fn n(x: u32) -> u32 { let y = 1 << x; y }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == n(x); } }").unwrap_err();
        assert!(e.msg.contains("`1u32 << …`"), "{}", e.msg);
        // the literal inside `Some` takes the default's type
        let s = spec("pub fn n(x: u32) -> u32 { let y = Some(3).unwrap_or(x as u64); y as u32 }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == n(x); } }", "n");
        assert!(s.contains("let y: u64 = (if Option::Some(3u64) is Some { (Option::Some(3u64)).unwrap() } else { ((x) as u64) });"), "{s}");
        let e = tr("pub fn n(x: u32) -> u32 { let y = Some(3).unwrap_or(None); 1 }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == n(x); } }").unwrap_err();
        assert!(e.msg.contains("Some(5u32)"), "{}", e.msg);
        // with a type from the context, the literal takes it
        let s = spec("pub fn n(x: u32) -> u32 { if x < 32 { 1 << x } else { x + (1 << 3) } }\ndjinn! { pub fn f(x: u32) -> r: u32 { r == n(x); } }", "n");
        assert!(s.contains("(if (x < 32u32) { (1u32 << ((x) as u32)) } else { ((x + (1u32 << 3u32)) as u32) })"), "{s}");
        let s = spec("pub fn n(o: Option<u32>, x: u32) -> u32 { Some(3).unwrap_or(x) + o.unwrap_or(1 + 2) }\ndjinn! { pub fn f(o: Option<u32>, x: u32) -> r: u32 { r == n(o, x); } }", "n");
        assert!(s.contains("((if Option::Some(3u32) is Some { (Option::Some(3u32)).unwrap() } else { x }) + (if o is Some { o.unwrap() } else { ((1u32 + 2u32) as u32) })"), "{s}");
    }

    #[test]
    fn rest_patterns_in_tuple_variants() {
        let s = spec(&format!("{PRELUDE}pub fn rp(k: Kind) -> u32 {{ match k {{ Kind::Big(..) => 1, Kind::Three(a, ..) => a as u32, Kind::Named {{ .. }} => 2, Kind::Small => 0 }} }}\ndjinn! {{ pub fn f(k: Kind) -> r: u32 {{ r == rp(k); }} }}"), "rp");
        assert!(s.contains("(match k { crate::spec::Kind::Big(..) => 1u32, crate::spec::Kind::Three(a, ..) => ((a) as u32), crate::spec::Kind::Named { .. } => 2u32, crate::spec::Kind::Small => 0u32 })"), "{s}");
        let s = spec(&format!("{PRELUDE}pub fn rp(k: Kind) -> u32 {{ match k {{ Kind::Three(.., c) => c, _ => 0 }} }}\ndjinn! {{ pub fn f(k: Kind) -> r: u32 {{ r == rp(k); }} }}"), "rp");
        assert!(s.contains("crate::spec::Kind::Three(.., c) => c"), "{s}");
        let e = tr(&format!("{PRELUDE}pub fn rp(k: Kind) -> u32 {{ match k {{ Kind::Three(a, b, c, d) => 1, _ => 0 }} }}\ndjinn! {{ pub fn f(k: Kind) -> r: u32 {{ r == rp(k); }} }}")).unwrap_err();
        assert!(e.msg.contains("wrong number of fields"), "{}", e.msg);
    }

    #[test]
    fn range_patterns_on_integers_and_chars() {
        let s = spec(&format!("{PRELUDE}pub fn rg(x: u32, c: char) -> u32 {{ match x {{ 1..=5 => 1, 6..10 | 20..=LIMIT => 2, _ => match c {{ 'a'..='z' => 3, _ => 4 }} }} }}\ndjinn! {{ pub fn f(x: u32, c: char) -> r: u32 {{ r == rg(x, c); }} }}"), "rg");
        assert!(s.contains("(match x { 1u32..=5u32 => 1u32, 6u32..10u32 | 20u32..=crate::spec::LIMIT => 2u32, _ => (match c { 'a'..='z' => 3u32, _ => 4u32 }) })"), "{s}");
        let e = tr("pub fn rg(x: i32) -> u32 { match x { -5..=5 => 1, 6.. => 2, _ => 3 } }\ndjinn! { pub fn f(x: i32) -> r: u32 { r == rg(x); } }").unwrap_err();
        assert!(e.msg.contains("half-open"), "{}", e.msg);
        let s = spec("pub fn rg(x: i32) -> u32 { match x { -5..=5 => 1, _ => 3 } }\ndjinn! { pub fn f(x: i32) -> r: u32 { r == rg(x); } }", "rg");
        assert!(s.contains("-5i32..=5i32 => 1u32"), "{s}");
    }

    #[test]
    fn std_cmp_from_into_saturating_and_checked() {
        let s = spec("pub fn mm(a: u32, b: u8) -> u32 { std::cmp::max(a, 3) + core::cmp::min(u32::from(b), 7) }\ndjinn! { pub fn f(a: u32, b: u8) -> r: u32 { r == mm(a, b); } }", "mm");
        assert!(s.contains("(((vstd::math::max(a as int, 3u32 as int) as u32) + (vstd::math::min(((b) as u32) as int, 7u32 as int) as u32)) as u32)"), "{s}");
        let s = spec("pub fn into(b: u8) -> u64 { let w: u64 = b.into(); w }\ndjinn! { pub fn f(b: u8) -> r: u64 { r == into(b); } }", "into");
        assert!(s.contains("let w: u64 = ((b) as u64);"), "{s}");
        let e = tr("pub fn fb(b: bool) -> u32 { u32::from(b) }\ndjinn! { pub fn f(b: bool) -> r: u32 { r == fb(b); } }").unwrap_err();
        assert!(e.msg.contains("`u32::from` of a `bool`"), "{}", e.msg);
        let e = tr("pub fn into(b: u8) -> u64 { let w = b.into(); w }\ndjinn! { pub fn f(b: u8) -> r: u64 { r == into(b); } }").unwrap_err();
        assert!(e.msg.contains("`.into()` whose target type"), "{}", e.msg);
        let s = spec("pub fn sat(a: u32, b: u32) -> u32 { a.saturating_add(b) + a.saturating_sub(1) + a.saturating_mul(b) }\ndjinn! { pub fn f(a: u32, b: u32) -> r: u32 { r == sat(a, b); } }", "sat");
        assert!(s.contains("(if (a + b) > u32::MAX { u32::MAX } else { ((a + b) as u32) })"), "{s}");
        assert!(s.contains("(if (a - 1u32) < 0 { 0u32 } else { ((a - 1u32) as u32) })"), "{s}");
        assert!(s.contains("(if (a * b) > u32::MAX { u32::MAX } else { ((a * b) as u32) })"), "{s}");
        let s = spec("pub fn chk(a: u8, b: u8) -> Option<u8> { if let Some(c) = a.checked_sub(b) { c.checked_div(b) } else { a.checked_add(b) } }\ndjinn! { pub fn f(a: u8, b: u8) -> r: Option<u8> { r == chk(a, b); } }", "chk");
        assert!(s.contains("(match (if (a - b) < 0 { Option::None } else { Option::Some(((a - b) as u8)) }) { Option::Some(c) => (if b == 0 { Option::None } else { Option::Some(((c / b) as u8)) }), _ => (if (a + b) > u8::MAX { Option::None } else { Option::Some(((a + b) as u8)) }) })"), "{s}");
        let e = tr("pub fn sat(a: i32, b: i32) -> i32 { a.saturating_add(b) }\ndjinn! { pub fn f(a: i32, b: i32) -> r: i32 { r == sat(a, b); } }").unwrap_err();
        assert!(e.msg.contains("signed"), "{}", e.msg);
        let e = tr("pub fn re(a: u32, b: u32) -> u32 { a.rem_euclid(b) }\ndjinn! { pub fn f(a: u32, b: u32) -> r: u32 { r == re(a, b); } }").unwrap_err();
        assert!(e.msg.contains("`.rem_euclid()`"), "{}", e.msg);
        let e = tr("pub fn lz(a: u32) -> u32 { a.leading_zeros() }\ndjinn! { pub fn f(a: u32) -> r: u32 { r == lz(a); } }").unwrap_err();
        assert!(e.msg.contains("`.leading_zeros()`") && e.msg.contains("vocab.rs"), "{}", e.msg);
    }
}
