//! Lowering declarations to Lean propositions and obligations.

use crate::ast::*;
use crate::types::*;
use std::collections::HashMap;

/// What the lowering of other declarations needs to know about a callee.
#[derive(Clone, Debug)]
pub struct DeclInfo {
    pub kind: Kind,
    pub inputs: Vec<RType>,
    pub outputs: Vec<RType>,
    pub has_pre: bool,
    pub total: bool,
    /// `#[weakly_specified]`: a caller lifts its choices into its own.
    pub weakly_specified: bool,
    /// Its choices, own and lifted, as `Lowered::choices`: known once it is
    /// lowered, which is why callees are lowered before their callers.
    pub choices: Vec<(String, String)>,
}

#[derive(Clone, Debug)]
pub struct Lowered {
    pub name: String,
    pub kind: Kind,
    pub total: bool,
    /// Spec-level inputs: `(v_old, List I32)`.
    pub inputs: Vec<(String, RType)>,
    pub outputs: Vec<(String, RType)>,
    /// Implementation parameters as Aeneas sees them: `(v, Vec I32)`.
    pub impl_params: Vec<(String, RType)>,
    pub pre: Vec<String>,
    pub spec: Vec<String>,
    pub ensures: Vec<String>,
    pub wf: Vec<String>,
    /// A recursive declaration: the `#[decreases]` measures as `ℤ` terms.
    pub decreases: Vec<String>,
    /// The implementer's choices: Lean name and type. Each is a function of
    /// the inputs (in their views) and of the `for` variables around its
    /// statement (or around the call site, for a choice lifted from a weakly
    /// specified callee), into the view of its type. Extra arguments of
    /// `_body`, existentially closed in `_spec`.
    pub choices: Vec<(String, String)>,
    /// `#[weakly_specified]`.
    pub weakly_specified: bool,
    /// Does the declaration (signature or body) mention a user type, so that
    /// `Spec.lean` needs the Aeneas `Types` module?
    pub uses_types: bool,
    /// Ambient functions the declaration calls (`Spec.lean` then needs the
    /// Aeneas `Funs` module, and Charon must translate them).
    pub ambient_calls: Vec<String>,
    /// The array constants the declaration mentions: name, Aeneas element
    /// type, elements in decimal (`Spec.lean` defines each once).
    pub tables: Vec<(String, RType, Vec<String>)>,
    /// The user types of the signature and every user type their fields
    /// mention, each after the types it contains (`Spec.lean` derives
    /// `Inhabited` for them in this order).
    pub named_types: Vec<String>,
}

#[derive(Clone)]
pub(crate) enum Cx {
    Forall(String, String),
    ForallRange(String, String, String),
    Guard(String),
    /// `match scrut with | pat => P | _ => True`
    /// scrutinee, this arm's pattern, the patterns of the arms before it,
    /// and the number of variants of the enum (a wildcard arm is emitted only
    /// while the arms so far leave some uncovered: Lean rejects a redundant one)
    MatchArm(String, String, Vec<String>, usize),
}

/// The lowering environment of one declaration.
pub(crate) struct L<'a> {
    pub(crate) decls: &'a HashMap<String, DeclInfo>,
    pub(crate) types: &'a TypeDefs,
    pub(crate) names: &'a TypeNames,
    /// variable → (Lean term, type)
    pub(crate) env: HashMap<String, (String, SType)>,
    /// `v` → `v_old` while lowering `requires`.
    pub(crate) pre_scope: bool,
    pub(crate) muts: Vec<String>,
    pub(crate) cx: Vec<Cx>,
    pub(crate) guards: Vec<String>,
    pub(crate) wf: Vec<String>,
    pub(crate) fresh: usize,
    /// The declaration being lowered, when it is recursive: conjunctions
    /// whose right side calls it are emitted as `A ∧ (A → B)` so that Lean's
    /// termination checker sees `A`.
    pub(crate) recursive: Option<String>,
    /// The declaration has choices (own `any`, or lifted from a weakly
    /// specified callee): a recursive one then calls itself through `_body`.
    pub(crate) has_choices: bool,
    /// The inputs as the arguments of every choice function: names, and
    /// view types.
    pub(crate) input_names: Vec<String>,
    pub(crate) input_tys: Vec<String>,
    /// The `for` variables in scope: Lean name and type. A choice made under
    /// them is a function of them (and of the inputs). `some` and `match`
    /// binders are determined by the rest: a choice depending on them would
    /// be circular, and unambiguous for no implementation.
    pub(crate) binders: Vec<(String, String)>,
    /// The choices met so far (see `Lowered::choices`).
    pub(crate) choices: Vec<(String, String)>,
    /// The source names bound by `any` in the blocks being lowered, for
    /// unbinding at the end of each block.
    pub(crate) any_scope: Vec<String>,
    pub(crate) uses_types: bool,
    pub(crate) ambient_calls: Vec<String>,
    pub(crate) tables: Vec<(String, RType, Vec<String>)>,
    /// Types met inside the body (`some` and `any` binders, lifted calls'
    /// outputs, pattern fields): their user types need `Inhabited` too.
    pub(crate) seen_types: Vec<RType>,
    /// Every name of the declaration's source (`Decl::names`): the names the
    /// lowering makes up (`v_call0`, pattern binders `x_0`, …) avoid them.
    pub(crate) user_names: std::collections::HashSet<String>,
    /// The Lean names of the pattern binders made so far: choices avoid them.
    pub(crate) pattern_names: Vec<String>,
}

/// `n'`, inside the guillemets of an escaped name (`«end'»`): Rust names never
/// contain `'`, so a primed name is none of the source's.
fn prime(n: &str) -> String {
    match n.strip_suffix('»') {
        Some(inner) => format!("{inner}'»"),
        None if lean_ident(n) != n => format!("«{n}'»"),
        None => format!("{n}'"),
    }
}

/// Placeholder in a self-call of a declaration with choices: the choice
/// functions, passed on unchanged, are all known only once the whole body
/// is lowered.
const SELF_CHOICES: &str = "⟪SELF_CHOICES⟫";

pub fn decl_info(d: &Decl) -> DeclInfo {
    DeclInfo {
        kind: d.kind,
        inputs: d.inputs().into_iter().map(|(_, t)| t).collect(),
        outputs: d.outputs().into_iter().map(|(_, t)| t).collect(),
        // the implicit preconditions too (a `String`'s UTF-8 and length, a map's
        // size, an array's length): callers owe them like `requires`
        has_pre: !d.requires.is_empty() || d.inputs().iter().any(|(_, t)| matches!(t, RType::Seq(_, SeqKind::String | SeqKind::Array(_)) | RType::Map(..))),
        total: d.total || d.kind == Kind::Func,
        weakly_specified: d.weakly_specified,
        choices: Vec::new(),
    }
}

pub fn lower(d: &Decl, decls: &HashMap<String, DeclInfo>, types: &TypeDefs) -> Result<Lowered> {
    lower_with(d, decls, types, &TypeNames::new())
}

pub fn lower_with(d: &Decl, decls: &HashMap<String, DeclInfo>, types: &TypeDefs, names: &TypeNames) -> Result<Lowered> {
    // ambiguity is declared, never silent: a fn that leaves a choice to the
    // implementer, or calls one that does, carries `#[weakly_specified]`,
    // and nothing else does
    let own = !d.choices().is_empty();
    let is_weak = |f: &str| decls.get(f).map(|i| i.weakly_specified).unwrap_or(false);
    let inherits = d.inherits_ambiguity(is_weak);
    if d.kind == Kind::Func && inherits && !d.weakly_specified {
        let weak = d.callees().into_iter().find(|f| is_weak(f)).unwrap_or_default();
        return Err(Error::new(d.name_span, format!("`{}` calls `{weak}`, which is weakly specified, so it inherits the implementer's choices: mark it `#[weakly_specified]`, so that a human reviews it", d.name)));
    }
    if d.weakly_specified && !own && !inherits {
        return Err(Error::new(d.name_span, format!("`{}` is marked `#[weakly_specified]` but has no `any` and calls no weakly specified fn: drop the attribute", d.name)));
    }
    let mut env = HashMap::new();
    for (n, t) in d.inputs() {
        env.insert(n.clone(), (lean_ident(&n), SType::Of(t)));
    }
    let muts: Vec<String> = d.params.iter().filter(|p| p.mut_ref).map(|p| p.name.clone()).collect();
    let mut l = L {
        decls,
        types,
        names,
        env,
        pre_scope: true,
        muts,
        cx: vec![],
        guards: vec![],
        wf: vec![],
        fresh: 0,
        recursive: if d.is_recursive() { Some(d.name.clone()) } else { None },
        has_choices: own || (d.kind == Kind::Func && inherits),
        input_names: d.inputs().into_iter().map(|(n, _)| lean_ident(&n)).collect(),
        input_tys: d.inputs().iter().map(|(_, t)| view_type(t, names)).collect(),
        binders: Vec::new(),
        choices: Vec::new(),
        any_scope: Vec::new(),
        uses_types: d.params.iter().any(|p| p.ty.needs_code_types())
            || d.ret.as_ref().map(|(_, t)| t.needs_code_types()).unwrap_or(false)
            || d.choices().iter().any(|c| c.ty.needs_code_types()),
        ambient_calls: Vec::new(),
        tables: Vec::new(),
        seen_types: Vec::new(),
        user_names: d.names().into_iter().flat_map(|n| [lean_ident(&n), n]).collect(),
        pattern_names: Vec::new(),
    };
    let mut pre = Vec::new();
    // what Rust guarantees of its values and the mathematical view does not
    // say (see `implicit_facts`), for the inputs and the values inside them
    for (n, t) in d.inputs() {
        pre.extend(implicit_facts(&lean_ident(&n), &t, true, types, &mut Vec::new(), 0, d.name_span)?);
    }
    for e in &d.requires {
        pre.push(l.constraint(e)?);
    }
    let mut decreases = Vec::new();
    for e in &d.decreases {
        decreases.push(l.num(e)?);
    }
    l.guards.clear();
    // outputs come into scope
    l.pre_scope = false;
    for (n, t) in d.outputs() {
        l.env.insert(n.clone(), (lean_ident(&n), SType::Of(t)));
    }
    let mut spec = Vec::new();
    // an output array `[T; N]` holds exactly `N` elements: part of what the
    // implementation guarantees, and what makes the output unambiguous
    for (n, t) in d.outputs() {
        if let RType::Seq(_, SeqKind::Array(len)) = &t {
            spec.push(format!("({}.length : ℤ) = {}", lean_ident(&n), array_len(len, types, d.name_span)?));
        }
    }
    for s in &d.body {
        spec.push(l.stmt(s)?);
    }
    // a recursive declaration: the top-level statements chained `A ∧ (A → B)`
    // as nested ones are, so that its termination proof sees the facts
    // before a recursive call
    if l.recursive.is_some() && spec.len() > 1 {
        let all = std::mem::take(&mut spec);
        spec.push(l.conj_rec(all));
    }
    let mut named_types = Vec::new();
    let mut seen = Vec::new();
    for (_, t) in d.inputs().iter().chain(d.outputs().iter()) {
        named_closure(t, types, &mut seen, &mut named_types);
    }
    for c in d.choices() {
        named_closure(&c.ty, types, &mut seen, &mut named_types);
    }
    for t in &l.seen_types {
        named_closure(t, types, &mut seen, &mut named_types);
    }
    let mut ensures = Vec::new();
    for e in &d.ensures {
        ensures.push(l.constraint(e)?);
    }
    // a self-call of a declaration with choices passes them all on: now
    // every choice is known
    let mut wf = l.wf;
    if l.has_choices {
        let all = l.choices.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>().join(" ");
        let fill = |x: &mut String| *x = x.replace(SELF_CHOICES, &all);
        pre.iter_mut().chain(spec.iter_mut()).chain(ensures.iter_mut()).chain(wf.iter_mut()).chain(decreases.iter_mut()).for_each(fill);
    }
    Ok(Lowered {
        name: d.name.clone(),
        kind: d.kind,
        total: d.total,
        inputs: d.inputs(),
        outputs: d.outputs(),
        impl_params: d.params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect(),
        pre,
        spec,
        ensures,
        wf,
        decreases,
        choices: l.choices,
        weakly_specified: d.weakly_specified,
        uses_types: l.uses_types,
        ambient_calls: l.ambient_calls,
        tables: l.tables,
        named_types,
    })
}

/// What Rust guarantees of a value of type `t` and its view does not say:
/// a `String` or a `HashMap` holds at most `usize::MAX` bytes / entries, a
/// `String` is valid UTF-8 (its view is the bytes of some Lean string; a
/// `rel`'s `String` input is otherwise any byte list), an array `[T; N]` holds
/// exactly `N` elements; and so for the elements of a sequence, the contents
/// of an `Option` and the fields of a struct. `term` is the value's view
/// (`view`) or its Aeneas value (inside a struct, whose fields are Aeneas
/// values: a `String` field is a Lean string, UTF-8 already). `stack` holds
/// the structs being unfolded (a recursive one is not unfolded again).
fn implicit_facts(term: &str, t: &RType, view: bool, types: &TypeDefs, stack: &mut Vec<String>, depth: usize, span: proc_macro2::Span) -> Result<Vec<String>> {
    let mut out = Vec::new();
    // binders no Rust name can be, distinct at each depth
    let y = format!("e{}", "'".repeat(depth + 1));
    match t {
        RType::Seq(_, SeqKind::String) if view => {
            out.push(format!("({term}.length : ℤ) ≤ ((Usize.max : ℕ) : ℤ)"));
            // a binder no input can capture: inputs are Rust names, `s'` is none
            out.push(format!("(∃ s' : String, Djinn.Vocab.bytes s' = {term})"));
        }
        RType::Seq(_, SeqKind::String) => out.push(format!("((Djinn.Vocab.bytes {term}).length : ℤ) ≤ ((Usize.max : ℕ) : ℤ)")),
        RType::Map(..) if view => out.push(format!("({term}.length : ℤ) ≤ ((Usize.max : ℕ) : ℤ)")),
        RType::Map(..) => out.push(format!("({term}.entries.length : ℤ) ≤ ((Usize.max : ℕ) : ℤ)")),
        RType::Seq(e, kind) => {
            if let (SeqKind::Array(len), true) = (kind, view) {
                out.push(format!("({term}.length : ℤ) = {}", array_len(len, types, span)?));
            }
            if !matches!(kind, SeqKind::Str) {
                let inner = implicit_facts(&y, e, view, types, stack, depth + 1, span)?;
                if !inner.is_empty() {
                    let elems = if view { term.to_string() } else { format!("{term}.val") };
                    out.push(format!("(∀ {y}, {y} ∈ {elems} → {})", conj(inner)));
                }
            }
        }
        RType::Option(e) => {
            let inner = implicit_facts(&y, e, view, types, stack, depth + 1, span)?;
            if !inner.is_empty() {
                out.push(format!("(∀ {y}, {term} = some {y} → {})", conj(inner)));
            }
        }
        RType::Named(n) if !stack.contains(n) => {
            if let Some(sd) = types.structs.get(n) {
                stack.push(n.clone());
                for (f, ft) in &sd.fields {
                    out.extend(implicit_facts(&format!("{term}.{}", lean_ident(f)), ft, false, types, stack, depth, span)?);
                }
                stack.pop();
            }
        }
        _ => {}
    }
    Ok(out)
}

/// Does a value of type `t` carry implicit preconditions (`implicit_facts`)?
fn has_implicit_facts(t: &RType, types: &TypeDefs) -> bool {
    implicit_facts("x", t, true, types, &mut Vec::new(), 0, proc_macro2::Span::call_site()).map(|f| !f.is_empty()).unwrap_or(true)
}

/// `t`'s user types and, first, those their fields mention (post-order).
fn named_closure(t: &RType, types: &TypeDefs, seen: &mut Vec<String>, out: &mut Vec<String>) {
    match t {
        RType::Named(n) => {
            if seen.contains(n) {
                return;
            }
            seen.push(n.clone());
            if let Some(s) = types.structs.get(n) {
                for (_, ft) in &s.fields {
                    named_closure(ft, types, seen, out);
                }
            }
            if let Some(e) = types.enums.get(n) {
                for v in &e.variants {
                    for (_, ft) in &v.fields {
                        named_closure(ft, types, seen, out);
                    }
                }
            }
            out.push(n.clone());
        }
        RType::Seq(e, _) | RType::Option(e) => named_closure(e, types, seen, out),
        RType::Result(a, b) | RType::Map(a, b) => {
            named_closure(a, types, seen, out);
            named_closure(b, types, seen, out);
        }
        _ => {}
    }
}

/// The length of an array type `[T; N]`: a literal, or an integer constant
/// of the specification file.
fn array_len(len: &str, types: &TypeDefs, span: proc_macro2::Span) -> Result<String> {
    let len = len.trim();
    if len.chars().all(|c| c.is_ascii_digit() || c == '_') {
        return Ok(len.replace('_', ""));
    }
    match types.consts.get(len).map(|c| &c.value.kind) {
        Some(ExprKind::Int(v)) => Ok(v.clone()),
        _ => Err(Error::new(span, format!("array length `{len}`: write a literal or an integer `const` of the specification file"))),
    }
}

pub(crate) fn conj(ps: Vec<String>) -> String {
    match ps.len() {
        0 => "True".into(),
        1 => ps.into_iter().next().unwrap(),
        _ => format!("({})", ps.join(" ∧ ")),
    }
}

pub(crate) fn is_atom(s: &str) -> bool {
    if s.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || c == '.') {
        return true;
    }
    // a single balanced parenthesized group counts as atomic
    if s.starts_with('(') && s.ends_with(')') {
        let mut depth = 0i32;
        for (i, c) in s.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 && i + 1 != s.len() {
                        return false;
                    }
                }
                _ => {}
            }
        }
        return depth == 0;
    }
    false
}

/// The width of a machine integer type, as a Lean `Nat` term.
fn width_lean(signed: bool, bits: u32) -> String {
    match (bits, signed) {
        (0, false) => "UScalarTy.Usize.numBits".to_string(),
        (0, true) => "IScalarTy.Isize.numBits".to_string(),
        (b, _) => b.to_string(),
    }
}

/// `t`, parenthesized unless atomic.
fn paren(t: &str) -> String {
    if is_atom(t) {
        t.to_string()
    } else {
        format!("({t})")
    }
}

/// `t.toNat` for an integer term `t`, ascribed `: ℤ` unless `t` is a variable: an expression of
/// literals (`64 * 268435456`, `8 - 3`) would otherwise elaborate in `ℕ`, where `.toNat` is no
/// operation.
pub(crate) fn to_nat(t: &str) -> String {
    if is_atom(t) && !t.chars().all(|c| c.is_ascii_digit()) && !t.starts_with('(') {
        format!("{t}.toNat")
    } else {
        format!("({t} : ℤ).toNat")
    }
}

fn dotval(t: &str) -> String {
    if is_atom(t) {
        format!("{t}.val")
    } else {
        format!("({t}).val")
    }
}

/// A Lean `Char` literal.
pub(crate) fn char_lit(c: char) -> String {
    if c.is_ascii_alphanumeric() || (c.is_ascii_punctuation() && c != '\'' && c != '\\') || c == ' ' {
        format!("'{c}'")
    } else {
        format!("(Char.ofNat {})", c as u32)
    }
}

/// A Lean `List U8` literal for a byte string.
pub(crate) fn bytes_lit(b: &[u8]) -> String {
    if b.is_empty() {
        "([] : List U8)".into()
    } else {
        format!("[{}]", b.iter().map(|x| format!("{x}#u8")).collect::<Vec<_>>().join(", "))
    }
}

/// What the lowering needs to know about something a constraint may call: a
/// declaration of the specification, or an ambient function of the file.
#[derive(Clone)]
pub(crate) enum Callee {
    Decl(DeclInfo),
    Ambient(Ambient),
}

impl Callee {
    fn inputs(&self) -> Vec<RType> {
        match self {
            Callee::Decl(i) => i.inputs.clone(),
            Callee::Ambient(a) => a.params.iter().map(|(_, t)| t.clone()).collect(),
        }
    }
    fn outputs(&self) -> Vec<RType> {
        match self {
            Callee::Decl(i) => i.outputs.clone(),
            Callee::Ambient(a) => vec![a.ret.clone()],
        }
    }
}

impl<'a> L<'a> {
    /// The callee named `f`, if a constraint may call it.
    pub(crate) fn callee(&self, f: &str) -> Option<Callee> {
        if let Some(i) = self.decls.get(f) {
            return Some(Callee::Decl(i.clone()));
        }
        self.types.ambient.get(f).map(|a| Callee::Ambient(a.clone()))
    }

    /// A made-up Lean name, `base` unless the source uses that name (then
    /// primed until it is none of the source's).
    pub(crate) fn avoid(&self, base: String) -> String {
        let mut n = base;
        while self.user_names.contains(&n) {
            n = prime(&n);
        }
        n
    }

    /// The Lean name of the Aeneas model of an ambient function.
    fn ambient_lean(&self, f: &str) -> String {
        self.names.get(&format!("fn:{f}")).cloned().unwrap_or_else(|| f.to_string())
    }

    pub(crate) fn wrap(&self, p: String) -> String {
        let mut p = p;
        for c in self.cx.iter().rev() {
            p = match c {
                Cx::Forall(x, t) => format!("∀ {x} : {t}, {p}"),
                Cx::ForallRange(i, lo, hi) => format!("∀ {i} : ℤ, {lo} ≤ {i} → {i} < {hi} → {p}"),
                Cx::Guard(g) => format!("{g} → {p}"),
                Cx::MatchArm(s, pat, prev, nvariants) => {
                    // the item holds in this arm only: the earlier arms are
                    // vacuous, and so is the rest unless this arm is the `_`
                    let before: String = prev.iter().map(|q| format!("| {q} => True ")).collect();
                    if pat == "_" {
                        format!("(match {s} with {before}| _ => {p})")
                    } else if prev.len() + 1 < *nvariants {
                        format!("(match {s} with {before}| {pat} => {p} | _ => True)")
                    } else {
                        format!("(match {s} with {before}| {pat} => {p})")
                    }
                }
            };
        }
        p
    }

    pub(crate) fn flush_guards(&mut self) {
        if !self.guards.is_empty() {
            let gs: Vec<String> = self.guards.drain(..).map(|g| format!("({g})")).collect();
            let p = gs.join(" ∧ ");
            let w = self.wrap(p);
            self.wf.push(w);
        }
    }

    /// Bind names to Lean terms for the duration of `f`.
    pub(crate) fn with_env<T>(&mut self, binds: &[(String, String, SType)], f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let mut saved = Vec::new();
        for (n, term, t) in binds {
            saved.push((n.clone(), self.env.insert(n.clone(), (term.clone(), t.clone()))));
        }
        let r = f(self);
        for (n, old) in saved {
            match old {
                Some(t) => self.env.insert(n, t),
                None => self.env.remove(&n),
            };
        }
        r
    }

    /// Bind names to themselves.
    pub(crate) fn with_vars<T>(&mut self, binds: &[(String, SType)], f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let b: Vec<(String, String, SType)> = binds.iter().map(|(n, t)| (n.clone(), lean_ident(n), t.clone())).collect();
        self.with_env(&b, f)
    }

    /// `A ∧ B`, written `A ∧ (A → B)` when lowering a recursive declaration
    /// and `B` calls it (the termination checker then sees `A`).
    /// The text a self-call contains: a declaration with choices calls
    /// itself through `_body`.
    fn self_marker(&self, me: &str) -> String {
        if self.has_choices {
            format!("{me}_body ")
        } else {
            format!("{me}_spec ")
        }
    }

    fn conj_rec(&self, ps: Vec<String>) -> String {
        let Some(me) = &self.recursive else { return conj(ps) };
        let marker = self.self_marker(me);
        if ps.len() < 2 || !ps.iter().skip(1).any(|p| p.contains(&marker)) {
            return conj(ps);
        }
        // right-nested, so that every later conjunct sees the earlier ones as
        // hypotheses and each conjunct is written at most twice
        // a conjunct that itself calls the declaration is never a hypothesis:
        // Lean would embed the termination proof of that call in the
        // hypothesis's type and later rewriting of the context would fail
        let mut acc = ps[ps.len() - 1].clone();
        for p in ps[..ps.len() - 1].iter().rev() {
            acc = if acc.contains(&marker) && !p.contains(&marker) { format!("({p} ∧ ({p} → {acc}))") } else { format!("({p} ∧ {acc})") };
        }
        acc
    }

    fn calls_me(&self, p: &str) -> bool {
        self.recursive.as_ref().map(|me| p.contains(&self.self_marker(me))).unwrap_or(false)
    }

    pub(crate) fn stmts(&mut self, ss: &[Stmt]) -> Result<String> {
        let mut v = Vec::new();
        // a choice (`any`) is in scope to the end of its block
        let mark = self.any_scope.len();
        for s in ss {
            v.push(self.stmt(s)?);
        }
        for n in self.any_scope.split_off(mark) {
            self.env.remove(&n);
        }
        Ok(self.conj_rec(v))
    }

    /// A fresh choice: a function of the inputs and of the binders in scope
    /// into `ty` (a Lean type), named after `name`; returns its Lean name
    /// and the term it stands for here (the function applied).
    fn new_choice(&mut self, name: &str, ty: &str) -> (String, String) {
        // distinct Lean names for choices of the same source name in
        // sibling blocks, or lifted from several calls of the same callee
        // (and from the source's names and the pattern binders, which a
        // suffixed name could otherwise be)
        let mut lean = lean_ident(name);
        let mut k = 1;
        while self.choices.iter().any(|(n, _)| n == &lean) || self.input_names.contains(&lean) || self.pattern_names.contains(&lean) || (k > 1 && self.user_names.contains(&lean)) {
            lean = lean_ident(&format!("{name}_{k}"));
            k += 1;
        }
        let paren = |t: &str| if t.contains(' ') { format!("({t})") } else { t.to_string() };
        let mut fun_ty: Vec<String> = self.input_tys.iter().map(|t| paren(t)).collect();
        fun_ty.extend(self.binders.iter().map(|(_, t)| paren(t)));
        fun_ty.push(ty.to_string());
        self.choices.push((lean.clone(), fun_ty.join(" → ")));
        let args: Vec<String> = self.input_names.iter().cloned().chain(self.binders.iter().map(|(n, _)| n.clone())).collect();
        let term = if args.is_empty() { lean.clone() } else { format!("({lean} {})", args.join(" ")) };
        (lean, term)
    }

    /// `any x: T where c;` — `x` is a fresh choice function applied to the
    /// inputs and binders; only `c` remains to be stated.
    fn any_stmt(&mut self, name: &str, ty: &RType, wherec: &Expr) -> Result<String> {
        let (_, term) = self.new_choice(name, &view_type(ty, self.names));
        self.env.insert(name.to_string(), (term, SType::Of(ty.clone())));
        self.any_scope.push(name.to_string());
        self.constraint(wherec)
    }

    pub(crate) fn stmt(&mut self, s: &Stmt) -> Result<String> {
        let span = s.span;
        match &s.kind {
            StmtKind::Constraint(e) => self.constraint(e),
            StmtKind::ForIn { var, seq, body } => {
                // a value-`if` calling relations in the sequence: the loop of
                // the branch taken (`if c { for x in a … } else { for x in b … }`)
                if let Some((c, a, b)) = self.split_if(seq) {
                    let mk = |s: Expr| vec![Stmt { span, kind: StmtKind::ForIn { var: var.clone(), seq: s, body: body.clone() } }];
                    return self.split_stmt(&c, mk(a), mk(b), span);
                }
                // a relation called in the sequence: lifted around the loop
                let mut lifted = Vec::new();
                let seq2 = self.lift_calls(seq, &mut lifted)?;
                if !lifted.is_empty() {
                    let binds = lifted_binds(&lifted);
                    let k = StmtKind::ForIn { var: var.clone(), seq: seq2, body: body.clone() };
                    let s2 = Stmt { span, kind: k };
                    return self.wrap_lifted(lifted, &binds, span, |l| l.stmt(&s2));
                }
                let (st, ty) = self.term(seq)?;
                let elem = match &ty {
                    SType::Of(RType::Seq(e, _)) => SType::Of((**e).clone()),
                    _ => return Err(Error::new(seq.span, format!("`for {var} in ..` needs a sequence"))),
                };
                self.flush_guards();
                let et = stype_lean(&elem, self.names);
                let v = lean_ident(var);
                self.cx.push(Cx::Forall(v.clone(), et.clone()));
                self.binders.push((v.clone(), et));
                let b = self.with_vars(&[(var.clone(), elem)], |l| l.stmts(body))?;
                self.binders.pop();
                self.cx.pop();
                Ok(format!("(∀ {v}, {v} ∈ {st} → {b})"))
            }
            StmtKind::ForRange { var, lo, hi, body } => {
                // a value-`if` calling relations in a bound: the loop of the
                // branch taken
                for (k, bound) in [lo, hi].into_iter().enumerate() {
                    if let Some((c, a, b)) = self.split_if(bound) {
                        let mk = |x: Expr| {
                            let (l2, h2) = if k == 0 { (x, hi.clone()) } else { (lo.clone(), x) };
                            vec![Stmt { span, kind: StmtKind::ForRange { var: var.clone(), lo: l2, hi: h2, body: body.clone() } }]
                        };
                        return self.split_stmt(&c, mk(a), mk(b), span);
                    }
                }
                // relations called in the bounds: lifted around the loop
                let mut lifted = Vec::new();
                let lo2 = self.lift_calls(lo, &mut lifted)?;
                let hi2 = self.lift_calls(hi, &mut lifted)?;
                if !lifted.is_empty() {
                    let binds = lifted_binds(&lifted);
                    let k = StmtKind::ForRange { var: var.clone(), lo: lo2, hi: hi2, body: body.clone() };
                    let s2 = Stmt { span, kind: k };
                    return self.wrap_lifted(lifted, &binds, span, |l| l.stmt(&s2));
                }
                let lo = self.num(lo)?;
                let hi = self.num(hi)?;
                self.flush_guards();
                let v = lean_ident(var);
                self.cx.push(Cx::ForallRange(v.clone(), lo.clone(), hi.clone()));
                self.binders.push((v.clone(), "ℤ".into()));
                let b = self.with_vars(&[(var.clone(), SType::Int)], |l| l.stmts(body))?;
                self.binders.pop();
                self.cx.pop();
                Ok(format!("(∀ {v} : ℤ, {lo} ≤ {v} → {v} < {hi} → {b})"))
            }
            StmtKind::Some { binders, body } => {
                self.seen_types.extend(binders.iter().map(|(_, t)| t.clone()));
                let binds: Vec<(String, SType)> = binders.iter().map(|(n, t)| (n.clone(), SType::Of(t.clone()))).collect();
                let bs: Vec<String> = binders.iter().map(|(n, t)| format!("({} : {})", lean_ident(n), view_type(t, self.names))).collect();
                // Well-formedness items inside escape universally, guarded by the
                // body (djinnc §6.5): lower the body once to obtain the guard,
                // discarding the items, then once more under the guard.
                let saved = self.wf.len();
                let saved_choices = self.choices.len();
                let guard = self.with_vars(&binds, |l| l.stmts(body))?;
                self.wf.truncate(saved);
                // choices lifted at call sites inside: made again, under the
                // binders, by the second lowering
                self.choices.truncate(saved_choices);
                self.guards.clear();
                for (n, t) in &binds {
                    self.cx.push(Cx::Forall(lean_ident(n), stype_lean(t, self.names)));
                }
                self.cx.push(Cx::Guard(guard));
                let b = self.with_vars(&binds, |l| l.stmts(body))?;
                self.cx.pop();
                for _ in &binds {
                    self.cx.pop();
                }
                Ok(format!("(∃ {}, {})", bs.join(" "), b))
            }
            StmtKind::Any { name, ty, wherec } => self.any_stmt(name, ty, wherec),
            StmtKind::Cases(alts) => {
                let mut v = Vec::new();
                for a in alts {
                    v.push(self.stmt(a)?);
                }
                Ok(format!("({})", v.join(" ∨ ")))
            }
            StmtKind::If { cond, then, els } => {
                // conditions may call funcs/rels: lifted like a constraint (djinnc §6.8 closes each side)
                let c = self.constraint_inner(cond)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(c.clone()));
                let t = self.stmts(then)?;
                self.cx.pop();
                match els {
                    None => Ok(format!("({c} → {t})")),
                    Some(e) => {
                        self.cx.push(Cx::Guard(format!("¬({c})")));
                        let e = self.stmts(e)?;
                        self.cx.pop();
                        Ok(format!("(({c} → {t}) ∧ (¬({c}) → {e}))"))
                    }
                }
            }
            StmtKind::Implies(c, s) => {
                let c = self.constraint_inner(c)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(c.clone()));
                let b = self.stmt(s)?;
                self.cx.pop();
                Ok(format!("({c} → {b})"))
            }
            StmtKind::Match { scrutinee, arms } => self.match_stmt(scrutinee, arms, span),
        }
    }

    /// `match t { Enum::V(x) => … }` as a Lean `match` on the Aeneas inductive.
    fn match_stmt(&mut self, scrutinee: &Expr, arms: &[Arm], span: proc_macro2::Span) -> Result<String> {
        let (st, ty) = self.term(scrutinee)?;
        // `Option` and `Result` match like two-variant enums; their contents are
        // already in their views (a user enum's fields are Aeneas values)
        let builtin = matches!(&ty, SType::Of(RType::Option(_) | RType::Result(..)));
        let (ename, edef) = match &ty {
            SType::Of(RType::Named(n)) => {
                let d = self.types.enums.get(n).cloned().ok_or_else(|| Error::new(scrutinee.span, format!("`{n}` is not an enum declared in the specification file")))?;
                self.uses_types = true;
                (n.clone(), d)
            }
            SType::Of(RType::Option(inner)) => (
                "Option".to_string(),
                EnumDef { name: "Option".into(), variants: vec![VariantDef { name: "None".into(), fields: vec![] }, VariantDef { name: "Some".into(), fields: vec![(None, (**inner).clone())] }] },
            ),
            SType::Of(RType::Result(a, b)) => (
                "Result".to_string(),
                EnumDef { name: "Result".into(), variants: vec![VariantDef { name: "Ok".into(), fields: vec![(None, (**a).clone())] }, VariantDef { name: "Err".into(), fields: vec![(None, (**b).clone())] }] },
            ),
            _ => return Err(Error::new(scrutinee.span, "`match` needs a value of a user enum type, an `Option` or a `Result`")),
        };
        // the Lean constructor of a variant
        let ctor = |v: &str| match (builtin, v) {
            (true, "Some") => "some".to_string(),
            (true, "None") => "none".to_string(),
            _ => v.to_string(),
        };
        self.flush_guards();
        let lean_enum = self.names.get(&ename).cloned().unwrap_or(ename.clone());
        let mut lines = Vec::new();
        let mut prev_pats: Vec<String> = Vec::new();
        let mut covered: Vec<String> = Vec::new();
        let mut has_wild = false;
        for a in arms {
            match &a.pat {
                Pattern::Wild => {
                    has_wild = true;
                    self.cx.push(Cx::MatchArm(st.clone(), "_".into(), prev_pats.clone(), edef.variants.len()));
                    let b = self.stmts(&a.body)?;
                    self.cx.pop();
                    prev_pats.push("_".into());
                    lines.push(format!("| _ => {b}"));
                }
                Pattern::Variant { enum_name, variant, fields } => {
                    if enum_name != &ename {
                        return Err(Error::new(a.span, format!("pattern of `{enum_name}` in a match on `{ename}`")));
                    }
                    let vdef = edef.variants.iter().find(|v| &v.name == variant).ok_or_else(|| Error::new(a.span, format!("`{ename}` has no variant `{variant}`")))?;
                    if covered.contains(variant) {
                        return Err(Error::new(a.span, format!("variant `{variant}` matched twice")));
                    }
                    covered.push(variant.clone());
                    // one Lean binder per field, in declaration order; the
                    // pattern's names bound to their views
                    let mut lean_binders = Vec::new();
                    let mut binds: Vec<(String, String, SType)> = Vec::new();
                    let field_names: Vec<Option<String>> = match fields {
                        PatFields::Unit => {
                            if !vdef.fields.is_empty() {
                                return Err(Error::new(a.span, format!("`{ename}::{variant}` has {} field(s); bind or ignore them", vdef.fields.len())));
                            }
                            vec![]
                        }
                        PatFields::Tuple(v) => {
                            if v.len() != vdef.fields.len() {
                                return Err(Error::new(a.span, format!("`{ename}::{variant}` has {} field(s), the pattern names {}", vdef.fields.len(), v.len())));
                            }
                            v.clone()
                        }
                        PatFields::Struct(v, dots) => {
                            let mut out = vec![None; vdef.fields.len()];
                            for (f, b) in v {
                                let i = vdef.fields.iter().position(|(n, _)| n.as_deref() == Some(f.as_str())).ok_or_else(|| Error::new(a.span, format!("`{ename}::{variant}` has no field `{f}`")))?;
                                out[i] = b.clone();
                            }
                            if !dots {
                                let missing: Vec<String> = vdef.fields.iter().filter(|(n, _)| !v.iter().any(|(f, _)| Some(f) == n.as_ref())).filter_map(|(n, _)| n.clone()).collect();
                                if !missing.is_empty() {
                                    return Err(Error::new(a.span, format!("pattern does not mention field(s) {}; add `..` to ignore them", missing.join(", "))));
                                }
                            }
                            out
                        }
                    };
                    for (k, ((_, fty), binder)) in vdef.fields.iter().zip(field_names.iter()).enumerate() {
                        match binder {
                            None => lean_binders.push("_".to_string()),
                            Some(b) => {
                                // `x_0`, unless the source or a choice has that name
                                let mut lean = lean_ident(&format!("{b}_{k}"));
                                while self.user_names.contains(&lean) || self.choices.iter().any(|(n, _)| n == &lean) {
                                    lean = prime(&lean);
                                }
                                self.pattern_names.push(lean.clone());
                                lean_binders.push(lean.clone());
                                self.seen_types.push(fty.clone());
                                let term = if builtin { lean.clone() } else { view_term(&lean, fty) };
                                binds.push((b.clone(), term, SType::Of(fty.clone())));
                            }
                        }
                    }
                    let pat = if lean_binders.is_empty() { format!(".{}", ctor(variant)) } else { format!(".{} {}", ctor(variant), lean_binders.join(" ")) };
                    self.cx.push(Cx::MatchArm(st.clone(), pat.clone(), prev_pats.clone(), edef.variants.len()));
                    let b = self.with_env(&binds, |l| l.stmts(&a.body))?;
                    self.cx.pop();
                    prev_pats.push(pat.clone());
                    lines.push(format!("| {pat} => {b}"));
                }
            }
        }
        if !has_wild {
            let missing: Vec<&str> = edef.variants.iter().map(|v| v.name.as_str()).filter(|v| !covered.iter().any(|c| c == v)).collect();
            if !missing.is_empty() {
                return Err(Error::new(span, format!("non-exhaustive `match` on `{ename}`: missing {}", missing.iter().map(|m| format!("`{ename}::{m}`")).collect::<Vec<_>>().join(", "))));
            }
        }
        let _ = lean_enum;
        Ok(format!("(match {st} with {})", lines.join(" ")))
    }

    /// A top-level constraint: relational call lifting happens here.
    pub(crate) fn constraint(&mut self, e: &Expr) -> Result<String> {
        let p = self.constraint_inner(e)?;
        self.flush_guards();
        Ok(p)
    }

    pub(crate) fn constraint_inner(&mut self, e: &Expr) -> Result<String> {
        // a value-`if` whose branches call relations: the constraint holds of
        // the branch the condition picks, `(c → P[a]) ∧ (¬c → P[b])`, so that
        // each branch's calls (and their preconditions) are stated only
        // where the branch is taken
        if let Some((c, a, b)) = self.split_if(e) {
            let then = vec![Stmt { span: e.span, kind: StmtKind::Constraint(a) }];
            let els = vec![Stmt { span: e.span, kind: StmtKind::Constraint(b) }];
            return self.split_stmt(&c, then, els, e.span);
        }
        // f(args) == e  /  e == f(args)
        if let ExprKind::Bin(BinOp::Eq, l, r) = &e.kind {
            if let ExprKind::Call(f, args) = &l.kind {
                if self.callee(f).is_some() {
                    return self.call_eq(f, args, r, e.span);
                }
            }
            if let ExprKind::Call(f, args) = &r.kind {
                if self.callee(f).is_some() {
                    return self.call_eq(f, args, l, e.span);
                }
            }
        }
        // call in prop position with a bool output: f(args) == true
        if let ExprKind::Call(f, args) = &e.kind {
            if let Some(info) = self.callee(f) {
                if info.outputs().len() == 1 && info.outputs()[0] == RType::Bool {
                    let t = Expr::new(e.span, ExprKind::Bool(true));
                    return self.call_eq(f, args, &t, e.span);
                }
            }
        }
        // `b == (P)` / `b != (P)` for a boolean `b`: `(b = true ↔ P)`, with `P`
        // read as a constraint (short-circuit scoping, local lifting)
        if let ExprKind::Bin(op @ (BinOp::Eq | BinOp::Ne), l, r) = &e.kind {
            if is_proplike(l) || is_proplike(r) {
                let (bside, pside) = if is_proplike(r) { (l, r) } else { (r, l) };
                let bp = self.constraint_inner(bside)?;
                self.flush_guards();
                let pp = self.constraint_inner(pside)?;
                self.flush_guards();
                let iff = format!("({bp} ↔ {pp})");
                return Ok(if *op == BinOp::Eq { iff } else { format!("¬{iff}") });
            }
        }
        // `!P`: `P` is read as a constraint, so that the scoping of `&&`, `||`
        // and `=>` inside it, and the local lifting of its relational calls,
        // are those of `P` itself; negation does not change what is defined
        if let ExprKind::Not(x) = &e.kind {
            let xp = self.constraint_inner(x)?;
            self.flush_guards();
            return Ok(format!("¬({xp})"));
        }
        // `A && B`, `A || B` and `A => B` (parsed as `!A || B`): the right operand
        // is read under the left's truth (resp. falsity), as Rust's short-circuit
        // operators are — its partial operations need only be defined there, and
        // relational calls inside it are lifted inside it, not outside the whole
        // disjunction.
        if let ExprKind::Bin(op @ (BinOp::And | BinOp::Or), l, r) = &e.kind {
            let (lp, guard, imp) = match (*op, &l.kind) {
                (BinOp::Or, ExprKind::Not(a)) => {
                    let ap = self.constraint_inner(a)?;
                    (ap.clone(), ap, true)
                }
                (BinOp::And, _) => {
                    let lp = self.constraint_inner(l)?;
                    (lp.clone(), lp, false)
                }
                _ => {
                    let lp = self.constraint_inner(l)?;
                    (lp.clone(), format!("¬({lp})"), false)
                }
            };
            self.flush_guards();
            self.cx.push(Cx::Guard(guard.clone()));
            let rp = self.constraint_inner(r)?;
            self.flush_guards();
            self.cx.pop();
            let rec = self.calls_me(&rp) && !self.calls_me(&lp);
            return Ok(if imp {
                format!("({lp} → {rp})")
            } else if *op == BinOp::And {
                if rec { format!("({lp} ∧ ({lp} → {rp}))") } else { format!("({lp} ∧ {rp})") }
            } else if rec {
                format!("({lp} ∨ (¬({lp}) → {rp}))")
            } else {
                format!("({lp} ∨ {rp})")
            });
        }
        // nested calls: implicit existentials
        let mut lifted = Vec::new();
        let e2 = self.lift_calls(e, &mut lifted)?;
        if lifted.is_empty() {
            return self.prop(e);
        }
        let binds = lifted_binds(&lifted);
        self.wrap_lifted(lifted, &binds, e.span, |l| l.prop(&e2))
    }

    /// `∃ v₁ …, f₁_spec … v₁ ∧ …` around a body that uses the lifted values.
    /// Well-formedness items found in the body (and in the calls' own
    /// arguments) are stated for the witnesses: under `∀ v, f_spec … v →`.
    fn wrap_lifted(&mut self, lifted: Vec<(String, String, Vec<Expr>, RType)>, binds: &[(String, SType)], span: proc_macro2::Span, body: impl FnOnce(&mut Self) -> Result<String>) -> Result<String> {
        let mut calls = Vec::new();
        let mut pushed = 0;
        for (v, f, args, t) in &lifted {
            let call = self.with_vars(binds, |l| l.spec_app(f, args, v, span))?;
            self.flush_guards();
            self.cx.push(Cx::Forall(v.clone(), view_type(t, self.names)));
            self.cx.push(Cx::Guard(call.clone()));
            pushed += 2;
            calls.push(call);
        }
        let mut s = self.with_vars(binds, body)?;
        self.flush_guards();
        for _ in 0..pushed {
            self.cx.pop();
        }
        for ((v, _, _, t), call) in lifted.iter().zip(calls).rev() {
            s = if self.calls_me(&s) && !self.calls_me(&call) { format!("(∃ {v} : {}, {call} ∧ ({call} → {s}))", view_type(t, self.names)) } else { format!("(∃ {v} : {}, {call} ∧ {s})", view_type(t, self.names)) };
        }
        Ok(s)
    }

    /// `f(args) == out` as `f_spec args out`, with calls nested in the
    /// arguments or in `out` lifted to existentials around it.
    fn call_eq(&mut self, f: &str, args: &[Expr], out: &Expr, span: proc_macro2::Span) -> Result<String> {
        let info = self.callee(f).unwrap();
        if info.outputs().len() != 1 {
            return Err(Error::new(span, format!("`{f}` has {} outputs; equating it with a tuple is not supported yet", info.outputs().len())));
        }
        let mut lifted = Vec::new();
        let mut nargs = Vec::new();
        for a in args {
            nargs.push(self.lift_calls(a, &mut lifted)?);
        }
        let nout = self.lift_calls(out, &mut lifted)?;
        let binds = lifted_binds(&lifted);
        let f = f.to_string();
        let out_ty = info.outputs()[0].clone();
        self.wrap_lifted(lifted, &binds, span, |l| {
            let (o, oty) = l.term(&nout)?;
            if oty == SType::Of(out_ty.clone()) || matches!((&oty, &out_ty), (SType::Int, RType::MathInt)) {
                return l.spec_app(&f, &nargs, &o, span);
            }
            // the output is of another type (a machine integer against a
            // mathematical one, say): name it and compare through the views
            let v = l.avoid(format!("v_out{}", l.fresh));
            l.fresh += 1;
            let eq = Expr::new(span, ExprKind::Bin(BinOp::Eq, Box::new(Expr::new(span, ExprKind::Var(v.clone()))), Box::new(nout.clone())));
            let (call, cmp) = l.with_vars(&[(v.clone(), SType::Of(out_ty.clone()))], |l| Ok((l.spec_app(&f, &nargs, &v, span)?, l.prop(&eq)?)))?;
            Ok(format!("(∃ {v} : {}, {call} ∧ {cmp})", view_type(&out_ty, l.names)))
        })
    }

    /// `f_spec a1 … an out`, plus the call-site obligation `f_pre a1 … an`;
    /// for an ambient function, `f a1 … an = ok out` over its Aeneas model.
    pub(crate) fn spec_app(&mut self, f: &str, args: &[Expr], out: &str, span: proc_macro2::Span) -> Result<String> {
        let info = self.callee(f).unwrap();
        let inputs = info.inputs();
        if args.len() != inputs.len() {
            return Err(Error::new(span, format!("`{f}` takes {} arguments, {} given", inputs.len(), args.len())));
        }
        let mut as_ = Vec::new();
        for (a, t) in args.iter().zip(&inputs) {
            as_.push(self.term_as(a, t)?);
        }
        match info {
            Callee::Decl(info) => {
                if info.has_pre || info.inputs.iter().any(|t| has_implicit_facts(t, self.types)) {
                    self.guards.push(format!("{f}_pre {}", as_.join(" ")));
                }
                // a recursive call of a declaration with choices passes its
                // choice functions on (`_spec`, their closure, is defined
                // only after `_body`)
                if self.recursive.as_deref() == Some(f) && self.has_choices {
                    return Ok(format!("{f}_body {} {SELF_CHOICES} {}", as_.join(" "), out));
                }
                // a call of a weakly specified callee: its choices are lifted
                // into this declaration, one fresh choice per choice of the
                // callee, a function of this declaration's inputs and of the
                // `for` variables at the call site
                if info.weakly_specified {
                    if info.choices.is_empty() {
                        return Err(Error::new(span, format!("`{f}` is weakly specified and mutually recursive with this declaration; that is not supported")));
                    }
                    let mut lifted = Vec::new();
                    for (cn, ct) in info.choices.clone() {
                        let (_, term) = self.new_choice(&format!("{f}_{}", cn.trim_start_matches('«').trim_end_matches('»')), &ct);
                        lifted.push(term);
                    }
                    return Ok(format!("{f}_body {} {} {}", as_.join(" "), lifted.join(" "), out));
                }
                Ok(format!("{f}_spec {} {}", as_.join(" "), out))
            }
            Callee::Ambient(_) => {
                if !self.ambient_calls.iter().any(|x| x == f) {
                    self.ambient_calls.push(f.to_string());
                }
                let args_s = if as_.is_empty() { String::new() } else { format!(" {}", as_.join(" ")) };
                Ok(format!("{}{args_s} = ok {out}", self.ambient_lean(f)))
            }
        }
    }

    fn lift_calls(&mut self, e: &Expr, out: &mut Vec<(String, String, Vec<Expr>, RType)>) -> Result<Expr> {
        let span = e.span;
        let mk = |k: ExprKind| Expr::new(span, k);
        macro_rules! rec {
            ($x:expr) => {
                Box::new(self.lift_calls($x, out)?)
            };
        }
        Ok(match &e.kind {
            ExprKind::Call(f, args) if self.callee(f).is_some() => {
                let info = self.callee(f).unwrap();
                if info.outputs().len() != 1 {
                    return Err(Error::new(span, format!("`{f}` must have exactly one output to be used as a value")));
                }
                let mut nargs = Vec::new();
                for a in args {
                    nargs.push(self.lift_calls(a, out)?);
                }
                let v = self.avoid(format!("v_call{}", self.fresh));
                self.fresh += 1;
                self.seen_types.push(info.outputs()[0].clone());
                out.push((v.clone(), f.clone(), nargs, info.outputs()[0].clone()));
                mk(ExprKind::Var(v))
            }
            ExprKind::Call(f, _) => return Err(Error::new(span, self.undeclared(f))),
            ExprKind::Bin(op, l, r) => mk(ExprKind::Bin(*op, rec!(l), rec!(r))),
            ExprKind::Not(x) => mk(ExprKind::Not(rec!(x))),
            ExprKind::Neg(x) => mk(ExprKind::Neg(rec!(x))),
            ExprKind::Cast(x, t) => mk(ExprKind::Cast(rec!(x), t.clone())),
            ExprKind::Field(x, f) => mk(ExprKind::Field(rec!(x), f.clone())),
            ExprKind::Ctor(c, args) => {
                let mut v = Vec::new();
                for a in args {
                    v.push(self.lift_calls(a, out)?);
                }
                mk(ExprKind::Ctor(c.clone(), v))
            }
            ExprKind::Variant { enum_name, variant, fields } => {
                let mut v = Vec::new();
                for (n, a) in fields {
                    v.push((n.clone(), self.lift_calls(a, out)?));
                }
                mk(ExprKind::Variant { enum_name: enum_name.clone(), variant: variant.clone(), fields: v })
            }
            ExprKind::In(a, b) => mk(ExprKind::In(rec!(a), rec!(b))),
            ExprKind::InRange(a, f) => mk(ExprKind::InRange(rec!(a), f.clone())),
            ExprKind::InDomain(a, f) => mk(ExprKind::InDomain(rec!(a), f.clone())),
            ExprKind::Index(a, b) => mk(ExprKind::Index(rec!(a), rec!(b))),
            ExprKind::Slice(a, b, c) => mk(ExprKind::Slice(rec!(a), rec!(b), rec!(c))),
            ExprKind::IfVal(a, b, c) => mk(ExprKind::IfVal(rec!(a), rec!(b), rec!(c))),
            ExprKind::Method(m) => {
                // calls inside vocabulary methods are lifted too, except under binders
                let m2 = match &**m {
                    Method::Len(x) => Method::Len(*rec!(x)),
                    Method::IsEmpty(x) => Method::IsEmpty(*rec!(x)),
                    Method::Contains(a, b) => Method::Contains(*rec!(a), *rec!(b)),
                    Method::Sum(x) => Method::Sum(*rec!(x)),
                    Method::First(x) => Method::First(*rec!(x)),
                    Method::Last(x) => Method::Last(*rec!(x)),
                    Method::Abs(x) => Method::Abs(*rec!(x)),
                    Method::Min(a, b) => Method::Min(*rec!(a), *rec!(b)),
                    Method::Max(a, b) => Method::Max(*rec!(a), *rec!(b)),
                    Method::Pow(a, b) => Method::Pow(*rec!(a), *rec!(b)),
                    Method::IsSome(x) => Method::IsSome(*rec!(x)),
                    Method::IsNone(x) => Method::IsNone(*rec!(x)),
                    Method::Unwrap(x) => Method::Unwrap(*rec!(x)),
                    Method::AsBytes(x) => Method::AsBytes(*rec!(x)),
                    Method::MapGet(a, b) => Method::MapGet(*rec!(a), *rec!(b)),
                    Method::ContainsKey(a, b) => Method::ContainsKey(*rec!(a), *rec!(b)),
                    Method::BitCount(k, x) => Method::BitCount(*k, *rec!(x)),
                    Method::Rotate(l, a, b) => Method::Rotate(*l, *rec!(a), *rec!(b)),
                    Method::Wrapping(op, a, b) => Method::Wrapping(*op, *rec!(a), *rec!(b)),
                    other => other.clone(),
                };
                mk(ExprKind::Method(Box::new(m2)))
            }
            _ => e.clone(),
        })
    }

    // ------------------------------------------------------------ propositions

    pub(crate) fn prop(&mut self, e: &Expr) -> Result<String> {
        let span = e.span;
        let err = |m: String| Err(Error::new(span, m));
        Ok(match &e.kind {
            ExprKind::Bool(true) => "True".into(),
            ExprKind::Bool(false) => "False".into(),
            ExprKind::Not(x) => format!("¬({})", self.prop(x)?),
            ExprKind::Bin(BinOp::And, l, r) => format!("({} ∧ {})", self.prop(l)?, self.prop(r)?),
            ExprKind::Bin(BinOp::Or, l, r) => format!("({} ∨ {})", self.prop(l)?, self.prop(r)?),
            ExprKind::Bin(op, l, r) if matches!(op, BinOp::Eq | BinOp::Ne) && (is_proplike(l) || is_proplike(r)) => {
                // `b == (proposition)` for a boolean b: `(b = true ↔ P)`
                let (bside, pside) = if is_proplike(r) { (l, r) } else { (r, l) };
                let bp = self.prop(bside)?;
                let pp = self.prop(pside)?;
                let iff = format!("({bp} ↔ {pp})");
                if *op == BinOp::Eq { iff } else { format!("¬{iff}") }
            }
            ExprKind::Bin(op, l, r) if op.is_cmp() => {
                let (lt, lty) = self.term(l)?;
                let (rt, rty) = self.term(r)?;
                let numeric = |t: &SType| matches!(t, SType::Int) || matches!(t, SType::Of(RType::Int { .. })) || matches!(t, SType::Of(RType::MathInt));
                let is_char = |t: &SType| matches!(t, SType::Of(RType::Char));
                let (ls, rs) = if matches!(op, BinOp::Eq | BinOp::Ne) && lty == rty && !matches!(lty, SType::Int) {
                    (lt, rt)
                } else if numeric(&lty) && numeric(&rty) {
                    (self.as_num(lt, &lty), self.as_num(rt, &rty))
                } else if is_char(&lty) && is_char(&rty) {
                    (format!("({lt}.toNat : ℤ)"), format!("({rt}.toNat : ℤ)"))
                } else if matches!(op, BinOp::Eq | BinOp::Ne) {
                    (lt, rt)
                } else {
                    return err("ordering comparison on non-numeric values".into());
                };
                let sym = match op {
                    BinOp::Eq => "=",
                    BinOp::Ne => "≠",
                    BinOp::Lt => "<",
                    BinOp::Le => "≤",
                    BinOp::Gt => ">",
                    BinOp::Ge => "≥",
                    _ => unreachable!(),
                };
                format!("{ls} {sym} {rs}")
            }
            ExprKind::In(x, s) => {
                let (st, sty) = self.term(s)?;
                // the element is written at the sequence's element type: a
                // literal (or a constant) `47` in a `&[u8]` is `47#u8`
                let elem = match &sty {
                    SType::Of(RType::Seq(elem, _)) => elem.as_ref().clone(),
                    _ => return err("`in` needs a sequence on the right".into()),
                };
                format!("{} ∈ {}", self.member(x, &elem)?, self.member_seq(x, &elem, &st)?)
            }
            ExprKind::InRange(x, f) => {
                let info = match self.decls.get(f) {
                    Some(i) => i.clone(),
                    None => return err(format!("`range({f})`: unknown function")),
                };
                if info.outputs.len() != 1 {
                    return err(format!("`range({f})`: `{f}` must have exactly one output"));
                }
                let (xt, _) = self.term(x)?;
                let as_: Vec<String> = (0..info.inputs.len()).map(|i| self.avoid(format!("a{i}"))).collect();
                let bs: Vec<String> = info.inputs.iter().zip(&as_).map(|(t, a)| format!("({a} : {})", view_type(t, self.names))).collect();
                format!("(∃ {}, {f}_spec {} {xt})", bs.join(" "), as_.join(" "))
            }
            ExprKind::InDomain(x, f) => {
                let info = match self.decls.get(f) {
                    Some(i) => i.clone(),
                    None => return err(format!("`domain({f})`: unknown function")),
                };
                if info.inputs.len() != 1 {
                    return err(format!("`domain({f})`: only unary functions are supported"));
                }
                let xt = self.term_as(x, &info.inputs[0])?;
                let pre = if info.has_pre || info.inputs.iter().any(|t| has_implicit_facts(t, self.types)) { format!("{f}_pre {xt}") } else { "True".into() };
                if info.total {
                    pre
                } else {
                    let on: Vec<String> = (0..info.outputs.len()).map(|i| self.avoid(format!("o{i}"))).collect();
                    let os: Vec<String> = info.outputs.iter().zip(&on).map(|(t, o)| format!("({o} : {})", view_type(t, self.names))).collect();
                    format!("({pre} ∧ ∃ {}, {f}_spec {xt} {})", os.join(" "), on.join(" "))
                }
            }
            ExprKind::Method(m) => match &**m {
                Method::IsEmpty(s) => format!("({}.length : ℤ) = 0", self.listlike(s)?),
                Method::ContainsKey(m, k) => {
                    let (mt, kty) = self.map(m)?;
                    let kt = self.term_as(k, &kty)?;
                    format!("(Djinn.Vocab.mapGet {mt} {kt}).isSome = true")
                }
                Method::Contains(s, x) => {
                    let (st, et) = self.seq(s)?;
                    // the element at the sequence's element type: a literal
                    // or constant `47` in a `&[u8]` is `47#u8`
                    let (xt, sq) = match &et {
                        SType::Of(rt) => (self.member(x, &rt.clone())?, self.member_seq(x, &rt.clone(), &st)?),
                        _ => (self.term(x)?.0, st),
                    };
                    format!("{xt} ∈ {sq}")
                }
                Method::All { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    let (v, p) = self.under_elem(var, et, &st, pred)?;
                    format!("(∀ {v}, {v} ∈ {st} → {p})")
                }
                Method::Any { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    let (v, p) = self.under_elem(var, et, &st, pred)?;
                    format!("(∃ {v}, {v} ∈ {st} ∧ {p})")
                }
                Method::Windows2All { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    // `w[0]` and `w[1]` are two fresh variables, read like the
                    // element of `all` (relations lifted inside, partial
                    // operations owed for every adjacent pair)
                    let a = self.avoid(format!("{var}0"));
                    let b = self.avoid(format!("{var}1"));
                    let pred2 = subst_window(pred, var, &a, &b);
                    let tl = stype_lean(&et, self.names);
                    let binds = [(a.clone(), lean_ident(&a), et.clone()), (b.clone(), lean_ident(&b), et)];
                    let p = self.under_binders(&binds, &tl, &format!("({}, {}) ∈ List.zip {st} (List.tail {st})", lean_ident(&a), lean_ident(&b)), &pred2)?;
                    format!("List.Chain' (fun {} {} => {p}) {st}", lean_ident(&a), lean_ident(&b))
                }
                Method::IsSome(o) => format!("{}.isSome = true", self.term(o)?.0),
                Method::IsNone(o) => format!("{}.isNone = true", self.term(o)?.0),
                _ => {
                    let (t, ty) = self.term(e)?;
                    return self.bool_prop(t, &ty, span);
                }
            },
            ExprKind::Call(f, _) if self.decls.contains_key(f) => {
                return err(format!("a call to `{f}` in a nested position needs the statement-level form; this is a bug in lifting"));
            }
            _ => {
                let (t, ty) = self.term(e)?;
                return self.bool_prop(t, &ty, span);
            }
        })
    }

    /// The two branches of a split value-`if` with the condition `c`. The
    /// condition's own calls are lifted around the split, as around an `if`
    /// that is not split — `∃ v, p_spec x v ∧ ((v → …) ∧ (¬v → …))`, never the
    /// statement reading `p_spec x true → …`.
    fn split_stmt(&mut self, c: &Expr, then: Vec<Stmt>, els: Vec<Stmt>, span: proc_macro2::Span) -> Result<String> {
        let mut lifted = Vec::new();
        let c2 = self.lift_calls(c, &mut lifted)?;
        let s = Stmt { span, kind: StmtKind::If { cond: c2, then, els: Some(els) } };
        if lifted.is_empty() {
            return self.stmt(&s);
        }
        let binds = lifted_binds(&lifted);
        self.wrap_lifted(lifted, &binds, span, |l| l.stmt(&s))
    }

    /// The predicate of `s.iter().all(|x| pred)` and kin, for an element
    /// `x` of `s` (`st`): read as a constraint, so that relations it calls are
    /// lifted inside it, and its well-formedness items are stated for every
    /// element.
    /// Returns the element's Lean name and the predicate.
    fn under_elem(&mut self, var: &str, et: SType, st: &str, pred: &Expr) -> Result<(String, String)> {
        let v = lean_ident(var);
        let tl = stype_lean(&et, self.names);
        let p = self.under_binders(&[(var.to_string(), v.clone(), et)], &tl, &format!("{v} ∈ {st}"), pred)?;
        Ok((v, p))
    }

    /// `pred` read as a constraint for the variables `binds` (source name,
    /// Lean name, type; Lean type `tl`) of which `member` holds: its
    /// well-formedness items are stated `∀ binds, member → …`.
    fn under_binders(&mut self, binds: &[(String, String, SType)], tl: &str, member: &str, pred: &Expr) -> Result<String> {
        self.flush_guards();
        for (_, v, _) in binds {
            self.cx.push(Cx::Forall(v.clone(), tl.to_string()));
            self.binders.push((v.clone(), tl.to_string()));
        }
        self.cx.push(Cx::Guard(member.to_string()));
        let r = self.with_env(binds, |l| {
            let p = l.constraint_inner(pred)?;
            l.flush_guards();
            Ok(p)
        });
        self.cx.pop();
        for _ in binds {
            self.binders.pop();
            self.cx.pop();
        }
        r
    }

    /// The first value-`if` of `e` (outside closures) whose branches call
    /// relations: its condition and `e` with the `if` replaced by each branch.
    fn split_if(&self, e: &Expr) -> Option<(Expr, Expr, Expr)> {
        // not through `&&`, `||`, `!` or `b == (P)`: `constraint_inner` reads
        // those itself and splits each operand under its guard (a split here
        // would state the condition's guards outside that context)
        match &e.kind {
            ExprKind::Bin(BinOp::And | BinOp::Or, _, _) | ExprKind::Not(_) => return None,
            ExprKind::Bin(BinOp::Eq | BinOp::Ne, l, r) if is_proplike(l) || is_proplike(r) => return None,
            _ => {}
        }
        let calls = |x: &Expr| x.any(&|y| matches!(&y.kind, ExprKind::Call(f, _) if self.callee(f).is_some()));
        if let ExprKind::IfVal(c, a, b) = &e.kind {
            if calls(a) || calls(b) {
                return Some(((**c).clone(), (**a).clone(), (**b).clone()));
            }
        }
        let mut found: Option<(usize, (Expr, Expr, Expr))> = None;
        let mut i = 0;
        e.map_children(&mut |ch| {
            if found.is_none() {
                if let Some(s) = self.split_if(ch) {
                    found = Some((i, s));
                }
            }
            i += 1;
            ch.clone()
        });
        let (k, (c, a, b)) = found?;
        let with = |r: &Expr| {
            let mut j = 0;
            e.map_children(&mut |ch| {
                let x = if j == k { r.clone() } else { ch.clone() };
                j += 1;
                x
            })
        };
        Some((c, with(&a), with(&b)))
    }

    /// Is `x` a mathematical integer (not a literal) tested against a sequence of machine
    /// integers? Then membership is stated through the elements' values.
    fn by_value(&mut self, x: &Expr, elem: &RType) -> Result<bool> {
        if !matches!(elem, RType::Int { .. }) {
            return Ok(false);
        }
        // a probe: its guards are pushed again when `x` is lowered for real
        let saved = self.guards.len();
        let saved_wf = self.wf.len();
        let r = self.term(x);
        self.guards.truncate(saved);
        self.wf.truncate(saved_wf);
        let (xt, xty) = r?;
        let literal = xt.chars().all(|c| c.is_ascii_digit());
        Ok(matches!(xty, SType::Int | SType::Of(RType::MathInt)) && (!literal || !fits(&xt, elem)))
    }

    /// The element side of `x in s` / `s.contains(&x)`.
    fn member(&mut self, x: &Expr, elem: &RType) -> Result<String> {
        if self.by_value(x, elem)? {
            Ok(self.term(x)?.0)
        } else {
            self.term_as(x, elem)
        }
    }

    /// The sequence side: the elements' values when `x` is a mathematical integer.
    fn member_seq(&mut self, x: &Expr, elem: &RType, st: &str) -> Result<String> {
        if self.by_value(x, elem)? {
            let y = self.as_num("y".into(), &SType::Of(elem.clone()));
            Ok(format!("({st}.map (fun y => {y}))"))
        } else {
            Ok(st.to_string())
        }
    }

    fn bool_prop(&self, t: String, ty: &SType, span: proc_macro2::Span) -> Result<String> {
        if *ty == SType::Of(RType::Bool) {
            Ok(format!("{t} = true"))
        } else {
            Err(Error::new(span, format!("`{t}` is not a boolean constraint")))
        }
    }

    // ------------------------------------------------------------------ terms

    pub(crate) fn as_num(&self, t: String, ty: &SType) -> String {
        match ty {
            SType::Int | SType::Of(RType::MathInt) => t,
            SType::Of(RType::Int { signed: true, .. }) => dotval(&t),
            SType::Of(RType::Int { signed: false, .. }) => format!("({} : ℤ)", dotval(&t)),
            _ => t,
        }
    }

    pub(crate) fn num(&mut self, e: &Expr) -> Result<String> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt) => Ok(self.as_num(t, &ty)),
            _ => Err(Error::new(e.span, format!("`{t}` is not a number"))),
        }
    }

    /// A numeric term, as a natural number (`true`) when it naturally is one:
    /// an unsigned machine value (its `.val`), a literal, or a bit operation
    /// on such. Otherwise (`false`) an integer term. Bit operations lower to
    /// Lean's `Nat` operations on the values, the forms Aeneas's `.val`
    /// lemmas state for the machine operations: `&&&`, `|||`, `^^^`, and
    /// `<<<`, `>>>` on a natural number. A shift of any other integer is
    /// `a * 2^n` or the floor division `a / 2^n` (an arithmetic shift).
    fn natish(&mut self, e: &Expr) -> Result<(String, bool)> {
        match &e.kind {
            ExprKind::Bin(op @ (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor), l, r) => {
                let a = self.nat_operand(l)?;
                let b = self.nat_operand(r)?;
                let sym = match op {
                    BinOp::BitAnd => "&&&",
                    BinOp::BitOr => "|||",
                    _ => "^^^",
                };
                Ok((format!("({a} {sym} {b})"), true))
            }
            ExprKind::Bin(op @ (BinOp::Shl | BinOp::Shr), l, r) => {
                let (a, nat) = self.natish(l)?;
                let k = self.nat_operand(r)?;
                let shl = *op == BinOp::Shl;
                Ok(if nat {
                    (format!("({a} {} {k})", if shl { "<<<" } else { ">>>" }), true)
                } else {
                    (format!("({a} {} 2 ^ {k})", if shl { "*" } else { "/" }), false)
                })
            }
            ExprKind::Method(m) if matches!(&**m, Method::BitCount(..) | Method::Rotate(..)) => self.bits_method(m),
            _ => {
                let (t, ty) = self.term(e)?;
                match &ty {
                    SType::Of(RType::Int { signed: false, .. }) => Ok((dotval(&t), true)),
                    SType::Int if t.chars().all(|c| c.is_ascii_digit()) => Ok((t, true)),
                    SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt) => Ok((self.as_num(t, &ty), false)),
                    _ => Err(Error::new(e.span, format!("`{t}` is not a number"))),
                }
            }
        }
    }

    /// The receiver of a method whose meaning depends on the width: a machine
    /// integer, or any integer cast to one (`e as u32`). Its value as an `ℤ`
    /// term, its signedness and width, and its bits as a `BitVec` term (an
    /// Aeneas scalar's own `.bv`; for a cast, the value's low bits).
    fn machine_int(&mut self, e: &Expr, what: &str) -> Result<(String, (bool, u32), String)> {
        if let ExprKind::Cast(inner, RType::Int { signed, bits }) = &e.kind {
            let v = self.num(inner)?;
            let w = width_lean(*signed, *bits);
            return Ok((v.clone(), (*signed, *bits), format!("(BitVec.ofInt {w} {v})")));
        }
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Int { signed, bits }) => {
                let bv = format!("{}.bv", paren(&t));
                Ok((self.as_num(t, &ty), (signed, bits), bv))
            }
            _ => Err(Error::new(e.span, format!("{what} need a machine integer: a parameter, field or element of an integer type, or a cast (`e as u32`); `{t}` is a mathematical integer, which has no width"))),
        }
    }

    /// A bit count, or a rotation: the term, and whether it is a natural number
    /// (a count, or an unsigned value's rotation) or an integer (a signed value's
    /// rotation, read back in two's complement). The receiver is lowered once,
    /// and its type — not its syntax — decides the signedness.
    fn bits_method(&mut self, m: &Method) -> Result<(String, bool)> {
        match m {
            Method::BitCount(k, x) => {
                let (_, _, bv) = self.machine_int(x, "the bit counts (`.count_ones()`, …)")?;
                Ok((k.lean(&bv), true))
            }
            Method::Rotate(left, x, n) => {
                let (_, (signed, _), bv) = self.machine_int(x, "`.rotate_left(n)` / `.rotate_right(n)`")?;
                let k = self.nat_operand(n)?;
                let dir = if *left { "rotateLeft" } else { "rotateRight" };
                Ok(if signed { (format!("({bv}.{dir} {k}).toInt"), false) } else { (format!("({bv}.{dir} {k}).toNat"), true) })
            }
            _ => unreachable!("only bit counts and rotations"),
        }
    }

    /// An operand of `&`, `|`, `^` or a shift amount, as a natural number:
    /// anything not naturally one must be non-negative (a well-formedness
    /// guard) and is taken `.toNat`.
    fn nat_operand(&mut self, e: &Expr) -> Result<String> {
        let (t, nat) = self.natish(e)?;
        if nat {
            return Ok(t);
        }
        self.guards.push(format!("0 ≤ {t}"));
        Ok(to_nat(&t))
    }

    pub(crate) fn seq(&mut self, e: &Expr) -> Result<(String, SType)> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Seq(el, _)) => Ok((t, SType::Of(*el))),
            SType::Of(RType::Map(..)) => Err(Error::new(e.span, format!("`{t}` is a map: use `.get(&k)`, `.contains_key(&k)`, `.len()`, `.is_empty()`"))),
            _ => Err(Error::new(e.span, format!("`{t}` is not a sequence"))),
        }
    }

    /// A sequence or a map, as the list it is viewed as.
    fn listlike(&mut self, e: &Expr) -> Result<String> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Seq(..)) | SType::Of(RType::Map(..)) => Ok(t),
            _ => Err(Error::new(e.span, format!("`{t}` is not a sequence or a map"))),
        }
    }

    /// A map: its list of entries and its key type.
    fn map(&mut self, e: &Expr) -> Result<(String, RType)> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Map(k, _)) => Ok((t, *k)),
            _ => Err(Error::new(e.span, format!("`{t}` is not a map (`.get(&k)` and `.contains_key(&k)` apply to `HashMap`s; a sequence is indexed with `s[i]`)"))),
        }
    }

    fn env_type_of(&mut self, e: &Expr) -> Result<RType> {
        match self.term(e)?.1 {
            SType::Of(t) => Ok(t),
            SType::Int => Ok(RType::MathInt),
        }
    }

    /// A term expected to have Rust type `t` (used for call arguments).
    pub(crate) fn term_as(&mut self, e: &Expr, t: &RType) -> Result<String> {
        let (s, ty) = self.term(e)?;
        match (&ty, t) {
            (SType::Of(RType::Seq(..)), RType::Seq(..)) => Ok(s),
            (SType::Int, RType::MathInt) | (SType::Of(RType::MathInt), RType::MathInt) => Ok(s),
            (SType::Of(RType::Int { .. }), RType::MathInt) => Ok(self.as_num(s, &ty)),
            // a literal is written as a scalar of the expected type; any other
            // mathematical integer has no canonical machine value
            (SType::Int, RType::Int { .. }) if s.chars().all(|c| c.is_ascii_digit()) && !fits(&s, t) => {
                Err(Error::new(e.span, format!("`{s}` does not fit in `{}`", rust_type(t))))
            }
            (SType::Int, RType::Int { signed, bits }) if s.chars().all(|c| c.is_ascii_digit()) => {
                Ok(format!("{s}#{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() }))
            }
            (SType::Int, RType::Int { .. }) => Err(Error::new(e.span, format!("`{s}`: a machine integer is expected, got a mathematical integer (declare the parameter as `int` in a `rel`)"))),
            _ => Ok(s),
        }
    }

    /// A constant of the specification file, as a literal term.
    fn constant(&mut self, v: &str, span: proc_macro2::Span) -> Result<(String, SType)> {
        let c = self.types.consts.get(v).cloned().ok_or_else(|| {
            Error::new(span, format!("unknown constant `{v}`: constants used in specifications must be literal `const` items of the specification file: integers, booleans, chars, strings, or arrays of integer literals (`&[u32]`, `[i16; N]`)"))
        })?;
        if let Some(elems) = &c.table {
            // defined once in `Spec.lean`, under the constant's own name
            if let RType::Seq(e, _) = &c.ty {
                if !self.tables.iter().any(|(n, _, _)| n == v) {
                    self.tables.push((v.to_string(), (**e).clone(), elems.clone()));
                }
            }
            return Ok((v.to_string(), SType::Of(c.ty)));
        }
        self.term(&c.value)
    }

    pub(crate) fn term(&mut self, e: &Expr) -> Result<(String, SType)> {
        let span = e.span;
        let err = |m: String| Err(Error::new(span, m));
        Ok(match &e.kind {
            ExprKind::Int(s) => (s.clone(), SType::Int),
            ExprKind::Bool(b) => (b.to_string(), SType::Of(RType::Bool)),
            ExprKind::Char(c) => (char_lit(*c), SType::Of(RType::Char)),
            ExprKind::Str(b) => (bytes_lit(b), SType::Of(RType::Seq(Box::new(RType::Int { signed: false, bits: 8 }), SeqKind::Str))),
            ExprKind::Var(v) => {
                let name = if self.pre_scope && self.muts.contains(v) { format!("{v}_old") } else { v.clone() };
                match self.env.get(&name) {
                    Some((t, ty)) => (t.clone(), ty.clone()),
                    None => {
                        if v.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                            return self.constant(v, span);
                        }
                        return err(format!("unknown variable `{v}`"));
                    }
                }
            }
            ExprKind::Old(v) => {
                let name = format!("{v}_old");
                match self.env.get(&name) {
                    Some((t, ty)) => (t.clone(), ty.clone()),
                    None => return err(format!("`old({v})`: not a `&mut` parameter")),
                }
            }
            ExprKind::Neg(x) => (format!("(-{})", self.num(x)?), SType::Int),
            ExprKind::Cast(x, to) => {
                let (t, ty) = self.term(x)?;
                match (&ty, to) {
                    (SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt), RType::Int { .. }) => (self.as_num(t, &ty), SType::Int),
                    (SType::Of(RType::Char), RType::Int { .. }) => (format!("({t}.toNat : ℤ)"), SType::Int),
                    (SType::Of(RType::Int { signed: false, bits: 8 }), RType::Char) => (format!("(Char.ofNat {t}.val)"), SType::Of(RType::Char)),
                    (SType::Int, RType::Char) => (format!("(Char.ofNat ({t}).toNat)"), SType::Of(RType::Char)),
                    _ => return err("unsupported cast: integers cast to integers (no overflow in the specification), `char as u32`, `u8 as char`".into()),
                }
            }
            ExprKind::Bin(op, _, _) if op.is_bits() => {
                let (t, nat) = self.natish(e)?;
                (if nat { format!("((({t}) : ℕ) : ℤ)") } else { t }, SType::Int)
            }
            ExprKind::Bin(op, l, r) if op.is_arith() => {
                let a = self.num(l)?;
                let b = self.num(r)?;
                let sym = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => {
                        self.guards.push(format!("{b} ≠ 0"));
                        "/"
                    }
                    BinOp::Rem => {
                        self.guards.push(format!("{b} ≠ 0"));
                        "%"
                    }
                    _ => unreachable!(),
                };
                (format!("({a} {sym} {b})"), SType::Int)
            }
            ExprKind::Ctor(c, args) => {
                let mut ts = Vec::new();
                let mut tys = Vec::new();
                for a in args {
                    let (t, ty) = self.term(a)?;
                    ts.push(if is_atom(&t) { t } else { format!("({t})") });
                    tys.push(ty);
                }
                let inner = |tys: &[SType]| -> RType {
                    match tys.first() {
                        Some(SType::Of(t)) => t.clone(),
                        _ => RType::Named("_".into()),
                    }
                };
                match c.as_str() {
                    "None" => ("none".into(), SType::Of(RType::Option(Box::new(RType::Named("_".into()))))),
                    "Some" => (format!("(some {})", ts.join(" ")), SType::Of(RType::Option(Box::new(inner(&tys))))),
                    "Ok" => (format!("(.Ok {})", ts.join(" ")), SType::Of(RType::Result(Box::new(inner(&tys)), Box::new(RType::Named("_".into()))))),
                    "Err" => (format!("(.Err {})", ts.join(" ")), SType::Of(RType::Result(Box::new(RType::Named("_".into())), Box::new(inner(&tys))))),
                    _ => unreachable!(),
                }
            }
            ExprKind::Variant { enum_name, variant, fields } => {
                let edef = self.types.enums.get(enum_name).cloned().ok_or_else(|| Error::new(span, format!("`{enum_name}` is not an enum declared in the specification file")))?;
                let vdef = edef.variants.iter().find(|v| &v.name == variant).ok_or_else(|| Error::new(span, format!("`{enum_name}` has no variant `{variant}`")))?;
                self.uses_types = true;
                if fields.len() != vdef.fields.len() {
                    return err(format!("`{enum_name}::{variant}` has {} field(s), {} given", vdef.fields.len(), fields.len()));
                }
                // arguments in declaration order
                let mut ordered: Vec<Option<&Expr>> = vec![None; vdef.fields.len()];
                for (k, (fname, fe)) in fields.iter().enumerate() {
                    let i = match fname {
                        None => k,
                        Some(f) => vdef.fields.iter().position(|(n, _)| n.as_deref() == Some(f.as_str())).ok_or_else(|| Error::new(fe.span, format!("`{enum_name}::{variant}` has no field `{f}`")))?,
                    };
                    ordered[i] = Some(fe);
                }
                let mut ts = Vec::new();
                for (fe, (_, fty)) in ordered.iter().zip(&vdef.fields) {
                    let fe = fe.ok_or_else(|| Error::new(span, "a field is missing from the constructor expression"))?;
                    ts.push(self.aeneas_value(fe, fty)?);
                }
                let lean_enum = self.names.get(enum_name).cloned().unwrap_or(enum_name.clone());
                let t = if ts.is_empty() { format!("{lean_enum}.{variant}") } else { format!("({lean_enum}.{variant} {})", ts.join(" ")) };
                (t, SType::Of(RType::Named(enum_name.clone())))
            }
            ExprKind::Field(x, f) => {
                let (t, ty) = self.term(x)?;
                let sname = match &ty {
                    SType::Of(RType::Named(n)) => n.clone(),
                    _ => return err(format!("`.{f}`: field access needs a struct value")),
                };
                let sdef = self.types.structs.get(&sname).cloned().ok_or_else(|| Error::new(span, format!("`{sname}` is not a struct declared in the specification file (enum fields are bound by `match` patterns)")))?;
                let (_, fty) = sdef.fields.iter().find(|(n, _)| n == f).ok_or_else(|| Error::new(span, format!("`{sname}` has no field `{f}`")))?;
                self.uses_types = true;
                let base = if is_atom(&t) { t } else { format!("({t})") };
                (view_term(&format!("{base}.{}", lean_ident(f)), fty), SType::Of(fty.clone()))
            }
            ExprKind::Index(s, i) => {
                let (st, et) = self.seq(s)?;
                let (it, ity) = self.term(i)?;
                let (idx, guard) = match &ity {
                    SType::Of(RType::Int { signed: false, .. }) => {
                        let v = dotval(&it);
                        (v.clone(), format!("({v} : ℤ) < ({st}.length : ℤ)"))
                    }
                    SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt) => {
                        let n = self.as_num(it, &ity);
                        if n.chars().all(|c| c.is_ascii_digit()) {
                            // a literal index is a Nat as it stands
                            (n.clone(), format!("{n} < ({st}.length : ℤ)"))
                        } else {
                            (to_nat(&n), format!("0 ≤ {n} ∧ {n} < ({st}.length : ℤ)"))
                        }
                    }
                    _ => return err("index must be an integer".into()),
                };
                self.guards.push(guard);
                (format!("{st}[{idx}]!"), et)
            }
            ExprKind::Slice(s, a, b) => {
                let (st, et) = self.seq(s)?;
                let a = self.num(a)?;
                let b = self.num(b)?;
                self.guards.push(format!("0 ≤ {a} ∧ {a} ≤ {b} ∧ {b} ≤ ({st}.length : ℤ)"));
                let elem = match et {
                    SType::Of(t) => t,
                    SType::Int => unreachable!(),
                };
                // literal bounds are natural numbers as they stand
                let is_lit = |x: &str| x.chars().all(|c| c.is_ascii_digit());
                let drop = if is_lit(&a) { a.clone() } else { to_nat(&a) };
                let take = match (is_lit(&a), is_lit(&b)) {
                    (true, true) => (b.parse::<i64>().unwrap_or(0) - a.parse::<i64>().unwrap_or(0)).max(0).to_string(),
                    (true, false) if a == "0" => to_nat(&b),
                    _ => to_nat(&format!("{b} - {a}")),
                };
                (format!("(({st}.drop {drop}).take {take})"), SType::Of(RType::Seq(Box::new(elem), SeqKind::Slice)))
            }
            ExprKind::IfVal(c, a, b) => {
                let cp = self.prop(c)?;
                // each branch's partial operations need only be defined
                // where it is taken
                self.flush_guards();
                self.cx.push(Cx::Guard(cp.clone()));
                let ra = self.term(a);
                self.flush_guards();
                self.cx.pop();
                let (at, aty) = ra?;
                self.cx.push(Cx::Guard(format!("¬({cp})")));
                let rb = self.term(b);
                self.flush_guards();
                self.cx.pop();
                let (bt, bty) = rb?;
                if aty == bty && aty != SType::Int {
                    (format!("(if {cp} then {at} else {bt})"), aty)
                } else {
                    let an = self.as_num(at, &aty);
                    let bn = self.as_num(bt, &bty);
                    // an `if` of two literals is a mathematical integer: said
                    // so, or Lean elaborates it as a natural number where no
                    // type is expected (a shift amount, `.toNat`)
                    let lit = |s: &str| {
                        let d = s.strip_prefix("(-").and_then(|x| x.strip_suffix(')')).unwrap_or(s);
                        !d.is_empty() && d.chars().all(|c| c.is_ascii_digit())
                    };
                    // a mathematical integer: said so, or Lean types it from its first branch (a
                    // literal: ℕ) where no type is expected or before it sees the second
                    let _ = lit;
                    (format!("(if {cp} then {an} else {bn} : ℤ)"), SType::Int)
                }
            }
            ExprKind::Method(m) => match &**m {
                Method::Len(s) => (format!("({}.length : ℤ)", self.listlike(s)?), SType::Int),
                Method::MapGet(m, k) => {
                    let (mt, kty) = self.map(m)?;
                    let vty = match &self.env_type_of(m)? {
                        RType::Map(_, v) => (**v).clone(),
                        _ => unreachable!(),
                    };
                    let kt = self.term_as(k, &kty)?;
                    (format!("(Djinn.Vocab.mapGet {mt} {kt})"), SType::Of(RType::Option(Box::new(vty))))
                }
                Method::Count { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    // `List.count x` needs `x` at the element type: a literal
                    // is written as a scalar of it; anything else is counted
                    // through the predicate
                    let target = match count_target(pred, var) {
                        Some(x) => {
                            let (xt, xty) = self.term(&x)?;
                            match &et {
                                _ if xty == et => Some(xt),
                                SType::Of(rt @ RType::Int { .. }) if xt.chars().all(|c| c.is_ascii_digit()) && fits(&xt, rt) => Some(self.term_as(&x, &rt.clone())?),
                                _ => None,
                            }
                        }
                        None => None,
                    };
                    match target {
                        Some(xt) => (format!("(List.count {xt} {st} : ℤ)"), SType::Int),
                        None => {
                            let (v, p) = self.under_elem(var, et, &st, pred)?;
                            (format!("({st}.countP (fun {v} => decide ({p})) : ℤ)"), SType::Int)
                        }
                    }
                }
                Method::Sum(s) => {
                    let (st, et) = self.seq(s)?;
                    let y = self.as_num("y".into(), &et);
                    (format!("({st}.map (fun y => {y})).sum"), SType::Int)
                }
                Method::First(s) => {
                    let (st, et) = self.seq(s)?;
                    (format!("{st}.head?"), opt(et))
                }
                Method::Last(s) => {
                    let (st, et) = self.seq(s)?;
                    (format!("{st}.getLast?"), opt(et))
                }
                Method::Abs(x) => (format!("|{}|", self.num(x)?), SType::Int),
                Method::Min(a, b) => (format!("(min {} {})", self.num(a)?, self.num(b)?), SType::Int),
                Method::Max(a, b) => (format!("(max {} {})", self.num(a)?, self.num(b)?), SType::Int),
                Method::Pow(a, n) => {
                    let n = self.num(n)?;
                    // a literal exponent is a natural number as it stands
                    // (`(32).toNat` would elaborate `32 : ℕ` and fail)
                    let k = if n.chars().all(|c| c.is_ascii_digit()) {
                        n
                    } else {
                        self.guards.push(format!("0 ≤ {n}"));
                        to_nat(&n)
                    };
                    (format!("({} ^ {k})", self.num(a)?), SType::Int)
                }
                Method::BitCount(..) | Method::Rotate(..) => {
                    let (n, nat) = self.bits_method(m)?;
                    (if nat { format!("(({n} : ℕ) : ℤ)") } else { n }, SType::Int)
                }
                Method::Wrapping(op, x, y) => {
                    let (a, (signed, bits), _) = self.machine_int(x, "`.wrapping_add(y)` and kin")?;
                    let b = self.num(y)?;
                    let sym = match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        _ => "*",
                    };
                    let w = width_lean(signed, bits);
                    // what `BitVec` addition and multiplication give: the
                    // residue, balanced (two's complement) for a signed `x`
                    (if signed { format!("(Int.bmod ({a} {sym} {b}) (2 ^ {w}))") } else { format!("(({a} {sym} {b}) % 2 ^ {w})") }, SType::Int)
                }
                Method::Unwrap(o) => {
                    let (ot, oty) = self.term(o)?;
                    let inner = match oty {
                        SType::Of(RType::Option(t)) => SType::Of(*t),
                        _ => return err("`.unwrap()` needs an Option".into()),
                    };
                    self.guards.push(format!("{ot}.isSome = true"));
                    (format!("{ot}.get!"), inner)
                }
                Method::AsBytes(s) => {
                    let (st, ty) = self.term(s)?;
                    match ty {
                        SType::Of(RType::Seq(e, _)) => (st, SType::Of(RType::Seq(e, SeqKind::Slice))),
                        _ => return err("`.as_bytes()` needs a string".into()),
                    }
                }
                Method::SizeBits => ("(UScalarTy.Usize.numBits : ℤ)".into(), SType::Int),
                Method::SizeBound { signed: false, .. } => ("((Usize.max : ℕ) : ℤ)".into(), SType::Int),
                Method::SizeBound { signed: true, max } => (if *max { "Isize.max" } else { "Isize.min" }.into(), SType::Int),
                // a proposition as a value: its truth as a `Bool`
                Method::IsEmpty(_) | Method::Contains(..) | Method::All { .. } | Method::Any { .. } | Method::Windows2All { .. } | Method::IsSome(_) | Method::IsNone(_) | Method::ContainsKey(..) => {
                    let p = self.prop(e)?;
                    (format!("(decide ({p}))"), SType::Of(RType::Bool))
                }
            },
            ExprKind::Call(f, _) => return err(format!("`{f}` cannot appear here (relational calls are lifted at statement level)")),
            // a proposition as a value (a `bool` argument, say): its truth
            ExprKind::Not(_) | ExprKind::Bin(..) | ExprKind::In(..) | ExprKind::InRange(..) | ExprKind::InDomain(..) => {
                let p = self.prop(e)?;
                (format!("(decide ({p}))"), SType::Of(RType::Bool))
            }
        })
    }

    /// A specification term as a value of the Aeneas type `t` (for the
    /// arguments of a user constructor, whose fields are Aeneas-typed):
    /// scalars from `ℤ` literals, sequences from lists are not expressible
    /// without a witness, so only exact types and literals are accepted.
    fn aeneas_value(&mut self, e: &Expr, t: &RType) -> Result<String> {
        let (s, ty) = self.term(e)?;
        match (&ty, t) {
            (SType::Int, RType::Int { signed, bits }) => {
                let suffix = format!("{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() });
                Ok(format!("{s}#{suffix}"))
            }
            (SType::Of(a), b) if a == b => Ok(s),
            (SType::Of(RType::Seq(..)), RType::Seq(..)) => Err(Error::new(e.span, "a sequence cannot be placed in a constructor directly; bind the value with a pattern or compare fields instead")),
            _ => Err(Error::new(e.span, "constructor argument of the wrong type")),
        }
    }
}

/// Does the non-negative literal `s` fit in the machine-integer type `t`?
/// (`usize`/`isize` are taken at 32 bits: Aeneas leaves the width open.)
fn fits(s: &str, t: &RType) -> bool {
    let Ok(v) = s.parse::<u128>() else { return false };
    match t {
        RType::Int { signed, bits } => {
            let w = if *bits == 0 { 32 } else { *bits };
            let w = if *signed { w - 1 } else { w };
            w >= 128 || v < (1u128 << w)
        }
        _ => true,
    }
}

fn lifted_binds(lifted: &[(String, String, Vec<Expr>, RType)]) -> Vec<(String, SType)> {
    lifted.iter().map(|(v, _, _, t)| (v.clone(), SType::Of(t.clone()))).collect()
}

impl<'a> L<'a> {
    fn undeclared(&self, f: &str) -> String {
        undeclared_call(f, self.types.ambient_errors.get(f).map(|s| s.as_str()))
    }
}

/// The message for a call to something a constraint cannot call: a name the
/// file does not define, or a function of the file whose signature a
/// constraint cannot use (`reason`).
pub fn undeclared_call(f: &str, reason: Option<&str>) -> String {
    match reason {
        Some(r) => format!("`{f}` is a function of this file but a constraint cannot call it: {r}. Constraints call the specification's `fn`s and `rel`s, the vocabulary's methods, and the file's ordinary functions over scalars, `bool`, `char`, `Option`s of those and the file's own types (their meaning is their Rust code, translated by Aeneas: trusted, like the rest of this file)"),
        None => format!("`{f}` is neither a `fn` or `rel` of the specification nor a function of this file. A constraint may call the specification's own declarations, the vocabulary's methods, and the ordinary functions written in this file (trusted Rust, translated by Aeneas). If `{f}` does I/O, it belongs in a driver beside the block (DESIGN.md §7)"),
    }
}

/// An expression that denotes a proposition rather than a value.
fn is_proplike(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Bin(op, _, _) => op.is_cmp() || matches!(op, BinOp::And | BinOp::Or),
        ExprKind::Not(_) | ExprKind::In(..) | ExprKind::InRange(..) | ExprKind::InDomain(..) => true,
        ExprKind::Method(m) => m.is_prop(),
        _ => false,
    }
}

fn opt(t: SType) -> SType {
    match t {
        SType::Of(t) => SType::Of(RType::Option(Box::new(t))),
        SType::Int => SType::Int,
    }
}

pub(crate) fn stype_lean(t: &SType, names: &TypeNames) -> String {
    match t {
        SType::Int => "ℤ".into(),
        SType::Of(t) => view_type(t, names),
    }
}

/// `|y| y == x` (either side, through `*`/`&`) → `x`
fn count_target(pred: &Expr, var: &str) -> Option<Expr> {
    if let ExprKind::Bin(BinOp::Eq, l, r) = &pred.kind {
        if matches!(&l.kind, ExprKind::Var(v) if v == var) && !mentions(r, var) {
            return Some((**r).clone());
        }
        if matches!(&r.kind, ExprKind::Var(v) if v == var) && !mentions(l, var) {
            return Some((**l).clone());
        }
    }
    None
}

fn mentions(e: &Expr, var: &str) -> bool {
    match &e.kind {
        ExprKind::Method(_) => true,
        _ => e.mentions(var),
    }
}

/// `pred` of `windows(2).all(|w| pred)` with `w[0]` and `w[1]` replaced by
/// the variables `a` and `b`, everywhere (in indices, calls, casts, nested
/// closures that do not bind `w` themselves, …).
fn subst_window(e: &Expr, w: &str, a: &str, b: &str) -> Expr {
    if let ExprKind::Index(seq, i) = &e.kind {
        if matches!(&seq.kind, ExprKind::Var(v) if v == w) {
            match &i.kind {
                ExprKind::Int(n) if n == "0" => return Expr::new(e.span, ExprKind::Var(a.into())),
                ExprKind::Int(n) if n == "1" => return Expr::new(e.span, ExprKind::Var(b.into())),
                _ => {}
            }
        }
    }
    let e2 = e.map_children(&mut |x| subst_window(x, w, a, b));
    // `map_children` leaves closure bodies alone
    let ExprKind::Method(m) = &e2.kind else { return e2 };
    let m2 = match &**m {
        Method::Count { seq, var, pred } if var != w => Method::Count { seq: seq.clone(), var: var.clone(), pred: subst_window(pred, w, a, b) },
        Method::All { seq, var, pred } if var != w => Method::All { seq: seq.clone(), var: var.clone(), pred: subst_window(pred, w, a, b) },
        Method::Any { seq, var, pred } if var != w => Method::Any { seq: seq.clone(), var: var.clone(), pred: subst_window(pred, w, a, b) },
        Method::Windows2All { seq, var, pred } if var != w => Method::Windows2All { seq: seq.clone(), var: var.clone(), pred: subst_window(pred, w, a, b) },
        _ => return e2,
    };
    Expr::new(e2.span, ExprKind::Method(Box::new(m2)))
}

#[cfg(test)]
mod bit_tests {
    use crate::emit::{spec_lean, EmitCx};
    use std::collections::HashMap;

    fn lowered(src: &str) -> Vec<crate::lower::Lowered> {
        let p = crate::parse_program(src).unwrap();
        crate::lower_program(&p).unwrap()
    }

    fn spec_of(src: &str) -> String {
        let l = lowered(src);
        let names = HashMap::new();
        let tn = crate::types::TypeNames::new();
        let cx = EmitCx { ns: "T", impl_names: &names, type_names: &tn, has_types: false, has_funs: false, unfoldable: vec![] };
        spec_lean(&cx, &l)
    }

    #[test]
    fn bitwise_on_unsigned_values_is_nat() {
        let l = lowered("djinn! { pub fn f(x: u32, y: u32) -> r: u32 { r == (x & y) ^ (x >> 3); } }");
        assert!(l[0].spec[0].contains("((((x.val &&& y.val) ^^^ (x.val >>> 3))) : ℕ) : ℤ)"), "{}", l[0].spec[0]);
        assert!(l[0].wf.is_empty(), "no guard for unsigned operands: {:?}", l[0].wf);
    }

    #[test]
    fn bitwise_on_signed_values_is_guarded() {
        let l = lowered("djinn! { pub fn f(x: i32) -> r: i32 { r == x & 7; } }");
        assert!(l[0].spec[0].contains("(x.val.toNat &&& 7)"), "{}", l[0].spec[0]);
        assert!(l[0].wf.iter().any(|w| w.contains("0 ≤ x.val")), "{:?}", l[0].wf);
    }

    #[test]
    fn shifts_of_integers_are_arithmetic() {
        let l = lowered("djinn! { pub fn f(x: i32, n: u32) -> r: i32 { r == (x >> 2) + (x << n); } }");
        assert!(l[0].spec[0].contains("(x.val / 2 ^ 2)"), "{}", l[0].spec[0]);
        assert!(l[0].spec[0].contains("(x.val * 2 ^ n.val)"), "{}", l[0].spec[0]);
    }

    #[test]
    fn literal_exponent_is_a_nat() {
        let l = lowered("djinn! { pub fn f(x: u64) -> r: u64 { r == x % 2.pow(32); } }");
        assert!(l[0].spec[0].contains("(2 ^ 32)"), "{}", l[0].spec[0]);
        assert!(!l[0].spec[0].contains("toNat"), "{}", l[0].spec[0]);
    }

    #[test]
    fn array_constants_are_tables() {
        let src = "pub const K: &[u32] = &[1, 0x10];\npub const D: [i16; 2] = [-3, 3];\npub const W: &[&str] = &[\"skipped\"];\n\
             djinn! {\n #[requires(i < K.len())] pub fn f(i: usize) -> r: u32 { r == K[i]; }\n\
             #[requires(i < D.len())] pub fn g(i: usize) -> r: i16 { r == D[i]; } }";
        let s = spec_of(src);
        assert!(s.contains("import T.Tables"), "{s}");
        assert!(s.contains("r = K[i.val]!"), "{s}");
        assert!(!s.contains("def K"), "tables live in Tables.lean");
        let p = crate::parse_program(src).unwrap();
        assert!(!p.types.consts.contains_key("W"), "a non-integer array constant is not a table");
        let mut names: Vec<&String> = p.types.consts.iter().filter(|(_, c)| c.table.is_some()).map(|(n, _)| n).collect();
        names.sort();
        let tables: Vec<crate::emit::Table> = names.iter().map(|n| { let c = &p.types.consts[*n]; crate::emit::Table { name: (*n).clone(), ty: c.ty.clone(), elems: c.table.clone().unwrap() } }).collect();
        let t = crate::emit::tables_lean("T", &tables);
        // entries packed lowest first: -3 and 3 as 16-bit two's complement
        assert!(t.contains("def D_packed : List Nat := [\n  0x3fffd]"), "{t}");
        assert!(t.contains("def K_packed : List Nat := [\n  0x1000000001]"), "{t}");
        assert!(t.contains("def K : List U32 := (List.range 2).map (fun i => ⟨BitVec.ofNat 32 (K_entry i)⟩)"), "{t}");
        assert!(t.contains("@[simp] theorem K_length : K.length = 2"), "{t}");
        assert!(t.contains("attribute [irreducible] K"), "{t}");
        let m = crate::emit::table_model("T", "spec.D", &tables[0]);
        assert!(m.starts_with("def spec.D : Result (Array Std.I16 2#usize)"), "{m}");
    }

    #[test]
    fn tables_are_chunked() {
        let elems: Vec<String> = (0..3000).map(|i| (i % 256).to_string()).collect();
        let t = crate::emit::tables_lean("T", &[crate::emit::Table { name: "B".into(), ty: crate::ast::RType::Seq(Box::new(crate::ast::RType::Int { signed: false, bits: 8 }), crate::ast::SeqKind::Slice), elems }]);
        // 2048 entries of 8 bits to a number: two numbers
        assert!(t.contains("2048 entries to a number"), "{t}");
        assert_eq!(t.matches("0x").count(), 2);
    }

    #[test]
    fn width_methods_lower_to_the_models_definitions() {
        let l = lowered("djinn! { pub fn f(x: u32, y: u64, z: u16) -> r: u32 { r == x.rotate_right(7) ^ y.count_ones() ^ z.leading_zeros(); } }");
        let s = &l[0].spec[0];
        assert!(s.contains("(x.bv.rotateRight 7).toNat"), "{s}");
        assert!(s.contains("(y.bv).cpop.toNat"), "{s}");
        assert!(s.contains("(Aeneas.Std.BitVec.leadingZeros (z.bv))"), "{s}");
        assert!(l[0].wf.is_empty(), "rotations and counts are natural numbers: {:?}", l[0].wf);
    }

    #[test]
    fn wrapping_reduces_to_the_width() {
        let l = lowered("djinn! { pub fn f(a: u32, b: u32, c: i8) -> r: i32 { r == (a.wrapping_add(b) as u32).wrapping_mul(3) + c.wrapping_sub(1); } }");
        let s = &l[0].spec[0];
        assert!(s.contains("((((a.val : ℤ) + (b.val : ℤ)) % 2 ^ 32) * 3) % 2 ^ 32)"), "{s}");
        assert!(s.contains("(Int.bmod (c.val - 1) (2 ^ 8))"), "{s}");
    }

    #[test]
    fn arrays_have_their_length() {
        let l = lowered("pub const N: usize = 3;\ndjinn! { pub fn f(a: [u8; N]) -> r: [u8; 4] { for i in 0..4 { r[i] == 0; } } }");
        assert!(l[0].pre.iter().any(|p| p == "(a.length : ℤ) = 3"), "{:?}", l[0].pre);
        assert_eq!(l[0].spec[0], "(r.length : ℤ) = 4");
    }

    #[test]
    fn width_methods_need_a_machine_integer() {
        let p = crate::parse_program("djinn! { pub rel f(x: int) -> r: int { r == x.count_ones(); } }").unwrap();
        let e = crate::lower_program(&p).unwrap_err();
        assert!(e.msg.contains("need a machine integer"), "{}", e.msg);
    }
    #[test]
    fn lean_keywords_are_escaped() {
        let l = lowered("djinn! { pub rel f(end: int, by: int) -> r: int { r == end + by; for fun in 0..end { 0 <= fun; } } }");
        assert!(l[0].spec[0].contains("r = («end» + «by»)"), "{}", l[0].spec[0]);
        assert!(l[0].spec[1].contains("∀ «fun» : ℤ"), "{}", l[0].spec[1]);
        let s = spec_of("djinn! { pub rel f(end: int) -> r: int { r == end; } }");
        assert!(s.contains("def f_spec («end» : ℤ) (r : ℤ)"), "{s}");
    }

    #[test]
    fn recursor_field_names_are_rejected() {
        let e = crate::parse_program("pub struct B { pub rec: u8 }\ndjinn! { pub rel f(x: int) -> r: int { r == x; } }").unwrap_err();
        assert!(e.msg.contains("cannot be named `rec`"), "{}", e.msg);
    }

    #[test]
    fn inhabited_in_dependency_order() {
        let p = crate::parse_program("pub struct O { pub i: I, pub n: u32 }\npub struct I { pub v: Vec<u8> }\ndjinn! { pub rel f(o: &[O]) -> r: int { r == o.len(); } }").unwrap();
        let l = crate::lower_program(&p).unwrap();
        assert_eq!(l[0].named_types, vec!["I".to_string(), "O".to_string()]);
    }

    #[test]
    fn literal_ifs_are_integers() {
        let l = lowered("djinn! { pub rel f(x: u32, c: bool) -> r: int { r == x >> (if c { 3 } else { 4 }); } }");
        assert!(l[0].spec[0].contains("((if c = true then 3 else 4 : ℤ) : ℤ).toNat"), "{}", l[0].spec[0]);
        // every integer value-if is ascribed: Lean would type it from a literal first branch
        let l = lowered("djinn! { pub rel f(p: u8, c: bool) -> r: int { r == if c { 127 } else { p }; } }");
        assert!(l[0].spec[0].contains("(if c = true then 127 else (p.val : ℤ) : ℤ)"), "{}", l[0].spec[0]);
    }

    #[test]
    fn counted_literals_take_the_element_type() {
        let l = lowered("djinn! { pub rel f(v: &[u8], w: &[i16]) -> r: int { r == v.iter().filter(|x| **x == 1).count() + w.iter().filter(|x| **x == -1).count(); } }");
        assert!(l[0].spec[0].contains("List.count 1#u8 v"), "{}", l[0].spec[0]);
        assert!(l[0].spec[0].contains("w.countP (fun x => decide (x.val = (-1)))"), "{}", l[0].spec[0]);
    }

    #[test]
    fn recursive_top_level_facts_are_chained() {
        let l = lowered("djinn! { #[decreases(253 - k)] pub rel f(k: int) -> r: int { k <= 253; if k == 253 { r == 0; } else { r == 1 + f(k + 1); } } }");
        assert_eq!(l[0].spec.len(), 1);
        assert!(l[0].spec[0].starts_with("(k ≤ 253 ∧ (k ≤ 253 → "), "{}", l[0].spec[0]);
    }

    #[test]
    fn propositions_as_bool_values() {
        let l = lowered("djinn! { pub rel g(b: bool) -> r: int { if b { r == 1; } else { r == 0; } }\npub rel f(x: int) -> r: int { r == g(x > 0); } }");
        assert!(l[1].spec[0].contains("g_spec (decide (x > 0)) r"), "{}", l[1].spec[0]);
    }

    #[test]
    fn calls_in_closures_and_loop_bounds() {
        let l = lowered("djinn! { pub rel ok(x: u8) -> b: bool { b == (x < 10); }\npub rel n(x: int) -> k: int { k == x; }\n\
            pub rel f(s: &[u8], t: &[u8], x: int) -> b: bool { b == s.iter().all(|e| ok(*e) && t[*e] < 5); for j in 0..n(x) { 0 <= j; } } }");
        let f = &l[2];
        assert!(f.spec[0].contains("(∀ e, e ∈ s → (ok_spec e true ∧"), "{}", f.spec[0]);
        assert!(f.spec[1].starts_with("(∃ v_call0 : ℤ, n_spec x v_call0 ∧ (∀ j : ℤ, 0 ≤ j → j < v_call0 →"), "{}", f.spec[1]);
        // the index guard is stated for every element
        assert!(f.wf.iter().any(|w| w.starts_with("∀ e : U8, e ∈ s →") && w.contains("< (t.length : ℤ)")), "{:?}", f.wf);
    }

    #[test]
    fn value_if_branches_are_guarded() {
        let l = lowered("djinn! { pub rel f(c: bool, a: &[u8], i: int) -> r: int { r == if c { a[i] } else { 0 }; } }");
        assert_eq!(l[0].wf, vec!["c = true → (0 ≤ i ∧ i < (a.length : ℤ))".to_string()]);
        let l = lowered("djinn! { pub rel n(x: int) -> k: int { k == x; }\npub rel f(c: bool, x: int) -> r: int { r == if c { n(x) } else { n(x + 1) + 1 }; } }");
        assert!(l[1].spec[0].starts_with("((c = true → n_spec x r) ∧ (¬(c = true) → (∃ v_call0 : ℤ, n_spec (x + 1) v_call0"), "{}", l[1].spec[0]);
    }

    #[test]
    fn integer_bounds() {
        let l = lowered("djinn! { pub rel f(n: int) -> b: bool { b == (n <= usize::MAX && n <= u32::MAX && i8::MIN <= n && n < u16::BITS); } }");
        let s = &l[0].spec[0];
        assert!(s.contains("((Usize.max : ℕ) : ℤ)") && s.contains("4294967295") && s.contains("(-128)") && s.contains("< 16"), "{s}");
    }
    #[test]
    fn comparisons_as_arguments_and_implications_in_values() {
        let l = lowered("djinn! { pub rel g(a: bool, b: bool) -> r: int { r == 0; }\npub rel f(col: int, row: int) -> r: int { r == g(col > 0, row > 0); } }");
        assert!(l[1].spec[0].contains("g_spec (decide (col > 0)) (decide (row > 0)) r"), "{}", l[1].spec[0]);
        let l = lowered("djinn! { pub rel f(a: bool, b: bool) -> r: bool { r == (a => b); } }");
        assert!(l[0].spec[0].contains("(a = true → b = true)"), "{}", l[0].spec[0]);
    }

    #[test]
    fn literal_exponents_are_integers() {
        let l = lowered("pub const M: usize = 268435456;\ndjinn! { pub rel f(x: int) -> r: int { r == x % 2.pow(64 * M); } }");
        assert!(l[0].spec[0].contains("(2 ^ ((64 * 268435456) : ℤ).toNat)"), "{}", l[0].spec[0]);
    }

    #[test]
    fn integers_in_byte_tables_compare_values() {
        let l = lowered("pub const B: &[u8] = &[1, 2];\ndjinn! { pub rel f(x: int) -> r: bool { r == (x in B); } }");
        assert!(l[0].spec[0].contains("x ∈ (B.map (fun y => (y.val : ℤ)))"), "{}", l[0].spec[0]);
        // a literal stays a scalar of the element type
        let l = lowered("pub const B: &[u8] = &[1, 2];\ndjinn! { pub rel f(x: int) -> r: bool { r == (1 in B); } }");
        assert!(l[0].spec[0].contains("1#u8 ∈ B"), "{}", l[0].spec[0]);
    }

    #[test]
    fn shifts_beside_literals_in_value_ifs() {
        let l = lowered("djinn! { pub rel f(bc: int) -> r: int { r == if bc == 1 { 192 } else if bc <= 5 { 144 << bc } else { 1 << bc }; } }");
        assert!(l[0].spec[0].starts_with("r = (if bc = 1 then 192 else (if bc ≤ 5 then"), "{}", l[0].spec[0]);
        assert!(l[0].spec[0].ends_with(": ℤ) : ℤ)"), "{}", l[0].spec[0]);
    }
    #[test]
    fn match_on_option_and_result() {
        let l = lowered("djinn! { pub rel f(x: Option<u32>) -> r: int { match x { Some(v) => { r == v + 1; } None => { r == 0; } } }\n\
            pub rel g(x: Result<u8, u16>) -> r: int { match x { Ok(a) => { r == a; } Err(e) => { r == e; } } } }");
        assert!(l[0].spec[0].contains("(match x with | .some v_0 => r = ((v_0.val : ℤ) + 1) | .none => r = 0)"), "{}", l[0].spec[0]);
        assert!(l[1].spec[0].contains("| .Ok a_0 => r = (a_0.val : ℤ) | .Err e_0 => r = (e_0.val : ℤ))"), "{}", l[1].spec[0]);
    }
    #[test]
    fn split_value_if_lifts_its_condition() {
        // `p` has no output for x ≤ 0: the condition is the lifted value `v`,
        // with or without relation calls in the branches
        let src = "djinn! { pub rel p(x: int) -> b: bool { x > 0; b == true; }\npub rel g(x: int) -> r: int { r == x; }\n\
            pub rel f(x: int) -> r: int { r == if p(x) { g(1) } else { 0 }; } }";
        let l = lowered(src);
        let s = &l[2].spec[0];
        assert!(s.starts_with("(∃ v_call0 : Bool, p_spec x v_call0 ∧ ((v_call0 = true →"), "{s}");
        assert!(!s.contains("p_spec x true"), "{s}");
    }

    #[test]
    fn signed_rotations_of_nested_receivers() {
        let l = lowered("pub struct S { pub v: i32 }\ndjinn! { pub rel f(s: &[S]) -> r: int { r == s[0].v.rotate_left(1) + s[0].v.count_ones(); } }");
        assert!(l[0].spec[0].contains(".rotateLeft 1).toInt"), "{}", l[0].spec[0]);
    }

    #[test]
    fn shifts_are_not_comparisons() {
        let l = lowered("djinn! { pub rel f(x: u32, a: int) -> r: bool { r == (x >> 3 < 5 && a < x << 1); } }");
        assert!(l[0].spec[0].contains("(x.val >>> 3)") && l[0].spec[0].contains("(x.val <<< 1)"), "{}", l[0].spec[0]);
    }
    #[test]
    fn more_lean_keywords_and_unicode_names() {
        let l = lowered("djinn! { pub rel f(to: int, until: int) -> r: int { r == to + until; } }");
        assert!(l[0].spec[0].contains("(«to» + «until»)"), "{}", l[0].spec[0]);
        assert_eq!(crate::types::lean_ident("λ"), "«λ»");
    }

    #[test]
    fn implicit_preconditions_are_preconditions() {
        // the array length and a String's UTF-8 are owed by callers (wf), not
        // silently assumed in their relation
        let l = lowered("djinn! { pub rel g(end: [u8; 3]) -> r: int { r == end[0]; }\npub rel h(s: String) -> r: int { r == s.len(); }\n\
            pub rel f(a: &[u8], t: String) -> r: int { r == g(a) + h(t); } }");
        assert!(l[0].pre.iter().any(|p| p == "(«end».length : ℤ) = 3"), "{:?}", l[0].pre);
        assert!(l[1].pre.iter().any(|p| p.contains("∃ s' : String, Djinn.Vocab.bytes s' = s")), "{:?}", l[1].pre);
        assert!(l[2].wf.iter().any(|w| w.contains("g_pre a")), "{:?}", l[2].wf);
    }

    #[test]
    fn split_value_if_under_and_keeps_its_guards_inside() {
        let l = lowered("djinn! { pub rel g(x: u8) -> r: int { r == x; }\n\
            pub rel f(a: &[u8], i: int) -> r: bool { r == (i >= 0 && i < a.len() && (if a[i] > 0 { g(a[i]) } else { 0 }) == 1); } }");
        // the index guard of the condition is stated under `0 ≤ i ∧ i < len`
        assert!(!l[1].wf.iter().any(|w| w.starts_with("(0 ≤ i ∧ i < (a.length : ℤ))") || w == "0 ≤ i ∧ i < (a.length : ℤ)"), "{:?}", l[1].wf);
    }

    #[test]
    fn value_if_in_a_loop_bound_is_split() {
        let l = lowered("djinn! { pub rel n(x: int) -> k: int { k == x; }\n\
            pub rel f(c: bool, x: int) -> r: int { for i in 0..(if c { n(x) } else { 0 }) { 0 <= i; } r == 0; } }");
        assert!(l[1].spec[0].starts_with("((c = true → (∃ v_call0 : ℤ, n_spec x v_call0"), "{}", l[1].spec[0]);
    }

    #[test]
    fn literals_outside_the_element_type_compare_by_value() {
        let l = lowered("djinn! { pub rel f(v: &[u8]) -> r: bool { r == (300 in v); } }");
        assert!(l[0].spec[0].contains("300 ∈ (v.map (fun y => (y.val : ℤ)))"), "{}", l[0].spec[0]);
        let l = lowered("djinn! { pub rel f(n: int) -> r: bool { r == (n < usize::BITS); } }");
        assert!(l[0].spec[0].contains("UScalarTy.Usize.numBits"), "{}", l[0].spec[0]);
    }

    #[test]
    fn membership_probe_does_not_duplicate_guards() {
        let l = lowered("djinn! { pub rel f(c: bool, a: &[u8], i: int, b: &[int]) -> r: bool { r == ((if c { a[i] } else { 0 }) in b); } }");
        assert_eq!(l[0].wf.len(), 1, "{:?}", l[0].wf);
    }

    #[test]
    fn windows_read_like_closures() {
        // `w[0]` inside an index or a call is the window's first element; the
        // index guards are owed for every adjacent pair, under its binders
        let l = lowered("djinn! { pub rel g(x: u8) -> k: int { k == x; }\npub rel f(s: &[u8], t: &[u8], i: int) -> b: bool { b == s.windows(2).all(|w| t[w[0]] <= t[w[1]] && g(w[0]) == i); } }");
        let f = &l[1];
        assert!(f.spec[0].contains("List.Chain' (fun w0 w1 => (((t[w0.val]!).val : ℤ) ≤ ((t[w1.val]!).val : ℤ) ∧ g_spec w0 i)) s"), "{}", f.spec[0]);
        assert_eq!(f.wf, vec!["∀ w0 : U8, ∀ w1 : U8, (w0, w1) ∈ List.zip s (List.tail s) → ((w0.val : ℤ) < (t.length : ℤ)) ∧ ((w1.val : ℤ) < (t.length : ℤ))".to_string()]);
    }

    #[test]
    fn implications_as_arguments_and_closure_bodies() {
        let l = lowered("djinn! { pub rel g(a: bool, b: bool) -> r: int { r == 0; }\npub rel f(a: bool, b: bool, c: bool, s: &[u8]) -> r: int { r == g(a => b, c); s.iter().all(|x| *x > 0 => *x < 5); s.iter().any(|&x| x > 0 => x < 5 && c); } }");
        let f = &l[1];
        assert!(f.spec[0].contains("g_spec (decide ((¬(a = true) ∨ b = true))) c r"), "{}", f.spec[0]);
        assert!(f.spec[1].contains("(∀ x, x ∈ s → ((x.val : ℤ) > 0 → (x.val : ℤ) < 5))"), "{}", f.spec[1]);
        assert!(f.spec[2].contains("(∃ x, x ∈ s ∧ ((x.val : ℤ) > 0 → ((x.val : ℤ) < 5 ∧ c = true)))"), "{}", f.spec[2]);
    }

    #[test]
    fn made_up_names_avoid_the_sources() {
        // a pattern binder `x_0`, a lifted call's `v_call0` and `range`'s `a0`
        // are primed where the source has that name
        let l = lowered("djinn! { pub rel g(x: int) -> k: int { k == x; }\npub rel f(x_0: int, v_call0: int, a0: int, o: Option<u8>) -> r: int { match o { Some(x) => { r == x + x_0; } None => { r == 0; } } g(g(v_call0)) == 1; a0 in range(g); } }");
        let f = &l[1];
        assert!(f.spec[0].contains("| .some x_0' => r = ((x_0'.val : ℤ) + x_0)"), "{}", f.spec[0]);
        assert!(f.spec[1].contains("(∃ v_call0' : ℤ, g_spec v_call0 v_call0' ∧ g_spec v_call0' 1)"), "{}", f.spec[1]);
        assert!(f.spec[2].contains("(∃ (a0' : ℤ), g_spec a0' a0)"), "{}", f.spec[2]);
        // and without a clash nothing changes
        let l = lowered("djinn! { pub rel f(o: Option<u8>) -> r: int { match o { Some(x) => { r == x; } None => { r == 0; } } } }");
        assert!(l[0].spec[0].contains("| .some x_0 => r = (x_0.val : ℤ)"), "{}", l[0].spec[0]);
    }

    #[test]
    fn strings_inside_values_are_bounded_and_utf8() {
        let src = "pub struct P { pub name: String, pub tags: Vec<String>, pub nick: Option<String> }\n\
                   djinn! { pub rel f(s: String) -> r: int { r == s.len(); }\n\
                   pub rel g(p: P) -> r: int { r == f(p.name); }\n\
                   pub rel h(v: Vec<String>, ps: Vec<P>) -> r: int { r == f(v[0]); }\n\
                   pub rel k(p: P) -> r: int { r == g(p); } }";
        let l = lowered(src);
        let max = "≤ ((Usize.max : ℕ) : ℤ)";
        // a struct's `String` fields (Lean strings, UTF-8 already) hold at most `usize::MAX` bytes
        assert_eq!(l[1].pre, vec![
            format!("((Djinn.Vocab.bytes p.«name»).length : ℤ) {max}"),
            format!("(∀ e', e' ∈ p.tags.val → ((Djinn.Vocab.bytes e').length : ℤ) {max})"),
            format!("(∀ e', p.nick = some e' → ((Djinn.Vocab.bytes e').length : ℤ) {max})"),
        ]);
        // a `Vec<String>`'s elements are views: bounded and UTF-8, like a `String` input
        assert_eq!(l[2].pre[0], format!("(∀ e', e' ∈ v → ((e'.length : ℤ) {max} ∧ (∃ s' : String, Djinn.Vocab.bytes s' = e')))"));
        assert!(l[2].pre[1].starts_with("(∀ e', e' ∈ ps → (((Djinn.Vocab.bytes e'.«name»).length : ℤ)") && l[2].pre[1].contains("∀ e'', e'' ∈ e'.tags.val"), "{}", l[2].pre[1]);
        // a caller owes them: `k` calls `g`, whose input is a struct with strings
        assert_eq!(l[3].wf, vec!["(g_pre p)".to_string()]);
    }

    #[test]
    fn maps_of_strings_are_viewed_entrywise() {
        use crate::ast::{RType, SeqKind};
        let t = RType::Map(Box::new(RType::Seq(Box::new(RType::Int { signed: false, bits: 8 }), SeqKind::String)), Box::new(RType::Int { signed: false, bits: 8 }));
        assert_eq!(crate::types::view_type(&t, &Default::default()), "List (List U8 × U8)");
        assert_eq!(crate::types::view_of("m", &t), "(m.entries.map (fun y => ((Djinn.Vocab.bytes y.1), y.2)))");
        let t = RType::Map(Box::new(RType::Int { signed: false, bits: 32 }), Box::new(RType::Int { signed: false, bits: 64 }));
        assert_eq!(crate::types::view_of("m", &t), "m.entries");
    }
}
