//! Lowering declarations to Verus `spec fn` bodies: the Verus backend's
//! counterpart of `lower.rs`. The structure follows `lower.rs` statement
//! for statement, so that the two backends state the same propositions in
//! two syntaxes; only the rendering differs:
//!
//! | Lean                         | Verus                                  |
//! |------------------------------|----------------------------------------|
//! | `List T`, `ℤ`                | `Seq<T>`, `int`                        |
//! | `x.val` (a scalar's value)   | `(x as int)`                           |
//! | `∀ x : T, P` / `∃`           | `forall|x: T| #![auto] P` / `exists`   |
//! | `l[i]!`, `l.length`          | `l[i]`, `l.len() as int`               |
//! | `(l.drop a).take (b - a)`    | `crate::vocab::slice(l, a, b)`         |
//! | `x ∈ l`                      | `l.contains(x)`                        |
//! | `match s with | .some x => …`| `match s { Option::Some(x) => …, … }`  |
//! | `f_spec a b r`               | `f_spec(a, b, r)`                      |
//! | `t = u` (a user type holding | `djinn_eq_T(t, u)` (`eq_fn`: the fields|
//! |  a `Vec`/`String`/`HashMap`) |  compared through their views)         |
//!
//! The result is a `lower::Lowered` (the same record the Lean backend
//! produces), whose strings are Verus expressions; its `helpers` are the
//! `djinn_eq_T` definitions `relations.rs` needs.

use crate::ast::*;
use crate::lower::{DeclInfo, Lowered};
use crate::types::TypeNames;
use std::collections::HashMap;

/// A made-up name's marker: no name of a specification may contain `djinn`
/// (checked by `lower_with`), so a name holding it is none of the source's.
const RESERVED: &str = "djinn";

/// Placeholder in a self-call of a declaration with choices: the choice
/// functions, passed on unchanged, are all known only once the whole body
/// is lowered (`", c1, c2"` — with its leading comma — or nothing).
const SELF_CHOICES: &str = "⟪SELF_CHOICES⟫";

/// Verus's additional keywords (beyond Rust's): a Rust name that is one is
/// written as a raw identifier `r#name` inside `verus! { … }`.
const VERUS_KEYWORDS: &[&str] = &[
    "spec", "proof", "exec", "requires", "ensures", "recommends", "decreases", "invariant", "invariant_except_break", "forall", "exists", "choose", "ghost", "tracked", "open", "closed", "uninterp",
    "assume", "assert", "int", "nat", "implies", "via", "when", "returns", "opens_invariants", "no_unwind", "axiom", "broadcast", "global", "is", "has", "matches", "FnSpec", "trigger", "reveal", "hide",
    "by", "with", "any", "none", "layout", "size_of", "align_of", "default_ensures", "unwind", "invariant_ensures", "ensures_", "calc", "assert_by", "assert_forall_by", "assert_by_compute", "proof_fn",
    "spec_fn", "Ghost", "Tracked",
];

/// The `spec fn` of `relations.rs` that denotes the ambient function `f`.
pub fn ambient_spec_name(f: &str) -> String {
    format!("{RESERVED}_amb_{f}")
}

/// The width of a machine integer type as a `nat` term (`usize`'s is the
/// target's).
pub fn width_verus(signed: bool, bits: u32) -> String {
    if bits == 0 {
        format!("({}size::BITS as nat)", if signed { "i" } else { "u" })
    } else {
        format!("{bits}nat")
    }
}

/// A Rust identifier as a Verus identifier.
pub fn verus_ident(n: &str) -> String {
    if VERUS_KEYWORDS.contains(&n) {
        format!("r#{n}")
    } else {
        n.to_string()
    }
}

// ----------------------------------------------------------------- types

/// A Verus type as the implementation sees it (the stubs' signatures):
/// `&[i32]`, `Vec<u8>`, `Option<Vec<u8>>`, `crate::spec::Token`.
pub fn exec_type(t: &RType, names: &TypeNames) -> String {
    match t {
        RType::Int { signed, bits } => format!("{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() }),
        RType::Bool => "bool".into(),
        RType::Char => "char".into(),
        RType::MathInt => "int".into(),
        RType::Seq(e, k) => match k {
            SeqKind::Slice => format!("&[{}]", exec_type(e, names)),
            SeqKind::Vec => format!("Vec<{}>", exec_type(e, names)),
            SeqKind::Array(n) => format!("[{}; {n}]", exec_type(e, names)),
            SeqKind::Str => "&str".into(),
            SeqKind::String => "String".into(),
        },
        RType::Map(k, v) => format!("std::collections::HashMap<{}, {}>", exec_type(k, names), exec_type(v, names)),
        RType::Option(e) => format!("Option<{}>", exec_type(e, names)),
        RType::Result(a, b) => format!("Result<{}, {}>", exec_type(a, names), exec_type(b, names)),
        RType::Unit => "()".into(),
        RType::Named(n) => names.get(n).cloned().unwrap_or_else(|| n.clone()),
    }
}

/// The type of a value in a relation: sequences are `Seq`s, `int` is `int`.
pub fn view_type(t: &RType, names: &TypeNames) -> String {
    match t {
        RType::Seq(e, _) => format!("Seq<{}>", view_type(e, names)),
        RType::Map(k, v) => format!("Map<{}, {}>", view_type(k, names), view_type(v, names)),
        RType::Option(e) => format!("Option<{}>", view_type(e, names)),
        RType::Result(a, b) => format!("Result<{}, {}>", view_type(a, names), view_type(b, names)),
        _ => exec_type(t, names),
    }
}

/// Does the view of a value of this type differ from the value?
pub fn needs_view(t: &RType) -> bool {
    match t {
        RType::Seq(..) | RType::Map(..) => true,
        RType::Option(e) => needs_view(e),
        RType::Result(a, b) => needs_view(a) || needs_view(b),
        _ => false,
    }
}

/// The `spec fn` of `relations.rs` comparing two values of the user type `n`
/// structurally (`eq_fn`).
pub fn eq_fn_name(n: &str) -> String {
    format!("{RESERVED}_eq_{n}")
}

/// The fields of a user type (a struct's, or those of every variant).
fn fields_of<'t>(n: &str, types: &'t TypeDefs) -> Vec<&'t RType> {
    let mut v: Vec<&RType> = Vec::new();
    if let Some(s) = types.structs.get(n) {
        v.extend(s.fields.iter().map(|(_, t)| t));
    }
    if let Some(e) = types.enums.get(n) {
        v.extend(e.variants.iter().flat_map(|va| va.fields.iter().map(|(_, t)| t)));
    }
    v
}

/// Must two values of this type be compared structurally (`eq_term`) rather
/// than with `==`? Verus's `==` on a value holding a `Vec`, a `String` or a
/// `HashMap` is equality of the Rust values, which vstd relates to the views
/// one way only (`a == b ==> a@ == b@`): `o1 == o2` for two such outputs
/// would be unprovable, where the Lean backend compares contents. So a user
/// type whose fields (transitively) carry a view, and the `Option`s,
/// `Result`s, sequences and maps of such types, are compared field by field
/// through the views.
pub fn needs_eq(t: &RType, types: &TypeDefs) -> bool {
    fn go(t: &RType, types: &TypeDefs, stack: &mut Vec<String>) -> bool {
        match t {
            RType::Named(n) => {
                if stack.contains(n) {
                    return false;
                }
                stack.push(n.clone());
                let r = fields_of(n, types).into_iter().any(|ft| needs_view(ft) || go(ft, types, stack));
                stack.pop();
                r
            }
            RType::Seq(e, _) | RType::Option(e) => go(e, types, stack),
            RType::Result(a, b) => go(a, types, stack) || go(b, types, stack),
            RType::Map(_, v) => go(v, types, stack),
            _ => false,
        }
    }
    go(t, types, &mut Vec::new())
}

/// `needs_eq` from a predicate on the user types alone (the emitter, which
/// has no `TypeDefs`, knows them by the `djinn_eq` helpers the lowering made).
pub fn needs_eq_with(t: &RType, named: &dyn Fn(&str) -> bool) -> bool {
    match t {
        RType::Named(n) => named(n),
        RType::Seq(e, _) | RType::Option(e) => needs_eq_with(e, named),
        RType::Result(a, b) => needs_eq_with(a, named) || needs_eq_with(b, named),
        RType::Map(_, v) => needs_eq_with(v, named),
        _ => false,
    }
}

/// `a` and `b`, two terms of the view type of `t`, equal: `a == b`, unless
/// `t` holds a user type with sequence fields (`needs`), when it is that
/// type's `djinn_eq_T(a, b)`, and through `Option`, `Result`, `Seq` and `Map`
/// the vocabulary's `opt_eq`, `res_eq`, `seq_eq` (length and pointwise) and
/// `map_eq` with the element comparison as a closure.
pub fn eq_term(a: &str, b: &str, t: &RType, names: &TypeNames, needs: &dyn Fn(&RType) -> bool) -> String {
    if !needs(t) {
        return format!("{a} == {b}");
    }
    let closure = |e: &RType| {
        let vt = view_type(e, names);
        format!("|{RESERVED}_x: {vt}, {RESERVED}_y: {vt}| {}", eq_term(&format!("{RESERVED}_x"), &format!("{RESERVED}_y"), e, names, needs))
    };
    match t {
        RType::Named(n) => format!("{}({a}, {b})", eq_fn_name(n)),
        RType::Option(e) => format!("crate::vocab::opt_eq({a}, {b}, {})", closure(e)),
        RType::Result(x, y) => format!("crate::vocab::res_eq({a}, {b}, {}, {})", closure(x), closure(y)),
        RType::Seq(e, _) => format!("crate::vocab::seq_eq({a}, {b}, {})", closure(e)),
        RType::Map(_, v) => format!("crate::vocab::map_eq({a}, {b}, {})", closure(v)),
        _ => format!("{a} == {b}"),
    }
}

/// Does the structural equality of `n` call itself (a type recursive through
/// a field that needs structural comparison)?
fn eq_recursive(n: &str, t: &RType, types: &TypeDefs, seen: &mut Vec<String>) -> bool {
    match t {
        RType::Named(m) => {
            if m == n {
                return true;
            }
            if seen.contains(m) || !needs_eq(t, types) {
                return false;
            }
            seen.push(m.clone());
            fields_of(m, types).into_iter().any(|ft| eq_recursive(n, ft, types, seen))
        }
        RType::Seq(e, _) | RType::Option(e) => eq_recursive(n, e, types, seen),
        RType::Result(a, b) => eq_recursive(n, a, types, seen) || eq_recursive(n, b, types, seen),
        RType::Map(_, v) => eq_recursive(n, v, types, seen),
        _ => false,
    }
}

/// The structural equality of the user type `n` (one that `needs_eq`), for
/// `relations.rs`: `pub open spec fn djinn_eq_T(a: T, b: T) -> bool`, the
/// fields compared through their views (`eq_term`); an enum by `match (a,
/// b)` over the variant pairs with a `_ => false` arm. A type recursive
/// through such a field is refused: its function would need a termination
/// measure Verus cannot see through a `Seq`.
pub fn eq_fn(n: &str, types: &TypeDefs, names: &TypeNames, span: proc_macro2::Span) -> Result<String> {
    let path = names.get(n).cloned().unwrap_or_else(|| n.to_string());
    let needs = |t: &RType| needs_eq(t, types);
    if fields_of(n, types).into_iter().any(|ft| eq_recursive(n, ft, types, &mut Vec::new())) {
        return Err(Error::new(span, format!("`{n}` holds a sequence and is recursive: the Verus backend cannot state the equality of two such values (it would need a termination measure through `Seq`); compare fields instead, or use the Lean backend")));
    }
    let field_eq = |a: &str, b: &str, ft: &RType| eq_term(&view_term(a, ft, names), &view_term(b, ft, names), ft, names, &needs);
    let body = if let Some(s) = types.structs.get(n) {
        conj(s.fields.iter().map(|(f, ft)| field_eq(&format!("a.{}", verus_ident(f)), &format!("b.{}", verus_ident(f)), ft)).collect())
    } else if let Some(e) = types.enums.get(n) {
        let mut arms = Vec::new();
        for v in &e.variants {
            let named = v.fields.iter().any(|(f, _)| f.is_some());
            let pat = |side: &str| -> String {
                if v.fields.is_empty() {
                    format!("{path}::{}", v.name)
                } else if named {
                    format!("{path}::{} {{ {} }}", v.name, v.fields.iter().enumerate().map(|(k, (f, _))| format!("{}: {RESERVED}_{side}{k}", verus_ident(f.as_deref().unwrap_or("")))).collect::<Vec<_>>().join(", "))
                } else {
                    format!("{path}::{}({})", v.name, (0..v.fields.len()).map(|k| format!("{RESERVED}_{side}{k}")).collect::<Vec<_>>().join(", "))
                }
            };
            let eqs: Vec<String> = v.fields.iter().enumerate().map(|(k, (_, ft))| field_eq(&format!("{RESERVED}_a{k}"), &format!("{RESERVED}_b{k}"), ft)).collect();
            arms.push(format!("({}, {}) => {}", pat("a"), pat("b"), conj(eqs)));
        }
        if e.variants.len() > 1 {
            arms.push("_ => false".into());
        }
        if arms.is_empty() {
            "true".to_string()
        } else {
            format!("match (a, b) {{\n        {},\n    }}", arms.join(",\n        "))
        }
    } else {
        return Err(Error::new(span, format!("`{n}` is not a struct or enum declared in the specification file")));
    };
    Ok(format!(
        "/// Two `{n}`s with the same contents: the fields compared through their views (a\n/// `Vec` or `String` field as its sequence), as the specification compares them; Verus's\n/// `==` on the Rust values would be unprovable from the relations.\npub open spec fn {}(a: {path}, b: {path}) -> bool {{\n    {body}\n}}\n",
        eq_fn_name(n)
    ))
}

/// The view of an implementation-typed term: `v@`, `v@.map_values(|y| y@)`,
/// a `match` for `Option`s and `Result`s of sequences; the term itself
/// where the view is the value.
pub fn view_term(term: &str, t: &RType, names: &TypeNames) -> String {
    match t {
        // a string is its UTF-8 bytes (vstd views it as its chars)
        RType::Seq(_, SeqKind::String) | RType::Seq(_, SeqKind::Str) => format!("crate::vocab::bytes({}@)", paren_term(term)),
        RType::Seq(e, _) if needs_view(e) => format!("{}@.map_values(|y: {}| {})", paren_term(term), exec_type(e, names), view_term("y", e, names)),
        RType::Seq(..) => format!("{}@", paren_term(term)),
        // a `HashMap` is vstd's `Map` view; the values in their views
        RType::Map(_, v) if needs_view(v) => format!("{}@.map_values(|y: {}| {})", paren_term(term), exec_type(v, names), view_term("y", v, names)),
        RType::Map(..) => format!("{}@", paren_term(term)),
        RType::Option(e) if needs_view(e) => format!("(match {term} {{ Option::Some(y) => Option::Some({}), Option::None => Option::None }})", view_term("y", e, names)),
        RType::Result(a, b) if needs_view(a) || needs_view(b) => format!("(match {term} {{ Result::Ok(y) => Result::Ok({}), Result::Err(y) => Result::Err({}) }})", view_term("y", a, names), view_term("y", b, names)),
        _ => term.to_string(),
    }
}

fn paren_term(t: &str) -> String {
    paren_literal(t)
}

fn paren(t: &str) -> String {
    paren_term(t)
}

pub(crate) fn conj(ps: Vec<String>) -> String {
    match ps.len() {
        0 => "true".into(),
        1 => ps.into_iter().next().unwrap(),
        _ => format!("({})", ps.join(" && ")),
    }
}

/// `(t as int)` for a machine-integer term.
fn as_int(t: &str) -> String {
    format!("({} as int)", paren_literal(t))
}

/// A term ready to take `as` or `.`: one with no operator at its top level
/// (no space outside brackets, no leading sign) as it is, anything else in
/// parentheses.
fn paren_literal(t: &str) -> String {
    if !top_level_space(t) && !t.starts_with('-') {
        t.to_string()
    } else {
        format!("({t})")
    }
}

/// Is there a space outside every bracket of `t`?
fn top_level_space(t: &str) -> bool {
    let mut depth = 0i32;
    for c in t.chars() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ' ' if depth == 0 => return true,
            _ => {}
        }
    }
    false
}

fn is_literal(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_ascii_digit())
}

/// A Verus `char` literal.
pub(crate) fn char_lit(c: char) -> String {
    match c {
        '\'' => "'\\''".into(),
        '\\' => "'\\\\'".into(),
        '\n' => "'\\n'".into(),
        '\t' => "'\\t'".into(),
        '\r' => "'\\r'".into(),
        c if c.is_ascii_graphic() || c == ' ' => format!("'{c}'"),
        c => format!("'\\u{{{:x}}}'", c as u32),
    }
}

/// A `Seq<u8>` literal for a byte string.
pub(crate) fn bytes_lit(b: &[u8]) -> String {
    if b.is_empty() {
        "Seq::<u8>::empty()".into()
    } else {
        format!("seq![{}]", b.iter().map(|x| format!("{x}u8")).collect::<Vec<_>>().join(", "))
    }
}

fn scalar_suffix(signed: bool, bits: u32) -> String {
    format!("{}{}", if signed { "i" } else { "u" }, if bits == 0 { "size".to_string() } else { bits.to_string() })
}

// ------------------------------------------------------------- triggers

/// A quantifier, `(forall|x: T, …| #![trigger …] body)`, with its triggers
/// chosen here rather than left to Verus: Verus refuses a quantifier it
/// cannot infer triggers for (nested quantifiers, a term beside the same
/// term shifted by one, …), and a trusted file that does not elaborate
/// would block the implementer. For each variable, the first application
/// term of the body (`f(…)`, `s.m(…)`, `s[…]`) that mentions it and no
/// variable bound inside the body — without arithmetic if there is one —
/// else `crate::vocab::trig(x)` (always true; the guide says how to
/// instantiate such a quantifier: `assert(trig(i0))`).
pub fn quant(kind: &str, binders: &[(String, String)], body: &str, extra_inner: &[String]) -> String {
    quant_excluding(kind, binders, body, extra_inner, &[])
}

/// `quant`, with applications of the functions named in `exclude` never
/// chosen as triggers. Inside a recursive `spec fn`, Verus encodes the
/// function's own calls with a fuel argument, so a trigger on such a call can
/// never be matched by a term a proof writes: an existential whose only
/// trigger is the recursive call could never be witnessed.
pub fn quant_excluding(kind: &str, binders: &[(String, String)], body: &str, extra_inner: &[String], exclude: &[String]) -> String {
    let bs: Vec<String> = binders.iter().map(|(n, t)| format!("{n}: {t}")).collect();
    let mut inner = inner_binders(body);
    inner.extend(extra_inner.iter().cloned());
    let mut triggers: Vec<String> = Vec::new();
    let mut fallback: Vec<String> = Vec::new();
    for (n, _) in binders {
        if triggers.iter().any(|t| mentions_var(t, n)) {
            continue;
        }
        match find_trigger_excluding(body, n, &inner, exclude) {
            Some(t) => triggers.push(t),
            None => {
                triggers.push(format!("crate::vocab::trig({n})"));
                fallback.push(format!("crate::vocab::trig({n})"));
            }
        }
    }
    // the fallback trigger is also a conjunct of the body: so a proof of the
    // same statement (the pinned wrapper from the implementer's lemma) has the
    // term `trig(x)` at hand and the quantifier instantiates
    let body = if fallback.is_empty() {
        body.to_string()
    } else if kind == "forall" {
        format!("{} ==> ({body})", fallback.join(" && "))
    } else {
        format!("{} && ({body})", fallback.join(" && "))
    };
    format!("({kind}|{}| #![trigger {}] {body})", bs.join(", "), triggers.join(", "))
}

/// Does `text` mention the variable `x`: an identifier token `x` that is not
/// a path segment (`a::x`, `x::b`), a field or method (`.x`), or a call (`x(`)?
fn mentions_var(text: &str, x: &str) -> bool {
    // by characters, not bytes: an identifier may be non-ASCII (`α`)
    let mut it = text.char_indices().peekable();
    while let Some((start, c)) = it.next() {
        if !is_ident_char(c) {
            continue;
        }
        let mut end = start + c.len_utf8();
        while let Some(&(j, d)) = it.peek() {
            if !is_ident_char(d) {
                break;
            }
            end = j + d.len_utf8();
            it.next();
        }
        if &text[start..end] == x {
            let before = text[..start].trim_end();
            let after = text[end..].trim_start();
            let segment = before.ends_with('.') || before.ends_with("::") || after.starts_with("::");
            let call = after.starts_with('(');
            if !segment && !call {
                return true;
            }
        }
    }
    false
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// The identifiers of a text.
fn idents(s: &str) -> Vec<&str> {
    s.split(|c: char| !is_ident_char(c)).filter(|w| !w.is_empty() && !w.starts_with(|c: char| c.is_ascii_digit())).collect()
}

/// The variables bound inside a body: by `forall|…|`, `exists|…|` and
/// closures `|y: T|` (every `|x:` and `, x:` — struct patterns' field names
/// are swept up too, which only costs a natural trigger, never soundness).
fn inner_binders(body: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (i, c) in body.char_indices() {
        if c != '|' && c != ',' {
            continue;
        }
        let rest = body[i + 1..].trim_start_matches(' ');
        let len: usize = rest.chars().take_while(|d| is_ident_char(*d)).map(|d| d.len_utf8()).sum();
        if len == 0 || rest.starts_with(|d: char| d.is_ascii_digit()) {
            continue;
        }
        let after = rest[len..].trim_start_matches(' ');
        if after.starts_with(':') && !after.starts_with("::") {
            out.push(rest[..len].to_string());
        }
    }
    out
}

/// A term of `body` to trigger on for `x`: an application (`f(…)`, `s.m(…)`,
/// `s[…]`) that mentions `x` and none of `inner`; one without arithmetic if
/// there is one (Z3 matches those reliably), else the first.
/// The spans of the quantifiers nested in `body` (`(exists|…| …)`,
/// `(forall|…| …)`): a term inside one is no trigger for an outer variable.
/// When Verus negates a goal `forall|k| …`, the Skolem `k` is ground only in
/// the terms outside the inner quantifiers; a trigger occurring solely inside
/// one (`lens[k]` in `exists|v| f_spec(k, v) && v == lens[k]`) never matches,
/// and the outer quantifier can neither be instantiated nor established.
fn inner_quantifier_spans(body: &str) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    for kw in ["exists|", "forall|"] {
        let mut from = 0;
        while let Some(off) = body[from..].find(kw) {
            let p = from + off;
            let (open, close) = if p > 0 && body.as_bytes()[p - 1] == b'(' { (p - 1, close_of(body, p - 1).unwrap_or(body.len() - 1)) } else { (p, body.len() - 1) };
            spans.push((open, close));
            from = p + kw.len();
        }
    }
    spans
}

fn find_trigger_excluding(body: &str, x: &str, inner: &[String], exclude: &[String]) -> Option<String> {
    let mut with_arith: Option<String> = None;
    let b = body.as_bytes();
    let nested = inner_quantifier_spans(body);
    for (i, &c) in b.iter().enumerate() {
        if c != b'(' && c != b'[' {
            continue;
        }
        if nested.iter().any(|(o, cl)| i > *o && i <= *cl) {
            continue;
        }
        // an application: the bracket follows an identifier, `)`, `]` or `@`
        if i == 0 {
            continue;
        }
        let prev = b[i - 1] as char;
        if !(is_ident_char(prev) || prev == ')' || prev == ']' || prev == '@') {
            continue;
        }
        let Some(end) = close_of(body, i) else { continue };
        // the receiver: a postfix chain of identifiers, `::`, `.`, `@` and groups
        let mut start = i;
        loop {
            let before = &body[..start];
            if let Some(stripped) = before.strip_suffix('@') {
                start = stripped.len();
                continue;
            }
            if before.ends_with(')') || before.ends_with(']') {
                match open_of(body, start - 1) {
                    Some(o) => {
                        start = o;
                        continue;
                    }
                    None => break,
                }
            }
            if before.ends_with('!') {
                // a macro invocation (`seq![…]`): part of the receiver
                let t = before[..before.len() - 1].trim_end_matches(is_ident_char);
                start = t.len();
                break;
            }
            let trimmed = before.trim_end_matches(is_ident_char);
            if trimmed.len() < before.len() {
                start = trimmed.len();
                if trimmed.ends_with("::") {
                    start -= 2;
                    continue;
                }
                if trimmed.ends_with('.') && !trimmed.ends_with("..") {
                    start -= 1;
                    continue;
                }
            }
            break;
        }
        let cand = &body[start..=end];
        let recv = &body[start..i];
        // a keyword, a macro (`seq!`), a constructor or a closure is no trigger
        let last = recv.rsplit(|c: char| c == ':' || c == '.' || c == '@' || c == ')' || c == ']').next().unwrap_or(recv);
        if recv.is_empty() || ["if", "match", "forall", "exists", "while", "return"].contains(&last) || last.starts_with(|c: char| c.is_ascii_uppercase()) || cand.contains('|') || cand.contains("seq![") || cand.starts_with('[') {
            continue;
        }
        // a recursive call of the function being defined (see `quant_excluding`)
        if exclude.iter().any(|f| f == last) {
            continue;
        }
        let ids = idents(cand);
        if !mentions_var(cand, x) || ids.iter().any(|w| inner.iter().any(|n| n == w)) {
            continue;
        }
        if has_arith(cand) {
            if with_arith.is_none() {
                with_arith = Some(cand.to_string());
            }
            continue;
        }
        return Some(cand.to_string());
    }
    with_arith
}

/// Is there a term of `body` to trigger on for `x` without arithmetic?
#[cfg(test)]
fn has_trigger(body: &str, x: &str, inner: &[String]) -> bool {
    find_trigger_excluding(body, x, inner, &[]).is_some_and(|t| !has_arith(&t))
}

fn has_arith(s: &str) -> bool {
    let b = s.as_bytes();
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'+' | b'*' | b'/' | b'%' => return true,
            b'-' if !(i + 1 < b.len() && b[i + 1] == b'>') => return true,
            _ => {}
        }
    }
    false
}

/// The index of the bracket closing the one at `open`.
fn close_of(s: &str, open: usize) -> Option<usize> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    for (j, &c) in b.iter().enumerate().skip(open) {
        match c {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(j);
                }
            }
            _ => {}
        }
    }
    None
}

/// The index of the bracket opening the one closing at `close`.
fn open_of(s: &str, close: usize) -> Option<usize> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    for j in (0..=close).rev() {
        match b[j] {
            b')' | b']' | b'}' => depth += 1,
            b'(' | b'[' | b'{' => {
                depth -= 1;
                if depth == 0 {
                    return Some(j);
                }
            }
            _ => {}
        }
    }
    None
}

#[derive(Clone)]
enum Cx {
    Forall(String, String),
    ForallRange(String, String, String),
    Guard(String),
    /// scrutinee, this arm's pattern, the patterns of the arms before it,
    /// and the number of variants of the enum
    MatchArm(String, String, Vec<String>, usize),
}

/// What the lowering needs to know about something a constraint may call.
#[derive(Clone)]
enum Callee {
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

/// The lowering environment of one declaration (see `lower::L`).
struct L<'a> {
    decls: &'a HashMap<String, DeclInfo>,
    types: &'a TypeDefs,
    names: &'a TypeNames,
    /// variable → (Verus term, type)
    env: HashMap<String, (String, SType)>,
    pre_scope: bool,
    muts: Vec<String>,
    cx: Vec<Cx>,
    guards: Vec<String>,
    wf: Vec<String>,
    fresh: usize,
    recursive: Option<String>,
    has_choices: bool,
    input_names: Vec<String>,
    input_tys: Vec<String>,
    /// The `for` variables in scope: Verus name and type.
    binders: Vec<(String, String)>,
    choices: Vec<(String, String)>,
    any_scope: Vec<String>,
    uses_types: bool,
    ambient_calls: Vec<String>,
    tables: Vec<(String, RType, Vec<String>)>,
    seen_types: Vec<RType>,
    user_names: std::collections::HashSet<String>,
    pattern_names: Vec<String>,
    /// The spec fns of the declaration being lowered, when it is recursive
    /// (`f_spec`, `f_body`): never triggers (`quant_excluding`).
    self_calls: Vec<String>,
}

/// Does a type have a view the Verus backend can state?
fn supported_type(t: &RType, what: &str, span: proc_macro2::Span) -> Result<()> {
    match t {
        // vstd states `HashMap::get`/`insert`/… only for keys it knows obey the
        // hash-table contract (`obeys_key_model`): the primitive integers and
        // `bool`. A `char`, `String` or user type as key would leave the
        // implementer no way to reason about the map.
        RType::Map(k, v) => match &**k {
            RType::Int { .. } | RType::Bool => supported_type(v, what, span),
            _ => Err(Error::new(span, format!("{what}: a `HashMap` key of type `{}` is not supported by the Verus backend (vstd specifies `HashMap` operations for integer and `bool` keys only)", crate::types::rust_type(k)))),
        },
        RType::Seq(e, _) | RType::Option(e) => supported_type(e, what, span),
        RType::Result(a, b) => supported_type(a, what, span).and_then(|_| supported_type(b, what, span)),
        _ => Ok(()),
    }
}

pub fn lower_with(d: &Decl, decls: &HashMap<String, DeclInfo>, types: &TypeDefs, names: &TypeNames) -> Result<Lowered> {
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
    // the names the lowering makes up hold `djinn`: no name of the source may
    for n in d.names() {
        if n.to_lowercase().contains(RESERVED) {
            return Err(Error::new(d.name_span, format!("`{n}`: names containing `djinn` are reserved for the generated code (Verus backend)")));
        }
    }
    // (a declaration named like a Verus keyword — `spec`, `open`, `has` — is
    // fine: `verus! { }` accepts them as function names, and the names formed
    // from it, `spec_pre`, `spec_spec`, `spec_wf_post`, are plain identifiers;
    // only a *parameter* so named needs `verus_ident`'s `r#`)
    for (n, t) in d.inputs().iter().chain(d.outputs().iter()) {
        supported_type(t, &format!("`{n}`"), d.name_span)?;
    }
    for c in d.choices() {
        supported_type(&c.ty, &format!("`any {}`", c.name), d.name_span)?;
    }
    let mut env = HashMap::new();
    for (n, t) in d.inputs() {
        env.insert(n.clone(), (verus_ident(&n), SType::Of(t)));
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
        input_names: d.inputs().into_iter().map(|(n, _)| verus_ident(&n)).collect(),
        input_tys: d.inputs().iter().map(|(_, t)| view_type(t, names)).collect(),
        binders: Vec::new(),
        choices: Vec::new(),
        any_scope: Vec::new(),
        uses_types: d.params.iter().any(|p| p.ty.needs_code_types()) || d.ret.as_ref().map(|(_, t)| t.needs_code_types()).unwrap_or(false) || d.choices().iter().any(|c| c.ty.needs_code_types()),
        ambient_calls: Vec::new(),
        tables: Vec::new(),
        seen_types: Vec::new(),
        user_names: d.names().into_iter().flat_map(|n| [verus_ident(&n), n]).collect(),
        pattern_names: Vec::new(),
        self_calls: if d.is_recursive() { vec![format!("{}_spec", d.name), format!("{}_body", d.name)] } else { Vec::new() },
    };
    let mut pre = Vec::new();
    for (n, t) in d.inputs() {
        pre.extend(implicit_facts(&verus_ident(&n), &t, true, types, &mut Vec::new(), 0, d.name_span, names)?);
    }
    for e in &d.requires {
        pre.push(l.constraint(e)?);
    }
    let mut decreases = Vec::new();
    for e in &d.decreases {
        decreases.push(l.num(e)?);
    }
    l.guards.clear();
    l.pre_scope = false;
    for (n, t) in d.outputs() {
        l.env.insert(n.clone(), (verus_ident(&n), SType::Of(t)));
    }
    let mut spec = Vec::new();
    for (n, t) in d.outputs() {
        if let RType::Seq(_, SeqKind::Array(len)) = &t {
            spec.push(format!("({}.len() as int) == {}", verus_ident(&n), array_len(len, types, d.name_span)?));
        }
    }
    for s in &d.body {
        spec.push(l.stmt(s)?);
    }
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
    let mut wf = l.wf;
    if l.has_choices {
        let all: String = l.choices.iter().map(|(n, _)| format!(", {n}")).collect();
        let fill = |x: &mut String| *x = x.replace(SELF_CHOICES, &all);
        pre.iter_mut().chain(spec.iter_mut()).chain(ensures.iter_mut()).chain(wf.iter_mut()).chain(decreases.iter_mut()).for_each(fill);
    }
    // the structural equalities of the user types the declaration may compare
    // (every type in reach of its signature and body), each after the types
    // its fields hold; the emitter defines each once
    let mut helpers = Vec::new();
    for n in &named_types {
        if needs_eq(&RType::Named(n.clone()), types) {
            helpers.push((eq_fn_name(n), eq_fn(n, types, names, d.name_span)?));
        }
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
        helpers,
    })
}

/// What Rust guarantees of a value of type `t` and its view does not say
/// (the same facts as the Lean backend's `implicit_facts`, for every
/// declaration, `rel`s included): a `String` is the UTF-8 encoding of some
/// character sequence and holds at most `usize::MAX` bytes, a `HashMap` at
/// most `usize::MAX` entries, an array `[T; N]` exactly `N` elements; and so
/// for the elements of a sequence, the contents of an `Option` and the
/// fields of a struct. A `&str` gets nothing (as in the Lean backend).
#[allow(clippy::too_many_arguments)]
fn implicit_facts(term: &str, t: &RType, view: bool, types: &TypeDefs, stack: &mut Vec<String>, depth: usize, span: proc_macro2::Span, names: &TypeNames) -> Result<Vec<String>> {
    let mut out = Vec::new();
    let y = format!("djinn_e{depth}");
    match t {
        RType::Seq(_, SeqKind::Str) => {}
        // a `String`'s view is the UTF-8 encoding of some character sequence,
        // at most `usize::MAX` bytes
        RType::Seq(_, SeqKind::String) if view => {
            out.push(format!("({term}.len() as int) <= (usize::MAX as int)"));
            let cs = format!("djinn_cs{depth}");
            out.push(quant("exists", &[(cs.clone(), "Seq<char>".into())], &format!("crate::vocab::bytes({cs}) == {term}"), &[]));
        }
        RType::Seq(_, SeqKind::String) => out.push(format!("(crate::vocab::bytes({}@).len() as int) <= (usize::MAX as int)", paren_term(term))),
        // a `HashMap` holds at most `usize::MAX` entries (its `Map` view is
        // finite by construction in vstd)
        RType::Map(..) if view => out.push(format!("({term}.dom().len() as int) <= (usize::MAX as int)")),
        RType::Map(..) => out.push(format!("({}@.dom().len() as int) <= (usize::MAX as int)", paren_term(term))),
        RType::Seq(e, kind) => {
            if let (SeqKind::Array(len), true) = (kind, view) {
                out.push(format!("({term}.len() as int) == {}", array_len(len, types, span)?));
            }
            let inner = implicit_facts(&y, e, view, types, stack, depth + 1, span, names)?;
            if !inner.is_empty() {
                let elems = if view { term.to_string() } else { format!("{term}@") };
                out.push(quant("forall", &[(y.clone(), if view { view_type(e, names) } else { exec_type(e, names) })], &format!("{elems}.contains({y}) ==> {}", conj(inner)), &[]));
            }
        }
        RType::Option(e) => {
            let inner = implicit_facts(&y, e, view, types, stack, depth + 1, span, names)?;
            if !inner.is_empty() {
                out.push(quant("forall", &[(y.clone(), if view { view_type(e, names) } else { exec_type(e, names) })], &format!("{term} == Option::Some({y}) ==> {}", conj(inner)), &[]));
            }
        }
        RType::Named(n) if !stack.contains(n) => {
            if let Some(sd) = types.structs.get(n) {
                stack.push(n.clone());
                for (f, ft) in &sd.fields {
                    out.extend(implicit_facts(&format!("{term}.{}", verus_ident(f)), ft, false, types, stack, depth, span, names)?);
                }
                stack.pop();
            }
        }
        _ => {}
    }
    Ok(out)
}

fn has_implicit_facts(t: &RType, types: &TypeDefs) -> bool {
    implicit_facts("x", t, true, types, &mut Vec::new(), 0, proc_macro2::Span::call_site(), &TypeNames::new()).map(|f| !f.is_empty()).unwrap_or(true)
}

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

fn stype_verus(t: &SType, names: &TypeNames) -> String {
    match t {
        SType::Int => "int".into(),
        SType::Of(t) => view_type(t, names),
    }
}

impl<'a> L<'a> {
    /// A quantifier of this declaration (see `quant`): the pattern binders
    /// made so far count as bound inside.
    fn quant(&self, kind: &str, binders: &[(String, String)], body: &str) -> String {
        quant_excluding(kind, binders, body, &self.pattern_names, &self.self_calls)
    }

    fn callee(&self, f: &str) -> Option<Callee> {
        if let Some(i) = self.decls.get(f) {
            return Some(Callee::Decl(i.clone()));
        }
        self.types.ambient.get(f).map(|a| Callee::Ambient(a.clone()))
    }

    /// A made-up name, `base` unless the source uses it (then suffixed with
    /// the reserved marker until it is none of the source's).
    fn avoid(&self, base: String) -> String {
        let mut n = base;
        let mut k = 1;
        while self.user_names.contains(&n) {
            n = format!("{}_{RESERVED}{k}", n.trim_end_matches(|c: char| c.is_ascii_digit()).trim_end_matches(&format!("_{RESERVED}")));
            k += 1;
        }
        n
    }

    fn wrap(&self, p: String) -> String {
        let mut p = p;
        for c in self.cx.iter().rev() {
            p = match c {
                Cx::Forall(x, t) => self.quant("forall", &[(x.clone(), t.clone())], &p),
                Cx::ForallRange(i, lo, hi) => self.quant("forall", &[(i.clone(), "int".into())], &format!("{lo} <= {i} && {i} < {hi} ==> {p}")),
                Cx::Guard(g) => format!("({g} ==> {p})"),
                Cx::MatchArm(s, pat, prev, nvariants) => {
                    let before: String = prev.iter().map(|q| format!("{q} => true, ")).collect();
                    if pat == "_" {
                        format!("(match {s} {{ {before}_ => {p} }})")
                    } else if prev.len() + 1 < *nvariants {
                        format!("(match {s} {{ {before}{pat} => {p}, _ => true }})")
                    } else {
                        format!("(match {s} {{ {before}{pat} => {p} }})")
                    }
                }
            };
        }
        p
    }

    fn flush_guards(&mut self) {
        if !self.guards.is_empty() {
            let gs: Vec<String> = self.guards.drain(..).map(|g| format!("({g})")).collect();
            let p = gs.join(" && ");
            let w = self.wrap(p);
            self.wf.push(w);
        }
    }

    fn with_env<T>(&mut self, binds: &[(String, String, SType)], f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
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

    fn with_vars<T>(&mut self, binds: &[(String, SType)], f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let b: Vec<(String, String, SType)> = binds.iter().map(|(n, t)| (n.clone(), verus_ident(n), t.clone())).collect();
        self.with_env(&b, f)
    }

    /// The text a self-call contains.
    fn self_marker(&self, me: &str) -> String {
        if self.has_choices {
            format!("{me}_body(")
        } else {
            format!("{me}_spec(")
        }
    }

    /// `A && B`, written `A && (A ==> B)` when lowering a recursive
    /// declaration and `B` calls it (the termination check then sees `A`).
    fn conj_rec(&self, ps: Vec<String>) -> String {
        let Some(me) = &self.recursive else { return conj(ps) };
        let marker = self.self_marker(me);
        if ps.len() < 2 || !ps.iter().skip(1).any(|p| p.contains(&marker)) {
            return conj(ps);
        }
        let mut acc = ps[ps.len() - 1].clone();
        for p in ps[..ps.len() - 1].iter().rev() {
            acc = if acc.contains(&marker) && !p.contains(&marker) { format!("({p} && ({p} ==> {acc}))") } else { format!("({p} && {acc})") };
        }
        acc
    }

    fn calls_me(&self, p: &str) -> bool {
        self.recursive.as_ref().map(|me| p.contains(&self.self_marker(me))).unwrap_or(false)
    }

    fn stmts(&mut self, ss: &[Stmt]) -> Result<String> {
        let mut v = Vec::new();
        let mark = self.any_scope.len();
        for s in ss {
            v.push(self.stmt(s)?);
        }
        for n in self.any_scope.split_off(mark) {
            self.env.remove(&n);
        }
        Ok(self.conj_rec(v))
    }

    /// A fresh choice: a `spec_fn` of the inputs and of the binders in
    /// scope into `ty`, named after `name`; its Verus name and the term it
    /// stands for here (the function applied).
    fn new_choice(&mut self, name: &str, ty: &str) -> (String, String) {
        let mut vn = verus_ident(name);
        let mut k = 1;
        while self.choices.iter().any(|(n, _)| n == &vn) || self.input_names.contains(&vn) || self.pattern_names.contains(&vn) || (k > 1 && self.user_names.contains(&vn)) {
            vn = verus_ident(&format!("{name}_{k}"));
            k += 1;
        }
        let mut fun_ty: Vec<String> = self.input_tys.clone();
        fun_ty.extend(self.binders.iter().map(|(_, t)| t.clone()));
        self.choices.push((vn.clone(), format!("spec_fn({}) -> {ty}", fun_ty.join(", "))));
        let args: Vec<String> = self.input_names.iter().cloned().chain(self.binders.iter().map(|(n, _)| n.clone())).collect();
        let term = format!("{vn}({})", args.join(", "));
        (vn, term)
    }

    fn any_stmt(&mut self, name: &str, ty: &RType, wherec: &Expr) -> Result<String> {
        let (_, term) = self.new_choice(name, &view_type(ty, self.names));
        self.env.insert(name.to_string(), (term, SType::Of(ty.clone())));
        self.any_scope.push(name.to_string());
        self.constraint(wherec)
    }

    fn stmt(&mut self, s: &Stmt) -> Result<String> {
        let span = s.span;
        match &s.kind {
            StmtKind::Constraint(e) => self.constraint(e),
            StmtKind::ForIn { var, seq, body } => {
                if let Some((c, a, b)) = self.split_if(seq) {
                    let mk = |s: Expr| vec![Stmt { span, kind: StmtKind::ForIn { var: var.clone(), seq: s, body: body.clone() } }];
                    return self.split_stmt(&c, mk(a), mk(b), span);
                }
                let mut lifted = Vec::new();
                let seq2 = self.lift_calls(seq, &mut lifted)?;
                if !lifted.is_empty() {
                    let binds = lifted_binds(&lifted);
                    let s2 = Stmt { span, kind: StmtKind::ForIn { var: var.clone(), seq: seq2, body: body.clone() } };
                    return self.wrap_lifted(lifted, &binds, span, |l| l.stmt(&s2));
                }
                let (st, ty) = self.term(seq)?;
                let elem = match &ty {
                    SType::Of(RType::Seq(e, _)) => SType::Of((**e).clone()),
                    _ => return Err(Error::new(seq.span, format!("`for {var} in ..` needs a sequence"))),
                };
                self.flush_guards();
                let et = stype_verus(&elem, self.names);
                let v = verus_ident(var);
                self.cx.push(Cx::Forall(v.clone(), et.clone()));
                self.binders.push((v.clone(), et.clone()));
                let b = self.with_vars(&[(var.clone(), elem)], |l| l.stmts(body))?;
                self.binders.pop();
                self.cx.pop();
                Ok(self.quant("forall", &[(v.clone(), et.clone())], &format!("{st}.contains({v}) ==> {b}")))
            }
            StmtKind::ForRange { var, lo, hi, body } => {
                for (k, bound) in [lo, hi].into_iter().enumerate() {
                    if let Some((c, a, b)) = self.split_if(bound) {
                        let mk = |x: Expr| {
                            let (l2, h2) = if k == 0 { (x, hi.clone()) } else { (lo.clone(), x) };
                            vec![Stmt { span, kind: StmtKind::ForRange { var: var.clone(), lo: l2, hi: h2, body: body.clone() } }]
                        };
                        return self.split_stmt(&c, mk(a), mk(b), span);
                    }
                }
                let mut lifted = Vec::new();
                let lo2 = self.lift_calls(lo, &mut lifted)?;
                let hi2 = self.lift_calls(hi, &mut lifted)?;
                if !lifted.is_empty() {
                    let binds = lifted_binds(&lifted);
                    let s2 = Stmt { span, kind: StmtKind::ForRange { var: var.clone(), lo: lo2, hi: hi2, body: body.clone() } };
                    return self.wrap_lifted(lifted, &binds, span, |l| l.stmt(&s2));
                }
                let lo = self.num(lo)?;
                let hi = self.num(hi)?;
                self.flush_guards();
                let v = verus_ident(var);
                self.cx.push(Cx::ForallRange(v.clone(), lo.clone(), hi.clone()));
                self.binders.push((v.clone(), "int".into()));
                let b = self.with_vars(&[(var.clone(), SType::Int)], |l| l.stmts(body))?;
                self.binders.pop();
                self.cx.pop();
                Ok(self.quant("forall", &[(v.clone(), "int".into())], &format!("{lo} <= {v} && {v} < {hi} ==> {b}")))
            }
            StmtKind::Some { binders, body } => {
                self.seen_types.extend(binders.iter().map(|(_, t)| t.clone()));
                for (n, t) in binders {
                    supported_type(t, &format!("`some {n}`"), span)?;
                }
                let binds: Vec<(String, SType)> = binders.iter().map(|(n, t)| (n.clone(), SType::Of(t.clone()))).collect();
                let bs: Vec<(String, String)> = binders.iter().map(|(n, t)| (verus_ident(n), view_type(t, self.names))).collect();
                let saved = self.wf.len();
                let saved_choices = self.choices.len();
                let guard = self.with_vars(&binds, |l| l.stmts(body))?;
                self.wf.truncate(saved);
                self.choices.truncate(saved_choices);
                self.guards.clear();
                for (n, t) in &binds {
                    self.cx.push(Cx::Forall(verus_ident(n), stype_verus(t, self.names)));
                }
                self.cx.push(Cx::Guard(guard));
                let b = self.with_vars(&binds, |l| l.stmts(body))?;
                self.cx.pop();
                for _ in &binds {
                    self.cx.pop();
                }
                Ok(self.quant("exists", &bs, &b))
            }
            StmtKind::Any { name, ty, wherec } => self.any_stmt(name, ty, wherec),
            StmtKind::Cases(alts) => {
                let mut v = Vec::new();
                for a in alts {
                    v.push(self.stmt(a)?);
                }
                Ok(format!("({})", v.join(" || ")))
            }
            StmtKind::If { cond, then, els } => {
                let c = self.constraint_inner(cond)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(c.clone()));
                let t = self.stmts(then)?;
                self.cx.pop();
                match els {
                    None => Ok(format!("({c} ==> {t})")),
                    Some(e) => {
                        self.cx.push(Cx::Guard(format!("!({c})")));
                        let e = self.stmts(e)?;
                        self.cx.pop();
                        Ok(format!("(({c} ==> {t}) && (!({c}) ==> {e}))"))
                    }
                }
            }
            StmtKind::Implies(c, s) => {
                let c = self.constraint_inner(c)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(c.clone()));
                let b = self.stmt(s)?;
                self.cx.pop();
                Ok(format!("({c} ==> {b})"))
            }
            StmtKind::Match { scrutinee, arms } => self.match_stmt(scrutinee, arms, span),
        }
    }

    /// `match t { Enum::V(x) => … }` as a Verus `match`.
    fn match_stmt(&mut self, scrutinee: &Expr, arms: &[Arm], span: proc_macro2::Span) -> Result<String> {
        let (st, ty) = self.term(scrutinee)?;
        let builtin = matches!(&ty, SType::Of(RType::Option(_) | RType::Result(..)));
        let (ename, edef) = match &ty {
            SType::Of(RType::Named(n)) => {
                let d = self.types.enums.get(n).cloned().ok_or_else(|| Error::new(scrutinee.span, format!("`{n}` is not an enum declared in the specification file")))?;
                self.uses_types = true;
                (n.clone(), d)
            }
            SType::Of(RType::Option(inner)) => ("Option".to_string(), EnumDef { name: "Option".into(), variants: vec![VariantDef { name: "None".into(), fields: vec![] }, VariantDef { name: "Some".into(), fields: vec![(None, (**inner).clone())] }] }),
            SType::Of(RType::Result(a, b)) => ("Result".to_string(), EnumDef { name: "Result".into(), variants: vec![VariantDef { name: "Ok".into(), fields: vec![(None, (**a).clone())] }, VariantDef { name: "Err".into(), fields: vec![(None, (**b).clone())] }] }),
            _ => return Err(Error::new(scrutinee.span, "`match` needs a value of a user enum type, an `Option` or a `Result`")),
        };
        self.flush_guards();
        let path = if builtin { ename.clone() } else { self.names.get(&ename).cloned().unwrap_or(ename.clone()) };
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
                    lines.push(format!("_ => {b}"));
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
                    let mut vbinders: Vec<String> = Vec::new();
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
                    let named_fields = vdef.fields.iter().any(|(n, _)| n.is_some());
                    for (k, ((fname, fty), binder)) in vdef.fields.iter().zip(field_names.iter()).enumerate() {
                        match binder {
                            None => {
                                if !named_fields {
                                    vbinders.push("_".to_string());
                                }
                            }
                            Some(b) => {
                                let mut vn = verus_ident(&format!("{b}_{k}"));
                                while self.user_names.contains(&vn) || self.choices.iter().any(|(n, _)| n == &vn) {
                                    vn = format!("{vn}_{RESERVED}");
                                }
                                self.pattern_names.push(vn.clone());
                                vbinders.push(match fname {
                                    Some(f) => format!("{}: {vn}", verus_ident(f)),
                                    None => vn.clone(),
                                });
                                self.seen_types.push(fty.clone());
                                let term = if builtin { vn.clone() } else { view_term(&vn, fty, self.names) };
                                binds.push((b.clone(), term, SType::Of(fty.clone())));
                            }
                        }
                    }
                    let pat = if vdef.fields.is_empty() {
                        format!("{path}::{variant}")
                    } else if named_fields {
                        format!("{path}::{variant} {{ {}{} }}", vbinders.join(", "), if vbinders.len() < vdef.fields.len() { if vbinders.is_empty() { "..".to_string() } else { ", ..".to_string() } } else { String::new() })
                    } else {
                        format!("{path}::{variant}({})", vbinders.join(", "))
                    };
                    self.cx.push(Cx::MatchArm(st.clone(), pat.clone(), prev_pats.clone(), edef.variants.len()));
                    let b = self.with_env(&binds, |l| l.stmts(&a.body))?;
                    self.cx.pop();
                    prev_pats.push(pat.clone());
                    lines.push(format!("{pat} => {b}"));
                }
            }
        }
        if !has_wild {
            let missing: Vec<&str> = edef.variants.iter().map(|v| v.name.as_str()).filter(|v| !covered.iter().any(|c| c == v)).collect();
            if !missing.is_empty() {
                return Err(Error::new(span, format!("non-exhaustive `match` on `{ename}`: missing {}", missing.iter().map(|m| format!("`{ename}::{m}`")).collect::<Vec<_>>().join(", "))));
            }
        }
        Ok(format!("(match {st} {{ {} }})", lines.join(", ")))
    }

    fn constraint(&mut self, e: &Expr) -> Result<String> {
        let p = self.constraint_inner(e)?;
        self.flush_guards();
        Ok(p)
    }

    fn constraint_inner(&mut self, e: &Expr) -> Result<String> {
        if let Some((c, a, b)) = self.split_if(e) {
            let then = vec![Stmt { span: e.span, kind: StmtKind::Constraint(a) }];
            let els = vec![Stmt { span: e.span, kind: StmtKind::Constraint(b) }];
            return self.split_stmt(&c, then, els, e.span);
        }
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
        if let ExprKind::Call(f, args) = &e.kind {
            if let Some(info) = self.callee(f) {
                if info.outputs().len() == 1 && info.outputs()[0] == RType::Bool {
                    let t = Expr::new(e.span, ExprKind::Bool(true));
                    return self.call_eq(f, args, &t, e.span);
                }
            }
        }
        if let ExprKind::Bin(op @ (BinOp::Eq | BinOp::Ne), l, r) = &e.kind {
            if is_proplike(l) || is_proplike(r) {
                let (bside, pside) = if is_proplike(r) { (l, r) } else { (r, l) };
                let bp = self.constraint_inner(bside)?;
                self.flush_guards();
                let pp = self.constraint_inner(pside)?;
                self.flush_guards();
                let iff = format!("({bp} <==> {pp})");
                return Ok(if *op == BinOp::Eq { iff } else { format!("!{iff}") });
            }
        }
        if let ExprKind::Not(x) = &e.kind {
            let xp = self.constraint_inner(x)?;
            self.flush_guards();
            return Ok(format!("!({xp})"));
        }
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
                    (lp.clone(), format!("!({lp})"), false)
                }
            };
            self.flush_guards();
            self.cx.push(Cx::Guard(guard.clone()));
            let rp = self.constraint_inner(r)?;
            self.flush_guards();
            self.cx.pop();
            let rec = self.calls_me(&rp) && !self.calls_me(&lp);
            return Ok(if imp {
                format!("({lp} ==> {rp})")
            } else if *op == BinOp::And {
                if rec { format!("({lp} && ({lp} ==> {rp}))") } else { format!("({lp} && {rp})") }
            } else if rec {
                format!("({lp} || (!({lp}) ==> {rp}))")
            } else {
                format!("({lp} || {rp})")
            });
        }
        let mut lifted = Vec::new();
        let e2 = self.lift_calls(e, &mut lifted)?;
        if lifted.is_empty() {
            return self.prop(e);
        }
        let binds = lifted_binds(&lifted);
        self.wrap_lifted(lifted, &binds, e.span, |l| l.prop(&e2))
    }

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
            let vt = view_type(t, self.names);
            s = if self.calls_me(&s) && !self.calls_me(&call) { self.quant("exists", &[(v.clone(), vt)], &format!("{call} && ({call} ==> {s})")) } else { self.quant("exists", &[(v.clone(), vt)], &format!("{call} && {s}")) };
        }
        Ok(s)
    }

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
            let v = l.avoid(format!("v_out{}", l.fresh));
            l.fresh += 1;
            let eq = Expr::new(span, ExprKind::Bin(BinOp::Eq, Box::new(Expr::new(span, ExprKind::Var(v.clone()))), Box::new(nout.clone())));
            let (call, cmp) = l.with_vars(&[(v.clone(), SType::Of(out_ty.clone()))], |l| Ok((l.spec_app(&f, &nargs, &v, span)?, l.prop(&eq)?)))?;
            Ok(l.quant("exists", &[(v.clone(), view_type(&out_ty, l.names))], &format!("{call} && {cmp}")))
        })
    }

    /// `f_spec(a1, …, an, out)`, plus the call-site obligation `f_pre(a1, …)`.
    fn spec_app(&mut self, f: &str, args: &[Expr], out: &str, span: proc_macro2::Span) -> Result<String> {
        let info = self.callee(f).unwrap();
        let inputs = info.inputs();
        if args.len() != inputs.len() {
            return Err(Error::new(span, format!("`{f}` takes {} arguments, {} given", inputs.len(), args.len())));
        }
        let mut as_ = Vec::new();
        for (a, t) in args.iter().zip(&inputs) {
            as_.push(self.term_as(a, t)?);
        }
        let args_s = as_.join(", ");
        match info {
            Callee::Decl(info) => {
                if info.has_pre || info.inputs.iter().any(|t| has_implicit_facts(t, self.types)) {
                    self.guards.push(format!("{f}_pre({args_s})"));
                }
                let sep = if as_.is_empty() { "" } else { ", " };
                if self.recursive.as_deref() == Some(f) && self.has_choices {
                    return Ok(format!("{f}_body({args_s}{SELF_CHOICES}{sep}{out})"));
                }
                if info.weakly_specified {
                    if info.choices.is_empty() {
                        return Err(Error::new(span, format!("`{f}` is weakly specified and mutually recursive with this declaration; that is not supported")));
                    }
                    let mut lifted = Vec::new();
                    for (cn, ct) in info.choices.clone() {
                        let (_, term) = self.new_choice(&format!("{f}_{}", cn.trim_start_matches("r#")), &ct);
                        lifted.push(term);
                    }
                    return Ok(format!("{f}_body({args_s}{sep}{}, {out})", lifted.join(", ")));
                }
                Ok(format!("{f}_spec({args_s}{sep}{out})"))
            }
            // an ambient function: its translation to a `spec fn` in
            // `relations.rs` (`emit_verus::ambient_rs`), which Verus checks
            // against the function itself in the mirrored module
            Callee::Ambient(a) => {
                if !self.ambient_calls.iter().any(|x| x == f) {
                    self.ambient_calls.push(f.to_string());
                }
                Ok(self.eq_term(out, &format!("crate::relations::{}({args_s})", ambient_spec_name(f)), &a.ret))
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
            ExprKind::Call(f, _) => return Err(Error::new(span, crate::lower::undeclared_call(f, self.types.ambient_errors.get(f).map(|s| s.as_str())))),
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

    fn prop(&mut self, e: &Expr) -> Result<String> {
        let span = e.span;
        let err = |m: String| Err(Error::new(span, m));
        Ok(match &e.kind {
            ExprKind::Bool(true) => "true".into(),
            ExprKind::Bool(false) => "false".into(),
            ExprKind::Not(x) => format!("!({})", self.prop(x)?),
            ExprKind::Bin(BinOp::And, l, r) => format!("({} && {})", self.prop(l)?, self.prop(r)?),
            ExprKind::Bin(BinOp::Or, l, r) => format!("({} || {})", self.prop(l)?, self.prop(r)?),
            ExprKind::Bin(op, l, r) if matches!(op, BinOp::Eq | BinOp::Ne) && (is_proplike(l) || is_proplike(r)) => {
                let (bside, pside) = if is_proplike(r) { (l, r) } else { (r, l) };
                let bp = self.prop(bside)?;
                let pp = self.prop(pside)?;
                let iff = format!("({bp} <==> {pp})");
                if *op == BinOp::Eq { iff } else { format!("!{iff}") }
            }
            ExprKind::Bin(op, l, r) if op.is_cmp() => {
                let (lt, lty) = self.term(l)?;
                let (rt, rty) = self.term(r)?;
                // two values of a user type with sequence fields: the same
                // contents (`needs_eq`), not Verus's `==` on the Rust values
                if matches!(op, BinOp::Eq | BinOp::Ne) && stype_verus(&lty, self.names) == stype_verus(&rty, self.names) {
                    if let SType::Of(t) = &lty {
                        if needs_eq(t, self.types) {
                            let eq = self.eq_term(&lt, &rt, t);
                            return Ok(if *op == BinOp::Eq { eq } else { format!("!{eq}") });
                        }
                    }
                }
                let numeric = |t: &SType| matches!(t, SType::Int) || matches!(t, SType::Of(RType::Int { .. })) || matches!(t, SType::Of(RType::MathInt));
                let is_char = |t: &SType| matches!(t, SType::Of(RType::Char));
                let (ls, rs) = if matches!(op, BinOp::Eq | BinOp::Ne) && lty == rty && !matches!(lty, SType::Int) {
                    (lt, rt)
                } else if numeric(&lty) && numeric(&rty) {
                    (self.as_num(lt, &lty), self.as_num(rt, &rty))
                } else if is_char(&lty) && is_char(&rty) {
                    (format!("({lt} as int)"), format!("({rt} as int)"))
                } else if matches!(op, BinOp::Eq | BinOp::Ne) {
                    (lt, rt)
                } else {
                    return err("ordering comparison on non-numeric values".into());
                };
                let sym = match op {
                    BinOp::Eq => "==",
                    BinOp::Ne => "!=",
                    BinOp::Lt => "<",
                    BinOp::Le => "<=",
                    BinOp::Gt => ">",
                    BinOp::Ge => ">=",
                    _ => unreachable!(),
                };
                format!("{ls} {sym} {rs}")
            }
            ExprKind::In(x, s) => {
                let (st, sty) = self.term(s)?;
                let elem = match &sty {
                    SType::Of(RType::Seq(elem, _)) => elem.as_ref().clone(),
                    _ => return err("`in` needs a sequence on the right".into()),
                };
                let m = self.member(x, &elem)?;
                let sq = self.member_seq(x, &elem, &st)?;
                self.contains(&sq, &m, Some(&elem))
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
                let bs: Vec<(String, String)> = info.inputs.iter().zip(&as_).map(|(t, a)| (a.clone(), view_type(t, self.names))).collect();
                let sep = if as_.is_empty() { "" } else { ", " };
                if bs.is_empty() {
                    format!("{f}_spec({xt})")
                } else {
                    self.quant("exists", &bs, &format!("{f}_spec({}{sep}{xt})", as_.join(", ")))
                }
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
                let pre = if info.has_pre || info.inputs.iter().any(|t| has_implicit_facts(t, self.types)) { format!("{f}_pre({xt})") } else { "true".into() };
                if info.total {
                    pre
                } else {
                    let on: Vec<String> = (0..info.outputs.len()).map(|i| self.avoid(format!("o{i}"))).collect();
                    let os: Vec<(String, String)> = info.outputs.iter().zip(&on).map(|(t, o)| (o.clone(), view_type(t, self.names))).collect();
                    format!("({pre} && {})", self.quant("exists", &os, &format!("{f}_spec({xt}, {})", on.join(", "))))
                }
            }
            ExprKind::Method(m) => match &**m {
                Method::IsEmpty(s) => format!("({}.len() as int) == 0", self.listlike(s)?),
                Method::ContainsKey(m, k) => {
                    let (mt, kty, _) = self.map(m)?;
                    let kt = self.term_as(k, &kty)?;
                    format!("{}.dom().contains({kt})", paren(&mt))
                }
                Method::MapGet(..) => return err("`m.get(&k)` is a value (an `Option`): compare it, `r == m.get(&k)`".into()),
                Method::Contains(s, x) => {
                    let (st, et) = self.seq(s)?;
                    let (xt, sq) = match &et {
                        SType::Of(rt) => (self.member(x, &rt.clone())?, self.member_seq(x, &rt.clone(), &st)?),
                        _ => (self.term(x)?.0, st),
                    };
                    let elem = match &et {
                        SType::Of(rt) => Some(rt.clone()),
                        SType::Int => None,
                    };
                    self.contains(&sq, &xt, elem.as_ref())
                }
                Method::All { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    let tl = stype_verus(&et, self.names);
                    let (v, p) = self.under_elem(var, et, &st, pred)?;
                    self.quant("forall", &[(v.clone(), tl)], &format!("{st}.contains({v}) ==> {p}"))
                }
                Method::Any { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    let tl = stype_verus(&et, self.names);
                    let (v, p) = self.under_elem(var, et, &st, pred)?;
                    self.quant("exists", &[(v.clone(), tl)], &format!("{st}.contains({v}) && {p}"))
                }
                Method::Windows2All { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    let a = self.avoid(format!("{var}0"));
                    let b = self.avoid(format!("{var}1"));
                    let pred2 = subst_window(pred, var, &a, &b);
                    let tl = stype_verus(&et, self.names);
                    let binds = [(a.clone(), verus_ident(&a), et.clone()), (b.clone(), verus_ident(&b), et)];
                    let p = self.under_binders(&binds, &tl, &format!("crate::vocab::adjacent({st}, {}, {})", verus_ident(&a), verus_ident(&b)), &pred2)?;
                    self.quant("forall", &[(verus_ident(&a), tl.clone()), (verus_ident(&b), tl.clone())], &format!("crate::vocab::adjacent({st}, {}, {}) ==> {p}", verus_ident(&a), verus_ident(&b)))
                }
                Method::IsSome(o) => format!("{}.is_some()", paren(&self.term(o)?.0)),
                Method::IsNone(o) => format!("{}.is_none()", paren(&self.term(o)?.0)),
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

    fn under_elem(&mut self, var: &str, et: SType, st: &str, pred: &Expr) -> Result<(String, String)> {
        let v = verus_ident(var);
        let tl = stype_verus(&et, self.names);
        let p = self.under_binders(&[(var.to_string(), v.clone(), et)], &tl, &format!("{st}.contains({v})"), pred)?;
        Ok((v, p))
    }

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

    fn split_if(&self, e: &Expr) -> Option<(Expr, Expr, Expr)> {
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

    /// Is `x` a mathematical integer (not a literal) tested against a sequence
    /// of machine integers? Then membership is stated through the values.
    fn by_value(&mut self, x: &Expr, elem: &RType) -> Result<bool> {
        if !matches!(elem, RType::Int { .. }) {
            return Ok(false);
        }
        let saved = self.guards.len();
        let saved_wf = self.wf.len();
        let r = self.term(x);
        self.guards.truncate(saved);
        self.wf.truncate(saved_wf);
        let (xt, xty) = r?;
        let literal = is_literal(&xt);
        Ok(matches!(xty, SType::Int | SType::Of(RType::MathInt)) && (!literal || !fits(&xt, elem)))
    }

    fn member(&mut self, x: &Expr, elem: &RType) -> Result<String> {
        if self.by_value(x, elem)? {
            Ok(self.term(x)?.0)
        } else {
            self.term_as(x, elem)
        }
    }

    fn member_seq(&mut self, x: &Expr, elem: &RType, st: &str) -> Result<String> {
        if self.by_value(x, elem)? {
            Ok(format!("{st}.map_values(|y: {}| (y as int))", exec_type(elem, self.names)))
        } else {
            Ok(st.to_string())
        }
    }

    /// `sq.contains(x)` — or, for elements compared structurally (`needs_eq`),
    /// an index of `sq` whose element has the contents of `x`.
    fn contains(&self, sq: &str, x: &str, elem: Option<&RType>) -> String {
        match elem {
            Some(t) if needs_eq(t, self.types) => {
                let i = format!("{RESERVED}_i");
                let at = format!("{}[{i}]", paren(sq));
                format!("(exists|{i}: int| #![trigger {at}] 0 <= {i} && {i} < ({sq}.len() as int) && {})", self.eq_term(&at, x, t))
            }
            _ => format!("{sq}.contains({x})"),
        }
    }

    /// Two view terms of type `t` equal (`eq_term`).
    fn eq_term(&self, a: &str, b: &str, t: &RType) -> String {
        eq_term(a, b, t, self.names, &|t| needs_eq(t, self.types))
    }

    fn bool_prop(&self, t: String, ty: &SType, span: proc_macro2::Span) -> Result<String> {
        if *ty == SType::Of(RType::Bool) {
            Ok(format!("{t} == true"))
        } else {
            Err(Error::new(span, format!("`{t}` is not a boolean constraint")))
        }
    }

    // ------------------------------------------------------------------ terms

    fn as_num(&self, t: String, ty: &SType) -> String {
        match ty {
            SType::Int | SType::Of(RType::MathInt) => t,
            SType::Of(RType::Int { .. }) => as_int(&t),
            _ => t,
        }
    }

    fn num(&mut self, e: &Expr) -> Result<String> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt) => Ok(self.as_num(t, &ty)),
            _ => Err(Error::new(e.span, format!("`{t}` is not a number"))),
        }
    }

    /// A bit operation. `&`, `|`, `^` between unsigned machine integers of
    /// one type are Verus's own operators; otherwise the vocabulary's
    /// definitions on the natural numbers (Verus has no bitwise operations on
    /// `int`); a shift of any integer is `a * pow(2, n)` or the floor
    /// division `a / pow(2, n)`.
    fn bits(&mut self, e: &Expr) -> Result<String> {
        match &e.kind {
            ExprKind::Bin(op @ (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor), l, r) => {
                // between unsigned machine integers of one type: Verus's own
                // operator (the same number as the definition on the values,
                // `vocab::lemma_bit_and_u32` …); otherwise (mathematical
                // integers, mixed widths, signed operands — whose two's
                // complement bits the Lean backend does not read either) the
                // vocabulary's definition on the natural numbers, as Lean's
                // `&&&` on `ℕ`, with the operands' non-negativity as guards
                let saved = (self.guards.len(), self.wf.len());
                if let Ok((t, RType::Int { signed: false, .. })) = self.machine_bits(e) {
                    return Ok(format!("({t} as int)"));
                }
                self.guards.truncate(saved.0);
                self.wf.truncate(saved.1);
                let a = self.nat_operand(l)?;
                let b = self.nat_operand(r)?;
                let f = match op {
                    BinOp::BitAnd => "bit_and",
                    BinOp::BitOr => "bit_or",
                    _ => "bit_xor",
                };
                Ok(format!("(crate::vocab::{f}({a}, {b}) as int)"))
            }
            ExprKind::Bin(op @ (BinOp::Shl | BinOp::Shr), l, r) => {
                let a = self.num(l)?;
                let k = self.nat_operand(r)?;
                Ok(format!("({a} {} vstd::arithmetic::power::pow(2, {k}))", if *op == BinOp::Shl { "*" } else { "/" }))
            }
            _ => self.num(e),
        }
    }

    /// A chain of `&`, `|`, `^` as a term of one machine-integer type: its
    /// leaves are machine integers of that type, or literals that fit it.
    fn machine_bits(&mut self, e: &Expr) -> Result<(String, RType)> {
        let unsupported = |span| Error::new(span, "the Verus backend states `&`, `|`, `^` only between machine integers of one type (or one and a literal that fits it): cast both operands in Rust (`e as u32`) before the specification, or use `/` and `%`");
        match &e.kind {
            ExprKind::Bin(op @ (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor), l, r) => {
                let sym = match op {
                    BinOp::BitAnd => "&",
                    BinOp::BitOr => "|",
                    _ => "^",
                };
                let a = self.machine_leaf(l)?;
                let b = self.machine_leaf(r)?;
                let (a, b, ty) = match (a, b) {
                    ((a, Some(ta)), (b, Some(tb))) if ta == tb => (a, b, ta),
                    ((a, Some(ta)), (b, None)) if fits(&b, &ta) => {
                        let RType::Int { signed, bits } = &ta else { unreachable!() };
                        (a, format!("{b}{}", scalar_suffix(*signed, *bits)), ta)
                    }
                    ((a, None), (b, Some(tb))) if fits(&a, &tb) => {
                        let RType::Int { signed, bits } = &tb else { unreachable!() };
                        (format!("{a}{}", scalar_suffix(*signed, *bits)), b, tb)
                    }
                    _ => return Err(unsupported(e.span)),
                };
                Ok((format!("({a} {sym} {b})"), ty))
            }
            _ => Err(unsupported(e.span)),
        }
    }

    /// A leaf of a bit chain: a nested chain, a machine integer (with its
    /// type), or a literal (`None`).
    fn machine_leaf(&mut self, e: &Expr) -> Result<(String, Option<RType>)> {
        if matches!(&e.kind, ExprKind::Bin(BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor, _, _)) {
            let (t, ty) = self.machine_bits(e)?;
            return Ok((t, Some(ty)));
        }
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(rt @ RType::Int { .. }) => Ok((t, Some(rt))),
            SType::Int if is_literal(&t) => Ok((t, None)),
            _ => Err(Error::new(e.span, "the Verus backend states `&`, `|`, `^` only between machine integers of one type (or one and a literal that fits it): cast both operands in Rust (`e as u32`) before the specification, or use `/` and `%`")),
        }
    }

    /// An exponent or shift amount, as a `nat`: a literal as it stands, any
    /// other integer with a `0 <= n` well-formedness guard.
    fn nat_operand(&mut self, e: &Expr) -> Result<String> {
        let n = self.num(e)?;
        if is_literal(&n) {
            return Ok(n);
        }
        self.guards.push(format!("0 <= {n}"));
        Ok(format!("({n} as nat)"))
    }

    fn seq(&mut self, e: &Expr) -> Result<(String, SType)> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Seq(el, _)) => Ok((t, SType::Of(*el))),
            SType::Of(RType::Map(..)) => Err(Error::new(e.span, format!("`{t}` is a map: use `.get(&k)`, `.contains_key(&k)`, `.len()`, `.is_empty()`"))),
            _ => Err(Error::new(e.span, format!("`{t}` is not a sequence"))),
        }
    }

    /// A term with a `.len()`: a sequence, or a map's domain.
    fn listlike(&mut self, e: &Expr) -> Result<String> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Seq(..)) => Ok(t),
            SType::Of(RType::Map(..)) => Ok(format!("{}.dom()", paren(&t))),
            _ => Err(Error::new(e.span, format!("`{t}` is not a sequence or a map"))),
        }
    }

    /// A map term with its key and value types.
    fn map(&mut self, e: &Expr) -> Result<(String, RType, RType)> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Map(k, v)) => Ok((t, *k, *v)),
            _ => Err(Error::new(e.span, format!("`{t}` is not a map (`.get(&k)` and `.contains_key(&k)` apply to `HashMap`s; a sequence is indexed with `s[i]`)"))),
        }
    }

    /// The receiver of a method whose meaning depends on the width: a machine
    /// integer, or any integer cast to one (`e as u32`). Its value as an
    /// `int` term, its signedness, and its width as a `nat` term. A cast's
    /// value is the integer reduced to the width — `wrap_unsigned(v, w)`, or
    /// `wrap_signed(v, w)` for a signed target — as Rust's `as` and the Lean
    /// backend's `BitVec.ofInt` take it (the vocabulary's bit definitions
    /// assume a receiver within its width).
    fn machine_int(&mut self, e: &Expr, what: &str) -> Result<(String, bool, String)> {
        if let ExprKind::Cast(inner, RType::Int { signed, bits }) = &e.kind {
            let v = self.num(inner)?;
            let w = width_verus(*signed, *bits);
            let v = format!("crate::vocab::{}({v}, {w})", if *signed { "wrap_signed" } else { "wrap_unsigned" });
            return Ok((v, *signed, w));
        }
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Int { signed, bits }) => Ok((self.as_num(t, &ty), signed, width_verus(signed, bits))),
            _ => Err(Error::new(e.span, format!("{what} need a machine integer: a parameter, field or element of an integer type, or a cast (`e as u32`); `{t}` is a mathematical integer, which has no width"))),
        }
    }

    /// The two's complement bits of a machine integer's value, as a `nat`
    /// (the value itself when unsigned).
    fn twos(&mut self, e: &Expr, what: &str) -> Result<(String, bool, String)> {
        let (v, signed, w) = self.machine_int(e, what)?;
        let bits = if signed { format!("crate::vocab::twos({v}, {w})") } else { format!("({v} as nat)") };
        Ok((bits, signed, w))
    }

    fn term_as(&mut self, e: &Expr, t: &RType) -> Result<String> {
        let (s, ty) = self.term(e)?;
        match (&ty, t) {
            (SType::Of(RType::Seq(..)), RType::Seq(..)) => Ok(s),
            (SType::Int, RType::MathInt) | (SType::Of(RType::MathInt), RType::MathInt) => Ok(s),
            (SType::Of(RType::Int { .. }), RType::MathInt) => Ok(self.as_num(s, &ty)),
            (SType::Int, RType::Int { .. }) if is_literal(&s) && !fits(&s, t) => Err(Error::new(e.span, format!("`{s}` does not fit in `{}`", crate::types::rust_type(t)))),
            (SType::Int, RType::Int { signed, bits }) if is_literal(&s) => Ok(format!("{s}{}", scalar_suffix(*signed, *bits))),
            (SType::Int, RType::Int { .. }) => Err(Error::new(e.span, format!("`{s}`: a machine integer is expected, got a mathematical integer (declare the parameter as `int` in a `rel`)"))),
            _ => Ok(s),
        }
    }

    fn constant(&mut self, v: &str, span: proc_macro2::Span) -> Result<(String, SType)> {
        let c = self.types.consts.get(v).cloned().ok_or_else(|| {
            Error::new(span, format!("unknown constant `{v}`: constants used in specifications must be literal `const` items of the specification file: integers, booleans, chars, strings, or arrays of integer literals (`&[u32]`, `[i16; N]`)"))
        })?;
        if let Some(elems) = &c.table {
            if let RType::Seq(e, _) = &c.ty {
                if !self.tables.iter().any(|(n, _, _)| n == v) {
                    self.tables.push((v.to_string(), (**e).clone(), elems.clone()));
                }
            }
            // the mirrored specification module defines the Rust constant (an
            // array); the relation sees its view
            let path = self.names.get(&format!("const:{v}")).cloned().unwrap_or_else(|| v.to_string());
            return Ok((format!("{path}@"), SType::Of(c.ty)));
        }
        self.term(&c.value)
    }

    fn term(&mut self, e: &Expr) -> Result<(String, SType)> {
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
                    (SType::Of(RType::Char), RType::Int { .. }) => (format!("({t} as int)"), SType::Int),
                    (SType::Of(RType::Int { signed: false, bits: 8 }), RType::Char) => (format!("({t} as char)"), SType::Of(RType::Char)),
                    (SType::Int, RType::Char) => (format!("(({t} as u8) as char)"), SType::Of(RType::Char)),
                    _ => return err("unsupported cast: integers cast to integers (no overflow in the specification), `char as u32`, `u8 as char`".into()),
                }
            }
            ExprKind::Bin(op, _, _) if op.is_bits() => (self.bits(e)?, SType::Int),
            ExprKind::Bin(op, l, r) if op.is_arith() => {
                let a = self.num(l)?;
                let b = self.num(r)?;
                let sym = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => {
                        self.guards.push(format!("{b} != 0"));
                        "/"
                    }
                    BinOp::Rem => {
                        self.guards.push(format!("{b} != 0"));
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
                    ts.push(t);
                    tys.push(ty);
                }
                let inner = |tys: &[SType]| -> RType {
                    match tys.first() {
                        Some(SType::Of(t)) => t.clone(),
                        _ => RType::Named("_".into()),
                    }
                };
                match c.as_str() {
                    "None" => ("Option::None".into(), SType::Of(RType::Option(Box::new(RType::Named("_".into()))))),
                    "Some" => (format!("Option::Some({})", ts.join(", ")), SType::Of(RType::Option(Box::new(inner(&tys))))),
                    "Ok" => (format!("Result::Ok({})", ts.join(", ")), SType::Of(RType::Result(Box::new(inner(&tys)), Box::new(RType::Named("_".into()))))),
                    "Err" => (format!("Result::Err({})", ts.join(", ")), SType::Of(RType::Result(Box::new(RType::Named("_".into())), Box::new(inner(&tys))))),
                    _ => unreachable!(),
                }
            }
            ExprKind::Variant { enum_name, variant, fields } => {
                let edef = self.types.enums.get(enum_name).cloned().ok_or_else(|| Error::new(span, format!("`{enum_name}` is not an enum declared in the specification file")))?;
                let vdef = edef.variants.iter().find(|v| &v.name == variant).ok_or_else(|| Error::new(span, format!("`{enum_name}` has no variant `{variant}`")))?;
                self.uses_types = true;
                self.seen_types.push(RType::Named(enum_name.clone()));
                if fields.len() != vdef.fields.len() {
                    return err(format!("`{enum_name}::{variant}` has {} field(s), {} given", vdef.fields.len(), fields.len()));
                }
                let mut ordered: Vec<Option<&Expr>> = vec![None; vdef.fields.len()];
                for (k, (fname, fe)) in fields.iter().enumerate() {
                    let i = match fname {
                        None => k,
                        Some(f) => vdef.fields.iter().position(|(n, _)| n.as_deref() == Some(f.as_str())).ok_or_else(|| Error::new(fe.span, format!("`{enum_name}::{variant}` has no field `{f}`")))?,
                    };
                    ordered[i] = Some(fe);
                }
                let mut ts = Vec::new();
                for (fe, (fname, fty)) in ordered.iter().zip(&vdef.fields) {
                    let fe = fe.ok_or_else(|| Error::new(span, "a field is missing from the constructor expression"))?;
                    let v = self.exec_value(fe, fty)?;
                    ts.push(match fname {
                        Some(f) => format!("{}: {v}", verus_ident(f)),
                        None => v,
                    });
                }
                let path = self.names.get(enum_name).cloned().unwrap_or(enum_name.clone());
                let named = vdef.fields.iter().any(|(n, _)| n.is_some());
                let t = if ts.is_empty() {
                    format!("{path}::{variant}")
                } else if named {
                    format!("({path}::{variant} {{ {} }})", ts.join(", "))
                } else {
                    format!("({path}::{variant}({}))", ts.join(", "))
                };
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
                let base = paren(&t);
                (view_term(&format!("{base}.{}", verus_ident(f)), fty, self.names), SType::Of(fty.clone()))
            }
            ExprKind::Index(s, i) => {
                let (st, et) = self.seq(s)?;
                let (it, ity) = self.term(i)?;
                let (idx, guard) = match &ity {
                    SType::Of(RType::Int { signed: false, .. }) => {
                        let v = as_int(&it);
                        (v.clone(), format!("{v} < ({st}.len() as int)"))
                    }
                    SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt) => {
                        let n = self.as_num(it, &ity);
                        if is_literal(&n) {
                            (n.clone(), format!("{n} < ({st}.len() as int)"))
                        } else {
                            (n.clone(), format!("0 <= {n} && {n} < ({st}.len() as int)"))
                        }
                    }
                    _ => return err("index must be an integer".into()),
                };
                self.guards.push(guard);
                (format!("{}[{idx}]", paren(&st)), et)
            }
            ExprKind::Slice(s, a, b) => {
                let (st, et) = self.seq(s)?;
                let a = self.num(a)?;
                let b = self.num(b)?;
                self.guards.push(format!("0 <= {a} && {a} <= {b} && {b} <= ({st}.len() as int)"));
                let elem = match et {
                    SType::Of(t) => t,
                    SType::Int => unreachable!(),
                };
                // `crate::vocab::slice` is `subrange` within range and clamps
                // outside it, as Lean's `(l.drop a).take (b - a)` does: so the
                // relation has one truth value in both backends, and
                // `s[..n] == t` says `n <= s.len()` (vstd's `subrange` is
                // specified only within range)
                (format!("crate::vocab::slice({st}, {a}, {b})"), SType::Of(RType::Seq(Box::new(elem), SeqKind::Slice)))
            }
            ExprKind::IfVal(c, a, b) => {
                let cp = self.prop(c)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(cp.clone()));
                let ra = self.term(a);
                self.flush_guards();
                self.cx.pop();
                let (at, aty) = ra?;
                self.cx.push(Cx::Guard(format!("!({cp})")));
                let rb = self.term(b);
                self.flush_guards();
                self.cx.pop();
                let (bt, bty) = rb?;
                if aty == bty && aty != SType::Int {
                    (format!("(if {cp} {{ {at} }} else {{ {bt} }})"), aty)
                } else {
                    let an = self.as_num(at, &aty);
                    let bn = self.as_num(bt, &bty);
                    // an `if` of two literals is a mathematical integer: said so
                    ((if is_literal(&an) || an.starts_with("(-") { format!("(if {cp} {{ ({an}) as int }} else {{ ({bn}) as int }})") } else { format!("(if {cp} {{ {an} }} else {{ {bn} }})") }), SType::Int)
                }
            }
            ExprKind::Method(m) => match &**m {
                Method::Len(s) => (format!("({}.len() as int)", self.listlike(s)?), SType::Int),
                Method::MapGet(m, k) => {
                    let (mt, kty, vty) = self.map(m)?;
                    let kt = self.term_as(k, &kty)?;
                    let mt = paren(&mt);
                    (format!("(if {mt}.dom().contains({kt}) {{ Option::Some({mt}[{kt}]) }} else {{ Option::None }})"), SType::Of(RType::Option(Box::new(vty))))
                }
                Method::ContainsKey(..) => {
                    let p = self.prop(e)?;
                    (format!("({p})"), SType::Of(RType::Bool))
                }
                Method::Count { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    // `count(s, x)` compares with `==`: not for elements compared
                    // structurally (then the predicate form, through `prop`)
                    let structural = matches!(&et, SType::Of(t) if needs_eq(t, self.types));
                    let target = match count_target(pred, var) {
                        Some(_) if structural => None,
                        Some(x) => {
                            let (xt, xty) = self.term(&x)?;
                            match &et {
                                _ if xty == et => Some(xt),
                                SType::Of(rt @ RType::Int { .. }) if is_literal(&xt) && fits(&xt, rt) => Some(self.term_as(&x, &rt.clone())?),
                                _ => None,
                            }
                        }
                        None => None,
                    };
                    match target {
                        Some(xt) => (format!("crate::vocab::count({st}, {xt})"), SType::Int),
                        None => {
                            let tl = stype_verus(&et, self.names);
                            let (v, p) = self.under_elem(var, et, &st, pred)?;
                            (format!("({st}.filter(|{v}: {tl}| {p}).len() as int)"), SType::Int)
                        }
                    }
                }
                Method::Sum(s) => {
                    let (st, et) = self.seq(s)?;
                    let y = self.as_num("y".into(), &et);
                    (format!("crate::vocab::sum({st}.map_values(|y: {}| {y}))", stype_verus(&et, self.names)), SType::Int)
                }
                Method::First(s) => {
                    let (st, et) = self.seq(s)?;
                    (format!("crate::vocab::first({st})"), opt(et))
                }
                Method::Last(s) => {
                    let (st, et) = self.seq(s)?;
                    (format!("crate::vocab::last({st})"), opt(et))
                }
                Method::Abs(x) => (format!("vstd::math::abs({})", self.num(x)?), SType::Int),
                Method::Min(a, b) => (format!("vstd::math::min({}, {})", self.num(a)?, self.num(b)?), SType::Int),
                Method::Max(a, b) => (format!("vstd::math::max({}, {})", self.num(a)?, self.num(b)?), SType::Int),
                Method::Pow(a, n) => {
                    let k = self.nat_operand(n)?;
                    (format!("vstd::arithmetic::power::pow({}, {k})", self.num(a)?), SType::Int)
                }
                // bit counts, rotations and wrapping arithmetic: on the two's
                // complement bits of the receiver's width (`crate::vocab`)
                Method::BitCount(k, x) => {
                    let (bits, _, w) = self.twos(x, "the bit counts (`.count_ones()`, …)")?;
                    let f = match k {
                        BitCount::CountOnes => "count_ones",
                        BitCount::CountZeros => "count_zeros",
                        BitCount::LeadingZeros => "leading_zeros",
                        BitCount::LeadingOnes => "leading_ones",
                        BitCount::TrailingZeros => "trailing_zeros",
                        BitCount::TrailingOnes => "trailing_ones",
                    };
                    (format!("(crate::vocab::{f}({bits}, {w}) as int)"), SType::Int)
                }
                Method::Rotate(left, x, n) => {
                    let (bits, signed, w) = self.twos(x, "`.rotate_left(n)` / `.rotate_right(n)`")?;
                    let k = self.nat_operand(n)?;
                    let r = format!("crate::vocab::{}({bits}, {k}, {w})", if *left { "rotate_left" } else { "rotate_right" });
                    (if signed { format!("crate::vocab::from_twos({r}, {w})") } else { format!("({r} as int)") }, SType::Int)
                }
                Method::Wrapping(op, x, y) => {
                    let (a, signed, w) = self.machine_int(x, "`.wrapping_add(y)` and kin")?;
                    let b = self.num(y)?;
                    let sym = match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        _ => "*",
                    };
                    // the residue of the exact result, balanced (two's
                    // complement) for a signed receiver
                    (format!("crate::vocab::{}({a} {sym} {b}, {w})", if signed { "wrap_signed" } else { "wrap_unsigned" }), SType::Int)
                }
                Method::Unwrap(o) => {
                    let (ot, oty) = self.term(o)?;
                    let inner = match oty {
                        SType::Of(RType::Option(t)) => SType::Of(*t),
                        _ => return err("`.unwrap()` needs an Option".into()),
                    };
                    self.guards.push(format!("{}.is_some()", paren(&ot)));
                    (format!("{}.unwrap()", paren(&ot)), inner)
                }
                Method::AsBytes(s) => {
                    let (st, ty) = self.term(s)?;
                    match ty {
                        SType::Of(RType::Seq(e, _)) => (st, SType::Of(RType::Seq(e, SeqKind::Slice))),
                        _ => return err("`.as_bytes()` needs a string".into()),
                    }
                }
                Method::SizeBits => ("(usize::BITS as int)".into(), SType::Int),
                Method::SizeBound { signed: false, .. } => ("(usize::MAX as int)".into(), SType::Int),
                Method::SizeBound { signed: true, max } => (if *max { "(isize::MAX as int)" } else { "(isize::MIN as int)" }.into(), SType::Int),
                Method::IsEmpty(_) | Method::Contains(..) | Method::All { .. } | Method::Any { .. } | Method::Windows2All { .. } | Method::IsSome(_) | Method::IsNone(_) => {
                    let p = self.prop(e)?;
                    (format!("({p})"), SType::Of(RType::Bool))
                }
            },
            ExprKind::Call(f, _) => return err(format!("`{f}` cannot appear here (relational calls are lifted at statement level)")),
            ExprKind::Not(_) | ExprKind::Bin(..) | ExprKind::In(..) | ExprKind::InRange(..) | ExprKind::InDomain(..) => {
                let p = self.prop(e)?;
                (format!("({p})"), SType::Of(RType::Bool))
            }
        })
    }

    /// A specification term as a value of the implementation type `t` (the
    /// arguments of a user constructor, whose fields are implementation
    /// values): a literal becomes a scalar of the field's type; exact types
    /// pass through; sequences cannot be placed in a constructor directly.
    fn exec_value(&mut self, e: &Expr, t: &RType) -> Result<String> {
        let (s, ty) = self.term(e)?;
        match (&ty, t) {
            (SType::Int, RType::Int { signed, bits }) if is_literal(&s) => Ok(format!("{s}{}", scalar_suffix(*signed, *bits))),
            (SType::Int, RType::Int { signed, bits }) => {
                // a machine value from a mathematical integer: `as` would
                // truncate, so its range is a well-formedness obligation (the
                // Lean backend refuses the term outright)
                let sfx = scalar_suffix(*signed, *bits);
                self.guards.push(format!("({sfx}::MIN as int) <= {s} && {s} <= ({sfx}::MAX as int)"));
                Ok(format!("(({s}) as {sfx})"))
            }
            (SType::Of(a), b) if a == b && !needs_view(b) => Ok(s),
            (SType::Of(RType::Seq(..)), RType::Seq(..)) => Err(Error::new(e.span, "a sequence cannot be placed in a constructor directly; bind the value with a pattern or compare fields instead")),
            _ => Err(Error::new(e.span, "constructor argument of the wrong type")),
        }
    }
}

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
        SType::Int => SType::Of(RType::Option(Box::new(RType::MathInt))),
    }
}

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

/// Lower a whole program for the Verus backend (see `crate::lower_program_named`).
pub fn lower_program(prog: &Program, names: &TypeNames) -> Result<Vec<Lowered>> {
    let mut infos = HashMap::new();
    for d in &prog.decls {
        if infos.insert(d.name.clone(), crate::lower::decl_info(d)).is_some() {
            return Err(Error::new(d.name_span, format!("duplicate declaration `{}`", d.name)).in_file(d.file));
        }
    }
    let mut out = Vec::with_capacity(prog.decls.len());
    for d in crate::dependency_order(&prog.decls) {
        let l = lower_with(d, &infos, &prog.types, names).map_err(|e| e.in_file(d.file))?;
        if let Some(i) = infos.get_mut(&d.name) {
            i.choices = l.choices.clone();
        }
        out.push(l);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    fn lowered(src: &str) -> Vec<crate::lower::Lowered> {
        let p = crate::parse_program(src).unwrap();
        super::lower_program(&p, &crate::types::TypeNames::new()).unwrap()
    }

    fn find<'a>(l: &'a [crate::lower::Lowered], n: &str) -> &'a crate::lower::Lowered {
        l.iter().find(|d| d.name == n).unwrap()
    }

    #[test]
    fn user_types_with_sequences_compare_by_contents() {
        let src = "#[derive(Clone, PartialEq, Eq, Debug)]\npub enum Token { Lit(Vec<u8>), End }\npub struct Rec { pub name: String, pub data: Vec<u8>, pub k: u32, pub t: Token }\n#[derive(Clone, Copy, PartialEq, Eq, Debug)]\npub enum Kind { Small, Big(u8) }\n\
            djinn! { pub fn mk(v: &[u8]) -> t: Token { match t { Token::Lit(x) => x == v, Token::End => false, } }\n\
            pub fn same(a: Token, b: Token, r1: Rec, r2: Rec, ts: &[Token], o: Option<Token>) -> r: bool { r == (a == b && r1 != r2 && a in ts && ts.contains(&b) && o == Some(a) && ts.iter().filter(|y| y == a).count() == 1); }\n\
            pub fn plain(a: Kind, b: Kind, ks: &[Kind]) -> r: bool { r == (a == b && a in ks && ks.iter().filter(|y| y == a).count() == 1); } }";
        let l = lowered(src);
        let same = find(&l, "same");
        // one helper per type that needs it, after the types its fields hold
        assert_eq!(same.helpers.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(), ["djinn_eq_Token", "djinn_eq_Rec"]);
        assert!(same.helpers[0].1.contains("pub open spec fn djinn_eq_Token(a: Token, b: Token) -> bool {\n    match (a, b) {\n        (Token::Lit(djinn_a0), Token::Lit(djinn_b0)) => djinn_a0@ == djinn_b0@,\n        (Token::End, Token::End) => true,\n        _ => false,\n    }\n}"), "{}", same.helpers[0].1);
        assert!(same.helpers[1].1.contains("pub open spec fn djinn_eq_Rec(a: Rec, b: Rec) -> bool {\n    (crate::vocab::bytes(a.name@) == crate::vocab::bytes(b.name@) && a.data@ == b.data@ && a.k == b.k && djinn_eq_Token(a.t, b.t))\n}"), "{}", same.helpers[1].1);
        let s = &same.spec[0];
        assert!(s.contains("djinn_eq_Token(a, b)"), "{s}");
        assert!(s.contains("!djinn_eq_Rec(r1, r2)"), "{s}");
        assert!(s.contains("(exists|djinn_i: int| #![trigger ts[djinn_i]] 0 <= djinn_i && djinn_i < (ts.len() as int) && djinn_eq_Token(ts[djinn_i], a))"), "{s}");
        assert!(s.contains("djinn_eq_Token(ts[djinn_i], b))"), "{s}");
        assert!(s.contains("crate::vocab::opt_eq(o, Option::Some(a), |djinn_x: Token, djinn_y: Token| djinn_eq_Token(djinn_x, djinn_y))"), "{s}");
        assert!(s.contains("(ts.filter(|y: Token| djinn_eq_Token(y, a)).len() as int) == 1"), "{s}");
        // the declaration whose output is such a type carries the helper too (for `unambiguous`)
        assert_eq!(find(&l, "mk").helpers.len(), 1);
        // a user type without sequences keeps `==`, `contains` and `count`
        let plain = find(&l, "plain");
        assert!(plain.helpers.is_empty());
        assert_eq!(plain.spec[0], "(r == true <==> ((a == b && ks.contains(a)) && crate::vocab::count(ks, a) == 1))");
        // nested wrappers
        let src = "pub struct Rec { pub data: Vec<u8> }\ndjinn! { pub fn g(a: Vec<Rec>, b: &[Rec], x: Result<Rec, u8>, y: Result<Rec, u8>) -> r: bool { r == (a == b && x == y); } }";
        let s = &lowered(src)[0].spec[0];
        assert!(s.contains("crate::vocab::seq_eq(a, b, |djinn_x: Rec, djinn_y: Rec| djinn_eq_Rec(djinn_x, djinn_y))"), "{s}");
        assert!(s.contains("crate::vocab::res_eq(x, y, |djinn_x: Rec, djinn_y: Rec| djinn_eq_Rec(djinn_x, djinn_y), |djinn_x: u8, djinn_y: u8| djinn_x == djinn_y)"), "{s}");
        // a type recursive through a sequence field is refused
        let p = crate::parse_program("pub enum Tree { Leaf(Vec<u8>), Node(Vec<Tree>) }\ndjinn! { pub fn f(t: Tree, u: Tree) -> r: bool { r == (t == u); } }").unwrap();
        let e = super::lower_program(&p, &Default::default()).unwrap_err();
        assert!(e.msg.contains("recursive"), "{}", e.msg);
    }

    #[test]
    fn a_cast_receiver_is_reduced_to_its_width() {
        let l = lowered("djinn! { pub rel f(x: int, n: u32) -> r: int { r == ((x + 256) as u8).leading_zeros() + ((x + 300) as u8).rotate_left(n) + ((x - 1) as i8).count_ones() + (x as u8).wrapping_add(1); } }");
        let s = &l[0].spec[0];
        // `leading_zeros(wrap_unsigned(256, 8), 8)` is 8 (the vocabulary assumes a receiver in range)
        assert!(s.contains("(crate::vocab::leading_zeros((crate::vocab::wrap_unsigned((x + 256), 8nat) as nat), 8nat) as int)"), "{s}");
        // `rotate_left(wrap_unsigned(300, 8), 0, 8)` is 44
        assert!(s.contains("(crate::vocab::rotate_left((crate::vocab::wrap_unsigned((x + 300), 8nat) as nat), ((n as int) as nat), 8nat) as int)"), "{s}");
        assert!(s.contains("(crate::vocab::count_ones(crate::vocab::twos(crate::vocab::wrap_signed((x - 1), 8nat), 8nat), 8nat) as int)"), "{s}");
        assert!(s.contains("crate::vocab::wrap_unsigned(crate::vocab::wrap_unsigned(x, 8nat) + 1, 8nat)"), "{s}");
        // a machine-typed receiver is in range already
        let l = lowered("djinn! { pub rel g(x: u16) -> r: int { r == x.leading_zeros(); } }");
        assert_eq!(l[0].spec[0], "r == (crate::vocab::leading_zeros(((x as int) as nat), 16nat) as int)");
    }

    #[test]
    fn signed_bit_operands_go_through_the_vocabulary_with_guards() {
        let l = lowered("djinn! { pub rel f(x: i32, y: i32, a: u8, b: u8) -> r: int { r == (x & y) + (a | b) + (x ^ 1); } }");
        let s = &l[0].spec[0];
        assert!(s.contains("(crate::vocab::bit_and(((x as int) as nat), ((y as int) as nat)) as int)"), "{s}");
        assert!(s.contains("((a | b) as int)"), "{s}");
        assert!(s.contains("(crate::vocab::bit_xor(((x as int) as nat), 1) as int)"), "{s}");
        assert!(l[0].wf.iter().any(|w| w.contains("(0 <= (x as int)) && (0 <= (y as int))")), "{:?}", l[0].wf);
    }

    #[test]
    fn a_computed_constructor_field_must_fit_its_type() {
        let l = lowered("#[derive(Clone, Copy, PartialEq, Eq, Debug)]\npub enum K { V(u8), W }\ndjinn! { pub fn mk(x: u8) -> r: K { r == K::V(x + 1); } pub fn lit() -> r: K { r == K::V(3); } }");
        assert_eq!(l[0].spec[0], "r == (K::V(((((x as int) + 1)) as u8)))");
        assert_eq!(l[0].wf, vec!["((u8::MIN as int) <= ((x as int) + 1) && ((x as int) + 1) <= (u8::MAX as int))".to_string()]);
        assert_eq!(l[1].spec[0], "r == (K::V(3u8))");
        assert!(l[1].wf.is_empty());
    }

    #[test]
    fn str_inputs_carry_no_implicit_facts() {
        let l = lowered("djinn! { pub fn f(s: &str) -> r: usize { r == s.len(); } pub rel g(s: String) -> r: usize { r == s.len(); } }");
        assert!(l[0].pre.is_empty(), "{:?}", l[0].pre);
        // a `rel`'s `String` carries the same facts as a `fn`'s (as in the Lean backend)
        assert_eq!(l[1].pre.len(), 2, "{:?}", l[1].pre);
        assert!(l[1].pre[1].contains("crate::vocab::bytes(djinn_cs0) == s"), "{:?}", l[1].pre);
    }

    #[test]
    fn non_ascii_identifiers_are_fine() {
        let l = lowered("djinn! { pub fn f(v: &[u8]) -> r: bool { r == true; some α: usize { v[α] == 0; } } }");
        assert!(l[0].spec[1].starts_with("(exists|α: usize| #![trigger v[(α as int)]]"), "{}", l[0].spec[1]);
        assert!(super::mentions_var("v[(α as int)] == 0", "α") && !super::mentions_var("vα == 0", "α") && !super::mentions_var("αv == 0", "α"));
        assert_eq!(super::inner_binders("(exists|α: usize| v[(α as int)] == 0)"), vec!["α".to_string()]);
        assert_eq!(super::inner_binders("f(|ü: int, y: int| ü + y)"), vec!["ü".to_string(), "y".to_string()]);
    }

    #[test]
    fn verus_keyword_names() {
        // a declaration so named is fine (Verus accepts `fn spec` inside `verus! { }`;
        // checked on every word of `VERUS_KEYWORDS`): the derived names are plain
        let l = lowered("djinn! { pub fn spec(x: u32) -> r: u32 { r == x; } }");
        assert_eq!(l[0].name, "spec");
        // a parameter of that name is a raw identifier
        let l = lowered("djinn! { pub fn f(spec: u32) -> r: u32 { r == spec; } }");
        assert_eq!(l[0].spec[0], "r == r#spec");
    }

    #[test]
    fn scalars_compare_as_int() {
        let l = lowered("djinn! { #[requires(lo <= hi)] pub fn clamp(x: i32, lo: i32, hi: i32) -> r: i32 { lo <= r <= hi; x < lo => r == lo; } }");
        assert_eq!(l[0].pre, vec!["(lo as int) <= (hi as int)".to_string()]);
        assert_eq!(l[0].spec[0], "((lo as int) <= (r as int) && (r as int) <= (hi as int))");
        assert_eq!(l[0].spec[1], "((x as int) < (lo as int) ==> r == lo)");
    }

    #[test]
    fn sequences_are_seqs() {
        let l = lowered("djinn! { #[requires(list.len() >= 1)] pub fn max(list: &[i32]) -> r: i32 { r in list; for x in list { x <= r; } } }");
        assert_eq!(l[0].pre, vec!["(list.len() as int) >= 1".to_string()]);
        assert_eq!(l[0].spec[0], "list.contains(r)");
        assert_eq!(l[0].spec[1], "(forall|x: i32| #![trigger list.contains(x)] list.contains(x) ==> (x as int) <= (r as int))");
    }

    #[test]
    fn counts_and_indices() {
        let l = lowered("djinn! { pub fn f(v: &[i32], i: usize) -> r: usize { r == v.iter().filter(|y| y < 0).count(); v[i] == 3; } }");
        assert_eq!(l[0].spec[0], "(r as int) == (v.filter(|y: i32| (y as int) < 0).len() as int)");
        assert_eq!(l[0].spec[1], "(v[(i as int)] as int) == 3");
        assert_eq!(l[0].wf, vec!["((i as int) < (v.len() as int))".to_string()]);
    }

    #[test]
    fn mut_params_and_calls() {
        let l = lowered("djinn! { #[total] pub rel perm(list: &[i32]) -> t: Vec<i32> { t.len() == list.len(); }\npub fn sort(v: &mut Vec<i32>) { perm(old(v)) == v; for i in 0..v.len() - 1 { v[i] <= v[i + 1]; } } }");
        let s = &l[1];
        assert_eq!(s.inputs[0].0, "v_old");
        assert_eq!(s.spec[0], "perm_spec(v_old, v)");
        assert!(s.spec[1].starts_with("(forall|i: int| #![trigger v[i]] 0 <= i && i < ((v.len() as int) - 1) ==> "), "{}", s.spec[1]);
        assert!(s.wf[0].contains("(v[(i + 1)] as int)") || s.wf[0].contains("(i + 1) < (v.len() as int)"), "{:?}", s.wf);
    }

    #[test]
    fn recursion_is_chained_and_matches_render() {
        let src = "pub enum Token { Lit(u8), Match { dist: u32, len: u32 } }\ndjinn! { pub fn toklen(t: Token) -> n: u32 { match t { Token::Lit(_) => n == 1, Token::Match { len, .. } => n == len, } }\n\
            #[decreases(ts.len())] pub rel encoded(ts: &[Token]) -> m: int { if ts.is_empty() { m == 0; } else { m == encoded(ts[..ts.len() - 1]) + toklen(ts[ts.len() - 1]); } } }";
        let l = lowered(src);
        assert_eq!(l[0].spec[0], "(match t { Token::Lit(_) => (n as int) == 1, Token::Match { len: len_1, .. } => n == len_1 })");
        assert!(l[1].decreases == vec!["(ts.len() as int)".to_string()]);
        assert!(l[1].spec[0].contains("encoded_spec(crate::vocab::slice(ts, 0, ((ts.len() as int) - 1)), v_call0)"), "{}", l[1].spec[0]);
        assert!(l[1].spec[0].contains("toklen_spec(ts[((ts.len() as int) - 1)], v_call1)"), "{}", l[1].spec[0]);
    }

    #[test]
    fn choices_are_spec_fns() {
        let l = lowered("djinn! { #[weakly_specified] pub fn shrink(v: &[u8]) -> out: Vec<u8> { out.len() == v.len(); for i in 0..v.len() { any w: u8 where w <= v[i]; out[i] == w; } } }");
        assert_eq!(l[0].choices, vec![("w".to_string(), "spec_fn(Seq<u8>, int) -> u8".to_string())]);
        assert!(l[0].spec[1].contains("(w(v, i) as int) <= (v[i] as int)"), "{}", l[0].spec[1]);
    }

    #[test]
    fn strings_are_bytes_and_maps_are_vstd_maps() {
        let l = lowered("djinn! { pub fn f(s: String) -> r: usize { r == s.len(); } }");
        assert_eq!(l[0].pre, vec!["(s.len() as int) <= (usize::MAX as int)".to_string(), "(exists|djinn_cs0: Seq<char>| #![trigger crate::vocab::bytes(djinn_cs0)] crate::vocab::bytes(djinn_cs0) == s)".to_string()]);
        assert_eq!(l[0].spec, vec!["(r as int) == (s.len() as int)".to_string()]);
        assert_eq!(super::view_term("s", &crate::ast::RType::Seq(Box::new(crate::ast::RType::Int { signed: false, bits: 8 }), crate::ast::SeqKind::Str), &crate::types::TypeNames::new()), "crate::vocab::bytes(s@)");
        let l = lowered("use std::collections::HashMap;\ndjinn! { pub fn g(m: HashMap<u32, u64>, k: u32) -> r: Option<u64> { r == m.get(&k); } pub fn h(m: HashMap<u32, u64>, k: u32) -> r: bool { r == m.contains_key(&k) && m.len() > 0; } }");
        assert_eq!(l[0].pre, vec!["(m.dom().len() as int) <= (usize::MAX as int)".to_string()]);
        assert_eq!(l[0].spec, vec!["r == (if m.dom().contains(k) { Option::Some(m[k]) } else { Option::None })".to_string()]);
        assert_eq!(l[1].spec, vec!["((r == true <==> m.dom().contains(k)) && (m.dom().len() as int) > 0)".to_string()]);
        assert_eq!(super::view_type(&crate::ast::RType::Map(Box::new(crate::ast::RType::Int { signed: false, bits: 32 }), Box::new(crate::ast::RType::Int { signed: false, bits: 64 })), &crate::types::TypeNames::new()), "Map<u32, u64>");
        // keys vstd cannot reason about are refused
        let p = crate::parse_program("use std::collections::HashMap;\ndjinn! { pub fn f(m: HashMap<String, u8>) -> r: usize { r == m.len(); } }").unwrap();
        let e = super::lower_program(&p, &Default::default()).unwrap_err();
        assert!(e.msg.contains("key of type `String`"), "{}", e.msg);
    }

    #[test]
    fn a_recursive_self_call_is_never_a_trigger() {
        // inside `field_spec`, Verus encodes `field_spec(…)` with a fuel
        // argument: an existential triggered on it could never be witnessed
        let l = lowered("djinn! { #[requires(0 <= n)] #[decreases(n)] pub rel field(s: &[u8], i: int, n: int) -> v: int { if n == 0 { v == 0; } else { v == 2 * field(s, i + 1, n - 1) + (s[i] % 2); } } }");
        let body = &l[0].spec[0];
        assert!(body.contains("#![trigger crate::vocab::trig(v_call0)] crate::vocab::trig(v_call0) && (field_spec(s, (i + 1), (n - 1), v_call0)"), "{body}");
        assert!(!body.contains("#![trigger field_spec("), "{body}");
        // a call of another relation is still a fine trigger
        let l = lowered("djinn! { pub rel g(x: int) -> y: int { y == x; } pub rel h(x: int) -> z: int { z == g(x) + 1; } }");
        assert!(l[1].spec[0].contains("#![trigger g_spec(x, v_call0)]"), "{}", l[1].spec[0]);
    }

    #[test]
    fn a_term_inside_a_nested_quantifier_is_no_trigger() {
        // `lens[k]` occurs only inside the lifted call's existential: in the
        // negated goal the Skolem `k` is ground nowhere, so the `forall` must
        // be triggered on `trig(k)`
        let l = lowered("djinn! { pub rel fixedlen(sym: int) -> n: int { n == sym % 8; } pub rel fixedlit() -> lens: Vec<u8> { lens.len() == 288; for k in 0..288 { lens[k] == fixedlen(k); } } }");
        let body = &l[1].spec[1];
        assert!(body.contains("forall|k: int| #![trigger crate::vocab::trig(k)] crate::vocab::trig(k) ==>"), "{body}");
        assert!(body.contains("#![trigger fixedlen_spec(k, v_out0)]"), "{body}");
        // a term outside the nested quantifier is still preferred
        let l = lowered("djinn! { pub rel f(k: int) -> n: int { n == k; } pub rel g(s: &[u8]) -> b: bool { b == true; for k in 0..s.len() { s[k] < 10; s[k] == f(k); } } }");
        assert!(l[1].spec[1].contains("forall|k: int| #![trigger s[k]]"), "{}", l[1].spec[1]);
    }

    #[test]
    fn bit_methods_use_the_vocabulary() {
        let l = lowered("djinn! { pub rel f(x: u32, y: i8, n: u32, a: u8, b: u32) -> r: int { r == x.count_ones() + y.rotate_right(n) + a.wrapping_add(3) + (a & b) + (x ^ 7); } }");
        let s = &l[0].spec[0];
        assert!(s.contains("(crate::vocab::count_ones(((x as int) as nat), 32nat) as int)"), "{s}");
        assert!(s.contains("crate::vocab::from_twos(crate::vocab::rotate_right(crate::vocab::twos((y as int), 8nat), ((n as int) as nat), 8nat), 8nat)"), "{s}");
        assert!(s.contains("crate::vocab::wrap_unsigned((a as int) + 3, 8nat)"), "{s}");
        assert!(s.contains("(crate::vocab::bit_and(((a as int) as nat), ((b as int) as nat)) as int)"), "{s}");
        assert!(s.contains("((x ^ 7u32) as int)"), "{s}");
    }

    #[test]
    fn shifts_are_arithmetic_and_bits_need_one_type() {
        let l = lowered("djinn! { pub rel f(x: u32, a: int) -> r: int { r == (a << 3) + (x >> a); } }");
        assert!(l[0].spec[0].contains("(a * vstd::arithmetic::power::pow(2, 3))"), "{}", l[0].spec[0]);
        assert!(l[0].spec[0].contains("((x as int) / vstd::arithmetic::power::pow(2, (a as nat)))"), "{}", l[0].spec[0]);
        assert!(l[0].wf.iter().any(|w| w.contains("0 <= a")), "{:?}", l[0].wf);
        let l = lowered("djinn! { pub rel g(x: u32, y: u32) -> r: int { r == (x & y) ^ 7; } }");
        assert_eq!(l[0].spec[0], "r == (((x & y) ^ 7u32) as int)");
    }

    #[test]
    fn reserved_names_are_rejected() {
        let p = crate::parse_program("djinn! { pub rel f(djinn_x: int) -> r: int { r == djinn_x; } }").unwrap();
        assert!(super::lower_program(&p, &Default::default()).is_err());
    }

    #[test]
    fn triggers_fall_back_to_trig() {
        // an index with arithmetic is no trigger; a plain index is
        let l = lowered("djinn! { pub rel f(v: &[u8], n: int) -> r: bool { r == true; for i in 0..n { v[i + 1] == 0; } for j in 0..n { v[j] == 0; } } }");
        assert!(l[0].spec[1].starts_with("(forall|i: int| #![trigger v[(i + 1)]] 0 <= i && i < n ==> "), "{}", l[0].spec[1]);
        assert!(l[0].spec[2].starts_with("(forall|j: int| #![trigger v[j]] "), "{}", l[0].spec[2]);
        // a well-formedness item with nothing but arithmetic: trig, also as a conjunct
        assert!(l[0].wf[0].starts_with("(forall|i: int| #![trigger crate::vocab::trig(i)] crate::vocab::trig(i) ==> (0 <= i"), "{:?}", l[0].wf);
        assert!(super::mentions_var("(s.len() as int) < 3", "s") && !super::mentions_var("(s.len() as int)", "len") && !super::mentions_var("crate::vocab::count(v, x)", "count") && super::mentions_var("f_body(v, w, out)", "w"));
        // a lifted call under a loop: the call mentions the loop variable, but
        // also the lifted output (bound inside), so the loop has no natural trigger
        let l = lowered("djinn! { pub rel m(s: &[u8], d: int) -> b: int { b == d; }\npub rel g(s: &[u8], k: int) -> r: bool { r == true; for d in 1..5 { m(s, d) > 0 => k > d; } } }");
        assert!(l[1].spec[1].starts_with("(forall|d: int| #![trigger crate::vocab::trig(d)] crate::vocab::trig(d) ==> (1 <= d"), "{}", l[1].spec[1]);
        assert!(l[1].spec[1].contains("(exists|v_call0: int| #![trigger m_spec(s, d, v_call0)] m_spec(s, d, v_call0) &&"), "{}", l[1].spec[1]);
        // closure variables bound inside do not count
        assert!(super::has_trigger("v.filter(|y: i32| (y as int) < x).len()", "x", &super::inner_binders("v.filter(|y: i32| (y as int) < x).len()")) == false);
        assert!(super::has_trigger("crate::vocab::count(v, x) == 2", "x", &[]));
        assert!(!super::has_trigger("Option::Some(x) == a", "x", &[]));
        assert!(super::has_trigger("s.subrange(0, i).len() == 0", "i", &[]));
    }

    #[test]
    fn domain_and_option_match() {
        let src = "djinn! { #[requires(g.len() == 81)] pub rel completion(g: &[u8]) -> c: Vec<u8> { c.len() == 81; }\n\
            pub fn solve(g: &[u8]) -> a: Option<Vec<u8>> { if g in domain(completion) { a.is_some(); completion(g) == a.unwrap(); } else { a == None; } } }";
        let l = lowered(src);
        let s = &l[1].spec[0];
        assert!(s.contains("(completion_pre(g) && (exists|o0: Seq<u8>| #![trigger completion_spec(g, o0)] completion_spec(g, o0)))"), "{s}");
        assert!(s.contains("completion_spec(g, a.unwrap())"), "{s}");
        assert!(s.contains("a == Option::None"), "{s}");
        assert!(l[1].wf.iter().any(|w| w.contains("completion_pre(g)")), "{:?}", l[1].wf);
    }
}
