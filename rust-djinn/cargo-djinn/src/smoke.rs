//! `cargo djinn smoke-test`: bounded, symbolic checks of the specification
//! with Z3, before any LLM is paid. Every sequence is fixed to each length up
//! to a bound and every quantifier over it is expanded, so the queries are
//! (mostly) quantifier-free linear arithmetic. Integers are first confined to
//! a small range so that counterexamples are readable; checks that find
//! nothing are repeated with the full machine ranges.
//!
//! Per declaration:
//!   consistency   pre ∧ spec                       sat → witness, else CONTRADICTION
//!   unambiguity   pre ∧ spec(o₁) ∧ spec(o₂) ∧ o₁≠o₂  sat → counterexample  (funcs)
//!   ensures i     pre ∧ spec ∧ ¬ens_i              sat → counterexample
//!   wf            pre ∧ spec ∧ ¬guard              sat → counterexample (index bounds,
//!                                                    divisors, callee preconditions)
//! Counterexamples are enumerated by blocking the found inputs, so the report
//! can say whether the one shown is the only one, one of a few, or one of many
//! within the bounds. Nothing here is a proof: an absent counterexample means
//! absent within the bounds.

use crate::config::Config;
use djinn_syntax::ast::*;
use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Stdio};

pub struct Bounds {
    pub max_len: usize,
    pub int_bound: i64,
    pub max_examples: usize,
    pub timeout_ms: u64,
    pub only: Option<String>,
}

impl Default for Bounds {
    fn default() -> Self {
        Bounds { max_len: 4, int_bound: 8, max_examples: 20, timeout_ms: 10_000, only: None }
    }
}

// ------------------------------------------------------------------ Z3 session

struct Z3 {
    child: Child,
    out: BufReader<std::process::ChildStdout>,
    errors: usize,
}

impl Z3 {
    fn start(timeout_ms: u64) -> std::result::Result<Z3, String> {
        let mut child = Command::new("z3")
            .args(["-in", "-smt2"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("cannot run z3 (is it installed?): {e}"))?;
        let out = BufReader::new(child.stdout.take().unwrap());
        let mut z = Z3 { child, out, errors: 0 };
        z.send(&format!("(set-option :timeout {timeout_ms})"));
        z.send("(set-option :produce-models true)");
        Ok(z)
    }
    fn send(&mut self, s: &str) {
        let stdin = self.child.stdin.as_mut().unwrap();
        let _ = writeln!(stdin, "{s}");
        let _ = stdin.flush();
    }
    /// Read one balanced s-expression (or a bare word) from z3.
    fn read(&mut self) -> String {
        let mut acc = String::new();
        let mut depth = 0i32;
        loop {
            let mut line = String::new();
            if self.out.read_line(&mut line).unwrap_or(0) == 0 {
                return acc;
            }
            for c in line.chars() {
                match c {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
            }
            acc.push_str(&line);
            if depth <= 0 && !acc.trim().is_empty() {
                return acc.trim().to_string();
            }
        }
    }
    fn check_sat(&mut self) -> String {
        self.send("(check-sat)");
        // skip anything that is not a verdict (an `(error …)` from an earlier
        // command would otherwise be taken for the answer), but report it
        for _ in 0..50 {
            let r = self.read();
            let t = r.trim();
            if t == "sat" || t == "unsat" || t == "unknown" || t.is_empty() {
                return t.to_string();
            }
            if std::env::var("DJINN_SMOKE_DUMP").is_ok() {
                eprintln!(";; z3 said: {t}");
            }
            if t.starts_with("(error") {
                self.errors += 1;
            }
        }
        "unknown".into()
    }
    fn get_value(&mut self, vars: &[String]) -> HashMap<String, String> {
        let mut m = HashMap::new();
        if vars.is_empty() {
            return m;
        }
        self.send(&format!("(get-value ({}))", vars.join(" ")));
        let text = self.read();
        for (k, v) in parse_value_pairs(&text) {
            m.insert(k, v);
        }
        m
    }
}

impl Drop for Z3 {
    fn drop(&mut self) {
        self.send("(exit)");
        let _ = self.child.wait();
    }
}

/// `((x 1) (y (- 2)) (z (some 3)))` → pairs with the value rendered humanly.
fn parse_value_pairs(text: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    // skip outer paren
    while i < chars.len() && chars[i] != '(' {
        i += 1;
    }
    i += 1;
    while i < chars.len() {
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= chars.len() || chars[i] == ')' {
            break;
        }
        if chars[i] != '(' {
            i += 1;
            continue;
        }
        // ( name value )
        let start = i;
        let mut depth = 0;
        while i < chars.len() {
            match chars[i] {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        i += 1;
                        break;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        let pair: String = chars[start + 1..i - 1].iter().collect();
        let pair = pair.trim();
        let (name, val) = match pair.find(char::is_whitespace) {
            Some(p) => (&pair[..p], pair[p..].trim()),
            None => (pair, ""),
        };
        out.push((name.to_string(), render_value(val)));
    }
    out
}

fn render_value(v: &str) -> String {
    let v = v.trim();
    if let Some(inner) = v.strip_prefix("(- ").and_then(|s| s.strip_suffix(')')) {
        return format!("-{}", inner.trim());
    }
    if let Some(inner) = v.strip_prefix("(some ").and_then(|s| s.strip_suffix(')')) {
        return format!("Some({})", render_value(inner));
    }
    if v == "none" {
        return "None".into();
    }
    v.to_string()
}

// --------------------------------------------------------------- SMT terms

#[derive(Clone, Debug)]
enum IntT {
    Lit(i64),
    Term(String),
}

impl IntT {
    fn s(&self) -> String {
        match self {
            IntT::Lit(n) if *n < 0 => format!("(- {})", -n),
            IntT::Lit(n) => n.to_string(),
            IntT::Term(t) => t.clone(),
        }
    }
    fn lit(&self) -> Option<i64> {
        match self {
            IntT::Lit(n) => Some(*n),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
enum Val {
    Int(IntT),
    Bool(String),
    Seq(Vec<Val>),
    Opt(String),
    /// a user enum value: (term, enum name)
    Data(String, String),
}

fn and(ts: Vec<String>) -> String {
    let ts: Vec<String> = ts.into_iter().filter(|t| t != "true").collect();
    match ts.len() {
        0 => "true".into(),
        1 => ts.into_iter().next().unwrap(),
        _ => format!("(and {})", ts.join(" ")),
    }
}
fn or(ts: Vec<String>) -> String {
    match ts.len() {
        0 => "false".into(),
        1 => ts.into_iter().next().unwrap(),
        _ => format!("(or {})", ts.join(" ")),
    }
}
fn not(t: &str) -> String {
    format!("(not {t})")
}
fn imp(a: &str, b: &str) -> String {
    if a == "true" {
        b.to_string()
    } else {
        format!("(=> {a} {b})")
    }
}

/// The SMT term for a bit count of the `w`-bit vector `bv`.
fn bit_count_smt(k: BitCount, bv: &str, w: u32) -> String {
    let bit = |v: &str, i: u32| format!("((_ extract {i} {i}) {v})");
    let inv = format!("(bvnot {bv})");
    let ones = |v: &str| format!("(+ {})", (0..w).map(|i| format!("(bv2nat {})", bit(v, i))).collect::<Vec<_>>().join(" "));
    // the index of the first 1 bit in `order`, or `w`
    let first = |v: &str, order: Vec<u32>| {
        let mut t = w.to_string();
        for (pos, i) in order.iter().enumerate().rev() {
            t = format!("(ite (= {} #b1) {pos} {t})", bit(v, *i));
        }
        t
    };
    match k {
        BitCount::CountOnes => ones(bv),
        BitCount::CountZeros => ones(&inv),
        BitCount::TrailingZeros => first(bv, (0..w).collect()),
        BitCount::TrailingOnes => first(&inv, (0..w).collect()),
        BitCount::LeadingZeros => first(bv, (0..w).rev().collect()),
        BitCount::LeadingOnes => first(&inv, (0..w).rev().collect()),
    }
}

/// A `w`-bit pattern given as a natural number, read in two's complement.
fn to_signed(t: &str, w: u32) -> String {
    let half = 1i128 << (w - 1).min(126);
    format!("(let ((u {t})) (ite (>= u {half}) (- u {}) u))", half * 2)
}

/// Tables longer than this are not expanded (every symbolic index into one
/// becomes a chain of that many cases).
const TABLE_LIMIT: usize = 4096;

/// A decimal integer as an SMT-LIB term.
fn smt_int(x: &str) -> String {
    match x.strip_prefix('-') {
        Some(p) => format!("(- {p})"),
        None => x.to_string(),
    }
}

fn arith(op: &str, a: &IntT, b: &IntT) -> IntT {
    if let (Some(x), Some(y)) = (a.lit(), b.lit()) {
        let r = match op {
            "+" => x.checked_add(y),
            "-" => x.checked_sub(y),
            "*" => x.checked_mul(y),
            "div" => {
                if y == 0 {
                    None
                } else {
                    Some(x.div_euclid(y))
                }
            }
            "mod" => {
                if y == 0 {
                    None
                } else {
                    Some(x.rem_euclid(y))
                }
            }
            _ => None,
        };
        if let Some(r) = r {
            return IntT::Lit(r);
        }
    }
    IntT::Term(format!("({op} {} {})", a.s(), b.s()))
}

fn scalar_range(t: &RType) -> Option<(i128, i128)> {
    match t {
        RType::Char => Some((0, 0x10FFFF)),
        RType::Int { signed, bits } => {
            let b = if *bits == 0 { 64 } else { *bits } as u32;
            if *signed {
                Some((-(1i128 << (b - 1)), (1i128 << (b - 1)) - 1))
            } else {
                Some((0, (1i128 << b) - 1))
            }
        }
        _ => None,
    }
}

fn big(n: i128) -> String {
    if n < 0 {
        format!("(- {})", -n)
    } else {
        n.to_string()
    }
}

// -------------------------------------------------------------------- lowering

struct Lo<'a> {
    decls: &'a HashMap<String, &'a Decl>,
    types: &'a TypeDefs,
    bounds: &'a Bounds,
    small: bool,
    env: HashMap<String, Val>,
    /// The Rust types of the declaration's parameters and outputs in scope
    /// (binders shadow them): the width of `x.count_ones()` and kin.
    vtypes: HashMap<String, RType>,
    /// Integer terms that are `(bv2nat B)` of a `w`-bit vector `B` built
    /// here: bit operations reuse `B` instead of converting back (Z3 times
    /// out on chains of `int2bv`/`bv2nat`, and is fast on bit vectors).
    bvs: HashMap<String, (String, u32)>,
    /// `v` → `v_old` while lowering a `requires`
    pre_scope: bool,
    muts: Vec<String>,
    /// declarations of fresh symbols (lifted calls)
    decls_out: Vec<String>,
    /// side constraints (lifted call specs)
    side: Vec<String>,
    /// well-formedness violations: (formula, description); a violation under a
    /// quantifier is existential in the quantifier's variables
    wf: Vec<(String, String)>,
    /// where the encoding stops being exact (a shift too far for it): the
    /// same shape as `wf`, but not obligations of the specification — Lean's
    /// shifts have no limit. Every query assumes none is reached (so what it
    /// finds is genuine), and a declaration that can reach one gets no
    /// "nothing found" verdict (see `Check::Limits`)
    limits: Vec<(String, String)>,
    cx: Vec<String>,
    /// the SMT binders of the quantifiers in scope (`(k_q0 Int)`), so that a
    /// guard inside a `forall`/`exists` body can refer to their variables
    quant: Vec<String>,
    fresh: usize,
    needs_opt: bool,
    /// user enums whose SMT datatype the query needs
    datatypes: Vec<String>,
    depth: usize,
    /// the `for` variables in scope: SMT term and sort, `None` for one no
    /// function can take (a sequence element). A choice (`any`) made under
    /// them is an uninterpreted function of them.
    binds: Vec<Option<(String, String)>>,
    /// the choice functions declared so far: (source name, call-site path,
    /// argument sorts) → SMT symbol. Shared by both copies of an unambiguity
    /// query, which is what "unambiguous modulo the choices" means.
    choice_fns: Vec<((String, Vec<usize>, Vec<String>), String)>,
    /// lower a nested `any` as a local existential instead (the existence
    /// check: an output must exist for SOME admissible choice)
    choices_local: bool,
    /// call sites, numbered per lowering of the body, so that a choice made
    /// inside an inlined callee is one function per call site, and the same
    /// one in both copies
    call_seq: usize,
    site: Vec<usize>,
}

type R<T> = std::result::Result<T, String>;

/// The SMT sort of a Rust type, if the smoke test can represent it.
fn sort_of(t: &RType, types: &TypeDefs) -> R<String> {
    match t {
        RType::Int { .. } | RType::MathInt | RType::Char => Ok("Int".into()),
        RType::Bool => Ok("Bool".into()),
        RType::Option(i) if matches!(**i, RType::Int { .. } | RType::Char) => Ok("OptInt".into()),
        RType::Named(n) if types.enums.contains_key(n) => Ok(n.clone()),
        other => Err(format!("type {} is not supported by smoke-test", djinn_syntax::types::rust_type(other))),
    }
}

/// `(declare-datatype Token ((Lit (Lit_f0 Int)) (Match (Match_f0 Int) (Match_f1 Int))))`
fn datatype_decl(e: &EnumDef, types: &TypeDefs) -> R<String> {
    let mut ctors = Vec::new();
    for v in &e.variants {
        let mut fields = Vec::new();
        for (k, (_, t)) in v.fields.iter().enumerate() {
            fields.push(format!("({}_f{k} {})", v.name, sort_of(t, types)?));
        }
        ctors.push(if fields.is_empty() { format!("({})", v.name) } else { format!("({} {})", v.name, fields.join(" ")) });
    }
    Ok(format!("(declare-datatype {} ({}))", e.name, ctors.join(" ")))
}

/// Range constraints on the scalar fields of an enum-typed symbol (every
/// variant's fields within their machine ranges, or the small bound).
fn data_ranges(nm: &str, en: &str, types: &TypeDefs, small: bool, int_bound: i64) -> Vec<String> {
    let mut out = Vec::new();
    let Some(e) = types.enums.get(en) else { return out };
    for v in &e.variants {
        let mut conds = Vec::new();
        for (k, (_, t)) in v.fields.iter().enumerate() {
            if let Some((lo, hi)) = scalar_range(t) {
                let (lo, hi) = if small { (lo.max(-(int_bound as i128)), hi.min(int_bound as i128)) } else { (lo, hi) };
                let sel = format!("({}_f{k} {nm})", v.name);
                conds.push(format!("(and (<= {} {sel}) (<= {sel} {}))", big(lo), big(hi)));
            }
        }
        if !conds.is_empty() {
            out.push(format!("(=> ((_ is {}) {nm}) {})", v.name, and(conds)));
        }
    }
    out
}

/// Datatype declarations in dependency order (an enum before the enums that mention it).
fn datatype_decls(names: &[String], types: &TypeDefs) -> R<Vec<String>> {
    let mut order: Vec<String> = Vec::new();
    fn visit(n: &str, types: &TypeDefs, order: &mut Vec<String>) {
        if order.iter().any(|x| x == n) {
            return;
        }
        if let Some(e) = types.enums.get(n) {
            for v in &e.variants {
                for (_, t) in &v.fields {
                    if let RType::Named(m) = t {
                        visit(m, types, order);
                    }
                }
            }
        }
        order.push(n.to_string());
    }
    for n in names {
        visit(n, types, &mut order);
    }
    order.iter().map(|n| datatype_decl(types.enums.get(n).ok_or_else(|| format!("unknown enum `{n}`"))?, types)).collect()
}

/// `(exists (BINDERS) BODY)` → `(BINDERS, BODY)`.
fn split_exists(s: &str) -> Option<(String, String)> {
    let rest = s.strip_prefix("(exists (")?;
    let mut depth = 1i32;
    for (i, c) in rest.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    let body = rest[i + 1..].trim().strip_suffix(')')?;
                    return Some((rest[..i].to_string(), body.trim().to_string()));
                }
            }
            _ => {}
        }
    }
    None
}

impl<'a> Lo<'a> {
    fn ctx(&self) -> String {
        and(self.cx.clone())
    }

    fn guard(&mut self, g: String, what: String) {
        let c = self.ctx();
        let v = and(vec![c, not(&g)]);
        let v = if self.quant.is_empty() { v } else { format!("(exists ({}) {})", self.quant.join(" "), v) };
        self.wf.push((v, what));
    }

    /// A limit of the encoding: `g` holds wherever the term built is exact.
    fn limit(&mut self, g: String, what: String) {
        let c = self.ctx();
        let v = and(vec![c, not(&g)]);
        let v = if self.quant.is_empty() { v } else { format!("(exists ({}) {})", self.quant.join(" "), v) };
        self.limits.push((v, what));
    }

    fn use_datatype(&mut self, n: &str) {
        if !self.datatypes.iter().any(|x| x == n) {
            self.datatypes.push(n.to_string());
        }
    }

    /// A width `w` such that the non-negative values of `e` (lowered to `t`)
    /// are below `2^w`, when it is evident: a bit vector built here, a
    /// machine value, a bit count, a literal.
    fn value_width(&self, e: &Expr, t: &IntT) -> Option<u32> {
        if let Some((_, w)) = self.bvs.get(&t.s()) {
            return Some(*w);
        }
        if let Some(n) = t.lit() {
            return Some((64 - (n.max(0) as u64).leading_zeros()).max(1));
        }
        match &e.kind {
            ExprKind::Method(m) if matches!(&**m, Method::BitCount(..)) => Some(8),
            _ => self.unsigned_width(e, t),
        }
    }

    /// The width of an unsigned machine value (or of a bit vector built here).
    fn unsigned_width(&self, e: &Expr, t: &IntT) -> Option<u32> {
        if let Some((_, w)) = self.bvs.get(&t.s()) {
            return Some(*w);
        }
        if let Some(w) = BV_DECLARED.with(|m| m.borrow().get(&t.s()).copied()) {
            return Some(w);
        }
        // a cast keeps the value (`(x + 1) as u8` may be 256): no width
        if matches!(e.kind, ExprKind::Cast(..)) {
            return None;
        }
        match self.int_width(e) {
            Ok((false, w)) => Some(w),
            _ => None,
        }
    }

    /// `t` as a `w`-bit vector: the vector itself when `t` is one built here.
    fn to_bv(&self, t: &IntT, w: u32) -> String {
        let declared = BV_DECLARED.with(|m| m.borrow().get(&t.s()).copied());
        if let Some(dw) = declared {
            let b = format!("{}_bv", t.s());
            return if dw == w {
                b
            } else if dw < w {
                format!("((_ zero_extend {}) {b})", w - dw)
            } else {
                format!("((_ extract {} 0) {b})", w - 1)
            };
        }
        match self.bvs.get(&t.s()) {
            Some((b, bw)) if *bw == w => b.clone(),
            Some((b, bw)) if *bw < w => format!("((_ zero_extend {}) {b})", w - bw),
            _ => format!("((_ int2bv {w}) {})", t.s()),
        }
    }

    /// The natural number of the `w`-bit vector `bv`, remembered as one.
    fn from_bv(&mut self, bv: String, w: u32) -> IntT {
        let t = format!("(bv2nat {bv})");
        self.bvs.insert(t.clone(), (bv, w));
        IntT::Term(t)
    }

    /// Signedness and width of a machine integer: a parameter or output, an
    /// element of one, or a cast (a `usize` is taken as 64 bits).
    fn int_width(&self, e: &Expr) -> R<(bool, u32)> {
        let t = match &e.kind {
            ExprKind::Var(v) | ExprKind::Old(v) => self.vtypes.get(v).cloned(),
            ExprKind::Index(s, _) => match &s.kind {
                ExprKind::Var(v) => match self.vtypes.get(v) {
                    Some(RType::Seq(el, _)) => Some((**el).clone()),
                    _ => None,
                },
                _ => None,
            },
            ExprKind::Cast(_, t) => Some(t.clone()),
            _ => None,
        };
        match t {
            Some(RType::Int { signed, bits }) => Ok((signed, if bits == 0 { 64 } else { bits })),
            _ => Err("smoke-test needs the receiver of a width-dependent method (`.count_ones()`, `.rotate_left(n)`, `.wrapping_add(y)`, …) to be a parameter, an element of one, or a cast".into()),
        }
    }

    fn with<T>(&mut self, binds: Vec<(String, Val)>, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let mut saved = Vec::new();
        let mut saved_types = Vec::new();
        for (n, v) in binds {
            // a binder's type is not tracked: it shadows any parameter's
            saved_types.push((n.clone(), self.vtypes.remove(&n)));
            saved.push((n.clone(), self.env.insert(n, v)));
        }
        let r = f(self);
        for (n, old) in saved {
            match old {
                Some(v) => self.env.insert(n, v),
                None => self.env.remove(&n),
            };
        }
        for (n, t) in saved_types {
            if let Some(t) = t {
                self.vtypes.insert(n, t);
            }
        }
        r
    }

    fn stmts(&mut self, ss: &[Stmt]) -> R<String> {
        let mut v = Vec::new();
        for (i, s) in ss.iter().enumerate() {
            // a choice is in scope for the rest of its block
            if let StmtKind::Any { name, ty, wherec } = &s.kind {
                v.push(self.any_block(name, ty, wherec, &ss[i + 1..])?);
                return Ok(and(v));
            }
            v.push(self.stmt(s)?);
        }
        Ok(and(v))
    }

    /// `any x: T where c;` followed by the rest of its block.
    fn any_block(&mut self, name: &str, ty: &RType, wherec: &Expr, rest: &[Stmt]) -> R<String> {
        // at the top level of the declaration under test the choice was
        // declared like an input (free, in every copy; quantified with the
        // outputs in the existence check): only `c` remains
        if self.depth == 0 && self.binds.is_empty() && self.env.contains_key(name) {
            let w = self.constraint(wherec)?;
            let r = self.stmts(rest)?;
            return Ok(and(vec![w, r]));
        }
        if self.choices_local {
            // an existential over the rest of the block, as `some`
            let nm = format!("{name}_e{}", self.fresh);
            self.fresh += 1;
            let (qvar, val) = match ty {
                RType::Bool => (format!("({nm} Bool)"), Val::Bool(nm.clone())),
                RType::Int { .. } | RType::MathInt | RType::Char => (format!("({nm} Int)"), Val::Int(IntT::Term(nm.clone()))),
                RType::Named(en) if self.types.enums.contains_key(en) => {
                    self.use_datatype(en);
                    (format!("({nm} {en})"), Val::Data(nm.clone(), en.clone()))
                }
                _ => return Err(format!("a choice (`any {name}`) of type {} under a binder is not supported by smoke-test", djinn_syntax::types::rust_type(ty))),
            };
            let ranges = self.choice_ranges(ty, &nm);
            self.quant.push(qvar.clone());
            let b = self.with(vec![(name.to_string(), val)], |l| {
                let w = l.constraint(wherec)?;
                let r = l.stmts(rest)?;
                Ok(and(vec![w, r]))
            })?;
            self.quant.pop();
            return Ok(format!("(exists ({qvar}) {})", and(ranges.into_iter().chain([b]).collect())));
        }
        // free: an uninterpreted function of the binders in scope
        let (val, ranges) = self.any_fun(name, ty)?;
        let b = self.with(vec![(name.to_string(), val)], |l| {
            let w = l.constraint(wherec)?;
            let r = l.stmts(rest)?;
            Ok(and(vec![w, r]))
        })?;
        Ok(and(ranges.into_iter().chain([b]).collect()))
    }

    /// The choice `name : ty` as an uninterpreted function of the binders in
    /// scope (one per call-site path), applied to them; and the range
    /// constraints of its value.
    fn any_fun(&mut self, name: &str, ty: &RType) -> R<(Val, Vec<String>)> {
        let sort = sort_of(ty, self.types)?;
        if let RType::Named(en) = ty {
            self.use_datatype(en);
        }
        let mut args = Vec::new();
        let mut sorts = Vec::new();
        for b in &self.binds {
            match b {
                Some((t, so)) => {
                    args.push(t.clone());
                    sorts.push(so.clone());
                }
                None => return Err(format!("a choice (`any {name}`) under a binder of sequence type is not supported by smoke-test")),
            }
        }
        let key = (name.to_string(), self.site.clone(), sorts.clone());
        let sym = match self.choice_fns.iter().find(|(k, _)| k == &key) {
            Some((_, sym)) => sym.clone(),
            None => {
                let sym = format!("{name}_c{}", self.choice_fns.len());
                self.decls_out.push(format!("(declare-fun {sym} ({}) {sort})", sorts.join(" ")));
                self.choice_fns.push((key, sym.clone()));
                sym
            }
        };
        let term = if args.is_empty() { sym } else { format!("({sym} {})", args.join(" ")) };
        let ranges = self.choice_ranges(ty, &term);
        Ok((self.val_of_sort(ty, term)?, ranges))
    }

    /// The range of a choice's value: its Rust type's, within the small
    /// regime's bound.
    fn choice_ranges(&self, ty: &RType, term: &str) -> Vec<String> {
        let mut v = Vec::new();
        if let Some((lo, hi)) = scalar_range(ty) {
            let b = self.bounds.int_bound as i128;
            let (lo, hi) = if self.small { (lo.max(-b), hi.min(b)) } else { (lo, hi) };
            v.push(format!("(and (<= {} {term}) (<= {term} {}))", big(lo), big(hi)));
        }
        if let RType::Named(en) = ty {
            v.extend(data_ranges(term, en, self.types, self.small, self.bounds.int_bound));
        }
        v
    }

    fn stmt(&mut self, s: &Stmt) -> R<String> {
        match &s.kind {
            StmtKind::Constraint(e) => self.constraint(e),
            StmtKind::Any { name, ty, wherec } => self.any_block(name, ty, wherec, &[]),
            StmtKind::ForIn { var, seq, body } => {
                let sv = self.term(seq)?;
                let elems = match sv {
                    Val::Seq(e) => e,
                    _ => return Err(format!("`for {var} in ..` over a non-sequence")),
                };
                let mut v = Vec::new();
                for el in elems {
                    self.binds.push(bind_of(&el));
                    let r = self.with(vec![(var.clone(), el)], |l| l.stmts(body));
                    self.binds.pop();
                    v.push(r?);
                }
                Ok(and(v))
            }
            StmtKind::ForRange { var, lo, hi, body } => {
                let lo = self.num(lo)?;
                let hi = self.num(hi)?;
                if let (Some(a), Some(b)) = (lo.lit(), hi.lit()) {
                    let mut v = Vec::new();
                    for k in a..b {
                        self.binds.push(Some((IntT::Lit(k).s(), "Int".into())));
                        let r = self.with(vec![(var.clone(), Val::Int(IntT::Lit(k)))], |l| l.stmts(body));
                        self.binds.pop();
                        v.push(r?);
                    }
                    return Ok(and(v));
                }
                if self.small {
                    // expand over the small range, and keep the range inside it
                    let b = self.bounds.int_bound;
                    let mut v = Vec::new();
                    for k in -b..=b {
                        let inside = format!("(and (<= {} {k}) (< {k} {}))", lo.s(), hi.s());
                        self.cx.push(inside.clone());
                        self.binds.push(Some((IntT::Lit(k).s(), "Int".into())));
                        let body_s = self.with(vec![(var.clone(), Val::Int(IntT::Lit(k)))], |l| l.stmts(body));
                        self.binds.pop();
                        self.cx.pop();
                        let body_s = body_s?;
                        v.push(imp(&inside, &body_s));
                    }
                    self.side.push(format!("(and (<= (- {b}) {}) (<= {} (+ {b} 1)))", lo.s(), hi.s()));
                    Ok(and(v))
                } else {
                    let i = format!("{var}_q{}", self.fresh);
                    self.fresh += 1;
                    let inside = format!("(and (<= {} {i}) (< {i} {}))", lo.s(), hi.s());
                    self.cx.push(inside.clone());
                    self.quant.push(format!("({i} Int)"));
                    self.binds.push(Some((i.clone(), "Int".into())));
                    let body_s = self.with(vec![(var.clone(), Val::Int(IntT::Term(i.clone())))], |l| l.stmts(body));
                    self.binds.pop();
                    self.quant.pop();
                    let body_s = body_s?;
                    self.cx.pop();
                    Ok(format!("(forall (({i} Int)) {})", imp(&inside, &body_s)))
                }
            }
            StmtKind::Some { binders, body } => {
                let mut qvars = Vec::new();
                let mut binds = Vec::new();
                let mut ranges = Vec::new();
                for (n, t) in binders {
                    match t {
                        RType::Int { .. } | RType::Bool | RType::MathInt | RType::Char => {
                            let nm = format!("{n}_e{}", self.fresh);
                            self.fresh += 1;
                            if *t == RType::Bool {
                                qvars.push(format!("({nm} Bool)"));
                                binds.push((n.clone(), Val::Bool(nm)));
                            } else {
                                qvars.push(format!("({nm} Int)"));
                                if let Some(r) = scalar_range(t) {
                                    ranges.push(format!("(and (<= {} {nm}) (<= {nm} {}))", big(r.0), big(r.1)));
                                }
                                binds.push((n.clone(), Val::Int(IntT::Term(nm))));
                            }
                        }
                        RType::Named(en) if self.types.enums.contains_key(en) => {
                            self.use_datatype(en);
                            let nm = format!("{n}_e{}", self.fresh);
                            self.fresh += 1;
                            qvars.push(format!("({nm} {en})"));
                            ranges.extend(data_ranges(&nm, en, self.types, false, self.bounds.int_bound));
                            binds.push((n.clone(), Val::Data(nm, en.clone())));
                        }
                        _ => return Err("`some` binders of sequence or other types are not supported by smoke-test".into()),
                    }
                }
                let nq = qvars.len();
                self.quant.extend(qvars.iter().cloned());
                let saved_wf = self.wf.len();
                let b = self.with(binds, |l| l.stmts(body))?;
                self.quant.truncate(self.quant.len() - nq);
                let inner = and(ranges.into_iter().chain(std::iter::once(b)).collect());
                // well-formedness inside is stated for the binders' values that
                // satisfy the body (as `Spec.lean` states it): a violation is
                // one with the body true, not any value of the binders
                for (w, _) in self.wf[saved_wf..].iter_mut() {
                    if let Some((q, rest)) = split_exists(w) {
                        *w = format!("(exists ({q}) (and {inner} {rest}))");
                    }
                }
                Ok(format!("(exists ({}) {})", qvars.join(" "), inner))
            }
            StmtKind::Cases(alts) => {
                let mut v = Vec::new();
                for a in alts {
                    v.push(self.stmt(a)?);
                }
                Ok(or(v))
            }
            StmtKind::If { cond, then, els } => {
                let c = self.prop(cond)?;
                self.cx.push(c.clone());
                let t = self.stmts(then)?;
                self.cx.pop();
                let mut parts = vec![imp(&c, &t)];
                if let Some(e) = els {
                    let nc = not(&c);
                    self.cx.push(nc.clone());
                    let es = self.stmts(e)?;
                    self.cx.pop();
                    parts.push(imp(&nc, &es));
                }
                Ok(and(parts))
            }
            StmtKind::Implies(c, s) => {
                let c = self.prop(c)?;
                self.cx.push(c.clone());
                let b = self.stmt(s)?;
                self.cx.pop();
                Ok(imp(&c, &b))
            }
            StmtKind::Match { scrutinee, arms } => {
                let (t, en) = match self.term(scrutinee)? {
                    Val::Data(t, en) => (t, en),
                    _ => return Err("`match` on a value that is not a user enum".into()),
                };
                let edef = self.types.enums.get(&en).ok_or_else(|| format!("unknown enum `{en}`"))?.clone();
                let mut parts = Vec::new();
                let mut covered = Vec::new();
                for a in arms {
                    match &a.pat {
                        Pattern::Wild => {
                            let g = not(&or(covered.iter().map(|v| format!("((_ is {v}) {t})")).collect()));
                            self.cx.push(g.clone());
                            let b = self.stmts(&a.body)?;
                            self.cx.pop();
                            parts.push(imp(&g, &b));
                        }
                        Pattern::Variant { variant, fields, .. } => {
                            let vdef = edef.variants.iter().find(|v| &v.name == variant).ok_or_else(|| format!("no variant `{variant}`"))?;
                            let g = format!("((_ is {variant}) {t})");
                            let binders: Vec<Option<String>> = match fields {
                                PatFields::Unit => vec![],
                                PatFields::Tuple(v) => v.clone(),
                                PatFields::Struct(v, _) => vdef.fields.iter().map(|(n, _)| v.iter().find(|(f, _)| Some(f) == n.as_ref()).and_then(|(_, b)| b.clone())).collect(),
                            };
                            let mut binds = Vec::new();
                            for (k, ((_, fty), b)) in vdef.fields.iter().zip(binders.iter().chain(std::iter::repeat(&None))).enumerate() {
                                if let Some(b) = b {
                                    let sel = format!("({variant}_f{k} {t})");
                                    binds.push((b.clone(), self.val_of_sort(fty, sel)?));
                                }
                            }
                            covered.push(variant.clone());
                            self.cx.push(g.clone());
                            let b = self.with(binds, |l| l.stmts(&a.body))?;
                            self.cx.pop();
                            parts.push(imp(&g, &b));
                        }
                    }
                }
                Ok(and(parts))
            }
        }
    }
}

/// A binder's value as an argument of a choice function: term and sort,
/// `None` for a sequence.
fn bind_of(v: &Val) -> Option<(String, String)> {
    match v {
        Val::Int(t) => Some((t.s(), "Int".into())),
        Val::Bool(b) => Some((b.clone(), "Bool".into())),
        Val::Data(t, en) => Some((t.clone(), en.clone())),
        Val::Opt(t) => Some((t.clone(), "OptInt".into())),
        Val::Seq(_) => None,
    }
}

impl<'a> Lo<'a> {
    /// A symbolic value of Rust type `t` backed by the SMT term `term`.
    fn val_of_sort(&mut self, t: &RType, term: String) -> R<Val> {
        Ok(match t {
            RType::Int { .. } | RType::MathInt | RType::Char => Val::Int(IntT::Term(term)),
            RType::Bool => Val::Bool(term),
            RType::Option(_) => {
                self.needs_opt = true;
                Val::Opt(term)
            }
            RType::Named(n) if self.types.enums.contains_key(n) => {
                self.use_datatype(n);
                Val::Data(term, n.clone())
            }
            other => return Err(format!("type {} is not supported by smoke-test", djinn_syntax::types::rust_type(other))),
        })
    }

    fn constraint(&mut self, e: &Expr) -> R<String> {
        // `A && B`, `A || B`, `A => B`: the right operand is read under the left's
        // truth (resp. falsity); its guards and lifted calls are scoped there.
        if let ExprKind::Bin(op @ (BinOp::And | BinOp::Or), l, r) = &e.kind {
            let lp = self.constraint(l)?;
            let g = if *op == BinOp::And { lp.clone() } else { not(&lp) };
            self.cx.push(g);
            let n = self.side.len();
            let rp = self.constraint(r)?;
            let scoped: Vec<String> = self.side.drain(n..).collect();
            self.cx.pop();
            let rp = if scoped.is_empty() { rp } else { and(scoped.into_iter().chain([rp]).collect()) };
            return Ok(if *op == BinOp::And { and(vec![lp, rp]) } else { or(vec![lp, rp]) });
        }
        if let ExprKind::Bin(BinOp::Eq, l, r) = &e.kind {
            if let ExprKind::Call(f, args) = &l.kind {
                if self.decls.contains_key(f) {
                    let out = self.term(r)?;
                    return self.inline_call(f, args, out);
                }
            }
            if let ExprKind::Call(f, args) = &r.kind {
                if self.decls.contains_key(f) {
                    let out = self.term(l)?;
                    return self.inline_call(f, args, out);
                }
            }
        }
        if let ExprKind::Call(f, args) = &e.kind {
            if let Some(d) = self.decls.get(f) {
                if d.outputs().len() == 1 && d.outputs()[0].1 == RType::Bool {
                    return self.inline_call(f, args, Val::Bool("true".into()));
                }
            }
        }
        self.prop(e)
    }

    /// Inline `f_spec args out` (the callee's pre and body), recording the
    /// callee's precondition as a call-site guard.
    fn inline_call(&mut self, f: &str, args: &[Expr], out: Val) -> R<String> {
        if self.types.ambient.contains_key(f) {
            return Err(format!("the ambient function `{f}` cannot be smoke-tested (its meaning is its Rust code)"));
        }
        let d = *self.decls.get(f).ok_or_else(|| format!("unknown function `{f}`"))?;
        if self.depth > 6 {
            return Err(format!("recursion through `{f}` is too deep for smoke-test (recursive relations are unfolded at most 6 times)"));
        }
        let outs = d.outputs();
        if outs.len() != 1 {
            return Err(format!("`{f}` has {} outputs; only single-output callees are supported", outs.len()));
        }
        if args.len() != d.params.len() {
            return Err(format!("`{f}` takes {} arguments, {} given", d.params.len(), args.len()));
        }
        let mut argv = Vec::new();
        for a in args {
            argv.push(self.term(a)?);
        }
        // a fresh lowering context for the callee: its own env
        let saved_env = std::mem::take(&mut self.env);
        let saved_vtypes = std::mem::replace(&mut self.vtypes, d.inputs().into_iter().chain(d.outputs()).collect());
        let saved_pre = self.pre_scope;
        let saved_muts = std::mem::take(&mut self.muts);
        self.depth += 1;
        self.call_seq += 1;
        self.site.push(self.call_seq);
        let mut env = HashMap::new();
        for ((n, _), v) in d.inputs().iter().zip(argv.iter()) {
            env.insert(n.clone(), v.clone());
        }
        self.env = env;
        self.muts = d.params.iter().filter(|p| p.mut_ref).map(|p| p.name.clone()).collect();
        self.pre_scope = true;
        let mut pre = Vec::new();
        let res = (|| -> R<(String, String)> {
            for e in &d.requires {
                pre.push(self.constraint(e)?);
            }
            self.pre_scope = false;
            self.env.insert(outs[0].0.clone(), out.clone());
            let body = self.stmts(&d.body)?;
            Ok((and(pre.clone()), body))
        })();
        self.depth -= 1;
        self.site.pop();
        self.env = saved_env;
        self.vtypes = saved_vtypes;
        self.pre_scope = saved_pre;
        self.muts = saved_muts;
        let (pre_s, body) = res?;
        if pre_s != "true" {
            self.guard(pre_s.clone(), format!("precondition of `{f}` at a call site"));
        }
        Ok(and(vec![pre_s, body]))
    }

    fn prop(&mut self, e: &Expr) -> R<String> {
        Ok(match &e.kind {
            ExprKind::Bool(b) => b.to_string(),
            ExprKind::Not(x) => not(&self.prop(x)?),
            // the right operand is read under the left's truth (resp. falsity),
            // so its guards are scoped there, as in `constraint`
            ExprKind::Bin(op @ (BinOp::And | BinOp::Or), l, r) => {
                let lp = self.prop(l)?;
                self.cx.push(if *op == BinOp::And { lp.clone() } else { not(&lp) });
                let rp = self.prop(r);
                self.cx.pop();
                let rp = rp?;
                if *op == BinOp::And { and(vec![lp, rp]) } else { or(vec![lp, rp]) }
            }
            ExprKind::Bin(op, l, r) if matches!(op, BinOp::Eq | BinOp::Ne) && (smoke_proplike(l) || smoke_proplike(r)) => {
                let (bside, pside) = if smoke_proplike(r) { (l, r) } else { (r, l) };
                let bp = self.prop(bside)?;
                let pp = self.prop(pside)?;
                let eq = format!("(= {bp} {pp})");
                if *op == BinOp::Eq { eq } else { not(&eq) }
            }
            ExprKind::Bin(op, l, r) if op.is_cmp() => {
                let a = self.term(l)?;
                let b = self.term(r)?;
                match (&a, &b) {
                    (Val::Int(x), Val::Int(y)) => {
                        let sym = match op {
                            BinOp::Eq => "=",
                            BinOp::Ne => "distinct",
                            BinOp::Lt => "<",
                            BinOp::Le => "<=",
                            BinOp::Gt => ">",
                            BinOp::Ge => ">=",
                            _ => unreachable!(),
                        };
                        format!("({sym} {} {})", x.s(), y.s())
                    }
                    (Val::Bool(x), Val::Bool(y)) | (Val::Opt(x), Val::Opt(y)) | (Val::Data(x, _), Val::Data(y, _)) => match op {
                        BinOp::Eq => format!("(= {x} {y})"),
                        BinOp::Ne => format!("(distinct {x} {y})"),
                        _ => return Err("ordering comparison on non-numeric values".into()),
                    },
                    (Val::Seq(x), Val::Seq(y)) => {
                        let eq = if x.len() != y.len() {
                            "false".to_string()
                        } else {
                            let mut v = Vec::new();
                            for (p, q) in x.iter().zip(y.iter()) {
                                v.push(self.val_eq(p, q)?);
                            }
                            and(v)
                        };
                        match op {
                            BinOp::Eq => eq,
                            BinOp::Ne => not(&eq),
                            _ => return Err("ordering comparison on sequences".into()),
                        }
                    }
                    _ => return Err("comparison between values of different kinds".into()),
                }
            }
            ExprKind::In(x, s) => {
                let xv = self.term(x)?;
                let sv = self.term(s)?;
                let elems = match sv {
                    Val::Seq(e) => e,
                    _ => return Err("`in` needs a sequence".into()),
                };
                let mut v = Vec::new();
                for el in &elems {
                    v.push(self.val_eq(&xv, el)?);
                }
                or(v)
            }
            ExprKind::InRange(x, f) => {
                // ∃ inputs. f_spec inputs x — inputs become fresh existentials
                let d = *self.decls.get(f).ok_or_else(|| format!("unknown `{f}`"))?;
                let xv = self.term(x)?;
                let mut qvars = Vec::new();
                let mut args = Vec::new();
                for p in &d.params {
                    match &p.ty {
                        RType::Int { .. } => {
                            let nm = format!("{}_r{}", p.name, self.fresh);
                            self.fresh += 1;
                            qvars.push(format!("({nm} Int)"));
                            args.push(Expr::new(e.span, ExprKind::Var(nm.clone())));
                            self.env.insert(nm.clone(), Val::Int(IntT::Term(nm)));
                        }
                        _ => return Err("`in range(f)` is only supported for scalar-input functions".into()),
                    }
                }
                let body = self.inline_call(f, &args, xv)?;
                if qvars.is_empty() {
                    body
                } else {
                    format!("(exists ({}) {})", qvars.join(" "), body)
                }
            }
            ExprKind::InDomain(_, _) => return Err("`in domain(f)` is not supported by smoke-test yet".into()),
            ExprKind::Method(m) => match &**m {
                Method::IsEmpty(s) => match self.term(s)? {
                    Val::Seq(e) => (e.is_empty()).to_string(),
                    _ => return Err("`.is_empty()` needs a sequence".into()),
                },
                Method::Contains(s, x) => return self.prop(&Expr::new(e.span, ExprKind::In(x.clone().into(), s.clone().into()))),
                Method::All { seq, var, pred } => {
                    let elems = self.seq(seq)?;
                    let mut v = Vec::new();
                    for el in elems {
                        v.push(self.with(vec![(var.clone(), el)], |l| l.prop(pred))?);
                    }
                    and(v)
                }
                Method::Any { seq, var, pred } => {
                    let elems = self.seq(seq)?;
                    let mut v = Vec::new();
                    for el in elems {
                        v.push(self.with(vec![(var.clone(), el)], |l| l.prop(pred))?);
                    }
                    or(v)
                }
                Method::Windows2All { seq, var, pred } => {
                    let elems = self.seq(seq)?;
                    let mut v = Vec::new();
                    for w in elems.windows(2) {
                        let pair = Val::Seq(vec![w[0].clone(), w[1].clone()]);
                        v.push(self.with(vec![(var.clone(), pair)], |l| l.prop(pred))?);
                    }
                    and(v)
                }
                Method::IsSome(o) => format!("((_ is some) {})", self.opt(o)?),
                Method::IsNone(o) => format!("((_ is none) {})", self.opt(o)?),
                Method::ContainsKey(..) => return Err("maps are not smoke-tested".into()),
                _ => {
                    let v = self.term(e)?;
                    match v {
                        Val::Bool(b) => b,
                        _ => return Err("not a boolean constraint".into()),
                    }
                }
            },
            ExprKind::Call(f, args) => {
                // a call in a nested boolean position: inline with a fresh output
                let d = *self.decls.get(f).ok_or_else(|| format!("unknown function `{f}`"))?;
                let outs = d.outputs();
                if outs.len() == 1 && outs[0].1 == RType::Bool {
                    self.inline_call(f, args, Val::Bool("true".into()))?
                } else {
                    return Err(format!("`{f}` used as a proposition but it does not return bool"));
                }
            }
            _ => match self.term(e)? {
                Val::Bool(b) => b,
                _ => return Err("not a boolean constraint".into()),
            },
        })
    }

    fn val_eq(&mut self, a: &Val, b: &Val) -> R<String> {
        Ok(match (a, b) {
            (Val::Int(x), Val::Int(y)) => format!("(= {} {})", x.s(), y.s()),
            (Val::Bool(x), Val::Bool(y)) | (Val::Opt(x), Val::Opt(y)) | (Val::Data(x, _), Val::Data(y, _)) => format!("(= {x} {y})"),
            (Val::Seq(x), Val::Seq(y)) => {
                if x.len() != y.len() {
                    "false".into()
                } else {
                    let mut v = Vec::new();
                    for (p, q) in x.iter().zip(y.iter()) {
                        v.push(self.val_eq(p, q)?);
                    }
                    and(v)
                }
            }
            _ => return Err("equality between values of different kinds".into()),
        })
    }

    fn seq(&mut self, e: &Expr) -> R<Vec<Val>> {
        match self.term(e)? {
            Val::Seq(v) => Ok(v),
            _ => Err("expected a sequence".into()),
        }
    }
    fn num(&mut self, e: &Expr) -> R<IntT> {
        match self.term(e)? {
            Val::Int(t) => Ok(t),
            _ => Err("expected a number".into()),
        }
    }
    fn opt(&mut self, e: &Expr) -> R<String> {
        match self.term(e)? {
            Val::Opt(t) => Ok(t),
            _ => Err("expected an Option".into()),
        }
    }

    /// The SMT term of a value (for `ite` chains and constructor arguments).
    fn raw(v: &Val) -> R<String> {
        Ok(match v {
            Val::Int(t) => t.s(),
            Val::Bool(t) | Val::Opt(t) | Val::Data(t, _) => t.clone(),
            Val::Seq(_) => return Err("a sequence has no single SMT term".into()),
        })
    }

    fn term(&mut self, e: &Expr) -> R<Val> {
        Ok(match &e.kind {
            ExprKind::Int(s) => Val::Int(IntT::Lit(s.parse::<i64>().map_err(|_| format!("integer literal `{s}` too large"))?)),
            ExprKind::Bool(b) => Val::Bool(b.to_string()),
            ExprKind::Char(c) => Val::Int(IntT::Lit(*c as i64)),
            ExprKind::Str(b) => Val::Seq(b.iter().map(|x| Val::Int(IntT::Lit(*x as i64))).collect()),
            ExprKind::Var(v) => {
                let name = if self.pre_scope && self.muts.contains(v) { format!("{v}_old") } else { v.clone() };
                match self.env.get(&name).cloned() {
                    Some(val) => val,
                    None => {
                        if let Some(c) = self.types.consts.get(v).cloned() {
                            if let Some(elems) = &c.table {
                                if elems.len() > TABLE_LIMIT {
                                    return Err(format!("the table `{v}` has {} elements; smoke-test expands tables of at most {TABLE_LIMIT}", elems.len()));
                                }
                                Val::Seq(elems.iter().map(|x| Val::Int(match x.parse::<i64>() { Ok(n) => IntT::Lit(n), Err(_) => IntT::Term(smt_int(x)) })).collect())
                            } else {
                                self.term(&c.value)?
                            }
                        } else {
                            return Err(format!("unknown variable `{v}`"));
                        }
                    }
                }
            }
            ExprKind::Old(v) => self.env.get(&format!("{v}_old")).cloned().ok_or_else(|| format!("`old({v})`: not a `&mut` parameter"))?,
            ExprKind::Neg(x) => {
                let t = self.num(x)?;
                Val::Int(arith("-", &IntT::Lit(0), &t))
            }
            ExprKind::Cast(x, t) => {
                let v = self.term(x)?;
                match (&v, t) {
                    (Val::Int(_), RType::Int { .. } | RType::Char) => v,
                    _ => return Err("unsupported cast".into()),
                }
            }
            ExprKind::Bin(op @ (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor), l, r) => {
                let a = self.num(l)?;
                let b = self.num(r)?;
                for x in [&a, &b] {
                    if x.lit().map(|n| n < 0).unwrap_or(true) {
                        self.guard(format!("(>= {} 0)", x.s()), "a negative operand of `&`, `|` or `^`".into());
                    }
                }
                if let (Some(x), Some(y)) = (a.lit(), b.lit()) {
                    if x >= 0 && y >= 0 {
                        return Ok(Val::Int(IntT::Lit(match op {
                            BinOp::BitAnd => x & y,
                            BinOp::BitOr => x | y,
                            _ => x ^ y,
                        })));
                    }
                }
                let f = match op {
                    BinOp::BitAnd => "bvand",
                    BinOp::BitOr => "bvor",
                    _ => "bvxor",
                };
                // the operands' common width when both are evidently below
                // it (they are non-negative by the guard), else 128 bits
                let w = match (self.value_width(l, &a), self.value_width(r, &b)) {
                    (Some(x), Some(y)) => x.max(y),
                    _ => 128,
                };
                let bv = format!("({f} {} {})", self.to_bv(&a, w), self.to_bv(&b, w));
                Val::Int(self.from_bv(bv, w))
            }
            ExprKind::Bin(op @ (BinOp::Shl | BinOp::Shr), l, r) => {
                let a = self.num(l)?;
                let n = self.num(r)?;
                let shl = *op == BinOp::Shl;
                let pow = |k: i64| {
                    let p = 1i128 << k;
                    match i64::try_from(p) {
                        Ok(v) => IntT::Lit(v),
                        Err(_) => IntT::Term(p.to_string()),
                    }
                };
                let sym = if shl { "*" } else { "div" };
                // the semantics is Lean's (lower.rs): `a <<< n` and `a >>> n` on
                // a natural number, `a * 2^n` and `a / 2^n` (floor) on an
                // integer — no limit on `n` — and `n ≥ 0` is the obligation
                if let Some(k) = n.lit() {
                    // a right shift of a value known to be a bit vector stays one
                    if !shl && a.lit().is_none() {
                        if let Some(w) = self.unsigned_width(l, &a) {
                            if k >= w as i64 {
                                return Ok(Val::Int(IntT::Lit(0)));
                            }
                            if k >= 0 {
                                let bv = format!("(bvlshr {} ((_ int2bv {w}) {k}))", self.to_bv(&a, w));
                                return Ok(Val::Int(self.from_bv(bv, w)));
                            }
                        }
                    }
                    if !(0..=126).contains(&k) {
                        return Err(format!("shift amount {k} is outside what smoke-test expands (0..=126)"));
                    }
                    return Ok(Val::Int(arith(sym, &a, &pow(k))));
                }
                self.guard(format!("(>= {} 0)", n.s()), "a negative shift amount".into());
                // an unsigned machine value shifts as a bit vector: `>>` at its
                // width (0 once the amount reaches it), `<<` at its width plus
                // the amount's largest value when the amount is a machine value
                // of at most 9 bits, else at 128 bits (exact while the result
                // fits: a limit beyond)
                if let Some(w) = self.unsigned_width(l, &a) {
                    if shl {
                        let exact = self.unsigned_width(r, &n).filter(|wn| *wn <= 9).map(|wn| w + (1u32 << wn) - 1);
                        let ww = match exact {
                            Some(ww) => ww.max(128),
                            None => {
                                self.limit(format!("(<= {} {})", n.s(), 128 - w), "a left shift past 128 bits".into());
                                128
                            }
                        };
                        let bv = format!("(bvshl {} {})", self.to_bv(&a, ww), self.to_bv(&n, ww));
                        return Ok(Val::Int(self.from_bv(bv, ww)));
                    }
                    let bv = format!("(ite (< {} {w}) (bvlshr {} {}) (_ bv0 {w}))", n.s(), self.to_bv(&a, w), self.to_bv(&n, w));
                    return Ok(Val::Int(self.from_bv(bv, w)));
                }
                // otherwise one case per amount up to 126; beyond, `>>` of a
                // value within 126 bits is exactly 0 or -1, and `<<` is a limit
                let beyond = if shl {
                    self.limit(format!("(<= {} 126)", n.s()), "a left shift by more than 126 bits".into());
                    arith("*", &a, &pow(126)).s()
                } else {
                    let h = 1i128 << 126;
                    self.limit(format!("(or (<= {} 126) (and (<= (- {h}) {}) (< {} {h})))", n.s(), a.s(), a.s()), "a right shift by more than 126 bits of a value of more than 126 bits".into());
                    format!("(ite (>= {} 0) 0 (- 1))", a.s())
                };
                let mut t = beyond;
                for k in (0..=126).rev() {
                    t = format!("(ite (= {} {k}) {} {t})", n.s(), arith(sym, &a, &pow(k)).s());
                }
                Val::Int(IntT::Term(t))
            }
            ExprKind::Bin(op, l, r) if op.is_arith() => {
                let a = self.num(l)?;
                let b = self.num(r)?;
                // the low `k` bits of a bit vector: a remainder by `2^k`
                if *op == BinOp::Rem {
                    let vector = self.bvs.get(&a.s()).map(|(_, w)| *w).or_else(|| BV_DECLARED.with(|m| m.borrow().get(&a.s()).copied()));
                    if let (Some(w), Ok(m)) = (vector, b.s().parse::<u128>()) {
                        if m.is_power_of_two() && a.lit().is_none() {
                            let k = m.trailing_zeros();
                            if k == 0 {
                                return Ok(Val::Int(IntT::Lit(0)));
                            }
                            if w <= k {
                                return Ok(Val::Int(a));
                            }
                            let bv = format!("((_ extract {} 0) {})", k - 1, self.to_bv(&a, w));
                            return Ok(Val::Int(self.from_bv(bv, k)));
                        }
                    }
                }
                let (sym, guard) = match op {
                    BinOp::Add => ("+", false),
                    BinOp::Sub => ("-", false),
                    BinOp::Mul => ("*", false),
                    BinOp::Div => ("div", true),
                    BinOp::Rem => ("mod", true),
                    _ => unreachable!(),
                };
                if guard {
                    self.guard(format!("(distinct {} 0)", b.s()), "division by zero".into());
                }
                Val::Int(arith(sym, &a, &b))
            }
            ExprKind::Ctor(c, args) => {
                self.needs_opt = true;
                match (c.as_str(), args.as_slice()) {
                    ("None", []) => Val::Opt("none".into()),
                    ("Some", [x]) => match self.term(x)? {
                        Val::Int(t) => Val::Opt(format!("(some {})", t.s())),
                        _ => return Err("only `Some(<integer>)` is supported by smoke-test".into()),
                    },
                    _ => return Err("`Ok`/`Err` are not supported by smoke-test".into()),
                }
            }
            ExprKind::Variant { enum_name, variant, fields } => {
                let edef = self.types.enums.get(enum_name).ok_or_else(|| format!("unknown enum `{enum_name}`"))?.clone();
                let vdef = edef.variants.iter().find(|v| &v.name == variant).ok_or_else(|| format!("no variant `{variant}`"))?;
                self.use_datatype(enum_name);
                let mut ordered: Vec<Option<&Expr>> = vec![None; vdef.fields.len()];
                for (k, (fname, fe)) in fields.iter().enumerate() {
                    let i = match fname {
                        None => k,
                        Some(f) => vdef.fields.iter().position(|(n, _)| n.as_deref() == Some(f.as_str())).ok_or_else(|| format!("no field `{f}`"))?,
                    };
                    if i < ordered.len() {
                        ordered[i] = Some(fe);
                    }
                }
                let mut ts = Vec::new();
                for fe in ordered {
                    let fe = fe.ok_or("missing constructor field")?;
                    let v = self.term(fe)?;
                    ts.push(Self::raw(&v)?);
                }
                Val::Data(if ts.is_empty() { variant.clone() } else { format!("({variant} {})", ts.join(" ")) }, enum_name.clone())
            }
            ExprKind::Field(..) => return Err("struct fields are not supported by smoke-test".into()),
            ExprKind::Index(s, i) => {
                let elems = self.seq(s)?;
                let idx = self.num(i)?;
                let n = elems.len() as i64;
                self.guard(format!("(and (<= 0 {}) (< {} {n}))", idx.s(), idx.s()), format!("index {} within length {n}", idx.s()));
                if let Some(k) = idx.lit() {
                    if k >= 0 && k < n {
                        elems[k as usize].clone()
                    } else {
                        // out of bounds: the guard fails; the value is arbitrary
                        self.default_elem(&elems)
                    }
                } else if elems.is_empty() {
                    Val::Int(IntT::Lit(0))
                } else {
                    // ite chain over the elements (all of one kind)
                    let mut t = Self::raw(&elems[0])?;
                    for (k, el) in elems.iter().enumerate().skip(1) {
                        t = format!("(ite (= {} {k}) {} {t})", idx.s(), Self::raw(el)?);
                    }
                    match &elems[0] {
                        Val::Int(_) => Val::Int(IntT::Term(t)),
                        Val::Bool(_) => Val::Bool(t),
                        Val::Opt(_) => Val::Opt(t),
                        Val::Data(_, en) => Val::Data(t, en.clone()),
                        Val::Seq(_) => return Err("symbolic indexing into a sequence of sequences".into()),
                    }
                }
            }
            ExprKind::Slice(s, a, b) => {
                let elems = self.seq(s)?;
                let a = self.num(a)?;
                let b = self.num(b)?;
                let n = elems.len() as i64;
                self.guard(format!("(and (<= 0 {}) (<= {} {}) (<= {} {n}))", a.s(), a.s(), b.s(), b.s()), "slice bounds".into());
                match (a.lit(), b.lit()) {
                    (Some(x), Some(y)) if 0 <= x && x <= y && y <= n => Val::Seq(elems[x as usize..y as usize].to_vec()),
                    _ => return Err("slicing with symbolic bounds is not supported by smoke-test".into()),
                }
            }
            ExprKind::IfVal(c, a, b) => {
                let cp = self.prop(c)?;
                // each branch's partial operations are owed only where it is taken
                self.cx.push(cp.clone());
                let av = self.term(a);
                self.cx.pop();
                self.cx.push(not(&cp));
                let bv = self.term(b);
                self.cx.pop();
                let (av, bv) = (av?, bv?);
                match (av, bv) {
                    (Val::Int(x), Val::Int(y)) => Val::Int(IntT::Term(format!("(ite {cp} {} {})", x.s(), y.s()))),
                    (Val::Bool(x), Val::Bool(y)) => Val::Bool(format!("(ite {cp} {x} {y})")),
                    (Val::Opt(x), Val::Opt(y)) => Val::Opt(format!("(ite {cp} {x} {y})")),
                    (Val::Data(x, en), Val::Data(y, _)) => Val::Data(format!("(ite {cp} {x} {y})"), en),
                    _ => return Err("`if` branches of different kinds".into()),
                }
            }
            ExprKind::Method(m) => match &**m {
                Method::Len(s) => Val::Int(IntT::Lit(self.seq(s)?.len() as i64)),
                Method::Count { seq, var, pred } => {
                    let elems = self.seq(seq)?;
                    let mut v = Vec::new();
                    for el in elems {
                        let p = self.with(vec![(var.clone(), el)], |l| l.prop(pred))?;
                        v.push(format!("(ite {p} 1 0)"));
                    }
                    Val::Int(if v.is_empty() { IntT::Lit(0) } else { IntT::Term(format!("(+ 0 {})", v.join(" "))) })
                }
                Method::Sum(s) => {
                    let elems = self.seq(s)?;
                    let mut v = Vec::new();
                    for el in elems {
                        match el {
                            Val::Int(t) => v.push(t.s()),
                            _ => return Err("`.sum()` over non-integers".into()),
                        }
                    }
                    Val::Int(if v.is_empty() { IntT::Lit(0) } else { IntT::Term(format!("(+ 0 {})", v.join(" "))) })
                }
                Method::First(s) | Method::Last(s) => {
                    self.needs_opt = true;
                    let elems = self.seq(s)?;
                    let pick = if matches!(&**m, Method::First(_)) { elems.first() } else { elems.last() };
                    match pick {
                        None => Val::Opt("none".into()),
                        Some(Val::Int(t)) => Val::Opt(format!("(some {})", t.s())),
                        _ => return Err("`.first()`/`.last()` over non-integers".into()),
                    }
                }
                Method::Abs(x) => {
                    let t = self.num(x)?;
                    Val::Int(match t.lit() {
                        Some(k) => IntT::Lit(k.abs()),
                        None => IntT::Term(format!("(ite (< {} 0) (- {}) {})", t.s(), t.s(), t.s())),
                    })
                }
                Method::Min(a, b) | Method::Max(a, b) => {
                    let x = self.num(a)?;
                    let y = self.num(b)?;
                    let is_min = matches!(&**m, Method::Min(..));
                    Val::Int(match (x.lit(), y.lit()) {
                        (Some(p), Some(q)) => IntT::Lit(if is_min { p.min(q) } else { p.max(q) }),
                        _ => IntT::Term(format!("(ite ({} {} {}) {} {})", if is_min { "<=" } else { ">=" }, x.s(), y.s(), x.s(), y.s())),
                    })
                }
                Method::Pow(a, n) => {
                    let x = self.num(a)?;
                    let k = self.num(n)?.lit().ok_or("`.pow(n)` needs a literal exponent in smoke-test")?;
                    if k < 0 {
                        return Err("negative exponent".into());
                    }
                    let mut t = IntT::Lit(1);
                    for _ in 0..k {
                        t = arith("*", &t, &x);
                    }
                    Val::Int(t)
                }
                Method::Unwrap(o) => {
                    let t = self.opt(o)?;
                    self.guard(format!("((_ is some) {t})"), "`.unwrap()` on a Some".into());
                    Val::Int(IntT::Term(format!("(val {t})")))
                }
                Method::AsBytes(s) => self.term(s)?,
                Method::BitCount(k, x) => {
                    let (signed, w) = self.int_width(x)?;
                    let v = self.num(x)?;
                    if let Some(n) = v.lit() {
                        let _ = signed;
                        return Ok(Val::Int(IntT::Lit(k.eval(n as i128 as u128, w) as i64)));
                    }
                    let bv = self.to_bv(&v, w);
                    Val::Int(IntT::Term(bit_count_smt(*k, &bv, w)))
                }
                Method::Rotate(left, x, n) => {
                    let (signed, w) = self.int_width(x)?;
                    let v = self.num(x)?;
                    let k = self.num(n)?;
                    let bv = format!("({} {} {})", if *left { "ext_rotate_left" } else { "ext_rotate_right" }, self.to_bv(&v, w), self.to_bv(&k, w));
                    if signed {
                        Val::Int(IntT::Term(to_signed(&format!("(bv2nat {bv})"), w)))
                    } else {
                        Val::Int(self.from_bv(bv, w))
                    }
                }
                Method::Wrapping(op, x, y) => {
                    let (signed, w) = self.int_width(x)?;
                    let a = self.num(x)?;
                    let b = self.num(y)?;
                    let sym = match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        _ => "*",
                    };
                    let m = format!("(mod ({sym} {} {}) {})", a.s(), b.s(), 1i128 << w.min(126));
                    if w > 126 {
                        return Err("128-bit wrapping arithmetic is not smoke-tested".into());
                    }
                    Val::Int(IntT::Term(if signed { to_signed(&m, w) } else { m }))
                }
                Method::MapGet(..) => return Err("maps are not smoke-tested".into()),
                m if m.is_prop() => Val::Bool(self.prop(e)?),
                _ => return Err("unsupported method in smoke-test".into()),
            },
            ExprKind::Call(f, args) => {
                // nested call in value position: fresh output symbol + the callee's spec as a side constraint
                let d = *self.decls.get(f).ok_or_else(|| format!("unknown function `{f}`"))?;
                let outs = d.outputs();
                if outs.len() != 1 {
                    return Err(format!("`{f}` must have one output to be used as a value"));
                }
                let out = match &outs[0].1 {
                    RType::Int { .. } | RType::MathInt | RType::Char => {
                        let nm = format!("{f}_out{}", self.fresh);
                        self.fresh += 1;
                        self.decls_out.push(format!("(declare-const {nm} Int)"));
                        if let Some(r) = scalar_range(&outs[0].1) {
                            self.side.push(format!("(and (<= {} {nm}) (<= {nm} {}))", big(r.0), big(r.1)));
                        }
                        Val::Int(IntT::Term(nm))
                    }
                    RType::Bool => {
                        let nm = format!("{f}_out{}", self.fresh);
                        self.fresh += 1;
                        self.decls_out.push(format!("(declare-const {nm} Bool)"));
                        Val::Bool(nm)
                    }
                    RType::Named(en) if self.types.enums.contains_key(en) => {
                        self.use_datatype(en);
                        let nm = format!("{f}_out{}", self.fresh);
                        self.fresh += 1;
                        self.decls_out.push(format!("(declare-const {nm} {en})"));
                        let rs = data_ranges(&nm, en, self.types, false, self.bounds.int_bound);
                        self.side.extend(rs);
                        Val::Data(nm, en.clone())
                    }
                    _ => return Err(format!("nested call to `{f}` returning a sequence/Option is not supported; write `{f}(..) == v;`")),
                };
                let spec = self.inline_call(f, args, out.clone())?;
                self.side.push(spec);
                out
            }
            ExprKind::Not(_) | ExprKind::Bin(..) | ExprKind::In(..) | ExprKind::InRange(..) | ExprKind::InDomain(..) => Val::Bool(self.prop(e)?),
        })
    }

    fn default_elem(&self, elems: &[Val]) -> Val {
        match elems.first() {
            Some(Val::Bool(_)) => Val::Bool("false".into()),
            Some(Val::Opt(_)) => Val::Opt("none".into()),
            Some(Val::Data(_, en)) => {
                let v = self.types.enums.get(en).and_then(|e| e.variants.iter().find(|v| v.fields.is_empty())).map(|v| v.name.clone());
                match v {
                    Some(v) => Val::Data(v, en.clone()),
                    None => Val::Data(format!("default_{en}"), en.clone()),
                }
            }
            _ => Val::Int(IntT::Lit(0)),
        }
    }
}

fn smoke_proplike(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Bin(op, _, _) => op.is_cmp() || matches!(op, BinOp::And | BinOp::Or),
        ExprKind::Not(_) | ExprKind::In(..) | ExprKind::InRange(..) | ExprKind::InDomain(..) => true,
        ExprKind::Method(m) => m.is_prop(),
        _ => false,
    }
}

// ----------------------------------------------------------------- the checks

/// A declared symbolic variable of a declaration (input or output).
struct Sym {
    name: String,
    ty: RType,
    /// SMT symbols backing it (one for scalars, one per element for sequences)
    smt: Vec<String>,
}

thread_local! {
    /// Declare machine integers as bit vectors (their `Int` defined from
    /// them): set for programs that use bit operations, where Z3 is fast on
    /// bit vectors and gives up on `int2bv` of plain integers.
    static BV_SYMBOLS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The unsigned symbols declared as bit vectors in the current query,
    /// with their widths: `x` is `(bv2nat x_bv)`.
    static BV_DECLARED: std::cell::RefCell<HashMap<String, u32>> = std::cell::RefCell::new(HashMap::new());
}

/// Start a query: bit-vector symbols if `d` uses bit operations.
fn bv_query(d: &Decl) {
    BV_SYMBOLS.with(|c| c.set(d.uses_bitwise()));
    BV_DECLARED.with(|m| m.borrow_mut().clear());
}

/// Declare `nm` as an integer of type `t`, with its range when `small` asks
/// for one (`range` adds it to `side`): a plain `Int`, or, for a machine
/// integer in a declaration with bit operations, the value of a bit vector.
/// A bit vector's range is its width, and a small range is stated on the
/// vector (Z3 gives up on integer bounds of `bv2nat` terms).
#[allow(clippy::too_many_arguments)]
fn declare_int(nm: &str, t: &RType, quantified: bool, small: bool, int_bound: i64, decls: &mut Vec<String>, side: &mut Vec<String>, range: &dyn Fn(&str, &RType, &mut Vec<String>)) {
    match t {
        RType::Int { signed, bits } if !quantified && BV_SYMBOLS.with(|c| c.get()) => {
            let w = if *bits == 0 { 64 } else { *bits };
            decls.push(format!("(declare-const {nm}_bv (_ BitVec {w}))"));
            let u = format!("(bv2nat {nm}_bv)");
            decls.push(format!("(define-fun {nm} () Int {})", if *signed { to_signed(&u, w) } else { u }));
            if !*signed {
                BV_DECLARED.with(|m| m.borrow_mut().insert(nm.to_string(), w));
            }
            if small {
                let b = format!("(_ bv{int_bound} {w})");
                side.push(if *signed { format!("(and (bvsle (bvneg {b}) {nm}_bv) (bvsle {nm}_bv {b}))") } else { format!("(bvule {nm}_bv {b})") });
            }
        }
        _ => {
            decls.push(format!("(declare-const {nm} Int)"));
            range(nm, t, side);
        }
    }
}

/// Declare a symbolic variable. Range constraints go to `side`; with
/// `quantified`, no `declare-const` is emitted (the caller binds the names).
#[allow(clippy::too_many_arguments)]
fn declare(prefix: &str, name: &str, ty: &RType, len: usize, decls: &mut Vec<String>, small: bool, int_bound: i64, side: &mut Vec<String>, needs_opt: &mut bool, quantified: bool, types: &TypeDefs, dts: &mut Vec<String>) -> R<(Sym, Val)> {
    let mut decls_local: Vec<String> = Vec::new();
    let decls: &mut Vec<String> = if quantified { &mut decls_local } else { decls };
    let mut use_dt = |n: &str| {
        if !dts.iter().any(|x| x == n) {
            dts.push(n.to_string());
        }
    };
    let range_assert = |nm: &str, t: &RType, side: &mut Vec<String>| {
        if let Some((lo, hi)) = scalar_range(t) {
            let (lo, hi) = if small { (lo.max(-(int_bound as i128)), hi.min(int_bound as i128)) } else { (lo, hi) };
            side.push(format!("(and (<= {} {nm}) (<= {nm} {}))", big(lo), big(hi)));
        }
    };
    Ok(match ty {
        RType::Int { .. } | RType::Char => {
            let nm = format!("{prefix}{name}");
            declare_int(&nm, ty, quantified, small, int_bound, decls, side, &range_assert);
            (Sym { name: name.into(), ty: ty.clone(), smt: vec![nm.clone()] }, Val::Int(IntT::Term(nm)))
        }
        RType::Named(en) if types.enums.contains_key(en) => {
            use_dt(en);
            let nm = format!("{prefix}{name}");
            decls.push(format!("(declare-const {nm} {en})"));
            side.extend(data_ranges(&nm, en, types, small, int_bound));
            (Sym { name: name.into(), ty: ty.clone(), smt: vec![nm.clone()] }, Val::Data(nm, en.clone()))
        }
        RType::MathInt => {
            let nm = format!("{prefix}{name}");
            decls.push(format!("(declare-const {nm} Int)"));
            if small {
                side.push(format!("(and (<= (- {int_bound}) {nm}) (<= {nm} {int_bound}))"));
            }
            (Sym { name: name.into(), ty: ty.clone(), smt: vec![nm.clone()] }, Val::Int(IntT::Term(nm)))
        }
        RType::Bool => {
            let nm = format!("{prefix}{name}");
            decls.push(format!("(declare-const {nm} Bool)"));
            (Sym { name: name.into(), ty: ty.clone(), smt: vec![nm.clone()] }, Val::Bool(nm))
        }
        RType::Option(inner) if matches!(**inner, RType::Int { .. }) => {
            *needs_opt = true;
            let nm = format!("{prefix}{name}");
            decls.push(format!("(declare-const {nm} OptInt)"));
            if let Some((lo, hi)) = scalar_range(inner) {
                let (lo, hi) = if small { (lo.max(-(int_bound as i128)), hi.min(int_bound as i128)) } else { (lo, hi) };
                side.push(format!("(=> ((_ is some) {nm}) (and (<= {} (val {nm})) (<= (val {nm}) {})))", big(lo), big(hi)));
            }
            (Sym { name: name.into(), ty: ty.clone(), smt: vec![nm.clone()] }, Val::Opt(nm))
        }
        RType::Seq(elem, _) => {
            let mut smt = Vec::new();
            let mut vals = Vec::new();
            for k in 0..len {
                let nm = format!("{prefix}{name}_{k}");
                match &**elem {
                    RType::Int { .. } | RType::Char => {
                        declare_int(&nm, elem, quantified, small, int_bound, decls, side, &range_assert);
                        vals.push(Val::Int(IntT::Term(nm.clone())));
                    }
                    RType::Bool => {
                        decls.push(format!("(declare-const {nm} Bool)"));
                        vals.push(Val::Bool(nm.clone()));
                    }
                    RType::Named(en) if types.enums.contains_key(en) => {
                        use_dt(en);
                        decls.push(format!("(declare-const {nm} {en})"));
                        side.extend(data_ranges(&nm, en, types, small, int_bound));
                        vals.push(Val::Data(nm.clone(), en.clone()));
                    }
                    _ => return Err(format!("sequence elements of type {} are not supported by smoke-test", djinn_syntax::types::rust_type(elem))),
                }
                smt.push(nm);
            }
            (Sym { name: name.into(), ty: ty.clone(), smt }, Val::Seq(vals))
        }
        other => return Err(format!("type {} is not supported by smoke-test", djinn_syntax::types::rust_type(other))),
    })
}

fn show(sym: &Sym, model: &HashMap<String, String>) -> String {
    match &sym.ty {
        RType::Seq(..) => format!("[{}]", sym.smt.iter().map(|s| model.get(s).cloned().unwrap_or("?".into())).collect::<Vec<_>>().join(", ")),
        _ => model.get(&sym.smt[0]).cloned().unwrap_or("?".into()),
    }
}

/// A rendered model value back to SMT syntax.
fn raw_value(val: &str) -> String {
    if let Some(n) = val.strip_prefix('-') {
        format!("(- {n})")
    } else if let Some(x) = val.strip_prefix("Some(").and_then(|x| x.strip_suffix(')')) {
        format!("(some {})", raw_value(x))
    } else if val == "None" {
        "none".into()
    } else {
        val.to_string()
    }
}

fn block(syms: &[Sym], model: &HashMap<String, String>) -> String {
    let mut eqs = Vec::new();
    for s in syms {
        for v in &s.smt {
            if let Some(val) = model.get(v) {
                eqs.push(format!("(= {v} {})", raw_value(val)));
            }
        }
    }
    format!("(assert (not {}))", and(eqs))
}

/// Which statements cannot hold together: a minimal unsatisfiable subset of
/// the `requires` clauses and top-level body statements, found through Z3's
/// unsat core and shrunk by deletion. With `fixed`, the inputs are pinned to
/// a model (an input that admits no output). Returns `None` when the
/// statements are satisfiable at these lengths.
#[allow(clippy::too_many_arguments)]
fn explain(
    z3: &mut Z3,
    d: &Decl,
    decls: &HashMap<String, &Decl>,
    types: &TypeDefs,
    bounds: &Bounds,
    small: bool,
    lens: &HashMap<String, usize>,
    fixed: Option<&HashMap<String, String>>,
) -> R<Option<(Vec<(bool, usize)>, Option<String>)>> {
    bv_query(d);
    let mut lo = Lo {
        decls,
        types,
        bounds,
        small,
        env: HashMap::new(),
        vtypes: d.inputs().into_iter().chain(d.outputs()).collect(),
        bvs: HashMap::new(),
        pre_scope: true,
        muts: d.params.iter().filter(|p| p.mut_ref).map(|p| p.name.clone()).collect(),
        decls_out: Vec::new(),
        side: Vec::new(),
        wf: Vec::new(),
        limits: Vec::new(),
        cx: Vec::new(),
        quant: Vec::new(),
        fresh: 0,
        needs_opt: false,
        datatypes: Vec::new(),
        depth: 0,
        binds: Vec::new(),
        choice_fns: Vec::new(),
        choices_local: false,
        call_seq: 0,
        site: Vec::new(),
    };
    let mut decl_lines = Vec::new();
    let mut side = Vec::new();
    let mut needs_opt = false;
    let mut dts = Vec::new();
    let mut inputs = Vec::new();
    for (n, t) in d.inputs() {
        let len = *lens.get(&n).unwrap_or(&0);
        let (sym, val) = declare("", &n, &t, len, &mut decl_lines, small, bounds.int_bound, &mut side, &mut needs_opt, false, types, &mut dts)?;
        lo.env.insert(n.clone(), val);
        inputs.push(sym);
    }
    // (name, term, is_requires, index)
    let mut named: Vec<(String, String, bool, usize)> = Vec::new();
    for (k, e) in d.requires.iter().enumerate() {
        let t = lo.constraint(e)?;
        named.push((format!("req_{k}"), t, true, k));
    }
    lo.pre_scope = false;
    for (n, t) in d.outputs() {
        let len = *lens.get(&n).unwrap_or(&0);
        let (_, val) = declare("", &n, &t, len, &mut decl_lines, false, bounds.int_bound, &mut side, &mut needs_opt, false, types, &mut dts)?;
        lo.env.insert(n.clone(), val);
    }
    for (k, st) in d.body.iter().enumerate() {
        let t = lo.stmt(st)?;
        named.push((format!("stmt_{k}"), t, false, k));
    }
    let mut header = String::new();
    if needs_opt || lo.needs_opt {
        header.push_str("(declare-datatype OptInt ((none) (some (val Int))))\n");
    }
    dts.extend(lo.datatypes.iter().cloned());
    for l in datatype_decls(&dts, types)? {
        header.push_str(&l);
        header.push('\n');
    }
    for l in decl_lines.iter().chain(lo.decls_out.iter()) {
        header.push_str(l);
        header.push('\n');
    }
    for c in side.iter().chain(lo.side.iter()) {
        header.push_str(&format!("(assert {c})\n"));
    }
    if let Some(m) = fixed {
        for sym in &inputs {
            for v in &sym.smt {
                if let Some(val) = m.get(v) {
                    header.push_str(&format!("(assert (= {v} {}))\n", raw_value(val)));
                }
            }
        }
    }
    let run = |z3: &mut Z3, subset: &[usize]| -> String {
        z3.send("(reset)");
        z3.send(&format!("(set-option :timeout {})", bounds.timeout_ms));
        z3.send("(set-option :produce-models true)");
        z3.send("(set-option :produce-unsat-cores true)");
        for line in header.lines() {
            z3.send(line);
        }
        for &i in subset {
            let (name, term, _, _) = &named[i];
            z3.send(&format!("(assert (! {term} :named {name}))"));
        }
        z3.check_sat()
    };
    let all: Vec<usize> = (0..named.len()).collect();
    if !run(z3, &all).starts_with("unsat") {
        return Ok(None);
    }
    z3.send("(get-unsat-core)");
    let core_text = z3.read();
    let mut core: Vec<usize> = core_text
        .trim_matches(|c| c == '(' || c == ')')
        .split_whitespace()
        .filter_map(|nm| named.iter().position(|(n, _, _, _)| n == nm))
        .collect();
    if core.is_empty() {
        core = all.clone();
    }
    core.sort();
    // shrink by deletion
    let mut i = 0;
    while i < core.len() && core.len() > 1 {
        let trial: Vec<usize> = core.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, &x)| x).collect();
        if run(z3, &trial).starts_with("unsat") {
            core = trial;
        } else {
            i += 1;
        }
    }
    // an example input admitted by the requires clauses alone
    let reqs: Vec<usize> = all.iter().copied().filter(|&i| named[i].2).collect();
    let example = if fixed.is_none() && run(z3, &reqs).starts_with("sat") {
        let vars: Vec<String> = inputs.iter().flat_map(|s| s.smt.clone()).collect();
        let m = z3.get_value(&vars);
        let ins = inputs.iter().map(|s| format!("{} = {}", s.name, show(s, &m))).collect::<Vec<_>>().join(", ");
        if ins.is_empty() { None } else { Some(ins) }
    } else {
        None
    };
    Ok(Some((core.into_iter().map(|i| (named[i].2, named[i].3)).collect(), example)))
}

fn conflict_title(n: usize, at_input: bool) -> &'static str {
    match (n, at_input) {
        (1, false) => "this statement is unsatisfiable on its own:",
        (1, true) => "at this input, this statement is unsatisfiable on its own:",
        (_, false) => "these statements cannot hold together:",
        (_, true) => "at this input, these statements cannot hold together:",
    }
}

struct Query {
    text: String,
    inputs: Vec<Sym>,
    outputs: Vec<Vec<Sym>>, // one group per copy of the outputs
    /// named violation flags (well-formedness only): (smt name, description)
    wf_flags: Vec<(String, String)>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Check {
    /// the preconditions alone (to tell "contradictory" from "unreachable within the bounds")
    PreSat,
    Consistent,
    /// an input admitted by the precondition for which NO output satisfies the relation
    Existence,
    Unambiguous,
    Ensures(usize),
    Wf,
    /// can the declaration reach a limit of the encoding (`Lo::limits`)?
    /// The specification is not asserted (its encoding is not exact there):
    /// the preconditions and the limits' own path conditions only
    Limits,
}

/// Build a query for one declaration, one assignment of sequence lengths
/// (indexed by variable name) and one integer regime.
fn build(d: &Decl, decls: &HashMap<String, &Decl>, types: &TypeDefs, bounds: &Bounds, small: bool, lens: &HashMap<String, usize>, check: Check) -> R<Query> {
    bv_query(d);
    let mut lo = Lo {
        decls,
        types,
        bounds,
        small,
        env: HashMap::new(),
        vtypes: d.inputs().into_iter().chain(d.outputs()).collect(),
        bvs: HashMap::new(),
        pre_scope: true,
        muts: d.params.iter().filter(|p| p.mut_ref).map(|p| p.name.clone()).collect(),
        decls_out: Vec::new(),
        side: Vec::new(),
        wf: Vec::new(),
        limits: Vec::new(),
        cx: Vec::new(),
        quant: Vec::new(),
        fresh: 0,
        needs_opt: false,
        datatypes: Vec::new(),
        depth: 0,
        binds: Vec::new(),
        choice_fns: Vec::new(),
        choices_local: false,
        call_seq: 0,
        site: Vec::new(),
    };
    let mut decl_lines = Vec::new();
    let mut side = Vec::new();
    let mut needs_opt = false;
    let mut dts = Vec::new();
    let mut inputs = Vec::new();
    for (n, t) in d.inputs() {
        let len = *lens.get(&n).unwrap_or(&0);
        let (sym, val) = declare("", &n, &t, len, &mut decl_lines, small, bounds.int_bound, &mut side, &mut needs_opt, false, types, &mut dts)?;
        lo.env.insert(n.clone(), val);
        inputs.push(sym);
    }
    // the implementer's choices at the top level of the body (under no
    // binder): free symbols like the inputs — shared by both copies of the
    // unambiguity query, universal for `ensures` and well-formedness — and
    // quantified with the outputs in the existence check (below); a choice
    // under a binder is an uninterpreted function of it (`any_block`)
    lo.choices_local = check == Check::Existence;
    let top_choices: Vec<(String, RType)> = top_choices(d);
    if check != Check::Existence {
        for (n, t) in &top_choices {
            let len = *lens.get(n).unwrap_or(&0);
            let (mut sym, val) = declare("", n, t, len, &mut decl_lines, small, bounds.int_bound, &mut side, &mut needs_opt, false, types, &mut dts)?;
            sym.name = format!("any {n}");
            lo.env.insert(n.clone(), val);
            inputs.push(sym);
        }
    }
    let mut pre = Vec::new();
    for e in &d.requires {
        pre.push(lo.constraint(e)?);
    }
    let pre_s = and(pre);
    lo.pre_scope = false;
    let copies = if check == Check::Unambiguous { 2 } else { 1 };
    let mut outputs = Vec::new();
    let mut specs = Vec::new();
    let mut ens: Vec<Vec<String>> = Vec::new();
    // existence: ∧ over output lengths of ∀ outputs. ¬spec
    let mut existence_parts: Vec<String> = Vec::new();
    if check == Check::Existence {
        let out_seq: Vec<(String, RType)> = d.outputs().into_iter().chain(top_choices.iter().cloned()).filter(|(_, t)| t.is_seq()).collect();
        let out_max = output_len_bound(d, bounds.max_len);
        let mut out_lens = vec![HashMap::new()];
        for (v, _) in &out_seq {
            let mut next = Vec::new();
            for a in &out_lens {
                for len in 0..=out_max {
                    let mut b = a.clone();
                    b.insert(v.clone(), len);
                    next.push(b);
                }
            }
            out_lens = next;
        }
        for ol in out_lens {
            let mut qvars = Vec::new();
            let mut ranges = Vec::new();
            let mut binds = Vec::new();
            let mut dummy = Vec::new();
            for (n, t) in d.outputs().into_iter().chain(top_choices.iter().cloned()) {
                let len = *ol.get(&n).unwrap_or(&0);
                let (sym, val) = declare("q_", &n, &t, len, &mut dummy, false, bounds.int_bound, &mut ranges, &mut needs_opt, true, types, &mut dts)?;
                let sort: String = match &t {
                    RType::Seq(e, _) => sort_of(e, types)?,
                    other => sort_of(other, types)?,
                };
                for nm in &sym.smt {
                    qvars.push(format!("({nm} {sort})"));
                }
                binds.push((n.clone(), val));
            }
            for (n, v) in binds {
                lo.env.insert(n, v);
            }
            lo.wf.clear();
            lo.call_seq = 0;
            let before = lo.limits.len();
            let spec = lo.stmts(&d.body)?;
            // the limits of this output's encoding are in the outputs' scope:
            // every output must be exactly encoded, and fail the relation
            let here: Vec<String> = lo.limits.drain(before..).map(|(f, _)| f).collect();
            let fails = if here.is_empty() { not(&spec) } else { and(vec![not(&or(here)), not(&spec)]) };
            let body = imp(&and(ranges), &fails);
            existence_parts.push(if qvars.is_empty() { body } else { format!("(forall ({}) {})", qvars.join(" "), body) });
        }
        outputs.push(Vec::new());
    } else {
        for c in 0..copies {
            let prefix = if copies == 2 { format!("o{}_", c + 1) } else { String::new() };
            let mut group = Vec::new();
            let mut binds = Vec::new();
            for (n, t) in d.outputs() {
                let len = *lens.get(&n).unwrap_or(&0);
                // outputs keep their full type range even in the small phase:
                // bounding them would manufacture "no output" counterexamples
                let (sym, val) = declare(&prefix, &n, &t, len, &mut decl_lines, false, bounds.int_bound, &mut side, &mut needs_opt, false, types, &mut dts)?;
                binds.push((n.clone(), val));
                group.push(sym);
            }
            for (n, v) in binds {
                lo.env.insert(n, v);
            }
            lo.wf.clear();
            lo.call_seq = 0;
            specs.push(lo.stmts(&d.body)?);
            let wf_here = std::mem::take(&mut lo.wf);
            if c == 0 {
                lo.wf = wf_here;
            }
            let mut es = Vec::new();
            for e in &d.ensures {
                es.push(lo.constraint(e)?);
            }
            ens.push(es);
            outputs.push(group);
        }
    }
    let mut wf_flags = Vec::new();
    let mut text = String::new();
    if needs_opt || lo.needs_opt {
        text.push_str("(declare-datatype OptInt ((none) (some (val Int))))\n");
    }
    dts.extend(lo.datatypes.iter().cloned());
    for l in datatype_decls(&dts, types)? {
        text.push_str(&l);
        text.push('\n');
    }
    for l in &decl_lines {
        text.push_str(l);
        text.push('\n');
    }
    for l in &lo.decls_out {
        text.push_str(l);
        text.push('\n');
    }
    for s in side.iter().chain(lo.side.iter()) {
        text.push_str(&format!("(assert {s})\n"));
    }
    text.push_str(&format!("(assert {pre_s})\n"));
    if !lo.limits.is_empty() && check != Check::Limits {
        let reached: Vec<String> = lo.limits.iter().map(|(f, _)| f.clone()).collect();
        text.push_str(&format!("(assert (not {}))\n", or(reached)));
    }
    match check {
        Check::PreSat => {}
        Check::Limits => {
            let mut hit = Vec::new();
            for (k, (formula, what)) in lo.limits.iter().enumerate() {
                let nm = format!("lim_{k}");
                text.push_str(&format!("(define-fun {nm} () Bool {})\n", formula));
                wf_flags.push((nm.clone(), what.clone()));
                hit.push(nm);
            }
            if hit.is_empty() {
                text.push_str("(assert false)\n");
                text.push_str(";; no-limits\n");
            } else {
                text.push_str(&format!("(assert {})\n", or(hit)));
            }
        }
        Check::Consistent => {
            text.push_str(&format!("(assert {})\n", specs[0]));
        }
        Check::Existence => {
            text.push_str(&format!("(assert {})\n", and(existence_parts)));
        }
        Check::Unambiguous => {
            text.push_str(&format!("(assert {})\n(assert {})\n", specs[0], specs[1]));
            let mut eqs = Vec::new();
            for (a, b) in outputs[0].iter().zip(outputs[1].iter()) {
                for (x, y) in a.smt.iter().zip(b.smt.iter()) {
                    eqs.push(format!("(= {x} {y})"));
                }
            }
            text.push_str(&format!("(assert (not {}))\n", and(eqs)));
        }
        Check::Ensures(i) => {
            text.push_str(&format!("(assert {})\n(assert (not {}))\n", specs[0], ens[0][i]));
        }
        Check::Wf => {
            text.push_str(&format!("(assert {})\n", specs[0]));
            let mut viol = Vec::new();
            for (k, (formula, what)) in lo.wf.iter().enumerate() {
                let nm = format!("wf_{k}");
                text.push_str(&format!("(define-fun {nm} () Bool {})\n", formula));
                wf_flags.push((nm.clone(), what.clone()));
                viol.push(nm);
            }
            if viol.is_empty() {
                // nothing partial at these lengths; the caller skips this instance
                text.push_str("(assert false)\n");
                text.push_str(";; no-partial-ops\n");
            } else {
                text.push_str(&format!("(assert {})\n", or(viol)));
            }
        }
    }
    Ok(Query { text, inputs, outputs, wf_flags })
}

/// Integer literals compared with a `.len()` anywhere in the declaration
/// (`s.len() == 81`), so that output lengths the spec pins can be reached.
fn len_literals(d: &Decl) -> Vec<usize> {
    fn walk_e(e: &Expr, out: &mut Vec<usize>) {
        match &e.kind {
            ExprKind::Bin(_, l, r) => {
                let is_len = |x: &Expr| matches!(&x.kind, ExprKind::Method(m) if matches!(&**m, Method::Len(_)));
                for (a, b) in [(&**l, &**r), (&**r, &**l)] {
                    if is_len(a) {
                        if let ExprKind::Int(k) = &b.kind {
                            if let Ok(n) = k.parse::<usize>() {
                                out.push(n);
                            }
                        }
                    }
                }
                walk_e(l, out);
                walk_e(r, out);
            }
            ExprKind::Not(x) | ExprKind::Neg(x) => walk_e(x, out),
            ExprKind::IfVal(a, b, c) => {
                walk_e(a, out);
                walk_e(b, out);
                walk_e(c, out);
            }
            _ => {}
        }
    }
    fn walk_s(st: &Stmt, out: &mut Vec<usize>) {
        match &st.kind {
            StmtKind::Constraint(e) => walk_e(e, out),
            StmtKind::ForIn { body, .. } | StmtKind::ForRange { body, .. } | StmtKind::Some { body, .. } => body.iter().for_each(|x| walk_s(x, out)),
            StmtKind::Any { wherec, .. } => walk_e(wherec, out),
            StmtKind::Cases(v) => v.iter().for_each(|x| walk_s(x, out)),
            StmtKind::If { cond, then, els } => {
                walk_e(cond, out);
                then.iter().for_each(|x| walk_s(x, out));
                if let Some(e) = els {
                    e.iter().for_each(|x| walk_s(x, out));
                }
            }
            StmtKind::Implies(c, x) => {
                walk_e(c, out);
                walk_s(x, out);
            }
            StmtKind::Match { arms, .. } => arms.iter().for_each(|a| a.body.iter().for_each(|x| walk_s(x, out))),
        }
    }
    let mut out = Vec::new();
    for e in d.requires.iter().chain(d.ensures.iter()) {
        walk_e(e, &mut out);
    }
    for st in &d.body {
        walk_s(st, &mut out);
    }
    out
}

/// Output sequences may be longer than inputs: up to twice the bound, or any
/// length the declaration pins by a literal (capped).
fn output_len_bound(d: &Decl, max_len: usize) -> usize {
    let lit = len_literals(d).into_iter().filter(|&n| n <= 32).max().unwrap_or(0);
    (2 * max_len).max(lit)
}

/// The implementer's choices at the top level of the body (under no `for`,
/// `some` or `match` binder): declared like inputs by `build`.
fn top_choices(d: &Decl) -> Vec<(String, RType)> {
    let mut v: Vec<(String, RType)> = Vec::new();
    for c in d.choices() {
        if c.under.is_empty() && !v.iter().any(|(n, _)| n == &c.name) {
            v.push((c.name, c.ty));
        }
    }
    v
}

/// All assignments of lengths to the sequence-typed variables: inputs (and
/// top-level choices) up to `max_len`, outputs up to `output_len_bound`.
fn length_assignments(d: &Decl, max_len: usize, inputs_only: bool) -> Vec<HashMap<String, usize>> {
    let out_max = output_len_bound(d, max_len);
    let mut ins: Vec<(String, usize)> = d.inputs().into_iter().filter(|(_, t)| t.is_seq()).map(|(n, _)| (n, max_len)).collect();
    if !inputs_only {
        ins.extend(top_choices(d).into_iter().filter(|(_, t)| t.is_seq()).map(|(n, _)| (n, max_len)));
    }
    let outs: Vec<(String, usize)> = if inputs_only { Vec::new() } else { d.outputs().into_iter().filter(|(_, t)| t.is_seq()).map(|(n, _)| (n, out_max)).collect() };
    let mut out = vec![HashMap::new()];
    for (v, m) in ins.into_iter().chain(outs) {
        let mut next = Vec::new();
        for a in &out {
            for len in 0..=m {
                let mut b = a.clone();
                b.insert(v.clone(), len);
                next.push(b);
            }
        }
        out = next;
    }
    out
}

struct Found {
    inputs: String,
    outputs: String,
    why: String,
    model: HashMap<String, String>,
    lens: HashMap<String, usize>,
}

/// Run one check: returns (examples found, total distinct inputs seen (capped), unknown?)
fn run_check(z3: &mut Z3, d: &Decl, decls: &HashMap<String, &Decl>, types: &TypeDefs, bounds: &Bounds, small: bool, check: Check) -> R<(Vec<Found>, usize, bool)> {
    let mut found = Vec::new();
    let mut total = 0usize;
    let mut unknown = false;
    let mut any_partial = false;
    for lens in length_assignments(d, bounds.max_len, check == Check::Existence) {
        let q = build(d, decls, types, bounds, small, &lens, check)?;
        if std::env::var("DJINN_SMOKE_DUMP").is_ok() {
            eprintln!(";; ---- {} {:?} small={small} lens={:?}\n{}", d.name, check, lens, q.text);
        }
        if check == Check::Wf {
            if q.text.contains(";; no-partial-ops") {
                continue;
            }
            any_partial = true;
        }
        if check == Check::Limits && q.text.contains(";; no-limits") {
            continue;
        }
        z3.send("(reset)");
        z3.send(&format!("(set-option :timeout {})", bounds.timeout_ms));
        z3.send("(set-option :produce-models true)");
        for line in q.text.lines() {
            z3.send(line);
        }
        let vars: Vec<String> = q.inputs.iter().chain(q.outputs.iter().flatten()).flat_map(|s| s.smt.clone()).collect();
        let mut n_here = 0;
        loop {
            let r = z3.check_sat();
            if r.starts_with("sat") {
                let model = z3.get_value(&vars);
                n_here += 1;
                total += 1;
                if found.len() < 3 {
                    let ins = q.inputs.iter().map(|s| format!("{} = {}", s.name, show(s, &model))).collect::<Vec<_>>().join(", ");
                    let outs = if q.outputs.len() == 1 && q.outputs[0].is_empty() {
                        String::new()
                    } else if q.outputs.len() == 2 {
                        let a = q.outputs[0].iter().map(|s| format!("{} = {}", s.name, show(s, &model))).collect::<Vec<_>>().join(", ");
                        let b = q.outputs[1].iter().map(|s| format!("{} = {}", s.name, show(s, &model))).collect::<Vec<_>>().join(", ");
                        format!("{a}   and also   {b}")
                    } else {
                        q.outputs[0].iter().map(|s| format!("{} = {}", s.name, show(s, &model))).collect::<Vec<_>>().join(", ")
                    };
                    let mut why = String::new();
                    if !q.wf_flags.is_empty() {
                        let names: Vec<String> = q.wf_flags.iter().map(|(n, _)| n.clone()).collect();
                        let flags = z3.get_value(&names);
                        let hits: Vec<&str> = q.wf_flags.iter().filter(|(n, _)| flags.get(n).map(|v| v == "true").unwrap_or(false)).map(|(_, w)| w.as_str()).collect();
                        why = hits.join("; ");
                    }
                    found.push(Found { inputs: ins, outputs: outs, why, model: model.clone(), lens: lens.clone() });
                }
                if check == Check::Limits {
                    return Ok((found, total, unknown));
                }
                if total >= bounds.max_examples {
                    return Ok((found, total, unknown));
                }
                // block these inputs (for consistency checks, block inputs+outputs)
                let blocked: Vec<&Sym> = if check == Check::Consistent { q.inputs.iter().chain(q.outputs[0].iter()).collect() } else { q.inputs.iter().collect() };
                let syms: Vec<Sym> = blocked.iter().map(|s| Sym { name: s.name.clone(), ty: s.ty.clone(), smt: s.smt.clone() }).collect();
                if syms.iter().all(|s| s.smt.is_empty()) {
                    break; // nothing to block (no inputs): one example is all there is
                }
                z3.send(&block(&syms, &model));
            } else if r.starts_with("unsat") {
                break;
            } else {
                unknown = true;
                break;
            }
            if n_here >= bounds.max_examples {
                break;
            }
        }
    }
    if check == Check::Wf && !any_partial {
        return Err("no partial operations".into());
    }
    Ok((found, total, unknown))
}

fn count_phrase(total: usize, max: usize, bounds: &Bounds, small: bool) -> String {
    let scope = if small {
        format!("inputs in [-{}, {}], sequences up to length {}", bounds.int_bound, bounds.int_bound, bounds.max_len)
    } else {
        format!("full input ranges, sequences up to length {}", bounds.max_len)
    };
    match total {
        1 => format!("the ONLY counterexample within the bounds ({scope})"),
        n if n < max => format!("one of {n} counterexamples within the bounds ({scope})"),
        _ => format!("one of MANY counterexamples ({max}+ within the bounds: {scope})"),
    }
}

/// Structured result of a smoke test, for the CLI printer and the LSP.
#[derive(Clone, Debug)]
pub struct SmokeReport {
    pub decls: Vec<DeclReport>,
    pub all_ok: bool,
}

impl SmokeReport {
    /// How many checks were unsupported or inconclusive (they say nothing
    /// about the specification), of how many (skipped and not-applicable
    /// checks count in neither).
    pub fn coverage(&self) -> (usize, usize) {
        let checks = self.decls.iter().flat_map(|d| d.checks.iter()).filter(|c| !matches!(c.status, CheckStatus::NotApplicable | CheckStatus::Skipped));
        let (mut u, mut n) = (0, 0);
        for c in checks {
            n += 1;
            if matches!(c.status, CheckStatus::Unsupported(_) | CheckStatus::Inconclusive(_)) {
                u += 1;
            }
        }
        (u, n)
    }
}

#[derive(Clone, Debug)]
pub struct DeclReport {
    pub name: String,
    pub kind: String,
    /// 1-based line and column of the declaration name in the source
    pub line: usize,
    pub col: usize,
    /// Index of the specification file (see `smoke_run_sources`).
    pub file: usize,
    pub checks: Vec<CheckReport>,
}

#[derive(Clone, Debug)]
pub struct CheckReport {
    pub label: String,
    pub status: CheckStatus,
}

#[derive(Clone, Debug)]
pub enum CheckStatus {
    Ok { note: String },
    Problem {
        /// AMBIGUOUS, CONTRADICTION, NO OUTPUT FOR SOME INPUT, ENSURES VIOLATED, ILL-FORMED
        what: String,
        how_many: String,
        /// rendered example lines
        examples: Vec<String>,
        conflict_title: String,
        /// (1-based line, source text) of statements that cannot hold together
        conflicts: Vec<(usize, String)>,
        example_input: Option<String>,
    },
    Unsupported(String),
    /// the check ran but cannot conclude: the solver gave up, or the
    /// specification reaches past what smoke-test models exactly
    Inconclusive(String),
    NotApplicable,
    /// the declaration carries `#[override_smoke_test]`
    Skipped,
}

impl CheckStatus {
    pub fn is_problem(&self) -> bool {
        matches!(self, CheckStatus::Problem { .. })
    }
}

fn conflict_pairs(d: &Decl, src_lines: &[&str], core: &[(bool, usize)]) -> Vec<(usize, String)> {
    core.iter()
        .map(|(is_req, k)| {
            let line = if *is_req { d.requires_spans.get(*k).map(|s| s.start().line) } else { d.body.get(*k).map(|s| s.span.start().line) }.unwrap_or(0);
            let text = src_lines.get(line.saturating_sub(1)).map(|l| l.trim()).unwrap_or("").to_string();
            let cont = if text.ends_with('{') { " …" } else { "" };
            (line, format!("{text}{cont}{}", if *is_req { "  (requires)" } else { "" }))
        })
        .collect()
}

/// Run every check on the specification source text.
pub fn smoke_run(src: &str, bounds: &Bounds) -> std::result::Result<SmokeReport, String> {
    smoke_run_sources(&[src.to_string()], bounds).map_err(|(_, e)| e)
}

/// Run every check on a specification of several files (see
/// `djinn_syntax::parse_sources`); an error comes with its file's index.
pub fn smoke_run_sources(srcs: &[String], bounds: &Bounds) -> std::result::Result<SmokeReport, (usize, String)> {
    let prog = djinn_syntax::parse_sources(srcs).map_err(|e| {
        let s = e.span.start();
        (e.file, format!("{}:{}: error: {}", s.line, s.column + 1, e.msg))
    })?;
    smoke_run_program(&prog, srcs, bounds).map_err(|e| (0, e))
}

fn smoke_run_program(prog: &djinn_syntax::Program, srcs: &[String], bounds: &Bounds) -> std::result::Result<SmokeReport, String> {
    let decls = &prog.decls;
    let types = &prog.types;
    let map: HashMap<String, &Decl> = decls.iter().map(|d| (d.name.clone(), d)).collect();
    let file_lines: Vec<Vec<&str>> = srcs.iter().map(|s| s.lines().collect()).collect();
    let mut z3 = Z3::start(bounds.timeout_ms)?;
    let mut all_ok = true;
    let mut out = Vec::new();
    for d in decls {
        if let Some(only) = &bounds.only {
            if &d.name != only {
                continue;
            }
        }
        let kind = d.kind.word();
        if d.override_smoke_test {
            let st = d.name_span.start();
            let checks = vec![CheckReport { label: "all checks".into(), status: CheckStatus::Skipped }];
            out.push(DeclReport { name: d.name.clone(), kind: kind.into(), line: st.line, col: st.column + 1, file: d.file, checks });
            continue;
        }
        let mut checks = vec![(Check::Consistent, "consistency".to_string())];
        if d.kind == Kind::Func || d.total {
            checks.push((Check::Existence, "existence".into()));
        }
        if d.kind == Kind::Func {
            let weak = !d.choices().is_empty() || d.inherits_ambiguity(|f| map.get(f).map(|x| x.weakly_specified).unwrap_or(false));
            checks.push((Check::Unambiguous, if weak { "unambiguity (modulo the choices)".into() } else { "unambiguity".into() }));
        }
        for i in 0..d.ensures.len() {
            checks.push((Check::Ensures(i), format!("ensures {i}")));
        }
        checks.push((Check::Wf, "well-formedness".into()));
        let mut reports = Vec::new();
        // preconditions first: if they cannot be met within the input bounds,
        // every other check would be vacuous (and possibly huge)
        let pre_ok = match run_check(&mut z3, d, &map, types, bounds, false, Check::PreSat) {
            Ok((found, _, unknown)) => !found.is_empty() || unknown,
            Err(_) => true,
        };
        if !pre_ok {
            reports.push(CheckReport {
                label: "preconditions".into(),
                status: CheckStatus::Unsupported(format!(
                    "cannot be met within the bounds (input sequences up to length {}): raise --max-len / --int-bound",
                    bounds.max_len
                )),
            });
            let st = d.name_span.start();
            out.push(DeclReport { name: d.name.clone(), kind: kind.into(), line: st.line, col: st.column + 1, file: d.file, checks: reports });
            continue;
        }
        // a limit of the encoding the declaration can reach: then finding
        // nothing (no witness, no counterexample) concludes nothing
        let beyond: Option<String> = match run_check(&mut z3, d, &map, types, bounds, false, Check::Limits) {
            Ok((found, _, unknown)) => match found.first() {
                Some(f) => Some(format!("{} (e.g. at {})", if f.why.is_empty() { "an operation smoke-test does not model exactly" } else { &f.why }, f.inputs)),
                None if unknown => Some("an operation smoke-test does not model exactly (the solver could not rule it out)".into()),
                None => None,
            },
            Err(_) => None,
        };
        let inconclusive = |unknown: bool, nothing: &str| -> Option<CheckStatus> {
            if unknown {
                Some(CheckStatus::Inconclusive(format!("{nothing}, but the solver gave up on some sizes (raise --timeout)")))
            } else {
                beyond.as_ref().map(|b| CheckStatus::Inconclusive(format!("{nothing} where smoke-test's encoding is exact, but the specification can reach {b}, beyond it")))
            }
        };
        for (check, label) in checks {
            let mut result = None;
            let mut unsupported = None;
            for small in [true, false] {
                match run_check(&mut z3, d, &map, types, bounds, small, check) {
                    Ok((found, total, unknown)) => {
                        if !found.is_empty() {
                            result = Some((Some((found, total, small)), unknown));
                            break;
                        }
                        // the full ranges decide what the small ones left open
                        result = Some((None, unknown));
                    }
                    Err(e) => {
                        unsupported = Some(e);
                        result = None;
                        break;
                    }
                }
            }
            let status = match (result, unsupported) {
                (None, Some(e)) if e == "no partial operations" => CheckStatus::NotApplicable,
                (None, Some(e)) => CheckStatus::Unsupported(e),
                (None, None) => CheckStatus::Unsupported("no result".into()),
                (Some((hit, unknown)), _) => match (check, hit) {
                    (Check::Consistent, Some((found, _, _))) => {
                        let f = &found[0];
                        CheckStatus::Ok { note: format!("satisfiable; e.g. {} with {}", f.inputs, f.outputs) }
                    }
                    // unsat only is a contradiction; `unknown` is not
                    (Check::Consistent, None) if inconclusive(unknown, "no witness found").is_some() => inconclusive(unknown, "no witness found").unwrap(),
                    (Check::Consistent, None) if !matches!(run_check(&mut z3, d, &map, types, bounds, false, Check::PreSat), Ok((ref f, _, _)) if !f.is_empty()) => {
                        // not even the preconditions can be met within the bounds
                        // (or the solver could not tell)
                        CheckStatus::Unsupported(format!(
                            "the preconditions cannot be met within the bounds (sequences up to length {}): raise --max-len / --int-bound",
                            bounds.max_len
                        ))
                    }
                    (Check::Consistent, None) => {
                        all_ok = false;
                        let mut conflicts = Vec::new();
                        let mut title = String::new();
                        let mut example_input = None;
                        for lens in length_assignments(d, bounds.max_len, false) {
                            if let Ok(Some((core, example))) = explain(&mut z3, d, &map, types, bounds, true, &lens, None) {
                                title = conflict_title(core.len(), false).to_string();
                                conflicts = conflict_pairs(d, &file_lines[d.file], &core);
                                example_input = example;
                                break;
                            }
                        }
                        CheckStatus::Problem {
                            what: "CONTRADICTION".into(),
                            how_many: "no input/output satisfies the relation within the bounds".into(),
                            examples: Vec::new(),
                            conflict_title: title,
                            conflicts,
                            example_input,
                        }
                    }
                    (_, Some((found, total, small))) => {
                        all_ok = false;
                        let what = match check {
                            Check::Unambiguous => "AMBIGUOUS",
                            Check::Existence => "NO OUTPUT FOR SOME INPUT",
                            Check::Ensures(_) => "ENSURES VIOLATED",
                            Check::Wf => "ILL-FORMED",
                            Check::Consistent | Check::PreSat | Check::Limits => unreachable!(),
                        };
                        let mut examples = Vec::new();
                        for (k, f) in found.iter().enumerate() {
                            let tag = if k == 0 { "counterexample" } else { "another" };
                            examples.push(match check {
                                Check::Unambiguous => format!("{tag}: {}  admits both  {}", f.inputs, f.outputs),
                                Check::Existence => format!("{tag}: {}  (the precondition holds, no output satisfies the relation)", f.inputs),
                                Check::Wf => format!("{tag}: {}  with  {}  — violates: {}", f.inputs, f.outputs, f.why),
                                _ => format!("{tag}: {}  with  {}", f.inputs, f.outputs),
                            });
                        }
                        let mut conflicts = Vec::new();
                        let mut title = String::new();
                        if check == Check::Existence {
                            let f = &found[0];
                            let out_seq: Vec<String> = d.outputs().into_iter().filter(|(_, t)| t.is_seq()).map(|(n, _)| n).collect();
                            let mut lens_list = vec![f.lens.clone()];
                            let out_max = output_len_bound(d, bounds.max_len);
                            for v in &out_seq {
                                let mut next = Vec::new();
                                for a in &lens_list {
                                    for len in 0..=out_max {
                                        let mut b = a.clone();
                                        b.insert(v.clone(), len);
                                        next.push(b);
                                    }
                                }
                                lens_list = next;
                            }
                            for lens in lens_list {
                                if let Ok(Some((core, _))) = explain(&mut z3, d, &map, types, bounds, small, &lens, Some(&f.model)) {
                                    title = conflict_title(core.len(), true).to_string();
                                    conflicts = conflict_pairs(d, &file_lines[d.file], &core);
                                    break;
                                }
                            }
                        }
                        CheckStatus::Problem {
                            what: what.into(),
                            how_many: count_phrase(total, bounds.max_examples, bounds, small),
                            examples,
                            conflict_title: title,
                            conflicts,
                            example_input: if check == Check::Existence { Some(found[0].inputs.clone()) } else { None },
                        }
                    }
                    (_, None) => match inconclusive(unknown, "no counterexample found") {
                        Some(st) => st,
                        None => CheckStatus::Ok { note: "no counterexample within the bounds".into() },
                    },
                },
            };
            reports.push(CheckReport { label, status });
        }
        let st = d.name_span.start();
        out.push(DeclReport { name: d.name.clone(), kind: kind.into(), line: st.line, col: st.column + 1, file: d.file, checks: reports });
    }
    Ok(SmokeReport { decls: out, all_ok })
}

/// `paths`: the specification files, named beside each declaration when
/// there are several.
pub fn print_report(r: &SmokeReport, bounds: &Bounds, paths: &[String]) {
    println!(
        "smoke-test: bounded symbolic checks with Z3 (sequences up to length {}, small integers in [-{}, {}] first, then full ranges; ≤{} examples per check)",
        bounds.max_len, bounds.int_bound, bounds.int_bound, bounds.max_examples
    );
    for d in &r.decls {
        match paths.get(d.file).filter(|_| paths.len() > 1) {
            Some(p) => println!("\n{} {}  ({p}:{})", d.kind, d.name, d.line),
            None => println!("\n{} {}", d.kind, d.name),
        }
        for c in &d.checks {
            let label = &c.label;
            match &c.status {
                CheckStatus::Ok { note } => println!("  {label:16} ok — {note}"),
                CheckStatus::NotApplicable => println!("  {label:16} n/a (no partial operations or callee preconditions)"),
                CheckStatus::Skipped => println!("  {label:16} skipped — #[override_smoke_test]"),
                CheckStatus::Unsupported(e) => println!("  {label:16} unsupported: {e}"),
                CheckStatus::Inconclusive(e) => println!("  {label:16} INCONCLUSIVE: {e}"),
                CheckStatus::Problem { what, how_many, examples, conflict_title, conflicts, example_input } => {
                    println!("  {label:16} {what}: {how_many}");
                    for (k, e) in examples.iter().enumerate() {
                        println!("    {e}");
                        if k == 0 && !conflicts.is_empty() {
                            println!("      {conflict_title}");
                            for (line, text) in conflicts {
                                println!("        line {line}: {text}");
                            }
                        }
                    }
                    if examples.is_empty() && !conflicts.is_empty() {
                        println!("    {conflict_title}");
                        for (line, text) in conflicts {
                            println!("      line {line}: {text}");
                        }
                        if let Some(e) = example_input {
                            println!("    e.g. at {e}");
                        }
                    }
                }
            }
        }
    }
    println!();
    let (unsupported, total) = r.coverage();
    if r.all_ok && unsupported > 0 {
        // not a clean result: the unsupported checks say nothing
        println!("smoke-test: INCOMPLETE: no contradiction and no counterexample among the checks it could run, but {unsupported} of {total} checks are unsupported or inconclusive (listed above) and say nothing about the specification.");
    } else if r.all_ok {
        println!("smoke-test: no contradiction and no counterexample within the bounds (this is not a proof).");
    } else {
        println!("smoke-test: problems found; fix the specification before paying an agent.");
    }
}

/// Exit status: 0 every check ran and found nothing, 1 problems found, 3 nothing
/// found but some checks were unsupported or inconclusive (an incomplete result).
pub fn smoke_test(cfg: &Config, bounds: &Bounds) -> std::result::Result<u8, String> {
    let texts = cfg.spec_texts()?;
    if texts.is_empty() {
        return Err(format!("{}: no `djinn! {{ … }}` declarations found", cfg.specs_display()));
    }
    let paths: Vec<String> = texts.iter().map(|(f, _)| cfg.rel(&f.path)).collect();
    let srcs: Vec<String> = texts.into_iter().map(|(_, t)| t).collect();
    let r = smoke_run_sources(&srcs, bounds).map_err(|(i, e)| format!("{}:{e}", paths.get(i).cloned().unwrap_or_default()))?;
    print_report(&r, bounds, &paths);
    Ok(match (r.all_ok, r.coverage().0) {
        (false, _) => 1,
        (true, 0) => 0,
        (true, _) => 3,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(body: &str) -> SmokeReport {
        let src = format!("use djinn::djinn;\ndjinn! {{\n{body}\n}}\n");
        smoke_run(&src, &Bounds { timeout_ms: 5_000, ..Default::default() }).unwrap()
    }

    fn status<'a>(r: &'a SmokeReport, decl: &str, label: &str) -> &'a CheckStatus {
        let d = r.decls.iter().find(|d| d.name == decl).unwrap();
        &d.checks.iter().find(|c| c.label.starts_with(label)).unwrap_or_else(|| panic!("no check {label} in {:?}", d.checks)).status
    }

    fn is_ok(s: &CheckStatus) -> bool {
        matches!(s, CheckStatus::Ok { .. })
    }

    #[test]
    fn right_shift_by_a_wide_or_large_amount_is_zero() {
        // `x >> n` is `x / 2^n`: zero once n ≥ 8, also for n = 256, whose low
        // 8 bits are 0 (the model once shifted by those)
        let r = run("#[ensures(n >= 8 => r == 0)]\npub fn f(x: u8, n: u32) -> r: u32 { r == x >> n; }\n\
                     #[ensures(r == 0)]\npub fn g(x: u8) -> r: u32 { r == x >> 256; }");
        assert!(is_ok(status(&r, "f", "ensures 0")), "{:?}", status(&r, "f", "ensures 0"));
        assert!(is_ok(status(&r, "g", "ensures 0")), "{:?}", status(&r, "g", "ensures 0"));
        assert!(r.all_ok);
    }

    #[test]
    fn left_shift_never_drops_bits() {
        // `<<` multiplies: a u8 amount stays exact (no 128-bit limit), and no
        // amount is a well-formedness violation of the specification
        let r = run("#[ensures(r >= x)]\npub rel f(x: u8, n: u8) -> r: int { r == x << n; }");
        assert!(is_ok(status(&r, "f", "ensures 0")), "{:?}", status(&r, "f", "ensures 0"));
        assert!(!status(&r, "f", "well-formedness").is_problem(), "{:?}", status(&r, "f", "well-formedness"));
        assert!(r.all_ok);
    }

    #[test]
    fn left_shift_beyond_the_model_is_inconclusive_not_ill_formed() {
        // a u32 amount can exceed what smoke-test models: that says nothing
        // about the specification (Lean's `<<<` has no limit)
        let r = run("#[ensures(r >= x)]\npub rel f(x: u64, n: u32) -> r: int { r == x << n; }");
        for c in &r.decls[0].checks {
            assert!(!c.status.is_problem(), "{}: {:?}", c.label, c.status);
        }
        assert!(matches!(status(&r, "f", "ensures 0"), CheckStatus::Inconclusive(_)), "{:?}", status(&r, "f", "ensures 0"));
        assert!(r.coverage().0 > 0);
        assert!(matches!(status(&r, "f", "consistency"), CheckStatus::Ok { .. }), "{:?}", status(&r, "f", "consistency"));
        // a precondition that keeps the amount in range makes it conclusive
        let r = run("#[requires(n < 32)]\n#[ensures(r >= x)]\npub rel f(x: u8, n: u32) -> r: int { r == x << n; }");
        assert!(is_ok(status(&r, "f", "ensures 0")), "{:?}", status(&r, "f", "ensures 0"));
        assert!(is_ok(status(&r, "f", "consistency")), "{:?}", status(&r, "f", "consistency"));
        assert!(r.all_ok && r.coverage().0 == 0, "{:?}", r.decls[0].checks);
    }

    #[test]
    fn a_solver_timeout_is_inconclusive_not_a_contradiction() {
        // satisfiable (x, y, z = 8866128975287528, -8778405442862239,
        // -2736111468807040), but no solver finds it in half a second
        let src = "use djinn::djinn;\ndjinn! {\npub rel cubes(x: i64, y: i64, z: i64) -> r: i64 { r == 0; x * x * x + y * y * y + z * z * z == 33; }\n}\n";
        let r = smoke_run(src, &Bounds { timeout_ms: 500, ..Default::default() }).unwrap();
        let c = status(&r, "cubes", "consistency");
        assert!(matches!(c, CheckStatus::Inconclusive(_)), "{c:?}");
        // an inconclusive check makes the run incomplete, not clean
        assert!(r.all_ok);
        assert!(r.coverage().0 > 0);
    }

    #[test]
    fn remainder_by_one_is_zero() {
        let r = run("#[ensures(r == 0)]\npub fn f(x: u32, y: u32) -> r: u32 { r == (x & y) % 1; }\n\
                     #[ensures(r < 4)]\npub fn g(x: u32, y: u32) -> r: u32 { r == (x | y) % 4; }");
        assert!(is_ok(status(&r, "f", "ensures 0")), "{:?}", status(&r, "f", "ensures 0"));
        assert!(is_ok(status(&r, "g", "ensures 0")), "{:?}", status(&r, "g", "ensures 0"));
        assert!(r.all_ok);
    }

    #[test]
    fn a_cast_does_not_truncate_in_a_bit_operation() {
        // casts are value-preserving in the specification: (300 as u8) >> 1 is 150
        let r = run("#[requires(x == 300)]\n#[ensures(r == 150)]\npub fn f(x: u32, n: u32) -> r: u32 { r == ((x + 0) as u8) >> (n - n + 1); }");
        assert!(is_ok(status(&r, "f", "ensures 0")), "{:?}", status(&r, "f", "ensures 0"));
    }
}
