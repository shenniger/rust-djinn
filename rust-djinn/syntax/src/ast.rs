//! The Djinn AST: declarations, statements (constraints) and expressions.
//! Every statement and expression carries the span of its source tokens, so
//! that errors found while lowering point at the construct, not at the
//! declaration.

use proc_macro2::{Span, TokenStream};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Func,
    Rel,
}

impl Kind {
    pub fn word(self) -> &'static str {
        match self {
            Kind::Func => "func",
            Kind::Rel => "rel",
        }
    }
    pub fn from_word(s: &str) -> Kind {
        match s {
            "rel" => Kind::Rel,
            _ => Kind::Func,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeqKind {
    Slice,
    Vec,
    /// `[T; N]`, with the length tokens as written.
    Array(String),
    /// `&str`: a byte string (Aeneas models `str` as `Slice U8`).
    Str,
    /// `String`: an owned string, viewed as its UTF-8 bytes (Aeneas keeps
    /// Lean's `String` as the carrier; the trusted models bridge it).
    String,
}

/// Rust types the specification language understands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RType {
    /// Machine integer; `bits == 0` means pointer-sized (`usize`/`isize`).
    Int { signed: bool, bits: u32 },
    /// The mathematical integer `int`: allowed only in `rel` signatures,
    /// which are never implemented.
    MathInt,
    Bool,
    Char,
    Seq(Box<RType>, SeqKind),
    /// `HashMap<K, V>`: viewed as the list of its entries, no key twice
    /// (modeled by the trusted library, DESIGN.md §6).
    Map(Box<RType>, Box<RType>),
    Option(Box<RType>),
    Result(Box<RType>, Box<RType>),
    Unit,
    /// A user type (`struct`/`enum` declared next to the block), by name.
    Named(String),
}

impl RType {
    pub fn is_scalar(&self) -> bool {
        matches!(self, RType::Int { .. })
    }
    pub fn is_numeric(&self) -> bool {
        matches!(self, RType::Int { .. } | RType::MathInt)
    }
    pub fn is_signed_scalar(&self) -> bool {
        matches!(self, RType::Int { signed: true, .. })
    }
    pub fn is_seq(&self) -> bool {
        matches!(self, RType::Seq(..))
    }
    pub fn elem(&self) -> Option<&RType> {
        match self {
            RType::Seq(e, _) => Some(e),
            _ => None,
        }
    }
    /// Does the type mention a user type?
    pub fn mentions_named(&self) -> bool {
        match self {
            RType::Named(_) => true,
            RType::Seq(e, _) | RType::Option(e) => e.mentions_named(),
            RType::Result(a, b) | RType::Map(a, b) => a.mentions_named() || b.mentions_named(),
            _ => false,
        }
    }
    /// Does the type need the Aeneas `Types` module (a user type, or a
    /// modeled standard type defined in `TypesExternal`)?
    pub fn needs_code_types(&self) -> bool {
        match self {
            RType::Named(_) | RType::Map(..) => true,
            RType::Seq(e, _) | RType::Option(e) => e.needs_code_types(),
            RType::Result(a, b) => a.needs_code_types() || b.needs_code_types(),
            _ => false,
        }
    }
}

/// The type of a specification-level term. `Int` is the unbounded
/// mathematical integer of constraints; everything else is a Rust type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SType {
    Int,
    Of(RType),
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: RType,
    /// `&mut T`: the parameter is also an output.
    pub mut_ref: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub kind: Kind,
    pub name: String,
    pub name_span: Span,
    pub params: Vec<Param>,
    /// Named return value, if the return type is not `()`.
    pub ret: Option<(String, RType)>,
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub total: bool,
    /// `#[override_smoke_test]`: the smoke-test skips this declaration (its
    /// bounded search is known to be inconclusive or misleading here).
    pub override_smoke_test: bool,
    /// `#[weakly_specified]`: the declaration leaves something to the
    /// implementer — it has `any` choices, or calls a declaration that does.
    /// Required exactly then, so that a human reviews every such function.
    pub weakly_specified: bool,
    /// `#[decreases(e, …)]` on a recursive declaration: the measure
    /// (mathematical integers, compared lexicographically).
    pub decreases: Vec<Expr>,
    pub body: Vec<Stmt>,
    /// Source positions of the `requires` attributes (parallel to `requires`).
    pub requires_spans: Vec<Span>,
    /// Index of the specification file the declaration comes from (see
    /// `parse_sources`; 0 for a single file).
    pub file: usize,
    // Raw tokens the macro needs to emit the delegation stub.
    pub vis_tokens: TokenStream,
    pub params_tokens: TokenStream,
    pub ret_tokens: Option<TokenStream>,
    /// The declaration's tokens in canonical text form (see `project::canonical`):
    /// what the report records and the macro compares.
    pub source: String,
}

impl Decl {
    /// Does the declaration use a bit operation anywhere (requires, ensures,
    /// decreases, body)?
    pub fn uses_bits(&self) -> bool {
        self.uses(&|e: &Expr| e.is_bit_op())
    }

    /// Does the declaration use `&`, `|`, `^`, a shift or a rotation (the
    /// operations a bounded check is fastest on in bit vectors)?
    pub fn uses_bitwise(&self) -> bool {
        self.uses(&|e: &Expr| match &e.kind {
            ExprKind::Bin(BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor, _, _) => true,
            // a shift by a literal is multiplication or division by a constant
            ExprKind::Bin(BinOp::Shl | BinOp::Shr, _, n) => !matches!(n.kind, ExprKind::Int(_)),
            ExprKind::Method(m) => matches!(&**m, Method::Rotate(..)),
            _ => false,
        })
    }

    fn uses(&self, p: &dyn Fn(&Expr) -> bool) -> bool {
        self.requires.iter().chain(self.ensures.iter()).chain(self.decreases.iter()).any(|e| e.any(&p)) || self.body.iter().any(|s| s.any_expr(&p))
    }
    /// Output names and types: the return value first, then every `&mut`
    /// parameter in order.
    pub fn outputs(&self) -> Vec<(String, RType)> {
        let mut v = Vec::new();
        if let Some((n, t)) = &self.ret {
            v.push((n.clone(), t.clone()));
        }
        for p in &self.params {
            if p.mut_ref {
                v.push((p.name.clone(), p.ty.clone()));
            }
        }
        v
    }
    /// Input names (as seen by the specification) and types: a `&mut`
    /// parameter `v` is the input `v_old`.
    pub fn inputs(&self) -> Vec<(String, RType)> {
        self.params
            .iter()
            .map(|p| (if p.mut_ref { format!("{}_old", p.name) } else { p.name.clone() }, p.ty.clone()))
            .collect()
    }
    /// Source positions of the top-level body statements.
    pub fn body_spans(&self) -> Vec<Span> {
        self.body.iter().map(|s| s.span).collect()
    }
    /// Does the body (or an attribute) call the declaration itself?
    pub fn is_recursive(&self) -> bool {
        let n = &self.name;
        self.requires.iter().chain(self.ensures.iter()).any(|e| e.calls(n)) || self.body.iter().any(|s| s.calls(n))
    }
    /// The implementer's own choices: every `any x: T where …;` statement of
    /// the body, however deeply nested, in source order, with the names of
    /// the `for` variables enclosing each (a choice is a function of those;
    /// `some` and `match` binders are determined by the rest and do not
    /// count — a choice depending on them would be circular).
    pub fn choices(&self) -> Vec<Choice> {
        fn walk(ss: &[Stmt], under: &mut Vec<String>, out: &mut Vec<Choice>) {
            for s in ss {
                match &s.kind {
                    StmtKind::Any { name, ty, .. } => out.push(Choice { name: name.clone(), ty: ty.clone(), under: under.clone() }),
                    StmtKind::ForIn { var, body, .. } | StmtKind::ForRange { var, body, .. } => {
                        under.push(var.clone());
                        walk(body, under, out);
                        under.pop();
                    }
                    StmtKind::Some { body, .. } => walk(body, under, out),
                    StmtKind::Cases(v) => walk(v, under, out),
                    StmtKind::If { then, els, .. } => {
                        walk(then, under, out);
                        if let Some(e) = els {
                            walk(e, under, out);
                        }
                    }
                    StmtKind::Implies(_, s) => walk(std::slice::from_ref(s), under, out),
                    StmtKind::Match { arms, .. } => arms.iter().for_each(|a| walk(&a.body, under, out)),
                    StmtKind::Constraint(_) => {}
                }
            }
        }
        let mut out = Vec::new();
        walk(&self.body, &mut Vec::new(), &mut out);
        out
    }
    /// The declarations the body and attributes call, each once.
    pub fn callees(&self) -> Vec<String> {
        let mut v = Vec::new();
        for e in self.requires.iter().chain(self.ensures.iter()) {
            e.callees(&mut v);
        }
        for s in &self.body {
            s.callees(&mut v);
        }
        v.dedup();
        v
    }
    /// Every name the declaration's source binds or mentions: parameters,
    /// outputs, `for`, `some`, `any`, closure and pattern binders, variables
    /// and constants. Names the lowering makes up (`v_call0`, `x_0`, …) avoid
    /// these, so that no binder of theirs captures a name of the source.
    pub fn names(&self) -> std::collections::HashSet<String> {
        fn expr(e: &Expr, out: &mut std::collections::HashSet<String>) {
            match &e.kind {
                ExprKind::Var(v) | ExprKind::Old(v) => {
                    out.insert(v.clone());
                }
                ExprKind::Method(m) => {
                    if let Method::Count { var, .. } | Method::All { var, .. } | Method::Any { var, .. } | Method::Windows2All { var, .. } = &**m {
                        out.insert(var.clone());
                    }
                }
                _ => {}
            }
            let _ = e.map_children(&mut |x| {
                expr(x, out);
                x.clone()
            });
            if let ExprKind::Method(m) = &e.kind {
                if let Method::Count { pred, .. } | Method::All { pred, .. } | Method::Any { pred, .. } | Method::Windows2All { pred, .. } = &**m {
                    expr(pred, out);
                }
            }
        }
        fn stmts(ss: &[Stmt], out: &mut std::collections::HashSet<String>) {
            for s in ss {
                match &s.kind {
                    StmtKind::Constraint(e) => expr(e, out),
                    StmtKind::ForIn { var, seq, body } => {
                        out.insert(var.clone());
                        expr(seq, out);
                        stmts(body, out);
                    }
                    StmtKind::ForRange { var, lo, hi, body } => {
                        out.insert(var.clone());
                        expr(lo, out);
                        expr(hi, out);
                        stmts(body, out);
                    }
                    StmtKind::Some { binders, body } => {
                        out.extend(binders.iter().map(|(n, _)| n.clone()));
                        stmts(body, out);
                    }
                    StmtKind::Any { name, wherec, .. } => {
                        out.insert(name.clone());
                        expr(wherec, out);
                    }
                    StmtKind::Cases(v) => stmts(v, out),
                    StmtKind::If { cond, then, els } => {
                        expr(cond, out);
                        stmts(then, out);
                        if let Some(e) = els {
                            stmts(e, out);
                        }
                    }
                    StmtKind::Implies(c, s) => {
                        expr(c, out);
                        stmts(std::slice::from_ref(s), out);
                    }
                    StmtKind::Match { scrutinee, arms } => {
                        expr(scrutinee, out);
                        for a in arms {
                            out.extend(a.pat.binders());
                            stmts(&a.body, out);
                        }
                    }
                }
            }
        }
        let mut out = std::collections::HashSet::new();
        for p in &self.params {
            out.insert(p.name.clone());
        }
        out.extend(self.inputs().into_iter().chain(self.outputs()).map(|(n, _)| n));
        for e in self.requires.iter().chain(&self.ensures).chain(&self.decreases) {
            expr(e, &mut out);
        }
        stmts(&self.body, &mut out);
        out
    }
    /// Does the declaration inherit ambiguity: does it call a declaration
    /// that `is_weak` (other than itself)?
    pub fn inherits_ambiguity(&self, is_weak: impl Fn(&str) -> bool) -> bool {
        self.callees().iter().any(|f| f != &self.name && is_weak(f))
    }
}

/// An `any x: T where …;` statement of a declaration (see `Decl::choices`).
#[derive(Clone, Debug)]
pub struct Choice {
    pub name: String,
    pub ty: RType,
    /// The `for` variables enclosing it, outermost first.
    pub under: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Constraint(Expr),
    ForIn { var: String, seq: Expr, body: Vec<Stmt> },
    ForRange { var: String, lo: Expr, hi: Expr, body: Vec<Stmt> },
    Some { binders: Vec<(String, RType)>, body: Vec<Stmt> },
    /// `any x: T where c;` — a value the implementer chooses, within `c`,
    /// in scope for the rest of its block. A choice is an extra argument of
    /// the relation: a function of the declaration's inputs and of the
    /// `for` variables around the statement, fixed before the outputs are
    /// compared.
    Any { name: String, ty: RType, wherec: Expr },
    Cases(Vec<Stmt>),
    If { cond: Expr, then: Vec<Stmt>, els: Option<Vec<Stmt>> },
    Implies(Expr, Box<Stmt>),
    /// `match e { Enum::V(x) => { … } Enum::W { f, .. } => { … } }`
    Match { scrutinee: Expr, arms: Vec<Arm> },
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub span: Span,
    pub pat: Pattern,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    /// `_`
    Wild,
    /// `Enum::Variant`, `Enum::Variant(a, _)`, `Enum::Variant { f, g: h, .. }`
    Variant { enum_name: String, variant: String, fields: PatFields },
}

#[derive(Clone, Debug)]
pub enum PatFields {
    Unit,
    /// Positional binders; `None` is `_`.
    Tuple(Vec<Option<String>>),
    /// `(field, binder)` pairs, `None` for `field: _`; the bool says `..` was present.
    Struct(Vec<(String, Option<String>)>, bool),
}

impl Stmt {
    pub fn new(span: Span, kind: StmtKind) -> Stmt {
        Stmt { span, kind }
    }
    /// Does any expression of the statement have a sub-expression with `p`?
    pub fn any_expr(&self, p: &dyn Fn(&Expr) -> bool) -> bool {
        let all = |ss: &[Stmt]| ss.iter().any(|s| s.any_expr(p));
        match &self.kind {
            StmtKind::Constraint(e) => e.any(p),
            StmtKind::ForIn { seq, body, .. } => seq.any(p) || all(body),
            StmtKind::ForRange { lo, hi, body, .. } => lo.any(p) || hi.any(p) || all(body),
            StmtKind::Some { body, .. } => all(body),
            StmtKind::Any { wherec, .. } => wherec.any(p),
            StmtKind::Cases(v) => all(v),
            StmtKind::If { cond, then, els } => cond.any(p) || all(then) || els.iter().any(|e| all(e)),
            StmtKind::Implies(c, s) => c.any(p) || s.any_expr(p),
            StmtKind::Match { scrutinee, arms } => scrutinee.any(p) || arms.iter().any(|a| all(&a.body)),
        }
    }
    /// Does the statement mention a call to `f`?
    pub fn calls(&self, f: &str) -> bool {
        match &self.kind {
            StmtKind::Constraint(e) => e.calls(f),
            StmtKind::ForIn { seq, body, .. } => seq.calls(f) || body.iter().any(|s| s.calls(f)),
            StmtKind::ForRange { lo, hi, body, .. } => lo.calls(f) || hi.calls(f) || body.iter().any(|s| s.calls(f)),
            StmtKind::Some { body, .. } => body.iter().any(|s| s.calls(f)),
            StmtKind::Any { wherec, .. } => wherec.calls(f),
            StmtKind::Cases(v) => v.iter().any(|s| s.calls(f)),
            StmtKind::If { cond, then, els } => cond.calls(f) || then.iter().any(|s| s.calls(f)) || els.iter().flatten().any(|s| s.calls(f)),
            StmtKind::Implies(c, s) => c.calls(f) || s.calls(f),
            StmtKind::Match { scrutinee, arms } => scrutinee.calls(f) || arms.iter().any(|a| a.body.iter().any(|s| s.calls(f))),
        }
    }
    /// The names of every function the statement calls.
    pub fn callees(&self, out: &mut Vec<String>) {
        match &self.kind {
            StmtKind::Constraint(e) => e.callees(out),
            StmtKind::ForIn { seq, body, .. } => {
                seq.callees(out);
                body.iter().for_each(|s| s.callees(out));
            }
            StmtKind::ForRange { lo, hi, body, .. } => {
                lo.callees(out);
                hi.callees(out);
                body.iter().for_each(|s| s.callees(out));
            }
            StmtKind::Some { body, .. } => body.iter().for_each(|s| s.callees(out)),
            StmtKind::Any { wherec, .. } => wherec.callees(out),
            StmtKind::Cases(v) => v.iter().for_each(|s| s.callees(out)),
            StmtKind::If { cond, then, els } => {
                cond.callees(out);
                then.iter().for_each(|s| s.callees(out));
                els.iter().flatten().for_each(|s| s.callees(out));
            }
            StmtKind::Implies(c, s) => {
                c.callees(out);
                s.callees(out);
            }
            StmtKind::Match { scrutinee, arms } => {
                scrutinee.callees(out);
                arms.iter().for_each(|a| a.body.iter().for_each(|s| s.callees(out)));
            }
        }
    }
}

impl Pattern {
    /// The variables a pattern binds, in field order.
    pub fn binders(&self) -> Vec<String> {
        match self {
            Pattern::Wild => vec![],
            Pattern::Variant { fields, .. } => match fields {
                PatFields::Unit => vec![],
                PatFields::Tuple(v) => v.iter().flatten().cloned().collect(),
                PatFields::Struct(v, _) => v.iter().filter_map(|(_, b)| b.clone()).collect(),
            },
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    /// `&`, `|`, `^` on non-negative integers: Lean's `Nat` bitwise operations
    /// on the values (`&&&`, `|||`, `^^^`), as Aeneas's `.val` lemmas state
    /// them for the machine operations.
    BitAnd,
    BitOr,
    BitXor,
    /// `a << n` is `a * 2^n` and `a >> n` is `a / 2^n` (floor division, so an
    /// arithmetic shift on negative `a`), for `n ≥ 0`. Integers in constraints
    /// are mathematical: `<<` never drops bits; reduce with `% 2.pow(w)`.
    Shl,
    Shr,
}

impl BinOp {
    pub fn is_cmp(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
    }
    pub fn is_arith(self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem) || self.is_bits()
    }
    /// The bit operators: integer-valued, like the arithmetic ones.
    pub fn is_bits(self) -> bool {
        matches!(self, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr)
    }
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(String),
    Bool(bool),
    /// `'a'`
    Char(char),
    /// `"text"` / `b"text"`: a byte string
    Str(Vec<u8>),
    Var(String),
    Old(String),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Neg(Box<Expr>),
    /// `e as T` (identity on integers; `char as u32` is the code point)
    Cast(Box<Expr>, RType),
    /// Call to a `func` or `rel` declared in the specification.
    Call(String, Vec<Expr>),
    /// `Some(x)`, `None`, `Ok(x)`, `Err(e)`.
    Ctor(String, Vec<Expr>),
    /// `Enum::Variant(a, b)` / `Enum::Variant { f: a, g: b }` / `Enum::Variant`;
    /// a field name is given for the struct form.
    Variant { enum_name: String, variant: String, fields: Vec<(Option<String>, Expr)> },
    /// `e.field` of a struct, or of a struct-like enum variant bound by a pattern.
    Field(Box<Expr>, String),
    In(Box<Expr>, Box<Expr>),
    InRange(Box<Expr>, String),
    InDomain(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    IfVal(Box<Expr>, Box<Expr>, Box<Expr>),
    Method(Box<Method>),
}

impl Expr {
    pub fn new(span: Span, kind: ExprKind) -> Expr {
        Expr { span, kind }
    }
    /// Does the expression or a sub-expression satisfy `p`?
    pub fn any(&self, p: &dyn Fn(&Expr) -> bool) -> bool {
        if p(self) {
            return true;
        }
        let rec = |x: &Expr| x.any(p);
        match &self.kind {
            ExprKind::Call(_, args) => args.iter().any(rec),
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::Old(_) => false,
            ExprKind::Bin(_, l, r) | ExprKind::In(l, r) | ExprKind::Index(l, r) => rec(l) || rec(r),
            ExprKind::Not(x) | ExprKind::Neg(x) | ExprKind::Cast(x, _) | ExprKind::InRange(x, _) | ExprKind::InDomain(x, _) | ExprKind::Field(x, _) => rec(x),
            ExprKind::Ctor(_, a) => a.iter().any(rec),
            ExprKind::Variant { fields, .. } => fields.iter().any(|(_, e)| rec(e)),
            ExprKind::Slice(a, b, c) | ExprKind::IfVal(a, b, c) => rec(a) || rec(b) || rec(c),
            ExprKind::Method(m) => m.children().iter().any(|x| rec(x)),
        }
    }
    /// The expression with `f` applied to each direct sub-expression, in
    /// order, except the bodies of closures (`|x| pred`), which stay as they are.
    pub fn map_children(&self, f: &mut dyn FnMut(&Expr) -> Expr) -> Expr {
        let mut b = |x: &Expr| Box::new(f(x));
        let k = match &self.kind {
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::Old(_) => self.kind.clone(),
            ExprKind::Bin(op, l, r) => {
                let l = b(l);
                ExprKind::Bin(*op, l, b(r))
            }
            ExprKind::Not(x) => ExprKind::Not(b(x)),
            ExprKind::Neg(x) => ExprKind::Neg(b(x)),
            ExprKind::Cast(x, t) => ExprKind::Cast(b(x), t.clone()),
            ExprKind::Call(g, a) => ExprKind::Call(g.clone(), a.iter().map(|x| *b(x)).collect()),
            ExprKind::Ctor(c, a) => ExprKind::Ctor(c.clone(), a.iter().map(|x| *b(x)).collect()),
            ExprKind::Variant { enum_name, variant, fields } => ExprKind::Variant { enum_name: enum_name.clone(), variant: variant.clone(), fields: fields.iter().map(|(n, x)| (n.clone(), *b(x))).collect() },
            ExprKind::Field(x, n) => ExprKind::Field(b(x), n.clone()),
            ExprKind::In(l, r) => {
                let l = b(l);
                ExprKind::In(l, b(r))
            }
            ExprKind::InRange(x, n) => ExprKind::InRange(b(x), n.clone()),
            ExprKind::InDomain(x, n) => ExprKind::InDomain(b(x), n.clone()),
            ExprKind::Index(l, r) => {
                let l = b(l);
                ExprKind::Index(l, b(r))
            }
            ExprKind::Slice(x, y, z) => {
                let x = b(x);
                let y = b(y);
                ExprKind::Slice(x, y, b(z))
            }
            ExprKind::IfVal(x, y, z) => {
                let x = b(x);
                let y = b(y);
                ExprKind::IfVal(x, y, b(z))
            }
            ExprKind::Method(m) => {
                let mut g = |x: &Expr| f(x);
                let m2 = match &**m {
                    Method::Len(x) => Method::Len(g(x)),
                    Method::IsEmpty(x) => Method::IsEmpty(g(x)),
                    Method::Sum(x) => Method::Sum(g(x)),
                    Method::First(x) => Method::First(g(x)),
                    Method::Last(x) => Method::Last(g(x)),
                    Method::Abs(x) => Method::Abs(g(x)),
                    Method::IsSome(x) => Method::IsSome(g(x)),
                    Method::IsNone(x) => Method::IsNone(g(x)),
                    Method::Unwrap(x) => Method::Unwrap(g(x)),
                    Method::AsBytes(x) => Method::AsBytes(g(x)),
                    Method::BitCount(k, x) => Method::BitCount(*k, g(x)),
                    Method::Contains(x, y) => {
                        let x = g(x);
                        Method::Contains(x, g(y))
                    }
                    Method::Min(x, y) => {
                        let x = g(x);
                        Method::Min(x, g(y))
                    }
                    Method::Max(x, y) => {
                        let x = g(x);
                        Method::Max(x, g(y))
                    }
                    Method::Pow(x, y) => {
                        let x = g(x);
                        Method::Pow(x, g(y))
                    }
                    Method::MapGet(x, y) => {
                        let x = g(x);
                        Method::MapGet(x, g(y))
                    }
                    Method::ContainsKey(x, y) => {
                        let x = g(x);
                        Method::ContainsKey(x, g(y))
                    }
                    Method::Rotate(l, x, y) => {
                        let x = g(x);
                        Method::Rotate(*l, x, g(y))
                    }
                    Method::Wrapping(op, x, y) => {
                        let x = g(x);
                        Method::Wrapping(*op, x, g(y))
                    }
                    Method::Count { seq, var, pred } => Method::Count { seq: g(seq), var: var.clone(), pred: pred.clone() },
                    Method::All { seq, var, pred } => Method::All { seq: g(seq), var: var.clone(), pred: pred.clone() },
                    Method::Any { seq, var, pred } => Method::Any { seq: g(seq), var: var.clone(), pred: pred.clone() },
                    Method::Windows2All { seq, var, pred } => Method::Windows2All { seq: g(seq), var: var.clone(), pred: pred.clone() },
                    Method::SizeBound { .. } | Method::SizeBits => (**m).clone(),
                };
                ExprKind::Method(Box::new(m2))
            }
        };
        Expr::new(self.span, k)
    }
    /// Is this a bit operation: a bit operator, or a method whose meaning
    /// depends on the width (`count_ones`, `rotate_left`, `wrapping_add`, …)?
    pub fn is_bit_op(&self) -> bool {
        match &self.kind {
            ExprKind::Bin(op, _, _) => op.is_bits(),
            ExprKind::Method(m) => matches!(&**m, Method::BitCount(..) | Method::Rotate(..) | Method::Wrapping(..)),
            _ => false,
        }
    }
    pub fn calls(&self, f: &str) -> bool {
        let rec = |x: &Expr| x.calls(f);
        match &self.kind {
            ExprKind::Call(g, args) => g == f || args.iter().any(rec),
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::Old(_) => false,
            ExprKind::Bin(_, l, r) | ExprKind::In(l, r) | ExprKind::Index(l, r) => rec(l) || rec(r),
            ExprKind::Not(x) | ExprKind::Neg(x) | ExprKind::Cast(x, _) | ExprKind::InRange(x, _) | ExprKind::InDomain(x, _) | ExprKind::Field(x, _) => rec(x),
            ExprKind::Ctor(_, a) => a.iter().any(rec),
            ExprKind::Variant { fields, .. } => fields.iter().any(|(_, e)| rec(e)),
            ExprKind::Slice(a, b, c) | ExprKind::IfVal(a, b, c) => rec(a) || rec(b) || rec(c),
            ExprKind::Method(m) => m.children().iter().any(|x| x.calls(f)),
        }
    }
    /// The names of every function the expression calls (`range(f)` and
    /// `domain(f)` mention `f` without calling it).
    pub fn callees(&self, out: &mut Vec<String>) {
        let mut rec = |x: &Expr| x.callees(out);
        match &self.kind {
            ExprKind::Call(g, args) => {
                out.push(g.clone());
                args.iter().for_each(|a| a.callees(out));
            }
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::Old(_) => {}
            ExprKind::Bin(_, l, r) | ExprKind::In(l, r) | ExprKind::Index(l, r) => {
                rec(l);
                rec(r);
            }
            ExprKind::Not(x) | ExprKind::Neg(x) | ExprKind::Cast(x, _) | ExprKind::InRange(x, _) | ExprKind::InDomain(x, _) | ExprKind::Field(x, _) => rec(x),
            ExprKind::Ctor(_, a) => a.iter().for_each(|x| x.callees(out)),
            ExprKind::Variant { fields, .. } => fields.iter().for_each(|(_, e)| e.callees(out)),
            ExprKind::Slice(a, b, c) | ExprKind::IfVal(a, b, c) => {
                rec(a);
                rec(b);
                rec(c);
            }
            ExprKind::Method(m) => m.children().iter().for_each(|x| x.callees(out)),
        }
    }
}

/// The std vocabulary (DESIGN.md §4).
#[derive(Clone, Debug)]
pub enum Method {
    Len(Expr),
    IsEmpty(Expr),
    Contains(Expr, Expr),
    /// `s.iter().filter(|var| pred).count()`
    Count { seq: Expr, var: String, pred: Expr },
    All { seq: Expr, var: String, pred: Expr },
    Any { seq: Expr, var: String, pred: Expr },
    Sum(Expr),
    First(Expr),
    Last(Expr),
    Abs(Expr),
    Min(Expr, Expr),
    Max(Expr, Expr),
    Pow(Expr, Expr),
    IsSome(Expr),
    IsNone(Expr),
    Unwrap(Expr),
    /// `s.windows(2).all(|w| pred)` where `pred` uses `w[0]` and `w[1]`.
    Windows2All { seq: Expr, var: String, pred: Expr },
    /// `s.as_bytes()` on a string: the identity (strings are byte sequences).
    AsBytes(Expr),
    /// `m.get(&k)` on a map: `Option<V>`.
    MapGet(Expr, Expr),
    /// `m.contains_key(&k)` on a map.
    ContainsKey(Expr, Expr),
    /// `x.count_ones()` and kin, on a machine integer: the same Lean
    /// definition as the implementation's model of the method.
    BitCount(BitCount, Expr),
    /// `x.rotate_left(n)` (`true`) / `x.rotate_right(n)`: Lean core's
    /// `BitVec.rotateLeft`/`rotateRight` on `x`'s bits, as Aeneas models them.
    Rotate(bool, Expr, Expr),
    /// `x.wrapping_add(y)`, `wrapping_sub`, `wrapping_mul` (`BinOp::Add`,
    /// `Sub`, `Mul`): the exact result reduced to `x`'s width (two's
    /// complement for a signed `x`).
    Wrapping(BinOp, Expr, Expr),
    /// `usize::MAX` (`false, true`), `isize::MAX` (`true, true`), `isize::MIN`
    /// (`true, false`): bounds of the widths Aeneas leaves open (32 or 64
    /// bits). The fixed widths' bounds are parsed as literals.
    SizeBound { signed: bool, max: bool },
    /// `usize::BITS` / `isize::BITS`: the width Aeneas leaves open.
    SizeBits,
}

/// The bit-counting methods of Rust's integer types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitCount {
    CountOnes,
    CountZeros,
    LeadingZeros,
    LeadingOnes,
    TrailingZeros,
    TrailingOnes,
}

impl BitCount {
    pub fn from_name(n: &str) -> Option<BitCount> {
        Some(match n {
            "count_ones" => BitCount::CountOnes,
            "count_zeros" => BitCount::CountZeros,
            "leading_zeros" => BitCount::LeadingZeros,
            "leading_ones" => BitCount::LeadingOnes,
            "trailing_zeros" => BitCount::TrailingZeros,
            "trailing_ones" => BitCount::TrailingOnes,
            _ => return None,
        })
    }
    /// The count of a value whose `BitVec` is `bv`, as a Lean `Nat`: Aeneas's
    /// own `leading_zeros`, and for the rest the definitions of
    /// `cargo-djinn`'s models (Lean core's `cpop`, `clz`, `ctz`).
    pub fn lean(self, bv: &str) -> String {
        match self {
            BitCount::CountOnes => format!("({bv}).cpop.toNat"),
            BitCount::CountZeros => format!("(~~~({bv})).cpop.toNat"),
            BitCount::LeadingZeros => format!("(Aeneas.Std.BitVec.leadingZeros ({bv}))"),
            BitCount::LeadingOnes => format!("(~~~({bv})).clz.toNat"),
            BitCount::TrailingZeros => format!("({bv}).ctz.toNat"),
            BitCount::TrailingOnes => format!("(~~~({bv})).ctz.toNat"),
        }
    }
    /// Rust's result on a value of `bits` bits.
    pub fn eval(self, v: u128, bits: u32) -> u32 {
        let mask = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
        let v = v & mask;
        let inv = !v & mask;
        match self {
            BitCount::CountOnes => v.count_ones(),
            BitCount::CountZeros => inv.count_ones(),
            BitCount::LeadingZeros => if v == 0 { bits } else { bits - (128 - v.leading_zeros()) },
            BitCount::LeadingOnes => if inv == 0 { bits } else { bits - (128 - inv.leading_zeros()) },
            BitCount::TrailingZeros => if v == 0 { bits } else { v.trailing_zeros() },
            BitCount::TrailingOnes => if inv == 0 { bits } else { inv.trailing_zeros() },
        }
    }
}

impl Method {
    /// The sub-expressions, binder bodies included.
    pub fn children(&self) -> Vec<&Expr> {
        match self {
            Method::Len(x) | Method::IsEmpty(x) | Method::Sum(x) | Method::First(x) | Method::Last(x) | Method::Abs(x) | Method::IsSome(x) | Method::IsNone(x) | Method::Unwrap(x) | Method::AsBytes(x) => vec![x],
            Method::Contains(a, b) | Method::Min(a, b) | Method::Max(a, b) | Method::Pow(a, b) | Method::MapGet(a, b) | Method::ContainsKey(a, b) | Method::Rotate(_, a, b) | Method::Wrapping(_, a, b) => vec![a, b],
            Method::BitCount(_, x) => vec![x],
            Method::SizeBound { .. } | Method::SizeBits => vec![],
            Method::Count { seq, pred, .. } | Method::All { seq, pred, .. } | Method::Any { seq, pred, .. } | Method::Windows2All { seq, pred, .. } => vec![seq, pred],
        }
    }
    /// Is the result a proposition (rather than a value)?
    pub fn is_prop(&self) -> bool {
        matches!(self, Method::IsEmpty(_) | Method::Contains(..) | Method::All { .. } | Method::Any { .. } | Method::Windows2All { .. } | Method::IsSome(_) | Method::IsNone(_) | Method::ContainsKey(..))
    }
}

// ----------------------------------------------------------- user types

/// A `struct` or `enum` declared in the specification file next to the
/// `djinn!` blocks, a `const` (its value is substituted as a literal), and
/// the file's ordinary functions, which constraints may call as *ambient*
/// functions (DESIGN.md §3): trusted Rust written by the human, denoted by
/// its Aeneas translation.
#[derive(Clone, Debug, Default)]
pub struct TypeDefs {
    pub enums: std::collections::HashMap<String, EnumDef>,
    pub structs: std::collections::HashMap<String, StructDef>,
    pub consts: std::collections::HashMap<String, Const>,
    pub ambient: std::collections::HashMap<String, Ambient>,
    /// Functions of the file a constraint cannot call, with the reason.
    pub ambient_errors: std::collections::HashMap<String, String>,
}

/// An ordinary Rust function of the specification file, callable from
/// constraints: `r == helper(x)` means `helper x = ok r` in Lean.
#[derive(Clone, Debug)]
pub struct Ambient {
    pub name: String,
    pub params: Vec<(String, RType)>,
    pub ret: RType,
    pub span: Span,
    /// The item's tokens in canonical form (so that editing it marks every
    /// declaration that calls it as changed).
    pub source: String,
}

#[derive(Clone, Debug)]
pub struct EnumDef {
    pub name: String,
    pub variants: Vec<VariantDef>,
}

#[derive(Clone, Debug)]
pub struct VariantDef {
    pub name: String,
    /// Field names (`None` for tuple variants) and types, in declaration
    /// order — the order of the Lean constructor's arguments.
    pub fields: Vec<(Option<String>, RType)>,
}

#[derive(Clone, Debug)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<(String, RType)>,
}

#[derive(Clone, Debug)]
pub struct Const {
    pub name: String,
    pub ty: RType,
    /// The literal, as a specification expression.
    pub value: Expr,
    /// An array constant (`const T: &[u32] = &[…]` or `[u32; N] = […]`): its
    /// integer elements in decimal, `ty` being the sequence type. `Spec.lean`
    /// defines it once, as a `List` of Aeneas scalars named after the
    /// constant, and constraints refer to it by that name.
    pub table: Option<Vec<String>>,
}

/// A parsed specification file: its declarations and the user types.
#[derive(Clone, Debug, Default)]
pub struct Program {
    pub decls: Vec<Decl>,
    pub types: TypeDefs,
    /// Every declaration, type, constant and ambient function → the index of
    /// the specification file defining it (see `parse_sources`).
    pub origin: std::collections::HashMap<String, usize>,
}

#[derive(Debug, Clone)]
pub struct Error {
    pub span: Span,
    pub msg: String,
    /// Index of the specification file the span is in (0 for a single file).
    pub file: usize,
}

impl Error {
    pub fn new(span: Span, msg: impl Into<String>) -> Self {
        Error { span, msg: msg.into(), file: 0 }
    }
    pub fn in_file(mut self, file: usize) -> Self {
        self.file = file;
        self
    }
}

pub type Result<T> = std::result::Result<T, Error>;
