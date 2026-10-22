//! Parsing a `djinn! { … }` block: items with a Rust-looking header (parsed
//! with syn) and a body in the constraint DSL (parsed over token trees; the
//! atoms are Rust expressions parsed with syn after a small rewrite of the
//! `in` / `not in` operators).

use crate::ast::*;
use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use quote::ToTokens;
use syn::parse::{Parse, ParseStream, Parser};
use syn::spanned::Spanned;

/// Parse a `djinn! { … }` block: a sequence of items, each
/// `[#[attr]…] [pub] (fn|rel) name(params) [-> [out:] T] { constraints }`.
pub fn parse_block(tokens: TokenStream) -> Result<Vec<Decl>> {
    let tts: Vec<TokenTree> = tokens.into_iter().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < tts.len() {
        let start = i;
        // attributes
        while i < tts.len() && is_punct(&tts[i], '#') {
            i += 2; // `#` and the `[…]` group
        }
        // visibility
        if i < tts.len() && is_ident(&tts[i], "pub") {
            i += 1;
            if i < tts.len() && matches!(&tts[i], TokenTree::Group(g) if g.delimiter() == Delimiter::Parenthesis) {
                i += 1;
            }
        }
        let kw_pos = i;
        let kind = match tts.get(i) {
            Some(t) if is_ident(t, "fn") => Kind::Func,
            Some(t) if is_ident(t, "rel") => Kind::Rel,
            Some(t) => return Err(Error::new(t.span(), "expected `fn` or `rel` (after optional attributes and `pub`)")),
            None => break,
        };
        // the item ends with its body: the first brace group after the keyword
        let mut j = kw_pos + 1;
        while j < tts.len() && is_brace(&tts[j]).is_none() {
            j += 1;
        }
        if j >= tts.len() {
            return Err(Error::new(tts[kw_pos].span(), "declaration has no `{ … }` body"));
        }
        let mut item: Vec<TokenTree> = tts[start..=j].to_vec();
        let source = crate::project::canonical_trees(&item);
        // `rel` is our keyword: hand `parse_decl` a Rust-shaped header
        if kind == Kind::Rel {
            item[kw_pos - start] = TokenTree::Ident(Ident::new("fn", tts[kw_pos].span()));
        }
        let mut d = parse_decl(kind, item.into_iter().collect())?;
        d.source = source;
        out.push(d);
        i = j + 1;
    }
    Ok(out)
}

pub fn parse_decl(kind: Kind, tokens: TokenStream) -> Result<Decl> {
    let span = tokens.clone().into_iter().next().map(|t| t.span()).unwrap_or_else(Span::call_site);
    let source = crate::project::canonical(&tokens);
    let header = (|input: ParseStream| -> syn::Result<Header> {
        let attrs = input.call(syn::Attribute::parse_outer)?;
        let vis: syn::Visibility = input.parse()?;
        input.parse::<syn::Token![fn]>()?;
        let name: Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let params_tokens: TokenStream = content.fork().parse()?;
        let params = content.parse_terminated(syn::FnArg::parse, syn::Token![,])?;
        let mut ret = None;
        if input.peek(syn::Token![->]) {
            input.parse::<syn::Token![->]>()?;
            let fork = input.fork();
            let named = fork.peek(syn::Ident) && fork.peek2(syn::Token![:]) && !fork.peek2(syn::Token![::]);
            let out_name = if named {
                let n: Ident = input.parse()?;
                input.parse::<syn::Token![:]>()?;
                Some(n)
            } else {
                None
            };
            let ty: syn::Type = input.parse()?;
            ret = Some((out_name, ty));
        }
        let body;
        syn::braced!(body in input);
        let body_tokens: TokenStream = body.parse()?;
        Ok(Header { attrs, vis, name, params_tokens, params: params.into_iter().collect(), ret, body_tokens })
    })
    .parse2(tokens)
    .map_err(|e| Error::new(e.span(), format!("{e}")))?;

    // Parameters.
    let mut params = Vec::new();
    for arg in &header.params {
        match arg {
            syn::FnArg::Typed(pt) => {
                let name = match &*pt.pat {
                    syn::Pat::Ident(pi) => pi.ident.to_string(),
                    other => return Err(Error::new(other.span(), "parameters must be plain identifiers")),
                };
                let (ty, mut_ref) = convert_type(&pt.ty)?;
                params.push(Param { name, ty, mut_ref, span: pt.span() });
            }
            syn::FnArg::Receiver(r) => return Err(Error::new(r.span(), "`self` parameters are not supported")),
        }
    }
    let name = header.name.to_string();
    let name_span = header.name.span();

    // Return value.
    let mut ret_tokens = None;
    let ret = match &header.ret {
        None => None,
        Some((out_name, ty)) => {
            ret_tokens = Some(ty.to_token_stream());
            let (rty, is_mut) = convert_type(ty)?;
            if is_mut || matches!(ty, syn::Type::Reference(_)) {
                return Err(Error::new(ty.span(), "a declaration may not return a borrow"));
            }
            if rty == RType::Unit {
                None
            } else {
                let n = match out_name {
                    Some(n) => n.to_string(),
                    None => "result".to_string(),
                };
                Some((n, rty))
            }
        }
    };

    // Attributes: requires / ensures / total / decreases.
    let mut requires = Vec::new();
    let mut requires_spans = Vec::new();
    let mut ensures = Vec::new();
    let mut decreases = Vec::new();
    let mut total = false;
    let mut override_smoke_test = false;
    let mut weakly_specified = false;
    for attr in &header.attrs {
        let path = attr.path().segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
        match (path.as_str(), &attr.meta) {
            ("requires", syn::Meta::List(ml)) => {
                requires.push(parse_expr_tokens(ml.tokens.clone())?);
                requires_spans.push(ml.tokens.clone().into_iter().next().map(|t| t.span()).unwrap_or(attr.span()));
            }
            ("ensures", syn::Meta::List(ml)) => ensures.push(parse_expr_tokens(ml.tokens.clone())?),
            ("decreases", syn::Meta::List(ml)) => {
                let tts: Vec<TokenTree> = ml.tokens.clone().into_iter().collect();
                for part in split_at(&tts, |t| is_punct(t, ',')) {
                    if !part.is_empty() {
                        decreases.push(parse_expr_tts(part, attr.span())?);
                    }
                }
                if decreases.is_empty() {
                    return Err(Error::new(attr.span(), "`#[decreases(..)]` needs at least one measure"));
                }
            }
            ("total", syn::Meta::Path(_)) => total = true,
            ("override_smoke_test", syn::Meta::Path(_)) => override_smoke_test = true,
            ("weakly_specified", syn::Meta::Path(_)) => weakly_specified = true,
            _ => {
                return Err(Error::new(
                    attr.span(),
                    "unknown attribute: expected #[requires(..)], #[ensures(..)], #[total], #[decreases(..)], #[override_smoke_test] or #[weakly_specified]",
                ))
            }
        }
    }
    if total && kind == Kind::Func {
        return Err(Error::new(span, "`total` applies to rels only; a func is total by construction"));
    }
    if weakly_specified && kind == Kind::Rel {
        return Err(Error::new(span, "`weakly_specified` applies to fns only; a rel is ambiguous by nature"));
    }
    if kind == Kind::Func {
        let uses_int = params.iter().any(|p| p.ty == RType::MathInt) || matches!(&ret, Some((_, RType::MathInt)));
        if uses_int {
            return Err(Error::new(name_span, "`int` is only allowed in `rel` signatures: a `fn` must be implementable, so its types must be Rust types"));
        }
    }
    if kind == Kind::Func && ret.is_none() && !params.iter().any(|p| p.mut_ref) {
        return Err(Error::new(name_span, "a func needs an output: a return value or a `&mut` parameter"));
    }

    let body_tts: Vec<TokenTree> = header.body_tokens.into_iter().collect();
    let body = parse_stmts(&body_tts, span)?;
    if body.is_empty() {
        return Err(Error::new(span, "the body must contain at least one constraint"));
    }

    let decl = Decl {
        kind,
        name,
        name_span,
        params,
        ret,
        requires,
        ensures,
        total,
        override_smoke_test,
        weakly_specified,
        decreases,
        body,
        requires_spans,
        file: 0,
        vis_tokens: header.vis.to_token_stream(),
        params_tokens: header.params_tokens,
        ret_tokens,
        source,
    };
    if decl.kind == Kind::Rel && !decl.choices().is_empty() {
        return Err(Error::new(name_span, "`any` is for fns: a rel is ambiguous by nature, say `some`"));
    }
    if !decl.choices().is_empty() && !decl.weakly_specified {
        return Err(Error::new(name_span, format!("`{}` leaves a choice to the implementer (`any`): mark it `#[weakly_specified]`, so that a human reviews it", decl.name)));
    }
    if decl.is_recursive() && decl.decreases.is_empty() {
        return Err(Error::new(name_span, format!("`{}` is recursive: give a measure that decreases at every recursive call with `#[decreases(..)]` (mathematical integers, lexicographic)", decl.name)));
    }
    if !decl.is_recursive() && !decl.decreases.is_empty() {
        return Err(Error::new(name_span, "`#[decreases(..)]` is only meaningful on a recursive declaration"));
    }
    crate::check::check_scope(&decl)?;
    Ok(decl)
}

struct Header {
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    name: Ident,
    params_tokens: TokenStream,
    params: Vec<syn::FnArg>,
    ret: Option<(Option<Ident>, syn::Type)>,
    body_tokens: TokenStream,
}

/// Rust type → `RType`; the bool says whether it was `&mut T`.
pub fn convert_type(ty: &syn::Type) -> Result<(RType, bool)> {
    match ty {
        syn::Type::Reference(r) => {
            let (inner, _) = convert_type_noref(&r.elem)?;
            Ok((inner, r.mutability.is_some()))
        }
        other => convert_type_noref(other),
    }
}

fn convert_type_noref(ty: &syn::Type) -> Result<(RType, bool)> {
    let bad = |msg: &str| Err(Error::new(ty.span(), msg.to_string()));
    match ty {
        syn::Type::Reference(_) => bad("nested references (`&&T`, `&[&T]`) are not supported; take `&[T]` or `&T`"),
        syn::Type::Slice(s) => Ok((RType::Seq(Box::new(convert_type(&s.elem)?.0), SeqKind::Slice), false)),
        syn::Type::Array(a) => Ok((
            RType::Seq(Box::new(convert_type(&a.elem)?.0), SeqKind::Array(a.len.to_token_stream().to_string())),
            false,
        )),
        syn::Type::Tuple(t) if t.elems.is_empty() => Ok((RType::Unit, false)),
        syn::Type::Tuple(_) => bad("tuples are not supported in specification signatures; declare a `struct` with named fields next to the block, or pass the components as separate parameters"),
        syn::Type::Paren(p) => convert_type(&p.elem),
        syn::Type::Path(p) => {
            let seg = p.path.segments.last().unwrap();
            let name = seg.ident.to_string();
            let generic = |i: usize| -> Result<RType> {
                match &seg.arguments {
                    syn::PathArguments::AngleBracketed(ab) => match ab.args.iter().nth(i) {
                        Some(syn::GenericArgument::Type(t)) => Ok(convert_type(t)?.0),
                        _ => Err(Error::new(seg.span(), "missing type argument")),
                    },
                    _ => Err(Error::new(seg.span(), "missing type argument")),
                }
            };
            let int = |signed, bits| Ok((RType::Int { signed, bits }, false));
            match name.as_str() {
                "i8" => int(true, 8),
                "i16" => int(true, 16),
                "i32" => int(true, 32),
                "i64" => int(true, 64),
                "i128" => int(true, 128),
                "isize" => int(true, 0),
                "u8" => int(false, 8),
                "u16" => int(false, 16),
                "u32" => int(false, 32),
                "u64" => int(false, 64),
                "u128" => int(false, 128),
                "usize" => int(false, 0),
                "bool" => Ok((RType::Bool, false)),
                "char" => Ok((RType::Char, false)),
                "int" => Ok((RType::MathInt, false)),
                "str" => Ok((RType::Seq(Box::new(RType::Int { signed: false, bits: 8 }), SeqKind::Str), false)),
                "Vec" => Ok((RType::Seq(Box::new(generic(0)?), SeqKind::Vec), false)),
                "Option" => Ok((RType::Option(Box::new(generic(0)?)), false)),
                "Result" => Ok((RType::Result(Box::new(generic(0)?), Box::new(generic(1)?)), false)),
                "String" => Ok((RType::Seq(Box::new(RType::Int { signed: false, bits: 8 }), SeqKind::String), false)),
                "HashMap" => Ok((RType::Map(Box::new(generic(0)?), Box::new(generic(1)?)), false)),
                "f16" | "f32" | "f64" | "f128" => bad("floating-point types have no Aeneas model (Aeneas's Lean backend defines no F32/F64), so they cannot be verified; use integers"),
                "HashSet" | "BTreeMap" | "BTreeSet" | "VecDeque" | "BinaryHeap" | "LinkedList" => bad(&format!("`{name}` has no model (of the standard library's collections, only `Vec`, slices, arrays and `HashMap` are modeled); use a `HashMap` or a `Vec`")),
                "Box" | "Rc" | "Arc" | "RefCell" | "Cell" | "Mutex" => bad(&format!("`{name}` has no place in a specification: it describes values, not ownership; use the value's type")),
                _ if seg.arguments.is_empty() => Ok((RType::Named(name), false)),
                _ => bad("generic user types are not supported in specification signatures"),
            }
        }
        _ => bad("unsupported type in a specification signature; supported: integers, bool, char, &str, slices `&[T]`, `Vec<T>`, arrays, `Option<T>`, `Result<T, E>`, and the `struct`s/`enum`s declared next to the block (`int` in rels)"),
    }
}

// ---------------------------------------------------------------- statements

fn is_ident(tt: &TokenTree, s: &str) -> bool {
    matches!(tt, TokenTree::Ident(i) if i == s)
}
fn is_punct(tt: &TokenTree, c: char) -> bool {
    matches!(tt, TokenTree::Punct(p) if p.as_char() == c)
}
fn is_brace(tt: &TokenTree) -> Option<&Group> {
    match tt {
        TokenTree::Group(g) if g.delimiter() == Delimiter::Brace => Some(g),
        _ => None,
    }
}
/// `=>` at position i?
fn is_fat_arrow(tts: &[TokenTree], i: usize) -> bool {
    matches!(&tts[i], TokenTree::Punct(p) if p.as_char() == '=' && p.spacing() == Spacing::Joint)
        && i + 1 < tts.len()
        && is_punct(&tts[i + 1], '>')
}
/// `..` at position i?
fn is_dotdot(tts: &[TokenTree], i: usize) -> bool {
    matches!(&tts[i], TokenTree::Punct(p) if p.as_char() == '.' && p.spacing() == Spacing::Joint)
        && i + 1 < tts.len()
        && is_punct(&tts[i + 1], '.')
}

fn parse_stmts(tts: &[TokenTree], span: Span) -> Result<Vec<Stmt>> {
    let mut out = Vec::new();
    let mut pos = 0;
    while pos < tts.len() {
        out.push(parse_one(tts, &mut pos, span)?);
    }
    Ok(out)
}

fn group_stmts(g: &Group) -> Result<Vec<Stmt>> {
    parse_stmts(&g.stream().into_iter().collect::<Vec<_>>(), g.span())
}

fn parse_one(tts: &[TokenTree], pos: &mut usize, span: Span) -> Result<Stmt> {
    let first = &tts[*pos];
    let fspan = first.span();
    let mk = |k: StmtKind| Ok(Stmt::new(fspan, k));
    // for x in SEQ { … } | for i in LO..HI { … }
    if is_ident(first, "for") {
        let (var, lo_hi_or_seq, body, end) = parse_for_head(tts, *pos + 1, fspan)?;
        *pos = end;
        return mk(match lo_hi_or_seq {
            Ok((lo, hi)) => StmtKind::ForRange { var, lo, hi, body },
            Err(seq) => StmtKind::ForIn { var, seq, body },
        });
    }
    // any x: T where c;
    if is_ident(first, "any") {
        let start = *pos + 1;
        let end = match (start..tts.len()).find(|&i| is_punct(&tts[i], ';')) {
            Some(e) => e,
            None => return Err(Error::new(fspan, "expected `any <ident>: <type> where <constraint>;`")),
        };
        let head = &tts[start..end];
        let colon = head.iter().position(|t| is_punct(t, ':'));
        let wh = head.iter().position(|t| is_ident(t, "where"));
        let (name, tyt, ct) = match (colon, wh) {
            (Some(1), Some(w)) if w > 2 && w + 1 < head.len() => (head[0].to_string(), &head[2..w], &head[w + 1..]),
            (Some(1), None) => return Err(Error::new(fspan, "`any` needs a `where` clause: say what the implementer's choice must satisfy (`where true` if anything goes)")),
            _ => return Err(Error::new(fspan, "expected `any <ident>: <type> where <constraint>;`")),
        };
        let ty: syn::Type = syn::parse2(tyt.iter().cloned().collect()).map_err(|e| Error::new(e.span(), format!("{e}")))?;
        let wherec = parse_expr_tts(ct, fspan)?;
        *pos = end + 1;
        return mk(StmtKind::Any { name, ty: convert_type(&ty)?.0, wherec });
    }
    // some x: T, y: U { … }
    if is_ident(first, "some") {
        let start = *pos + 1;
        let (end, group) = find_brace(tts, start, fspan)?;
        let head = &tts[start..end];
        let mut binders = Vec::new();
        for part in split_at(head, |t| is_punct(t, ',')) {
            if part.is_empty() {
                continue;
            }
            let colon = part.iter().position(|t| is_punct(t, ':'));
            let (nm, tyt) = match colon {
                Some(c) if c == 1 => (part[0].to_string(), &part[c + 1..]),
                _ => return Err(Error::new(fspan, "expected `some <ident>: <type>, … { … }`")),
            };
            let ty: syn::Type = syn::parse2(tyt.iter().cloned().collect()).map_err(|e| Error::new(e.span(), format!("{e}")))?;
            binders.push((nm, convert_type(&ty)?.0));
        }
        if binders.is_empty() {
            return Err(Error::new(fspan, "`some` needs at least one binder"));
        }
        let body = group_stmts(group)?;
        *pos = end + 1;
        return mk(StmtKind::Some { binders, body });
    }
    // cases { s1; s2; … }
    if is_ident(first, "cases") {
        let group = match tts.get(*pos + 1).and_then(is_brace) {
            Some(g) => g,
            None => return Err(Error::new(fspan, "expected `cases { … }`")),
        };
        let alts = group_stmts(group)?;
        if alts.is_empty() {
            return Err(Error::new(fspan, "`cases` needs at least one alternative"));
        }
        *pos += 2;
        return mk(StmtKind::Cases(alts));
    }
    // if COND { … } [else { … } | else if …]
    if is_ident(first, "if") {
        let start = *pos + 1;
        let (end, group) = find_brace(tts, start, fspan)?;
        let cond = parse_expr_tts(&tts[start..end], fspan)?;
        let then = group_stmts(group)?;
        *pos = end + 1;
        let mut els = None;
        if matches!(tts.get(*pos), Some(t) if is_ident(t, "else")) {
            *pos += 1;
            if matches!(tts.get(*pos), Some(t) if is_ident(t, "if")) {
                let nested = parse_one(tts, pos, span)?;
                els = Some(vec![nested]);
            } else {
                let g = match tts.get(*pos).and_then(is_brace) {
                    Some(g) => g,
                    None => return Err(Error::new(fspan, "expected `else { … }`")),
                };
                els = Some(group_stmts(g)?);
                *pos += 1;
            }
        }
        return mk(StmtKind::If { cond, then, els });
    }
    // match E { PAT => { … } … }
    if is_ident(first, "match") {
        let start = *pos + 1;
        let (end, group) = find_brace(tts, start, fspan)?;
        let scrutinee = parse_expr_tts(&tts[start..end], fspan)?;
        let arms = parse_arms(&group.stream().into_iter().collect::<Vec<_>>(), group.span())?;
        if arms.is_empty() {
            return Err(Error::new(fspan, "`match` needs at least one arm"));
        }
        *pos = end + 1;
        return mk(StmtKind::Match { scrutinee, arms });
    }
    // EXPR ;   |   EXPR => STMT
    let start = *pos;
    let mut i = start;
    while i < tts.len() {
        if is_punct(&tts[i], ';') {
            let e = parse_expr_tts(&tts[start..i], fspan)?;
            *pos = i + 1;
            return mk(StmtKind::Constraint(e));
        }
        if is_fat_arrow(tts, i) {
            let c = parse_expr_tts(&tts[start..i], fspan)?;
            *pos = i + 2;
            if *pos >= tts.len() {
                return Err(Error::new(fspan, "expected a statement after `=>`"));
            }
            let s = parse_one(tts, pos, span)?;
            return mk(StmtKind::Implies(c, Box::new(s)));
        }
        i += 1;
    }
    // a constraint is a statement: it ends with `;`, as in Rust
    let _ = parse_expr_tts(&tts[start..], fspan)?; // report a malformed expression first
    Err(Error::new(tts[tts.len() - 1].span(), "missing `;` after this constraint (constraints are statements and end with `;`, like Rust)"))
}

/// After `for`: `x in HEAD { BODY }`. Returns the binder, `Ok((lo, hi))` for
/// a range or `Err(seq)`, the body and the position after the block.
#[allow(clippy::type_complexity)]
fn parse_for_head(tts: &[TokenTree], at: usize, fspan: Span) -> Result<(String, std::result::Result<(Expr, Expr), Expr>, Vec<Stmt>, usize)> {
    let var = match tts.get(at) {
        Some(TokenTree::Ident(i)) => i.to_string(),
        _ => return Err(Error::new(fspan, "expected `for <ident> in <expr> { … }`")),
    };
    if !matches!(tts.get(at + 1), Some(t) if is_ident(t, "in")) {
        return Err(Error::new(fspan, "expected `in` after the `for` binder"));
    }
    let start = at + 2;
    let (end, group) = find_brace(tts, start, fspan)?;
    let head = &tts[start..end];
    let body = group_stmts(group)?;
    if let Some(dd) = (0..head.len()).find(|&i| is_dotdot(head, i)) {
        let lo = parse_expr_tts(&head[..dd], fspan)?;
        let hi = parse_expr_tts(&head[dd + 2..], fspan)?;
        return Ok((var, Ok((lo, hi)), body, end + 1));
    }
    let seq = parse_expr_tts(head, fspan)?;
    Ok((var, Err(seq), body, end + 1))
}

/// `PAT => { stmts } [,]` or `PAT => constraint [,|;]`, repeated.
fn parse_arms(tts: &[TokenTree], span: Span) -> Result<Vec<Arm>> {
    let mut arms = Vec::new();
    let mut i = 0;
    while i < tts.len() {
        let aspan = tts[i].span();
        let start = i;
        while i < tts.len() && !is_fat_arrow(tts, i) {
            i += 1;
        }
        if i >= tts.len() {
            return Err(Error::new(aspan, "expected `pattern => …` in a `match` arm"));
        }
        let pat = parse_pattern(&tts[start..i], aspan)?;
        i += 2;
        if i >= tts.len() {
            return Err(Error::new(aspan, "expected a body after `=>`"));
        }
        let body = if let Some(g) = is_brace(&tts[i]) {
            i += 1;
            if matches!(tts.get(i), Some(t) if is_punct(t, ',')) {
                i += 1;
            }
            group_stmts(g)?
        } else {
            // a single constraint up to `,` or `;` (or the end)
            let s = i;
            while i < tts.len() && !is_punct(&tts[i], ',') && !is_punct(&tts[i], ';') {
                i += 1;
            }
            let e = parse_expr_tts(&tts[s..i], aspan)?;
            let espan = tts[s].span();
            if i < tts.len() {
                i += 1;
            }
            vec![Stmt::new(espan, StmtKind::Constraint(e))]
        };
        if body.is_empty() {
            return Err(Error::new(aspan, "a `match` arm needs at least one constraint (write `true;` for an arm that constrains nothing)"));
        }
        arms.push(Arm { span: aspan, pat, body });
    }
    let _ = span;
    Ok(arms)
}

fn parse_pattern(tts: &[TokenTree], span: Span) -> Result<Pattern> {
    if tts.len() == 1 && is_ident(&tts[0], "_") {
        return Ok(Pattern::Wild);
    }
    // Enum :: Variant [ (…) | {…} ]; `Some(x)`, `None`, `Ok(x)`, `Err(e)` are the
    // variants of `Option` and `Result`
    let builtin = |v: &str| match v {
        "Some" | "None" => Some("Option"),
        "Ok" | "Err" => Some("Result"),
        _ => None,
    };
    let (enum_name, variant, rest) = match tts {
        [TokenTree::Ident(e), TokenTree::Punct(a), TokenTree::Punct(b), TokenTree::Ident(v), rest @ ..] if a.as_char() == ':' && b.as_char() == ':' => (e.to_string(), v.to_string(), rest),
        [TokenTree::Ident(v), rest @ ..] if builtin(&v.to_string()).is_some() => (builtin(&v.to_string()).unwrap().to_string(), v.to_string(), rest),
        _ => return Err(Error::new(span, "expected a pattern `Enum::Variant`, `Enum::Variant(a, _)`, `Enum::Variant { f, g: h, .. }` or `_`")),
    };
    let fields = match rest {
        [] => PatFields::Unit,
        [TokenTree::Group(g)] if g.delimiter() == Delimiter::Parenthesis => {
            let inner: Vec<TokenTree> = g.stream().into_iter().collect();
            let mut v = Vec::new();
            for part in split_at(&inner, |t| is_punct(t, ',')) {
                match part {
                    [] => {}
                    [TokenTree::Ident(i)] if i == "_" => v.push(None),
                    [TokenTree::Ident(i)] => v.push(Some(i.to_string())),
                    _ => return Err(Error::new(g.span(), "tuple patterns bind plain identifiers or `_`")),
                }
            }
            PatFields::Tuple(v)
        }
        [TokenTree::Group(g)] if g.delimiter() == Delimiter::Brace => {
            let inner: Vec<TokenTree> = g.stream().into_iter().collect();
            let mut v = Vec::new();
            let mut dots = false;
            for part in split_at(&inner, |t| is_punct(t, ',')) {
                match part {
                    [] => {}
                    [TokenTree::Punct(a), TokenTree::Punct(b)] if a.as_char() == '.' && b.as_char() == '.' => dots = true,
                    [TokenTree::Ident(f)] => v.push((f.to_string(), Some(f.to_string()))),
                    [TokenTree::Ident(f), TokenTree::Punct(c), TokenTree::Ident(b)] if c.as_char() == ':' => v.push((f.to_string(), if b == "_" { None } else { Some(b.to_string()) })),
                    _ => return Err(Error::new(g.span(), "struct patterns are `field`, `field: binder`, `field: _` or `..`")),
                }
            }
            PatFields::Struct(v, dots)
        }
        _ => return Err(Error::new(span, "expected `Enum::Variant`, `Enum::Variant(…)` or `Enum::Variant { … }`")),
    };
    Ok(Pattern::Variant { enum_name, variant, fields })
}

fn find_brace(tts: &[TokenTree], start: usize, span: Span) -> Result<(usize, &Group)> {
    for i in start..tts.len() {
        if let Some(g) = is_brace(&tts[i]) {
            return Ok((i, g));
        }
    }
    Err(Error::new(span, "expected a `{ … }` block"))
}

fn split_at<'a>(tts: &'a [TokenTree], f: impl Fn(&TokenTree) -> bool) -> Vec<&'a [TokenTree]> {
    let mut parts = Vec::new();
    let mut last = 0;
    for (i, t) in tts.iter().enumerate() {
        if f(t) {
            parts.push(&tts[last..i]);
            last = i + 1;
        }
    }
    parts.push(&tts[last..]);
    parts
}

// --------------------------------------------------------------- expressions

fn parse_expr_tts(tts: &[TokenTree], span: Span) -> Result<Expr> {
    if tts.is_empty() {
        return Err(Error::new(span, "expected an expression"));
    }
    parse_expr_tokens(tts.iter().cloned().collect())
}

pub fn parse_expr_tokens(tokens: TokenStream) -> Result<Expr> {
    let span = tokens.clone().into_iter().next().map(|t| t.span()).unwrap_or_else(Span::call_site);
    // `A => B` inside an expression (e.g. an `ensures`): implication, as ¬A ∨ B
    let tts: Vec<TokenTree> = tokens.clone().into_iter().collect();
    if let Some(i) = (0..tts.len()).find(|&i| is_fat_arrow(&tts, i)) {
        let lhs = parse_expr_tokens(tts[..i].iter().cloned().collect())?;
        let rhs = parse_expr_tokens(tts[i + 2..].iter().cloned().collect())?;
        let nspan = lhs.span;
        return Ok(Expr::new(span, ExprKind::Bin(BinOp::Or, Box::new(Expr::new(nspan, ExprKind::Not(Box::new(lhs)))), Box::new(rhs))));
    }
    let rewritten = rewrite_in(tokens);
    let e: syn::Expr = syn::parse2(rewritten).map_err(|e| Error::new(e.span(), format!("{e}")))?;
    convert_expr(&e)
}

/// Rewrite `A in B` and `A not in B` (at comparison precedence) into calls
/// `__djinn_in(A, B)` / `__djinn_notin(A, B)` so that syn can parse them.
fn rewrite_in(tokens: TokenStream) -> TokenStream {
    let tts: Vec<TokenTree> = tokens
        .into_iter()
        .map(|t| match t {
            TokenTree::Group(g) => {
                // inside parentheses `=>` can only be an implication (statement-level `=>` and
                // `match` arms are never parenthesized): `!(A) || (B)`, which syn parses; in
                // each argument of a call (`g(a => b, c)`) and in a closure's body
                // (`all(|x| a => b)`)
                let inner = if g.delimiter() == Delimiter::Parenthesis { rewrite_implies_args(g.stream()) } else { g.stream() };
                let mut ng = Group::new(g.delimiter(), rewrite_in(inner));
                ng.set_span(g.span());
                TokenTree::Group(ng)
            }
            t => t,
        })
        .collect();
    // split at depth-0 `&&`, `||` and keep the separators
    let mut out: Vec<TokenTree> = Vec::new();
    let mut seg: Vec<TokenTree> = Vec::new();
    let mut i = 0;
    let flush = |seg: &mut Vec<TokenTree>, out: &mut Vec<TokenTree>| {
        out.extend(rewrite_in_segment(std::mem::take(seg)));
    };
    while i < tts.len() {
        let two = i + 1 < tts.len();
        let is_andor = two
            && matches!(&tts[i], TokenTree::Punct(p) if (p.as_char() == '&' || p.as_char() == '|') && p.spacing() == Spacing::Joint)
            && matches!((&tts[i], &tts[i+1]), (TokenTree::Punct(a), TokenTree::Punct(b)) if a.as_char() == b.as_char());
        // a comma separates call arguments: `f(a > 0, b > 0)` is two comparisons, not a chain
        let is_boundary = is_ident(&tts[i], "if") || is_ident(&tts[i], "else") || is_brace(&tts[i]).is_some() || is_punct(&tts[i], ',');
        if is_andor {
            flush(&mut seg, &mut out);
            out.push(tts[i].clone());
            out.push(tts[i + 1].clone());
            i += 2;
        } else if is_boundary {
            flush(&mut seg, &mut out);
            out.push(tts[i].clone());
            i += 1;
        } else {
            seg.push(tts[i].clone());
            i += 1;
        }
    }
    flush(&mut seg, &mut out);
    out.into_iter().collect()
}

/// `rewrite_implies` on each comma-separated part of a parenthesized group (the
/// arguments of a call, the elements of a tuple), and on the body of a part that
/// is a closure `|x| body` (whose body extends to the end of the part).
fn rewrite_implies_args(tokens: TokenStream) -> TokenStream {
    let tts: Vec<TokenTree> = tokens.into_iter().collect();
    let mut out: Vec<TokenTree> = Vec::new();
    let mut rest = &tts[..];
    loop {
        let end = rest.iter().position(|t| is_punct(t, ',')).unwrap_or(rest.len());
        let part = &rest[..end];
        // a closure's parameters `|…|` (or `move |…|`, `||`) stay; its body is rewritten
        let start = usize::from(part.first().is_some_and(|t| is_ident(t, "move")));
        let body_at = match (part.get(start), part.get(start + 1)) {
            (Some(a), Some(b)) if is_punct(a, '|') && is_punct(b, '|') => start + 2,
            (Some(a), _) if is_punct(a, '|') => part.iter().skip(start + 1).position(|t| is_punct(t, '|')).map(|j| start + j + 2).unwrap_or(0),
            _ => 0,
        };
        out.extend(part[..body_at].iter().cloned());
        out.extend(rewrite_implies(part[body_at..].iter().cloned().collect()));
        if end == rest.len() {
            break;
        }
        out.push(rest[end].clone());
        rest = &rest[end + 1..];
    }
    out.into_iter().collect()
}

/// `A => B` (right-associative, below `||`) as `!(A) || (B)`, at the top level of `tokens`;
/// unchanged without a top-level `=>`.
fn rewrite_implies(tokens: TokenStream) -> TokenStream {
    let tts: Vec<TokenTree> = tokens.into_iter().collect();
    let Some(i) = (0..tts.len()).find(|&i| is_fat_arrow(&tts, i)) else { return tts.into_iter().collect() };
    let span = tts[i].span();
    let lhs: TokenStream = tts[..i].iter().cloned().collect();
    let rhs = rewrite_implies(tts[i + 2..].iter().cloned().collect());
    let mut out = TokenStream::new();
    let mut bang = Punct::new('!', Spacing::Alone);
    bang.set_span(span);
    out.extend([TokenTree::Punct(bang)]);
    let mut gl = Group::new(Delimiter::Parenthesis, lhs);
    gl.set_span(span);
    out.extend([TokenTree::Group(gl)]);
    let mut o1 = Punct::new('|', Spacing::Joint);
    o1.set_span(span);
    let mut o2 = Punct::new('|', Spacing::Alone);
    o2.set_span(span);
    out.extend([TokenTree::Punct(o1), TokenTree::Punct(o2)]);
    let mut gr = Group::new(Delimiter::Parenthesis, rhs);
    gr.set_span(span);
    out.extend([TokenTree::Group(gr)]);
    out
}

/// Comparison operators at the top level of a segment: (start index, width).
fn cmp_ops(seg: &[TokenTree]) -> Vec<(usize, usize)> {
    let mut ops = Vec::new();
    let mut i = 0;
    while i < seg.len() {
        if let TokenTree::Punct(p) = &seg[i] {
            let c = p.as_char();
            let next = seg.get(i + 1).and_then(|t| match t {
                TokenTree::Punct(q) => Some(q.as_char()),
                _ => None,
            });
            let joint = p.spacing() == Spacing::Joint;
            match (c, joint, next) {
                ('<', true, Some('=')) | ('>', true, Some('=')) => {
                    ops.push((i, 2));
                    i += 2;
                    continue;
                }
                ('=', true, Some('=')) | ('!', true, Some('=')) => {
                    i += 2;
                    continue;
                }
                ('=', true, Some('>')) => {
                    i += 2;
                    continue;
                }
                // `<<` and `>>` are shifts, not two comparisons
                ('<', true, Some('<')) | ('>', true, Some('>')) => {
                    i += 2;
                    continue;
                }
                (':', true, Some(':')) => {
                    i += 2;
                    continue;
                }
                ('<', _, _) | ('>', _, _) if !joint => {
                    ops.push((i, 1));
                }
                _ => {}
            }
        }
        i += 1;
    }
    ops
}

/// `a <= b < c` → `(a <= b) && (b < c)`.
fn rewrite_chain(seg: &[TokenTree]) -> Option<Vec<TokenTree>> {
    let ops = cmp_ops(seg);
    if ops.len() < 2 {
        return None;
    }
    let mut operands: Vec<&[TokenTree]> = Vec::new();
    let mut last = 0;
    for &(i, w) in &ops {
        operands.push(&seg[last..i]);
        last = i + w;
    }
    operands.push(&seg[last..]);
    let mut out: Vec<TokenTree> = Vec::new();
    for (k, &(i, w)) in ops.iter().enumerate() {
        if k > 0 {
            let mut a = Punct::new('&', Spacing::Joint);
            a.set_span(seg[i].span());
            let mut b = Punct::new('&', Spacing::Alone);
            b.set_span(seg[i].span());
            out.push(TokenTree::Punct(a));
            out.push(TokenTree::Punct(b));
        }
        let mut inner = TokenStream::new();
        inner.extend(operands[k].iter().cloned());
        inner.extend(seg[i..i + w].iter().cloned());
        inner.extend(operands[k + 1].iter().cloned());
        let mut g = Group::new(Delimiter::Parenthesis, inner);
        g.set_span(seg[i].span());
        out.push(TokenTree::Group(g));
    }
    Some(out)
}

fn rewrite_in_segment(seg: Vec<TokenTree>) -> Vec<TokenTree> {
    if let Some(chain) = rewrite_chain(&seg) {
        return chain;
    }
    let pos = seg.iter().position(|t| is_ident(t, "in"));
    let Some(p) = pos else { return seg };
    let (neg, lhs_end) = if p >= 1 && is_ident(&seg[p - 1], "not") { (true, p - 1) } else { (false, p) };
    let lhs: TokenStream = seg[..lhs_end].iter().cloned().collect();
    let rhs: TokenStream = seg[p + 1..].iter().cloned().collect();
    let span = seg[p].span();
    let name = Ident::new(if neg { "__djinn_notin" } else { "__djinn_in" }, span);
    let mut args = TokenStream::new();
    args.extend(lhs);
    args.extend(std::iter::once(TokenTree::Punct(Punct::new(',', Spacing::Alone))));
    args.extend(rhs);
    let mut g = Group::new(Delimiter::Parenthesis, args);
    g.set_span(span);
    vec![TokenTree::Ident(name), TokenTree::Group(g)]
}

/// `Enum::Variant` from a two-segment path (the variant capitalized).
/// `u32::MAX`, `i8::MIN`, `u16::BITS`, `usize::MAX`, …: a literal for a
/// fixed width; `usize::MAX`, `isize::MAX` and `isize::MIN` stay symbolic
/// (Aeneas leaves the width of `usize` open).
fn int_const(p: &syn::Path, span: proc_macro2::Span) -> Option<ExprKind> {
    if p.segments.len() != 2 || p.segments.iter().any(|s| !s.arguments.is_empty()) {
        return None;
    }
    let (signed, bits): (bool, u32) = match p.segments[0].ident.to_string().as_str() {
        "u8" => (false, 8),
        "u16" => (false, 16),
        "u32" => (false, 32),
        "u64" => (false, 64),
        "u128" => (false, 128),
        "usize" => (false, 0),
        "i8" => (true, 8),
        "i16" => (true, 16),
        "i32" => (true, 32),
        "i64" => (true, 64),
        "i128" => (true, 128),
        "isize" => (true, 0),
        _ => return None,
    };
    let lit = |v: u128| ExprKind::Int(v.to_string());
    let pow = |k: u32| if k == 128 { u128::MAX } else { (1u128 << k) - 1 };
    Some(match (p.segments[1].ident.to_string().as_str(), bits) {
        ("MAX", 0) => ExprKind::Method(Box::new(Method::SizeBound { signed, max: true })),
        ("MIN", 0) if signed => ExprKind::Method(Box::new(Method::SizeBound { signed, max: false })),
        ("MIN", _) if !signed => lit(0),
        ("MAX", b) if signed => lit(pow(b - 1)),
        ("MAX", b) => lit(pow(b)),
        ("MIN", b) => ExprKind::Neg(Box::new(Expr::new(span, lit(pow(b - 1) + 1)))),
        ("BITS", b) if b > 0 => lit(b as u128),
        ("BITS", _) => ExprKind::Method(Box::new(Method::SizeBits)),
        _ => return None,
    })
}

fn variant_path(p: &syn::Path) -> Option<(String, String)> {
    if p.segments.len() == 2 && p.segments.iter().all(|s| s.arguments.is_empty()) {
        let e = p.segments[0].ident.to_string();
        let v = p.segments[1].ident.to_string();
        if v.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
            return Some((e, v));
        }
    }
    None
}

fn convert_expr(e: &syn::Expr) -> Result<Expr> {
    use syn::Expr as S;
    let span = e.span();
    let err = |m: &str| Err(Error::new(span, m.to_string()));
    let mk = |k: ExprKind| Ok(Expr::new(span, k));
    match e {
        S::Lit(l) => match &l.lit {
            syn::Lit::Int(i) => mk(ExprKind::Int(i.base10_digits().to_string())),
            syn::Lit::Bool(b) => mk(ExprKind::Bool(b.value)),
            syn::Lit::Char(c) => mk(ExprKind::Char(c.value())),
            syn::Lit::Byte(b) => mk(ExprKind::Int(b.value().to_string())),
            syn::Lit::Str(s) => mk(ExprKind::Str(s.value().into_bytes())),
            syn::Lit::ByteStr(s) => mk(ExprKind::Str(s.value())),
            syn::Lit::Float(_) => err("floating-point literals are not supported (Aeneas has no float model)"),
            _ => err("only integer, boolean, char and string literals are supported"),
        },
        S::Path(p) => {
            if let Some(k) = int_const(&p.path, span) {
                return mk(k);
            }
            if let Some((en, v)) = variant_path(&p.path) {
                return mk(ExprKind::Variant { enum_name: en, variant: v, fields: vec![] });
            }
            if p.path.segments.len() != 1 {
                return err("paths are not supported; use a plain identifier (or `Enum::Variant`)");
            }
            let id = p.path.segments[0].ident.to_string();
            match id.as_str() {
                "None" => mk(ExprKind::Ctor("None".into(), vec![])),
                _ => mk(ExprKind::Var(id)),
            }
        }
        S::Paren(p) => convert_expr(&p.expr),
        S::Group(g) => convert_expr(&g.expr),
        S::Reference(r) => convert_expr(&r.expr),
        S::Cast(c) => {
            let (ty, _) = convert_type(&c.ty)?;
            mk(ExprKind::Cast(Box::new(convert_expr(&c.expr)?), ty))
        }
        S::Unary(u) => match u.op {
            syn::UnOp::Deref(_) => convert_expr(&u.expr),
            syn::UnOp::Not(_) => mk(ExprKind::Not(Box::new(convert_expr(&u.expr)?))),
            syn::UnOp::Neg(_) => mk(ExprKind::Neg(Box::new(convert_expr(&u.expr)?))),
            _ => err("unsupported unary operator"),
        },
        S::Binary(b) => {
            let op = match b.op {
                syn::BinOp::Add(_) => BinOp::Add,
                syn::BinOp::Sub(_) => BinOp::Sub,
                syn::BinOp::Mul(_) => BinOp::Mul,
                syn::BinOp::Div(_) => BinOp::Div,
                syn::BinOp::Rem(_) => BinOp::Rem,
                syn::BinOp::Eq(_) => BinOp::Eq,
                syn::BinOp::Ne(_) => BinOp::Ne,
                syn::BinOp::Lt(_) => BinOp::Lt,
                syn::BinOp::Le(_) => BinOp::Le,
                syn::BinOp::Gt(_) => BinOp::Gt,
                syn::BinOp::Ge(_) => BinOp::Ge,
                syn::BinOp::And(_) => BinOp::And,
                syn::BinOp::Or(_) => BinOp::Or,
                syn::BinOp::BitAnd(_) => BinOp::BitAnd,
                syn::BinOp::BitOr(_) => BinOp::BitOr,
                syn::BinOp::BitXor(_) => BinOp::BitXor,
                syn::BinOp::Shl(_) => BinOp::Shl,
                syn::BinOp::Shr(_) => BinOp::Shr,
                _ => return err("unsupported binary operator (assignments are not constraints)"),
            };
            let l = convert_expr(&b.left)?;
            let r = convert_expr(&b.right)?;
            // chained comparison: `a <= b < c` parses as `(a <= b) < c`
            if op.is_cmp() {
                if let ExprKind::Bin(lop, ll, lr) = &l.kind {
                    if lop.is_cmp() && *lop != BinOp::Eq && *lop != BinOp::Ne && op != BinOp::Eq && op != BinOp::Ne {
                        let left = Expr::new(l.span, ExprKind::Bin(*lop, ll.clone(), lr.clone()));
                        let right = Expr::new(span, ExprKind::Bin(op, lr.clone(), Box::new(r)));
                        return mk(ExprKind::Bin(BinOp::And, Box::new(left), Box::new(right)));
                    }
                }
            }
            mk(ExprKind::Bin(op, Box::new(l), Box::new(r)))
        }
        S::Struct(st) => {
            let Some((en, v)) = variant_path(&st.path) else {
                return err("struct literals are written `Enum::Variant { field: value, … }`");
            };
            if st.rest.is_some() {
                return err("`..` is not allowed in a constructor expression");
            }
            let mut fields = Vec::new();
            for f in &st.fields {
                let name = match &f.member {
                    syn::Member::Named(i) => i.to_string(),
                    syn::Member::Unnamed(_) => return err("tuple fields are not supported in constructor expressions"),
                };
                fields.push((Some(name), convert_expr(&f.expr)?));
            }
            mk(ExprKind::Variant { enum_name: en, variant: v, fields })
        }
        S::Field(f) => {
            let name = match &f.member {
                syn::Member::Named(i) => i.to_string(),
                syn::Member::Unnamed(_) => return err("tuple-struct fields (`.0`) are not supported"),
            };
            mk(ExprKind::Field(Box::new(convert_expr(&f.base)?), name))
        }
        S::Call(c) => {
            if let S::Path(p) = &*c.func {
                if let Some((en, v)) = variant_path(&p.path) {
                    let mut fields = Vec::new();
                    for a in &c.args {
                        fields.push((None, convert_expr(a)?));
                    }
                    return mk(ExprKind::Variant { enum_name: en, variant: v, fields });
                }
            }
            let name = match &*c.func {
                S::Path(p) if p.path.segments.len() == 1 => p.path.segments[0].ident.to_string(),
                _ => return err("calls must be to a plain name"),
            };
            // `x in range(f)` / `x in domain(f)`: the right operand names a function
            if (name == "__djinn_in" || name == "__djinn_notin") && c.args.len() == 2 {
                if let S::Call(inner) = &c.args[1] {
                    if let S::Path(ip) = &*inner.func {
                        let f = ip.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
                        if (f == "range" || f == "domain") && inner.args.len() == 1 {
                            let g = match &inner.args[0] {
                                S::Path(gp) if gp.path.segments.len() == 1 => gp.path.segments[0].ident.to_string(),
                                _ => return err("`range(f)` / `domain(f)` take a function name"),
                            };
                            let x = convert_expr(&c.args[0])?;
                            let inner_e = if f == "range" { ExprKind::InRange(Box::new(x), g) } else { ExprKind::InDomain(Box::new(x), g) };
                            return mk(if name == "__djinn_notin" { ExprKind::Not(Box::new(Expr::new(span, inner_e))) } else { inner_e });
                        }
                    }
                }
            }
            let args: Vec<Expr> = c.args.iter().map(convert_expr).collect::<Result<_>>()?;
            match name.as_str() {
                "old" => match args.as_slice() {
                    [Expr { kind: ExprKind::Var(v), .. }] => mk(ExprKind::Old(v.clone())),
                    _ => err("`old(..)` takes a parameter name"),
                },
                "__djinn_in" | "__djinn_notin" => {
                    let neg = name == "__djinn_notin";
                    let [x, s] = <[Expr; 2]>::try_from(args).map_err(|_| Error::new(span, "bad `in`"))?;
                    let inner = match s.kind {
                        ExprKind::Call(ref f, ref fa) if (f == "range" || f == "domain") && fa.len() == 1 => {
                            let g = match &fa[0].kind {
                                ExprKind::Var(g) => g.clone(),
                                _ => return err("`range(f)` / `domain(f)` take a function name"),
                            };
                            if f == "range" { ExprKind::InRange(Box::new(x), g) } else { ExprKind::InDomain(Box::new(x), g) }
                        }
                        _ => ExprKind::In(Box::new(x), Box::new(s)),
                    };
                    mk(if neg { ExprKind::Not(Box::new(Expr::new(span, inner))) } else { inner })
                }
                "Some" | "Ok" | "Err" => mk(ExprKind::Ctor(name, args)),
                "range" | "domain" => err("`range(f)` / `domain(f)` are only valid after `in`"),
                _ => mk(ExprKind::Call(name, args)),
            }
        }
        S::Index(ix) => {
            let s = convert_expr(&ix.expr)?;
            match &*ix.index {
                S::Range(r) => {
                    let lo = match &r.start {
                        Some(x) => convert_expr(x)?,
                        None => Expr::new(span, ExprKind::Int("0".into())),
                    };
                    let hi = match &r.end {
                        Some(x) => convert_expr(x)?,
                        None => Expr::new(span, ExprKind::Method(Box::new(Method::Len(s.clone())))),
                    };
                    if matches!(r.limits, syn::RangeLimits::Closed(_)) {
                        return err("use `a..b` (half-open) for slicing");
                    }
                    mk(ExprKind::Slice(Box::new(s), Box::new(lo), Box::new(hi)))
                }
                i => mk(ExprKind::Index(Box::new(s), Box::new(convert_expr(i)?))),
            }
        }
        S::If(i) => {
            let cond = convert_expr(&i.cond)?;
            let then = block_expr(&i.then_branch)?;
            let els = match &i.else_branch {
                Some((_, e)) => match &**e {
                    S::Block(b) => block_expr(&b.block)?,
                    other => convert_expr(other)?,
                },
                None => return err("a value-level `if` needs an `else`"),
            };
            mk(ExprKind::IfVal(Box::new(cond), Box::new(then), Box::new(els)))
        }
        S::Block(b) => block_expr(&b.block),
        S::MethodCall(m) => convert_method(m),
        S::Closure(_) => err("closures are only allowed inside `.iter().all/any/filter(..)` and `.windows(2).all(..)`"),
        S::Macro(m) => {
            let name = m.mac.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
            match name.as_str() {
                "println" | "print" | "eprintln" | "eprint" | "dbg" | "write" | "writeln" | "panic" | "assert" | "assert_eq" | "todo" | "unimplemented" => {
                    err(&format!("`{name}!` is not a constraint: a specification describes values and has no side effects — nothing in it is executed. Printing and I/O belong in a driver function written beside the block in plain Rust (DESIGN.md §7)"))
                }
                "format" | "vec" => err(&format!("`{name}!` is not part of the specification vocabulary; state the sequence's length and elements instead (`s.len() == …`, `s[i] == …`), or use a byte-string literal `b\"…\"`")),
                _ => err(&format!("`{name}!`: macros are not constraints; a specification is a set of relations over values")),
            }
        }
        S::Assign(_) => err("`=` is assignment in Rust and has no meaning in a specification; equality between values is `==`"),
        S::Let(_) | S::Return(_) | S::Break(_) | S::Continue(_) | S::Loop(_) | S::While(_) | S::ForLoop(_) | S::Match(_) => {
            err("this is a statement of Rust's execution model; a constraint is a proposition about values. Use the specification forms: `for x in s { … }` (every element), `some x: T { … }` (there is), `cases { … }` (one of), `if c { … } else { … }`, `c => …`")
        }
        S::Range(_) => err("a range is only meaningful as `for i in a..b { … }` or in a slice `s[a..b]`"),
        S::Try(_) | S::Await(_) | S::Async(_) | S::Unsafe(_) => err("`?`, `await`, `async` and `unsafe` have no meaning in a specification"),
        _ => err("unsupported expression form in a constraint; constraints are built from comparisons, arithmetic over mathematical integers, `&&`/`||`/`!`/`=>`, calls to the specification's funcs and rels, `x in s`, `s[i]`, `s[a..b]`, and the std methods of the vocabulary (`s.len()`, `s.contains(&x)`, `s.iter().filter(..).count()`, …)"),
    }
}

fn block_expr(b: &syn::Block) -> Result<Expr> {
    match b.stmts.as_slice() {
        [syn::Stmt::Expr(e, None)] => convert_expr(e),
        _ => Err(Error::new(b.span(), "a value block must contain exactly one expression")),
    }
}

fn closure_param(c: &syn::ExprClosure) -> Result<String> {
    if c.inputs.len() != 1 {
        return Err(Error::new(c.span(), "expected a one-argument closure"));
    }
    fn name(p: &syn::Pat) -> Option<String> {
        match p {
            syn::Pat::Ident(i) => Some(i.ident.to_string()),
            syn::Pat::Reference(r) => name(&r.pat),
            syn::Pat::Type(t) => name(&t.pat),
            syn::Pat::Paren(p) => name(&p.pat),
            _ => None,
        }
    }
    name(&c.inputs[0]).ok_or_else(|| Error::new(c.span(), "closure parameter must be an identifier"))
}

/// The vocabulary, for messages.
const VOCABULARY: &str = "`s.len()`, `s.is_empty()`, `s.contains(&x)`, `s.iter().filter(|y| p).count()`, `s.iter().all(|y| p)`, `s.iter().any(|y| p)`, `s.iter().sum()`, `s.first()`, `s.last()`, `s.windows(2).all(|w| p)`, `s.as_bytes()`, `x.abs()`, `x.pow(n)`, `a.min(b)`, `a.max(b)`, `o.is_some()`, `o.is_none()`, `o.unwrap()`, `x.count_ones()` (and `count_zeros`, `leading_zeros`, `leading_ones`, `trailing_zeros`, `trailing_ones`), `x.rotate_left(n)`, `x.rotate_right(n)`, `x.wrapping_add(y)` (and `wrapping_sub`, `wrapping_mul`)";

/// Why a method is not in the vocabulary, when the reason is a common one.
fn method_hint(name: &str) -> String {
    match name {
        "push" | "pop" | "insert" | "remove" | "clear" | "sort" | "sort_unstable" | "swap" | "truncate" | "extend" | "retain" | "dedup" | "reverse" | "push_str" | "append" | "drain" | "resize" | "fill" => {
            format!("`.{name}()` mutates its receiver, and a specification describes values, not steps: relate the output to the input instead (`v.len() == old(v).len() + 1`, `v[old(v).len()] == x`, …). The vocabulary: {VOCABULARY}")
        }
        "checked_add" | "checked_sub" | "checked_mul" | "saturating_add" | "saturating_sub" | "overflowing_add" | "rem_euclid" | "div_euclid" => {
            format!("`.{name}()` speaks about machine overflow, but specification integers are unbounded: write the plain arithmetic (`x + 1`); `/` and `%` are already Euclidean")
        }
        "map" | "fold" | "collect" | "zip" | "enumerate" | "rev" | "skip" | "take" | "chain" | "flat_map" | "position" | "find" | "max" | "min" | "max_by_key" | "min_by_key" | "cloned" | "copied" => {
            format!("`.iter().{name}(..)` is not in the vocabulary (iterator pipelines are not relations): say it with `for x in s {{ … }}`, `some i: int {{ … }}`, `s.iter().filter(|y| p).count()` or `s.iter().all/any(|y| p)`. The vocabulary: {VOCABULARY}")
        }
        "chars" | "bytes" | "to_string" | "to_owned" | "as_str" | "trim" | "split" | "starts_with" | "ends_with" | "to_uppercase" | "to_lowercase" | "parse" => {
            format!("`.{name}()`: strings are byte sequences here (Aeneas models `str` as bytes), with `s.len()`, `s[i]`, `s.as_bytes()` and `'c' as u32`; there is no model of `.{name}()`")
        }
        "get_mut" | "get_unchecked" | "iter_mut" | "as_slice" | "as_mut_slice" | "to_vec" | "clone" | "len_utf8" => {
            format!("`.{name}()` is not needed in a specification: index with `s[i]` (every value is already a mathematical view), and references are transparent")
        }
        _ => format!("`.{name}()` is not in the vocabulary. The vocabulary: {VOCABULARY}; anything else is written as a helper `rel` or `fn` in the specification"),
    }
}

fn convert_method(m: &syn::ExprMethodCall) -> Result<Expr> {
    use syn::Expr as S;
    let span = m.span();
    let name = m.method.to_string();
    let err = |msg: String| Err(Error::new(m.method.span(), msg));
    let mk = |me: Method| Ok(Expr::new(span, ExprKind::Method(Box::new(me))));
    let arg = |i: usize| -> Result<Expr> {
        match m.args.iter().nth(i) {
            Some(a) => convert_expr(a),
            None => Err(Error::new(m.span(), format!("`.{name}()` is missing an argument"))),
        }
    };
    let closure_arg = |i: usize| -> Result<(String, Expr)> {
        match m.args.iter().nth(i) {
            Some(S::Closure(c)) => Ok((closure_param(c)?, convert_expr(&c.body)?)),
            _ => Err(Error::new(m.span(), format!("`.{name}(..)` expects a closure"))),
        }
    };
    // `.iter()` chains
    if let S::MethodCall(inner) = &*m.receiver {
        let iname = inner.method.to_string();
        if iname == "iter" && inner.args.is_empty() {
            let seq = convert_expr(&inner.receiver)?;
            return match name.as_str() {
                "all" => {
                    let (var, pred) = closure_arg(0)?;
                    mk(Method::All { seq, var, pred })
                }
                "any" => {
                    let (var, pred) = closure_arg(0)?;
                    mk(Method::Any { seq, var, pred })
                }
                "sum" => mk(Method::Sum(seq)),
                _ => err(method_hint(&name)),
            };
        }
        if iname == "filter" && name == "count" {
            if let S::MethodCall(it) = &*inner.receiver {
                if it.method == "iter" && it.args.is_empty() {
                    let seq = convert_expr(&it.receiver)?;
                    let (var, pred) = match inner.args.iter().next() {
                        Some(S::Closure(c)) => (closure_param(c)?, convert_expr(&c.body)?),
                        _ => return err("`.filter(..)` expects a closure".into()),
                    };
                    return mk(Method::Count { seq, var, pred });
                }
            }
        }
        if iname == "windows" && name == "all" {
            let two = matches!(inner.args.iter().next(), Some(S::Lit(l)) if matches!(&l.lit, syn::Lit::Int(i) if i.base10_digits() == "2"));
            if !two {
                return err("only `.windows(2).all(..)` is supported".into());
            }
            let seq = convert_expr(&inner.receiver)?;
            let (var, pred) = closure_arg(0)?;
            return mk(Method::Windows2All { seq, var, pred });
        }
    }
    let recv = convert_expr(&m.receiver)?;
    mk(match name.as_str() {
        "len" => Method::Len(recv),
        "is_empty" => Method::IsEmpty(recv),
        "contains" => Method::Contains(recv, arg(0)?),
        "first" => Method::First(recv),
        "last" => Method::Last(recv),
        "abs" => Method::Abs(recv),
        "min" => Method::Min(recv, arg(0)?),
        "max" => Method::Max(recv, arg(0)?),
        "pow" => Method::Pow(recv, arg(0)?),
        "is_some" => Method::IsSome(recv),
        "is_none" => Method::IsNone(recv),
        "unwrap" => Method::Unwrap(recv),
        "as_bytes" => Method::AsBytes(recv),
        "get" => Method::MapGet(recv, arg(0)?),
        "contains_key" => Method::ContainsKey(recv, arg(0)?),
        "rotate_left" => Method::Rotate(true, recv, arg(0)?),
        "rotate_right" => Method::Rotate(false, recv, arg(0)?),
        "wrapping_add" => Method::Wrapping(BinOp::Add, recv, arg(0)?),
        "wrapping_sub" => Method::Wrapping(BinOp::Sub, recv, arg(0)?),
        "wrapping_mul" => Method::Wrapping(BinOp::Mul, recv, arg(0)?),
        n if BitCount::from_name(n).is_some() => Method::BitCount(BitCount::from_name(n).unwrap(), recv),
        "iter" => return err("`.iter()` must be followed by `.all(..)`, `.any(..)`, `.sum()` or `.filter(..).count()`".into()),
        _ => return err(method_hint(&name)),
    })
}

// --------------------------------------------------------------- user types

/// Types an ambient function may take and return: those whose specification
/// view is the Aeneas value itself.
fn ambient_type_ok(t: &RType) -> bool {
    match t {
        RType::Int { .. } | RType::Bool | RType::Char | RType::Named(_) | RType::Unit => true,
        RType::Option(e) => ambient_type_ok(e),
        RType::Result(a, b) => ambient_type_ok(a) && ambient_type_ok(b),
        RType::MathInt | RType::Seq(..) | RType::Map(..) => false,
    }
}

/// The elements of an array literal of integers (`&[1, -2, 0x3]`, `[7u16; 0]`
/// is not one: repeat expressions are not tables), in decimal; `None` for any
/// other expression. Element types and ranges are rustc's to check: the
/// specification file is compiled like any other module.
fn table_literal(e: &syn::Expr) -> Option<Vec<String>> {
    fn elem(e: &syn::Expr) -> Option<String> {
        match e {
            syn::Expr::Lit(l) => match &l.lit {
                syn::Lit::Int(i) => Some(i.base10_digits().to_string()),
                syn::Lit::Byte(b) => Some(b.value().to_string()),
                _ => None,
            },
            syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Neg(_)) => {
                let v = elem(&u.expr)?;
                Some(if v == "0" { v } else if let Some(p) = v.strip_prefix('-') { p.to_string() } else { format!("-{v}") })
            }
            syn::Expr::Paren(p) => elem(&p.expr),
            syn::Expr::Group(g) => elem(&g.expr),
            _ => None,
        }
    }
    match e {
        syn::Expr::Reference(r) => table_literal(&r.expr),
        syn::Expr::Paren(p) => table_literal(&p.expr),
        syn::Expr::Group(g) => table_literal(&g.expr),
        syn::Expr::Array(a) => a.elems.iter().map(elem).collect(),
        _ => None,
    }
}

/// `struct`, `enum`, literal `const` and `fn` items of a specification file.
pub fn collect_types(file: &syn::File) -> Result<TypeDefs> {
    let mut t = TypeDefs::default();
    for item in &file.items {
        match item {
            syn::Item::Enum(e) => {
                if !e.generics.params.is_empty() {
                    return Err(Error::new(e.ident.span(), "generic enums are not supported in specifications"));
                }
                let mut variants = Vec::new();
                for v in &e.variants {
                    let fields = match &v.fields {
                        syn::Fields::Unit => vec![],
                        syn::Fields::Unnamed(u) => u.unnamed.iter().map(|f| convert_type(&f.ty).map(|(t, _)| (None, t))).collect::<Result<Vec<_>>>()?,
                        syn::Fields::Named(n) => n.named.iter().map(|f| convert_type(&f.ty).map(|(t, _)| (f.ident.as_ref().map(|i| i.to_string()), t))).collect::<Result<Vec<_>>>()?,
                    };
                    variants.push(VariantDef { name: v.ident.to_string(), fields });
                }
                t.enums.insert(e.ident.to_string(), EnumDef { name: e.ident.to_string(), variants });
            }
            syn::Item::Struct(s) => {
                if !s.generics.params.is_empty() {
                    return Err(Error::new(s.ident.span(), "generic structs are not supported in specifications"));
                }
                let fields = match &s.fields {
                    syn::Fields::Named(n) => n.named.iter().map(|f| convert_type(&f.ty).map(|(t, _)| (f.ident.as_ref().map(|i| i.to_string()).unwrap_or_default(), t))).collect::<Result<Vec<_>>>()?,
                    _ => return Err(Error::new(s.ident.span(), "only structs with named fields are supported in specifications")),
                };
                if let syn::Fields::Named(n) = &s.fields {
                    for f in &n.named {
                        if let Some(id) = &f.ident {
                            if crate::types::RESERVED_FIELDS.contains(&id.to_string().as_str()) {
                                return Err(Error::new(id.span(), format!("a field cannot be named `{id}`: Lean defines `{}.{id}` for every structure itself (its recursor and kin), so the Aeneas translation would not compile; rename the field", s.ident)));
                            }
                        }
                    }
                }
                t.structs.insert(s.ident.to_string(), StructDef { name: s.ident.to_string(), fields });
            }
            syn::Item::Fn(f) => {
                let name = f.sig.ident.to_string();
                let span = f.sig.ident.span();
                let source = crate::project::canonical(&f.to_token_stream());
                let reason = (|| -> std::result::Result<Ambient, String> {
                    if !f.sig.generics.params.is_empty() {
                        return Err("it is generic".into());
                    }
                    if f.sig.asyncness.is_some() || f.sig.unsafety.is_some() {
                        return Err("it is `async` or `unsafe`".into());
                    }
                    let mut params = Vec::new();
                    for a in &f.sig.inputs {
                        match a {
                            syn::FnArg::Typed(pt) => {
                                let pname = match &*pt.pat {
                                    syn::Pat::Ident(pi) => pi.ident.to_string(),
                                    _ => return Err("a parameter is a pattern, not a name".into()),
                                };
                                let (t, is_mut) = convert_type(&pt.ty).map_err(|e| format!("parameter `{pname}`: {}", e.msg))?;
                                if is_mut {
                                    return Err(format!("parameter `{pname}` is `&mut`"));
                                }
                                if !ambient_type_ok(&t) {
                                    return Err(format!("parameter `{pname}` has type `{}`; ambient functions take and return scalars, `bool`, `char`, `Option`s of those and the file's `enum`s/`struct`s (sequences would need a bridge from the mathematical view)", crate::types::rust_type(&t)));
                                }
                                params.push((pname, t));
                            }
                            syn::FnArg::Receiver(_) => return Err("it has a `self` parameter".into()),
                        }
                    }
                    let ret = match &f.sig.output {
                        syn::ReturnType::Default => return Err("it returns nothing".into()),
                        syn::ReturnType::Type(_, ty) => {
                            let (t, is_ref) = convert_type(ty).map_err(|e| format!("return type: {}", e.msg))?;
                            if is_ref || matches!(**ty, syn::Type::Reference(_)) {
                                return Err("it returns a borrow".into());
                            }
                            if !ambient_type_ok(&t) {
                                return Err(format!("it returns `{}`; ambient functions take and return scalars, `bool`, `char`, `Option`s of those and the file's `enum`s/`struct`s", crate::types::rust_type(&t)));
                            }
                            t
                        }
                    };
                    Ok(Ambient { name: name.clone(), params, ret, span, source: source.clone() })
                })();
                match reason {
                    Ok(a) => {
                        t.ambient.insert(name, a);
                    }
                    Err(r) => {
                        t.ambient_errors.insert(name, r);
                    }
                }
            }
            syn::Item::Const(c) => {
                // an array of integer literals is a table: `Spec.lean` defines it once
                if let Some(elems) = table_literal(&c.expr) {
                    // a table is `&[T]` or `[T; N]` of an integer type; any other
                    // array constant is not usable in specifications, as before
                    let ty = match convert_type(&c.ty) {
                        Ok((ty @ RType::Seq(_, SeqKind::Slice | SeqKind::Array(_)), _)) if matches!(&ty, RType::Seq(e, _) if matches!(**e, RType::Int { .. })) => ty,
                        _ => continue,
                    };
                    let value = Expr::new(c.ident.span(), ExprKind::Var(c.ident.to_string()));
                    t.consts.insert(c.ident.to_string(), Const { name: c.ident.to_string(), ty, value, table: Some(elems) });
                    continue;
                }
                // only literal constants (optionally negated) are usable in specifications
                let value = match convert_expr(&c.expr) {
                    Ok(v) if matches!(v.kind, ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_)) || matches!(&v.kind, ExprKind::Neg(x) if matches!(x.kind, ExprKind::Int(_))) => v,
                    _ => continue,
                };
                let (ty, _) = convert_type(&c.ty)?;
                t.consts.insert(c.ident.to_string(), Const { name: c.ident.to_string(), ty, value, table: None });
            }
            _ => {}
        }
    }
    Ok(t)
}
