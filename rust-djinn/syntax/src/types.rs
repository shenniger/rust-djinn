//! Rust types → Aeneas types and their mathematical views (DESIGN.md §4).

use crate::ast::*;
use std::collections::HashMap;

/// Rust name of a user type → its fully qualified Lean name (from Aeneas's
/// `translation.json`, or predicted from the namespace and module).
pub type TypeNames = HashMap<String, String>;

fn paren(s: String) -> String {
    if s.contains(' ') {
        format!("({s})")
    } else {
        s
    }
}

/// Words Lean reserves (with Aeneas loaded): Aeneas's own list
/// (`src/extract/LeanKeywords.ml`, generated from Lean's token table by
/// `backends/lean/ExtractLeanKeywords.lean`), plus a few Djinn found itself.
/// A Rust name that is one is written `«name»`.
const LEAN_KEYWORDS: &[&str] = &[
    "PiType", "Prop", "Sort", "StateRefT", "Type", "_", "abbrev", "add_aesop_rules", "add_decl_doc", "alias", "as", "assert!",
    "assert_not_exists", "assert_not_imported", "assumeInstancesCommuteDummy", "at", "attribute", "axiom", "bif", "binder_predicate", "break", "builtin_cbv_simproc", "builtin_cbv_simproc_decl", "builtin_dsimproc",
    "builtin_dsimproc_decl", "builtin_grind_propagator", "builtin_initialize", "builtin_simproc", "builtin_simproc_decl", "by", "by?", "by_elab", "calc", "catch", "cbv_eval", "cbv_simproc",
    "cbv_simproc_decl", "class", "coinductive", "coinductive_fixpoint", "continue", "dbg_trace", "debug_assert!", "declare_aesop_rule_sets", "declare_bitwise_int_theorems", "declare_bitwise_uint_theorems", "declare_command_config_elab", "declare_command_config_elab_legacy",
    "declare_config_elab", "declare_config_elab_legacy", "declare_core_config_elab", "declare_eval_bin", "declare_eval_bin_bitwise", "declare_eval_bin_bool_pred", "declare_int_theorems", "declare_option_config_elab", "declare_simp_like_tactic", "declare_sint_simprocs", "declare_syntax_cat", "declare_term_config_elab",
    "declare_uint_simprocs", "declare_uint_theorems", "decreasing_by", "def", "def_eval_config_item", "def_wanted", "deprecate", "deprecated_module", "deprecated_syntax", "deriving", "do", "docs_to_verso",
    "dsimproc", "dsimproc_decl", "elab", "elab_rules", "elab_stx_quot", "else", "end", "erase_aesop_rules", "eval_prec", "eval_prio", "example", "exists",
    "export", "extend_docs", "extends", "f!", "finally", "for", "forall", "from", "fun", "generalizing", "grind_annotated", "grind_pattern",
    "grind_propagator", "guard_min_heartbeats", "have", "haveI", "hiding", "idbg", "if", "impl_def", "import", "in", "include", "include_str",
    "inductive", "inductive_fixpoint", "inferInstanceAs", "infix", "infixl", "infixr", "init_grind_norm", "init_quot", "initialize", "initialize_simps_projections", "initialize_simps_projections?", "insert_to_additive_translation",
    "instance", "instance_wanted", "irreducible_def", "kerodon", "leading_parser", "lemma", "let", "letI", "let_delayed", "let_expr", "let_fun", "let_impl_detail",
    "let_tmp", "library_note", "library_note2", "local", "logNamedError", "logNamedErrorAt", "logNamedWarning", "logNamedWarningAt", "m!", "macro", "macro_rules", "match",
    "match_expr", "matches", "max_prec", "meta", "mk_iff_of_inductive_prop", "mod_cast", "mut", "mutual", "name", "namespace", "nat_lit", "no_index",
    "nofun", "nomatch", "noncomputable", "nonrec", "norm_cast_add_elim", "notation", "notation3", "omit", "only", "opaque", "open", "panic!",
    "partial", "partial_fixpoint", "postfix", "prefix", "print_decl", "println!", "private", "progress_array_spec", "proof_wanted", "protected", "public", "recommended_spelling",
    "register_builtin_option", "register_error_explanation", "register_grind_attr", "register_hint", "register_label_attr", "register_linter_set", "register_option", "register_parser_alias", "register_simp_attr", "register_sym_dsimp", "register_sym_simp", "register_sym_simp_attr",
    "register_tactic_tag", "register_try?_tactic", "renaming", "repeat", "reportDbgIssue!", "reportEMatchIssue!", "reportIssue!", "reprove", "return", "run_cmd", "run_elab", "run_meta",
    "s!", "says", "scoped", "seal", "section", "set_library_suggestions", "set_option", "show", "show_panel_widgets", "show_term", "show_term_elab", "simproc",
    "simproc_decl", "sorry", "stacks", "step_array_spec", "structure", "sudo", "suffices", "syntax", "tactic_alt", "tactic_extension", "tactic_name", "tactic_tag",
    "termination_by", "termination_by?", "test_extern", "then", "theorem", "theorem_wanted", "throwError", "throwErrorAt", "throwNamedError", "throwNamedErrorAt", "to", "to_additive_name_hint",
    "to_dual_insert_cast", "to_dual_insert_cast_fun", "to_dual_name_hint", "trailing_parser", "try", "unif_hint", "universe", "unless", "unlock_limits", "unreachable!", "unsafe", "unseal",
    "unset_option", "until", "using", "using!", "variable", "variable?", "variables", "whatsnew", "where", "while", "with", "with_weak_namespace",
    "without_expected_type",
    // found by Djinn (identifiers Lean rejects with Aeneas and Mathlib loaded)
    "name", "sorry", "only", "says", "generalizing", "lemma", "this", "public", "meta", "omit", "include",
];

/// A Rust identifier as a Lean identifier: Lean's keywords escaped.
pub fn lean_ident(n: &str) -> String {
    // a non-ASCII name (Rust allows `λ`, `π`, …) may be a Lean token: escaped too
    if LEAN_KEYWORDS.contains(&n) || !n.is_ascii() {
        format!("«{n}»")
    } else {
        n.to_string()
    }
}

/// Field names a Lean structure cannot have: Lean defines these itself for
/// every structure (the recursor and its kin), so Aeneas's translation of a
/// struct with such a field does not compile.
pub const RESERVED_FIELDS: &[&str] = &["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "mk", "below", "brecOn", "binductionOn", "ibelow", "ctorIdx", "toCtorIdx"];

fn named(n: &str, names: &TypeNames) -> String {
    names.get(n).cloned().unwrap_or_else(|| n.to_string())
}

/// The Lean type Aeneas gives a Rust value of this type.
pub fn aeneas_type(t: &RType, names: &TypeNames) -> String {
    match t {
        RType::Int { signed, bits } => {
            let base = if *signed { "I" } else { "U" };
            if *bits == 0 {
                format!("{}size", base)
            } else {
                format!("{base}{bits}")
            }
        }
        RType::Bool => "Bool".into(),
        RType::Char => "Char".into(),
        RType::MathInt => "ℤ".into(),
        RType::Seq(e, k) => match k {
            SeqKind::Slice => format!("Aeneas.Std.Slice {}", paren(aeneas_type(e, names))),
            SeqKind::Str => "Aeneas.Std.Str".into(),
            SeqKind::String => "String".into(),
            SeqKind::Vec => format!("alloc.vec.Vec {}", paren(aeneas_type(e, names))),
            SeqKind::Array(n) => format!("Aeneas.Std.Array {} {}#usize", paren(aeneas_type(e, names)), n),
        },
        RType::Map(k, v) => format!("std.collections.hash.map.HashMap {} {} std.hash.random.RandomState Global", paren(aeneas_type(k, names)), paren(aeneas_type(v, names))),
        RType::Option(e) => format!("Option {}", paren(aeneas_type(e, names))),
        RType::Result(a, b) => format!("core.result.Result {} {}", paren(aeneas_type(a, names)), paren(aeneas_type(b, names))),
        RType::Unit => "Unit".into(),
        RType::Named(n) => named(n, names),
    }
}

/// The type used in specification predicates: sequences become lists.
pub fn view_type(t: &RType, names: &TypeNames) -> String {
    match t {
        RType::Seq(e, _) => format!("List {}", paren(view_type(e, names))),
        RType::Map(k, v) => format!("List ({} × {})", view_type(k, names), view_type(v, names)),
        RType::Option(e) => format!("Option {}", paren(view_type(e, names))),
        RType::Result(a, b) => format!("core.result.Result {} {}", paren(view_type(a, names)), paren(view_type(b, names))),
        _ => aeneas_type(t, names),
    }
}

/// The view of a variable of Aeneas type `t`, as the `impl_correct`
/// statements have always written it: `.val` on sequences, identity
/// elsewhere (Aeneas's coercions bridge `Option (Vec α)` to `Option (List α)`).
pub fn view_of(var: &str, t: &RType) -> String {
    match t {
        RType::Seq(_, SeqKind::String) => format!("(Djinn.Vocab.bytes {var})"),
        RType::Seq(e, _) if needs_view(e) => format!("({var}.val.map (fun y => {}))", view_term("y", e)),
        RType::Seq(..) => format!("{var}.val"),
        RType::Map(..) => view_term(var, t),
        RType::Result(..) if needs_view(t) => view_term(var, t),
        _ => var.to_string(),
    }
}

/// The view of an Aeneas-typed term, written out in full (no coercions):
/// used for pattern-bound fields.
pub fn view_term(term: &str, t: &RType) -> String {
    match t {
        RType::Seq(_, SeqKind::String) => format!("(Djinn.Vocab.bytes {term})"),
        RType::Seq(e, _) if needs_view(e) => format!("({term}.val.map (fun y => {}))", view_term("y", e)),
        RType::Seq(..) => format!("{term}.val"),
        // the entries in their views (a `String` key is its bytes), as `view_type` says
        RType::Map(k, v) if needs_view(k) || needs_view(v) => format!("({term}.entries.map (fun y => ({}, {})))", view_term("y.1", k), view_term("y.2", v)),
        RType::Map(..) => format!("{term}.entries"),
        RType::Option(e) if needs_view(e) => format!("({term}.map (fun y => {}))", view_term("y", e)),
        RType::Result(a, b) if needs_view(a) || needs_view(b) => format!(
            "(match {term} with | .Ok y => .Ok {} | .Err y => .Err {})",
            paren(view_term("y", a)),
            paren(view_term("y", b))
        ),
        _ => term.to_string(),
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

/// A Rust type's tokens, for messages.
pub fn rust_type(t: &RType) -> String {
    match t {
        RType::Int { signed, bits } => format!("{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() }),
        RType::Bool => "bool".into(),
        RType::Char => "char".into(),
        RType::MathInt => "int".into(),
        RType::Seq(e, SeqKind::Vec) => format!("Vec<{}>", rust_type(e)),
        RType::Seq(e, SeqKind::Slice) => format!("&[{}]", rust_type(e)),
        RType::Seq(e, SeqKind::Array(n)) => format!("[{}; {n}]", rust_type(e)),
        RType::Seq(_, SeqKind::Str) => "&str".into(),
        RType::Seq(_, SeqKind::String) => "String".into(),
        RType::Map(k, v) => format!("HashMap<{}, {}>", rust_type(k), rust_type(v)),
        RType::Option(e) => format!("Option<{}>", rust_type(e)),
        RType::Result(a, b) => format!("Result<{}, {}>", rust_type(a), rust_type(b)),
        RType::Unit => "()".into(),
        RType::Named(n) => n.clone(),
    }
}
