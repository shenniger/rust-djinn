//! GUIDE.md for the Verus backend: the harness guide handed to the
//! implementing agent.
//!
//! Order: environment, files, verifier, how to read the obligations, how
//! the specification reads in Verus (triggers included), the Verus the
//! implementer will need, timing, the rules for `proofs.rs`, then the
//! per-declaration obligations (compact when the guide would grow past what
//! an agent reads at once), then reporting.

use crate::config::Config;
use djinn_syntax::emit_verus::{self, EmitCx, How, Obligation};
use djinn_syntax::ast::RType;
use djinn_syntax::lower::Lowered;
use djinn_syntax::lower_verus::{exec_type, verus_ident, view_term};
use djinn_syntax::Kind;
use std::collections::HashMap;

/// Above this many bytes, the per-obligation section names the obligations
/// and points at `obligations.rs` instead of printing every statement
/// (roughly 20k tokens).
const COMPACT_ABOVE: usize = 80_000;

pub fn guide(cfg: &Config, lowered: &[Lowered], names: &HashMap<String, String>) -> String {
    let tn = crate::verify::parse_spec(cfg).map(|p| crate::verify_verus::type_names(cfg, &p)).unwrap_or_default();
    let cx = EmitCx { names: &tn, impl_names: names };
    let mut g = String::new();
    let shell: Vec<String> = crate::agent::ALLOWED_TOOLS
        .iter()
        .filter_map(|t| t.strip_prefix("Bash(").map(|x| x.trim_end_matches(')').trim_end_matches('*').trim().to_string()))
        // `lake` is the Lean build tool: allowed, useless here
        .filter(|x| x != "lake")
        .fold(Vec::new(), |mut acc: Vec<String>, x| {
            if !acc.contains(&x) {
                acc.push(x);
            }
            acc
        });
    let shell = shell.join(", ");
    let specmods: Vec<String> = cfg.specs().iter().map(|f| f.module.clone().map(|m| format!("crate::{m}")).unwrap_or_else(|| "crate".into())).collect();
    let specmod = specmods.first().cloned().unwrap_or_else(|| "crate::spec".into());
    let vstd = vstd_source_dir();
    let decl_count = lowered.len();

    g.push_str(&format!(r#"# GUIDE — implementing and proving `{krate}` (Verus backend)

You are the implementer in a Djinn-on-Verus project. The human wrote only a
specification; you write the Rust implementation, with its Verus annotations,
and the Verus proofs; a verifier judges them. The specification is unambiguous
(every `fn` has an unambiguity obligation), so you have no leeway on *what*
the program computes, only on *how* — except where a `fn` marked
`#[weakly_specified]` leaves a choice to you with `any x: T where …;`
(see §3a). Only `PASS` counts; the summary you write at the end is the one
thing a human reads.

Read §0–§7 once, completely, before touching a file; §8 lists the {decl_count}
declarations and their obligations.

## 0. Your environment — facts, so you need not test them

- You are in a **jail**: a working copy of the crate (`{work}/jails/…` of the
  real crate). Everything you need is here; the directories above it are not
  yours. `agent.log` is your own transcript: ignore it.
- `{verus}/` is a complete Verus crate (no Cargo.toml: it is verified with the
  `verus` driver directly). `./verus-check` from this directory runs Verus on
  it as it is — nothing synced, nothing compiled. The `verify` tool is the
  judge: it syncs your files, builds the real crate, audits your files,
  regenerates the trusted files and runs Verus with `--no-cheating`.
- Shell commands are allowed by prefix and denied otherwise (a denied command
  returns a permission error, not output). Allowed prefixes:
  `{shell}`. A compound command (`a && b`, `a | b`) is allowed only if every
  part is allowed.
- What works: heredocs (`python3 - <<'EOF' … EOF`), `python3 -I script.py` on
  a script you wrote with the Write tool, `sed -i`, `grep -n`, redirections
  (`./verus-check > check.out 2>&1`), relative paths inside this directory.
- What is denied every time, so do not try: any path outside this directory
  (absolute or `~`, also for `ls`/`cat`/`grep`), `for`/`while` loops,
  `$?`/`$var`/`$(…)`, a multi-line `python3 -c`, `cd … && … > file`. Keep
  shell lines plain; scratch files go in this directory.
- The Read and Grep tools (not the shell) can read Verus's standard library,
  vstd, at `{vstd}` — `seq.rs`, `seq_lib.rs`, `std_specs/vec.rs`,
  `std_specs/num.rs`, `std_specs/bits.rs`, `arithmetic/power2.rs`, … Read a
  file or Grep a name there when you need a lemma's exact statement; do not
  Glob the whole registry.
- Tools: the MCP server `djinn` has `verify` and `status`; `./verify`,
  `./status`, `./verus-check` and `./bench` are the same from a shell.
- `rustc` pins the signatures: a `pub fn` in `{sol}/` with a different
  signature from the stub fails `cargo build`. (Outside this jail, `cargo
  build` also refuses unverified `fn`s; in the jail that gate is off.)
- The real crate compiles your solution with Verus's ghost code **erased**
  (`vstd` is a dependency; `verus! {{ … }}` erases `requires`, `ensures`,
  `proof {{ }}`, `assert`, `ghost`/`tracked` and `spec`/`proof` functions when
  built by plain `cargo`). Write the solution inside `verus! {{ … }}` and
  start it with `use vstd::prelude::*;`.

## 1. Files

| Path | You | Meaning |
|---|---|---|
| `{specrel}` | read only | the specification: `djinn! {{ … }}` blocks of `fn` / `rel` items, plus the `enum`s, `struct`s and `const`s they mention; the plain Rust beside the blocks is the human's driver (not verified) |
| `{sol}/` | **edit** | one `pub fn` per `fn` of the specification, exact signature of the stub, inside `verus! {{ … }}`; helpers as you like |
| `{proofs_main}` | **edit** | one `proof fn` per proof obligation, named exactly as in `{verus}/src/obligations.rs`, plus any helper lemmas |
| `{helpers}/*.rs` | edit | optional helper modules (`mod helper;` in `proofs.rs` loads `proofs/helper.rs`) |
| `{verus}/src/relations.rs` | read only | the relations `f_pre`, `f_spec` (regenerated): `open spec fn`s over `Seq` and `int` |
| `{verus}/src/obligations.rs` | read only | the pinned obligations: each `proof fn` has the pinned contract and calls yours by name |
| `{verus}/src/<spec module>.rs` | read only | a mirror of each specification module: its types and constants verbatim (a slice table `&[u8]` as the array of its elements), the ambient functions the specification calls (verbatim, with their translation as their contract), and one stub per implemented `fn`, carrying the relation as its contract and calling `crate::solution::f` — `f.impl_correct` |
| `{verus}/src/vocab.rs` | read only | `count`, `sum`, `first`, `last`, `adjacent`, `slice`, `trig`; `bytes` (a string's view); the bit-level definitions (`bit_and`, `count_ones`, `rotate_left`, `wrap_unsigned`, …) and the lemmas relating them to Verus's operators |
| `{verus}/src/lib.rs` | read only | the module tree; `#[path]` to your solution |

Edits to read-only files are discarded by the verifier. The specification
cannot be changed.

## 2. The verifier

Call the `verify` tool (MCP server `djinn`) or run `./verify`. It:

1. syncs `{sol}/` and `{proofs_main}` (and `{helpers}/`) into the real crate;
2. `cargo build` — your function signatures must match the stubs exactly,
   and your code must compile with the ghost code erased;
3. audits your files, on tokens (so a banned word is banned wherever it
   appears, also as a variable or field name): no `unsafe`, `assume`,
   `admit`, `axiom`, `assume_specification`, `assume_termination`; no
   `external`, `external_body`, `external_fn_specification`,
   `external_type_specification`, `external_trait_specification`,
   `external_trait_blanket`, `external_trait_extension`, `external_derive`
   (anything Verus would not verify); no `exec_allows_no_decreases_clause`,
   `trusted`, `accept_recursive_types`, `when_used_as_spec`,
   `inline_air_stmt`; no `macro_rules`, `macro_export`, `cfg`, `cfg_attr`,
   `extern`, `no_mangle`, `link_section`, `export_name`, `link_name`,
   `global_allocator`, `panic_handler`, `no_std`, `no_core`, `feature`,
   `Drop`, `pervasive`, `print_u64`; no `static` items (global state is a
   side effect no relation constrains; the lifetime `'static` is fine); no
   `global size_of`/`layout`/`align_of` directives; none of the macros
   `include!`, `include_str!`, `include_bytes!`, `env!`, `option_env!`,
   `cfg!`, `file!`, `line!`, `column!`, `module_path!`, `concat!`,
   `stringify!`, `compile_error!` (anything that could make the verified code
   differ from the compiled code). So do not name a variable `trusted`,
   `feature`, `external`, `cfg` or `static`: the audit does not parse, it
   matches;
4. regenerates the trusted files and this guide;
5. runs Verus on `{verus}/src/lib.rs` with `--no-cheating`: the WHOLE crate
   must verify with `0 errors`.

It prints `PASS` or `FAIL: <stage>` with the errors (`SPECIFICATION VERIFIED`,
exit 3, when every obligation so far is proved but some `fn` is not
implemented), and refreshes the generated files in this directory.

- `verify` reports obligations as proved only when the whole crate verifies:
  Verus is modular, so a lemma's verdict is only as good as its callees'.
  Until then an obligation whose pinned function has an error is shown as
  an error; the others as unverified.
- The `impl_correct` stubs appear in the mirrored module only once the
  solution has a function of that name (so the `fn`s you have not
  implemented yet do not break the crate). `status` shows the progression.
- The pinned wrappers in `obligations.rs` carry their own resource limit
  (`#[verifier::rlimit(…)]`): a proof that verifies in `proofs.rs` but makes
  the wrapper time out needs its statement proved more directly (a lemma per
  conjunct), not a larger limit in your file.

Order of work:

1. Prove the specification-level obligations first: `unambiguous`, `ens_*`,
   `wf`, and the `exists` of total rels. They need no implementation, and
   if one of them is false the specification is ambiguous or contradictory:
   report that instead of implementing.
2. Implement each `fn` in Rust inside `verus! {{ … }}`, with `requires`/
   `ensures` of your choosing (the stub's contract is what is checked:
   your `ensures` must imply `f_spec(inputs, result)` and your `requires`
   must follow from `f_pre`; note that `f_spec` includes `f_pre`, so
   `ensures f_spec(…)` needs `requires f_pre(…)`), loop `invariant`s and
   `decreases` clauses.
3. `verify`; loop until it prints PASS.

## 3. The obligations

What each kind guarantees (the pinned functions are in `obligations.rs`;
the implementer's copies in `proofs.rs` start with the same contract):

- `f.unambiguous` — `proof fn f_unambiguous(inputs, o1, o2) requires
  f_spec(inputs, o1), f_spec(inputs, o2) ensures o1 == o2`: for fixed
  inputs, any two outputs satisfying the relation are equal. Ambiguity
  inherited from mentioned rels must be resolved here. (Outputs of a user
  type holding a `Vec`/`String`/`HashMap` are compared by contents through
  the generated `djinn_eq_T` in `relations.rs`.)
- Every pinned `proof fn` states its conclusion as `ensures f_X_post(args)`,
  an `open spec fn` in `relations.rs` next to `f_spec` that unfolds to the
  conjuncts listed in §8; your stub says the same, so proving the body of
  `f_X_post` directly (it unfolds automatically) is all there is to do.
- `f.ens_i` — `ensures` clause *i* follows from the relation itself.
- `f.wf` — every partial operation is in its domain and every callee's
  precondition holds, wherever its side matters.
- `f.impl_correct` — the stub `{specmod}::f` (your signature, `requires
  f_pre(views of the inputs)`, `ensures f_spec(views of inputs and outputs)`)
  verifies with your `crate::solution::f` as its body. Verus proves
  termination (every loop and recursion needs `decreases`), absence of
  overflow, out-of-bounds indices and other panics, and the postcondition.
  §8 prints the contract the stub will carry for each `fn` not implemented
  yet; once implemented, read it in the mirrored module.
- `f.exists` — realizability: for every input satisfying the preconditions,
  at least one output satisfies the relation. For a `fn` it follows from
  `impl_correct`; a `total` rel owes it directly.

## 3a. Choices: `#[weakly_specified]` and `any x: T where …;`

A `fn` marked `#[weakly_specified]` leaves something to you. Each
`any x: T where c;` in its body is a value YOU choose, within `c`; a `fn`
that calls a weakly specified one inherits its choices. In `relations.rs`
such a `fn` has two relations:

- `f_body(inputs, choices, outputs)` — the body, with every choice an
  explicit extra argument of type `spec_fn(Inputs…, loop vars…) -> T`: a
  choice is a FUNCTION of the inputs and of the `for` variables around its
  statement (or call site), applied as `w(v, i)` in the relation.
- `f_spec(inputs, outputs) := exists|choices| f_body(inputs, choices, outputs)`
  — what callers and `impl_correct` see.

What this means for you:

- `f.unambiguous` and `f.wf` are stated on `f_body`, quantified over the
  choices: outputs may differ only because a choice differs.
- `f.ens_*` is stated on `f_spec`: an `ensures` must hold for EVERY
  admissible choice. If it does not, the specification is wrong: report it.
- `f.impl_correct` is stated on `f_spec`: you supply the witnesses — the
  choice functions your code realizes — in your `ensures` proof: define
  each as a named `spec fn` in the solution (e.g. `spec fn checked_div_msg(a:
  u32, b: u32) -> Seq<u8>`) and prove `f_body(inputs, |a, b|
  checked_div_msg(a, b), result)`; a human reviews what you chose.

## 4. How the specification reads in Verus

The relations are `open spec fn`s over the mathematical views of the Rust
values: a `&[T]`, `Vec<T>` or `[T; N]` is a `Seq<T>` (the stub passes `v@`),
machine integers are compared through `as int`, `int` is `int`, an
`Option<Vec<u8>>` is an `Option<Seq<u8>>` (the stub passes a `match`), a user
`struct`/`enum` is itself (its sequence fields are read as `s.f@`).

- `for i in lo..hi {{ … }}` is `forall|i: int| lo <= i && i < hi ==> …`;
  `for x in s {{ … }}` is `forall|x: T| s.contains(x) ==> …`; `some x: T {{ … }}`
  is `exists|x: T| …`; `cases {{ a; b; }}` is `a || b`; `c => s` is `c ==> s`;
  `x == if c {{ a }} else {{ b }}` is Verus's `if`.
- `s[i]` is `s[i]` (an `int` index; a `usize` index is `i as int`),
  `s.len()` is `s.len() as int`, `s[a..b]` is `crate::vocab::slice(s, a, b)`
  (`s.subrange(a, b)` when `0 <= a <= b <= s.len()`, clamped otherwise —
  vstd's `subrange` and `s[i]` are specified only in range),
  `x in s` is `s.contains(x)`, `s.iter().filter(|y| y == x).count()` is
  `crate::vocab::count(s, x)` (other predicates: `s.filter(|y| p).len()`),
  `.sum()` is `vocab::sum(s.map_values(|y| y as int))`, `.first()`/`.last()`
  are `vocab::first`/`vocab::last`, `windows(2).all(|w| p)` is
  `forall|a, b| vocab::adjacent(s, a, b) ==> p`.
- A call `g(args) == v` in the specification is `g_spec(args, v)`; a call
  used as a value is lifted to `exists|v_call0| g_spec(args, v_call0) && …`.
  A rel's precondition at a call site is owed in the caller's `wf`.
- Recursive relations (`#[decreases(..)]`) carry `decreases` and are written
  `pre && (pre ==> body)`; a statement before a recursive call appears as
  `A && (A ==> B)` so the termination check sees `A`. Unfold them with
  `reveal_with_fuel(f_spec, 2)` or by asserting the body at the arguments.
- `/` and `%` are Euclidean (`int`); `a << n` is `a * pow(2, n)`, `a >> n`
  is `a / pow(2, n)` (`vstd::arithmetic::power::pow`, which is
  `#[verifier::opaque]`: `reveal(pow)` or the lemmas of
  `vstd::arithmetic::power2`); `&`, `|`, `^` are stated only between machine
  integers of one type.
- Arrays of integer constants (`pub const K: [u8; 19] = […]`) are mirrored
  verbatim; the relation reads `K@`, your code indexes `K[i]`.

**Triggers — read this before your first `forall`.** Every quantifier in
`relations.rs` and `obligations.rs` has an explicit `#![trigger …]`, chosen
by the generator (never `#![auto]`): for each bound variable, the first
application term of the body (`s[i]`, `g_spec(a, v)`, `s.contains(x)`,
`vocab::count(s, x)`) that mentions the variable, lies outside any nested
quantifier, and is not a call of the relation being defined (inside a
recursive `spec fn` Verus encodes the function's own calls with a fuel
argument, so such a trigger could never be matched); a term without
arithmetic is preferred. Where no such term exists — a body of pure
arithmetic, a lifted call that also mentions its own existential, a
recursive relation's self-call — the quantifier is triggered on
`crate::vocab::trig(x)` (always true), which is then also a conjunct of the
body. Read the trigger of each quantifier you use in `relations.rs`; it
decides how to drive it:

- To instantiate a `forall` triggered on `s[i]` at `i0`, mention `s[i0]`
  (`assert(s[i0] == s[i0])` suffices); one triggered on `trig(i)`: write
  `assert(trig(i0));` first (or `assert(p(i0)) by {{ assert(trig(i0)); }}`).
- To prove an `exists` triggered on `trig(w)`, exhibit the witness and
  assert its trigger: `assert(trig(w));` with `w` of exactly the binder's
  type (an `int` witness for an `int` binder), then the `exists`.
- A lifted call `exists|v_call0: T| #![trigger trig(v_call0)] trig(v_call0)
  && (f_spec(.., v_call0) && …)` inside the definition of `f_spec` itself:
  the hypothesis about the inner call is reachable only through the
  `trig(v_call0)` trigger. The pattern that works, in an induction over the
  recursive relation:
  `assert forall|v: T| #![trigger trig(v)] f_spec(args, v) implies P(v) by {{
  ih(args, v); }}` — an `assert forall` whose own trigger is `trig(v)`,
  so that every instance the relation produces is covered by the induction
  hypothesis.
- `reveal_with_fuel(f_spec, 2)` unfolds a recursive relation one level
  (`reveal(f_spec)` for a non-recursive one that Verus has made opaque for
  size); state the unfolded body with `assert(f_spec(args, v) == (…)) by {{
  reveal_with_fuel(f_spec, 2); }}` where the body is long.
- A recursive relation that is a function of its inputs is best handled
  once: define `spec fn f_val(args) -> T` (the value) and `spec fn
  f_dom(args) -> bool` (where it is defined) in `proofs.rs`, prove
  `broadcast proof fn f_spec_is(args, v) ensures #[trigger] f_spec(args, v)
  <==> f_dom(args) && v == f_val(args)` by induction, `broadcast use` it,
  and never unfold `f_spec` again.

## 5. Verus you will need

- Loops: `while c invariant …, decreases …, {{ … }}` (also `for i in 0..n
  invariant … {{ … }}`, which needs no `decreases`). Every loop and every
  recursive `fn` needs `decreases`; `exec_allows_no_decreases_clause` is
  refused. Loop bodies are isolated by default: a fact known before the loop
  (a `requires`, an earlier `assert`) is NOT available inside unless it is in
  the `invariant`; `#[verifier::loop_isolation(false)]` on the function makes
  the function's `requires` and the facts before the loop visible in the
  body.
- Arithmetic is checked: `a + b` on `u32` must be provably in range
  (`requires`, invariants, `assert(… <= u32::MAX)`). Indices need `i < v.len()`.
  In spec code a literal takes the type Verus infers; where it cannot (`1 <<
  n`, a literal alone in `choose`/`assert`), write the suffix: `1int`,
  `0nat`, `1u32`.
- Proofs: `assert(p)`, `assert(p) by {{ … }}`, `assert forall|i: int| … implies
  … by {{ … }}` (the keyword is `implies`, not `==>`), `assert(s1 =~= s2)` for
  sequence equality (extensionality), `reveal(f)`, `reveal_with_fuel(f, n)`,
  `proof {{ … }}` blocks in exec code, `lemma(…)` calls, `choose|x| p(x)`,
  `assert(exists|x| p(x)) by {{ assert(p(w)); }}`.
- `Seq` (vstd): `s.len()`, `s[i]`, `s.subrange(a, b)`, `s.push(x)`,
  `s.update(i, x)`, `s.contains(x)`, `s.filter(p)`, `s.map_values(f)`,
  `s.take(n)`, `s.skip(n)`, `s.add(t)` / `s + t`, `Seq::empty()`, `seq![…]`,
  `Seq::new(n, |i| f(i))` (its `.len()` is `n` only after `assert(Seq::new(n,
  f).len() == n)` or a reveal; the axioms trigger on `Seq::new(n, f)[i]`);
  `v@` for a `Vec`/slice/array; for a `&mut v` parameter `old(v)@` is its
  value on entry and `final(v)@` its value on exit (in `ensures`). Lemmas:
  `broadcast use vstd::seq_lib::group_seq_properties;` (contains, push,
  take/skip, `lemma_seq_subrange_elements`), `s.lemma_filter_len(p)` (a
  method: `filter(p).len() <= len()`), `vstd::seq::lemma_seq_subrange_len`,
  `lemma_seq_subrange_index`, `lemma_seq_subrange_composition` (in
  `vstd::seq`, broadcast by default), `s.lemma_subrange_max(a, b)`. There is
  no `lemma_seq_properties` and no `lemma_seq_subrange_all`.
- `Vec` methods with specs (`std_specs/vec.rs`): `len`, `is_empty`, `push`,
  `pop`, `index`/`v[i]`, `v[i] = x` (`vec_index_mut`), `Vec::new()`,
  `with_capacity`, `clear`, `truncate`, `resize`, `insert`, `remove`,
  `swap_remove`, `append`, `split_off`, `extend_from_slice`, `as_slice`,
  `clone` (with `T: Clone`'s spec); slices (`std_specs/slice.rs`): `&v[a..b]`,
  `len`, `contains`, `first`, `last`, `split_at`, `starts_with`,
  `ends_with`, `reverse`, `copy_from_slice`. No spec: `Vec::swap`, `sort`,
  `iter().map(…)`, `dedup`, `retain`, `drain` — write the loop (`for x in
  v.iter()` is specified, with an invariant on the iterator's position).
- Integers: `as int`, `as nat`, `u32::MAX` in spec; `vstd::arithmetic::power::pow`
  (opaque), `vstd::arithmetic::power2::{{pow2, lemma_pow2, lemma2_to64,
  lemma_pow2_strictly_increases}}`, `vstd::math::{{min, max, abs}}` (spec
  functions on `int`). Specified exec methods (`std_specs/num.rs`):
  `wrapping_add/sub/mul/shl/shr`, `checked_add/sub/mul/div/rem`,
  `saturating_add/sub/mul` (unsigned); (`std_specs/bits.rs`)
  `leading_zeros`, `trailing_zeros`, `leading_ones`, `trailing_ones` on
  `u8`–`u64`, with `broadcast use vstd::std_specs::bits::group_bits_axioms;`
  for their properties. NO spec: `count_ones`, `rotate_left/right`, `abs`,
  `pow`, `rem_euclid`, signed `saturating_*` — implement them with shifts and
  masks (§ Bits).
- `Option`: `a.is_some()`, `a.unwrap()` (spec, `is_some()` recommended),
  `match`; `Result` likewise. User enums: `match` in spec and exec. `==`
  on a user `struct`/`enum` in exec code relates to the specification's
  equality only if the type derives `Structural` (`#[derive(PartialEq, Eq,
  Structural)]`, from `vstd::prelude`); the specification's types either
  have it (the mirror is verbatim) or you compare field by field.
- Spec closures (`spec_fn(A) -> B`): `|a: A| expr`; a witness for
  `exists|w: spec_fn(…)| f_body(…, w, …)` is such a closure.
- Verus has no `print`, no `format!`: a `fn` returns data; the human's
  driver prints it.
- **Strings.** The specification sees a `String`/`&str` as its UTF-8 bytes:
  `crate::vocab::bytes(s@)` (`== vstd::utf8::encode_utf8(s@)`, where `s@` is
  vstd's view, a `Seq<char>`). Specified: `s.as_bytes()` (`b@ ==
  bytes(s@)`), `s.as_bytes().len()` (use this for the byte length: vstd's
  `str::len` spec truncates to `usize`), `String::new`, `push`, `push_str`,
  `as_str`, `clone`, `==`, `"lit".to_string()` (then `broadcast use
  vstd::string::to_string_from_display_ensures_for_str;` gives `res@ ==
  "lit"@`); the bytes of an ASCII literal: `vstd::string::is_ascii_spec_bytes`;
  `vstd::utf8::encode_utf8_concat`, `encode_utf8_push` relate the encoding
  of a concatenation to its parts. A `rel`'s `String` argument is any byte
  sequence; a `fn`'s is some string's bytes (`exists|cs| bytes(cs) == s`,
  in `f_pre`).
- **Maps.** A `HashMap<K, V>` is its vstd view `m@: Map<K, V>`; the
  specification's `m.get(&k)` is `if m@.dom().contains(k) {{ Some(m@[k]) }}
  else {{ None }}`, `m.contains_key(&k)` is `m@.dom().contains(k)`, `m.len()`
  is `m@.dom().len()`. Put `broadcast use vstd::std_specs::hash::group_hash_axioms;`
  inside your `verus! {{ }}`: it supplies `obeys_key_model::<K>()` for integer
  and `bool` keys and the hasher axiom, which the specs of `HashMap::new`,
  `insert`, `get`, `contains_key`, `remove`, `len` need. `m.get(&k)` returns
  `Option<&V>`: `match m.get(&k) {{ Some(v) => Some(*v), None => None }}`.
- **Bits.** `x.count_ones()`, `leading_zeros`, `trailing_zeros`,
  `rotate_left/right`, `wrapping_*` and `&`/`|`/`^` between different types
  are stated with `crate::vocab`'s definitions on natural numbers
  (`count_ones(x, w)`, `rotate_left(x, n, w)`, `wrap_unsigned(x, w)`,
  `twos`/`from_twos` for signed values, `bit_and(a, b)`, …; read them in
  `vocab.rs`). Where vstd has no exec spec (`count_ones`, `rotate_*`),
  implement with shifts and masks, proving against the definitions
  (`count_ones(x, w) == x % 2 + count_ones(x / 2, w - 1)` by unfolding;
  `assert(v & 1 == v % 2) by (bit_vector)`;
  `vstd::arithmetic::power2::{{lemma2_to64, lemma_pow2_unfold, lemma_pow2_pos}}`).
  `vocab::lemma_bit_and_u32(a, b)` (also `_u8`, `_u16`, `_u64`, and
  `bit_or`, `bit_xor`) states `bit_and(a as nat, b as nat) == (a & b) as nat`.
  `x.wrapping_add(y)` is specified by vstd as `vstd::wrapping::u8_specs::
  wrapping_add(x, y)` (one module per width); with `lemma2_to64()` Z3 relates
  it to `wrap_unsigned(x + y, 8)`. `&`, `|`, `^` between two values of one
  machine type are Verus's own operators in the relation (prove with
  `by (bit_vector)`).
- **Ambient functions.** A plain `fn` of the specification file that a
  constraint calls (`r == bump(k)`) appears in the mirrored module with the
  contract `ensures djinn_r == crate::relations::djinn_amb_bump(x)`, where
  `djinn_amb_bump` is its body translated to a `spec fn` in `relations.rs`;
  Verus verifies that contract against the function itself (it is not your
  job; if it fails, the specification file is at fault). Call the function
  from your solution as `{specmod}::bump(k)` and reason with
  `djinn_amb_bump(k)`.
- `#[verifier::rlimit(N)]` on a slow function; `#[verifier::spinoff_prover]`;
  `#[verifier::loop_isolation(false)]`; `assert(…) by (nonlinear_arith)` and
  `by (bit_vector)` for those theories; `#[verifier::opaque]` + `reveal`.

## 6. Time

- `./verus-check` runs Verus on the whole verification crate: seconds on a
  small specification, 1–5 minutes on a large one — and a function that
  fails burns its whole resource limit before it is reported. Run it in the
  background or with a timeout and read the file:
  `timeout 900 ./verus-check > check.out 2>&1`, then `grep -n "^error" check.out`.
- Verus checks the functions of one module one after another and separate
  modules in parallel. A function that fails on its resource limit takes
  20–35 s, so a module full of unfinished proofs is slow: example/vp8's
  `proofs.rs` with 70 unproved stubs took 31 minutes, its other modules
  under 1.5 minutes each. Functions in helper modules (`proofs/…`) are
  checked alongside each other.
- Narrow it while you work on one lemma: `./verus-check --verify-only-module
  proofs` verifies only `proofs.rs` (a helper module is `proofs::huff`);
  `./verus-check --verify-only-module proofs --verify-function 'lemma_*'`
  only the functions matching the pattern (`--verify-function` needs a
  single `--verify-module`/`--verify-only-module`, and `--verify-module`
  cannot be combined with `--verify-function` across modules). Everything
  else is then unverified: the judge is the full run.
- `./verify` does all of §2 and takes as long as Verus plus `cargo build`:
  `timeout 900 ./verify > verify.out 2>&1` and read the file; call it when
  `./verus-check` is clean, not after every edit.
- `./status` also runs Verus on the project as it is (to classify your proof
  functions): it costs a Verus run, not a lookup.

## 7. `proofs.rs`: stubs, refreshes, bans

- `{proofs_main}` was written once by `translate` with one TODO stub per
  obligation (`{todo}`), and is never overwritten. When the specification
  changes, `translate`/`verify` rewrites ONLY the stubs you have not touched
  (still the TODO marker as their whole body) and appends stubs for new
  obligations at the end; a proof you filled in is never updated — after a
  specification change, compare each of your statements with
  `obligations.rs` and bring it up to date yourself (the wrapper fails
  otherwise, naming the function).
- Your `proof fn` must have exactly the pinned name; its `requires` must be
  implied by the pinned ones and its `ensures` must imply the pinned ones
  (copy the statement from `obligations.rs`). An obligation that Verus
  proves with an empty body is fine: delete the TODO line, keep the body `{{}}`.
- The audit (§2.3) matches banned words as identifiers anywhere in your
  files: do not name a variable, field or lemma `trusted`, `feature`,
  `external`, `cfg`, `static`, `global`, `Drop`, `axiom`, `assume`.
- Helper lemmas go in `proofs.rs` or in `{helpers}/<name>.rs` with `mod
  <name>;` in `proofs.rs`; `pub` what the stubs use.

"#,
        krate = cfg.crate_name,
        shell = shell,
        sol = cfg.sol_rel(),
        verus = cfg.proof_root_rel(),
        proofs_main = cfg.proof_main_rel(),
        helpers = cfg.proof_helpers_rel(),
        specrel = cfg.specs_display(),
        work = cfg.rel(&cfg.state_dir()),
        specmod = specmod,
        vstd = vstd,
        todo = emit_verus::TODO,
        decl_count = decl_count,
    ));

    // the per-declaration section, in full, then compacted if too long
    let full = obligations_section(cfg, &cx, lowered, names, false);
    let section = if g.len() + full.len() > COMPACT_ABOVE { obligations_section(cfg, &cx, lowered, names, true) } else { full };
    g.push_str(&section);

    g.push_str(
        r#"## 9. Reporting

When `verify` prints PASS, stop and summarize what you did in a few lines.
If an obligation resists after a serious attempt, stop and say precisely
which obligation, what the remaining goal is, and what you tried. Never
weaken a statement, never add an axiom or an `assume`, never touch the
specification.
"#,
    );
    g
}

/// §8: every declaration with its obligations. In full, each proof
/// obligation's statement one conjunct per line; compact, its name, its
/// `proof fn` and one line on what it says (the statement is in
/// `obligations.rs`).
fn obligations_section(cfg: &Config, cx: &EmitCx, lowered: &[Lowered], names: &HashMap<String, String>, compact: bool) -> String {
    let mut g = String::new();
    g.push_str("## 8. The declarations and their obligations\n\n");
    if compact {
        g.push_str(&format!(
            "The specification is large, so this section names the obligations; every statement is in\n`{}/src/obligations.rs` (search `proof fn <name>(`), and your `{}` starts\nwith the same statements as stubs.\n\n",
            cfg.proof_root_rel(),
            cfg.proof_main_rel()
        ));
    }
    for d in lowered {
        g.push_str(&format!("### `{}` ({}{})\n\n", d.name, d.kind.word(), if d.total { ", total" } else { "" }));
        if d.kind == Kind::Func {
            match names.get(&d.name) {
                Some(stub) => g.push_str(&format!("Implemented in `{sol}/`; the stub `{stub}` carries `impl_correct`.\n\n", sol = cfg.sol_rel())),
                None => {
                    g.push_str(&format!("Implement `pub fn {}` in `{sol}/` (not implemented yet: no stub, no `impl_correct` until then). The stub will state:\n\n", d.name, sol = cfg.sol_rel()));
                    g.push_str(&format!("```rust\n{}```\n\n", stub_contract(cx, d)));
                }
            }
        } else {
            g.push_str("A relation: never implemented.\n\n");
        }
        for o in emit_verus::obligations(cx, d) {
            match o.how {
                How::Derived => g.push_str(&format!("- `{}` — derived from `impl_correct`; nothing to do.\n", o.name)),
                How::Impl => g.push_str(&format!("- `{}` — the stub in the mirrored module (see above).\n", o.name)),
                How::Proof => {
                    if compact {
                        g.push_str(&format!("- `{}` — `proof fn {}`: {}.\n", o.name, o.fn_name, one_line(&o)));
                    } else {
                        let mut sig = format!("pub proof fn {}({})", o.fn_name, o.params);
                        if !o.requires.is_empty() {
                            sig.push_str(&format!("\n  requires\n{}", clauses(&o.requires)));
                        }
                        if !o.ensures.is_empty() {
                            sig.push_str(&format!("\n  ensures\n{}", clauses(&o.ensures)));
                        }
                        g.push_str(&format!("- `{}`\n  ```rust\n  {}\n  ```\n", o.name, sig.replace('\n', "\n  ")));
                    }
                }
            }
        }
        g.push('\n');
    }
    g
}

/// What a proof obligation says, in one line, from its name.
fn one_line(o: &Obligation) -> String {
    let (f, kind) = o.name.rsplit_once('.').unwrap_or((&o.name, ""));
    if kind == "unambiguous" {
        format!("two outputs of `{f}_spec` for the same inputs (and choices) are equal")
    } else if let Some(i) = kind.strip_prefix("ens_") {
        format!("`ensures` clause {i} of `{f}` follows from `{f}_spec`")
    } else if kind == "wf" {
        format!("every partial operation in `{f}`'s body is in its domain and every callee's precondition holds")
    } else if kind == "exists" {
        format!("for every input in `{f}_pre`, some output satisfies `{f}_spec`")
    } else {
        o.doc.lines().next().unwrap_or("").trim_start_matches("/// ").to_string()
    }
}

/// Clauses of a `requires`/`ensures`, one conjunct per line.
fn clauses(cs: &[String]) -> String {
    let mut s = String::new();
    for c in cs {
        let parts = conjuncts(c);
        for (i, p) in parts.iter().enumerate() {
            if i == 0 {
                s.push_str(&format!("    {p}\n"));
            } else {
                s.push_str(&format!("    && {p}\n"));
            }
        }
        if let Some(last) = s.strip_suffix('\n') {
            s = format!("{last},\n");
        }
    }
    s.trim_end_matches('\n').to_string()
}

/// Split on top-level ` && ` (outside parentheses, brackets, braces and
/// string literals), stripping one pair of outer parentheses around the
/// whole statement first.
fn conjuncts(s: &str) -> Vec<String> {
    let s = strip_outer_parens(s.trim());
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut in_str = false;
    let mut parts = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if in_str {
            if c == b'\\' {
                i += 1;
            } else if c == b'"' {
                in_str = false;
            }
        } else {
            match c {
                b'"' => in_str = true,
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth -= 1,
                b' ' if depth == 0 && s[i..].starts_with(" && ") => {
                    parts.push(s[start..i].to_string());
                    i += 4;
                    start = i;
                    continue;
                }
                _ => {}
            }
        }
        i += 1;
    }
    parts.push(s[start..].to_string());
    parts
}

fn strip_outer_parens(s: &str) -> &str {
    if !(s.starts_with('(') && s.ends_with(')')) {
        return s;
    }
    // the first `(` must close at the last `)`
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 && i + 1 != s.len() {
                    return s;
                }
            }
            _ => {}
        }
    }
    &s[1..s.len() - 1]
}

/// The contract the mirrored module's stub will carry for a `fn` once it is
/// implemented, built from the lowered declaration as `emit_verus::impl_stub`
/// builds the stub (which needs the implementation to exist).
fn stub_contract(cx: &EmitCx, d: &Lowered) -> String {
    let is_mut = |n: &str| d.outputs.iter().any(|(o, _)| o == n);
    let ret = d.outputs.iter().find(|(n, _)| !d.impl_params.iter().any(|(p, _)| p == n));
    let params: Vec<String> = d.impl_params.iter().map(|(n, t)| format!("{}: {}{}", verus_ident(n), if is_mut(n) { "&mut " } else { "" }, exec_type(t, cx.names))).collect();
    // as `emit_verus::impl_stub`: a `&mut` of a viewed type is `old(v)@`/`final(v)@`,
    // anything else is dereferenced first
    let mut_term = |f: &str, n: &str, t: &RType| match t {
        RType::Seq(..) | RType::Map(..) => view_term(&format!("{f}({})", verus_ident(n)), t, cx.names),
        _ => view_term(&format!("*{f}({})", verus_ident(n)), t, cx.names),
    };
    let in_views: Vec<String> = d.impl_params.iter().map(|(n, t)| if is_mut(n) { mut_term("old", n, t) } else { view_term(&verus_ident(n), t, cx.names) }).collect();
    let mut all = in_views.clone();
    if let Some((n, t)) = ret {
        all.push(view_term(&verus_ident(n), t, cx.names));
    }
    for (n, t) in &d.impl_params {
        if is_mut(n) {
            all.push(mut_term("final", n, t));
        }
    }
    let ret_s = match ret {
        Some((n, t)) => format!(" -> ({}: {})", verus_ident(n), exec_type(t, cx.names)),
        None => String::new(),
    };
    format!(
        "pub fn {0}({1}){2}\n    requires\n        crate::relations::{0}_pre({3}),\n    ensures\n        crate::relations::{0}_spec({4}),\n",
        d.name,
        params.join(", "),
        ret_s,
        in_views.join(", "),
        all.join(", ")
    )
}

/// Where vstd's sources are, for the Read/Grep tools: the one `vstd-*`
/// directory of the cargo registry, else the pattern to look for.
fn vstd_source_dir() -> String {
    let home = std::env::var("CARGO_HOME").map(std::path::PathBuf::from).or_else(|_| std::env::var("HOME").map(|h| std::path::PathBuf::from(h).join(".cargo")));
    let pattern = "~/.cargo/registry/src/index.crates.io-*/vstd-<version>/".to_string();
    let Ok(home) = home else { return pattern };
    let Ok(idx) = std::fs::read_dir(home.join("registry").join("src")) else { return pattern };
    let mut found: Vec<std::path::PathBuf> = Vec::new();
    for e in idx.flatten() {
        if let Ok(rd) = std::fs::read_dir(e.path()) {
            for v in rd.flatten() {
                if v.file_name().to_string_lossy().starts_with("vstd-") {
                    found.push(v.path());
                }
            }
        }
    }
    found.sort();
    match found.len() {
        0 => pattern,
        1 => format!("{}/", found[0].display()),
        _ => format!("{}/ (the version your Cargo.toml names)", found.last().unwrap().display()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conjuncts_split_at_the_top_level_only() {
        assert_eq!(conjuncts("((a && b) && (forall|i: int| #![trigger s[i]] 0 <= i && i < 3 ==> s[i] > 0) && c)"), vec!["(a && b)", "(forall|i: int| #![trigger s[i]] 0 <= i && i < 3 ==> s[i] > 0)", "c"]);
        assert_eq!(conjuncts("(a) && (b)"), vec!["(a)", "(b)"]);
        assert_eq!(conjuncts("f(x)"), vec!["f(x)"]);
        assert_eq!(clauses(&["a && b".to_string(), "c".to_string()]), "    a\n    && b,\n    c,");
    }
}
