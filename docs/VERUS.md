# The Verus backend

`cargo djinn --backend verus` verifies a Djinn crate with
[Verus](https://github.com/verus-lang/verus) instead of Lean. The
specification language, the `djinn!` macro, the build gate, the smoke-test,
the jail and the agent loop are the same; what changes is how the obligations
are stated and who checks them. This document says what the backend
generates, what makes a `PASS` trustworthy, and what it does not support.

Choosing the backend, in order of precedence: `--backend lean|verus` on the
command line; `DJINN_BACKEND`; `backend = "verus"` in
`[package.metadata.djinn]`; the backend recorded in `djinn/report.toml` by the
last verify; else Lean. The build gate (`cargo build`) always judges by the
report's backend, so a crate verified with Verus compiles against its Verus
report whatever the environment says.

## One crate, two backends

A crate can hold an implementation for each backend. Lean's lives in
`djinn/solution/`, `djinn/proofs/` and `djinn/report.toml`; Verus's in
`djinn/verus/`: `djinn/verus/solution/` (the implementer's Rust),
`djinn/verus/report.toml` and the verification crate `djinn/verus/src/`.
`src/lib.rs` includes the solution with `djinn::solution!();`, which reads
it from the directory of the backend the build is for. That backend is
`DJINN_BACKEND` (`cargo djinn` sets it for everything it runs, so a
`--backend verus` command builds and benches the Verus solution), else the
metadata's `backend`, else the backend whose report exists (Lean's first),
else Lean: a plain `cargo build` of a crate with both compiles the Lean
solution, `DJINN_BACKEND=verus cargo build` the Verus one. The build gate
checks the solution it compiles against that backend's report. The Verus
backend's job records, jails and logs are in `.djinnscratch/verus/`.

## What the crate needs

```toml
[dependencies]
djinn = { path = "/path/to/rust-djinn/rust-djinn" }
vstd = "=0.0.0-2026-10-25-0158"          # the version of the installed Verus

[package.metadata.djinn]
backend = "verus"
verus = "../../tools/verus/verus"        # or DJINN_VERUS, or `verus` on PATH
# verus_dir = "djinn/verus"              # where the verification crate is generated (default)
```

The crate's `package.edition` is passed to Verus as `--edition`, so the
solution is parsed as the real crate parses it.

`vstd` is Verus's standard library. The solution is written inside
`verus! { … }` (the macro comes with `vstd::prelude`), so the real crate must
depend on it: built by plain `cargo`, the macro erases the ghost code —
`requires`, `ensures`, `proof { }`, `assert`, `spec`/`proof` functions,
`ghost`/`tracked` values — and what remains is ordinary Rust. The build gate
and the drivers are untouched; `cargo build` compiles the crate exactly as
with the Lean backend. Installing Verus: [INSTALL.md](INSTALL.md).

## What is generated

Everything lives in `djinn/verus/`, a Verus crate verified with the `verus`
driver directly (no Cargo.toml):

```
djinn/verus/src/lib.rs          trusted: the module tree; `#[path]` to the solution
djinn/verus/src/vocab.rs        trusted: count, sum, first, last, adjacent, trig
djinn/verus/src/relations.rs    trusted: f_pre, f_spec — the specification, lowered
djinn/verus/src/obligations.rs  trusted: the proof obligations, pinned
djinn/verus/src/<module>.rs     trusted: a mirror of each specification module
djinn/verus/src/proofs.rs       the implementer's: one `proof fn` per obligation
djinn/verus/src/proofs/         the implementer's helper modules
djinn/verus/solution/           the implementer's Rust (Lean's is djinn/solution/)
djinn/verus/report.toml         the verifier's report
```

**Relations.** Every `fn` and `rel` becomes two `open spec fn`s over the
mathematical views of its Rust values: `f_pre(inputs)` and `f_spec(inputs,
outputs)`. A `&[T]`, `Vec<T>` or `[T; N]` is a `Seq<T>`, machine integers are
compared through `as int`, `int` is `int`, an `Option<Vec<u8>>` is an
`Option<Seq<u8>>`, a user `struct`/`enum` is itself. `for` is `forall`, `some`
is `exists`, `cases` is `||`, calls are `g_spec(args, v)` (lifted to an
existential when used as values), recursive relations carry `decreases` and
are written `pre && (pre ==> body)` as in the Lean backend. A weakly specified
`fn` has `f_body(inputs, choices, outputs)` with each choice a
`spec_fn(Inputs…, loop vars…) -> T`, and `f_spec` closing the choices
existentially. Each proof obligation's conclusion is also a definition,
`f_wf_post(params)` (`f_unambiguous_post`, `f_ens_0_post`, …), next to the
relation it belongs to: the pinned wrapper and the implementer's stub both
say `ensures f_wf_post(…)`, so the transfer from the implementer's lemma to
the pinned one is syntactic however large the statement (an `open spec fn`
unfolds, so a proof may still establish the body directly).

**Equality by contents.** A user `struct`/`enum` whose fields (transitively)
hold a sequence, a string or a map has a generated `djinn_eq_T(a, b)` in
`relations.rs` comparing the fields through their views (variants pairwise,
`_ => false`); `==`, `!=`, `in`/`contains`, `count` on such values, and the
`unambiguous` obligation's `o1 == o2`, go through it (and through
`vocab::opt_eq`, `res_eq`, `seq_eq`, `map_eq` for `Option`/`Result`/sequences/
maps of such types). Verus's own `==` on an exec `Vec` is identity of the
value, which no relation over views can establish; the Lean backend compares
contents, and so does this. A type recursive through such a field is refused.

**Triggers.** Verus refuses a quantifier it cannot infer a trigger for, and a
trusted file that does not elaborate would block the implementer. So every
quantifier gets an explicit `#![trigger …]` from the generator (never
`#![auto]`): for each bound variable, the first application term of the body
(`s[i]`, `g_spec(a, v)`, `s.contains(x)`, `vocab::count(s, x)`) that mentions
the variable, lies outside any nested quantifier, and is not a call of the
relation being defined — inside a recursive `spec fn` Verus encodes the
function's own calls with a fuel argument, so a trigger on such a call could
never be matched by a term a proof writes, and an existential triggered on it
could never be witnessed; a term without arithmetic is preferred. Where no
such term exists — a body of pure arithmetic, a lifted call that also mentions
its own existential, a recursive relation's self-call — the quantifier is
triggered on `crate::vocab::trig(x)` (always true), which is also a conjunct
of the body, so that the pinned wrapper below can instantiate the
implementer's identical statement. Proofs instantiate such a quantifier at
`i0` with `assert(trig(i0))`, witness such an `exists` with `assert(trig(w))`
on a `w` of the binder's type, and reach the hypothesis of a recursive
relation's inner call through an `assert forall|v| #![trigger trig(v)] …
implies … by { … }`; the guide (`cargo djinn guide --backend verus`) spells
these patterns out.

**Obligations.** The same kinds as with Lean. How each is pinned without a
kernel:

| Obligation | Trusted form |
|---|---|
| `f.unambiguous`, `f.ens_i`, `f.wf`, `f.exists` (total rel) | `proof fn f_unambiguous(…) requires … ensures f_unambiguous_post(…)` in `obligations.rs` (the conclusion is the `open spec fn` of that name in `relations.rs`), whose body is the single call `crate::proofs::f_unambiguous(…)`. Verus checks the call: the implementer's `requires` must follow from the pinned ones, the pinned `ensures` from the implementer's. The implementer's function may state anything; what is proved is what the trusted file says. |
| `f.impl_correct` | the stub `pub fn f(params) requires f_pre(views) ensures f_spec(views) { crate::solution::f(args) }` in the mirrored specification module (a `&mut v` parameter is the input `old(v)@` and the output `final(v)@`; for a `&mut` of a type without a view, `*old(c)` and `*final(c)`). Verus verifies the stub against the solution's contract, and the solution against its own; termination (`decreases` on every loop and recursion), absence of overflow, out-of-bounds indices and other panics are part of verifying any Verus function. The stub exists once the solution has a function of that name (so unimplemented `fn`s do not break the crate). |
| `f.exists` (fn) | derived: a verified Verus function terminates and returns an output in the relation for every input admitted by the precondition. |

**Mirrored modules.** The solution is one file in two crates: the real crate
compiles it, the verification crate verifies it. Both must resolve its names
the same way, so the verification crate mirrors each specification module
(`src/spec.rs` → `djinn/verus/src/spec.rs`): the `struct`s, `enum`s and
usable `const`s verbatim (inside `verus! { }`), the ambient functions the
constraints call (below), one contract-carrying stub per implemented `fn`
(so `crate::spec::other_fn(…)` works from the solution, with its
specification as its contract, exactly as in the real crate), and the root's
`pub use` re-exports of those names. Drivers and other modules are not
mirrored: a solution that reaches for them fails to compile in the
verification crate.

**Tables.** An array constant `pub const K: [u8; 19] = […]` is mirrored
verbatim; a slice constant (`&[u8] = &[…]`, `b"…"`) is mirrored as the array
of its elements, `pub const K: [u8; N] = […]`, because Verus has no slice
constants. The relations read it as `crate::spec::K@` either way. A solution
uses it as `K[i]`, `K.len()`, `&K[..]` (the same in both crates); anything
that tells an array from a slice fails to compile in one of the two crates,
which is safe.

**Strings.** vstd views a `String` or `&str` as its characters (`s@:
Seq<char>`); the specification, as with Lean, as its UTF-8 bytes. The view
is `crate::vocab::bytes(s@) == vstd::utf8::encode_utf8(s@)`, vstd's own
encoding — the one its specification of `str::as_bytes` uses, so
`s.as_bytes()@ == bytes(s@)` for the implementer. A `fn`'s `String` input
carries the implicit precondition that it is some string's bytes
(`exists|cs: Seq<char>| bytes(cs) == s`) and at most `usize::MAX` long, for
`fn`s and `rel`s alike (both backends add these facts to every declaration's
`String` inputs); a `&str` input carries no implicit fact, as in the Lean
backend. Strings as outputs and in `Result`s and choices (`any msg: String`)
are viewed the same way.

**Maps.** A `HashMap<K, V>` is its vstd view `m@: Map<K, V>` (values in
their views): `m.get(&k)` is `if m.dom().contains(k) { Some(m[k]) } else {
None }`, `m.contains_key(&k)` is `m.dom().contains(k)`, `m.len()` is
`m.dom().len()`; a `fn`'s map input has at most `usize::MAX` entries. Keys
must be integers or `bool`: vstd states `HashMap::get`, `insert`, … only for
keys that satisfy its `obeys_key_model`, which it asserts for those types;
the implementer brings the axioms in with `broadcast use
vstd::std_specs::hash::group_hash_axioms;`. Where the Lean backend views a
map as a list of entries (a `rel` over a map ranges over such lists), this
backend's `rel`s range over finite maps; the operations the specification
language offers cannot tell the two apart.

**Bits.** `&`, `|`, `^` between two *unsigned* values of one machine type are
Verus's own operators. Everything else is defined in `vocab.rs` on the
natural numbers, as the Lean backend defines it on `BitVec`s: `bit_and`,
`bit_or`, `bit_xor` (for signed operands, operands of different types or
mathematical integers, with their non-negativity as a well-formedness guard,
as in Lean),
`count_ones(x, w)`, `count_zeros`, `leading_zeros`, `trailing_zeros`,
`leading_ones`, `trailing_ones`, `rotate_left(x, n, w)`, `rotate_right`,
`wrap_unsigned(x, w)` and `wrap_signed` (for `wrapping_add` and kin), on the
two's complement bits `twos(x, w)` of a signed receiver and back through
`from_twos`. A cast receiver (`(e as u8).leading_zeros()`) is first reduced
to the target's width (`wrap_unsigned`/`wrap_signed`), as Rust's `as` and
Lean's `BitVec.ofInt` do. `vocab.rs` also proves, in Verus, that `bit_and`/`bit_or`/
`bit_xor` agree with `&`/`|`/`^` on `u8`…`u64` (`lemma_bit_and_u32`, …), for
the implementer's use. Shifts are `a * pow(2, n)` and `a / pow(2, n)`, as
with Lean.

**Ambient functions.** An ordinary Rust function of the specification file
that a constraint calls (`r == bump(k)`) has, in the Lean backend, its Aeneas
model as its meaning. Verus has no denotation of exec code in spec code, so
the generator *translates* the function's body into a `spec fn`
`djinn_amb_bump` in `relations.rs`, and the mirrored module carries the
function verbatim with the contract `ensures djinn_r ==
crate::relations::djinn_amb_bump(x)`, which Verus verifies like any
function: the body must terminate, never panic (overflow, division by zero,
`unwrap` of `None`) and return exactly what the translation says, for every
input. The translation is therefore not trusted: a mistake in it, or a
function Verus cannot verify, is an error in a generated file and fails the
run (with a message naming the function); it can never make a wrong relation
pass. Translated: pure, loop-free, non-recursive bodies over the ambient
types — literals, parameters, `let`, `if`/`else`, `if let`, `match` (with
literal, constant, `..` and range patterns), arithmetic, comparisons,
`&&`/`||`, bit operations (on `bool` operands `&`, `|`, `^` become `&&`,
`||`, `!=`), `as` and `T::from`/`.into()` between integer types,
`Some`/`None`/`Ok`/`Err`, struct literals and fields, enum variants, calls
of other ambient functions, `std::cmp::min`/`max`, `min`, `max`, `is_some`,
`is_none`, `unwrap`, `unwrap_or`, `wrapping_*`, and — on unsigned integers,
where vstd specifies them — `saturating_add/sub/mul` and
`checked_add/sub/mul/div/rem`. Machine arithmetic is translated as `(a + b)
as T`, exact in the specification and the identity wherever the function
does not overflow, which Verus proves of the function. Anything else (a
method vstd does not specify, such as `rem_euclid`, `pow`, `abs`, signed
`saturating_*`, or `leading_zeros`, which the specification language states
through `vocab.rs`) is refused with a message at the construct, never
guessed; an untyped literal whose width the translation cannot know (`1 <<
n`, `!1`) is refused with the suffix to write. Two differences from the Lean
backend: an ambient function must be total (Lean lets a panicking call make
the constraint false), and `/`, `%` on signed integers are refused (Rust
truncates toward zero, a specification rounds down). `==`/`!=` on a user
`struct` or `enum` (also inside an `Option`) requires `#[derive(…,
Structural)]` on the type (the marker from `vstd::prelude`, beside
`PartialEq`), without which Verus cannot relate the exec comparison to the
specification's equality: the translation refuses the comparison otherwise.
A parameter or variable of an ambient function may not be a Verus keyword
(`int`, `nat`, `spec`, …) or begin with `djinn`: the function is mirrored
verbatim into a Verus crate.

## What makes a PASS trustworthy

The specification and the generator are trusted, as with Lean; Verus and its
Z3 replace Lean's kernel and the Aeneas model. Beyond that:

- **The trusted files are regenerated on every verify** from the real crate's
  specification, in the real crate; a jail's copies are overwritten.
- **Pinning by call.** The implementer never states an obligation; the
  trusted wrapper does, and Verus checks the implementer's function against
  it. A weaker lemma, a shadowed relation, a renamed function: the wrapper
  fails. (This is also why the whole crate must verify: Verus is modular, and
  a wrapper's verdict rests on its callee's.) The wrappers and the
  `impl_correct` stubs carry `#[verifier::rlimit(200)]`, a resource limit for
  the one call they make; the implementer's functions choose their own.
- **`--no-cheating`.** Verus refuses `assume`, `admit`,
  `#[verifier::external_body]` and `assume_specification` anywhere in the
  crate.
- **The audit of the implementer's files** (every regular file under the
  solution directory, `proofs.rs` and every file under `proofs/`, whatever
  its name: rustc compiles a `#[path = "impl.txt"]` module too, so a file
  that does not read as Rust tokens fails the audit — keep notes and data
  elsewhere), on tokens, fail-closed: no `unsafe`, `assume`,
  `admit`, `axiom`; no `#[verifier::external*]` (an item Verus would ignore),
  `assume_specification`, `exec_allows_no_decreases_clause`, `trusted`,
  `accept_recursive_types`, `when_used_as_spec`, `inline_air_stmt`; no
  `global` layout directive; no `#[cfg]`/`cfg_attr`, `include!`,
  `include_str!`, `include_bytes!`, `env!`, `option_env!`, `cfg!`, `file!`,
  `line!`, `column!`, `module_path!`, `concat!`, `stringify!`,
  `compile_error!` (anything whose meaning depends on where the file is
  compiled: the verified code must be the compiled code); no `macro_rules!`,
  `macro_export`, `extern`, `no_mangle`, `link_section`, `export_name`,
  `link_name`, `global_allocator`, `panic_handler`, `feature`, `no_std`,
  `no_core`, `assume_termination`, and every `external_*` token (`external`,
  `external_body`, `external_fn_specification`,
  `external_type_specification`, `external_trait_specification`,
  `external_trait_blanket`, `external_trait_extension`, `external_derive`);
  no `static` items (Verus accepts `exec static X:
  AtomicU32 …` with vstd's atomic specifications, global state that no
  relation constrains; the lifetime `'static` is a different token and
  allowed); no `Drop` (a destructor runs at a point no relation constrains,
  and an `impl Drop` written outside `verus! { }` for a type declared inside
  it is code Verus never sees); no `pervasive`/`print_u64`
  (`vstd::pervasive::print_u64` is an `external_body` function that prints
  from verified code). The audit matches tokens, not syntax: a variable
  named `trusted` or `feature` fails it too. `#[path]` targets must be `.rs`
  files inside the implementer's directories (the same reach check as for
  Lean; a `.txt` module or an absolute path is refused); `include!` is
  banned outright, so it gets no reach check.
- **Side effects.** Verus refuses a call to any function without a
  specification, and vstd specifies none with an effect outside the process:
  `println!`, `std::fs`, `std::env`, `std::io`, `std::process`,
  `std::thread`, `Mutex` are all rejected, as is a printing `Drop`. What a
  verified function can still do is consume time and memory (a long loop
  with a `decreases`, a large `Vec`), and spawn a thread through
  `vstd::thread::spawn`, which may run verified code after the call returns
  — the same class of effect, since that code can neither perform I/O nor
  (with `static` banned) reach any state the caller sees. Threads are
  allowed because a parallel implementation is a legitimate way to meet a
  performance target (`cargo djinn optimize`).
- **Items outside `verus! { }`** are ignored by Verus; a verified function
  cannot call them, so a solution written outside the macro fails.
- **Verus's result is read strictly:** the `verification results:: N
  verified, 0 errors` line, exit status 0, no error block, and `N` at least
  the number of obligations; anything else fails. The real crate must also
  `cargo build` (the signatures match the stubs; the ghost code erases).
- **The evidence fingerprint** covers the solution directory, `proofs.rs`
  and `proofs/`: the files Verus read. The build gate refuses the crate when
  they change; `verify` fails if they change while it runs.
- **`#[forbid(unsafe_code)]`** on the solution module in both crates.

What the backend assumes beyond Verus's soundness: that the erased build of
`verus! { }` code has the semantics Verus verified (Verus's erasure
guarantee), and that `vstd`'s specifications of the standard library are
right. Verus does not rule out aborts on allocation failure or `Vec` capacity
overflow (its unwind model); the Lean backend's Aeneas model proves
`push` never exceeds `usize::MAX` elements. A verified function never returns
a wrong answer; it may abort when memory runs out.

## How a run looks

```
$ cargo djinn verify --backend verus
== cargo build
== verus (djinn/verus src/lib.rs)
verus: 18 verified, 0 errors
PASS
```

`verify` reports every obligation as proved only when the whole crate
verifies. Before that, an obligation whose pinned wrapper, stub or own
`proof fn` in `proofs.rs` has an error is shown as `error`, the others as
`unverified`. `status` shows the report's states; `status --local` also runs
Verus on the project as it is and classifies the implementer's proof
functions: still the skeleton's TODO, an error, or passing locally (Verus on
a large crate takes minutes, so neither `status` nor the `implement`
monitor does this unasked; the monitor reports each verify instead). When
the specification changes, `translate` (and every `verify`) replaces a stub
whose whole body is still the TODO marker by the current one and appends
stubs for obligations that did not exist before; a function with any proof
in it is never touched, so the implementer compares it with
`obligations.rs` after a specification change (the wrapper fails until it
is brought up to date).

The agent gets a Verus guide (`cargo djinn guide --backend verus`,
`GUIDE.md` in the jail), a `./verus-check` script that runs Verus on its copy
without syncing, and the usual `verify`/`status`/`bench`.

## Not supported by this backend

The lowering refuses these with a message pointing at the construct; the Lean
backend handles them.

- `HashMap` keys other than integers and `bool` (vstd specifies the map
  operations for no other key types).
- Ambient functions with loops, recursion, mutation, `/` or `%` on signed
  integers, methods beyond those listed above, `==` on a type without
  `Structural`, or Verus keywords as variable names; ambient functions that
  may panic (Verus must prove them total).
- Names containing `djinn` are reserved for generated identifiers; a
  specification module may not be named `vocab`, `relations`, `obligations`,
  `proofs`, `solution` or `lib`.
- A user type recursive through a field that holds a sequence (its equality
  by contents would need a termination measure).

A constructor or struct literal whose integer field is computed (`K::V(x +
1)`) gets the well-formedness obligation that the value fits the field's
type (the Lean backend refuses the form outright). The mirrored modules copy
the specification file's `use` items except `use djinn::…` (the macro crate
is not part of the verification crate).

What differs from the Lean backend without being refused: a `rel` over a
`HashMap` ranges over finite maps, not lists of entries; an ambient function
must be total. Verus does not rule out aborts on allocation failure.

Every example in `example/` lowers and type-checks in Verus (the recursive
relations' termination included); `example/strmap` (strings, a map, an
ambient function) verifies end to end with a Verus solution;
`example/clamp-verus` is `example/clamp` verified with this backend, and a
`cargo djinn implement --agent claude` run on a copy of it produced a passing
solution and proofs in under two minutes.
