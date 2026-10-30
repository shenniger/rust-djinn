# example/clamp-verus — `example/clamp`, verified with Verus

The same specification as [`../clamp`](../clamp) (`src/spec.rs` is identical),
verified with `cargo djinn --backend verus` instead of Lean. What differs:

| | `clamp` (Lean) | `clamp-verus` |
|---|---|---|
| `Cargo.toml` | Charon/Aeneas paths | `backend = "verus"`, `verus = …`, a `vstd` dependency |
| `djinn/solution/mod.rs` | plain Rust | the same functions inside `verus! { … }`, with `requires`/`ensures`, loop invariants and `decreases` |
| `djinn/proofs/` (Lean project) | `Spec.lean`, `Obligations.lean`, `Proofs.lean`, the Aeneas model | — |
| `djinn/verus/src/` | — | `lib.rs`, `vocab.rs`, `relations.rs`, `obligations.rs`, `spec.rs` (generated, trusted, rewritten on every verify), `proofs.rs` (the implementer's; helper modules under `proofs/`) |

The report (`djinn/report.toml`) records `backend = "verus"`, so `cargo build`
judges the crate by the Verus project. See [docs/VERUS.md](../../docs/VERUS.md)
for what is generated and what makes the PASS trustworthy.

```sh
cargo djinn verify        # == cargo build, == verus …, PASS
cargo build               # the gate accepts the verified crate
cargo run                 # the driver, as in example/clamp
```

Here the four unambiguity proofs are the skeleton's empty bodies: Verus
proves them without help. `count_negative`'s implementation carries the loop
invariant and the two `Seq::filter` facts its postcondition needs.
