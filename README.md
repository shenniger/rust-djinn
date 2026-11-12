# rust-djinn

**Write what your program must compute. Let an LLM figure out how.**

[Blog post](https://henniger.dev/post/djinn)

rust-djinn is a specification language that is also a programming language.
Djinn functions consist of *constraints*: they relate function inputs to
outputs. An LLM writes the code
that finds that output, and it must also hand over a machine-checked proof
that its code meets the specification. Every Djinn function must be
specified unambiguously: an LLM must prove that every implementation
of the specification must have the same outputs given the same inputs.

rust-djinn's main design goal is ease of use. You do not ever need to read
Lean or Aeneas code, or figure out how to judge whether it is correct. You
just type `cargo djinn verify` and our tooling handles it for you.
The unambiguity constraint means you do not need to be overly worried about
having the LLM run wild. Similar to the
borrow checker, you may end up fighting with it a bit early on, but the
system tries to give you counterexamples and clear error messages.
And you should never feel like you need to write your whole program in Djinn:
you can freely mix and match Djinn functions with traditional Rust functions.
Use Djinn wherever it is useful and then write the rest in Rust.

You can use the Djinn to optimize code. While you specify everything about
how inputs relate to outputs, the Djinn chooses algorithms and figures out
all the other little details that determine performance. Faster code can
be just a `cargo djinn optimize` away.

The idea and the first implementation (on Dafny) are described in the paper:

> Simon Henniger, Stephen Chong, Nada Amin. *Djinnlang: Higher-Level
> Programming by Unambiguous Specification with an LLM in the Compiler.*
> 2026. [arXiv:2609.23954](https://arxiv.org/abs/2609.23954)

Specifications are `djinn! { … }` blocks in normal Rust crates; you can mix
them freely with Rust functions. The generated implementations are plain Rust,
compiled by `rustc`; the proofs are Lean 4 over the [Aeneas](https://github.com/AeneasVerif/aeneas)
model of that Rust — or, with `cargo djinn --backend verus`, [Verus](https://github.com/verus-lang/verus)
annotations and proofs on the Rust itself.

- **Install:** [docs/INSTALL.md](docs/INSTALL.md)
- **First steps:** [docs/FIRST_STEPS.md](docs/FIRST_STEPS.md)
- **The Verus backend:** [docs/VERUS.md](docs/VERUS.md)

_Note: This is research code and far from production-ready. Use at your own peril._

## What a Djinnlang program looks like

A simple example:

```rust
use djinn::djinn;

djinn! {
    #[requires(list.len() >= 1)]
    pub fn max(list: &[i32]) -> r: i32 {
        r in list;                      // r is one of the elements ...
        for x in list { x <= r; }       // ... and none of them is larger
    }
}
```

The body contains no executable code. The two statements are a relation between the
input `list` and the output `r`, and the function is their conjunction. An LLM
implements the function and proves:

| Obligation | What it says |
|---|---|
| `max.unambiguous` | any two outputs the statements admit for the same input are equal |
| `max.exists` | every input that meets the precondition has an output |
| `max.impl_correct` | the generated Rust returns an output the statements admit, terminates, and never panics |
| `max.ens_0` | each `#[ensures]` clause follows from the statements, so callers may rely on it |

Note that the first obligation is what makes this a programming language
rather than a wish list. Because the output is exhaustively specified,
the LLM gets no say in what the program means. The LLM-generated code never
needs to be read, and it can be thrown away and regenerated at any time,
like the output of any other compiler.

## Why

### Shorter code that says what you mean.
A specification states how inputs relate to outputs: no indices to keep in
step, no early returns, no helper that exists only because the loop needed
one. In Rust, a function that finds the start of the line `k` lines before a
position might be a loop with three exits and a comment explaining the off-by-one;
in Djinnlang it is three statements: `r` is at most `pos`, `r` is a line
start, and exactly `k` line terminators lie between `r` and `pos`, or as many
as there are.

Specifications-as-programs also invite a relational style that makes many
programs even shorter. If two functions must round-trip, it is enough to
write one of them and define the other as its preimage: a parser is "the
input whose printing is this string", and the unambiguity proof then
doubles as a proof that the printer is injective. So even where specifying
sounds a lot like programming, the effort is usually lower.

### Constraints help you avoid bugs.
The first draft of a specification contains bugs, just as a program does,
and many of them are contradictions: one part of your head had one mental
model, another part another. A program with a contradiction in it fails
quietly, which is one reason programmers repeat "don't repeat yourself". A
specification with a contradiction in it cannot be implemented at all, so
the bug has to be found before anything else happens. With specifications
the adage becomes *do repeat yourself*: every line is certain knowledge
about your program, and stating the same fact twice from two angles
challenges your assumptions for free.

The unambiguity constraint catches most of the rest, and it is surprisingly
powerful. Forget to say what is in the first cell of an array and the
specification admits two outputs, so the off-by-one is caught; specify a
parser and unambiguity means the grammar itself must be unambiguous.
Section 5.2 of the [paper](https://arxiv.org/abs/2609.23954)
takes a nasty piece of specification and shows that
the common mistakes in it never make it past the unambiguity checker. The
disadvantage: whether your specification is unambiguous is an undecidable
question. While LLMs are pretty good at finding either a proof or a
counterexample, they sometimes may not and you are left waiting.
A compiler that does not terminate is arguably better than one that
produces broken code, but it is a new kind of problem.

### Hillclimbing performance.
The LLM gets a lot of leeway on performance and none on anything else.
Once a specification is proved, optimisation is free of risk: any rewrite
the verifier accepts means the same thing. `cargo djinn optimize` times a
workload you name, asks the LLM for a faster implementation, proves it
again, and keeps it only if it is both verified and faster.

Even in Djinnlang there are different ways to write a function,
inductively versus iteratively, say. But since you only describe how the
outputs relate to the inputs, every way of expressing the same function
is logically equivalent and should have no impact on performance.
As LLMs get better at optimising heavily while still proving adherence to a
specification written without the optimisations in mind, this moves toward
the Platonic ideal of an optimising compiler: you write your function
somehow and the result is the fastest possible program.

## How it works

```
spec.rs ──djinn!──▶ Spec.lean, Obligations.lean       (trusted: generated from the spec)
    │                        ▲
    ▼                        │ Lean checks
cargo djinn implement ──▶ solution/mod.rs + Proofs.lean   (untrusted: written by the agent)
    │
    ▼
cargo build   compiles solution/mod.rs only if the verification report matches the spec
```

1. The `djinn!` macro parses the specification, checks it, and expands to
   Rust signatures that the implementation must provide.
2. `cargo djinn translate` lowers the specification to Lean (`Spec.lean`), runs
   Charon and Aeneas on the implementation to obtain its Lean model, and
   generates the obligations. With `--backend verus` it lowers the
   specification to Verus `spec fn`s instead and generates a verification
   crate in which the obligations are pinned contracts and Verus verifies the
   implementation directly ([docs/VERUS.md](docs/VERUS.md)).
3. `cargo djinn implement` runs an agent in a jail with `cargo djinn verify`
   as a tool: Claude models through Claude Code, or GPT models through Codex,
   billed to whichever subscription you already have. It writes
   `solution/mod.rs` and `Proofs.lean` (with `--backend verus`: the solution
   inside `verus! { … }` and `djinn/verus/src/proofs.rs`) until every
   obligation checks.
4. `cargo djinn verify` has Lean (or Verus) check every obligation. With Lean it
   also audits the axioms the proofs rest on: Lean's own three and
   `Djinn.Vocab.platform_64`, the assumption that the target is 64-bit.
5. `cargo djinn bench` and `cargo djinn optimize` time a workload and
   hill-climb on it under the verifier.
6. `rust-djinn-lsp` shows the proof status after every function in VS Code and
   Neovim, lints with the smoke-test as you type, and runs the commands.

rust-djinn keeps Rust's type system and its functions can easily interface
with Rust.

## This Repository

```
docs/              INSTALL.md, FIRST_STEPS.md, VERUS.md
rust-djinn/        the tools (Cargo workspace)
  syntax/            parser, checks, lowering to Lean and to Verus, emitters
  macros/            the `djinn! { … }` macro
  cargo-djinn/       translate | verify | implement | status | smoke-test | bench | optimize
  lsp/               rust-djinn-lsp
editors/           VS Code extension, Neovim config, a scripted LSP client
example/           sort, clamp, sudoku, lz77 (from the paper), gzip, calib, choice, strmap,
                   broken (what smoke-test catches), clamp-verus (clamp, verified with the Verus backend)
```

## Status and limits

_This is research code and mostly vibe-coded. It is not production-ready
in the least. Use at your own peril._

Currently, this can handle safe Rust over integers,
slices, vectors, strings, structs, enums, `Option` and `Result`, and
recursion. Calls into other crates need a model in the trusted library. We
currently have models for parts of `std`, `core`, `alloc` and `memchr` but they
are mostly vibe-coded and thus untrustworthy. The Verus backend relies on
Verus's `vstd` instead (strings as UTF-8 bytes, `HashMap`s with integer or
`bool` keys, bit-level methods through definitions in its vocabulary, ambient
functions translated and checked by Verus; see [docs/VERUS.md](docs/VERUS.md)).

Because rust-djinn cannot specify performance, it is prone to side-channel
attacks. It is thus (conceptually) not suitable for cryptography.

Unambiguity, existence and implementation proofs are written by
the agent and can fail on hard specifications; the harness reports which
obligation stopped it and the cost so far.
