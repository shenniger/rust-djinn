# First steps

This walk-through uses `example/clamp`, a crate with four small verified
functions and a plain-Rust driver. It assumes the installation in
[INSTALL.md](INSTALL.md) is done: `cargo djinn --help` prints the commands,
`cargo djinn verify` in `example/sort` ends with `PASS`, and one of the
editor plugins is set up.

Here's what we'll do on our short guide through Djinn: look at what a Djinn
crate contains and the language it is written in, open it in the editor and
add a function to it, have that function optimised, and end with the
command-line reference behind all of it.

## What's in a Djinn crate?

```sh
cd example/clamp
```

```
Cargo.toml            depends on `djinn`; [package.metadata.djinn] names the spec file and tool paths
src/spec.rs           the specification: a `djinn! { … }` block, plus plain Rust (the driver)
src/lib.rs            `mod spec;` and the implementation module, included by path from djinn/
src/main.rs           reads stdin, calls the driver in spec.rs
src/bench.rs          a workload, for `cargo djinn bench` and `optimize`
djinn/solution/mod.rs the implementation: written by the agent, never by you
djinn/proofs/         a Lean project: Spec, Obligations and Vocab (generated), Code (Aeneas), Proofs (the agent)
djinn/report.toml     the verification report; `cargo build` reads it
.djinnscratch/        disposable: jails, job logs, backups, Charon/Aeneas output, the agent's guide
```

Djinn functions are specifications. Here's a few:

```rust
use djinn::djinn;

djinn! {
    #[requires(lo <= hi)]
    pub fn clamp(x: i32, lo: i32, hi: i32) -> r: i32 {
        lo <= r <= hi;
        x < lo => r == lo;
        x > hi => r == hi;
        lo <= x <= hi => r == x;
    }

    pub fn count_negative(v: &[i32]) -> r: usize {
        r == v.iter().filter(|y| y < 0).count();
    }

    pub fn min(a: i32, b: i32) -> r: i32 {
        r <= a;
        r <= b;
        r == a || r == b;
    }

    pub fn max(a: i32, b: i32) -> r: i32 {
        r >= a;
        r >= b;
        r == a || r == b;
    }
}
```

A `fn` has a Rust signature with a named output, and a body of statements.
Every statement is a constraint on the output, and the body is their
conjunction: `clamp`'s result lies in the range and equals whichever of
`x`, `lo`, `hi` the three implications pick. `#[requires]` is a
precondition; callers must establish it, and the implementation may assume
it.

The `djinn!` macro expands each `fn` into a Rust declaration whose body
lives in `djinn/solution/mod.rs`, so the rest of the crate calls `clamp(x,
lo, hi)` like any function. The driver at the bottom of `spec.rs` does
exactly that:

```rust
let negatives = count_negative(&values);
let clamped: Vec<i32> = values.iter().map(|&x| clamp(x, lo, hi)).collect();
```

The driver is ordinary Rust and is never translated or verified; its one
duty is to establish preconditions, and you can see it check `lo <= hi`
before calling `clamp`.

An LLM must implement each function in normal Rust and prove certain
obligations about it: that the specification admits one output per input
(`unambiguous`), and that the implementation produces it, terminates and
never panics (`impl_correct`). The example ships with that done. The rest
of this guide adds a function and has it done again.

Apart from `func`s, you can also define `rel`s. A `rel` is a named relation:
a set of constraints you can use inside `fn`s, with the same syntax. It is
never implemented and owes no unambiguity proof, so it may relate an input
to many outputs. Think of a `rel` as providing vocabulary you can use in
Djinn functions.


## The editor

Use either VS Code or Neovim (see setup in
[INSTALL.md](INSTALL.md)). Open the example:

```sh
code example/clamp                                           # with the extension installed
nvim -u ../../editors/nvim/djinn.lua src/spec.rs             # the demo configuration
```

### The status at every function

After each `fn` and `rel`, you'll see the proof status, taken from the last
verification and kept current: green `✓ ok`, grey `unverified`,
`changed since verification` once you edit a function, and red when the
smoke-test found something. In VS Code it is drawn after the line; in Neovim
on a dimmed line below. Hover it for the detail.

Above the first function, find a row of code lenses: `obligations`, `proofs`,
`▶ implement`, `verify`, `smoke-test`, `guide`. Every function has its own
`obligations` and `proofs` lenses, which open the Lean file at that
function's theorem. Click `obligations` on `clamp` to see what the LLM had
to prove, and `proofs` to see that it did.

![`clamp` in VS Code: the lens row above the function and the green `✓ ok` status after its first line](clamp.png)

### Adding a function

Add an absolute value to the block in `src/spec.rs`:

```rust
    pub fn abs(x: i32) -> r: i64 {
        r == x || r == -x;
    }
```

Its status reads `unverified`, and a moment after you stop typing it
turns red, `smoke: ambiguous — x = -1 admits both r = -1 and also r = 1`,
with a diagnostic on the name:

```
abs unambiguity: AMBIGUOUS — one of 16 counterexamples within the bounds (inputs in [-8, 8], sequences up to length 4)
x = -1  admits both  r = -1   and also   r = 1
```

This is the smoke-test, a solver searching small inputs for a contradiction,
an input with no output, two outputs for one input, or an index out of
range. It runs on open, on save and while you type, takes seconds, and
costs nothing. Here it found that two outputs satisfy `r == x || r == -x`
for every non-zero input; an agent would have found the unambiguity proof
impossible after some expensive trying. A contradiction is reported
differently: each of the statements that cannot hold together gets a mark,
and they are linked in the problems view.

![`abs` in VS Code: the name underlined, and after the line the red status `unverified · smoke: ambiguous — x = -1 admits …`](abs-amb.png)

Add the missing statement and the diagnostic goes away:

```rust
    pub fn abs(x: i32) -> r: i64 {
        r >= 0;
        r == x || r == -x;
    }
```

### Having it implemented

Now run `▶ implement` from the lens row, the palette, or the key (typically
"<space>di" in Neovim). You'll see the agent's progress where the editor shows
long-running work (the status bar in VS Code and the status line in Neovim,
one line per event): `abs: unambiguity proof now passing`, `verify #2:
PASS`. The status after `abs` changes as obligations get through, and the
run ends with a one-line message, `djinn implement (codex): PASS — every
obligation verified`, or the failing line.

Implement completes only what is missing, so the four verified functions
are untouched and the run takes a few minutes: a fraction of a dollar with
Codex, or a dollar or two with Claude Code. When `abs` is green, `cargo build`
goes through and the driver can call `abs` like the others. The code
is in `djinn/solution/mod.rs` if you are curious. No need to read it though!
Lean has verified it.

Once the code passes verification, you can compile it as you usually would
with Rust code, e.g. `cargo build`.

### Reference: The commands

In VS Code the commands are in the palette under *Djinn:*, on the
lenses and as chords (`ctrl+alt+d`, then the letter). In Neovim,
use `<leader>d` (typically `<space>d`) followed by the letter.

| Key | Command |
|---|---|
| `i` | implement, with the configured agent |
| `v` | verify |
| `s` | smoke-test |
| `o` | open the obligations of the function under the cursor |
| `p` | open its proofs |
| `g` | open the agent's guide |
| `S` | status |

## Measuring and optimising

Let's now optimize for performance!

First, we measure. For this purpose, `clamp` has a built-in benchmark test set.
Read it in `src/bench.rs` if you are curious.
Run from a shell in `example/clamp`:

```sh
cargo djinn bench
```

```
== bench: 5.72 µs per iteration (median of 5 batches × 39320 iterations; spread 2.3%)
```

Then we ask an agent to optimize:

```sh
cargo djinn optimize --cycles 2 --limit 5 --agent codex
```

Each cycle asks the agent for a faster implementation, re-verifies it, and
keeps it only if it is both proved and faster than the last accepted one.
Anything else is reverted, as is a run you interrupt. The `optimize:` line
in `status` records the result: on this crate, `count_negative` went from
15.92 µs to 5.74 µs over the workload.

### Leaving a choice to the implementer: `any`

Normally every `fn` is unambiguous: you decide *what* is computed and the
agent only decides *how*. `any x: T where c;` gives up part of that control
on purpose. `x` becomes a value the agent picks, constrained only by `c`.
For example, a search that may return any position of `x`, not necessarily
the first, which leaves the agent free to search from the back, in chunks,
or by bisection:

```rust
djinn! {
    // Some position of x in v: which one, if there are several, is the implementer's choice.
    #[weakly_specified]
    #[requires(x in v)]
    #[ensures(v[i] == x)]
    pub fn find(v: &[i32], x: i32) -> i: usize {
        any j: usize where j < v.len() && v[j] == x;
        i == j;
    }
}
```

The proof still covers everything you wrote: `find` returns a position that
holds `x`, never panics and terminates, and every `ensures` must hold for
*every* choice the `where` allows. But the LLM decides what you left open.
**Use `any` only very sparingly and with great care:**

- **Specify carefully.** The `where` clause is your entire guarantee about
  the choice. Forget a constraint and the agent may legally pick something
  you did not want. Drop `v[j] == x` here and any index in range qualifies.
- **Check the code by hand.** `#[weakly_specified]` is required on the `fn`
  and on every `fn` that calls it, and `status` marks each of them "review
  the choices". A human should read all functions that carry this attribute.
- **Know when to use it.** A free choice pays off only if something pushes it
  in a good direction. Usually that is `cargo djinn optimize` with a workload
  that measures what you care about: here, the speed of `find` on your
  data. If you just don't want to type out some trivial detail (e.g. an
  error message), it is almost always a better choice to have an agent help
  you with writing the spec instead of using `any`. That way, what the agent
  chose stays constant across implementation cycles and it is easier to check.

The full semantics, including choices inside `for` loops and in callers, are
in [ANY.md](ANY.md). `example/choice` and the compression levels of
`example/gzip` use `any`.

## Reference: The command line

Everything the editor does is a `cargo djinn` subcommand, run in the crate
directory (or with `--manifest-path`). The ones you will use:

| Command | What it does |
|---|---|
| `cargo djinn status` | one line per function with its obligations, then the agent runs on this crate with their token use and cost |
| `cargo djinn smoke-test [--only NAME]` | the Z3 checks the editor runs as you type, with every counterexample; `example/broken` shows each kind of finding |
| `cargo djinn implement [--agent codex\|claude] [--limit USD]` | runs the agent until every obligation checks; reuses what already passes, `-B` starts over, `--background` returns at once and `status` follows the job |
| `cargo djinn verify` | the whole chain: `cargo build`, Charon, Aeneas, the Lean build, the axiom audit; every run writes `djinn/report.toml` |
| `cargo djinn translate` | regenerates the Lean specification, obligations and the agent's guide without verifying |
| `cargo djinn bench` / `optimize` | see above |
| `cargo djinn clean [--list \| --restore [ID]]` | sets the implementation and proofs aside under `.djinnscratch/backup/`, lists the backups, or brings one back and verifies it |
| `cargo djinn guide` | prints the guide the agent is given |

`status` is the one to remember:

```
  func clamp            unambiguous ✓   impl drafted   impl_correct ✓   [exists ✓]   → ok
  func abs              unambiguous ✓?  impl drafted   impl_correct ✓?  [exists ✓?]   → CHANGED since verification — re-run verify
  funcs implemented and fully verified: 4/5
```

And `cargo build` compiles. A function without a verification that
matches its current text is a compile error until `implement` or `verify`
has passed again:

```
error: djinn func `abs` was never attempted (not in djinn/report.toml); run `cargo djinn implement`
```

The editor plugins turn the gate off for rust-analyzer with
`DJINN_GATE=off`, which is why you could keep editing earlier; `cargo build`
always enforces it.

## Reference: The language in brief

The bodies constrain the output. The forms you will use first:

| Form | Meaning |
|---|---|
| `r == e;`  `lo <= r <= hi;` | equality, chained comparisons |
| `cond => stmt;` | the statement holds when the condition does |
| `if c { … } else { … }` | both branches are statements |
| `for x in list { … }`  `for i in 0..n { … }` | the body holds for every element or index |
| `x in list`  `x not in list` | membership |
| `some k: int { … }` | there is a `k` for which the statements hold (an unnamed intermediate) |
| `match e { Pat(a) => { … } _ => { false; } }` | case analysis on an enum or `Option` |
| `v.iter().filter(\|y\| y < 0).count()` | the Rust idioms the verifier knows models for |
| `a & b`  `a \| b`  `a ^ b` | bitwise and, or, xor of non-negative integers |
| `a << n`  `a >> n` | `a * 2^n` and `a / 2^n` (rounding down): integers are mathematical, so `<<` drops no bits; a 32-bit word is `(a << n) % 2.pow(32)` |
| `const K: &[u32] = &[…];` then `K[i]`, `K.len()` | an array constant of the file, a table of integers (any size: tables are packed for Lean) |
| `x.count_ones()`  `x.leading_zeros()`  `x.trailing_zeros()` (and `count_zeros`, `leading_ones`, `trailing_ones`) | Rust's bit counts of a machine integer (or of `e as u32`) |
| `x.rotate_left(n)`  `x.rotate_right(n)` | Rust's rotations at `x`'s width |
| `x.wrapping_add(y)`  `x.wrapping_sub(y)`  `x.wrapping_mul(y)` | the result reduced to `x`'s width, as Rust computes it (two's complement for signed `x`) |
| `x == if c { a } else { b }` | a value chosen by a condition; each branch need only make sense where it is taken |
| `f(x > 0)`  `b == s.iter().all(\|e\| ok(e))` | a comparison passed as a `bool`; closures may call `rel`s |
| `u32::MAX`  `i8::MIN`  `u16::BITS`  `usize::MAX` | integer bounds (`usize`'s width is left open: 32 or 64 bits) |
| `old(v)` | the entry value of a `&mut` parameter |
| `#[requires(…)]` `#[ensures(…)]` | precondition; a consequence exported to callers and proved from the body |
| `pub rel name(…) -> r: T { … }` | a relation: used by `fn`s, never implemented, may be ambiguous |
| `#[decreases(e)]` `#[total]` | termination measure of a recursive `rel`; ask for its existence proof |
| `#[override_smoke_test]` | skip the smoke-test for this declaration, when its bounded search cannot reach it (a 288-element table, say) |
| `any x: T where c;` | a value the implementer chooses, within `c` — in a `fn` marked `#[weakly_specified]` (see [ANY.md](ANY.md)) |
| `#[weakly_specified]` | required on every `fn` that has an `any` or calls one that does: the implementer's choices are reviewed by a human |

Arguments of a `fn` are Rust types; a `rel` may additionally take `int`, the
mathematical integers, for indices and counts. Structs with `Vec` fields and
arrays `[T; N]` work as inputs and outputs (an array's length is part of its
specification). There is no `Box` and no mutual recursion between `rel`s:
represent a tree as a flat arena of nodes with indices (`example/shapes`).

# Examples
Find more examples in [../example](../example).
