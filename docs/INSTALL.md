# Installing Djinn

Apart from Rust, you need the following four parts:
- the Djinn tools themselves
- the verification toolchain they call (Charon, Aeneas, Lean)
- a coding agent
- the editor plugins

## 1. Compiling Djinn

Clone this repository and build:

```sh
git clone https://github.com/shenniger/rust-djinn
cd rust-djinn/rust-djinn
cargo build --workspace
```

Below, *the checkout* is the directory `git clone` created: the one holding
`docs/`, `example/`, `editors/` and the tool sources in `rust-djinn/`.

The build produces three things under `rust-djinn/target/debug/` in the checkout:

| Binary | Role |
|---|---|
| `cargo-djinn` | the driver: `cargo djinn translate / verify / implement / status / smoke-test / bench / optimize / clean / guide` |
| `rust-djinn-lsp` | the language server for the editor plugins |
| the `djinn` library and its `djinn!` macro | what your crates depend on; built on demand by `cargo` |

Put the two binaries on `PATH`. Symlinks into `~/.cargo/bin` track later
rebuilds, so you only do this once:

```sh
ln -sf "$PWD/target/debug/cargo-djinn" ~/.cargo/bin/cargo-djinn
ln -sf "$PWD/target/debug/rust-djinn-lsp" ~/.cargo/bin/rust-djinn-lsp
cargo djinn --help
```

`cargo install --path cargo-djinn --force` works too, but you would have to repeat it
after every change to the tools.

A crate uses Djinn by loading the library and giving its Lean namespace:

```toml
[dependencies]
djinn = { path = "/path/to/rust-djinn/rust-djinn" }   # the library crate, in the workspace

[package.metadata.charon]
preset = "aeneas"

[package.metadata.djinn]
namespace = "MyCrate"                          # the Lean namespace
```

The specification is every `djinn! { … }` block in the crate's `src/` (the
binaries in `src/bin/` aside), in as many files as you like. To name the
files yourself instead, say `spec = "src/spec.rs"` or
`spec = ["src/spec.rs", "src/lz77.rs"]`.

The examples under `example/` are set up this way and are the quickest check
that part 1 worked: `cd example/clamp && cargo build` compiles, because the
example ships verified and its verification report is in place.

## 2. Aeneas and the other dependencies

Djinn needs tools to prove things about Rust code: Charon turns the crates
into an intermediate form, Aeneas turns that into Lean, and Lean checks the
proofs against the Mathlib-based Aeneas library. The tools expect all three
under `tools/aeneas`, but any location works if you say where (see the end
of this section).

### Rust nightly

Charon is a rustc plugin and pins its own nightly. Installing rustup is all
you need: Charon's `rust-toolchain` file makes rustup fetch
`nightly-2026-09-17` with the `rustc-dev`, `llvm-tools`, `rust-src` and
`miri` components the first time it builds. Your own crates keep using
whatever toolchain they like; Charon runs them through its pinned one only
during translation.

### OCaml and opam

Aeneas and the Charon library are OCaml. Install
[opam](https://opam.ocaml.org/doc/Install.html), create an OCaml 5 switch,
and install the packages both projects need:

```sh
opam switch create 5.4.0
eval $(opam env)
opam install dune calendar core_unix domainslib easy_logging logs menhir \
  ocamlformat ocamlgraph odoc ppx_deriving ppx_deriving_yojson progress \
  unionFind visitors yojson zarith
```

### Aeneas and Charon

```sh
# in the checkout:
mkdir -p tools && cd tools
git clone https://github.com/AeneasVerif/aeneas
cd aeneas && git checkout 557eff83
make setup-charon        # clones Charon at the commit in ./charon-pin and builds it (Rust + OCaml)
make                     # builds ./bin/aeneas
```

`make setup-charon` takes a while: it builds Charon's rustc driver with
the nightly above and runs its tests. When it finishes you have
`tools/aeneas/charon/bin/charon` and `tools/aeneas/bin/aeneas`, which is
where the example crates look.

### Lean and the Aeneas library

Install [elan](https://github.com/leanprover/elan); it picks the Lean version
from each project's `lean-toolchain` file (Aeneas pins `v4.31.0`). Then
build the Aeneas Lean backend once. Mathlib comes from its cache; the Aeneas
library itself compiles from source and takes a quarter of an hour on a
laptop.

```sh
# in the checkout:
cd tools/aeneas/backends/lean
lake exe cache get
lake build
```

Every Djinn crate gets its own small Lean project under `djinn/proofs/`,
requiring Aeneas by path. To keep them from each downloading Mathlib again,
`cargo djinn` links each project's package directory to a shared cache if
one exists. Create it from the backend you just built:

```sh
mkdir -p ~/.cache/djinn
cp -R tools/aeneas/backends/lean/.lake/packages ~/.cache/djinn/lake-packages
```

A different location can be given as `lake_packages` in the crate metadata
or as `DJINN_LAKE_PACKAGES`.

### Z3

`cargo djinn smoke-test` and the editor's as-you-type lint run bounded checks
of a specification with Z3 before any agent time is spent. They need the
`z3` binary on `PATH`:

```sh
brew install z3            # macOS
sudo apt install z3        # Debian and Ubuntu
```

### Telling the tools where things are

Each crate names its tool paths in `Cargo.toml`, relative to the crate
directory, except for the Lean backend, which is relative to the crate's
Lean project in `djinn/proofs/` because it ends up in that project's
lakefile:

```toml
[package.metadata.djinn]
namespace = "MyCrate"
charon = "../../tools/aeneas/charon/bin/charon"
aeneas = "../../tools/aeneas/bin/aeneas"
aeneas_lean = "../../../../tools/aeneas/backends/lean"
```

Absolute paths are fine, and so are environment variables, which win over
nothing but lose to the metadata: `DJINN_CHARON`, `DJINN_AENEAS`,
`DJINN_AENEAS_LEAN`, `DJINN_LAKE_PACKAGES`. Setting the three tool variables
in your shell profile lets a new crate's metadata hold only `namespace`.

### Checking the installation

```sh
# in the checkout:
cd example/sort
cargo djinn verify
```

The run prints its stages, `== cargo build`, `== charon`, `== aeneas`,
`== lake build`, `== axiom audit`, and ends with `PASS`. The first verify of
any crate compiles the Lean project and takes a minute or two; later runs
take about twenty seconds. If `charon` or `aeneas` is reported missing, the
paths in the previous step are wrong; if `lake` complains about Mathlib,
the shared cache was not created or `lake exe cache get` did not run.

## 3. An agent

`cargo djinn implement` and `cargo djinn optimize` hand the specification
to a coding agent, running in a jail with the verifier as its tool. Nothing
else in Djinn needs one: `translate`, `verify`, `status`, `smoke-test` and
`bench` are deterministic and free. Install either or both of:

| Agent | Models | Install |
|---|---|---|
| [Claude Code](https://docs.anthropic.com/en/docs/claude-code) | Claude | `npm install -g @anthropic-ai/claude-code`, or `brew install --cask claude-code` |
| [Codex CLI](https://github.com/openai/codex) | GPT | `npm install -g @openai/codex`, or `brew install codex` |

Coding agents are expensive. You have two options:

- **A subscription.** Run `claude` or `codex` once in a terminal and choose
  to log in; the browser flow links the CLI to your Claude or ChatGPT
  account, and usage counts against that plan.
- **An API key.** Set `ANTHROPIC_API_KEY` for Claude Code or `OPENAI_API_KEY`
  for Codex in the environment `cargo djinn` runs in, and usage is billed
  per token to that key.

Djinn can get expensive! If you don't have the more expensive subscriptions,
it will noticably drain your usage. The `--limit` option of `implement` and `optimize`
stops a run at a dollar amount; with a subscription the figure is an
estimate from token counts, with a key it is what you pay.

Check that the agent answers before handing it a crate:

```sh
claude -p 'say ok'
codex exec 'say ok'
```

Codex is the default; pick per run with `--agent codex` or `--agent claude`.
The editor plugins use the `djinn.agent` setting or the `AGENT` variable at the
top of the Neovim config, both `codex` by default.

> **Note:** Codex is a bit faster than Claude. In our runs its `implement` and
> `optimize` rounds took minutes where Claude's often took the better part of
> an hour, and cost far less; Claude's long rounds sometimes found larger wins.
> Choose Claude explicitly when you want that trade.

## 4. The editor plugins (not required, but highly recommended!)

To comfortably use rust-djinn, set up your code editor for it!

You will see the proof status of every function, the smoke-test as a linter while you type,
the implement / verify / smoke-test commands with their progress, and you can easily jump
to the implementation and proofs.

### VS Code

The extension is in `editors/vscode`. Run it from the checkout:

```sh
cd editors/vscode
npm install
code --extensionDevelopmentPath=$PWD ../../example/clamp
```

Or package it once and install the result like any extension:

```sh
npx @vscode/vsce package --allow-missing-repository     # answers yes to the licence warning if asked
code --install-extension rust-djinn-0.2.0.vsix
```

The server is looked up on `PATH`, then in `~/.cargo/bin`, then as the debug
build inside the checkout, so after part 1 nothing needs configuring.
Settings, all under `djinn.`:

| Setting | Default | Meaning |
|---|---|---|
| `serverPath` | `rust-djinn-lsp` | the server binary, if not found by the lookup |
| `driverPath` | empty | `cargo-djinn`, if not next to the server |
| `agent` | `codex` | the agent for *Djinn: Implement* |
| `status` | `line` | how the status is drawn: `line` after each function, `inlayHint`, or `off` |

The extension also sets `rust-analyzer.cargo.extraEnv` to `DJINN_GATE=off`
by default. The compile-time gate (a `fn` without a current verification is a
compile error) would otherwise make rust-analyzer flag every function you
are still working on; with the gate off for analysis, the Djinn status shows
the verification state instead, and `cargo build` still enforces it.

### Neovim

`editors/nvim/djinn.lua` is a complete, plugin-free configuration for
Neovim 0.10 or later. Try it without touching your own config:

```sh
# in the checkout:
nvim -u editors/nvim/djinn.lua example/clamp/src/spec.rs
```

To add Djinn to an existing configuration, the essential part is one
`vim.lsp.start` beside your rust-analyzer setup:

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "rust",
  callback = function(ev)
    vim.lsp.start({
      name = "rust-djinn-lsp",
      cmd = { "rust-djinn-lsp" },
      root_dir = vim.fs.root(ev.buf, { "Cargo.toml" }),
    })
  end,
})
```

and, for rust-analyzer, `settings = { ["rust-analyzer"] = { cargo = {
extraEnv = { DJINN_GATE = "off" } } } }` for the same reason as in VS Code.
The full file adds the status drawn as a dimmed line below each function,
key maps under `<leader>d`, and progress in the status line; copy what you
want from it.

### Without an editor

Use `cargo djinn` directly, e.g. `cargo djinn implement` to run the agent and
`cargo djinn verify` to verify.

`editors/lsp-check.py` is a scripted client that starts the server on a
file, prints the lenses, hints and diagnostics it sends, and can run
commands. It is the fastest way to tell whether a problem is in the server
or in the editor setup:

```sh
# in the checkout:
python3 editors/lsp-check.py rust-djinn-lsp example/clamp/src/spec.rs
```

# Next steps
Once you're set up, follow [FIRST_STEPS.md](FIRST_STEPS.md).
