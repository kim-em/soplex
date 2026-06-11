# LP

[![Lean](https://img.shields.io/badge/Lean-4.31.0--rc1-blue.svg)](./lean-toolchain)
[![License](https://img.shields.io/github/license/leanprover/lp.svg)](./LICENSE)

Linear programming in Lean 4: the `lp` and `maximize` tactics for discharging
linear-arithmetic goals, and a verified solver that runs
[SoPlex](https://soplex.zib.de/) (the LP solver from the SCIP optimization
suite) and checks its exact certificate in Lean before returning a
proof-carrying result. SoPlex is an untrusted oracle — every certificate is
validated by a pure-Lean checker, so a solver bug can never yield an unsound
proof.

Jump straight into the [Quickstart](#quickstart). LP is sliced into small
packages (a pure checker, the tactics, and pluggable solver backends); if you
want only part of it or a different backend, see
[Just the verified solver](#just-the-verified-solver-no-tactics),
[Choosing a backend](#choosing-a-backend), and [Packages](#packages) below.

## Quickstart

Add `LP` to your `lakefile.lean`:

```lean
require LP from git "https://github.com/leanprover/lp" @ "main"
```

This example maximizes `3 x₀ + 5 x₁` subject to
`x₀ ≤ 4`, `2 x₁ ≤ 12`, `3 x₀ + 2 x₁ ≤ 18`, and `x₀, x₁ ≥ 0`
(textbook example; optimum is `x = (2, 6)` with objective `36`):

```lean
import LP
open LP LP.Verify

-- Proving theorems via `lp` is usually faster than Mathlib's `linarith`.
example (x₀ x₁ : Rat) (_ : x₀ ≤ 4) (_ : 2 * x₁ ≤ 12) (_ : 3 * x₀ + 2 * x₁ ≤ 18)
    (_ : 0 ≤ x₀) (_ : 0 ≤ x₁) : 3 * x₀ + 5 * x₁ ≤ 36 := by lp

-- The tactic also solves linear arithmetic problems involving quantifiers.
example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 3 ∧
    ∀ y : Rat, x ≤ y → y ≤ 5 → y ≤ 2 * x := by lp

-- The library can also generate certificates for linear programming problems:

def lp : Problem 3 2 :=
  { c         := #v[3, 5]
    a         := #[(0, 0, 1), (1, 1, 2), (2, 0, 3), (2, 1, 2)]
    rowBounds := #v[(none, some 4), (none, some 12), (none, some 18)]
    colBounds := #v[(some 0, none), (some 0, none)] }

def main : IO Unit := do
  match solveVerified (opts := { sense := .maximize }) lp with
  | .error e  => IO.println s!"solve failed: {repr e}"
  | .ok r =>
    match r.verified with
    | .optimal x h =>
      -- `h.1 : IsFeasible r.normalized x.toArray`
      -- `h.2 : IsOptimal  r.normalized .maximize x.toArray`
      let _ := h
      IO.println s!"optimal x = {repr x.toArray}"
    | .infeasible _    => IO.println "infeasible (with Lean proof)"
    | .unbounded _ _ _ => IO.println "unbounded (with Lean proof)"
    | .unchecked s     => IO.println s!"unchecked: {repr s}"
```

Key shape:

* `Problem m n` is indexed by `m` constraints and `n` variables, so
  every array has its size pinned in the type. `c`, `rowBounds`,
  `colBounds` are `Vector`s; `a` is a sparse `(row, col, value)` list.
* `rowBounds` and `colBounds` are `(lo, hi)` pairs with `none = ±∞`,
  covering `≤`, `=`, `≥`, ranged constraints, and boxed variables
  uniformly.
* `solveVerified` returns a `VerifiedSolve` whose `verified` field is
  either a constructor carrying a real Lean soundness proof
  (`.optimal x h`, `.infeasible h`, `.unbounded x r h`) or
  `.unchecked status` when SoPlex was undecided or the certificate
  failed to check.

This example is kept in [`Examples/Quickstart.lean`](./Examples/Quickstart.lean)
and built as `lake exe quickstart-example` so it stays in sync with
the API. See [`Examples/`](./Examples/) for the examples index.

## Tactics

The verified pipeline is exposed as two `Rat`-affine tactics that
build kernel proof terms — no `Problem`/`Certificate` data reaches the
kernel, only a weighted-sum-of-hypotheses identity discharged by an
explicit-proof-term constructor.

### `lp` 

```lean
import LP

example : (1 : Rat) < 2 := by lp

example (a b : Rat) (_ : 2 * a + b ≤ 5) (_ : a - b ≤ 1) :
    3 * a ≤ 6 := by lp

example (a : Rat) (_ : a ≤ 0 ∧ 0 ≤ a) : a = 0 := by lp

example (x : Rat) (_ : x ≤ 0) : x < 1 := by lp

example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 1 := by lp

example : ∃ x : Rat, ∀ y : Rat, 0 ≤ y → y ≤ 1 → x ≥ y := by lp

example : ∃ x : Rat, 0 ≤ x ∧ x ≤ 3 ∧
    ∀ y : Rat, x ≤ y → y ≤ 5 → y ≤ 2 * x := by lp
```

Hypotheses that are not non-strict `Rat`-affine are silently ignored
(strict hypotheses are rejected with a tactic-level diagnostic). When
SoPlex returns infeasible, `lp` derives `False` from the dual and
closes any goal.

`lp` handles a Π₂ fragment of linear rational arithmetic. Atoms are
`Rat`-affine (in)equalities (`≤`, `<`, `=`, `≥`, `>`) in the
`Rat`-typed locals; these combine under `∧`, under `∃ x : Rat`, and
under inner `∀ y : Rat, g₁ → … → gₖ → b` whose guards `gᵢ` and body
`b` are themselves `Rat`-affine atoms — including guards that mention
the outer existential witness. The local context contributes
non-strict linear `Rat` hypotheses; SoPlex serves as an untrusted
oracle for Farkas / dual multipliers, and the kernel proof is
reconstructed from those multipliers and the original hypothesis
terms.

### `maximize` 

`maximize <expr>` runs a sup-LP over the local hypotheses and injects
`hbound : <expr> ≤ N` where `N` is the certified maximum. Use
`maximize h : <expr>` to choose the hypothesis name.

```lean
example (x₀ x₁ : Rat) (_ : 0 ≤ x₀) (_ : 0 ≤ x₁) (_ : x₀ ≤ 4)
    (_ : 2 * x₁ ≤ 12) (_ : 3 * x₀ + 2 * x₁ ≤ 18) :
    3 * x₀ + 5 * x₁ ≤ 36 := by
  maximize 3 * x₀ + 5 * x₁
  exact hbound

example (x : Rat) (_ : 0 ≤ x) (_ : x ≤ 4) : 3 * x + 7 ≤ 19 := by
  maximize h : 3 * x + 7
  exact h
```

If hypotheses are inconsistent, `maximize` closes the surrounding
goal by `False.elim`. If the LP is unbounded above, it fails without
producing a proof.

## Just the verified solver (no tactics)

If you don't need the `lp` / `maximize` tactics and only want verified LP
solving — or just the checker — depend on a narrower slice instead of `LP`:

- **[`leanprover/lp-backend-soplex-ffi`](https://github.com/leanprover/lp-backend-soplex-ffi)**
  gives you `solveVerified`: run SoPlex and get back a `Solution` carrying a
  Lean-checked certificate, without the tactic frontend.
- **[`leanprover/lp-verify`](https://github.com/leanprover/lp-verify)** is the
  pure-Lean certificate checker on its own — no native dependencies, no SoPlex
  build. Use it to validate certificates your own code (or another solver)
  produced against the
  [`leanprover/lp-core`](https://github.com/leanprover/lp-core) `Problem` /
  `Certificate` types.

## Choosing a backend

`by lp`, `solveVerifiedWith`, and the verified drivers dispatch through a
backend registry that lives in
[`leanprover/lp-tactic`](https://github.com/leanprover/lp-tactic). `LP` bundles
the FFI backend by default; to use a different one, `require` exactly the
backend you want. Importing several is fine — the lowest-priority backend whose
probe succeeds wins:

- **[`leanprover/lp-backend-soplex-ffi`](https://github.com/leanprover/lp-backend-soplex-ffi)**
  (priority 10, the default). Production-grade native binding to the vendored
  SoPlex build; what `import LP` resolves to.
- **[`leanprover/lp-backend-soplex-json`](https://github.com/leanprover/lp-backend-soplex-json)**
  (priority 50, experimental). Drives an external binary through a JSON stdio
  protocol (`docs/json-contract.md` in that repository is the wire spec). It
  ships a wrapper (`scripts/soplex-json-wrapper.py`) that drives a stock
  `soplex` CLI in exact-rational mode, so `brew install soplex` +
  `import LPBackendSoplexJSON` is a working `by lp` with no further setup.
  Point `LP_BACKEND_SOPLEX_JSON_BIN` at a different contract-speaking wrapper
  (a Python harness driving HiGHS, a Rust shim around SoPlex, …) to override.
- **[`leanprover/lp-backend-pure`](https://github.com/leanprover/lp-backend-pure)**
  (priority 100). A pure-Lean two-phase tableau simplex on exact rationals —
  zero native deps, zero subprocess calls; `by lp` works in a fresh container
  with only Lean installed. Expect it to be slow beyond toy LPs (exact-rational
  simplex pays for the verifier's exact-rational input contract); the point is
  zero-install CI lanes and demos. Use the FFI backend for production solves.

See [`leanprover/lp-tactic`](https://github.com/leanprover/lp-tactic) for the
registry surface (`registerBackend`, `resolveBackend`, `availableBackends`).

## Packages

`LP` is a thin meta-package: it bundles the default FFI backend and re-exports a
convenient surface, so `import LP` gives you the tactics, `solveVerified`, and
MPS / LP file I/O in one import. The actual work lives in its dependencies:

- **[`leanprover/lp-core`](https://github.com/leanprover/lp-core)** — the shared
  LP vocabulary (`Problem`, `Options`, `Solution`, `Certificate`, `SolveError`)
  and the `LPBackend` record. Pure Lean.
- **[`leanprover/lp-verify`](https://github.com/leanprover/lp-verify)** — the
  pure-Lean certificate checker (`Verified`, `verifyOutcome`, soundness lemmas).
- **[`leanprover/lp-tactic`](https://github.com/leanprover/lp-tactic)** — the
  `lp` and `maximize` tactics, the backend registry, and the backend-pluggable
  `solveVerifiedWith` driver.
- **[`leanprover/lp-backend-soplex-ffi`](https://github.com/leanprover/lp-backend-soplex-ffi)**
  — the FFI backend adapter (priority 10) and the synchronous `solveVerified`
  driver.
- **[`leanprover/soplex-ffi`](https://github.com/leanprover/soplex-ffi)** — the
  vendored SoPlex build, the C++ FFI wrapper, and the direct Lean bindings.

For reference, the name of each piece in its three guises:

| Repository | Lake package | Top-level import | Primary namespace |
|---|---|---|---|
| `lp` | `LP` | `LP` | `LP` |
| `lp-core` | `LPCore` | `LPCore` | `LP` |
| `lp-verify` | `LPVerify` | `LPVerify` | `LP.Verify` |
| `lp-tactic` | `LPTactic` | `LPTactic` | `LP` / `LP.Tactic.LP` |
| `lp-backend-soplex-ffi` | `LPBackendSoplexFFI` | `LPBackendSoplexFFI` | `LP.Backend.SoplexFFI` |
| `lp-backend-soplex-json` | `LPBackendSoplexJSON` | `LPBackendSoplexJSON` | `LP.Backend.SoplexJSON` |
| `lp-backend-pure` | `LPBackendPure` | `LPBackendPure` | `LP.Backend.Pure` |
| `soplex-ffi` | `SoplexFFI` | `SoplexFFI` | `LP` |

## Benchmarks

Performance comparisons of `by lp` against Mathlib's `linarith`, plus
the multi-carrier sweep over `Rat` / `Int` / `Dyadic` / `Nat` / `Real`,
live in [`leanprover/lp-benchmark`](https://github.com/leanprover/lp-benchmark).
On the same `ℚ` goals `lp` runs about 2x faster than `linarith`, and the
native computable carriers (`Int`, `Dyadic`, `Nat`) beat the `Rat`
baseline.

## Build

Pinned SoPlex tag: **`v8.0.2`** (transitive via `SoplexFFI`). Pinned
Lean toolchain: see [`lean-toolchain`](./lean-toolchain).

System dependencies:

| Platform | Packages |
|----------|----------|
| Linux    | `build-essential cmake libgmp-dev libgmpxx4ldbl libboost-dev` |
| macOS    | `brew install gmp boost cmake` (plus Xcode Command Line Tools) |
| Windows  | MSYS2 `mingw-w64-x86_64-{gcc,cmake,ninja,make,gmp,boost}` |

Clone and build through Lake:

```bash
git clone https://github.com/leanprover/lp
cd lp
lake exe quickstart-example
lake test
```

Lake fetches `SoplexFFI` and initializes its vendored SoPlex submodule
as part of the build — there are no submodules in this repository
itself.

`quickstart-example` runs the verified solve from the
[Quickstart](#quickstart) above and prints `optimal x = #[2, 6]`.
`lake test` builds and runs the full test suite under
[`LPTest/`](./LPTest). The suite includes
`LPTest/FFIProbe.lean`, which calls `solveVerified` from inside a
tactic and checks the elaboration-time FFI loading path used by future
tactics. For a lower-level FFI-only check
(SoPlex version, throw/catch ABI, small LP sanity check via the direct
binding) use `lake exe ffi-check`.

The first Lake build is slow (~1–3 min) because the `SoplexFFI`
dependency configures and compiles vendored SoPlex with CMake.
Subsequent runs are nearly instant: CMake reuses its cache, and Lake
only rebuilds the FFI wrapper or extracted SoPlex objects when their
inputs change.

## Trust model

SoPlex is treated as an unverified mathematical oracle. Every exact
certificate it produces is checked in Lean before any proof is
constructed. Incorrect certificates, including certificates affected by
solver bugs or sign-convention translation mistakes, are rejected by
the Lean checker and reported as `Verified.unchecked`.

The native C++ FFI remains part of the runtime trusted computing base.
It is trusted to run safely in-process, preserve memory safety and ABI
correctness, and faithfully marshal Lean-side `Problem` and
certificate data. The Lean checker protects the mathematical proof
boundary; it does not make arbitrary native memory-safety or ABI
failures harmless.

Detailed notes on `solveVerified`, presolve, dual multipliers,
maximization canonicalization, and denominator budgets are maintained
in [`docs/verification.md`](./docs/verification.md).

## Layout

```
LP.lean                   # top-level import
LP/Basic.lean             # high-level API + `solveVerified`
LP/Core.lean              # re-exports `LPCore.Backend` + registry
LP/Backend/SoplexFFI.lean # SoPlex FFI backend adapter
LP/Tactic/                # `lp` and `maximize` tactics
  LP.lean                     #   tactic frontend (elaboration + dispatch)
  Q.lean                      #   kernel-reducible rational literals for tactic proofs
LP/Verify.lean            # verifier re-export module
LP/Verify/                # pure-Lean certificate checker
  Types.lean                  #   re-exports `LPCore.Types` (`Problem`, `Certificate`, ...)
  Validate.lean               #   re-exports `LPCore.Validate`
  Driver.lean                 #   compose validate + solveExact + check
  Sound.lean                  #   soundness lemmas 
  Prop.lean, Bool.lean        #   Prop/Bool views of the checker
  Arith.lean, Budget.lean     #   rational arithmetic + denominator budget
Examples/
  README.md                   # examples index
  Quickstart.lean             # quickstart example executable
LPTest/                   # test suite (run via `lake test`)
  FFICheck.lean               #   `ffi-check` executable
  Common.lean                 #   shared test scaffolding (`LP.Verify` only)
  SolveCommon.lean            #   adds `LP` for SoPlex-backed tests
  FFIProbe.lean               #   elaboration-time FFI loading regression probe
  LP*.lean                    #   tactic frontend and proof-term tests
  Solve*.lean, Verify.lean    #   solver and verifier regression tests
  AccessorGoldens.lean        #   accessor documentation golden tests
  FileIo.lean                 #   LP/MPS file-input tests
  Runner.lean                 #   `lake test` driver
  fixtures/                   #   MPS / LP test inputs
docs/accessors.md             # row-sense × column-status accessor reference
docs/backend-abstraction.md   # backend split and registry notes
docs/verification.md          # detailed verified-solve trust model
docs/lp-proof-construction.md # `lp` tactic proof construction notes
lakefile.lean                 # pins the lp sub-packages + `SoplexFFI`
scripts/install-toolchain.sh  # elan + GitHub-fallback toolchain installer
scripts/install-sanitizer-runtime.sh
                              # CI sanitizer runtime installer
scripts/check-pins.py         # pin/manifest consistency + drift report
.github/workflows/ci.yml      # Linux + macOS + Windows CI matrix
.github/workflows/check-pins.yml
                              # pin consistency on PRs; weekly drift report
```

## Licence

`LP` is licensed under the [Apache License 2.0](./LICENSE),
matching SoPlex itself. The compiled binary's GMP runtime dependency
(LGPL) is linked dynamically by default through `SoplexFFI`. SoPlex
itself is linked into the Lean shared library from the vendored static
archive.
