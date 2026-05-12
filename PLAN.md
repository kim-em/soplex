# lean-soplex — plan

Stub repo. Goal: Lean 4 FFI bindings for **SoPlex**, the LP solver from
the SCIP optimization suite, used in its **exact (iterative-refinement)
mode**.

This repo doesn't ship code yet. It exists as a forward-looking design doc
so that if/when [`kim-em/sos`](https://github.com/kim-em/sos) (or another
Lean project) needs a production-grade exact LP solver, this is the place
to drop one.

## What SoPlex is

SoPlex is a high-performance LP solver developed at ZIB. It's part of the
SCIP optimization suite and one of the standard LP solvers used in research
MILP/MIP backends. The interesting feature for our purposes is its
**iterative refinement** mode: it solves in floating point at full
production speed and then refines to an exact rational answer using
controlled perturbations + GMP, with provably exact basis decisions.

References:
- Gleixner, Steffy, Wolter. *Iterative Refinement for Linear Programming*
  (INFORMS J. Computing, 2016).
- Source: https://github.com/scipopt/soplex (active development).
- Project page: https://soplex.zib.de/
- Licence: Apache 2.0 (clean to wrap).

## Why we'd want it

Where [`lean-qsopt`](https://github.com/kim-em/lean-qsopt) gives us a
pure-rational simplex (slow but simple), SoPlex gives us **fast** exact
LP — interior-point speed for the float pass, exact-rational refinement
only on the final answer. Two situations where this matters:

- The half-Newton-polytope basis pruning for `kim-em/sos` issue #23 has a
  bounded LP size (a few dozen monomials) that QSopt-Exact and Tier-0
  in-tree both handle fine. SoPlex would only matter if the SOS pipeline
  starts solving LPs at a larger scale (e.g. exact polyhedral
  preprocessing of Putinar constraints, exact rational basis recovery
  from float SDP solutions).
- A future Lean MILP backend, where the LP relaxation needs to be both
  exact and fast.

For the immediate `kim-em/sos` use case, the in-tree Tier-0 simplex
suffices and we should not add this FFI dependency until a second
LP-shaped problem appears.

## Template: follow `lean-csdp`

The build pattern is fully solved by [`kim-em/lean-csdp`](https://github.com/kim-em/lean-csdp).
Mirror that structure:

```
soplex/                  # vendor as git submodule (scipopt/soplex)
ffi/lean_soplex.cpp      # C++ glue translating flat sparse LP data
ffi/lean_soplex_bridge.cpp  # Lean-callable C-ABI entry points
LeanSoplex/Basic.lean    # opaque FFI declarations + Lean-side types
Main.lean                # worked example (used as smoke test)
lakefile.lean            # build configuration
.github/workflows/ci.yml # Linux + macOS + Windows CI
scripts/install-toolchain.sh
README.md
LICENSE                  # Apache 2.0 for the wrapper
```

Note: SoPlex is C++. The bridge file needs `extern "C"` linkage to expose
a C ABI Lean can call. That's a wrinkle relative to lean-csdp (pure C);
keep the bridge surface narrow.

## API to expose

Mirror SoPlex's high-level entry. Minimum viable surface:

```lean
namespace LeanSoplex

structure Problem where
  numVars        : Nat
  numConstraints : Nat
  /-- Objective coefficients (length = numVars). Set all zero for feasibility. -/
  c              : Array Rat
  /-- Constraint matrix entries: (row, col, value), 0-indexed. -/
  a              : Array (Nat × Nat × Rat)
  /-- RHS of each constraint (length = numConstraints). -/
  b              : Array Rat
  /-- Constraint sense per row: ≤, =, ≥. -/
  sense          : Array ConstraintSense
  /-- Variable bounds: (lo, hi); use `none` for ±∞. -/
  bounds         : Array (Option Rat × Option Rat)

inductive Solution where
  | optimal     (x : Array Rat) (objective : Rat) (dual : Array Rat)
  | infeasible  (farkas : Array Rat)
  | unbounded   (ray : Array Rat)
  | error       (message : String)

/-- Solve in iterative-refinement mode. Float pass + GMP refinement;
output is exact but solver still runs at near-float speed. -/
@[extern "lean_soplex_solve_exact"]
opaque solveExact (p : Problem) : IO Solution

/-- Solve in pure float mode. Use only when you don't need exact basis
decisions (e.g. as a preconditioner). -/
@[extern "lean_soplex_solve_float"]
opaque solveFloat (p : Problem) : IO Solution
```

Expose both modes — the float mode is useful as a preconditioner / sanity
check, and SoPlex's whole value proposition is "you get to choose".

## System dependencies

SoPlex needs GMP for exact mode and (optionally) Boost. Per-platform
pattern from lean-csdp:

| Platform | Packages |
|----------|---|
| Linux    | `libgmp-dev libboost-dev` |
| macOS    | `gmp boost` (Homebrew) |
| Windows  | MSYS2 `mingw-w64-x86_64-gmp mingw-w64-x86_64-boost` |

Vendoring: git submodule `scipopt/soplex` pinned to a tagged release. Build
via SoPlex's bundled CMake invoked from the lakefile.

## What this repo is NOT yet

- No Lean code is committed.
- No CI is configured.
- No release of SoPlex is pinned.

This file is the contract for what someone (maybe Claude in a future
session) should build out. Open an issue here when you start, and link
back to `kim-em/sos` issue #23 (or wherever the immediate need is).

## Comparison with lean-qsopt

| Property | lean-qsopt (QSopt-Exact) | lean-soplex (SoPlex exact) |
|---|---|---|
| Algorithm | Pure rational simplex | Float simplex + iterative refinement |
| Speed | Slow on large LPs | Near-float speed |
| Exactness | Always exact | Exact final answer |
| Codebase size | Small, C, autotools | Large, C++, CMake |
| FFI complexity | Lower (C ABI) | Higher (C++ → C ABI bridge) |
| Maintenance | Low (stable, small) | Higher (active SCIP project, frequent releases) |
| When to pick | Educational, small LPs, simplicity | Production-scale exact LP |

If only one ever ships, it's probably `lean-qsopt` (lower complexity,
sufficient for any small-LP need). `lean-soplex` is the move when LP size
makes pure-rational simplex genuinely too slow.
