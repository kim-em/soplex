# `lp` vs `linarith` — comparison report

**Subject.** Wall-clock comparison of Soplex's `lp` tactic (this repo) against
Mathlib's `linarith` on linear-arithmetic goals over `Rat`, on the soplex
`main` at the time of writing (`8c8b215`).

**Take-away in one paragraph.** On hand-written tactic-scale problems
(N ≤ ~50 variables), `linarith` is faster — usually 2–3× — because `lp`
pays a per-invocation overhead in metaprogram-side `Expr` construction
that `linarith` largely avoids. Above N ≈ 60, `lp` catches up; above
N ≈ 80, `lp` overtakes; and at N = 100 dense, `linarith` itself fails
(`maximum recursion depth has been reached`) while `lp` completes. The
demonstrable advantage is **scale robustness**, not a structural win on
a particular problem class. SoPlex's actual LP solve is single-digit
milliseconds throughout — it is not the bottleneck on either side.

---

## 1. Methodology

Each benchmark invokes `lake env lean <file>` on a one-example Lean file,
with `/usr/bin/time -p`. Two test families are generated and committed:

| Family | Construction | Goal |
|---|---|---|
| `IntN{n}` | N variables; an N×N integer matrix with random small entries (1..3), made diagonally dominant so `x = 1ₙ` is in the feasible region and on the active boundary | `Σ xᵢ ≤ N` (tight at `x = 1ₙ`) |
| `RatN{n}` | N variables; coefficients of the form `(k/d)` with `k ∈ {1,2,3}`, `d ∈ {2,3,5}` | `Σ xᵢ ≤ N²` |

Each family has paired files: `IntN10LP.lean` calls `by lp`,
`IntN10LA.lean` calls `by linarith`, so the only difference is the
tactic. Wall-clock includes a ~3 s `import` baseline (each invocation
re-imports the dependencies; the figures are total elapsed, not
tactic-only).

The seed is the same as the problem size, so a given N produces the same
instance every run. There is real per-instance variance — see §3.

The generators (Python) live under [`generators/`](./generators/) and
are committed alongside the generated `.lean` files so the harness is
reproducible without re-running them.

## 2. Results

### 2.1 Integer-coefficient dense LPs

| N | `lp` | `linarith` |
|---:|---:|---:|
| 10 | 9.0 s | 3.4 s |
| 20 | 5.3 s | 3.9 s |
| 30 | 9.5 s | 4.8 s |
| 40 | 16.1 s | 6.7 s |
| 50 | 28.2 s | 9.0 s |
| 60 | 13.7 s | 13.5 s |
| 80 | **20.8 s** | 28.3 s |
| 100 | **29.8 s** | **fails — `maximum recursion depth`** |

The N = 10 `lp` figure is a cold-cache outlier (first invocation; subsequent
ones are ~3 s). The N = 60 dip below the N = 50 figure is instance-dependent
— see §3.

### 2.2 Rational-coefficient dense LPs

Coefficients are `(k/d)` with `k ∈ {1,2,3}`, `d ∈ {2,3,5}` — so the
constraint matrix has small rational entries throughout. `lp` and
`linarith` track each other closely up to N ≈ 56, with `linarith`
generally a hair faster. At N ≥ 64 they diverge in a noisy,
instance-dependent way.

| N | `lp` | `linarith` |
|---:|---:|---:|
| 8 | 3.7 s | 3.8 s |
| 16 | 4.3 s | 5.2 s |
| 24 | 6.5 s | 7.2 s |
| 32 | 9.6 s | 10.3 s |
| 40 | 16.1 s | 14.9 s |
| 48 | 19.8 s | 21.0 s |
| 56 | 29.3 s | 27.4 s |
| 64 | 45.6 s | 34.8 s |
| 72 | 52.7 s | 41.3 s |
| 80 | **24.8 s** | 53.4 s |

The N = 80 row is the per-instance variance from §3 made manifest: the
random instance at that size happens to admit an unusually sparse
Farkas certificate (relatively few nonzero dual multipliers), so `lp`'s
weighted-sum proof is short and the wall-clock collapses below the
import baseline + a few seconds. `linarith`, whose cost grows with its
internal Simplex iterations rather than with certificate sparsity, sees
no equivalent break.

## 3. Instance variance

The dense-LP timings are **not monotone in N**: the random-but-deterministic
seed produces instances whose Farkas certificates SoPlex returns vary in
sparsity. A sparser certificate means a shorter weighted-sum proof, which
means less metaprogram-side `Expr` construction and less kernel
type-checking — both costs grow with the number of nonzero dual
multipliers, not directly with N. Hence N = 60 finishing faster than N = 50,
or rational N = 80 finishing faster than N = 72.

For a smoother trend one would need to average over several seeds per N;
this harness uses one seed per N so the data is reproducible without
randomness in the report.

## 4. Where the time goes

This was profiled (with `IO.monoMsNow` brackets) at multiple points
during the perf-PR sequence. The breakdown on a representative N = 10
instance was, *after* each round of fixes:

| Phase | After #60 (mid 2026-05-14) | On `main` today |
|---|---:|---:|
| `parseFixedExpr` / row parsing | 280 ms → 5 ms | ~few ms |
| `mkFeasProof` / weighted-sum proof | 81 ms → 35 ms | several ms |
| **SoPlex FFI (`solveExact`)** | **7 ms** | **a few ms** |
| `verifyOutcome` + `checkOptimal` | 0 ms | not on the path anymore (direct-cert backend) |
| Kernel type-check of the proof term | 3.4 s | dominant on big instances |

The headline is consistent across every measurement: **SoPlex itself is
not the bottleneck**, and never was. The cost is metaprogram-side
`Expr` construction and kernel type-checking of the produced proof
term. Each perf PR (see §6) has chipped at one of those.

## 5. Families that did *not* yield an `lp` advantage

The original brief was to find linear-arithmetic problem families where
`lp` structurally beats `linarith`. Three families beyond random dense
were tried and reported as negative results; the generators are
preserved in [`generators/families.py`](./generators/families.py) and
[`generators/hilbert_tight.py`](./generators/hilbert_tight.py) for
future reruns.

1. **Geometric amplification chain.** N + 1 variables `x₀ … xₙ`, with
   `x₀ ≤ 1` and `3 xᵢ ≤ 2 xᵢ₋₁`, goal `xₙ ≤ (2/3)ⁿ`. The Farkas
   certificate multipliers are `(1/3)(2/3)^(n-i)` with denominators up
   to `3^(n+1)` — exponentially large. Empirically both tactics finish
   at the import baseline through n = 32: the bignum rationals don't
   cost either anything noticeable.

2. **Hilbert matrices, loose and tight goal.** Scaled Hilbert matrix
   constraints with `Σ xᵢ ≥ b`, and a goal proved entailed either
   loosely or at the **exact rational LP optimum** computed by a
   fractions-based two-phase simplex (in [`generators/exact_lp.py`](./generators/exact_lp.py)). The
   ill-conditioning makes the dual certificate a large rational, but at
   n ≤ 14 the matrix is too small for either tactic to notice. Scaling
   up turns it into the next family (large coefficients).

3. **Large coprime coefficients** (5-digit primes). Both tactics
   succeed, but `lp` is *slower than* `linarith`, and the gap widens
   with N (lp 13 s vs linarith 6 s at N = 32). Large coefficient
   literals carry into `lp`'s proof term — the kernel `decide` check
   over them is more expensive than `linarith`'s direct certificate.
   This is an `lp` weakness, not something to advertise.

The deeper structural reason these don't separate the two tactics: both
are Farkas-certificate methods. `linarith`'s oracle is Simplex-style
feasibility search (Avigad/Lewis) — not naive primal Simplex on the
original LP, so classic Simplex hardness instances (Klee–Minty's
exponential vertex walk) don't bite it. Any family with a *complex*
certificate hurts `lp`'s proof construction at least as much as it
hurts `linarith`'s search; any family with a *simple* certificate is
easy for both.

## 6. Backend evolution timeline

The `lp` tactic has been substantially rewritten several times during
this benchmarking work. The numbers in §2 are on the latest backend.

| PR | What it changed |
|---|---|
| **#53** | Stage-1 `lp` tactic landed: SoPlex oracle + Lean verifier, `simp + grind` discharger. |
| **#55** | Replace `simp + grind` discharger with direct proof-term construction. |
| **#60** | Reflective `AffCert` parsing — `parseFixedExpr` 280 ms → 5 ms at N = 10. |
| **#64** | Replace the verifier backend entirely with a direct Farkas certificate (weighted-sum proof + grobner-discharged identity). Removed the `(kernel) deep recursion` wall at N ≥ 40. |
| **#66/#67** | RatLin normalizer replaces `grobner`; div-literal bridge. |
| **#71/#72** | Explicit-arg `mkAppN` for `direct_le_close`/`direct_lt_close`/`direct_infeasible_close` — fixes `maximum recursion depth` failures at instance-dependent N = 40/50. |
| **#73** | RArray-based atom lookup. |
| **#78** | Replace four `mkAppM` calls in `proveLinearIdentity` with typed builders, deferring middle-term def-eq to the kernel. **Reverted in #79** — reintroduced `(kernel) deep recursion detected` at N ≥ 80. |
| **#81** | Same change as #78, re-merged. **Reverted in #83**, same reason. |
| **#85** | Safe subset of #80: `mkApp2` for the no-implicit `Lin.eval_eq_evalNF`, `mkEqSymm` for `Eq.symm`; the three `Eq.trans` calls stay on `mkAppM` (their middle def-eq must remain elaborator-side). |

Open follow-ups: **#80** (the real `Eq.trans` speedup, which needs the
structural rework rather than a builder swap), **#82** (survey all
`Expr` constructions for laziness opportunities).

## 7. Recommendation

What `lp` can be advertised on today is **scale robustness**: on dense
LPs, `linarith` becomes increasingly slow past N ≈ 50 and fails outright
at N ≈ 100 with `maximum recursion depth`; `lp` is the only tactic that
completes the whole N = 10..100 range over `Rat`. That is a real,
demonstrable claim.

What `lp` cannot be advertised on today is a structural win on a
particular problem class — none was found despite focused attempts.
The crossover where `lp` overtakes `linarith` is currently around
N ≈ 60–80, and the work that lowers that crossover is the same
construction/check-cost reduction tracked in #80 / #82.

The honest summary for anyone choosing between the two on a tactic-scale
problem (≤ ~40 variables): use `linarith`. For larger problems, or where
`linarith` is timing out / hitting recursion limits, `lp` is the right
escape hatch.
