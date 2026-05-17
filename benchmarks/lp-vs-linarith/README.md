# `lp` vs `linarith` — benchmark harness

A self-contained Lake project that compares Soplex's `lp` tactic against
Mathlib's `linarith` on dense linear-arithmetic goals over `Rat`. It lives
under the Soplex repo but is **not** built by default CI — it requires
Mathlib (for `linarith`), which Soplex itself deliberately does not depend
on. See [`REPORT.md`](./REPORT.md) for methodology and findings.

## Layout

```
benchmarks/lp-vs-linarith/
├── REPORT.md                 — engineering report (read this)
├── README.md                 — this file
├── lakefile.toml             — Lake config (path-requires soplex, requires Mathlib)
├── lean-toolchain            — pinned to the soplex toolchain
├── run.sh                    — wall-clock benchmark runner
├── generators/               — Python generators for the test families
│   ├── dense_integer.py
│   ├── dense_rational.py
│   ├── families.py           — geometric chain, Hilbert (loose), bigcoeff
│   ├── hilbert_tight.py      — Hilbert with the exact rational optimum as goal
│   └── exact_lp.py           — exact-rational two-phase simplex (Fraction-based)
└── LPvsLinarith/             — committed generated test files
    ├── IntN{10..100}{LP,LA}.lean    — integer dense, 16 files
    ├── RatN{8..80}{LP,LA}.lean      — rational dense, 20 files
    ├── DenseInteger.lean            — import index
    └── DenseRational.lean           — import index
```

## Running

```bash
cd benchmarks/lp-vs-linarith
lake exe cache get        # fetch Mathlib's olean cache
lake build                # build the test files (and Mathlib oleans)
./run.sh                  # wall-clock comparison, one row per (N, tactic)
```

The first `lake build` will download the Mathlib cache (several thousand
files). After that, individual examples elaborate in seconds.

To regenerate the test files from the Python generators (e.g. for new
sizes), edit the generator and run something like:

```bash
python3 generators/dense_integer.py 120 lp       > LPvsLinarith/IntN120LP.lean
python3 generators/dense_integer.py 120 linarith > LPvsLinarith/IntN120LA.lean
```
