/-
Exp 4 — real soplex certificates: integer-clearing soundness + coefficient growth.

Drives the real exact solver on a few LPs, reads the dual `rowUpper` multipliers
(the same field `lp`'s `assembleLeProof` consumes), and checks the integer-
clearing recipe from the plan (decision 1): scale by `L = lcm` of multiplier
denominators ⇒ integer `kᵢ = L·λᵢ`, and — given integer-affine input rows — every
product `kᵢ·(row entry)` is then integral too. Reports `L` and `max|kᵢ|` to show
magnitudes stay sane (no blow-up).

Run:  cd /Users/kim/projects/lean/lean-soplex && lake env lean SoplexTest/Proto/Exp4Clearing.lean
-/
import SoplexTest.SolveCommon

open Soplex SoplexTest

namespace Exp4

/-- lcm of the denominators of a list of rationals. -/
def denLcm (rs : Array Rat) : Nat := rs.foldl (fun acc r => Nat.lcm acc r.den) 1

/-- Scale the multipliers by `L = lcm(denominators)` and report integrality +
magnitude of the resulting integer multipliers. -/
def clearReport (name : String) (mults : Array Rat) : IO Unit := do
  let L := denLcm mults
  let ks := mults.map (fun r => (L : Rat) * r)
  let allInt := ks.all (fun q => q.den == 1)
  let maxAbs := ks.foldl (fun m q => Nat.max m q.num.natAbs) 0
  IO.println s!"  {name}: mults={mults}"
  IO.println s!"    L(lcm den)={L}  k=L·λ={ks.map (·.num)}  allIntegral={allInt}  max|k|={maxAbs}"

/-- Options matching what the `lp` tactic actually uses: presolve off, but
`precisionBoost` left at its default (unlike `noPresolve`, which disables it). -/
def lpOpts : Options := { ({} : Options) with presolve := false }

/-- Solve one problem and clear its dual `rowUpper` multipliers. -/
def runOne {m n : Nat} (opts : Options) (name : String) (p : Problem m n) : IO Unit := do
  match solveExact opts p with
  | .error e => IO.println s!"  {name}: solveExact error {repr e}"
  | .ok s =>
    IO.println s!"  {name} [status={repr s.status}]  obj={repr s.objective}  primal={repr (s.certificate.primal.map (·.toArray))}"
    match s.certificate.dual with
    | some d =>
      IO.println s!"    dual.rowUpper={d.rowUpper.toArray}  dual.rowLower={d.rowLower.toArray}"
      clearReport name d.rowUpper.toArray
    | none   => IO.println s!"    no dual certificate"

-- Maximize x s.t. 2x ≤ 1  (encoded as minimize -x): optimal x = 1/2, fractional dual.
def ex1 : Problem 1 1 :=
  mkProblem 1 1 (c := #[-1]) (a := #[(0, 0, 2)])
    (rowBounds := #[(none, some 1)]) (colBounds := #[(some 0, none)])

-- Maximize 3a s.t. 2a+b ≤ 5, a-b ≤ 1 (minimize -3a): the lp-style example whose
-- certificate combines the two rows with fractional multipliers.
def ex2 : Problem 2 2 :=
  mkProblem 2 2 (c := #[-3, 0])
    (a := #[(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 1, -1)])
    (rowBounds := #[(none, some 5), (none, some 1)])
    (colBounds := #[(none, none), (none, none)])

-- Maximize x s.t. 3x ≤ 1, 5x ≤ 2 (minimize -x): denominators 3 and 5 → L = 15.
def ex3 : Problem 2 1 :=
  mkProblem 1 2 (c := #[-1]) (a := #[(0, 0, 3), (1, 0, 5)])
    (rowBounds := #[(none, some 1), (none, some 2)])
    (colBounds := #[(some 0, none)])

def main : IO Unit := do
  IO.println "Exp 4 — integer-clearing of real soplex dual multipliers:"
  IO.println "[noPresolve: precisionBoost OFF]"
  runOne noPresolve "ex1 (2x≤1)" ex1
  runOne noPresolve "ex2 (2a+b≤5, a-b≤1)" ex2
  runOne noPresolve "ex3 (3x≤1, 5x≤2)" ex3
  IO.println "[lpOpts: precisionBoost default — matches the lp tactic]"
  runOne lpOpts "ex1 (2x≤1)" ex1
  runOne lpOpts "ex2 (2a+b≤5, a-b≤1)" ex2
  runOne lpOpts "ex3 (3x≤1, 5x≤2)" ex3
  IO.println "[boost: presolve off + precisionBoost := true]"
  let boost : Options := { ({} : Options) with presolve := false, precisionBoost := true }
  runOne boost "ex3 (3x≤1, 5x≤2)" ex3

end Exp4

def main : IO Unit := Exp4.main

-- After rebuilding the FFI from current source, the real `lp` tactic proves a
-- non-dyadic (1/3) dual goal (it FAILED before the rebuild). Only checked when
-- this module is built as an exe (it imports the FFI).
example (x : Rat) (h1 : 3 * x ≤ 1) (_h2 : 5 * x ≤ 2) : x ≤ 1 / 3 := by lp

/-
FINDING — RESOLVED: it was a STALE FFI BUILD, not a real limitation.

Initial observation: solveExact returned `6004799503160661 / 2^54` (≈1/3) for
`max x s.t. 3x≤1,5x≤2`, and the `lp` tactic failed with "dual certificate did
not algebraically cancel".

Root cause: `.lake/packages/SoplexFFI/.lake/build/lib/libsoplexffi.a` was built
2026-05-14 10:44 — BEFORE that day's commit (21:38) "Use exact SoPlex tolerances
for certificates" which fixed the shim (sets FEASTOL=OPTTOL=0, reads
`getDualRational`). Lake "Replayed" the cached `.a` instead of relinking, so Lean
linked a pre-fix bridge that surfaced a float dual.

Proof it was the binary, not SoPlex or the design:
  * A standalone C++ program linking the SAME `build-soplex/lib/libsoplex.a`
    solves ex3 EXACTLY (`primal=1/3`, `dual=[-1/3,0]`, `obj=-1/3`), via both the
    rational and real LP-loading APIs, with PRECISION_BOOSTING on/off/default
    (`setBoolParam(PRECISION_BOOSTING,true)` is rejected but exact works anyway).
  * After `rm`-ing the stale `libsoplexffi.{a,dylib}` and rebuilding, the Lean
    side returns exact `1/3` (`mults=#[1/3,0]`) and `lp` proves `x ≤ 1/3`.

Takeaways:
  * Integer-clearing (decision 1) holds and stays small with exact duals.
  * On a clean checkout the shipped SoplexFFI builds correctly; the staleness was
    a local incremental-build cache artifact. Worth a belt-and-suspenders check
    that lake invalidates the FFI lib when the shim source changes.
-/
