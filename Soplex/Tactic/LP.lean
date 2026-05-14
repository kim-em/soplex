import Lean
import Soplex.Basic

open Lean Meta Elab Tactic
open Soplex Soplex.Verify

namespace Soplex.Tactic.LP

inductive Rel where
  | le
  | lt
  | eq
  deriving Repr, DecidableEq

structure LinExpr where
  const : Rat := 0
  coeffs : Array (FVarId × Rat) := #[]
  deriving Inhabited

structure ParseState where
  vars : Array FVarId := #[]
  deriving Inhabited

abbrev ParseM := StateT ParseState MetaM

private def ratType : Expr := mkConst ``Rat

private def addVar (fvarId : FVarId) : ParseM Unit := do
  let s ← get
  if s.vars.any (· == fvarId) then
    return ()
  set { s with vars := s.vars.push fvarId }

private def addCoeff (coeffs : Array (FVarId × Rat)) (v : FVarId) (c : Rat) :
    Array (FVarId × Rat) := Id.run do
  if c = 0 then
    return coeffs
  let mut out := #[]
  let mut found := false
  for (v', c') in coeffs do
    if v' == v then
      found := true
      let c'' := c' + c
      if c'' != 0 then
        out := out.push (v', c'')
    else
      out := out.push (v', c')
  if found then out else out.push (v, c)

private def LinExpr.add (a b : LinExpr) : LinExpr :=
  { const := a.const + b.const
    coeffs := b.coeffs.foldl (fun acc (v, c) => addCoeff acc v c) a.coeffs }

private def LinExpr.neg (a : LinExpr) : LinExpr :=
  { const := -a.const, coeffs := a.coeffs.map fun (v, c) => (v, -c) }

private def LinExpr.sub (a b : LinExpr) : LinExpr :=
  a.add b.neg

private def LinExpr.smul (c : Rat) (a : LinExpr) : LinExpr :=
  if c = 0 then {}
  else { const := c * a.const, coeffs := a.coeffs.map fun (v, k) => (v, c * k) }

private def fvarLetValue? (id : FVarId) : MetaM (Option Expr) := do
  let decl ← id.getDecl
  match decl with
  | .cdecl .. => return none
  | .ldecl (value := value) .. => return some value

private partial def parseScalar? (e : Expr) : MetaM (Option Rat) := do
  let e ← withReducible <| whnfR e
  match e with
  | .fvar id =>
      match ← fvarLetValue? id with
      | some value => parseScalar? value
      | none => return none
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``OfNat.ofNat _ =>
          if args.size == 3 then
            match args[1]! with
            | .lit (.natVal n) => return some (OfNat.ofNat n)
            | _ => return none
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseScalar? args[2]!).map (fun x => -x)
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a + b)
            | _, _ => return none
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a - b)
            | _, _ => return none
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some a, some b => return some (a * b)
            | _, _ => return none
      | .const ``HDiv.hDiv _ =>
          if args.size == 6 then
            match ← parseScalar? args[4]!, ← parseScalar? args[5]! with
            | some _, some 0 => return none
            | some a, some b => return some (a / b)
            | _, _ => return none
      | _ => return none
      return none

private partial def parseExpr (e : Expr) : ParseM LinExpr := do
  if let some v ← parseScalar? e then
    return { const := v }
  let e ← withReducible <| whnfR e
  if let some v ← parseScalar? e then
    return { const := v }
  match e with
  | .fvar id =>
      if let some value ← fvarLetValue? id then
        if let some v ← parseScalar? value then
          return { const := v }
      let ty ← inferType e
      unless ← isDefEq ty ratType do
        throwError "lp: expected a Rat expression, found{indentExpr e}"
      addVar id
      return { coeffs := #[(id, 1)] }
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const ``HAdd.hAdd _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).add (← parseExpr args[5]!)
      | .const ``HSub.hSub _ =>
          if args.size == 6 then
            return (← parseExpr args[4]!).sub (← parseExpr args[5]!)
      | .const ``Neg.neg _ =>
          if args.size == 3 then
            return (← parseExpr args[2]!).neg
      | .const ``OfNat.ofNat _ =>
          if let some v ← parseScalar? e then
            return { const := v }
      | .const ``HMul.hMul _ =>
          if args.size == 6 then
            let lhs := args[4]!
            let rhs := args[5]!
            if let some c ← parseScalar? lhs then
              return (← parseExpr rhs).smul c
            if let some c ← parseScalar? rhs then
              return (← parseExpr lhs).smul c
            throwError "lp: nonlinear multiplication; one side of `*` must be a reducibly-closed Rat scalar"
      | .const ``HDiv.hDiv _ =>
          throwError "lp: division is outside the supported affine Rat grammar"
      | _ => pure ()
      throwError "lp: unsupported Rat expression{indentExpr e}"

private def ensureRat (e : Expr) : MetaM Unit := do
  let ty ← inferType e
  unless ← isDefEq ty ratType do
    throwError "lp: expected a Rat expression, found{indentExpr e}"

private def isRatExpr (e : Expr) : MetaM Bool := do
  isDefEq (← inferType e) ratType

private def parseAtomicRat (rel : Rel) (lhs rhs : Expr) :
    ParseM (Option (Rel × LinExpr × LinExpr)) := do
  unless (← isRatExpr lhs) && (← isRatExpr rhs) do
    return none
  return some (rel, ← parseExpr lhs, ← parseExpr rhs)

private def parseAtomic? (type : Expr) : ParseM (Option (Rel × LinExpr × LinExpr)) := do
  let e := type
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const ``LE.le _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[2]! args[3]!
  | .const ``GE.ge _ =>
      if args.size == 4 then
        return ← parseAtomicRat .le args[3]! args[2]!
  | .const ``LT.lt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[2]! args[3]!
  | .const ``GT.gt _ =>
      if args.size == 4 then
        return ← parseAtomicRat .lt args[3]! args[2]!
  | .const ``Eq _ =>
      if args.size == 3 then
        return ← parseAtomicRat .eq args[1]! args[2]!
  | _ => pure ()
  return none

private def isAnd? (type : Expr) : Option (Expr × Expr) :=
  let fn := type.getAppFn
  let args := type.getAppArgs
  match fn with
  | .const ``And _ =>
      if args.size == 2 then some (args[0]!, args[1]!) else none
  | _ => none

private partial def collectHypType (origin : Name) (type : Expr) :
    ParseM (Array LinExpr) := do
  if let some (p, q) := isAnd? type then
    return (← collectHypType origin p) ++ (← collectHypType origin q)
  match ← parseAtomic? type with
  | none => return #[]
  | some (.lt, _, _) =>
      throwError "lp: strict hypothesis `{origin}` is not supported in Stage 1"
  | some (.le, lhs, rhs) =>
      return #[lhs.sub rhs]
  | some (.eq, lhs, rhs) =>
      let d := lhs.sub rhs
      return #[d, d.neg]

private def collectHyps : ParseM (Array LinExpr) := do
  let mut rows := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then
        rows := rows ++ (← collectHypType decl.userName decl.type)
  return rows

private def coeffAt (e : LinExpr) (v : FVarId) : Rat :=
  match e.coeffs.find? (fun (v', _) => v' == v) with
  | some (_, c) => c
  | none => 0

private def mkEntries (rows : Array LinExpr) (vars : Array FVarId) :
    Array (Fin rows.size × Fin vars.size × Rat) := Id.run do
  let mut out := #[]
  for i in [0:rows.size] do
    if hi : i < rows.size then
      let row := rows[i]
      for j in [0:vars.size] do
        if hj : j < vars.size then
          let c := coeffAt row vars[j]
          if c != 0 then
            out := out.push (⟨i, hi⟩, ⟨j, hj⟩, c)
  return out

private def buildProblem (rows : Array LinExpr) (obj : LinExpr)
    (vars : Array FVarId) : Problem rows.size vars.size :=
  let rowBounds := rows.map fun r => (none, some (-r.const))
  { c := Vector.ofFn fun j => coeffAt obj vars[j]
    objOffset := obj.const
    a := mkEntries rows vars
    rowBounds := ⟨rowBounds, by simp [rowBounds]⟩
    colBounds := Vector.replicate vars.size (none, none) }

private def ratList (xs : Array Rat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map (toString ·)) ++ "]"

private def checkEntailed (rows : Array LinExpr) (obj : LinExpr) (strict : Bool)
    (vars : Array FVarId) : MetaM Unit := do
  let p := buildProblem rows obj vars
  let opts : Options := { ({} : Options) with sense := .maximize, presolve := false }
  match solveVerified opts p with
  | .error e =>
      throwError "lp: solveVerified failed: {repr e}"
  | .ok r =>
      match r.verified with
      | .optimal x _ =>
          let m := primalObj r.normalized x.toArray
          if strict then
            unless decide (m < 0) do
              throwError "lp: goal is not entailed; verified optimum is {m}, not < 0"
          else
            unless decide (m ≤ 0) do
              throwError "lp: goal is not entailed; verified optimum is {m}, not ≤ 0"
      | .infeasible _ =>
          return ()
      | .unbounded x ray _ =>
          throwError "lp: objective is unbounded above; base={ratList x.toArray}, ray={ratList ray.toArray}"
      | .unchecked status =>
          throwError "lp: solver outcome was unchecked: {repr status}"

private def solveAtomic (g : MVarId) : TacticM Unit := do
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let ((parsed?, rows), st) ← (do
      let p ← parseAtomic? target
      let hs ← collectHyps
      pure (p, hs)).run {}
    let some (rel, lhs, rhs) := parsed?
      | throwError "lp: goal is not an atomic Rat comparison"
    match rel with
    | .le =>
        checkEntailed rows (lhs.sub rhs) false st.vars
    | .lt =>
        checkEntailed rows (lhs.sub rhs) true st.vars
    | .eq =>
        let d := lhs.sub rhs
        checkEntailed rows d false st.vars
        checkEntailed rows d.neg false st.vars
  throwError
    "lp: verified SoPlex entailment succeeded, but certificate proof reconstruction is not implemented yet; refusing to close the goal with another arithmetic tactic"

private partial def solveGoal (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  g.withContext do
    let target ← whnfR (← g.getType)
    if isAnd? target |>.isSome then
      replaceMainGoal [g]
      evalTactic (← `(tactic| constructor))
      let goals ← getGoals
      for subgoal in goals do
        solveGoal subgoal
    else
      solveAtomic g

elab "lp" : tactic => do
  let goals ← getGoals
  match goals with
  | [] => throwError "lp: no goals"
  | g :: rest =>
      setGoals [g]
      solveGoal g
      let newGoals ← getGoals
      setGoals (newGoals ++ rest)

end Soplex.Tactic.LP
