/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import Lean
import LeanBound.Discovery.Find
import LeanBound.Meta.ToExpr
import LeanBound.Meta.ProveSupported
import LeanBound.Meta.ProveContinuous
import LeanBound.Tactic.IntervalAuto
import LeanBound.Numerics.Optimization.Global
import LeanBound.Numerics.Certificate

/-!
# Discovery Mode: Tactics

This module provides tactics for automatically proving existential goals
using discovery algorithms:

* `interval_minimize` - Prove `∃ m, ∀ x ∈ I, f(x) ≥ m` by finding the minimum
* `interval_maximize` - Prove `∃ M, ∀ x ∈ I, f(x) ≤ M` by finding the maximum
* `interval_roots` - Prove `∃ x ∈ I, f(x) = 0` by finding roots (Stub)

## Usage

```lean
-- Automatically find and prove a lower bound exists
example : ∃ m : ℚ, ∀ x ∈ I01, x^2 + Real.sin x ≥ m := by
  interval_minimize

-- Find a root (Not fully implemented yet)
example : ∃ x ∈ Icc (-2 : ℝ) 2, x^3 - x = 0 := by
  interval_roots
```

## Implementation

The tactics:
1. Analyze the goal to find the function `f` and interval `I`.
2. Reify `f` to a LeanBound AST.
3. Execute the optimization algorithm (via `evalExpr`) to find the bound `m`.
4. Instantiate the existential `∃ m` with the found value.
5. Call `opt_bound` to prove the resulting universal bound.
-/

open Lean Meta Elab Tactic Term
open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Optimization
open LeanBound.Meta
open LeanBound.Discovery

namespace LeanBound.Tactic.Discovery

-- Use explicit alias to avoid ambiguity with Lean.Expr
abbrev LExpr := LeanBound.Core.Expr

/-! ## Helper Functions -/

/-- Parse a domain expression into a Box -/
unsafe def parseDomainToBox (domainExpr : Lean.Expr) : MetaM Box := do
  -- This is a simplified parser. In a real implementation, this would
  -- need to evaluate the domainExpr to a Box value.
  -- For now, we assume domainExpr is an identifier or simple term
  -- that evaluates to an IntervalRat or Box.
  -- Since we need the value at runtime to pass to globalMinimize,
  -- we rely on the user providing a term that evaluates to Box or IntervalRat.
  -- Here we handle the case where it's a single IntervalRat.
  let e ← evalExpr IntervalRat (mkConst ``IntervalRat) domainExpr
  return [e]

/-- Check if the goal is an existential bound: `∃ m, ∀ x ∈ I, f(x) ≥ m` or `≤ m` -/
inductive ExistentialBoundGoal where
  | minimize (varName : Name) (domain : Lean.Expr) (func : Lean.Expr)
  | maximize (varName : Name) (domain : Lean.Expr) (func : Lean.Expr)

def parseExistentialGoal (goalType : Lean.Expr) : MetaM (Option ExistentialBoundGoal) := do
  if let .app (.app (.const ``Exists _) _) body := goalType then
    -- body is `fun m => ∀ x ∈ I, ...`
    if let .lam mName mTy mBody _ := body then
      -- Introduce m as a local variable to properly resolve bound variables
      withLocalDeclD mName mTy fun m => do
        let mBodyInst := mBody.instantiate1 m
        -- Analyze mBodyInst: `∀ x ∈ I, f(x) ≥ m` (minimize) or `f(x) ≤ m` (maximize)
        -- We reuse parseBoundGoal from IntervalAuto logic roughly
        if let some boundGoal ← LeanBound.Tactic.Auto.parseBoundGoal mBodyInst then
          match boundGoal with
          | .forallGe _name intervalInfo func bound =>
             -- c ≤ f(x) where c is m (the fvar we introduced)
             -- The bound might be a coercion of m, so check if it contains m
             let boundContainsM := bound.containsFVar m.fvarId!
             if boundContainsM then
               return some (.minimize _name intervalInfo.intervalRat func)
             else return none
          | .forallLe _name intervalInfo func bound =>
             -- f(x) ≤ c where c is m
             let boundContainsM := bound.containsFVar m.fvarId!
             if boundContainsM then
               return some (.maximize _name intervalInfo.intervalRat func)
             else return none
          | _ => return none
        else return none
    else return none
  else return none

/-! ## Helper Functions -/

/-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
def getAstFromFunc (func : Lean.Expr) : TacticM Lean.Expr := do
  -- func is (fun x => body) where body might be Expr.eval or a raw expression
  lambdaTelescope func fun _vars body => do
    -- Check if body is an Expr.eval application
    let fn := body.getAppFn
    if fn.isConstOf ``LeanBound.Core.Expr.eval then
      -- It's Expr.eval env ast - extract the ast
      let args := body.getAppArgs
      -- Expr.eval takes: (env : Nat → ℝ) → Expr → ℝ
      -- So args[0] is env, args[1] is ast
      if args.size ≥ 2 then
        return args[1]!
      else
        throwError "Unexpected Expr.eval application structure"
    else
      -- It's a raw expression - reify it
      reify func

/-! ## Minimization Tactic -/

/-- The interval_minimize tactic implementation -/
unsafe def intervalMinimizeCore (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.minimize _varName domainExpr funcExpr) ← parseExistentialGoal goalType
    | throwError "interval_minimize: Goal must be of form `∃ m, ∀ x ∈ I, f(x) ≥ m`"

  -- Debug: show what we're trying to reify
  trace[LeanBound.tactic] "funcExpr = {funcExpr}"

  -- 1. Reify the function (or extract from Expr.eval)
  -- The function might be a lambda (fun x => Expr.eval (fun _ => x) ast)
  -- In that case, we need to extract the AST from the Expr.eval application
  let ast ← getAstFromFunc funcExpr
  trace[LeanBound.tactic] "ast = {ast}"

  -- 2. Prepare for evaluation
  -- We need to evaluate the globalMinimizeCore function
  -- We construct the expression `globalMinimizeCore ast [domain] cfg`
  let cfg : GlobalOptConfig := {
    maxIterations := 1000,
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true
  }

  -- Note: safely evaluating the domain expression from syntax to a value
  -- requires `evalExpr`. We assume domainExpr evaluates to IntervalRat.
  let domainVal ← evalExpr IntervalRat (mkConst ``IntervalRat) domainExpr
  let boxVal : Box := [domainVal]

  -- 3. Run optimization
  let astVal ← evalExpr LExpr (mkConst ``LeanBound.Core.Expr) ast
  let result := globalMinimizeCore astVal boxVal cfg
  let boundVal := result.bound.lo

  -- 4. Provide witness and prove the bound
  -- Use `exact` with the witness wrapped in Exists.intro
  -- First construct the goal with the specific witness
  let boundRatExpr := toExpr boundVal

  -- Use refine to provide the witness
  let boundSyntax ← Term.exprToSyntax boundRatExpr
  evalTactic (← `(tactic| refine ⟨$boundSyntax:term, ?_⟩))

  -- 5. Now we have a goal `∀ x ∈ I, f(x) ≥ bound`
  -- Use intervalBoundCore which handles 1D goals properly
  LeanBound.Tactic.Auto.intervalBoundCore taylorDepth

/-- The interval_minimize tactic.

Proves goals of the form `∃ m, ∀ x ∈ I, f(x) ≥ m` by:
1. Running global optimization to find the minimum `m`.
2. Instantiating the existential with `m`.
3. Proving the bound using `opt_bound`.
-/
syntax (name := intervalMinimizeTac) "interval_minimize" (num)? : tactic

@[tactic intervalMinimizeTac]
unsafe def elabIntervalMinimize : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalMinimizeCore depth

/-! ## Maximization Tactic -/

/-- The interval_maximize tactic implementation -/
unsafe def intervalMaximizeCore (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.maximize _varName domainExpr funcExpr) ← parseExistentialGoal goalType
    | throwError "interval_maximize: Goal must be of form `∃ M, ∀ x ∈ I, f(x) ≤ M`"

  -- Use getAstFromFunc to handle both Expr.eval and raw expressions
  let ast ← getAstFromFunc funcExpr
  let cfg : GlobalOptConfig := {
    maxIterations := 1000,
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true
  }

  let domainVal ← evalExpr IntervalRat (mkConst ``IntervalRat) domainExpr
  let boxVal : Box := [domainVal]
  let astVal ← evalExpr LExpr (mkConst ``LeanBound.Core.Expr) ast

  let result := globalMaximizeCore astVal boxVal cfg
  let boundVal := result.bound.hi
  let boundRatExpr := toExpr boundVal

  -- Use refine to provide the witness
  let boundSyntax ← Term.exprToSyntax boundRatExpr
  evalTactic (← `(tactic| refine ⟨$boundSyntax:term, ?_⟩))

  -- Now prove the bound using intervalBoundCore
  LeanBound.Tactic.Auto.intervalBoundCore taylorDepth

/-- The interval_maximize tactic.

Proves goals of the form `∃ M, ∀ x ∈ I, f(x) ≤ M`.
-/
syntax (name := intervalMaximizeTac) "interval_maximize" (num)? : tactic

@[tactic intervalMaximizeTac]
unsafe def elabIntervalMaximize : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalMaximizeCore depth

/-! ## Roots Tactic -/

/-- Result of analyzing a root existence goal -/
inductive RootExistsGoal where
  /-- ∃ x ∈ I, f x = 0 -/
  | existsRoot (varName : Name) (interval : Lean.Expr) (func : Lean.Expr)
  deriving Repr

/-- Try to parse a goal as a root existence goal: ∃ x ∈ I, f(x) = 0 -/
def parseRootExistsGoal (goal : Lean.Expr) : MetaM (Option RootExistsGoal) := do
  let goal ← whnf goal
  -- Check for ∃ x, x ∈ I ∧ f x = 0
  -- Mathlib notation ∃ x ∈ I, P x expands to ∃ x, x ∈ I ∧ P x
  match_expr goal with
  | Exists _ body =>
    -- body is `fun x => x ∈ I ∧ f x = 0`
    if let .lam name ty innerBody _ := body then
      withLocalDeclD name ty fun x => do
        let bodyInst := innerBody.instantiate1 x
        let bodyInst ← whnf bodyInst
        -- bodyInst should be x ∈ I ∧ f x = 0
        match_expr bodyInst with
        | And memExpr eqExpr =>
          -- Extract interval from membership
          let interval? ← extractInterval memExpr x
          let some interval := interval? | return none
          -- Extract function from equality f(x) = 0
          let func? ← extractFuncFromEqZero eqExpr x
          let some func := func? | return none
          return some (.existsRoot name interval func)
        | _ => return none
    else return none
  | _ => return none
where
  /-- Extract the interval from a membership expression x ∈ I -/
  extractInterval (memExpr : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memExpr with
    | Membership.mem _ _ _ interval xExpr =>
      if ← isDefEq xExpr x then return some interval else return none
    | _ => return none

  /-- Extract function from f(x) = 0 -/
  extractFuncFromEqZero (eqExpr : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr eqExpr with
    | Eq _ lhs rhs =>
      -- Check if rhs is 0 by constructing (0 : ℝ) and checking definitional equality
      let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
      let rhs ← whnf rhs
      let isZero ← isDefEq rhs zero
      if !isZero then return none
      -- lhs should contain x
      if lhs.containsFVar x.fvarId! then
        return some (← mkLambdaFVars #[x] lhs)
      else
        return none
    | _ => return none

/-- The interval_roots tactic implementation -/
def intervalRootsCore (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- 1. Parse the goal
  let some (.existsRoot _varName interval func) ← parseRootExistsGoal goalType
    | throwError "interval_roots: Goal must be of form `∃ x ∈ I, f(x) = 0`"

  goal.withContext do
    -- 2. Get AST (either from Expr.eval or by reifying)
    let ast ← getAstFromFunc func

    -- 3. Generate ExprSupportedCore proof
    let supportProof ← mkSupportedCoreProof ast

    -- 4. Generate ContinuousOn proof
    let contProof ← mkContinuousOnProof ast interval

    -- 5. Build config expression
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    -- 6. Apply verify_sign_change theorem
    -- verify_sign_change : ExprSupportedCore e → ContinuousOn ... → checkSignChange e I cfg = true → ∃ x ∈ I, f(x) = 0
    let proof ← mkAppM ``LeanBound.Numerics.Certificate.RootFinding.verify_sign_change
      #[ast, supportProof, interval, cfgExpr, contProof]

    -- 7. Apply the proof - this leaves the certificate check as a goal
    let newGoals ← goal.apply proof
    setGoals newGoals

    -- 8. Solve remaining goals with native_decide
    for g in newGoals do
      setGoals [g]
      evalTactic (← `(tactic| native_decide))

/-- The interval_roots tactic.

Proves goals of the form `∃ x ∈ I, f(x) = 0` by:
1. Checking for a sign change at the interval endpoints using interval arithmetic
2. Applying the Intermediate Value Theorem

The tactic automatically:
- Reifies the function to a LeanBound AST
- Generates an `ExprSupportedCore` proof
- Generates a `ContinuousOn` proof (automatic for supported expressions)
- Verifies the sign change certificate using `native_decide`

**Usage:**
```lean
example : ∃ x ∈ Icc (0 : ℝ) 2, x^2 - 2 = 0 := by
  interval_roots
```

**Limitations:**
- Only works for expressions in `ExprSupportedCore` (no `log`, `inv`)
- Requires a sign change at the endpoints (IVT condition)
- If there's no sign change, the tactic will fail
-/
elab "interval_roots" depth:(num)? : tactic => do
  let taylorDepth := match depth with
    | some n => n.getNat
    | none => 10
  intervalRootsCore taylorDepth

/-! ## Unique Root Tactic -/

/-- Parse a unique root goal: ∃! x, x ∈ I ∧ f(x) = 0 -/
def parseUniqueRootGoal (goalType : Lean.Expr) : MetaM (Option (Name × Lean.Expr × Lean.Expr)) := do
  -- Match: ∃! x, P x where P x = (x ∈ I ∧ f(x) = 0)
  -- NOTE: Don't call whnf before matching ExistsUnique - it would expand to Exists!
  match_expr goalType with
  | ExistsUnique _ body =>
    -- body is `fun x => x ∈ I ∧ f x = 0`
    if let .lam name ty innerBody _ := body then
      withLocalDeclD name ty fun x => do
        let bodyInst := innerBody.instantiate1 x
        let bodyInst ← whnf bodyInst
        -- bodyInst should be x ∈ I ∧ f x = 0
        match_expr bodyInst with
        | And memExpr eqExpr =>
          -- Extract interval from membership (use pattern matching)
          let some interval := ← (do
            match_expr memExpr with
            | Membership.mem _ _ _ interval xExpr =>
              if ← isDefEq xExpr x then return some interval else return none
            | _ => return none) | return none
          -- Extract function from equality
          let some func := ← (do
            match_expr eqExpr with
            | Eq _ lhs rhs =>
              let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
              let rhs ← whnf rhs
              let isZero ← isDefEq rhs zero
              if !isZero then return none
              if lhs.containsFVar x.fvarId! then
                return some (← mkLambdaFVars #[x] lhs)
              else
                return none
            | _ => return none) | return none
          return some (name, interval, func)
        | _ => return none
    else return none
  | _ => return none

/-- Core implementation for interval_unique_root tactic.

    Proves `∃! x ∈ I, f(x) = 0` by:
    1. Checking Newton contraction (derivative bounded away from 0)
    2. Applying verify_unique_root_core theorem

    The new signature requires both checkNewtonContractsCore (computable) and
    checkNewtonContracts (noncomputable) proofs. We use native_decide for the
    computable check and decide for the noncomputable one.
-/
unsafe def intervalUniqueRootCore (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse goal: ∃! x, x ∈ I ∧ f(x) = 0
  let some (_varName, interval, func) ← parseUniqueRootGoal goalType
    | throwError "interval_unique_root: Goal must be of form `∃! x, x ∈ I ∧ f(x) = 0`"

  -- Extract AST
  let ast ← getAstFromFunc func

  -- Generate ExprSupportedCore proof
  let supportProof ← mkSupportedCoreProof ast

  -- Generate UsesOnlyVar0 proof
  let var0Proof ← mkUsesOnlyVar0Proof ast

  -- Generate ContinuousOn proof
  let contProof ← LeanBound.Meta.mkContinuousOnProof ast interval

  -- Build EvalConfig (for core check)
  let evalCfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

  -- Build NewtonConfig (default)
  let newtonCfgExpr ← mkAppM ``Certificate.RootFinding.NewtonConfig.mk #[toExpr (5 : Nat), toExpr (1 : Nat)]

  -- Apply verify_unique_root_core with both configs
  -- Args: e, hsupp, hvar0, I, evalCfg, newtonCfg, hCont
  let proof ← mkAppM ``Certificate.RootFinding.verify_unique_root_core
    #[ast, supportProof, var0Proof, interval, evalCfgExpr, newtonCfgExpr, contProof]

  -- Apply the proof (leaves two certificate check goals)
  let newGoals ← goal.apply proof
  setGoals newGoals

  -- Solve certificate checks
  -- Goal 1: checkNewtonContractsCore e I evalCfg = true (computable - use native_decide)
  -- Goal 2: checkNewtonContracts e I newtonCfg = true (noncomputable - use decide)
  for g in newGoals do
    setGoals [g]
    -- Try native_decide first (works for computable), then decide
    try
      evalTactic (← `(tactic| native_decide))
    catch _ =>
      -- Fallback to decide for noncomputable checks
      evalTactic (← `(tactic| decide))

/-- The interval_unique_root tactic.

Proves goals of the form `∃! x ∈ I, f(x) = 0` by:
1. Using Newton contraction to verify uniqueness (derivative bounded away from 0)
2. Applying the Intermediate Value Theorem for existence

**Usage:**
```lean
example : ∃! x ∈ I_1_2, Expr.eval (fun _ => x) (x² - 2) = 0 := by
  interval_unique_root
```

**Requirements:**
- Function must be in `ExprSupportedCore` (no log, inv)
- Newton step must contract (derivative doesn't contain 0)
-/
syntax (name := intervalUniqueRootTac) "interval_unique_root" (num)? : tactic

@[tactic intervalUniqueRootTac]
unsafe def elabIntervalUniqueRoot : Tactic := fun stx => do
  let taylorDepth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalUniqueRootCore taylorDepth

/-! ## Integration Tactic -/

/-- Extract components from integration goal:
    ∫ x in lo..hi, f(x) ∈ bound
    returns (lo, hi, integral, bound) -/
def parseIntegrationGoal (goalType : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) := do
  -- Goal form: Membership.mem integral bound
  match_expr goalType with
  | Membership.mem _ _ _ bound integral =>
    -- integral form: intervalIntegral f μ lo hi
    if integral.getAppNumArgs >= 4 then
      let args := integral.getAppArgs
      let lo := args[2]!
      let hi := args[3]!
      return some (lo, hi, integral, bound)
    else
      return none
  | _ =>
    return none

/-- Core implementation for interval_integrate tactic.

Proves goals of the form `∫ x in (I.lo)...(I.hi), f(x) ∈ bound` by:
1. Computing the integral bound using interval arithmetic
2. Proving the computed bound contains the integral

The goal must be exactly of the form:
  ∫ x in (I.lo:ℝ)..(I.hi:ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg
-/
unsafe def intervalIntegrateCore (_taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse the goal to extract the bound expression
  let some (_lo, _hi, _integral, bound) ← parseIntegrationGoal goalType
    | throwError "interval_integrate: Could not parse goal. Expected form: ∫ x in lo..hi, f(x) ∈ bound"

  -- The bound should be: Certificate.Integration.integrateInterval1Core e I cfg
  -- Extract e, I, cfg from it
  if !bound.isAppOfArity ``Certificate.Integration.integrateInterval1Core 3 then
    throwError "interval_integrate: Bound must be of form `Certificate.Integration.integrateInterval1Core e I cfg`"

  let args := bound.getAppArgs
  let ast := args[0]!
  let interval := args[1]!
  let cfg := args[2]!

  -- Generate ExprSupportedCore proof for the AST
  let supportProof ← mkSupportedCoreProof ast

  -- Build the proof term: integrateInterval1Core_correct e supportProof I cfg
  let proof ← mkAppM ``Certificate.Integration.integrateInterval1Core_correct
    #[ast, supportProof, interval, cfg]

  -- Assign the proof
  goal.assign proof

/-- The interval_integrate tactic.

Proves goals of the form `∫ x in (I.lo)...(I.hi), f(x) ∈ bound` by:
1. Computing the integral bound using interval arithmetic
2. Applying the integrateInterval1Core_correct theorem

**Usage:**
```lean
example : ∫ x in (0:ℝ)..1, x ∈ Certificate.Integration.integrateInterval1Core (Expr.var 0) ⟨0, 1, by norm_num⟩ {} := by
  interval_integrate
```

**Limitations:**
- The bound must exactly match `integrateInterval1Core e I cfg`
- The function must be in `ExprSupportedCore` (no log, inv)
-/
syntax (name := intervalIntegrateTac) "interval_integrate" (num)? : tactic

@[tactic intervalIntegrateTac]
unsafe def elabIntervalIntegrate : Tactic := fun stx => do
  let taylorDepth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalIntegrateCore taylorDepth

/-! ## Discover Tactic -/

/-- The discover tactic - generic discovery.

Analyzes the goal and applies the appropriate discovery tactic.
-/
syntax (name := discoverTac) "discover" (num)? : tactic

@[tactic discoverTac]
unsafe def elabDiscover : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  let goal ← getMainGoal
  let goalType ← goal.getType

  if let some goalKind ← parseExistentialGoal goalType then
    match goalKind with
    | .minimize .. => intervalMinimizeCore depth
    | .maximize .. => intervalMaximizeCore depth
  else
    throwError "discover: Goal not recognized. Supported forms:\n\
                - ∃ m, ∀ x ∈ I, f(x) ≥ m\n\
                - ∃ M, ∀ x ∈ I, f(x) ≤ M"

/-! ## Exploration Command -/

/-- Syntax for signed integer: either a nat or -nat -/
declare_syntax_cat signedInt
syntax num : signedInt
syntax "-" num : signedInt

/-- Parse a signedInt syntax to Int -/
def parseSignedInt : Syntax → Int
  | `(signedInt| $n:num) => n.getNat
  | `(signedInt| -$n:num) => -(n.getNat : Int)
  | _ => 0

open Lean.Elab.Command in
/-- The `#explore` command analyzes a function on an interval.

Usage:
```lean
#explore (Expr.sin (Expr.var 0)) on [0, 7]
#explore (Expr.cos (Expr.var 0)) on [-1, 2]
```

Output includes:
- Range bounds
- Global minimum/maximum
- Root detection (sign changes)

Note: Bounds must be integer literals (positive or negative).
-/
elab "#explore " e:term " on " "[" lo:signedInt ", " hi:signedInt "]" : command => do
  liftTermElabM do
    -- Elaborate the expression
    let exprE ← elabTerm e (some (mkConst ``LeanBound.Core.Expr))
    let exprE ← instantiateMVars exprE

    -- Parse bounds as integers from syntax
    let loInt := parseSignedInt lo
    let hiInt := parseSignedInt hi
    let loVal : ℚ := loInt
    let hiVal : ℚ := hiInt

    -- Evaluate to get the actual values
    let astVal ← unsafe evalExpr LExpr (mkConst ``LeanBound.Core.Expr) exprE

    -- Check bounds are valid
    if h : loVal ≤ hiVal then
      let intervalVal : IntervalRat := ⟨loVal, hiVal, h⟩

      let cfg : GlobalOptConfig := {
        maxIterations := 1000,
        tolerance := 1/1000,
        taylorDepth := 10,
        useMonotonicity := true
      }
      let box : Box := [intervalVal]

      -- Compute range (min and max)
      let minResult := globalMinimizeCore astVal box cfg
      let maxResult := globalMaximizeCore astVal box cfg

      -- Check for sign change (root detection)
      let evalCfg : EvalConfig := { taylorDepth := 10 }
      let hasSignChange := Certificate.RootFinding.checkSignChange astVal intervalVal evalCfg

      -- Format output
      let minStr := s!"{minResult.bound.lo}"
      let maxStr := s!"{maxResult.bound.hi}"

      logInfo m!"=== Function Analysis ===\n\
                 Expression: {exprE}\n\
                 Domain: [{loVal}, {hiVal}]\n\
                 \n\
                 Range: [{minStr}, {maxStr}]\n\
                 Global minimum: ≥ {minStr}\n\
                 Global maximum: ≤ {maxStr}\n\
                 \n\
                 Sign change detected: {hasSignChange}\n\
                 (If true, a root exists by IVT)"
    else
      throwError "#explore: Invalid interval: lo ({loVal}) must be ≤ hi ({hiVal})"

end LeanBound.Tactic.Discovery
