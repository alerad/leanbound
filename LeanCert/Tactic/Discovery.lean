/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Discovery.Find
import LeanCert.Meta.ToExpr
import LeanCert.Meta.ProveSupported
import LeanCert.Meta.ProveContinuous
import LeanCert.Tactic.IntervalAuto
import LeanCert.Engine.Optimization.Global
import LeanCert.Engine.Optimization.Guided
import LeanCert.Engine.Optimization.Gradient
import LeanCert.Validity.Bounds

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
2. Reify `f` to a LeanCert AST.
3. Execute the optimization algorithm (via `evalExpr`) to find the bound `m`.
4. Instantiate the existential `∃ m` with the found value.
5. Call `opt_bound` to prove the resulting universal bound.
-/

open Lean Meta Elab Tactic Term
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization
open LeanCert.Meta
open LeanCert.Discovery

namespace LeanCert.Tactic.Discovery

-- Trace class for discovery mode diagnostics
initialize registerTraceClass `LeanCert.discovery

-- Use explicit alias to avoid ambiguity with Lean.Expr
abbrev LExpr := LeanCert.Core.Expr

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
  | minimize (varName : Name) (varType : Lean.Expr) (domain : Lean.Expr) (func : Lean.Expr)
  | maximize (varName : Name) (varType : Lean.Expr) (domain : Lean.Expr) (func : Lean.Expr)

/-- Parse an existential bound goal.
    Supports goals of the form:
    - `∃ m, ∀ x ∈ I, f(x) ≥ m` (minimize)
    - `∃ M, ∀ x ∈ I, f(x) ≤ M` (maximize)

    The function f can be:
    - A raw Lean expression like `x * x + Real.sin x`
    - An `Expr.eval` wrapped expression

    Auto-reification will convert raw expressions to LeanCert AST. -/
def parseExistentialGoal (goalType : Lean.Expr) : MetaM (Option ExistentialBoundGoal) := do
  -- Try to match the Exists pattern
  let goalType ← whnf goalType
  if let .app (.app (.const ``Exists _) _) body := goalType then
    -- body is `fun m => ∀ x ∈ I, ...`
    if let .lam mName mTy mBody _ := body then
      -- Introduce m as a local variable to properly resolve bound variables
      withLocalDeclD mName mTy fun m => do
        let mBodyInst := mBody.instantiate1 m
        -- Analyze mBodyInst: `∀ x ∈ I, f(x) ≥ m` (minimize) or `f(x) ≤ m` (maximize)
        -- We reuse parseBoundGoal from IntervalAuto logic roughly
        if let some boundGoal ← LeanCert.Tactic.Auto.parseBoundGoal mBodyInst then
          match boundGoal with
          | .forallGe _name intervalInfo func bound =>
             -- c ≤ f(x) where c is m (the fvar we introduced)
             -- The bound might be a coercion of m, so check if it contains m
             let boundContainsM := bound.containsFVar m.fvarId!
             if boundContainsM then
               return some (.minimize _name mTy intervalInfo.intervalRat func)
             else return none
          | .forallLe _name intervalInfo func bound =>
             -- f(x) ≤ c where c is m
             let boundContainsM := bound.containsFVar m.fvarId!
             if boundContainsM then
               return some (.maximize _name mTy intervalInfo.intervalRat func)
             else return none
          | _ => return none
        else return none
    else return none
  else return none

/-! ## Helper Functions -/

/-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression.
    This enables automatic reification - users can write standard math like `x * x + sin x`
    without needing to wrap in `Expr.eval`. -/
def getAstFromFunc (func : Lean.Expr) : TacticM Lean.Expr := do
  -- func is (fun x => body) where body might be Expr.eval or a raw expression
  lambdaTelescope func fun _vars body => do
    -- Check if body is an Expr.eval application
    let fn := body.getAppFn
    if fn.isConstOf ``LeanCert.Core.Expr.eval then
      -- It's Expr.eval env ast - extract the ast
      let args := body.getAppArgs
      -- Expr.eval takes: (env : Nat → ℝ) → Expr → ℝ
      -- So args[0] is env, args[1] is ast
      if args.size ≥ 2 then
        trace[LeanCert.discovery] "Extracted AST from Expr.eval wrapper"
        return args[1]!
      else
        throwError "Unexpected Expr.eval application structure"
    else
      -- It's a raw expression - reify it automatically
      trace[LeanCert.discovery] "Auto-reifying raw expression: {body}"
      try
        let ast ← reify func
        trace[LeanCert.discovery] "Reification successful"
        return ast
      catch e =>
        throwError m!"Failed to reify expression to LeanCert AST.\n\
                      Expression: {body}\n\n\
                      Error: {e.toMessageData}\n\n\
                      Supported operations: +, -, *, /, sin, cos, exp, log, sqrt, π, ...\n\
                      Tip: Unfold custom definitions with 'simp only [myDef]' first."

/-! ### Domain normalization helpers -/

private def extractNatLit (e : Lean.Expr) : MetaM (Option ℕ) := do
  if let some n := e.rawNatLit? then
    return some n
  let e ← whnf e
  if let some n := e.rawNatLit? then
    return some n
  else return none

private def extractIntLit (e : Lean.Expr) : MetaM (Option ℤ) := do
  let e ← whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Int.ofNat then
    if args.size > 0 then
      if let some n ← extractNatLit args[0]! then
        return some (n : ℤ)
    return none
  else if fn.isConstOf ``Int.negSucc then
    if args.size > 0 then
      if let some n ← extractNatLit args[0]! then
        return some (-(n + 1 : ℤ))
    return none
  else
    return none

private def extractRatFromRat (e : Lean.Expr) : MetaM (Option ℚ) := do
  -- Try without whnf first (preserves OfNat.ofNat structure)
  if let some q ← tryExtractRat e then
    return some q
  -- Then try with whnf
  let e' ← whnf e
  tryExtractRat e'
where
  tryExtractRat (e : Lean.Expr) : MetaM (Option ℚ) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Rat.ofInt then
      if args.size > 0 then
        if let some i ← extractIntLit args[0]! then
          return some (i : ℚ)
      return none
    else if fn.isConstOf ``OfNat.ofNat then
      if args.size >= 2 then
        if let some n ← extractNatLit args[1]! then
          return some (n : ℚ)
      return none
    -- Check for Nat.cast to ℚ (handles ↑1, ↑2, etc.)
    else if fn.isConstOf ``Nat.cast || fn.isConstOf ``NatCast.natCast then
      if args.size > 0 then
        if let some n ← extractNatLit args.back! then
          return some (n : ℚ)
      return none
    -- Check for Int.cast to ℚ
    else if fn.isConstOf ``Int.cast || fn.isConstOf ``IntCast.intCast then
      if args.size > 0 then
        if let some i ← extractIntLit args.back! then
          return some (i : ℚ)
      return none
    else if fn.isConstOf ``Rat.mk' then
      return none
    else
      return none

/-- Try to extract a rational value from a Lean expression that represents a real number.
    Handles: Rat.cast, OfNat.ofNat, Nat.cast, Int.cast, negations, and divisions.
    Also handles direct ℚ expressions as a fallback. -/
partial def extractRatFromReal (e : Lean.Expr) : MetaM (Option ℚ) := do
  -- First try without whnf (preserves structure like OfNat.ofNat)
  if let some q ← tryExtract e then
    return some q
  -- Then try with whnf
  let e' ← whnf e
  if let some q ← tryExtract e' then
    return some q
  -- Finally, try extracting from ℚ directly (for goals like ∀ x ∈ I, f(x) ≤ (1 : ℚ))
  extractRatFromRat e'
where
  tryExtract (e : Lean.Expr) : MetaM (Option ℚ) := do
    let fn := e.getAppFn
    let args := e.getAppArgs

    -- Case 1: Rat.cast q or RatCast.ratCast q
    if fn.isConstOf ``Rat.cast || fn.isConstOf ``RatCast.ratCast then
      if args.size > 0 then
        return ← extractRatFromRat args.back!
      else return none

    -- Case 2: OfNat.ofNat (for numeric literals like 2 : ℝ)
    else if fn.isConstOf ``OfNat.ofNat then
      if args.size >= 2 then
        if let some n ← extractNatLit args[1]! then
          return some (n : ℚ)
      return none

    -- Case 3: Nat.cast n
    else if fn.isConstOf ``Nat.cast || fn.isConstOf ``NatCast.natCast then
      if args.size > 0 then
        if let some n ← extractNatLit args.back! then
          return some (n : ℚ)
      return none

    -- Case 4: Int.cast i
    else if fn.isConstOf ``Int.cast || fn.isConstOf ``IntCast.intCast then
      if args.size > 0 then
        if let some i ← extractIntLit args.back! then
          return some (i : ℚ)
      return none

    -- Case 5: Neg.neg x (for negative numbers)
    else if fn.isConstOf ``Neg.neg then
      if args.size > 0 then
        if let some q ← extractRatFromReal args.back! then
          return some (-q)
      return none

    -- Case 6: HDiv.hDiv a b (for fractions like 1/2)
    else if fn.isConstOf ``HDiv.hDiv then
      if args.size >= 6 then
        if let some a ← extractRatFromReal args[4]! then
          if let some b ← extractRatFromReal args[5]! then
            if b ≠ 0 then
              return some (a / b)
      return none

    -- Case 7: OfScientific.ofScientific (for decimal literals like 2.72)
    else if fn.isConstOf ``OfScientific.ofScientific then
      if args.size >= 5 then
        if let some mantissa ← extractNatLit args[2]! then
          let isNegExp := args[3]!.isConstOf ``Bool.true
          if let some exp ← extractNatLit args[4]! then
            let base : ℚ := 10
            if isNegExp then
              return some ((mantissa : ℚ) / (base ^ exp))
            else
              return some ((mantissa : ℚ) * (base ^ exp))
      return none

    else
      return none

private def tryConvertSetIcc (interval : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``LE.le && args.size >= 4 then
      return some (args[2]!, args[3]!)
    return none

  let extractLowerBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq b x then
        return some a
    return none

  let extractUpperBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq a x then
        return some b
    return none

  let parseSetIccBounds (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Set.Icc && args.size >= 4 then
      return some (args[2]!, args[3]!)
    return none

  let parseSetIccLambda (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match e with
    | Lean.Expr.lam name ty body _ =>
      withLocalDeclD name ty fun x => do
        let bodyInst := body.instantiate1 x
        let fn := bodyInst.getAppFn
        let args := bodyInst.getAppArgs
        if fn.isConstOf ``And && args.size >= 2 then
          let left := args[0]!
          let right := args[1]!
          if let some lo ← extractLowerBound left x then
            if let some hi ← extractUpperBound right x then
              return some (lo, hi)
          if let some lo ← extractLowerBound right x then
            if let some hi ← extractUpperBound left x then
              return some (lo, hi)
        return none
    | _ => return none

  let parseBounds (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    if let some bounds ← parseSetIccBounds e then
      return some bounds
    parseSetIccLambda e

  let mkIntervalRatFromBounds (loExpr hiExpr : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some lo ← extractRatFromReal loExpr then
      if let some hi ← extractRatFromReal hiExpr then
        let loRatExpr := toExpr lo
        let hiRatExpr := toExpr hi
        let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
        let leProof ← mkDecideProof leProofTy
        let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
        return some intervalRat
    return none

  if let some (loExpr, hiExpr) ← parseBounds interval then
    if let some intervalRat ← mkIntervalRatFromBounds loExpr hiExpr then
      return some intervalRat
  let intervalWhnf ← withTransparency TransparencyMode.all <| whnf interval
  if intervalWhnf == interval then
    return none
  if let some (loExpr, hiExpr) ← parseBounds intervalWhnf then
    return ← mkIntervalRatFromBounds loExpr hiExpr
  return none

/-! ## Minimization Tactic -/

/-- The interval_minimize tactic implementation -/
unsafe def intervalMinimizeCore (taylorDepth : Nat) : TacticM Unit := do
  LeanCert.Tactic.Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.minimize _varName varType domainExpr funcExpr) ← parseExistentialGoal goalType
    | let diagReport ← LeanCert.Tactic.Auto.mkDiagnosticReport "interval_minimize" goalType "parse"
        (some m!"Expected form: ∃ m, ∀ x ∈ I, f(x) ≥ m\n\n\
                 Where:\n\
                 • m is a rational bound variable\n\
                 • x is the quantified variable over interval I\n\
                 • f(x) is an expression supported by LeanCert")
      throwError "interval_minimize: Could not parse goal.\n\n{diagReport}"

  trace[LeanCert.discovery] "Parsing goal: ∃ m, ∀ x ∈ I, f(x) ≥ m"
  trace[LeanCert.discovery] "Function expression: {funcExpr}"

  -- 1. Reify the function (or extract from Expr.eval)
  let ast ← getAstFromFunc funcExpr
  trace[LeanCert.discovery] "Reified AST: {ast}"

  -- 2. Prepare for evaluation with guided optimization
  let cfg : GuidedOptConfig := {
    maxIterations := 1000,
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true,
    heuristicSamples := 200,
    seed := 12345,
    useGridSearch := true,
    gridPointsPerDim := 10
  }

  -- Note: safely evaluating the domain expression from syntax to a value
  let domainExpr ←
    match ← tryConvertSetIcc domainExpr with
    | some intervalRat => pure intervalRat
    | none => pure domainExpr
  let domainVal ← evalExpr IntervalRat (mkConst ``IntervalRat) domainExpr
  let boxVal : Box := [domainVal]
  trace[LeanCert.discovery] "Domain: [{domainVal.lo}, {domainVal.hi}]"

  -- 3. Run float-guided optimization
  trace[LeanCert.discovery] "Running float-guided optimization (heuristic samples={cfg.heuristicSamples}, maxIters={cfg.maxIterations}, taylorDepth={taylorDepth})..."
  let astVal ← evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
  let result := globalMinimizeGuided astVal boxVal cfg
  let boundVal := result.bound.lo

  trace[LeanCert.discovery] "Optimization complete: {result.bound.iterations} iterations"
  trace[LeanCert.discovery] "Found minimum bound: {boundVal}"
  trace[LeanCert.discovery] "Gap: [{result.bound.lo}, {result.bound.hi}]"

  -- Check if optimization converged well
  let gap := result.bound.hi - result.bound.lo
  if gap > cfg.tolerance then
    logWarning m!"⚠️ Optimization gap [{result.bound.lo}, {result.bound.hi}] exceeds tolerance {cfg.tolerance}.\n\
                  Consider increasing maxIterations or taylorDepth."

  -- 4. Provide witness and prove the bound
  -- Note: Coerce to ℝ since Expr.eval returns ℝ
  let boundRatExpr := toExpr boundVal
  let boundTerm ←
    match (← whnf varType) with
    | ty =>
      if ty.isConstOf ``Rat then
        pure boundRatExpr
      else if ty.isConstOf ``Real then
        mkAppOptM ``Rat.cast #[mkConst ``Real, none, boundRatExpr]
      else
        throwError "interval_minimize: Unsupported bound type. Use ℚ or ℝ."
  let boundSyntax ← Term.exprToSyntax boundTerm
  trace[LeanCert.discovery] "Providing witness: m = {boundVal}"
  evalTactic (← `(tactic| refine ⟨$boundSyntax, ?_⟩))

  -- 5. Now we have a goal `∀ x ∈ I, f(x) ≥ bound`
  trace[LeanCert.discovery] "Proving universal bound with interval_bound..."
  LeanCert.Tactic.Auto.intervalBoundCore taylorDepth
  trace[LeanCert.discovery] "✓ Proof complete"

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
  LeanCert.Tactic.Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.maximize _varName varType domainExpr funcExpr) ← parseExistentialGoal goalType
    | let diagReport ← LeanCert.Tactic.Auto.mkDiagnosticReport "interval_maximize" goalType "parse"
        (some m!"Expected form: ∃ M, ∀ x ∈ I, f(x) ≤ M\n\n\
                 Where:\n\
                 • M is a rational bound variable\n\
                 • x is the quantified variable over interval I\n\
                 • f(x) is an expression supported by LeanCert")
      throwError "interval_maximize: Could not parse goal.\n\n{diagReport}"

  trace[LeanCert.discovery] "Parsing goal: ∃ M, ∀ x ∈ I, f(x) ≤ M"
  trace[LeanCert.discovery] "Function expression: {funcExpr}"

  -- Use getAstFromFunc to handle both Expr.eval and raw expressions
  let ast ← getAstFromFunc funcExpr
  trace[LeanCert.discovery] "Reified AST: {ast}"

  let cfg : GuidedOptConfig := {
    maxIterations := 1000,
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true,
    heuristicSamples := 200,
    seed := 12345,
    useGridSearch := true,
    gridPointsPerDim := 10
  }

  let domainExpr ←
    match ← tryConvertSetIcc domainExpr with
    | some intervalRat => pure intervalRat
    | none => pure domainExpr
  let domainVal ← evalExpr IntervalRat (mkConst ``IntervalRat) domainExpr
  let boxVal : Box := [domainVal]
  trace[LeanCert.discovery] "Domain: [{domainVal.lo}, {domainVal.hi}]"

  trace[LeanCert.discovery] "Running float-guided optimization (heuristic samples={cfg.heuristicSamples}, maxIters={cfg.maxIterations}, taylorDepth={taylorDepth})..."
  let astVal ← evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
  let result := globalMaximizeGuided astVal boxVal cfg
  let boundVal := result.bound.hi

  trace[LeanCert.discovery] "Optimization complete: {result.bound.iterations} iterations"
  trace[LeanCert.discovery] "Found maximum bound: {boundVal}"
  trace[LeanCert.discovery] "Gap: [{result.bound.lo}, {result.bound.hi}]"

  -- Check if optimization converged well
  let gap := result.bound.hi - result.bound.lo
  if gap > cfg.tolerance then
    logWarning m!"⚠️ Optimization gap [{result.bound.lo}, {result.bound.hi}] exceeds tolerance {cfg.tolerance}.\n\
                  Consider increasing maxIterations or taylorDepth."

  let boundRatExpr := toExpr boundVal
  let boundTerm ←
    match (← whnf varType) with
    | ty =>
      if ty.isConstOf ``Rat then
        pure boundRatExpr
      else if ty.isConstOf ``Real then
        mkAppOptM ``Rat.cast #[mkConst ``Real, none, boundRatExpr]
      else
        throwError "interval_maximize: Unsupported bound type. Use ℚ or ℝ."
  let boundSyntax ← Term.exprToSyntax boundTerm
  trace[LeanCert.discovery] "Providing witness: M = {boundVal}"
  evalTactic (← `(tactic| refine ⟨$boundSyntax, ?_⟩))

  -- Now prove the bound using intervalBoundCore
  trace[LeanCert.discovery] "Proving universal bound with interval_bound..."
  LeanCert.Tactic.Auto.intervalBoundCore taylorDepth
  trace[LeanCert.discovery] "✓ Proof complete"

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

/-! ## Argmax/Argmin Tactics -/

/-- Result of analyzing an argmax goal -/
inductive ArgmaxGoal where
  /-- ∃ x ∈ I, ∀ y ∈ I, f(y) ≤ f(x) -/
  | argmax (varName : Name) (domain : Lean.Expr) (func : Lean.Expr)
  deriving Repr

/-- Try to parse a goal as an argmax goal: ∃ x ∈ I, ∀ y ∈ I, f(y) ≤ f(x) -/
def parseArgmaxGoal (goal : Lean.Expr) : MetaM (Option ArgmaxGoal) := do
  let goal ← whnf goal
  -- Goal: ∃ x, x ∈ I ∧ ∀ y ∈ I, f(y) ≤ f(x)
  match_expr goal with
  | Exists _ body =>
    if let .lam name ty innerBody _ := body then
      withLocalDeclD name ty fun x => do
        let bodyInst := innerBody.instantiate1 x
        let bodyInst ← whnf bodyInst
        -- bodyInst should be x ∈ I ∧ ∀ y ∈ I, f(y) ≤ f(x)
        match_expr bodyInst with
        | And memExpr forallExpr =>
          -- Extract interval from membership
          let interval? ← extractIntervalExpr memExpr x
          let some intervalExpr := interval? | return none
          -- Check if forallExpr is ∀ y ∈ I, f(y) ≤ f(x)
          let forallExpr ← whnf forallExpr
          if forallExpr.isForall then
            let .forallE yname yty forallBody _ := forallExpr | return none
            withLocalDeclD yname yty fun y => do
              let forallBody := forallBody.instantiate1 y
              let forallBody ← whnf forallBody
              -- forallBody should be y ∈ I → f(y) ≤ f(x)
              if forallBody.isForall then
                let .forallE _ _memTy compBody _ := forallBody | return none
                -- compBody should be f(y) ≤ f(x) (with y free, x from outer scope)
                match_expr compBody with
                | LE.le _ _ lhs _rhs =>
                  -- lhs is f(y), we extract the function structure
                  -- The function is fun z => (lhs with y replaced by z)
                  let func ← mkLambdaFVars #[y] lhs
                  return some (.argmax name intervalExpr func)
                | _ => return none
              else return none
          else return none
        | _ => return none
    else return none
  | _ => return none
where
  /-- Extract the interval from a membership expression x ∈ I -/
  extractIntervalExpr (memExpr : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memExpr with
    | Membership.mem _ _ _ interval xExpr =>
      if ← isDefEq xExpr x then return some interval else return none
    | _ => return none

/-- Result of analyzing an argmin goal -/
inductive ArgminGoal where
  /-- ∃ x ∈ I, ∀ y ∈ I, f(x) ≤ f(y) -/
  | argmin (varName : Name) (domain : Lean.Expr) (func : Lean.Expr)
  deriving Repr

/-- Try to parse a goal as an argmin goal: ∃ x ∈ I, ∀ y ∈ I, f(x) ≤ f(y) -/
def parseArgminGoal (goal : Lean.Expr) : MetaM (Option ArgminGoal) := do
  let goal ← whnf goal
  -- Goal: ∃ x, x ∈ I ∧ ∀ y ∈ I, f(x) ≤ f(y)
  match_expr goal with
  | Exists _ body =>
    if let .lam name ty innerBody _ := body then
      withLocalDeclD name ty fun x => do
        let bodyInst := innerBody.instantiate1 x
        let bodyInst ← whnf bodyInst
        -- bodyInst should be x ∈ I ∧ ∀ y ∈ I, f(x) ≤ f(y)
        match_expr bodyInst with
        | And memExpr forallExpr =>
          -- Extract interval from membership
          let interval? ← extractIntervalExpr memExpr x
          let some intervalExpr := interval? | return none
          -- Check if forallExpr is ∀ y ∈ I, f(x) ≤ f(y)
          let forallExpr ← whnf forallExpr
          if forallExpr.isForall then
            let .forallE yname yty forallBody _ := forallExpr | return none
            withLocalDeclD yname yty fun y => do
              let forallBody := forallBody.instantiate1 y
              let forallBody ← whnf forallBody
              -- forallBody should be y ∈ I → f(x) ≤ f(y)
              if forallBody.isForall then
                let .forallE _ _memTy compBody _ := forallBody | return none
                -- compBody should be f(x) ≤ f(y) (with y free, x from outer scope)
                match_expr compBody with
                | LE.le _ _ _lhs rhs =>
                  -- rhs is f(y), we extract the function structure
                  -- The function is fun z => (rhs with y replaced by z)
                  let func ← mkLambdaFVars #[y] rhs
                  return some (.argmin name intervalExpr func)
                | _ => return none
              else return none
          else return none
        | _ => return none
    else return none
  | _ => return none
where
  /-- Extract the interval from a membership expression x ∈ I -/
  extractIntervalExpr (memExpr : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memExpr with
    | Membership.mem _ _ _ interval xExpr =>
      if ← isDefEq xExpr x then return some interval else return none
    | _ => return none

/-- Check if a function expression is wrapped in Expr.eval -/
def isExprEvalFunc (func : Lean.Expr) : MetaM Bool := do
  lambdaTelescope func fun _vars body => do
    let fn := body.getAppFn
    return fn.isConstOf ``LeanCert.Core.Expr.eval

/-- The interval_argmax tactic implementation -/
unsafe def intervalArgmaxCore (taylorDepth : Nat) : TacticM Unit := do
  LeanCert.Tactic.Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.argmax _varName domainExpr funcExpr) ← parseArgmaxGoal goalType
    | let diagReport ← LeanCert.Tactic.Auto.mkDiagnosticReport "interval_argmax" goalType "parse"
        (some m!"Expected form: ∃ x ∈ I, ∀ y ∈ I, f(y) ≤ f(x)\n\n\
                 This proves existence of a maximizer point x in I.")
      throwError "interval_argmax: Could not parse goal.\n\n{diagReport}"

  trace[LeanCert.discovery] "Parsing argmax goal: ∃ x ∈ I, ∀ y ∈ I, f(y) ≤ f(x)"
  trace[LeanCert.discovery] "Function expression: {funcExpr}"

  -- Check if using native syntax (not Expr.eval)
  let isNativeSyntax := !(← isExprEvalFunc funcExpr)
  trace[LeanCert.discovery] "Using native syntax: {isNativeSyntax}"

  -- 1. Reify the function
  let ast ← getAstFromFunc funcExpr
  trace[LeanCert.discovery] "Reified AST: {ast}"

  -- 2. Prepare optimization config
  let cfg : GuidedOptConfig := {
    maxIterations := 1000,
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true,
    heuristicSamples := 200,
    seed := 12345,
    useGridSearch := true,
    gridPointsPerDim := 10
  }

  let domainExpr ←
    match ← tryConvertSetIcc domainExpr with
    | some intervalRat => pure intervalRat
    | none => pure domainExpr
  let domainVal ← evalExpr IntervalRat (mkConst ``IntervalRat) domainExpr
  let boxVal : Box := [domainVal]
  trace[LeanCert.discovery] "Domain: [{domainVal.lo}, {domainVal.hi}]"

  -- 3. Run optimization to find the argmax
  trace[LeanCert.discovery] "Running float-guided maximization..."
  let astVal ← evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
  let result := globalMaximizeGuided astVal boxVal cfg

  -- 4. Extract the midpoint of the best box as witness
  let bestBox := result.bound.bestBox
  let xOpt : ℚ := match bestBox with
    | [I] => (I.lo + I.hi) / 2
    | _ => domainVal.lo  -- Fallback

  trace[LeanCert.discovery] "Best box: {bestBox.map (fun I => s!"[{I.lo}, {I.hi}]")}"
  trace[LeanCert.discovery] "Witness point: x = {xOpt}"
  trace[LeanCert.discovery] "Maximum value ≈ {result.bound.hi}"

  -- 5. Evaluate f at xOpt to get a concrete lower bound
  -- We use the lower bound of interval evaluation at the point as our transitivity constant
  let evalCfg : EvalConfig := { taylorDepth := taylorDepth }
  let pointInterval : IntervalRat := ⟨xOpt, xOpt, le_refl xOpt⟩
  let fAtXOpt := evalIntervalCore1 astVal pointInterval evalCfg
  let cBound := fAtXOpt.lo  -- c such that c ≤ f(xOpt)

  trace[LeanCert.discovery] "f(xOpt) ∈ [{fAtXOpt.lo}, {fAtXOpt.hi}]"
  trace[LeanCert.discovery] "Using bound c = {cBound} for transitivity"

  -- 6. Check that ∀ y ∈ I, f(y) ≤ c (upper bound check)
  let upperOk := LeanCert.Validity.checkUpperBound astVal domainVal cBound evalCfg
  trace[LeanCert.discovery] "checkUpperBound: {upperOk}"

  -- 7. Check that c ≤ f(xOpt) (point lower bound check)
  let pointOk := LeanCert.Validity.checkPointLowerBound astVal xOpt cBound evalCfg
  trace[LeanCert.discovery] "checkPointLowerBound: {pointOk}"

  if !upperOk || !pointOk then
    throwError "interval_argmax: Bound verification failed.\n\
      • checkUpperBound (∀ y ∈ I, f(y) ≤ {cBound}): {upperOk}\n\
      • checkPointLowerBound ({cBound} ≤ f({xOpt})): {pointOk}\n\
      Try increasing Taylor depth or using a different witness."

  -- 8. Generate support proof
  let suppProof ← LeanCert.Meta.mkSupportedCoreProof ast

  -- 9. Provide witness: refine ⟨xOpt, ?memProof, ?boundProof⟩
  let xOptExpr := toExpr xOpt
  let xOptSyntax ← Term.exprToSyntax xOptExpr
  evalTactic (← `(tactic| refine ⟨(($xOptSyntax : ℚ) : ℝ), ?_, ?_⟩))

  -- 10. Prove membership (x ∈ I)
  trace[LeanCert.discovery] "Proving membership..."
  try
    let memGoal ← getMainGoal
    let memType ← memGoal.getType
    let memTypeWhnf ← whnf memType
    match_expr memTypeWhnf with
    | And _ _ =>
      let memTypeWhnfSyntax ← Term.exprToSyntax memTypeWhnf
      evalTactic (← `(tactic| change $memTypeWhnfSyntax))
      evalTactic (← `(tactic| constructor <;> norm_cast))
    | _ =>
      match_expr memType with
      | Membership.mem _ _ _ interval _xExpr =>
        let intervalSyntax ← Term.exprToSyntax interval
        evalTactic (← `(tactic| simp [($intervalSyntax:term), Set.mem_Icc]))
      | _ =>
        evalTactic (← `(tactic| simp [Set.mem_Icc]))
      if (← getGoals).isEmpty then
        pure ()
      else
        let memGoal ← getMainGoal
        let memType ← memGoal.getType
        match_expr memType with
        | And _ _ =>
          evalTactic (← `(tactic| constructor <;> norm_cast))
        | _ =>
          evalTactic (← `(tactic| norm_cast))
  catch _ =>
    try
      evalTactic (← `(tactic| decide))
    catch _ =>
      logWarning m!"Could not automatically prove {xOpt} ∈ [{domainVal.lo}, {domainVal.hi}]. Goal left open."
      return

  -- 11. Prove the bound: ∀ y ∈ I, f(y) ≤ f(xOpt)
  trace[LeanCert.discovery] "Proving universal bound..."

  if isNativeSyntax then
    -- For native syntax, simplify and use intervalBoundCore directly
    trace[LeanCert.discovery] "Using native syntax path with intervalBoundCore"
    try
      -- The goal is: ∀ y ∈ Set.Icc a b, f(y) ≤ f(xOpt)
      -- where f(xOpt) involves xOpt which is (q : ℚ) : ℝ

      -- First, simplify the goal to reduce f(xOpt) to a concrete form
      -- Use push_cast and norm_num to simplify rational arithmetic
      try evalTactic (← `(tactic| simp only [Rat.cast_intCast, Rat.cast_natCast])) catch _ => pure ()
      try evalTactic (← `(tactic| push_cast)) catch _ => pure ()
      try evalTactic (← `(tactic| norm_num [Rat.divInt_eq_div])) catch _ => pure ()

      -- Now call intervalBoundCore on the simplified goal
      LeanCert.Tactic.Auto.intervalBoundCore taylorDepth
      trace[LeanCert.discovery] "✓ Proof complete (native syntax)"
    catch e =>
      throwError "interval_argmax: Could not prove universal bound.\n\
        Error: {e.toMessageData}\n\
        The witness x = {xOpt} may need higher precision."
  else
    -- For Expr.eval syntax, use verify_argmax
    trace[LeanCert.discovery] "Using verify_argmax path"
    try
      -- Build the proof term using verify_argmax
      let astSyntax ← Term.exprToSyntax ast
      let suppSyntax ← Term.exprToSyntax suppProof
      let domainSyntax ← Term.exprToSyntax domainExpr
      let cBoundExpr := toExpr cBound
      let cBoundSyntax ← Term.exprToSyntax cBoundExpr
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]
      let cfgSyntax ← Term.exprToSyntax cfgExpr

      -- Membership proof for xOpt
      evalTactic (← `(tactic|
        apply LeanCert.Validity.verify_argmax $astSyntax $suppSyntax $domainSyntax $xOptSyntax $cBoundSyntax $cfgSyntax
          ?_ (by native_decide) (by native_decide)))

      -- Prove xOpt ∈ I
      if !(← getGoals).isEmpty then
        evalTactic (← `(tactic| constructor <;> norm_cast))

      trace[LeanCert.discovery] "✓ Proof complete"
    catch e =>
      -- Fallback to intervalBoundCore
      trace[LeanCert.discovery] "verify_argmax failed, trying intervalBoundCore fallback..."
      try
        LeanCert.Tactic.Auto.intervalBoundCore taylorDepth
        trace[LeanCert.discovery] "✓ Proof complete (via fallback)"
      catch e2 =>
        throwError "interval_argmax: Could not prove universal bound.\n\
          Primary method (verify_argmax): {e.toMessageData}\n\
          Fallback method (intervalBoundCore): {e2.toMessageData}\n\
          The witness x = {xOpt} may need higher precision."

/-- The interval_argmax tactic.

Proves goals of the form `∃ x ∈ I, ∀ y ∈ I, f(y) ≤ f(x)` by:
1. Running global optimization to find the point x where f is maximized.
2. Instantiating the existential with x.
3. Proving membership x ∈ I.
4. Proving the universal bound using interval arithmetic.
-/
syntax (name := intervalArgmaxTac) "interval_argmax" (num)? : tactic

@[tactic intervalArgmaxTac]
unsafe def elabIntervalArgmax : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalArgmaxCore depth

/-- The interval_argmin tactic implementation -/
unsafe def intervalArgminCore (taylorDepth : Nat) : TacticM Unit := do
  LeanCert.Tactic.Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.argmin _varName domainExpr funcExpr) ← parseArgminGoal goalType
    | let diagReport ← LeanCert.Tactic.Auto.mkDiagnosticReport "interval_argmin" goalType "parse"
        (some m!"Expected form: ∃ x ∈ I, ∀ y ∈ I, f(x) ≤ f(y)\n\n\
                 This proves existence of a minimizer point x in I.")
      throwError "interval_argmin: Could not parse goal.\n\n{diagReport}"

  trace[LeanCert.discovery] "Parsing argmin goal: ∃ x ∈ I, ∀ y ∈ I, f(x) ≤ f(y)"
  trace[LeanCert.discovery] "Function expression: {funcExpr}"

  -- Check if using native syntax (not Expr.eval)
  let isNativeSyntax := !(← isExprEvalFunc funcExpr)
  trace[LeanCert.discovery] "Using native syntax: {isNativeSyntax}"

  -- 1. Reify the function
  let ast ← getAstFromFunc funcExpr
  trace[LeanCert.discovery] "Reified AST: {ast}"

  -- 2. Prepare optimization config
  let cfg : GuidedOptConfig := {
    maxIterations := 1000,
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true,
    heuristicSamples := 200,
    seed := 12345,
    useGridSearch := true,
    gridPointsPerDim := 10
  }

  let domainExpr ←
    match ← tryConvertSetIcc domainExpr with
    | some intervalRat => pure intervalRat
    | none => pure domainExpr
  let domainVal ← evalExpr IntervalRat (mkConst ``IntervalRat) domainExpr
  let boxVal : Box := [domainVal]
  trace[LeanCert.discovery] "Domain: [{domainVal.lo}, {domainVal.hi}]"

  -- 3. Run optimization to find the argmin (use minimize instead of maximize)
  trace[LeanCert.discovery] "Running float-guided minimization..."
  let astVal ← evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
  let result := globalMinimizeGuided astVal boxVal cfg

  -- 4. Extract the midpoint of the best box as witness
  let bestBox := result.bound.bestBox
  let xOpt : ℚ := match bestBox with
    | [I] => (I.lo + I.hi) / 2
    | _ => domainVal.lo  -- Fallback

  trace[LeanCert.discovery] "Best box: {bestBox.map (fun I => s!"[{I.lo}, {I.hi}]")}"
  trace[LeanCert.discovery] "Witness point: x = {xOpt}"
  trace[LeanCert.discovery] "Minimum value ≈ {result.bound.lo}"

  -- 5. Evaluate f at xOpt to get a concrete upper bound
  -- We use the upper bound of interval evaluation at the point as our transitivity constant
  let evalCfg : EvalConfig := { taylorDepth := taylorDepth }
  let pointInterval : IntervalRat := ⟨xOpt, xOpt, le_refl xOpt⟩
  let fAtXOpt := evalIntervalCore1 astVal pointInterval evalCfg
  let cBound := fAtXOpt.hi  -- c such that f(xOpt) ≤ c

  trace[LeanCert.discovery] "f(xOpt) ∈ [{fAtXOpt.lo}, {fAtXOpt.hi}]"
  trace[LeanCert.discovery] "Using bound c = {cBound} for transitivity"

  -- 6. Check that ∀ y ∈ I, c ≤ f(y) (lower bound check)
  let lowerOk := LeanCert.Validity.checkLowerBound astVal domainVal cBound evalCfg
  trace[LeanCert.discovery] "checkLowerBound: {lowerOk}"

  -- 7. Check that f(xOpt) ≤ c (point upper bound check)
  let pointOk := LeanCert.Validity.checkPointUpperBound astVal xOpt cBound evalCfg
  trace[LeanCert.discovery] "checkPointUpperBound: {pointOk}"

  if !lowerOk || !pointOk then
    throwError "interval_argmin: Bound verification failed.\n\
      • checkLowerBound (∀ y ∈ I, {cBound} ≤ f(y)): {lowerOk}\n\
      • checkPointUpperBound (f({xOpt}) ≤ {cBound}): {pointOk}\n\
      Try increasing Taylor depth or using a different witness."

  -- 8. Generate support proof
  let suppProof ← LeanCert.Meta.mkSupportedCoreProof ast

  -- 9. Provide witness: refine ⟨xOpt, ?memProof, ?boundProof⟩
  let xOptExpr := toExpr xOpt
  let xOptSyntax ← Term.exprToSyntax xOptExpr
  evalTactic (← `(tactic| refine ⟨(($xOptSyntax : ℚ) : ℝ), ?_, ?_⟩))

  -- 10. Prove membership (x ∈ I)
  trace[LeanCert.discovery] "Proving membership..."
  try
    let memGoal ← getMainGoal
    let memType ← memGoal.getType
    let memTypeWhnf ← whnf memType
    match_expr memTypeWhnf with
    | And _ _ =>
      let memTypeWhnfSyntax ← Term.exprToSyntax memTypeWhnf
      evalTactic (← `(tactic| change $memTypeWhnfSyntax))
      evalTactic (← `(tactic| constructor <;> norm_cast))
    | _ =>
      match_expr memType with
      | Membership.mem _ _ _ interval _xExpr =>
        let intervalSyntax ← Term.exprToSyntax interval
        evalTactic (← `(tactic| simp [($intervalSyntax:term), Set.mem_Icc]))
      | _ =>
        evalTactic (← `(tactic| simp [Set.mem_Icc]))
      if (← getGoals).isEmpty then
        pure ()
      else
        let memGoal ← getMainGoal
        let memType ← memGoal.getType
        match_expr memType with
        | And _ _ =>
          evalTactic (← `(tactic| constructor <;> norm_cast))
        | _ =>
          evalTactic (← `(tactic| norm_cast))
  catch _ =>
    try
      evalTactic (← `(tactic| decide))
    catch _ =>
      logWarning m!"Could not automatically prove {xOpt} ∈ [{domainVal.lo}, {domainVal.hi}]. Goal left open."
      return

  -- 11. Prove the bound: ∀ y ∈ I, f(xOpt) ≤ f(y)
  trace[LeanCert.discovery] "Proving universal bound..."

  if isNativeSyntax then
    -- For native syntax, simplify and use intervalBoundCore directly
    trace[LeanCert.discovery] "Using native syntax path with intervalBoundCore"
    try
      -- First, simplify the goal to reduce f(xOpt) to a concrete form
      try evalTactic (← `(tactic| simp only [Rat.cast_intCast, Rat.cast_natCast])) catch _ => pure ()
      try evalTactic (← `(tactic| push_cast)) catch _ => pure ()
      try evalTactic (← `(tactic| norm_num [Rat.divInt_eq_div])) catch _ => pure ()

      -- Now call intervalBoundCore on the simplified goal
      LeanCert.Tactic.Auto.intervalBoundCore taylorDepth
      trace[LeanCert.discovery] "✓ Proof complete (native syntax)"
    catch e =>
      throwError "interval_argmin: Could not prove universal bound.\n\
        Error: {e.toMessageData}\n\
        The witness x = {xOpt} may need higher precision."
  else
    -- For Expr.eval syntax, use verify_argmin
    trace[LeanCert.discovery] "Using verify_argmin path"
    try
      -- Build the proof term using verify_argmin
      let astSyntax ← Term.exprToSyntax ast
      let suppSyntax ← Term.exprToSyntax suppProof
      let domainSyntax ← Term.exprToSyntax domainExpr
      let cBoundExpr := toExpr cBound
      let cBoundSyntax ← Term.exprToSyntax cBoundExpr
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]
      let cfgSyntax ← Term.exprToSyntax cfgExpr

      -- Membership proof for xOpt
      evalTactic (← `(tactic|
        apply LeanCert.Validity.verify_argmin $astSyntax $suppSyntax $domainSyntax $xOptSyntax $cBoundSyntax $cfgSyntax
          ?_ (by native_decide) (by native_decide)))

      -- Prove xOpt ∈ I
      if !(← getGoals).isEmpty then
        evalTactic (← `(tactic| constructor <;> norm_cast))

      trace[LeanCert.discovery] "✓ Proof complete"
    catch e =>
      -- Fallback to intervalBoundCore
      trace[LeanCert.discovery] "verify_argmin failed, trying intervalBoundCore fallback..."
      try
        LeanCert.Tactic.Auto.intervalBoundCore taylorDepth
        trace[LeanCert.discovery] "✓ Proof complete (via fallback)"
      catch e2 =>
        throwError "interval_argmin: Could not prove universal bound.\n\
          Primary method (verify_argmin): {e.toMessageData}\n\
          Fallback method (intervalBoundCore): {e2.toMessageData}\n\
          The witness x = {xOpt} may need higher precision."

/-- The interval_argmin tactic.

Proves goals of the form `∃ x ∈ I, ∀ y ∈ I, f(x) ≤ f(y)` by:
1. Running global optimization to find the point x where f is minimized.
2. Instantiating the existential with x.
3. Proving membership x ∈ I.
4. Proving the universal bound using interval arithmetic.
-/
syntax (name := intervalArgminTac) "interval_argmin" (num)? : tactic

@[tactic intervalArgminTac]
unsafe def elabIntervalArgmin : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalArgminCore depth

/-! ## Multivariate Minimization/Maximization Tactics -/

/-- Result of analyzing a multivariate existential bound goal -/
inductive MultivariateExistentialGoal where
  /-- ∃ m, ∀ x ∈ I, ∀ y ∈ J, ..., f(...) ≥ m (minimize) -/
  | minimize (varType : Lean.Expr) (vars : Array LeanCert.Tactic.Auto.VarIntervalInfo) (func : Lean.Expr)
  /-- ∃ M, ∀ x ∈ I, ∀ y ∈ J, ..., f(...) ≤ M (maximize) -/
  | maximize (varType : Lean.Expr) (vars : Array LeanCert.Tactic.Auto.VarIntervalInfo) (func : Lean.Expr)

/-- Parse a multivariate existential bound goal.
    Supports goals of the form:
    - `∃ m, ∀ x ∈ I, ∀ y ∈ J, f(x,y) ≥ m` (minimize)
    - `∃ M, ∀ x ∈ I, ∀ y ∈ J, f(x,y) ≤ M` (maximize) -/
def parseMultivariateExistentialGoal (goalType : Lean.Expr) :
    MetaM (Option MultivariateExistentialGoal) := do
  let goalType ← whnf goalType
  -- Match: ∃ m, body where body is a forall chain
  if let .app (.app (.const ``Exists _) _) body := goalType then
    if let .lam mName mTy mBody _ := body then
      withLocalDeclD mName mTy fun m => do
        let mBodyInst := mBody.instantiate1 m
        -- Now parse the multivariate forall chain
        if let some mvGoal ← LeanCert.Tactic.Auto.parseMultivariateBoundGoal mBodyInst then
          match mvGoal with
          | .forallGe vars func bound =>
            -- c ≤ f(...) where c should be our existential variable m
            let boundContainsM := bound.containsFVar m.fvarId!
            if boundContainsM then
              return some (.minimize mTy vars func)
            else return none
          | .forallLe vars func bound =>
            -- f(...) ≤ c where c should be our existential variable m
            let boundContainsM := bound.containsFVar m.fvarId!
            if boundContainsM then
              return some (.maximize mTy vars func)
            else return none
        else return none
    else return none
  else return none

/-- The interval_minimize_mv tactic implementation for multivariate goals -/
unsafe def intervalMinimizeMvCore (taylorDepth : Nat) : TacticM Unit := do
  LeanCert.Tactic.Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.minimize varType vars funcExpr) ← parseMultivariateExistentialGoal goalType
    | throwError "interval_minimize_mv: Goal must be of form `∃ m, ∀ x ∈ I, ∀ y ∈ J, ..., f(...) ≥ m`"

  trace[LeanCert.discovery] "Parsing multivariate goal: ∃ m, ∀ vars ∈ domains, f(...) ≥ m"
  trace[LeanCert.discovery] "Number of variables: {vars.size}"
  trace[LeanCert.discovery] "Function expression: {funcExpr}"

  -- 1. Reify the function
  let ast ← getAstFromFunc funcExpr
  trace[LeanCert.discovery] "Reified AST: {ast}"

  -- 2. Build the box from all variable intervals
  let mut boxVals : Array IntervalRat := #[]
  for v in vars do
    let intervalVal ← evalExpr IntervalRat (mkConst ``IntervalRat) v.intervalRat
    boxVals := boxVals.push intervalVal
    trace[LeanCert.discovery] "Variable {v.varName}: [{intervalVal.lo}, {intervalVal.hi}]"

  let boxVal : Box := boxVals.toList

  -- 3. Prepare config for multivariate guided optimization
  let cfg : GuidedOptConfig := {
    maxIterations := 2000,  -- More iterations for multivariate
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true,
    heuristicSamples := 300,  -- More samples for higher dimensions
    seed := 12345,
    useGridSearch := true,
    gridPointsPerDim := 5  -- Fewer points per dim for multivariate
  }

  -- 4. Run float-guided optimization
  trace[LeanCert.discovery] "Running multivariate float-guided optimization..."
  let astVal ← evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
  let result := globalMinimizeGuided astVal boxVal cfg
  let boundVal := result.bound.lo

  trace[LeanCert.discovery] "Optimization complete: {result.bound.iterations} iterations"
  trace[LeanCert.discovery] "Found minimum bound: {boundVal}"
  trace[LeanCert.discovery] "Gap: [{result.bound.lo}, {result.bound.hi}]"

  -- Check if optimization converged well
  let gap := result.bound.hi - result.bound.lo
  if gap > cfg.tolerance then
    logWarning m!"⚠️ Optimization gap [{result.bound.lo}, {result.bound.hi}] exceeds tolerance {cfg.tolerance}.\n\
                  Consider increasing maxIterations or taylorDepth."

  -- 5. Provide witness and prove the bound
  -- Note: Coerce to ℝ since Expr.eval returns ℝ
  let boundRatExpr := toExpr boundVal
  let boundTerm ←
    match (← whnf varType) with
    | ty =>
      if ty.isConstOf ``Rat then
        pure boundRatExpr
      else if ty.isConstOf ``Real then
        mkAppOptM ``Rat.cast #[mkConst ``Real, none, boundRatExpr]
      else
        throwError "interval_minimize_mv: Unsupported bound type. Use ℚ or ℝ."
  let boundSyntax ← Term.exprToSyntax boundTerm
  trace[LeanCert.discovery] "Providing witness: m = {boundVal}"
  evalTactic (← `(tactic| refine ⟨$boundSyntax, ?_⟩))

  -- 6. Now we have a multivariate goal `∀ x ∈ I, ∀ y ∈ J, ..., f(...) ≥ bound`
  trace[LeanCert.discovery] "Proving multivariate universal bound with interval_bound..."
  LeanCert.Tactic.Auto.multivariateBoundCore cfg.maxIterations cfg.tolerance cfg.useMonotonicity taylorDepth
  trace[LeanCert.discovery] "✓ Proof complete"

/-- The interval_minimize_mv tactic.

Proves multivariate goals of the form `∃ m, ∀ x ∈ I, ∀ y ∈ J, f(x,y) ≥ m` by:
1. Running global optimization over the n-dimensional domain.
2. Instantiating the existential with the found minimum.
3. Proving the bound using `interval_bound`.
-/
syntax (name := intervalMinimizeMvTac) "interval_minimize_mv" (num)? : tactic

@[tactic intervalMinimizeMvTac]
unsafe def elabIntervalMinimizeMv : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalMinimizeMvCore depth

/-- The interval_maximize_mv tactic implementation for multivariate goals -/
unsafe def intervalMaximizeMvCore (taylorDepth : Nat) : TacticM Unit := do
  LeanCert.Tactic.Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some (.maximize varType vars funcExpr) ← parseMultivariateExistentialGoal goalType
    | throwError "interval_maximize_mv: Goal must be of form `∃ M, ∀ x ∈ I, ∀ y ∈ J, ..., f(...) ≤ M`"

  trace[LeanCert.discovery] "Parsing multivariate goal: ∃ M, ∀ vars ∈ domains, f(...) ≤ M"
  trace[LeanCert.discovery] "Number of variables: {vars.size}"
  trace[LeanCert.discovery] "Function expression: {funcExpr}"

  -- 1. Reify the function
  let ast ← getAstFromFunc funcExpr
  trace[LeanCert.discovery] "Reified AST: {ast}"

  -- 2. Build the box from all variable intervals
  let mut boxVals : Array IntervalRat := #[]
  for v in vars do
    let intervalVal ← evalExpr IntervalRat (mkConst ``IntervalRat) v.intervalRat
    boxVals := boxVals.push intervalVal
    trace[LeanCert.discovery] "Variable {v.varName}: [{intervalVal.lo}, {intervalVal.hi}]"

  let boxVal : Box := boxVals.toList

  -- 3. Prepare config
  let cfg : GuidedOptConfig := {
    maxIterations := 2000,
    tolerance := 1/1000,
    taylorDepth := taylorDepth,
    useMonotonicity := true,
    heuristicSamples := 300,
    seed := 12345,
    useGridSearch := true,
    gridPointsPerDim := 5
  }

  -- 4. Run float-guided optimization
  trace[LeanCert.discovery] "Running multivariate float-guided optimization..."
  let astVal ← evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
  let result := globalMaximizeGuided astVal boxVal cfg
  let boundVal := result.bound.hi

  trace[LeanCert.discovery] "Optimization complete: {result.bound.iterations} iterations"
  trace[LeanCert.discovery] "Found maximum bound: {boundVal}"
  trace[LeanCert.discovery] "Gap: [{result.bound.lo}, {result.bound.hi}]"

  -- Check convergence
  let gap := result.bound.hi - result.bound.lo
  if gap > cfg.tolerance then
    logWarning m!"⚠️ Optimization gap [{result.bound.lo}, {result.bound.hi}] exceeds tolerance {cfg.tolerance}.\n\
                  Consider increasing maxIterations or taylorDepth."

  -- 5. Provide witness
  -- Note: Coerce to ℝ since Expr.eval returns ℝ
  let boundRatExpr := toExpr boundVal
  let boundTerm ←
    match (← whnf varType) with
    | ty =>
      if ty.isConstOf ``Rat then
        pure boundRatExpr
      else if ty.isConstOf ``Real then
        mkAppOptM ``Rat.cast #[mkConst ``Real, none, boundRatExpr]
      else
        throwError "interval_maximize_mv: Unsupported bound type. Use ℚ or ℝ."
  let boundSyntax ← Term.exprToSyntax boundTerm
  trace[LeanCert.discovery] "Providing witness: M = {boundVal}"
  evalTactic (← `(tactic| refine ⟨$boundSyntax, ?_⟩))

  -- 6. Prove the multivariate bound
  trace[LeanCert.discovery] "Proving multivariate universal bound with interval_bound..."
  LeanCert.Tactic.Auto.multivariateBoundCore cfg.maxIterations cfg.tolerance cfg.useMonotonicity taylorDepth
  trace[LeanCert.discovery] "✓ Proof complete"

/-- The interval_maximize_mv tactic.

Proves multivariate goals of the form `∃ M, ∀ x ∈ I, ∀ y ∈ J, f(x,y) ≤ M` by:
1. Running global optimization over the n-dimensional domain.
2. Instantiating the existential with the found maximum.
3. Proving the bound using `interval_bound`.
-/
syntax (name := intervalMaximizeMvTac) "interval_maximize_mv" (num)? : tactic

@[tactic intervalMaximizeMvTac]
unsafe def elabIntervalMaximizeMv : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.toNat
    | none => 10
  intervalMaximizeMvCore depth

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
  getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``LE.le && args.size >= 4 then
      return some (args[2]!, args[3]!)
    return none

  extractLowerBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq b x then
        return some a
    return none

  extractUpperBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq a x then
        return some b
    return none

  extractBoundsFromAnd (memExpr : Lean.Expr) (x : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match_expr memExpr with
    | And a b =>
      if let some lo ← extractLowerBound a x then
        if let some hi ← extractUpperBound b x then
          return some (lo, hi)
      if let some lo ← extractLowerBound b x then
        if let some hi ← extractUpperBound a x then
          return some (lo, hi)
      return none
    | _ => return none

  mkSetIccFromBounds (loExpr hiExpr : Lean.Expr) : MetaM Lean.Expr := do
    mkAppM ``Set.Icc #[loExpr, hiExpr]

  /-- Extract the interval from a membership expression x ∈ I -/
  extractInterval (memExpr : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memExpr with
    | Membership.mem _ _ _ interval xExpr =>
      if ← isDefEq xExpr x then return some interval else return none
    | _ =>
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memExpr x then
        return some (← mkSetIccFromBounds loExpr hiExpr)
      let memExprWhnf ← withTransparency TransparencyMode.all <| whnf memExpr
      if memExprWhnf == memExpr then
        return none
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memExprWhnf x then
        return some (← mkSetIccFromBounds loExpr hiExpr)
      return none

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

/-- Check if a root goal needs normalization (f = c where c ≠ 0) -/
private def needsRootNormalization (goalType : Lean.Expr) : MetaM Bool := do
  let goalType ← whnf goalType
  match_expr goalType with
  | Exists _ body =>
    if let .lam _ _ innerBody _ := body then
      let innerBody ← whnf innerBody
      match_expr innerBody with
      | And _ eqExpr =>
        match_expr eqExpr with
        | Eq _ _ rhs =>
          let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
          let rhs ← whnf rhs
          let isZero ← isDefEq rhs zero
          return !isZero
        | _ => return false
      | _ => return false
    else return false
  | _ => return false

/-- The interval_roots tactic implementation -/
def intervalRootsCore (taylorDepth : Nat) : TacticM Unit := do
  LeanCert.Tactic.Auto.intervalNormCore
  -- Normalize f = c to f - c = 0 form only if needed
  let goal ← getMainGoal
  let goalType ← goal.getType
  if ← needsRootNormalization goalType then
    try evalTactic (← `(tactic| conv => arg 1; ext x; arg 2; rw [← sub_eq_zero]))
    catch _ => pure ()
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- 1. Parse the goal
  let some (.existsRoot _varName interval func) ← parseRootExistsGoal goalType
    | let diagReport ← LeanCert.Tactic.Auto.mkDiagnosticReport "interval_roots" goalType "parse"
        (some m!"Expected form: ∃ x ∈ I, f(x) = 0\n\n\
                 The function f must be continuous on interval I.\n\
                 Uses intermediate value theorem to find roots.")
      throwError "interval_roots: Could not parse goal.\n\n{diagReport}"

  goal.withContext do
    let mut fromSetIcc := false
    let intervalExpr ←
      match ← tryConvertSetIcc interval with
      | some intervalRat =>
          fromSetIcc := true
          pure intervalRat
      | none =>
          let intervalTy ← inferType interval
          if intervalTy.isConstOf ``IntervalRat then
            pure interval
          else
            throwError "interval_roots: Only IntervalRat or literal Set.Icc intervals are supported"

    -- 2. Get AST (either from Expr.eval or by reifying)
    let ast ← getAstFromFunc func

    -- 3. Generate ExprSupportedCore proof
    let supportProof ← mkSupportedCoreProof ast

    -- 4. Generate ContinuousOn proof
    let contProof ← mkContinuousOnProof ast intervalExpr

    -- 5. Build config expression
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    -- 6. Apply verify_sign_change theorem
    -- verify_sign_change : ExprSupportedCore e → ContinuousOn ... → checkSignChange e I cfg = true → ∃ x ∈ I, f(x) = 0
    let proof ← mkAppM ``LeanCert.Validity.RootFinding.verify_sign_change
      #[ast, supportProof, intervalExpr, cfgExpr, contProof]

    if fromSetIcc then
      let proofSyntax ← Term.exprToSyntax proof
      evalTactic (← `(tactic| refine (by
        have h := $proofSyntax (by native_decide)
        simpa [IntervalRat.mem_iff_mem_Icc, sub_eq_add_neg, sq, pow_two] using h)))
    else
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
- Reifies the function to a LeanCert AST
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
        let getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
          let fn := e.getAppFn
          let args := e.getAppArgs
          if fn.isConstOf ``LE.le && args.size >= 4 then
            return some (args[2]!, args[3]!)
          return none
        let extractLowerBound (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
          if let some (a, b) ← getLeArgs e then
            if ← isDefEq b x then
              return some a
          return none
        let extractUpperBound (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
          if let some (a, b) ← getLeArgs e then
            if ← isDefEq a x then
              return some b
          return none
        let extractBoundsFromAnd (memExpr : Lean.Expr) :
            MetaM (Option (Lean.Expr × Lean.Expr)) := do
          match_expr memExpr with
          | And a b =>
            if let some lo ← extractLowerBound a then
              if let some hi ← extractUpperBound b then
                return some (lo, hi)
            if let some lo ← extractLowerBound b then
              if let some hi ← extractUpperBound a then
                return some (lo, hi)
            return none
          | _ => return none
        let extractInterval (memExpr : Lean.Expr) : MetaM (Option Lean.Expr) := do
          match_expr memExpr with
          | Membership.mem _ _ _ interval xExpr =>
            if ← isDefEq xExpr x then return some interval else return none
          | _ =>
            if let some (loExpr, hiExpr) ← extractBoundsFromAnd memExpr then
              return some (← mkAppM ``Set.Icc #[loExpr, hiExpr])
            let memExprWhnf ← withTransparency TransparencyMode.all <| whnf memExpr
            if memExprWhnf == memExpr then
              return none
            if let some (loExpr, hiExpr) ← extractBoundsFromAnd memExprWhnf then
              return some (← mkAppM ``Set.Icc #[loExpr, hiExpr])
            return none
        -- bodyInst should be x ∈ I ∧ f x = 0
        match_expr bodyInst with
        | And memExpr eqExpr =>
          -- Extract interval from membership (use pattern matching)
          let some interval ← extractInterval memExpr | return none
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
    2. Applying verify_unique_root_computable theorem

    Uses the fully computable `verify_unique_root_computable` theorem which only
    requires `checkNewtonContractsCore`. This allows `native_decide` to work
    without noncomputable Real functions.
-/
unsafe def intervalUniqueRootCore (taylorDepth : Nat) : TacticM Unit := do
  LeanCert.Tactic.Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse goal: ∃! x, x ∈ I ∧ f(x) = 0
  let some (_varName, interval, func) ← parseUniqueRootGoal goalType
    | throwError "interval_unique_root: Goal must be of form `∃! x, x ∈ I ∧ f(x) = 0`"

  let mut fromSetIcc := false
  let intervalExpr ←
    match ← tryConvertSetIcc interval with
    | some intervalRat =>
        fromSetIcc := true
        pure intervalRat
    | none =>
        let intervalTy ← inferType interval
        if intervalTy.isConstOf ``IntervalRat then
          pure interval
        else
          throwError "interval_unique_root: Only IntervalRat or literal Set.Icc intervals are supported"

  -- Extract AST
  let ast ← getAstFromFunc func

  -- Generate ExprSupported proof (required by verify_unique_root_computable)
  let supportProof ← mkSupportedProof ast

  -- Generate UsesOnlyVar0 proof
  let var0Proof ← mkUsesOnlyVar0Proof ast

  -- Generate ContinuousOn proof
  let contProof ← LeanCert.Meta.mkContinuousOnProof ast intervalExpr

  -- Build EvalConfig (for the computable core check)
  let evalCfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

  -- Apply verify_unique_root_computable (fully computable version)
  -- Args: e, hsupp, hvar0, I, cfg, hCont
  let proof ← mkAppM ``Validity.RootFinding.verify_unique_root_computable
    #[ast, supportProof, var0Proof, intervalExpr, evalCfgExpr, contProof]

    if fromSetIcc then
      let proofSyntax ← Term.exprToSyntax proof
      evalTactic (← `(tactic| refine (by
        have h := $proofSyntax (by native_decide)
        simpa [IntervalRat.mem_iff_mem_Icc, sub_eq_add_neg] using h)))
  else
    -- Apply the proof (leaves one certificate check goal)
    let newGoals ← goal.apply proof
    setGoals newGoals

    -- Solve certificate check: checkNewtonContractsCore e I cfg = true
    -- This is computable, so native_decide works
    for g in newGoals do
      setGoals [g]
      evalTactic (← `(tactic| native_decide))

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
- Function must be in `ExprSupported` (const, var, add, mul, neg, sin, cos, exp only)
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

  -- The bound should be: Validity.Integration.integrateInterval1Core e I cfg
  -- Extract e, I, cfg from it
  if !bound.isAppOfArity ``Validity.Integration.integrateInterval1Core 3 then
    throwError "interval_integrate: Bound must be of form `Validity.Integration.integrateInterval1Core e I cfg`"

  let args := bound.getAppArgs
  let ast := args[0]!
  let interval := args[1]!
  let cfg := args[2]!

  -- Generate ExprSupportedCore proof for the AST
  let supportProof ← mkSupportedCoreProof ast

  -- Build the proof term: integrateInterval1Core_correct e supportProof I cfg
  let proof ← mkAppM ``Validity.Integration.integrateInterval1Core_correct
    #[ast, supportProof, interval, cfg]

  -- Assign the proof
  goal.assign proof

/-- The interval_integrate tactic.

Proves goals of the form `∫ x in (I.lo)...(I.hi), f(x) ∈ bound` by:
1. Computing the integral bound using interval arithmetic
2. Applying the integrateInterval1Core_correct theorem

**Usage:**
```lean
example : ∫ x in (0:ℝ)..1, x ∈ Validity.Integration.integrateInterval1Core (Expr.var 0) ⟨0, 1, by norm_num⟩ default := by
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
    let exprE ← elabTerm e (some (mkConst ``LeanCert.Core.Expr))
    let exprE ← instantiateMVars exprE

    -- Parse bounds as integers from syntax
    let loInt := parseSignedInt lo
    let hiInt := parseSignedInt hi
    let loVal : ℚ := loInt
    let hiVal : ℚ := hiInt

    -- Evaluate to get the actual values
    let astVal ← unsafe evalExpr LExpr (mkConst ``LeanCert.Core.Expr) exprE

    -- Check bounds are valid
    if h : loVal ≤ hiVal then
      let intervalVal : IntervalRat := ⟨loVal, hiVal, h⟩

      let cfg : GuidedOptConfig := {
        maxIterations := 1000,
        tolerance := 1/1000,
        taylorDepth := 10,
        useMonotonicity := true,
        heuristicSamples := 200,
        seed := 12345,
        useGridSearch := true,
        gridPointsPerDim := 10
      }
      let box : Box := [intervalVal]

      -- Compute range (min and max) using float-guided optimization
      let minResult := globalMinimizeGuided astVal box cfg
      let maxResult := globalMaximizeGuided astVal box cfg

      -- Check for sign change (root detection)
      let evalCfg : EvalConfig := { taylorDepth := 10 }
      let hasSignChange := Validity.RootFinding.checkSignChange astVal intervalVal evalCfg

      -- Compute gradient/derivative bounds for monotonicity analysis
      let grad := gradientIntervalCore astVal box evalCfg
      let gradStr := match grad with
        | [] => "N/A (no variables)"
        | [dI] => s!"[{dI.lo}, {dI.hi}]"
        | _ => s!"{grad.map (fun dI => s!"[{dI.lo}, {dI.hi}]")}"

      -- Classify monotonicity based on derivative sign
      let monotonicityStr := match grad with
        | [] => "constant"
        | [dI] =>
          if dI.lo > 0 then "strictly increasing"
          else if dI.hi < 0 then "strictly decreasing"
          else if dI.lo ≥ 0 then "non-decreasing"
          else if dI.hi ≤ 0 then "non-increasing"
          else "non-monotonic (derivative changes sign)"
        | _ => "multivariate"

      -- Count potential roots from sign change
      let rootStr := if hasSignChange then
        "Sign change detected - at least one root exists (by IVT)"
      else
        "No sign change - may have no roots or an even number"

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
                 Derivative bounds: {gradStr}\n\
                 Monotonicity: {monotonicityStr}\n\
                 \n\
                 Roots: {rootStr}\n\
                 Iterations: min={minResult.bound.iterations}, max={maxResult.bound.iterations}"
    else
      throwError "#explore: Invalid interval: lo ({loVal}) must be ≤ hi ({hiVal})"

end LeanCert.Tactic.Discovery
