/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Meta.ProveSupported
import LeanCert.Meta.ToExpr
import LeanCert.Validity.Bounds

/-!
# Automated Interval Arithmetic Tactics

This file provides smart tactics that automatically:
1. Reify Lean expressions to LeanCert AST (Phase 1)
2. Generate ExprSupportedCore proofs (Phase 2)
3. Apply the appropriate verification theorem and close the goal (Phase 3)

## Main tactics

* `interval_bound` - Automatically prove bounds using interval arithmetic

## Usage

```lean
-- Automatically proves the bound
example : ∀ x ∈ I01, x * x + Real.sin x ≤ 2 := by
  interval_bound

-- With custom Taylor depth for exp
example : ∀ x ∈ I01, Real.exp x ≤ 3 := by
  interval_bound { taylorDepth := 20 }
```

## Design notes

The tactic detects the goal structure:
- `∀ x ∈ I, f x ≤ c` → uses `verify_upper_bound`
- `∀ x ∈ I, c ≤ f x` → uses `verify_lower_bound`
-/

open Lean Meta Elab Tactic Term

-- Debug trace option for interval_decide
initialize registerTraceClass `interval_decide

-- Unified debug option for all interval tactics
register_option leancert.debug : Bool := {
  defValue := false
  descr := "Enable detailed diagnostic output for all LeanCert interval tactics"
}

/-- Check if LeanCert debug mode is enabled -/
def isLeanCertDebugEnabled : CoreM Bool :=
  return (← getOptions).getBool `leancert.debug false

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-! ## Goal Normalization -/

/-- Bridge: Set.Icc bound to arrow chain (lo ≤ x → x ≤ hi). -/
theorem forall_arrow_of_Icc {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, lo ≤ x → x ≤ hi → P x := by
  intro h x hxlo hxhi
  exact h x ⟨hxlo, hxhi⟩

/-- Bridge: Set.Icc bound to reversed arrow chain (x ≤ hi → lo ≤ x). -/
theorem forall_arrow_of_Icc_rev {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, x ≤ hi → lo ≤ x → P x := by
  intro h x hxhi hxlo
  exact h x ⟨hxlo, hxhi⟩

/-- Bridge: Set.Icc bound to conjunctive domain (lo ≤ x ∧ x ≤ hi). -/
theorem forall_and_of_Icc {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, (lo ≤ x ∧ x ≤ hi) → P x := by
  intro h x hx
  exact h x hx

/-- Bridge: Set.Icc bound to reversed conjunctive domain (x ≤ hi ∧ lo ≤ x). -/
theorem forall_and_of_Icc_rev {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, (x ≤ hi ∧ lo ≤ x) → P x := by
  intro h x hx
  exact h x ⟨hx.2, hx.1⟩

private def goalNeedsIccWrapper (goalType : Lean.Expr) : MetaM Bool := do
  let goalType ← whnf goalType
  if !goalType.isForall then
    return false
  let .forallE name ty body _ := goalType | return false
  withLocalDeclD name ty fun x => do
    let bodyRaw := body.instantiate1 x
    let bodyWhnf ← whnf bodyRaw
    if !bodyWhnf.isForall then
      return false
    let .forallE _ memTy innerBody _ := bodyWhnf | return false
    let memTyRaw :=
      match bodyRaw with
      | .forallE _ memTyRaw _ _ => memTyRaw
      | _ => memTy

    let isMembership : MetaM Bool := do
      match_expr memTyRaw with
      | Membership.mem _ _ _ _ _ => return true
      | _ => return false

    if (← isMembership) then
      return false

    let isAnd (e : Lean.Expr) : Bool :=
      match e with
      | .app (.app (.const ``And _) _) _ => true
      | _ => false

    let getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isConstOf ``LE.le && args.size >= 4 then
        return some (args[2]!, args[3]!)
      if fn.isConstOf ``LT.lt && args.size >= 4 then
        return some (args[2]!, args[3]!)
      return none

    let isBoundProp (e : Lean.Expr) : MetaM Bool := do
      if let some (a, b) ← getLeArgs e then
        if (← isDefEq a x) || (← isDefEq b x) then
          return true
      return false

    let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
    if isAnd memTy || isAnd memTyWhnf then
      return true

    if innerBody.isForall then
      let .forallE _ memTy2 _ _ := innerBody | return false
      let memTy2Whnf ← withTransparency TransparencyMode.all <| whnf memTy2
      if (← isBoundProp memTy) || (← isBoundProp memTyWhnf) then
        if (← isBoundProp memTy2) || (← isBoundProp memTy2Whnf) then
          return true
    return false

private partial def hasNonPropBinder (e : Lean.Expr) : MetaM Bool := do
  let eWhnf ← whnf e
  if !eWhnf.isForall then
    return false
  let .forallE name ty body _ := eWhnf | return false
  if (← isProp ty) then
    withLocalDeclD name ty fun h => do
      hasNonPropBinder (body.instantiate1 h)
  else
    return true

private def goalIsMultivariate (goalType : Lean.Expr) : MetaM Bool := do
  let goalType ← whnf goalType
  if !goalType.isForall then
    return false
  let .forallE name ty body _ := goalType | return false
  withLocalDeclD name ty fun x => do
    let body := body.instantiate1 x
    let bodyWhnf ← whnf body
    if !bodyWhnf.isForall then
      return false
    let .forallE _ memTy innerBody _ := bodyWhnf | return false
    withLocalDeclD `hx memTy fun _hx => do
      let innerInst := innerBody.instantiate1 _hx
      hasNonPropBinder innerInst

private def tryNormalizeGoalToIcc : TacticM Bool := do
  let goal ← getMainGoal
  if ← goalNeedsIccWrapper (← goal.getType) then
    try
      evalTactic (← `(tactic|
        first
        | refine (forall_arrow_of_Icc ?_)
        | refine (forall_arrow_of_Icc_rev ?_)
        | refine (forall_and_of_Icc ?_)
        | refine (forall_and_of_Icc_rev ?_)
      ))
      return true
    catch _ => return false
  else
    return false

/-- Normalize common goal patterns for interval tactics. -/
def intervalNormCore : TacticM Unit := do
  try
    evalTactic (← `(tactic|
      simp only [ge_iff_le, gt_iff_lt, sub_eq_add_neg, Rat.divInt_eq_div,
        Set.mem_setOf] at *))
  catch _ =>
    pure ()
  -- Try to normalize the outermost variable to Set.Icc form.
  -- The parser handles mixed forms, so partial normalization is fine for multivariate goals.
  discard <| tryNormalizeGoalToIcc

/-- The interval_norm tactic.

    Normalizes inequalities, subtraction, rational division, and domain syntax
    to reduce goal-shape variation before parsing. -/
syntax (name := intervalNormTac) "interval_norm" : tactic

@[tactic intervalNormTac]
def elabIntervalNorm : Tactic := fun _ => intervalNormCore

/-! ## Rational Extraction Helpers

Utilities for extracting rational numbers from Lean expressions representing
real number literals or coercions.
-/

/-- Extract a natural number from a Nat literal expression -/
private def extractNatLit (e : Lean.Expr) : MetaM (Option ℕ) := do
  -- Try raw literal first
  if let some n := e.rawNatLit? then
    return some n
  -- Try after reduction
  let e ← whnf e
  if let some n := e.rawNatLit? then
    return some n
  else return none

/-- Extract an integer from an Int literal expression -/
private def extractIntLit (e : Lean.Expr) : MetaM (Option ℤ) := do
  let e ← whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- Int.ofNat n
  if fn.isConstOf ``Int.ofNat then
    if args.size > 0 then
      if let some n ← extractNatLit args[0]! then
        return some (n : ℤ)
    return none
  -- Int.negSucc n (represents -(n+1))
  else if fn.isConstOf ``Int.negSucc then
    if args.size > 0 then
      if let some n ← extractNatLit args[0]! then
        return some (-(n + 1 : ℤ))
    return none
  else return none

/-- Extract a rational from a Rat expression -/
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

    -- Check for Rat.ofInt
    if fn.isConstOf ``Rat.ofInt then
      if args.size > 0 then
        if let some i ← extractIntLit args[0]! then
          return some (i : ℚ)
      return none

    -- Check for OfNat.ofNat on Rat
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

    -- Try to match Rat.mk' num den ...
    else if fn.isConstOf ``Rat.mk' then
      return none  -- TODO: implement if needed

    else return none

/-- Try to extract a rational value from a Lean expression that represents a real number.
    Handles: Rat.cast, OfNat.ofNat, Nat.cast, Int.cast, negations, and divisions.
    Also handles direct ℚ expressions as a fallback. -/
partial def extractRatFromReal (e : Lean.Expr) : MetaM (Option ℚ) := do
  let e ←
    if e.isMVar then
      if let some val ← getExprMVarAssignment? e.mvarId! then
        instantiateMVars val
      else
        pure e
    else
      instantiateMVars e
  -- First try without whnf (preserves structure like OfNat.ofNat)
  if let some q ← tryExtract e then
    return some q
  -- Then try with whnf
  let e' ← whnf e
  let e' ← instantiateMVars e'
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
      -- OfNat.ofNat : {α : Type} → (n : ℕ) → [OfNat α n] → α
      -- args[1] is the natural number
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
      if args.size >= 6 then  -- HDiv.hDiv has 6 args: α β γ inst a b
        if let some a ← extractRatFromReal args[4]! then
          if let some b ← extractRatFromReal args[5]! then
            if b ≠ 0 then
              return some (a / b)
      return none

    -- Case 7: OfScientific.ofScientific (for decimal literals like 2.72)
    -- OfScientific.ofScientific : {α : Type} → [OfScientific α] → ℕ → Bool → ℕ → α
    -- 2.72 = ofScientific 272 true 2 = 272 * 10^(-2) = 272/100
    else if fn.isConstOf ``OfScientific.ofScientific then
      -- args: [type, inst, mantissa, isNegExp, exponent]
      if args.size >= 5 then
        if let some mantissa ← extractNatLit args[2]! then
          let isNegExp := args[3]!.isConstOf ``Bool.true
          if let some exp ← extractNatLit args[4]! then
            let base : ℚ := 10
            if isNegExp then
              -- mantissa * 10^(-exp) = mantissa / 10^exp
              return some ((mantissa : ℚ) / (base ^ exp))
            else
              -- mantissa * 10^exp
              return some ((mantissa : ℚ) * (base ^ exp))
      return none

    else return none

/-- Build an IntervalRat expression from two rational expressions and their Lean representations -/
def mkIntervalRat (loExpr hiExpr : Lean.Expr) (lo hi : ℚ) : MetaM Lean.Expr := do
  if lo > hi then
    throwError "Cannot create interval: lo ({lo}) > hi ({hi})"
  -- Build ⟨lo, hi, proof⟩
  -- The proof is `lo ≤ hi` which we can close with `by norm_num` or `by decide`
  let proofType ← mkAppM ``LE.le #[loExpr, hiExpr]

  -- Create the proof using decide (works for concrete rationals)
  let proof ← mkDecideProof proofType

  mkAppM ``IntervalRat.mk #[loExpr, hiExpr, proof]

/-! ## Goal Analysis

Utilities for analyzing the goal structure to determine which theorem to apply.
-/

/-- Information about interval source -/
structure IntervalInfo where
  /-- The IntervalRat expression to use in proofs -/
  intervalRat : Lean.Expr
  /-- If converted from Set.Icc, contains (lo, hi, loRatExpr, hiRatExpr, leProof, origLoExpr, origHiExpr) -/
  fromSetIcc : Option (ℚ × ℚ × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := none
  deriving Repr

/-- Result of analyzing a bound goal -/
inductive BoundGoal where
  /-- ∀ x ∈ I, f x ≤ c -/
  | forallLe (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, c ≤ f x -/
  | forallGe (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, f x < c -/
  | forallLt (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, c < f x -/
  | forallGt (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

/-- Try to parse a goal as a bound goal -/
def parseBoundGoal (goal : Lean.Expr) : MetaM (Option BoundGoal) := do
  -- Reduce the goal first to handle definitional equality
  let goal ← whnf goal

  -- Check for ∀ x, x ∈ I → ...
  if goal.isForall then
    let .forallE name ty body _ := goal | return none

    -- body should be x ∈ I → comparison
    withLocalDeclD name ty fun x => do
      let body := body.instantiate1 x
      let body ← whnf body
      if body.isForall then
        let .forallE _ memTy innerBody _ := body | return none

        let parseComparison (comparison : Lean.Expr) (interval : IntervalInfo) :
            MetaM (Option BoundGoal) := do
          match_expr comparison with
          | LE.le _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallLe name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallGe name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | GE.ge _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallGe name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallLe name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | LT.lt _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallLt name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallGt name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | GT.gt _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallGt name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallLt name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | _ => return none

        -- memTy should be x ∈ I (Membership.mem x I)
        -- Don't reduce with whnf as it will expand the membership definition

        -- Try to extract interval from membership
        let interval? ← extractInterval memTy x
        if let some interval := interval? then
          -- innerBody is the comparison
          return ← withLocalDeclD `hx memTy fun _hx => do
            let comparison := innerBody.instantiate1 _hx
            parseComparison comparison interval
        let parseArrowBounds (memTy innerBody : Lean.Expr) : MetaM (Option BoundGoal) := do
          let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
          let memTyCandidates := if memTyWhnf == memTy then #[memTy] else #[memTy, memTyWhnf]

          let rec findSome (cands : List Lean.Expr) (f : Lean.Expr → MetaM (Option BoundGoal)) :
              MetaM (Option BoundGoal) := do
            match cands with
            | [] => return none
            | cand :: rest =>
              if let some goal ← f cand then
                return some goal
              findSome rest f

          let tryLower (memTyCand : Lean.Expr) : MetaM (Option BoundGoal) := do
            if let some loExpr ← extractLowerBound memTyCand x then
              return ← withLocalDeclD `hx1 memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Whnf ← withTransparency TransparencyMode.all <| whnf memTy2
                  let memTy2Candidates := if memTy2Whnf == memTy2 then #[memTy2] else #[memTy2, memTy2Whnf]
                  let tryUpper (memTy2Cand : Lean.Expr) : MetaM (Option BoundGoal) := do
                    if let some hiExpr ← extractUpperBound memTy2Cand x then
                      if let some interval ← mkIntervalInfoFromBounds loExpr hiExpr then
                        return ← withLocalDeclD `hx2 memTy2 fun _hx2 => do
                          let comparison := innerBody2.instantiate1 _hx2
                          parseComparison comparison interval
                    return none
                  return ← findSome memTy2Candidates.toList tryUpper
                return none
            return none

          let tryUpper (memTyCand : Lean.Expr) : MetaM (Option BoundGoal) := do
            if let some hiExpr ← extractUpperBound memTyCand x then
              return ← withLocalDeclD `hx1 memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Whnf ← withTransparency TransparencyMode.all <| whnf memTy2
                  let memTy2Candidates := if memTy2Whnf == memTy2 then #[memTy2] else #[memTy2, memTy2Whnf]
                  let tryLower (memTy2Cand : Lean.Expr) : MetaM (Option BoundGoal) := do
                    if let some loExpr ← extractLowerBound memTy2Cand x then
                      if let some interval ← mkIntervalInfoFromBounds loExpr hiExpr then
                        return ← withLocalDeclD `hx2 memTy2 fun _hx2 => do
                          let comparison := innerBody2.instantiate1 _hx2
                          parseComparison comparison interval
                    return none
                  return ← findSome memTy2Candidates.toList tryLower
                return none
            return none

          if let some goal ← findSome memTyCandidates.toList tryLower then
            return some goal
          if let some goal ← findSome memTyCandidates.toList tryUpper then
            return some goal
          return none

        if let some arrowGoal ← parseArrowBounds memTy innerBody then
          return some arrowGoal
        return none
      else
        return none
  else
    return none

where
  /-- Extract (lhs, rhs) from an LE.le application. -/
  getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``LE.le && args.size >= 4 then
      return some (args[2]!, args[3]!)
    return none

  /-- Extract lower bound lo from lo ≤ x. -/
  extractLowerBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq b x then
        return some a
    return none

  /-- Extract upper bound hi from x ≤ hi. -/
  extractUpperBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq a x then
        return some b
    return none

  /-- Extract bounds from conjunction form lo ≤ x ∧ x ≤ hi. -/
  extractBoundsFromAnd (memTy : Lean.Expr) (x : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match_expr memTy with
    | And a b =>
      if let some lo ← extractLowerBound a x then
        if let some hi ← extractUpperBound b x then
          return some (lo, hi)
      if let some lo ← extractLowerBound b x then
        if let some hi ← extractUpperBound a x then
          return some (lo, hi)
      return none
    | _ => return none

  /-- Build IntervalInfo from explicit lo/hi bounds. -/
  mkIntervalInfoFromBounds (loExpr hiExpr : Lean.Expr) : MetaM (Option IntervalInfo) := do
    if let some lo ← extractRatFromReal loExpr then
      if let some hi ← extractRatFromReal hiExpr then
        let loRatExpr := toExpr lo
        let hiRatExpr := toExpr hi
        let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
        let leProof ← mkDecideProof leProofTy
        let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
        return some {
          intervalRat := intervalRat
          fromSetIcc := some (lo, hi, loRatExpr, hiRatExpr, leProof, loExpr, hiExpr)
        }
    return none

  /-- Extract the interval from a membership expression -/
  extractInterval (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option IntervalInfo) := do
    -- Try direct Membership.mem match
    -- Membership.mem : {α : Type u_1} → {γ : outParam (Type u_2)} → [self : Membership α γ] → γ → α → Prop
    -- Note: The mem function takes (container, element), but notation x ∈ I displays as element ∈ container
    match_expr memTy with
    | Membership.mem _ _ _ interval xExpr =>
      -- Check if xExpr matches x (might be the same or definitionally equal)
      if ← isDefEq xExpr x then
        -- Check if interval is already an IntervalRat
        let intervalTy ← inferType interval
        if intervalTy.isConstOf ``IntervalRat then
          return some { intervalRat := interval }
        -- Check if interval is Set.Icc lo hi
        else if let some info ← tryConvertSetIcc interval then
          return some info
        else
          return some { intervalRat := interval }  -- Return as-is, let type checking fail later if wrong
      else return none
    | _ =>
      -- The memTy might be definitionally expanded - check if it's a conjunction
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTy x then
        return ← mkIntervalInfoFromBounds loExpr hiExpr
      let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
      if memTyWhnf == memTy then
        return none
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTyWhnf x then
        return ← mkIntervalInfoFromBounds loExpr hiExpr
      return none

  /-- Try to convert a Set.Icc expression to an IntervalRat with full info -/
  tryConvertSetIcc (interval : Lean.Expr) : MetaM (Option IntervalInfo) := do
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
      -- Set.Icc : {α : Type*} → [Preorder α] → α → α → Set α
      -- So args are: [α, inst, lo, hi]
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

    let mkIntervalFromBounds (loExpr hiExpr : Lean.Expr) : MetaM (Option IntervalInfo) := do
      if let some lo ← extractRatFromReal loExpr then
        if let some hi ← extractRatFromReal hiExpr then
          let loRatExpr := toExpr lo
          let hiRatExpr := toExpr hi
          let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
          let leProof ← mkDecideProof leProofTy
          let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
          return some {
            intervalRat := intervalRat
            fromSetIcc := some (lo, hi, loRatExpr, hiRatExpr, leProof, loExpr, hiExpr)
          }
      return none

    if let some (loExpr, hiExpr) ← parseBounds interval then
      if let some info ← mkIntervalFromBounds loExpr hiExpr then
        return some info
    let intervalWhnf ← withTransparency TransparencyMode.all <| whnf interval
    if intervalWhnf == interval then
      return none
    if let some (loExpr, hiExpr) ← parseBounds intervalWhnf then
      return ← mkIntervalFromBounds loExpr hiExpr
    return none

/-! ## Diagnostic Helpers for Shadow Computation -/

/-- Extract interval bounds (lo, hi) from IntervalInfo for diagnostics -/
private def extractIntervalBoundsForDiag (info : IntervalInfo) : TacticM (ℚ × ℚ) := do
  match info.fromSetIcc with
  | some (lo, hi, _, _, _, _, _) => return (lo, hi)
  | none =>
    throwError "Cannot extract bounds from non-Icc interval for diagnostics"

/-- Reify a function expression to actual AST value for diagnostics -/
private def reifyFuncForDiag (func : Lean.Expr) : TacticM LeanCert.Core.Expr := do
  lambdaTelescope func fun _vars body => do
    let fn := body.getAppFn
    if fn.isConstOf ``LeanCert.Core.Expr.eval then
      let args := body.getAppArgs
      if args.size ≥ 2 then
        let astExpr := args[1]!
        let astVal ← unsafe evalExpr LeanCert.Core.Expr (mkConst ``LeanCert.Core.Expr) astExpr
        return astVal
      else
        throwError "Unexpected Expr.eval structure in diagnostic"
    else
      let astExpr ← reify func
      let astVal ← unsafe evalExpr LeanCert.Core.Expr (mkConst ``LeanCert.Core.Expr) astExpr
      return astVal

/-- Run shadow computation to diagnose why a proof failed -/
def runShadowDiagnostic (boundGoal : Option BoundGoal) (_goalType : Lean.Expr) : TacticM MessageData := do
  let some bg := boundGoal | return m!"(Could not parse goal for diagnostics)"

  match bg with
  | .forallLe _ interval func bound
  | .forallGe _ interval func bound
  | .forallLt _ interval func bound
  | .forallGt _ interval func bound =>
    try
      -- Extract interval bounds
      let (lo, hi) ← extractIntervalBoundsForDiag interval
      let I : IntervalRat :=
        if hle : lo ≤ hi then ⟨lo, hi, hle⟩
        else ⟨0, 1, by native_decide⟩

      -- Reify function to actual AST value
      let ast ← reifyFuncForDiag func

      -- Evaluate with high precision
      let diagCfg : EvalConfig := { taylorDepth := 30 }
      let result := evalIntervalCore1 ast I diagCfg

      -- Extract bound as rational
      let limitOpt ← extractRatFromReal bound

      -- Format diagnostic based on goal type
      let isUpperBound := match bg with
        | .forallLe .. | .forallLt .. => true
        | .forallGe .. | .forallGt .. => false

      match limitOpt with
      | some limit =>
        if isUpperBound then
          -- For f(x) ≤ c, check if computed lower bound exceeds limit
          if result.lo > limit then
            return m!"❌ Diagnostic Analysis:\n\
                      Goal: f(x) ≤ {limit}\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Mathematical Violation: Lower bound {result.lo} > limit {limit}.\n\
                      • The theorem is likely FALSE."
          else if result.hi > limit then
            return m!"⚠️ Diagnostic Analysis:\n\
                      Goal: f(x) ≤ {limit}\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Precision Issue: Upper bound {result.hi} > limit {limit}.\n\
                      • Try: interval_bound 50 or subdivide the domain."
          else
            return m!"Diagnostic Analysis:\n\
                      Computed Range: [{result.lo}, {result.hi}] ≤ {limit}\n\
                      The proof failed for technical reasons (side goal closure, etc.)."
        else
          -- For c ≤ f(x), check if computed upper bound is below limit
          if result.hi < limit then
            return m!"❌ Diagnostic Analysis:\n\
                      Goal: {limit} ≤ f(x)\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Mathematical Violation: Upper bound {result.hi} < limit {limit}.\n\
                      • The theorem is likely FALSE."
          else if result.lo < limit then
            return m!"⚠️ Diagnostic Analysis:\n\
                      Goal: {limit} ≤ f(x)\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Precision Issue: Lower bound {result.lo} < limit {limit}.\n\
                      • Try: interval_bound 50 or subdivide the domain."
          else
            return m!"Diagnostic Analysis:\n\
                      Computed Range: [{result.lo}, {result.hi}] ≥ {limit}\n\
                      The proof failed for technical reasons (side goal closure, etc.)."
      | none =>
        return m!"Diagnostic Analysis:\n\
                  Computed Range (depth 30): [{result.lo}, {result.hi}]\n\
                  (Could not extract rational from bound for comparison)"
    catch e =>
      return m!"(Diagnostic computation failed: {e.toMessageData})"

/-! ## Shared Diagnostic Helpers -/

/-- Format goal context for diagnostic output, showing both normal and detailed forms -/
def formatGoalContext (goalType : Lean.Expr) : MetaM MessageData := do
  let goalNormal ← Meta.ppExpr goalType
  let goalAll ← withOptions (fun opts => opts.setBool `pp.all true) (Meta.ppExpr goalType)
  return m!"Goal: {goalNormal}\n\nGoal (detailed): {goalAll}"

/-- Count foralls in an expression (for diagnostics) -/
private partial def countForallsAux (e : Lean.Expr) (depth : Nat) : MetaM (Nat × Option String) := do
  if depth > 20 then return (0, some "too deeply nested")
  if e.isForall then
    let .forallE name ty body _ := e | return (0, none)
    withLocalDeclD name ty fun x => do
      let (n, issue) ← countForallsAux (body.instantiate1 x) (depth + 1)
      return (n + 1, issue)
  else
    return (0, none)

/-- Find comparison operator at the body of a goal (for diagnostics) -/
private partial def findComparisonAux (e : Lean.Expr) (depth : Nat) : MetaM (Option String) := do
  if depth > 20 then return none
  let e ← whnf e
  if e.isForall then
    let .forallE name ty body _ := e | return none
    withLocalDeclD name ty fun x =>
      findComparisonAux (body.instantiate1 x) (depth + 1)
  else
    match_expr e with
    | LE.le _ _ _ _ => return some "≤"
    | GE.ge _ _ _ _ => return some "≥"
    | LT.lt _ _ _ _ => return some "<"
    | GT.gt _ _ _ _ => return some ">"
    | Eq _ _ _ => return some "="
    | Ne _ _ _ => return some "≠"
    | _ => return none

/-- Analyze goal structure and report what was found vs expected -/
def analyzeGoalStructure (goalType : Lean.Expr) : MetaM MessageData := do
  let goalType ← whnf goalType
  let mut findings := #[]

  let (numForalls, nestIssue) ← countForallsAux goalType 0
  findings := findings.push m!"• Found {numForalls} quantifier(s)"

  if let some issue := nestIssue then
    findings := findings.push m!"• Warning: {issue}"

  if let some comp ← findComparisonAux goalType 0 then
    findings := findings.push m!"• Found comparison: {comp}"
  else
    findings := findings.push m!"• No comparison operator found at goal body"

  return MessageData.joinSep findings.toList "\n"

/-- Suggest next actions based on failure type -/
def suggestNextActions (failureType : String) : MessageData :=
  match failureType with
  | "parse" => m!"Suggestions:\n\
      • Ensure goal has form: ∀ x ∈ I, f(x) ≤ c (or ≥, <, >)\n\
      • Try `interval_norm` to normalize the goal first\n\
      • Check that bounds are rational (not Real.pi, Real.sqrt, etc.)"
  | "precision" => m!"Suggestions:\n\
      • Try increasing Taylor depth: `interval_bound 50`\n\
      • Try subdivision: `interval_bound_subdiv 20 5`\n\
      • The bound may be too tight for automatic verification"
  | "reify" => m!"Suggestions:\n\
      • Check that all functions are supported (sin, cos, exp, log, pow, etc.)\n\
      • Try unfolding custom definitions with `simp only [myDef]`\n\
      • See LeanCert documentation for supported expressions"
  | "domain" => m!"Suggestions:\n\
      • Ensure domain is Set.Icc, IntervalRat, or arrow/And bounds\n\
      • Try rewriting with `simp only [Set.mem_Icc]`"
  | _ => m!"Suggestions:\n\
      • Check the error message above for specific guidance\n\
      • Try `set_option leancert.debug true` for detailed traces"

/-- Create a full diagnostic report for a failed tactic -/
def mkDiagnosticReport (tacticName : String) (goalType : Lean.Expr)
    (failureType : String) (additionalInfo : Option MessageData := none) : MetaM MessageData := do
  let goalCtx ← formatGoalContext goalType
  let analysis ← analyzeGoalStructure goalType
  let suggestions := suggestNextActions failureType
  let extra := match additionalInfo with
    | some info => m!"\n\nAdditional Info:\n{info}"
    | none => m!""
  return m!"─── {tacticName} Diagnostic ───\n\n\
            {goalCtx}\n\n\
            Structure Analysis:\n{analysis}\n\n\
            {suggestions}{extra}"

/-! ## Main Tactic Implementation -/

/-- The main interval_bound tactic implementation -/
def intervalBoundCore (taylorDepth : Nat) : TacticM Unit := do
  intervalNormCore
  -- Pre-process: convert ≥ to ≤ and > to < for uniform handling
  -- First intro variables to get into the body of the forall
  let preprocessed ← do
    try
      evalTactic (← `(tactic| intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
      pure true
    catch e =>
      trace[interval_decide] "Forall preprocessing failed: {e.toMessageData}"
      try
        evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
        pure true
      catch _ => pure false
  if preprocessed then
    trace[interval_decide] "Preprocessing applied ≥/> → ≤/<"

  -- Pre-process: normalize powers (x^2 → x*x, x^3 → x*x*x, etc.)
  try
    evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one] at *))
  catch _ => pure ()

  -- Check if the goal was already solved by simplification (e.g., x^0 ≤ 1 → 1 ≤ 1)
  let goals ← getGoals
  if goals.isEmpty then
    return

  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse the goal
  let some boundGoal ← parseBoundGoal goalType
    | do
      -- If parsing fails, try to solve trivially (e.g., after x^0 → 1, goal becomes 1 ≤ 1)
      try
        evalTactic (← `(tactic| intro _ _; norm_num))
        return
      catch _ => pure ()
      -- Debug: show the goal structure
      let goalWhnf ← whnf goalType
      throwError "interval_bound: Could not parse goal as a bound. Expected:\n\
                  • ∀ x ∈ I, f x ≤ c\n\
                  • ∀ x ∈ I, c ≤ f x\n\
                  • ∀ x ∈ I, f x < c\n\
                  • ∀ x ∈ I, c < f x\n\
                  \nGoal type: {goalType}\n\
                  Goal (whnf): {goalWhnf}"

  match boundGoal with
  | .forallLe _name interval func bound =>
    proveForallLe goal interval func bound taylorDepth
  | .forallGe _name interval func bound =>
    proveForallGe goal interval func bound taylorDepth
  | .forallLt _name interval func bound =>
    proveForallLt goal interval func bound taylorDepth
  | .forallGt _name interval func bound =>
    proveForallGt goal interval func bound taylorDepth

where
  /-- Try to extract the rational from a bound expression (possibly coerced to ℝ) -/
  extractRatBound (bound : Lean.Expr) : TacticM Lean.Expr := do
    -- The bound might be:
    -- 1. A direct ℚ literal
    -- 2. A coercion ↑q where q : ℚ (as Rat.cast)
    -- 3. A coercion instance application (Real.instRatCast.1 q)
    -- 4. A numeric literal like 2 : ℝ (OfNat.ofNat)
    let fn := bound.getAppFn
    let args := bound.getAppArgs

    -- Check for Rat.cast (which is what ↑ becomes for ℚ → ℝ)
    if fn.isConstOf ``Rat.cast then
      -- Rat.cast inst q - the last arg is the rational
      if args.size > 0 then
        return args.back!
      else
        throwError "Unexpected Rat.cast structure"
    else
      -- Check for the RatCast.ratCast form (the actual implementation)
      if fn.isConstOf ``RatCast.ratCast then
        -- RatCast.ratCast inst q - the last arg is the rational
        if args.size > 0 then
          return args.back!
        else
          throwError "Unexpected RatCast.ratCast structure"
      else
        -- Check if the type is already ℚ
        let boundTy ← inferType bound
        if boundTy.isConstOf ``Rat then
          return bound
        else
          -- Try to extract a rational value using our helper
          if let some q ← extractRatFromReal bound then
            return toExpr q
          else
            -- Last resort: try to see if this is a reducible form
            let boundReduced ← whnf bound
            let fnReduced := boundReduced.getAppFn
            if fnReduced.isConstOf ``Rat.cast || fnReduced.isConstOf ``RatCast.ratCast then
              let argsReduced := boundReduced.getAppArgs
              if argsReduced.size > 0 then
                return argsReduced.back!
              else
                throwError "Unexpected reduced coercion structure"
            else
              throwError m!"Cannot extract rational from bound: {bound}\n\
                            Type: {boundTy}\n\n\
                            This happens when the bound contains non-computable constants\n\
                            (e.g., Real.pi, Real.sqrt 2, or complex expressions).\n\
                            Suggestions:\n\
                            • Use a rational approximation (e.g., 3.15 instead of Real.pi)\n\
                            • Use interval_decide for point inequalities with transcendentals"

  /-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
  getAst (func : Lean.Expr) : TacticM Lean.Expr := do
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
          return args[1]!
        else
          throwError m!"Unexpected Expr.eval application structure.\n\
                        Expected: Expr.eval env ast\n\
                        Got {args.size} arguments: {args.toList}"
      else
        -- It's a raw expression - reify it
        reify func

  /-- Try to generate ExprSupportedCore proof, falling back to ExprSupportedWithInv if needed.
      Returns (supportProof, useWithInv) where useWithInv is true if we used WithInv. -/
  getSupportProof (ast : Lean.Expr) : TacticM (Lean.Expr × Bool) := do
    try
      let proof ← mkSupportedCoreProof ast
      return (proof, false)
    catch _ =>
      let proof ← mkSupportedWithInvProof ast
      return (proof, true)

  /-- Prove ∀ x ∈ I, f x ≤ c -/
  proveForallLe (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      -- 1. Get AST (either from Expr.eval or by reifying)
      let ast ← getAst func

      -- 2. Extract rational bound from possible coercion
      let boundRat ← extractRatBound bound

      -- 3. Generate support proof (tries Core first, falls back to WithInv for log/inv)
      let (supportProof, useWithInv) ← getSupportProof ast

      -- 4. Build config expression
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- 5. Apply appropriate theorem based on interval source and support type
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_upper_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_upper_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  let goalsEmpty := (← getGoals).isEmpty
                  return goalsEmpty
                catch _ =>
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, so we need to use convert
            setGoals [goal]

            -- Build the certificate expression (using appropriate check function)
            -- Note: WithInv check functions don't take a cfg parameter
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkUpperBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkUpperBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof that checkUpperBound ... = true using native_decide via an auxiliary goal
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal

            -- Apply the theorem with the certificate to get the conclusion
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

            -- Now use convert on the conclusion (not the full proof)
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))

            -- Close side goals (usually equality goals for Set.Icc and bounds)
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  -- Check if goal is now assigned/closed
                  let goalsEmpty := (← getGoals).isEmpty
                  return goalsEmpty
                catch _ =>
                  return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              -- For Set.Icc equality, use congr_arg with norm_num
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle decimal bounds (2.72 = ↑(Rat.divInt 68 25))
              -- norm_num converts 2.72 to 68/25, then simp+push_cast closes the equality
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              -- Last resort - leave the goal for the user but warn
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate verify_upper_bound theorem
          let proof ← if useWithInv then
            mkAppM ``verify_upper_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_upper_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            evalTactic (← `(tactic| native_decide))

  /-- Prove ∀ x ∈ I, c ≤ f x -/
  proveForallGe (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let (supportProof, useWithInv) ← getSupportProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- Handle based on interval source
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_lower_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_lower_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  let goalsEmpty := (← getGoals).isEmpty
                  return goalsEmpty
                catch _ =>
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkLowerBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkLowerBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof using native_decide via an auxiliary goal
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal

            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))

            -- Close side goals
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  -- Check if goal is now assigned/closed
                  if (← getGoals).isEmpty then return true
                  return false
                catch _ => return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle decimal bounds (2.72 = ↑(Rat.divInt 68 25)) - fallback tactics
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate verify_lower_bound theorem
          let proof ← if useWithInv then
            mkAppM ``verify_lower_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_lower_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            evalTactic (← `(tactic| native_decide))

  /-- Prove ∀ x ∈ I, f x < c -/
  proveForallLt (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let (supportProof, useWithInv) ← getSupportProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- Handle based on interval source
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_strict_upper_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_strict_upper_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  let goalsEmpty := (← getGoals).isEmpty
                  return goalsEmpty
                catch _ =>
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkStrictUpperBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkStrictUpperBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof using native_decide via an auxiliary goal
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal

            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))

            -- Close side goals
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  -- Check if goal is now assigned/closed
                  if (← getGoals).isEmpty then return true
                  return false
                catch _ => return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle decimal bounds - fallback tactics
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate theorem
          let proof ← if useWithInv then
            mkAppM ``verify_strict_upper_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_strict_upper_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            try
              evalTactic (← `(tactic| native_decide))
            catch _ =>
              try
                evalTactic (← `(tactic| norm_cast))
              catch _ =>
                evalTactic (← `(tactic| simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast]))

  /-- Prove ∀ x ∈ I, c < f x -/
  proveForallGt (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let (supportProof, useWithInv) ← getSupportProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- Handle based on interval source
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_strict_lower_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_strict_lower_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  let goalsEmpty := (← getGoals).isEmpty
                  return goalsEmpty
                catch _ =>
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkStrictLowerBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkStrictLowerBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof using native_decide via an auxiliary goal
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal

            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))

            -- Close side goals
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                try
                  tac
                  -- Check if goal is now assigned/closed
                  if (← getGoals).isEmpty then return true
                  return false
                catch _ => return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle decimal bounds - fallback tactics
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate theorem
          let proof ← if useWithInv then
            mkAppM ``verify_strict_lower_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_strict_lower_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            try
              evalTactic (← `(tactic| native_decide))
            catch _ =>
              try
                evalTactic (← `(tactic| norm_cast))
              catch _ =>
                evalTactic (← `(tactic| simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast]))

/-! ## Tactic Syntax -/

/-- The certify_bound tactic.

    Automatically proves bounds on expressions using interval arithmetic.

    Usage:
    - `certify_bound` - uses adaptive precision (tries depths 10, 15, 20, 25, 30)
    - `certify_bound 20` - uses fixed Taylor depth of 20

    Supports goals of the form:
    - `∀ x ∈ I, f x ≤ c`
    - `∀ x ∈ I, c ≤ f x`
    - `∀ x ∈ I, f x < c`
    - `∀ x ∈ I, c < f x`

    Note: `interval_bound` is an alias for backward compatibility.
-/
elab "certify_bound" depth:(num)? : tactic => do
  match depth with
  | some n =>
    -- Fixed depth specified by user
    intervalBoundCore n.getNat
  | none =>
    -- Adaptive: try increasing depths until success
    let depths := [10, 15, 20, 25, 30]
    let _goal ← getMainGoal
    let goalState ← saveState
    let mut lastError : Option Exception := none
    for d in depths do
      try
        restoreState goalState
        trace[interval_decide] "Trying Taylor depth {d}..."
        intervalBoundCore d
        trace[interval_decide] "Success with Taylor depth {d}"
        return  -- Success!
      catch e =>
        lastError := some e
        continue
    -- All depths failed - run diagnostics and report enriched error
    match lastError with
    | some e =>
      -- Restore state and try to parse goal for diagnostics
      restoreState goalState
      let diagMsg ← try
        -- Apply same preprocessing as intervalBoundCore for consistent parsing
        try
          evalTactic (← `(tactic| intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
        catch _ =>
          try evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
          catch _ => pure ()
        try
          evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one] at *))
        catch _ => pure ()

        let goal ← getMainGoal
        let goalType ← goal.getType
        let boundGoalOpt ← parseBoundGoal goalType
        runShadowDiagnostic boundGoalOpt goalType
      catch _ =>
        pure m!"(Could not run diagnostics)"

      throwError m!"{e.toMessageData}\n\n{diagMsg}"
    | none => throwError "certify_bound: All precision levels failed"

/-- Backward-compatible alias for certify_bound -/
macro "interval_bound" depth:(num)? : tactic => `(tactic| certify_bound $[$depth]?)

/-! ## Multivariate Bounds Tactic

The `multivariate_bound` tactic handles goals with multiple quantified variables:
- `∀ x ∈ I, ∀ y ∈ J, f(x, y) ≤ c`
- `∀ x ∈ I, ∀ y ∈ J, c ≤ f(x, y)`

This uses the global optimization theorems (verify_global_upper_bound/verify_global_lower_bound)
from Validity/Bounds.lean, which operate over Box (List IntervalRat) domains.
-/

open LeanCert.Engine.Optimization in
/-- Information about a quantified variable and its interval -/
structure VarIntervalInfo where
  /-- Variable name -/
  varName : Name
  /-- Variable type -/
  varType : Lean.Expr
  /-- Extracted interval (lo, hi rationals and their expressions) -/
  intervalRat : Lean.Expr
  /-- Original lower bound expression for Set.Icc -/
  loExpr : Lean.Expr
  /-- Original upper bound expression for Set.Icc -/
  hiExpr : Lean.Expr
  /-- Low bound as rational -/
  lo : ℚ
  /-- High bound as rational -/
  hi : ℚ
  deriving Repr, Inhabited

open LeanCert.Engine.Optimization in
/-- Result of analyzing a multivariate bound goal -/
inductive MultivariateBoundGoal where
  /-- ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, f(x₁,...,xₙ) ≤ c -/
  | forallLe (vars : Array VarIntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, c ≤ f(x₁,...,xₙ) -/
  | forallGe (vars : Array VarIntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

/-- Try to extract interval info from a Set.Icc membership type -/
private def extractIntervalFromSetIcc (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option VarIntervalInfo) := do
  -- memTy should be x ∈ Set.Icc lo hi
  match_expr memTy with
  | Membership.mem _ _ _ interval xExpr =>
    if ← isDefEq xExpr x then
      let fn := interval.getAppFn
      let args := interval.getAppArgs
      if fn.isConstOf ``Set.Icc then
        if args.size >= 4 then
          let loExpr := args[2]!
          let hiExpr := args[3]!
          if let some lo ← extractRatFromReal loExpr then
            if let some hi ← extractRatFromReal hiExpr then
              let loRatExpr := toExpr lo
              let hiRatExpr := toExpr hi
              -- Build proof that lo ≤ hi
              let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
              let leProof ← mkDecideProof leProofTy
              let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
              let xTy ← inferType x
              let varName ← do
                match x with
                | .fvar fv => pure (← fv.getDecl).userName
                | _ => pure `x
              return some {
                varName := varName
                varType := xTy
                intervalRat := intervalRat
                loExpr := loExpr
                hiExpr := hiExpr
                lo := lo
                hi := hi
              }
      return none
    else return none
  | _ => return none

/-- Try to extract interval info from an IntervalRat membership type -/
private def extractIntervalFromIntervalRat (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option VarIntervalInfo) := do
  match_expr memTy with
  | Membership.mem _ _ _ interval xExpr =>
    if ← isDefEq xExpr x then
      let intervalTy ← inferType interval
      if intervalTy.isConstOf ``IntervalRat then
        -- Try to extract lo and hi from the IntervalRat structure
        -- For now, we'll assume the interval is already in the right form
        let xTy ← inferType x
        let varName ← do
          match x with
          | .fvar fv => pure (← fv.getDecl).userName
          | _ => pure `x
        let loExpr ← mkAppM ``IntervalRat.lo #[interval]
        let hiExpr ← mkAppM ``IntervalRat.hi #[interval]
        return some {
          varName := varName
          varType := xTy
          intervalRat := interval
          loExpr := loExpr
          hiExpr := hiExpr
          lo := 0  -- Placeholder - we don't need these for non-Set.Icc
          hi := 1  -- Placeholder
        }
      return none
    else return none
  | _ => return none

/-- Recursively parse a multivariate bound goal, collecting variables and intervals.
    This processes all quantifiers within nested withLocalDeclD scopes so that
    fvars remain valid for mkLambdaFVars. -/
partial def parseMultivariateBoundGoal (goal : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
  -- We need to work within the withLocalDeclD scopes, so we'll return a function that
  -- builds the result while fvars are still valid.
  -- First, instantiate any metavariables (e.g., from refine/apply) to get the actual goal.
  let goal ← instantiateMVars goal
  let goal ← if goal.isForall then
    pure goal
  else
    whnf goal
  let extractLowerBound (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memTy with
    | LE.le _ _ lo xExpr =>
      if ← isDefEq xExpr x then
        return some lo
      return none
    | _ => return none

  let extractUpperBound (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memTy with
    | LE.le _ _ xExpr hi =>
      if ← isDefEq xExpr x then
        return some hi
      return none
    | _ => return none

  let extractBoundsFromAnd (memTy : Lean.Expr) (x : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match_expr memTy with
    | And a b =>
      if let some lo ← extractLowerBound a x then
        if let some hi ← extractUpperBound b x then
          return some (lo, hi)
      if let some lo ← extractLowerBound b x then
        if let some hi ← extractUpperBound a x then
          return some (lo, hi)
      return none
    | _ => return none

  let mkVarIntervalInfoFromBounds (x : Lean.Expr) (loExpr hiExpr : Lean.Expr) :
      MetaM (Option VarIntervalInfo) := do
    if let some lo ← extractRatFromReal loExpr then
      if let some hi ← extractRatFromReal hiExpr then
        let xTy ← inferType x
        let varName ← do
          match x with
          | .fvar fv => pure (← fv.getDecl).userName
          | _ => pure `x
        let loRatExpr := toExpr lo
        let hiRatExpr := toExpr hi
        let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
        let leProof ← mkDecideProof leProofTy
        let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
        return some {
          varName := varName
          varType := xTy
          intervalRat := intervalRat
          loExpr := loExpr
          hiExpr := hiExpr
          lo := lo
          hi := hi
        }
    return none

  let memCandidates (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
    let eWhnf ← withTransparency TransparencyMode.all <| whnf e
    if eWhnf == e then
      return #[e]
    return #[e, eWhnf]

  let rec findSome (cands : List Lean.Expr)
      (f : Lean.Expr → MetaM (Option MultivariateBoundGoal)) :
      MetaM (Option MultivariateBoundGoal) := do
    match cands with
    | [] => return none
    | cand :: rest =>
      if let some goal ← f cand then
        return some goal
      findSome rest f

  let rec collect (e : Lean.Expr) (acc : Array VarIntervalInfo) (fvars : Array Lean.Expr) :
      MetaM (Option MultivariateBoundGoal) := do
    -- Don't use whnf at the top level - it might destroy the forall structure
    if !e.isForall then
      -- We've reached the inner body - process the comparison
      if acc.isEmpty then
        return none  -- No quantified variables found

      -- Match the comparison
      match_expr e with
      | LE.le _ _ lhs rhs =>
        -- Build the function as a lambda over all bound variables
        let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
        let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
        if lhsHasVars && !rhsHasVars then
          let func ← mkLambdaFVars fvars lhs
          return some (.forallLe acc func rhs)
        else if rhsHasVars && !lhsHasVars then
          let func ← mkLambdaFVars fvars rhs
          return some (.forallGe acc func lhs)
        else
          return none
      | GE.ge _ _ lhs rhs =>
        let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
        let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
        if lhsHasVars && !rhsHasVars then
          let func ← mkLambdaFVars fvars lhs
          return some (.forallGe acc func rhs)
        else if rhsHasVars && !lhsHasVars then
          let func ← mkLambdaFVars fvars rhs
          return some (.forallLe acc func lhs)
        else
          return none
      | _ => return none

    let .forallE name ty body _ := e | return none

    -- Introduce the variable (stay in this scope for the rest of parsing)
    withLocalDeclD name ty fun x => do
      let body := body.instantiate1 x

      -- Check if this is a membership quantifier (x ∈ I → ...)
      if body.isForall then
        let .forallE _ memTy innerBody _ := body | return none

        -- Try to extract interval from membership (don't whnf memTy)
        if let some info ← extractIntervalFromSetIcc memTy x then
          withLocalDeclD `_ memTy fun _hx => do
            let nextBody := innerBody.instantiate1 _hx
            collect nextBody (acc.push info) (fvars.push x)
        else if let some info ← extractIntervalFromIntervalRat memTy x then
          withLocalDeclD `_ memTy fun _hx => do
            let nextBody := innerBody.instantiate1 _hx
            collect nextBody (acc.push info) (fvars.push x)
        else
          let memTyCandidates ← memCandidates memTy
          -- Handle conjunction form: (lo ≤ x ∧ x ≤ hi) → ...
          let tryAnd (memTyCand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
            if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTyCand x then
              if let some info ← mkVarIntervalInfoFromBounds x loExpr hiExpr then
                return ← withLocalDeclD `_ memTy fun _hx => do
                  let nextBody := innerBody.instantiate1 _hx
                  collect nextBody (acc.push info) (fvars.push x)
            return none
          if let some result ← findSome memTyCandidates.toList tryAnd then
            return some result
          -- Handle expanded bounds: lo ≤ x → x ≤ hi → ...
          let tryLower (memTyCand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
            if let some loExpr ← extractLowerBound memTyCand x then
              return ← withLocalDeclD `_ memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Candidates ← memCandidates memTy2
                  let tryUpper (memTy2Cand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
                    if let some hiExpr ← extractUpperBound memTy2Cand x then
                      if let some info ← mkVarIntervalInfoFromBounds x loExpr hiExpr then
                        return ← withLocalDeclD `_ memTy2 fun _hx2 => do
                          let nextBody := innerBody2.instantiate1 _hx2
                          collect nextBody (acc.push info) (fvars.push x)
                    return none
                  return ← findSome memTy2Candidates.toList tryUpper
                return none
            return none
          let tryUpper (memTyCand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
            if let some hiExpr ← extractUpperBound memTyCand x then
              return ← withLocalDeclD `_ memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Candidates ← memCandidates memTy2
                  let tryLower (memTy2Cand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
                    if let some loExpr ← extractLowerBound memTy2Cand x then
                      if let some info ← mkVarIntervalInfoFromBounds x loExpr hiExpr then
                        return ← withLocalDeclD `_ memTy2 fun _hx2 => do
                          let nextBody := innerBody2.instantiate1 _hx2
                          collect nextBody (acc.push info) (fvars.push x)
                    return none
                  return ← findSome memTy2Candidates.toList tryLower
                return none
            return none
          if let some result ← findSome memTyCandidates.toList tryLower then
            return some result
          if let some result ← findSome memTyCandidates.toList tryUpper then
            return some result
          -- Not a membership quantifier, treat as the inner body
          if acc.isEmpty then
            return none
          match_expr body with
          | LE.le _ _ lhs rhs =>
            let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
            let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
            if lhsHasVars && !rhsHasVars then
              let func ← mkLambdaFVars fvars lhs
              return some (.forallLe acc func rhs)
            else if rhsHasVars && !lhsHasVars then
              let func ← mkLambdaFVars fvars rhs
              return some (.forallGe acc func lhs)
            else
              return none
          | GE.ge _ _ lhs rhs =>
            let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
            let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
            if lhsHasVars && !rhsHasVars then
              let func ← mkLambdaFVars fvars lhs
              return some (.forallGe acc func rhs)
            else if rhsHasVars && !lhsHasVars then
              let func ← mkLambdaFVars fvars rhs
              return some (.forallLe acc func lhs)
            else
              return none
          | _ => return none
      else
        -- No more foralls - process comparison within current scope
        if acc.isEmpty then
          return none
        match_expr body with
        | LE.le _ _ lhs rhs =>
          let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
          let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
          if lhsHasVars && !rhsHasVars then
            let func ← mkLambdaFVars fvars lhs
            return some (.forallLe acc func rhs)
          else if rhsHasVars && !lhsHasVars then
            let func ← mkLambdaFVars fvars rhs
            return some (.forallGe acc func lhs)
          else
            return none
        | GE.ge _ _ lhs rhs =>
          let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
          let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
          if lhsHasVars && !rhsHasVars then
            let func ← mkLambdaFVars fvars lhs
            return some (.forallGe acc func rhs)
          else if rhsHasVars && !lhsHasVars then
            let func ← mkLambdaFVars fvars rhs
            return some (.forallLe acc func lhs)
          else
            return none
        | _ => return none

  collect goal #[] #[]

/-- Build a Box expression (List IntervalRat) from an array of VarIntervalInfo -/
def mkBoxExpr (infos : Array VarIntervalInfo) : MetaM Lean.Expr := do
  let intervalRatType := Lean.mkConst ``IntervalRat
  let intervals := infos.map (·.intervalRat)
  mkListLit intervalRatType intervals.toList

open LeanCert.Engine.Optimization in
open LeanCert.Validity.GlobalOpt in
/-- The main multivariate_bound tactic implementation -/
def multivariateBoundCore (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
  intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType
  trace[LeanCert.discovery] "multivariate_bound goal: {goalType}"

  -- Parse the multivariate goal
  let parsed ← parseMultivariateBoundGoal goalType
  let some boundGoal := parsed
    | let diagReport ← mkDiagnosticReport "multivariate_bound" goalType "parse"
        (some m!"Expected forms:\n\
                 • ∀ x ∈ I, ∀ y ∈ J, ... f(x,y,...) ≤ c\n\
                 • ∀ x ∈ I, ∀ y ∈ J, ... c ≤ f(x,y,...)\n\n\
                 Domain formats accepted:\n\
                 • x ∈ Set.Icc a b\n\
                 • a ≤ x ∧ x ≤ b\n\
                 • a ≤ x → x ≤ b → ...")
      throwError "multivariate_bound: Could not parse goal as multivariate bound.\n\n{diagReport}"

  match boundGoal with
  | .forallLe vars func bound =>
    proveMultivariateLe goal vars func bound maxIters tolerance useMonotonicity taylorDepth
  | .forallGe vars func bound =>
    proveMultivariateGe goal vars func bound maxIters tolerance useMonotonicity taylorDepth

where
  /-- Extract rational bound from possible coercion (reusing logic from intervalBoundCore) -/
  extractRatBound (bound : Lean.Expr) : TacticM Lean.Expr := do
    let fn := bound.getAppFn
    let args := bound.getAppArgs

    -- Check for Rat.cast (which is what ↑ becomes for ℚ → ℝ)
    if fn.isConstOf ``Rat.cast then
      if args.size > 0 then
        return args.back!
      else
        throwError "Unexpected Rat.cast structure"
    else if fn.isConstOf ``RatCast.ratCast then
      if args.size > 0 then
        return args.back!
      else
        throwError "Unexpected RatCast.ratCast structure"
    else
      let boundTy ← inferType bound
      if boundTy.isConstOf ``Rat then
        return bound
      else
        if let some q ← extractRatFromReal bound then
          return toExpr q
        else
          let boundReduced ← whnf bound
          let fnReduced := boundReduced.getAppFn
          if fnReduced.isConstOf ``Rat.cast || fnReduced.isConstOf ``RatCast.ratCast then
            let argsReduced := boundReduced.getAppArgs
            if argsReduced.size > 0 then
              return argsReduced.back!
          throwError m!"Cannot extract rational from bound: {bound}\n\n\
                        This happens when the bound contains non-computable constants.\n\
                        Suggestions:\n\
                        • Use a rational approximation\n\
                        • Use interval_decide for point inequalities with transcendentals"

  /-- Fetch local variable expressions in the order of VarIntervalInfo. -/
  getVarExprs (vars : Array VarIntervalInfo) : TacticM (Array Lean.Expr) := do
    let lctx ← getLCtx
    let mut out : Array Lean.Expr := #[]
    let mut used : Array Lean.FVarId := #[]
    for info in vars do
      match lctx.findFromUserName? info.varName with
      | some decl =>
          out := out.push (Lean.mkFVar decl.fvarId)
          used := used.push decl.fvarId
      | none =>
          let mut fallback : Option Lean.LocalDecl := none
          for decl in lctx do
            if !(used.any (fun id => id == decl.fvarId)) then
              if (← isDefEq decl.type info.varType) then
                fallback := some decl
                break
          match fallback with
          | some decl =>
              out := out.push (Lean.mkFVar decl.fvarId)
              used := used.push decl.fvarId
          | none =>
              throwError m!"multivariate_bound: missing local {info.varName}"
    return out

  /-- Build an environment function ρ from a list of variables. -/
  mkEnvExpr (varsListExpr : Lean.Expr) : TacticM Lean.Expr := do
    withLocalDeclD `i (Lean.mkConst ``Nat) fun i => do
      let zeroRat := toExpr (0 : ℚ)
      let zeroReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, zeroRat]
      let body ← mkAppM ``List.getD #[varsListExpr, i, zeroReal]
      mkLambdaFVars #[i] body

  /-- Prove ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, f(x) ≤ c using verify_global_upper_bound -/
  proveMultivariateLe (goal : MVarId) (vars : Array VarIntervalInfo) (func bound : Lean.Expr)
      (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      -- 1. Build Box expression
      let boxExpr ← mkBoxExpr vars

      -- 2. Reify the function to AST
      let ast ← reify func

      -- 3. Extract rational bound
      let boundRat ← extractRatBound bound

      -- 4. Generate support proof
      let supportProof ← mkSupportedCoreProof ast

      -- 5. Build config expression
      let cfgExpr ← mkAppM ``GlobalOptConfig.mk #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity, toExpr taylorDepth]

      -- 6. Apply verify_global_upper_bound theorem
      -- The theorem has signature:
      -- verify_global_upper_bound (e : Expr) (hsupp : ExprSupportedCore e) (B : Box) (c : ℚ) (cfg : GlobalOptConfig)
      --   (h_cert : checkGlobalUpperBound e B c cfg = true) :
      --   ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → Expr.eval ρ e ≤ c
      let proof ← mkAppM ``verify_global_upper_bound #[ast, supportProof, boxExpr, boundRat, cfgExpr]

      -- 7. We need to prove the certificate check (checkGlobalUpperBound e B c cfg = true)
      -- Then apply the result to close the goal

      -- The goal after applying the theorem will need:
      -- - h_cert: checkGlobalUpperBound e B c cfg = true  (provable by native_decide)
      -- Then we need to "intro" the quantifiers and convert Set.Icc membership to Box.envMem

      -- For now, we'll use a direct approach: intro all vars and hypotheses, then apply the theorem
      setGoals [goal]

      -- Intro all binders (variables and hypotheses) in order.
      try
        evalTactic (← `(tactic| repeat intro))
      catch _ => pure ()

      let mainGoalAfterIntro ← getMainGoal

      let (rhoSyntax, varsListSyntax, boxSyntax) ← withMainContext do
        let varExprs ← getVarExprs vars
        let varsListExpr ← mkListLit (Lean.mkConst ``Real) varExprs.toList
        let rhoExpr ← mkEnvExpr varsListExpr
        let rhoSyntax ← Lean.Elab.Term.exprToSyntax rhoExpr
        let varsListSyntax ← Lean.Elab.Term.exprToSyntax varsListExpr
        let boxSyntax ← Lean.Elab.Term.exprToSyntax boxExpr
        return (rhoSyntax, varsListSyntax, boxSyntax)

      -- Now build the environment function and proofs
      -- We need to prove Box.envMem ρ B and ∀ i ≥ B.length, ρ i = 0
      -- where ρ i = x_i for i < n and ρ i = 0 for i ≥ n

      -- Build the final proof using convert
      let checkExpr ← mkAppM ``checkGlobalUpperBound #[ast, boxExpr, boundRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      setGoals [certGoalId]
      try
        evalTactic (← `(tactic| native_decide))
      catch e =>
        throwError "multivariate_bound: Certificate check failed. The bound may be too tight.\n{e.toMessageData}"

      let conclusionProof ← mkAppM' proof #[certGoal]
      let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

      setGoals [mainGoalAfterIntro]
      evalTactic (← `(tactic| exact (by
        have hmem : Box.envMem $rhoSyntax $boxSyntax := by
          intro i
          fin_cases i <;>
            simp [Box.envMem, IntervalRat.mem_iff_mem_Icc, Set.mem_Icc] at * <;>
            first | assumption | constructor <;> assumption
        have hzero : ∀ i, i ≥ ($boxSyntax).length → $rhoSyntax i = 0 := by
          intro i hi
          have hnot : ¬ i < ($boxSyntax).length := by exact not_lt.mpr hi
          have hnot' : ¬ i < ($varsListSyntax).length := by
            simpa using hnot
          have hge' : ($varsListSyntax).length ≤ i := by
            exact not_lt.mp hnot'
          simp [List.getD, List.getElem?_eq_none hge', Option.getD]
        exact $conclusionTerm $rhoSyntax hmem hzero
      )))

  /-- Prove ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, c ≤ f(x) using verify_global_lower_bound -/
  proveMultivariateGe (goal : MVarId) (vars : Array VarIntervalInfo) (func bound : Lean.Expr)
      (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      -- Similar to proveMultivariateLe but with verify_global_lower_bound
      let boxExpr ← mkBoxExpr vars
      let ast ← reify func
      let boundRat ← extractRatBound bound
      let supportProof ← mkSupportedCoreProof ast
      let cfgExpr ← mkAppM ``GlobalOptConfig.mk #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity, toExpr taylorDepth]

      let proof ← mkAppM ``verify_global_lower_bound #[ast, supportProof, boxExpr, boundRat, cfgExpr]

      setGoals [goal]

      -- Intro all binders (variables and hypotheses) in order.
      try
        evalTactic (← `(tactic| repeat intro))
      catch _ => pure ()

      let mainGoalAfterIntro ← getMainGoal

      let (rhoSyntax, varsListSyntax, boxSyntax) ← withMainContext do
        let varExprs ← getVarExprs vars
        let varsListExpr ← mkListLit (Lean.mkConst ``Real) varExprs.toList
        let rhoExpr ← mkEnvExpr varsListExpr
        let rhoSyntax ← Lean.Elab.Term.exprToSyntax rhoExpr
        let varsListSyntax ← Lean.Elab.Term.exprToSyntax varsListExpr
        let boxSyntax ← Lean.Elab.Term.exprToSyntax boxExpr
        return (rhoSyntax, varsListSyntax, boxSyntax)

      let checkExpr ← mkAppM ``checkGlobalLowerBound #[ast, boxExpr, boundRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      setGoals [certGoalId]
      try
        evalTactic (← `(tactic| native_decide))
      catch e =>
        throwError "multivariate_bound: Certificate check failed. The bound may be too tight.\n{e.toMessageData}"

      let conclusionProof ← mkAppM' proof #[certGoal]
      let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

      setGoals [mainGoalAfterIntro]
      evalTactic (← `(tactic| exact (by
        have hmem : Box.envMem $rhoSyntax $boxSyntax := by
          intro i
          fin_cases i <;>
            simp [Box.envMem, IntervalRat.mem_iff_mem_Icc, Set.mem_Icc] at * <;>
            first | assumption | constructor <;> assumption
        have hzero : ∀ i, i ≥ ($boxSyntax).length → $rhoSyntax i = 0 := by
          intro i hi
          have hnot : ¬ i < ($boxSyntax).length := by exact not_lt.mpr hi
          have hnot' : ¬ i < ($varsListSyntax).length := by
            simpa using hnot
          have hge' : ($varsListSyntax).length ≤ i := by
            exact not_lt.mp hnot'
          simp [List.getD, List.getElem?_eq_none hge', Option.getD]
        exact $conclusionTerm $rhoSyntax hmem hzero
      )))

/-- The multivariate_bound tactic.

    Automatically proves bounds on multivariate expressions using global optimization.

    Usage:
    - `multivariate_bound` - uses defaults (1000 iterations, tolerance 1/1000, Taylor depth 10)
    - `multivariate_bound 2000` - uses 2000 iterations

    Supports goals of the form:
    - `∀ x ∈ I, ∀ y ∈ J, f(x,y) ≤ c`
    - `∀ x ∈ I, ∀ y ∈ J, c ≤ f(x,y)`
-/
elab "multivariate_bound" iters:(num)? : tactic => do
  let maxIters := match iters with
    | some n => n.getNat
    | none => 1000
  multivariateBoundCore maxIters (1/1000) false 10

/-! ## Global Optimization Tactic

The `opt_bound` tactic handles goals of the form:
- `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → c ≤ Expr.eval ρ e`
- `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → Expr.eval ρ e ≤ c`

This uses global branch-and-bound optimization with optional monotonicity pruning.
-/

/-- Skip through foralls (from ≥ binder notation) to get to the final comparison -/
partial def skipForallsAux (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  if e.isForall then
    let .forallE _ _ body _ := e | return e
    skipForallsAux body
  else
    return e

open LeanCert.Engine.Optimization in
/-- Result of analyzing a global bound goal -/
inductive GlobalBoundGoal where
  /-- ∀ ρ ∈ B, (zero extension) → c ≤ f(ρ) -/
  | globalGe (box : Lean.Expr) (expr : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ ρ ∈ B, (zero extension) → f(ρ) ≤ c -/
  | globalLe (box : Lean.Expr) (expr : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

/-- Check if expression is Expr.eval (checking both short and full names) -/
def isExprEval (e : Lean.Expr) : Bool :=
  let fn := e.getAppFn
  fn.isConstOf ``LeanCert.Core.Expr.eval || fn.isConstOf ``Expr.eval

/-- Check if name ends with Expr.eval -/
def isExprEvalName (name : Lean.Name) : Bool :=
  (`Expr.eval).isSuffixOf name

/-- Try to parse an already-intro'd goal as a global optimization bound.
    After intro ρ hρ hzero, the goal should be a comparison: Expr.eval ρ e ≤ c or c ≤ Expr.eval ρ e -/
def parseSimpleBoundGoal (goal : Lean.Expr) : MetaM (Option GlobalBoundGoal) := do
  let goal ← whnf goal
  -- Check if it's an application of LE.le
  let fn := goal.getAppFn
  let args := goal.getAppArgs
  if let .const name _ := fn then
    -- Should be LE.le or a variant
    if name == ``LE.le && args.size ≥ 4 then
      -- args are: [type, inst, lhs, rhs]
      let lhs := args[2]!
      let rhs := args[3]!
      -- Check if lhs is Expr.eval
      let lhsFn := lhs.getAppFn
      if let .const lhsName _ := lhsFn then
        if isExprEvalName lhsName then
          let lhsArgs := lhs.getAppArgs
          if lhsArgs.size ≥ 2 then
            return some (.globalLe (Lean.mkConst ``Unit) lhsArgs[1]! rhs)
      -- Check if rhs is Expr.eval
      let rhsFn := rhs.getAppFn
      if let .const rhsName _ := rhsFn then
        if isExprEvalName rhsName then
          let rhsArgs := rhs.getAppArgs
          if rhsArgs.size ≥ 2 then
            return some (.globalGe (Lean.mkConst ``Unit) rhsArgs[1]! lhs)
  return none

open LeanCert.Engine.Optimization in
/-- Build a GlobalOptConfig expression -/
def mkGlobalOptConfigExpr (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : MetaM Lean.Expr := do
  mkAppM ``GlobalOptConfig.mk #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity, toExpr taylorDepth]

open LeanCert.Engine.Optimization in
/-- The main opt_bound tactic implementation -/
def optBoundCore (maxIters : Nat) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
  -- Apply verify_global_upper_bound or verify_global_lower_bound using plain apply
  -- Let Lean figure out the unification

  let cfgExpr ← mkGlobalOptConfigExpr maxIters ((1 : ℚ)/1000) useMonotonicity taylorDepth

  -- First try applying upper bound theorem (for f(ρ) ≤ c goals)
  let goal ← getMainGoal
  try
    let proof ← mkAppOptM ``LeanCert.Validity.GlobalOpt.verify_global_upper_bound
      #[none, none, none, none, some cfgExpr]
    let newGoals ← goal.apply proof
    setGoals newGoals
    -- Now prove the remaining goals: hsupp and h_cert
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let gType ← g.getType
      -- Check if this is a support goal or a decidable goal
      if gType.getAppFn.isConstOf ``ExprSupportedCore then
        -- Generate support proof
        proveSupport g
      else
        evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  -- Try lower bound theorem (for c ≤ f(ρ) goals)
  let goal ← getMainGoal
  try
    let proof ← mkAppOptM ``LeanCert.Validity.GlobalOpt.verify_global_lower_bound
      #[none, none, none, none, some cfgExpr]
    let newGoals ← goal.apply proof
    setGoals newGoals
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let gType ← g.getType
      if gType.getAppFn.isConstOf ``ExprSupportedCore then
        proveSupport g
      else
        evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  throwError "opt_bound: Could not apply global bound theorem. Check that goal has form:\n\
              • ∀ ρ, Box.envMem ρ B → (∀ i ≥ B.length, ρ i = 0) → c ≤ Expr.eval ρ e\n\
              • ∀ ρ, Box.envMem ρ B → (∀ i ≥ B.length, ρ i = 0) → Expr.eval ρ e ≤ c"

where
  /-- Prove ExprSupportedCore goal by generating the proof -/
  proveSupport (goal : MVarId) : TacticM Unit := do
    goal.withContext do
      let gType ← goal.getType
      -- gType should be ExprSupportedCore e for some e
      let args := gType.getAppArgs
      if args.size ≥ 1 then
        let expr := args[0]!
        let proof ← mkSupportedCoreProof expr
        goal.assign proof

/-- The opt_bound tactic.

    Automatically proves global bounds on expressions over boxes using
    branch-and-bound optimization.

    Usage:
    - `opt_bound` - uses defaults (1000 iterations, no monotonicity, Taylor depth 10)
    - `opt_bound 2000` - uses 2000 iterations
    - `opt_bound 1000 mono` - enables monotonicity pruning

    Supports goals of the form:
    - `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → c ≤ Expr.eval ρ e`
    - `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → Expr.eval ρ e ≤ c`
-/
elab "opt_bound" iters:(num)? mono:("mono")? : tactic => do
  let maxIters := match iters with
    | some n => n.getNat
    | none => 1000
  let useMonotonicity := mono.isSome
  optBoundCore maxIters useMonotonicity 10

/-! ## Root Finding Tactic

The `root_bound` tactic handles goals related to root finding:
- `∀ x ∈ I, f x ≠ 0` (no root exists) - uses verify_no_root
-/

/-- Result of analyzing a root finding goal -/
inductive RootGoal where
  /-- ∀ x ∈ I, f x ≠ 0 -/
  | forallNeZero (varName : Name) (interval : Lean.Expr) (func : Lean.Expr)
  deriving Repr

/-- Try to parse a goal as a root finding goal -/
def parseRootGoal (goal : Lean.Expr) : MetaM (Option RootGoal) := do
  let goal ← whnf goal

  -- Check for ∀ x, x ∈ I → f x ≠ 0
  if goal.isForall then
    let .forallE name ty body _ := goal | return none

    withLocalDeclD name ty fun x => do
      let body := body.instantiate1 x
      let body ← whnf body
      if body.isForall then
        let .forallE _ memTy innerBody _ := body | return none

        -- Extract interval from membership
        let interval? ← extractInterval memTy x
        let some interval := interval? | return none

        -- innerBody should be f x ≠ 0 (which is f x = 0 → False)
        withLocalDeclD `hx memTy fun _hx => do
          let neqExpr := innerBody.instantiate1 _hx

          -- Try to match Ne (f x) 0 or f x ≠ 0
          match_expr neqExpr with
          | Ne _ lhs _rhs =>
            -- Check if lhs (the function value) depends on x
            let lhsHasX := lhs.containsFVar x.fvarId!
            if lhsHasX then
              return some (.forallNeZero name interval (← mkLambdaFVars #[x] lhs))
            else
              return none
          | _ =>
            -- Also check for Not (Eq ...)
            match_expr neqExpr with
            | Not eqExpr =>
              match_expr eqExpr with
              | Eq _ lhs _rhs =>
                let lhsHasX := lhs.containsFVar x.fvarId!
                if lhsHasX then
                  return some (.forallNeZero name interval (← mkLambdaFVars #[x] lhs))
                else
                  return none
              | _ => return none
            | _ => return none
      else
        return none
  else
    return none

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

  extractBoundsFromAnd (memTy : Lean.Expr) (x : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match_expr memTy with
    | And a b =>
      if let some lo ← extractLowerBound a x then
        if let some hi ← extractUpperBound b x then
          return some (lo, hi)
      if let some lo ← extractLowerBound b x then
        if let some hi ← extractUpperBound a x then
          return some (lo, hi)
      return none
    | _ => return none

  mkIntervalRatFromBounds (loExpr hiExpr : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some lo ← extractRatFromReal loExpr then
      if let some hi ← extractRatFromReal hiExpr then
        let loRatExpr := toExpr lo
        let hiRatExpr := toExpr hi
        let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
        let leProof ← mkDecideProof leProofTy
        let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
        return some intervalRat
    return none

  /-- Extract the interval from a membership expression -/
  extractInterval (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memTy with
    | Membership.mem _ _ _ interval xExpr =>
      if ← isDefEq xExpr x then return some interval else return none
    | _ =>
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTy x then
        return ← mkIntervalRatFromBounds loExpr hiExpr
      let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
      if memTyWhnf == memTy then
        return none
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTyWhnf x then
        return ← mkIntervalRatFromBounds loExpr hiExpr
      return none

/-- The main root_bound tactic implementation -/
def rootBoundCore (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse the goal
  let some rootGoal ← parseRootGoal goalType
    | let diagReport ← mkDiagnosticReport "root_bound" goalType "parse"
        (some m!"Expected form: ∀ x ∈ I, f x ≠ 0\n\n\
                 The function f must be continuous and supported by LeanCert.\n\
                 The interval I must be Set.Icc or equivalent.")
      throwError "root_bound: Could not parse goal as a root goal.\n\n{diagReport}"

  match rootGoal with
  | .forallNeZero _name interval func =>
    proveForallNeZero goal interval func taylorDepth

where
  /-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
  getAst (func : Lean.Expr) : TacticM Lean.Expr := do
    lambdaTelescope func fun _vars body => do
      let fn := body.getAppFn
      if fn.isConstOf ``LeanCert.Core.Expr.eval then
        let args := body.getAppArgs
        if args.size ≥ 2 then
          return args[1]!
        else
          throwError m!"Unexpected Expr.eval application structure.\n\
                        Expected: Expr.eval env ast\n\
                        Got {args.size} arguments: {args.toList}"
      else
        reify func

  /-- Prove ∀ x ∈ I, f x ≠ 0 using verify_no_root -/
  proveForallNeZero (goal : MVarId) (interval func : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      -- 1. Get AST
      let ast ← getAst func

      -- 2. Generate ExprSupportedCore proof
      let supportProof ← mkSupportedCoreProof ast

      -- 3. Build config expression
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- 4. Apply verify_no_root theorem
      let proof ← mkAppM ``Validity.RootFinding.verify_no_root
        #[ast, supportProof, interval, cfgExpr]

      -- 5. Apply the proof - this leaves the certificate check as a goal
      let newGoals ← goal.apply proof

      setGoals newGoals

      -- 6. Solve remaining goals with native_decide
      for g in newGoals do
        setGoals [g]
        evalTactic (← `(tactic| native_decide))

/-- The root_bound tactic.

    Automatically proves root-related properties using interval arithmetic.

    Usage:
    - `root_bound` - uses default Taylor depth of 10
    - `root_bound 20` - uses Taylor depth of 20

    Supports goals of the form:
    - `∀ x ∈ I, f x ≠ 0` (proves no root exists in interval)
-/
elab "root_bound" depth:(num)? : tactic => do
  let taylorDepth := match depth with
    | some n => n.getNat
    | none => 10
  rootBoundCore taylorDepth

/-! ## Point Inequality Tactic (interval_decide)

The `interval_decide` tactic proves point inequalities like `Real.exp 1 ≤ 3` by
transforming them into singleton interval bounds `∀ x ∈ Set.Icc c c, f x ≤ b`
and using the existing `interval_bound` machinery.
-/

/-- Check if a Lean Name ends with a given suffix string -/
private def nameEndsWithStr (n : Lean.Name) (suffix : String) : Bool :=
  match n with
  | .str _ s => s == suffix || s.endsWith ("." ++ suffix)
  | _ => false

/-- Parse a point inequality goal and extract lhs, rhs, and inequality type.
    Returns (lhs, rhs, isStrict, isReversed) where:
    - isStrict: true for < or >, false for ≤ or ≥
    - isReversed: true for ≥ or > (need to flip the comparison) -/
def parsePointIneq (goal : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Bool × Bool)) := do
  let goal ← whnf goal
  let fn := goal.getAppFn
  let args := goal.getAppArgs

  if let .const name _ := fn then
    -- Check for LE/le patterns (handles both LE.le and Real.le etc.)
    -- LE.le: args = [type, inst, lhs, rhs] (4 args)
    -- Real.le: args = [lhs, rhs] (2 args)
    if name == ``LE.le && args.size >= 4 then
      return some (args[2]!, args[3]!, false, false)
    if nameEndsWithStr name "le" && args.size >= 2 then
      -- Likely a specialized le like Real.le
      return some (args[args.size - 2]!, args[args.size - 1]!, false, false)
    -- LT.lt patterns
    if name == ``LT.lt && args.size >= 4 then
      return some (args[2]!, args[3]!, true, false)
    if nameEndsWithStr name "lt" && args.size >= 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!, true, false)
    -- GE.ge patterns
    if name == ``GE.ge && args.size >= 4 then
      return some (args[2]!, args[3]!, false, true)
    if nameEndsWithStr name "ge" && args.size >= 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!, false, true)
    -- GT.gt patterns
    if name == ``GT.gt && args.size >= 4 then
      return some (args[2]!, args[3]!, true, true)
    if nameEndsWithStr name "gt" && args.size >= 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!, true, true)
  return none

/-- Try to collect all constant rational values from an expression.
    Returns the list of rational constants found (for building the singleton interval). -/
partial def collectConstants (e : Lean.Expr) : MetaM (List ℚ) := do
  -- Don't use whnf - it expands Real.exp to Complex.exp which we don't want
  -- First try to extract as rational directly
  if let some q ← extractRatFromReal e then
    return [q]

  let fn := e.getAppFn
  let args := e.getAppArgs

  -- For function applications, collect from arguments
  if let .const name _ := fn then
    let nameStr := name.toString
    -- Unary functions: collect from the argument
    -- Check by name suffix since the full name might include module prefix
    if nameStr.endsWith "exp" || nameStr.endsWith "sin" || nameStr.endsWith "cos" ||
       nameStr.endsWith "sqrt" || nameStr.endsWith "log" || nameStr.endsWith "sinh" ||
       nameStr.endsWith "cosh" || nameStr.endsWith "tanh" || nameStr.endsWith "arctan" then
      if args.size > 0 then
        return ← collectConstants args.back!
    -- Negation
    if name == ``Neg.neg && args.size >= 3 then
      return ← collectConstants args[2]!

  -- Binary operations
  if fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``HSub.hSub ||
     fn.isConstOf ``HMul.hMul || fn.isConstOf ``HDiv.hDiv then
    if args.size >= 6 then
      let lhsConsts ← collectConstants args[4]!
      let rhsConsts ← collectConstants args[5]!
      return lhsConsts ++ rhsConsts

  return []

/-- Try to prove a closed expression bound directly using certificate verification.
    For goals like `Real.pi ≤ 4` where the expression doesn't contain any variables,
    we can directly use verify_upper_bound/verify_lower_bound with a singleton interval. -/
def proveClosedExpressionBound (goal : MVarId) (goalType : Lean.Expr) (taylorDepth : Nat) : TacticM Unit := do
  trace[interval_decide] "proveClosedExpressionBound: Starting with goal {goalType}"
  goal.withContext do
    -- Parse the inequality
    let some (lhs, rhs, isStrict, isReversedOrig) ← parsePointIneq goalType
      | throwError "proveClosedExpressionBound: Expected a point inequality"
    trace[interval_decide] "Parsed: lhs={lhs}, rhs={rhs}, isStrict={isStrict}, isReversedOrig={isReversedOrig}"

    -- Determine which side has the function by checking where we find rational constants
    let lhsConsts ← collectConstants lhs
    let rhsConsts ← collectConstants rhs

    let (funcExpr, boundExpr, needsFlip) :=
      if lhsConsts.isEmpty && !rhsConsts.isEmpty then
        -- lhs is the function (has no extractable rationals, likely transcendental)
        (lhs, rhs, false)
      else if rhsConsts.isEmpty && !lhsConsts.isEmpty then
        -- rhs is the function (has no extractable rationals, likely transcendental)
        (rhs, lhs, true)
      else
        -- Either both have constants or neither does - default based on isReversed
        if isReversedOrig then (rhs, lhs, false) else (lhs, rhs, false)

    -- isReversed indicates whether we need a lower bound (true) or upper bound (false)
    -- For lhs ≤ rhs: if funcExpr is lhs, we need upper bound on func
    -- For lhs ≤ rhs: if funcExpr is rhs (needsFlip=true), we need lower bound on func
    let isReversed := isReversedOrig != needsFlip
    trace[interval_decide] "funcExpr={funcExpr}, boundExpr={boundExpr}, needsFlip={needsFlip}, isReversed={isReversed}"

    -- Try to extract the bound as a rational
    let boundRat? ← extractRatFromReal boundExpr

    -- If bound is not a rational, we have two transcendental expressions (like pi < sqrt(2) + sqrt(3))
    -- Transform to: 0 < rhs - lhs (for LT) or 0 < lhs - rhs (for GT) etc.
    if boundRat?.isNone then
      trace[interval_decide] "Bound is not rational, trying difference approach"
      -- Build the difference expression
      let diffExpr ←
        if isStrict then
          if isReversed then
            -- bound > func means func - bound < 0, so we prove bound - func > 0
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]
          else
            -- func < bound means bound - func > 0
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]
        else
          if isReversed then
            -- bound ≥ func means we prove bound - func ≥ 0
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]
          else
            -- func ≤ bound means bound - func ≥ 0
            mkAppM ``HSub.hSub #[boundExpr, funcExpr]

      trace[interval_decide] "diffExpr = {diffExpr}"

      -- Reify the difference expression
      let diffAst ← reify diffExpr
      let supportProof ← mkSupportedCoreProof diffAst
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- Build singleton interval
      let zeroRat : ℚ := 0
      let leProof ← mkAppM ``le_refl #[toExpr zeroRat]
      let intervalExpr ← mkAppM ``IntervalRat.mk #[toExpr zeroRat, toExpr zeroRat, leProof]

      -- We want to prove 0 < diff or 0 ≤ diff
      let theoremName := if isStrict then ``verify_strict_lower_bound else ``verify_lower_bound
      let checkName := if isStrict then ``LeanCert.Validity.checkStrictLowerBound
                       else ``LeanCert.Validity.checkLowerBound

      -- Build certificate check
      let checkExpr ← mkAppM checkName #[diffAst, intervalExpr, toExpr zeroRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      certGoalId.withContext do
        try
          setGoals [certGoalId]
          evalTactic (← `(tactic| native_decide))
        catch _ =>
          throwError "proveClosedExpressionBound: Certificate check failed for difference expression"

      -- Apply theorem: 0 < diff on [0,0]
      let proof ← mkAppM theoremName #[diffAst, supportProof, intervalExpr, toExpr zeroRat, cfgExpr, certGoal]

      -- Build membership and application like before
      let zeroRatAsReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr (0 : ℚ)]
      let h1 ← mkAppM ``le_refl #[zeroRatAsReal]
      let h2 ← mkAppM ``le_refl #[zeroRatAsReal]
      let memProof ← mkAppM ``And.intro #[h1, h2]
      let proofAtZero := Lean.mkApp2 proof zeroRatAsReal memProof

      let proofType ← inferType proofAtZero
      trace[interval_decide] "Difference proof type: {proofType}"

      -- Now we need to transform 0 < diff into the original goal lhs < rhs
      setGoals [goal]
      let proofStx ← Term.exprToSyntax proofAtZero

      try
        -- Apply simp to unfold Expr.eval
        evalTactic (← `(tactic| (
          have h0 := $proofStx;
          simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                     LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                     LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                     LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                     LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                     LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                     Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                     Rat.cast_zero, sub_zero, zero_sub, neg_neg] at h0
        )))

        -- Log the hypothesis after first simp
        let hyps ← getLCtx
        for d in hyps do
          if d.userName.toString.startsWith "h0" then
            trace[interval_decide] "After first simp, h0 type: {← inferType d.toExpr}"

        -- Normalize rational expressions
        evalTactic (← `(tactic| norm_num at h0))

        -- Log after norm_num
        let hyps2 ← getLCtx
        for d in hyps2 do
          if d.userName.toString.startsWith "h0" then
            trace[interval_decide] "After norm_num, h0 type: {← inferType d.toExpr}"

        -- Try various approaches to close the goal
        evalTactic (← `(tactic| (
          first
          | linarith
          | (simp only [← sub_eq_add_neg] at h0; exact sub_pos.mp h0)
          | (simp only [← sub_eq_add_neg, sub_pos] at h0; exact h0)
          | (have h1 := lt_add_of_neg_add_lt_left h0; simp at h1; exact h1)
          | (have h1 := h0; ring_nf at h1; linarith)
        )))
        let remainingGoals ← getGoals
        if !remainingGoals.isEmpty then
          throwError "proveClosedExpressionBound: Goal not closed after difference approach"
        return
      catch e =>
        trace[interval_decide] "Difference approach error: {e.toMessageData}"
        throwError "proveClosedExpressionBound: Difference approach failed: {e.toMessageData}"

    let some boundRat := boundRat?
      | throwError "proveClosedExpressionBound: Could not extract rational bound from {boundExpr}"

    trace[interval_decide] "boundRat extracted: {boundRat}"

    -- Reify the function expression directly
    let ast ← reify funcExpr
    trace[interval_decide] "ast reified"

    -- Generate the support proof
    let supportProof ← mkSupportedCoreProof ast
    trace[interval_decide] "supportProof generated"

    -- Build config expression
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    -- Build the singleton interval [0, 0]
    let zeroRat : ℚ := 0
    let leProof ← mkAppM ``le_refl #[toExpr zeroRat]
    let intervalExpr ← mkAppM ``IntervalRat.mk #[toExpr zeroRat, toExpr zeroRat, leProof]

    -- Choose the appropriate verify theorem based on strict/reversed
    let theoremName :=
      if isStrict then
        if isReversed then ``verify_strict_lower_bound else ``verify_strict_upper_bound
      else
        if isReversed then ``verify_lower_bound else ``verify_upper_bound

    -- Build the check function name for native_decide (use full paths to avoid ambiguity)
    let checkName :=
      if isStrict then
        if isReversed then ``LeanCert.Validity.checkStrictLowerBound
        else ``LeanCert.Validity.checkStrictUpperBound
      else
        if isReversed then ``LeanCert.Validity.checkLowerBound
        else ``LeanCert.Validity.checkUpperBound

    -- Build the certificate check expression and verify it's true
    trace[interval_decide] "Building certificate check"
    let checkExpr ← mkAppM checkName #[ast, intervalExpr, toExpr boundRat, cfgExpr]
    trace[interval_decide] "checkExpr built"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    certGoalId.withContext do
      try
        setGoals [certGoalId]
        trace[interval_decide] "Running native_decide"
        evalTactic (← `(tactic| native_decide))
        trace[interval_decide] "Certificate verified"
      catch e =>
        trace[interval_decide] "native_decide failed: {e.toMessageData}"
        throwError "proveClosedExpressionBound: Certificate check failed for closed expression"

    -- Apply the verify theorem with the certificate to get:
    -- ∀ x ∈ I, Expr.eval (fun _ => x) ast ≤/≥ (boundRat : ℝ)
    let proof ← mkAppM theoremName #[ast, supportProof, intervalExpr, toExpr boundRat, cfgExpr, certGoal]

    -- Build the membership proof for x=0: 0 ∈ ⟨0, 0, _⟩
    -- IntervalRat membership: (0 : ℝ) ∈ ⟨lo, hi, _⟩ means (↑lo : ℝ) ≤ 0 ∧ 0 ≤ (↑hi : ℝ)
    -- Since lo = hi = 0, this is (↑(0:ℚ) : ℝ) ≤ 0 ∧ 0 ≤ (↑(0:ℚ) : ℝ)
    -- Which simplifies to 0 ≤ 0 ∧ 0 ≤ 0

    -- Now we need to apply the proof to 0 and provide the membership proof
    -- The membership type is: zeroReal ∈ intervalExpr
    -- IntervalRat.instMembership defines: x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)
    -- For I = ⟨0, 0, _⟩, this is (↑(0:ℚ) : ℝ) ≤ x ∧ x ≤ (↑(0:ℚ) : ℝ)

    -- Build (↑(0:ℚ) : ℝ)
    -- Rat.cast requires target type annotation
    let zeroRatAsReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr (0 : ℚ)]

    -- Build (↑(0:ℚ) : ℝ) ≤ (0 : ℝ)  - this is 0 ≤ 0
    let h1 ← mkAppM ``le_refl #[zeroRatAsReal]

    -- Build (0 : ℝ) ≤ (↑(0:ℚ) : ℝ)  - same as above
    let h2 ← mkAppM ``le_refl #[zeroRatAsReal]

    -- The membership proof
    let memProof ← mkAppM ``And.intro #[h1, h2]

    -- Apply the universal statement to x=0 with the membership proof
    -- proof 0 memProof : Expr.eval (fun _ => 0) ast ≤/≥ (boundRat : ℝ)
    let proofAtZero := Lean.mkApp2 proof zeroRatAsReal memProof

    -- Now we need to simp the lhs to get the actual value
    -- Use the main goal and apply the proof, then simp to close
    setGoals [goal]

    -- Convert proof to syntax
    let proofStx ← Term.exprToSyntax proofAtZero

    -- Debug: check proof type
    let proofType ← inferType proofAtZero
    trace[interval_decide] "Proof type: {proofType}"
    trace[interval_decide] "Goal type: {goalType}"

    -- Use convert to match the proof with the goal, allowing for definitional equality
    -- The proof has type: Expr.eval (fun _ => 0) ast ≤/≥ (boundRat : ℝ)
    -- The goal has type: Real.pi ≤/≥ 4 (or similar)
    -- We need to show these are definitionally equal after simp
    -- Try multiple approaches to close the goal
    -- Approach 1: Direct simp + exact (works for integer bounds like 4)
    try
      setGoals [goal]
      evalTactic (← `(tactic| have h0 := $proofStx))
      evalTactic (← `(tactic| (
        simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                   LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                   LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                   LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                   LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                   LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                   Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast] at h0
      )))
      evalTactic (← `(tactic| exact h0))
      return  -- Success!
    catch _ => pure ()

    -- Approach 2: Use convert with norm_num to handle decimal bounds like 3.15
    setGoals [goal]
    try
      evalTactic (← `(tactic| (
        have h0 := $proofStx;
        simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                   LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                   LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                   LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                   LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                   LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                   Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                   Rat.divInt_eq_div] at h0;
        convert h0 using 1 <;> norm_num
      )))
      return  -- Success!
    catch e2 =>
      trace[interval_decide] "Approach 2 failed: {e2.toMessageData}"

    -- Approach 3: Normalize goal bound first using show_term
    setGoals [goal]
    let boundRatStx ← Term.exprToSyntax (toExpr boundRat)
    try
      -- Use show to rewrite the goal type
      evalTactic (← `(tactic| (
        show $(← Term.exprToSyntax funcExpr) ≤ ↑($boundRatStx : ℚ)
      )))
      -- Now types should match
      evalTactic (← `(tactic| (
        have h0 := $proofStx;
        simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                   LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                   LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                   LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                   LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                   LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                   Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                   Rat.divInt_eq_div] at h0;
        exact h0
      )))
      return  -- Success!
    catch e3 =>
      trace[interval_decide] "Approach 3 failed: {e3.toMessageData}"

    -- Approach 4: Use refine with explicit type cast
    setGoals [goal]
    try
      evalTactic (← `(tactic| (
        refine ?_;
        have h0 := $proofStx;
        simp only [LeanCert.Core.Expr.eval, LeanCert.Core.Expr.eval_pi,
                   LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_sqrt,
                   LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_sub,
                   LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg,
                   LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_log,
                   LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos,
                   Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast,
                   Rat.divInt_eq_div] at h0;
        exact_mod_cast h0
      )))
      return  -- Success!
    catch e4 =>
      trace[interval_decide] "Approach 4 failed: {e4.toMessageData}"

    throwError "proveClosedExpressionBound: Failed to close goal after all attempts"

/-- The interval_decide tactic implementation.
    Transforms `f(c) ≤ b` into `∀ x ∈ [c,c], f(x) ≤ b` and uses interval_bound. -/
def intervalDecideCore (taylorDepth : Nat) : TacticM Unit := do
  intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType
  trace[interval_decide] "intervalDecideCore: goal type = {goalType}"

  let some (lhs, rhs, _isStrict, isReversed) ← parsePointIneq goalType
    | let diagReport ← mkDiagnosticReport "interval_decide" goalType "parse"
        (some m!"Expected a point inequality of form:\n\
                 • expr ≤ bound  (or <, ≥, >)\n\
                 • e.g., Real.exp 1 ≤ 3\n\n\
                 For universally quantified goals, use `interval_bound` instead.")
      throwError "interval_decide: Could not parse as point inequality.\n\n{diagReport}"

  -- Determine which side has the transcendental function by checking where we find rational constants
  -- If lhs has only rational constants and rhs doesn't (or vice versa), swap appropriately
  let lhsConsts ← collectConstants lhs
  let rhsConsts ← collectConstants rhs

  -- The bound side should have rational constants, the function side shouldn't (or has transcendentals)
  -- If lhs has rationals and rhs doesn't → rhs is the function (flip for LE goals)
  -- If rhs has rationals and lhs doesn't → lhs is the function (standard for LE goals)
  let (funcExpr, boundExpr, needsFlip) :=
    if lhsConsts.isEmpty && !rhsConsts.isEmpty then
      -- lhs is the function (has no extractable rationals, likely transcendental)
      (lhs, rhs, false)
    else if rhsConsts.isEmpty && !lhsConsts.isEmpty then
      -- rhs is the function (has no extractable rationals, likely transcendental)
      (rhs, lhs, true)
    else
      -- Either both have constants or neither does - default to lhs as function
      if isReversed then (rhs, lhs, false) else (lhs, rhs, false)

  let actualIsReversed := isReversed != needsFlip  -- XOR to determine final orientation
  trace[interval_decide] "funcExpr = {funcExpr}, boundExpr = {boundExpr}, needsFlip = {needsFlip}, actualIsReversed = {actualIsReversed}"

  -- Collect constants from the function expression for the singleton point
  let consts ← collectConstants funcExpr
  trace[interval_decide] "consts = {consts}"

  -- Check if funcExpr has any free variables - if not, it's a closed expression
  let hasFreeVars := funcExpr.hasFVar
  trace[interval_decide] "hasFreeVars = {hasFreeVars}"

  -- Determine the singleton point to use
  let c : ℚ ←
    if !hasFreeVars then
      trace[interval_decide] "No free variables, trying closed expression path"
      -- This is a closed expression (like Real.pi, Real.sqrt 2, etc.)
      -- First try norm_num for simple cases
      -- Track if norm_num created a new goal (e.g., converting 3.15 to 63/20)
      let mut currentGoal := goal
      let mut currentGoalType := goalType
      try
        evalTactic (← `(tactic| norm_num))
        let remainingGoals ← getGoals
        if remainingGoals.isEmpty then
          return  -- norm_num closed the goal
        else
          let isAssignedAfter ← goal.isAssigned
          -- If norm_num assigned our goal but didn't close it, use the new goal
          if isAssignedAfter && !remainingGoals.isEmpty then
            currentGoal := remainingGoals.head!
            currentGoalType ← currentGoal.getType
      catch _ => pure ()

      -- Try to handle as a closed expression (no variables, just constants like pi)
      -- This uses direct certificate verification instead of interval_bound
      try
        proveClosedExpressionBound currentGoal currentGoalType taylorDepth
        return
      catch _ => pure ()

      -- Use first constant as fallback singleton point if available, else 0
      trace[interval_decide] "Falling through to fallback"
      if consts.isEmpty then pure 0 else pure consts.head!
    else
      -- Expression has free variables - use constants if available, else 0
      if consts.isEmpty then pure 0 else pure consts.head!

  -- Try norm_num first for simple cases
  let goalsBefore ← getGoals
  try
    evalTactic (← `(tactic| norm_num))
    let goalsAfter ← getGoals
    if goalsAfter.isEmpty || goalsAfter.length < goalsBefore.length then
      return
  catch _ => pure ()

  -- Build syntax for the constant c as a real number literal
  let cStx : Lean.Term ←
    if c.den == 1 then
      if c.num >= 0 then
        pure ⟨Syntax.mkNumLit (toString c.num)⟩
      else
        `(- $(Syntax.mkNumLit (toString (-c.num))))
    else
      if c.num >= 0 then
        `($(Syntax.mkNumLit (toString c.num)) / $(Syntax.mkNumLit (toString c.den)))
      else
        `(- ($(Syntax.mkNumLit (toString (-c.num))) / $(Syntax.mkNumLit (toString c.den))))

  let depthStx := Syntax.mkNumLit (toString taylorDepth)

  -- Try using interval_bound with singleton interval
  -- Note: This approach has limitations due to macro hygiene
  try
    evalTactic (← `(tactic|
      (have h : ∀ x ∈ Set.Icc ($cStx : ℝ) $cStx, _ := by interval_bound $depthStx) <;>
      exact h $cStx ⟨le_refl $cStx, le_refl $cStx⟩
    ))
    return
  catch _ => pure ()

  -- Provide helpful error message with manual workaround
  let cStr := if c.den == 1 then s!"{c.num}" else s!"{c.num}/{c.den}"
  let funcStr ← Meta.ppExpr funcExpr
  let boundStr ← Meta.ppExpr boundExpr
  throwError "interval_decide: Could not automatically prove this inequality.\n\n\
              Detected:\n\
              • Function: {funcStr}\n\
              • Bound: {boundStr}\n\
              • Evaluation point: {cStr}\n\n\
              Suggestions:\n\
              • Try increasing depth: `interval_decide 30`\n\
              • Check if the bound is mathematically correct\n\n\
              Manual workaround pattern:\n\
              ```lean\n\
              have h : ∀ x ∈ Set.Icc ({cStr}:ℝ) {cStr}, f x ≤ bound := by interval_bound\n\
              exact h {cStr} ⟨le_refl {cStr}, le_refl {cStr}⟩\n\
              ```\n\
              Replace `f x` with your expression (using `x` instead of `{cStr}`)."

/-- The interval_decide tactic.

    Attempts to prove point inequalities involving transcendental functions.

    Usage:
    - `interval_decide` - uses default Taylor depth of 10
    - `interval_decide 20` - uses Taylor depth of 20

    The tactic first tries `norm_num` for simple cases like `Real.exp 0 ≤ 2`.

    For more complex cases involving non-zero constants (like `Real.exp 1 ≤ 3`),
    use the manual workaround pattern:
    ```lean
    example : Real.exp 1 ≤ 3 := by
      have h : ∀ x ∈ Set.Icc (1:ℝ) 1, Real.exp x ≤ 3 := by interval_bound
      exact h 1 ⟨le_refl 1, le_refl 1⟩
    ```

    The key is to use a singleton interval `[c, c]` and replace the constant `c`
    with a variable `x` in the expression.
-/
elab "interval_decide" depth:(num)? : tactic => do
  let taylorDepth := match depth with
    | some n => n.getNat
    | none => 10
  intervalDecideCore taylorDepth

/-! ## Subdivision-aware bound proving

The `interval_bound_subdiv` tactic uses interval subdivision when the direct approach fails.
This helps with tight bounds where interval arithmetic has excessive width due to the
dependency problem (when a variable appears multiple times, we lose correlation).

Subdivision works because:
1. Narrower intervals → tighter bounds
2. May subdivide near critical points, reducing dependency
-/

/-- Check if a certificate check will succeed (without throwing) -/
private def certCheckSucceeds (checkFn : Lean.Expr) : TacticM Bool := do
  let certTy ← mkAppM ``Eq #[checkFn, mkConst ``Bool.true]
  let certGoal ← mkFreshExprMVar certTy
  let certGoalId := certGoal.mvarId!
  let savedState ← saveState
  try
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    restoreState savedState
    return true
  catch _ =>
    restoreState savedState
    return false

/-- Try to prove upper bound with subdivision.
    Returns a proof term if successful, or none if it fails. -/
private partial def proveUpperBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  -- Build the interval
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]

  -- Build the check expression
  let checkExpr ← mkAppM ``LeanCert.Validity.checkUpperBound
    #[ast, intervalRat, boundRat, cfgExpr]

  -- Try direct check first
  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct check succeeded"
    -- Build the proof using the direct theorem
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal

    let proof ← mkAppM ``Validity.verify_upper_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  -- Direct failed - try subdivision if we have depth left
  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct check failed, trying subdivision (depth {maxSubdiv})"

  -- Extract lo and hi as rationals
  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  -- Compute midpoint
  let mid : ℚ := (lo + hi) / 2

  -- Build proof that lo ≤ mid
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  -- Try left half [lo, mid]
  let leftProof ← proveUpperBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  -- Try right half [mid, hi]
  let rightProof ← proveUpperBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  -- Build certificate proofs for the split theorem
  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkUpperBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkUpperBound
    #[ast, rightInterval, boundRat, cfgExpr]

  -- Build certificate proofs
  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining proofs"

  -- Use verify_upper_bound_general_split to combine the two proofs
  -- theorem verify_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
  --     (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
  --     (h_left : checkUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
  --     (h_right : checkUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
  --     ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c
  let proof ← mkAppM ``Validity.verify_upper_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

where
  getLiteral? (e : Lean.Expr) : TacticM (Option ℚ) := do
    try
      let val ← unsafe Lean.Meta.evalExpr ℚ (mkConst ``Rat) e
      return some val
    catch _ =>
      return none

private def getSubdivBounds (intervalInfo : IntervalInfo) :
    TacticM (Option (ℚ × ℚ × Lean.Expr × Lean.Expr × Lean.Expr × Bool)) := do
  match intervalInfo.fromSetIcc with
  | some (lo, hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
    return some (lo, hi, loRatExpr, hiRatExpr, leProof, true)
  | none =>
    try
      let intervalVal ← unsafe evalExpr IntervalRat (mkConst ``IntervalRat) intervalInfo.intervalRat
      let lo := intervalVal.lo
      let hi := intervalVal.hi
      let loRatExpr := toExpr lo
      let hiRatExpr := toExpr hi
      let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
      let leProof ← mkDecideProof leProofTy
      return some (lo, hi, loRatExpr, hiRatExpr, leProof, false)
    catch _ =>
      return none

/-- Prove ∀ x ∈ I, f x ≤ c using subdivision as fallback -/
private def proveForallLeSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← intervalBoundCore.getAst func
    let boundRat ← intervalBoundCore.extractRatBound bound
    let (supportProof, _useWithInv) ← intervalBoundCore.getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    -- Save the current goal state
    let savedGoals ← getGoals

    -- Try with subdivision
    let some proof ← proveUpperBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      -- The proof has type: ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c
      -- But goal has type: ∀ x ∈ Set.Icc lo hi, f x ≤ bound
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      -- IntervalRat goal: bridge via mem_iff_mem_Icc
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    -- Close side goals (equality goals for Set.Icc, bounds, and expressions)
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- Try to prove lower bound with subdivision.
    Returns a proof term if successful, or none if it fails. -/
private partial def proveLowerBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  -- Build the interval
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]

  -- Build the check expression
  let checkExpr ← mkAppM ``LeanCert.Validity.checkLowerBound
    #[ast, intervalRat, boundRat, cfgExpr]

  -- Try direct check first
  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct lower bound check succeeded"
    -- Build the proof using the direct theorem
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal

    let proof ← mkAppM ``Validity.verify_lower_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  -- Direct failed - try subdivision if we have depth left
  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct lower bound check failed, trying subdivision (depth {maxSubdiv})"

  -- Extract lo and hi as rationals
  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  -- Compute midpoint
  let mid : ℚ := (lo + hi) / 2

  -- Build proof that lo ≤ mid
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  -- Try left half [lo, mid]
  let leftProof ← proveLowerBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  -- Try right half [mid, hi]
  let rightProof ← proveLowerBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  -- Build certificate proofs for the split theorem
  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkLowerBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkLowerBound
    #[ast, rightInterval, boundRat, cfgExpr]

  -- Build certificate proofs
  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining lower bound proofs"

  -- Use verify_lower_bound_general_split to combine the two proofs
  let proof ← mkAppM ``Validity.verify_lower_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

where
  getLiteral? (e : Lean.Expr) : TacticM (Option ℚ) := do
    try
      let val ← unsafe Lean.Meta.evalExpr ℚ (mkConst ``Rat) e
      return some val
    catch _ =>
      return none

/-- Prove ∀ x ∈ I, c ≤ f x using subdivision as fallback -/
private def proveForallGeSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← intervalBoundCore.getAst func
    let boundRat ← intervalBoundCore.extractRatBound bound
    let (supportProof, _useWithInv) ← intervalBoundCore.getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    -- Save the current goal state
    let savedGoals ← getGoals

    -- Try with subdivision
    let some proof ← proveLowerBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision (lower bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      -- The proof has type: ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e
      -- But goal has type: ∀ x ∈ Set.Icc lo hi, bound ≤ f x
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    -- Close side goals (equality goals for Set.Icc, bounds, and expressions)
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- Try to prove strict upper bound with subdivision.
    Returns a proof term if successful, or none if it fails. -/
private partial def proveStrictUpperBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  -- Build the interval
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]

  -- Build the check expression
  let checkExpr ← mkAppM ``LeanCert.Validity.checkStrictUpperBound
    #[ast, intervalRat, boundRat, cfgExpr]

  -- Try direct check first
  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct strict upper bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal

    let proof ← mkAppM ``Validity.verify_strict_upper_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  -- Direct failed - try subdivision if we have depth left
  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct strict upper bound check failed, trying subdivision (depth {maxSubdiv})"

  -- Extract lo and hi as rationals
  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  -- Compute midpoint
  let mid : ℚ := (lo + hi) / 2

  -- Build proof that lo ≤ mid
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  -- Try left half [lo, mid]
  let leftProof ← proveStrictUpperBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  -- Try right half [mid, hi]
  let rightProof ← proveStrictUpperBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  -- Build certificate proofs for the split theorem
  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictUpperBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictUpperBound
    #[ast, rightInterval, boundRat, cfgExpr]

  -- Build certificate proofs
  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining strict upper bound proofs"

  let proof ← mkAppM ``Validity.verify_strict_upper_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

where
  getLiteral? (e : Lean.Expr) : TacticM (Option ℚ) := do
    try
      let val ← unsafe Lean.Meta.evalExpr ℚ (mkConst ``Rat) e
      return some val
    catch _ =>
      return none

/-- Try to prove strict lower bound with subdivision.
    Returns a proof term if successful, or none if it fails. -/
private partial def proveStrictLowerBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  -- Build the interval
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]

  -- Build the check expression
  let checkExpr ← mkAppM ``LeanCert.Validity.checkStrictLowerBound
    #[ast, intervalRat, boundRat, cfgExpr]

  -- Try direct check first
  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct strict lower bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal

    let proof ← mkAppM ``Validity.verify_strict_lower_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  -- Direct failed - try subdivision if we have depth left
  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct strict lower bound check failed, trying subdivision (depth {maxSubdiv})"

  -- Extract lo and hi as rationals
  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  -- Compute midpoint
  let mid : ℚ := (lo + hi) / 2

  -- Build proof that lo ≤ mid
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  -- Try left half [lo, mid]
  let leftProof ← proveStrictLowerBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  -- Try right half [mid, hi]
  let rightProof ← proveStrictLowerBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  -- Build certificate proofs for the split theorem
  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictLowerBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictLowerBound
    #[ast, rightInterval, boundRat, cfgExpr]

  -- Build certificate proofs
  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining strict lower bound proofs"

  let proof ← mkAppM ``Validity.verify_strict_lower_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

where
  getLiteral? (e : Lean.Expr) : TacticM (Option ℚ) := do
    try
      let val ← unsafe Lean.Meta.evalExpr ℚ (mkConst ``Rat) e
      return some val
    catch _ =>
      return none

/-- Prove ∀ x ∈ I, f x < c using subdivision as fallback -/
private def proveForallLtSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← intervalBoundCore.getAst func
    let boundRat ← intervalBoundCore.extractRatBound bound
    let (supportProof, _useWithInv) ← intervalBoundCore.getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveStrictUpperBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision (strict upper bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    -- Close side goals
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      if ← tryClose (evalTactic (← `(tactic| field_simp; ring))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- Prove ∀ x ∈ I, c < f x using subdivision as fallback -/
private def proveForallGtSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← intervalBoundCore.getAst func
    let boundRat ← intervalBoundCore.extractRatBound bound
    let (supportProof, _useWithInv) ← intervalBoundCore.getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveStrictLowerBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision (strict lower bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    -- Close side goals
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- The interval_bound_subdiv tactic.

    Like interval_bound, but uses interval subdivision when the direct approach fails.
    This can help with tight bounds where the dependency problem causes excessive width.

    Usage:
    - `interval_bound_subdiv` - uses default Taylor depth 10 and max subdivision depth 3
    - `interval_bound_subdiv 20` - uses Taylor depth 20
    - `interval_bound_subdiv 20 5` - uses Taylor depth 20 and max subdivision depth 5
-/
elab "interval_bound_subdiv" depth:(num)? subdivDepth:(num)? : tactic => do
  intervalNormCore
  let maxSubdiv := match subdivDepth with
    | some n => n.getNat
    | none => 3
  let depths : List Nat := match depth with
    | some n => [n.getNat]
    | none => [10, 15, 20, 25]

  -- Pre-process like intervalBoundCore
  try
    evalTactic (← `(tactic| intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
  catch _ =>
    try evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
    catch _ => pure ()

  try
    evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one] at *))
  catch _ => pure ()

  let savedState ← saveState
  let mut lastErr : Option MessageData := none
  for taylorDepth in depths do
    restoreState savedState
    let goal ← getMainGoal
    let goalType ← goal.getType
    let some boundGoal ← parseBoundGoal goalType
      | throwError "interval_bound_subdiv: Could not parse goal"
    try
      match boundGoal with
      | .forallLe _name interval func bound =>
        proveForallLeSubdiv goal interval func bound taylorDepth maxSubdiv
      | .forallGe _name interval func bound =>
        proveForallGeSubdiv goal interval func bound taylorDepth maxSubdiv
      | .forallLt _name interval func bound =>
        proveForallLtSubdiv goal interval func bound taylorDepth maxSubdiv
      | .forallGt _name interval func bound =>
        proveForallGtSubdiv goal interval func bound taylorDepth maxSubdiv
      return
    catch e =>
      lastErr := some e.toMessageData
  throwError m!"interval_bound_subdiv: All precision levels failed\n{lastErr.getD ""}"

end LeanCert.Tactic.Auto
