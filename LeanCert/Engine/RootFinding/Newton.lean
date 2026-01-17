/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.AD
import LeanCert.Engine.TaylorModel
import LeanCert.Engine.Optimize  -- For derivInterval_correct_single, evalFunc1
import LeanCert.Engine.RootFinding.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Root Finding: Newton Method

This file implements the interval Newton method for root finding.

## Main definitions

* `newtonStepTM` - TM-based interval Newton step
* `newtonStepSimple` - Simple interval Newton step (fallback)
* `newtonStep` - Combined Newton step (tries TM first)
* `newtonIntervalGo` - Main Newton iteration loop
* `newtonIntervalTM` - Newton interval iteration using TM

## Main theorems

* `newton_preserves_root` - Roots are preserved by Newton refinement (via MVT)
* `newton_step_at_most_one_root` - At most one root when Newton step succeeds (via Rolle)
* `newtonIntervalGo_preserves_root` - If root exists, noRoot cannot be returned

All Newton theorems for root preservation are FULLY PROVED with no `sorry`.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Newton step definitions -/

/-- One TM-based interval Newton step for `e` on `I` w.r.t. variable `varIdx`.

The Newton operator is: N(I) = c - f(c)/f'(I)
where c is the center (midpoint) of I.

We use Taylor model evaluation to get a sharper bound on f(c) than plain
interval evaluation, and AD for the derivative interval f'(I).

Returns the intersection I ∩ N(I), or `none` if:
- The Taylor model build fails (e.g., division by interval containing 0)
- The derivative interval contains 0 (cannot safely divide)
- The intersection is empty

`degree` is the Taylor model degree (1 is usually enough for Newton). -/
noncomputable def newtonStepTM
    (e : Expr) (I : IntervalRat) (varIdx : Nat) (degree : ℕ := 1) :
    Option IntervalRat := do
  -- 1. Build a Taylor model for e on I
  let tm ← TaylorModel.fromExpr? e I degree
  -- 2. Get derivative interval on I using AD
  let dI := derivInterval e (fun _ => I) varIdx
  -- If derivative interval contains zero, we can't safely divide
  if hzero : IntervalRat.containsZero dI then
    none
  else
    -- 3. Newton center: we use tm.center (which fromExpr? ensures is I.midpoint)
    let c : ℚ := tm.center
    -- 4. Interval for f(c) using the TM (sharper than plain interval eval)
    let fc : IntervalRat := TaylorModel.valueAtCenterInterval tm
    -- 5. Build nonzero interval for derivative and invert
    let dNonzero : IntervalRat.IntervalRatNonzero :=
      { lo := dI.lo
        hi := dI.hi
        le := dI.le
        nonzero := hzero }
    let dInv : IntervalRat := IntervalRat.invNonzero dNonzero
    -- 6. Compute quotient Q ≈ f(c) / f'(I) as fc * dInv
    let Q : IntervalRat := IntervalRat.mul fc dInv
    -- 7. Build N(I) = c - Q as an interval: [c - Q.hi, c - Q.lo]
    let N : IntervalRat :=
      { lo := c - Q.hi
        hi := c - Q.lo
        le := by
          have hQ : Q.lo ≤ Q.hi := Q.le
          linarith }
    -- 8. Intersect with original I
    IntervalRat.intersect I N

/-- Simple Newton step using plain interval arithmetic (fallback).
    Less precise than TM-based but always available. -/
noncomputable def newtonStepSimple
    (e : Expr) (I : IntervalRat) (varIdx : Nat) :
    Option IntervalRat := do
  let c : ℚ := I.midpoint
  -- Interval for f(c) using singleton interval eval
  let fc := evalInterval1 e (IntervalRat.singleton c)
  -- Derivative interval on I
  let dI := derivInterval e (fun _ => I) varIdx
  -- If derivative interval contains zero, we can't safely divide
  if hzero : IntervalRat.containsZero dI then
    none
  else
    let dNonzero : IntervalRat.IntervalRatNonzero :=
      { lo := dI.lo, hi := dI.hi, le := dI.le, nonzero := hzero }
    let dInv := IntervalRat.invNonzero dNonzero
    let Q := IntervalRat.mul fc dInv
    let N : IntervalRat :=
      { lo := c - Q.hi
        hi := c - Q.lo
        le := by linarith [Q.le] }
    IntervalRat.intersect I N

/-- Combined Newton step: tries TM-based first, falls back to simple.
    This is the main entry point for the Newton iteration. -/
noncomputable def newtonStep
    (e : Expr) (I : IntervalRat) (varIdx : Nat) (degree : ℕ := 1) :
    Option IntervalRat :=
  match newtonStepTM e I varIdx degree with
  | some N => some N
  | none => newtonStepSimple e I varIdx

/-- Main Newton iteration loop. Extracted from newtonIntervalTM for proof purposes. -/
noncomputable def newtonIntervalGo (e : Expr) (varIdx : Nat) (degree : ℕ)
    (J : IntervalRat) (iter : ℕ) (contracted : Bool) : IntervalRat × RootStatus :=
  match iter with
  | 0 =>
    if contracted then
      (J, RootStatus.uniqueRoot)
    else
      (J, checkRootStatus e J)
  | n + 1 =>
    -- Try TM-based Newton step first
    match newtonStepTM e J varIdx degree with
    | none =>
      -- TM step failed, try simple
      match newtonStepSimple e J varIdx with
      | none =>
        if contracted then (J, RootStatus.uniqueRoot)
        else (J, checkRootStatus e J)
      | some N =>
        -- Process step result (inlined for termination)
        if N.lo > J.lo ∧ N.hi < J.hi then
          newtonIntervalGo e varIdx degree N n true
        else if N.lo > J.hi ∨ N.hi < J.lo then
          -- Strict inequality for soundness: truly disjoint intervals
          (J, RootStatus.noRoot)
        else
          newtonIntervalGo e varIdx degree N n contracted
    | some N =>
      -- Process step result (inlined for termination)
      if N.lo > J.lo ∧ N.hi < J.hi then
        newtonIntervalGo e varIdx degree N n true
      else if N.lo > J.hi ∨ N.hi < J.lo then
        -- Strict inequality for soundness: truly disjoint intervals
        (J, RootStatus.noRoot)
      else
        newtonIntervalGo e varIdx degree N n contracted
termination_by iter

/-- Interval Newton iteration using TM-based steps.

If Newton step contracts (result ⊂ input), we have uniqueness.

Parameters:
- `e`: the expression representing the function
- `I`: initial interval to search for root
- `varIdx`: variable index (typically 0 for single-variable)
- `maxIter`: maximum number of Newton iterations
- `degree`: Taylor model degree (default 1, higher for more precision)
-/
noncomputable def newtonIntervalTM (e : Expr) (I : IntervalRat) (varIdx : Nat)
    (maxIter : ℕ) (degree : ℕ := 1) : IntervalRat × RootStatus :=
  newtonIntervalGo e varIdx degree I maxIter false

/-- Original Newton iteration (for backwards compatibility).
    Now uses TM-based implementation with degree 1. -/
noncomputable def newtonInterval (e : Expr) (I : IntervalRat) (varIdx : Nat)
    (maxIter : ℕ) : IntervalRat × RootStatus :=
  newtonIntervalTM e I varIdx maxIter 1

/-! ### Auxiliary lemmas for Newton proofs -/

/-- The derivative of evalFunc1 at any point in I is contained in derivInterval.
    This bridges our AD derivative bounds to actual derivatives.
    Requires UsesOnlyVar0, which we'll assume for root finding on single-variable expressions. -/
theorem deriv_in_derivInterval (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (ξ : ℝ) (hξ : ξ ∈ I) :
    deriv (evalFunc1 e) ξ ∈ derivInterval e (fun _ => I) 0 :=
  derivInterval_correct_single e hsupp hvar0 I ξ hξ

/-- Mean Value Theorem application: for differentiable f, f(x) - f(c) = f'(ξ)(x - c)
    for some ξ between c and x. -/
theorem mvt_for_eval (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c x : ℝ) (_hcI : c ∈ I) (_hxI : x ∈ I) (hcx : c ≠ x) :
    ∃ ξ, (min c x < ξ ∧ ξ < max c x) ∧
      evalFunc1 e x - evalFunc1 e c = deriv (evalFunc1 e) ξ * (x - c) := by
  have hdiff := evalFunc1_differentiable e hsupp
  -- Need continuity on [min c x, max c x] and differentiability on (min c x, max c x)
  have hcont : ContinuousOn (evalFunc1 e) (Set.Icc (min c x) (max c x)) :=
    hdiff.continuous.continuousOn
  have hdiffOn : DifferentiableOn ℝ (evalFunc1 e) (Set.Ioo (min c x) (max c x)) :=
    hdiff.differentiableOn
  have hlt : min c x < max c x := by
    rcases lt_trichotomy c x with hlt | heq | hgt
    · simp [min_eq_left hlt.le, max_eq_right hlt.le, hlt]
    · exact absurd heq hcx
    · simp [min_eq_right hgt.le, max_eq_left hgt.le, hgt]
  -- Apply MVT: exists ξ with deriv f ξ = (f(max) - f(min)) / (max - min)
  rcases exists_deriv_eq_slope (evalFunc1 e) hlt hcont hdiffOn with ⟨ξ, hξ_mem, hξ_eq⟩
  use ξ
  constructor
  · exact hξ_mem
  · -- Convert slope equation to what we need
    -- hξ_eq: deriv f ξ = (f(max) - f(min)) / (max - min)
    rcases le_or_gt c x with hcx_le | hcx_gt
    · -- c ≤ x case: min = c, max = x
      have hmin : min c x = c := min_eq_left hcx_le
      have hmax : max c x = x := max_eq_right hcx_le
      rw [hmin, hmax] at hξ_eq
      -- hξ_eq: deriv f ξ = (f x - f c) / (x - c)
      have hxc_ne : x - c ≠ 0 := by
        intro heq
        have : x = c := by linarith
        exact hcx this.symm
      field_simp [hxc_ne] at hξ_eq
      linarith
    · -- x < c case: min = x, max = c
      have hmin : min c x = x := min_eq_right hcx_gt.le
      have hmax : max c x = c := max_eq_left hcx_gt.le
      rw [hmin, hmax] at hξ_eq
      -- hξ_eq: deriv f ξ = (f c - f x) / (c - x)
      have hcx_ne : c - x ≠ 0 := by linarith
      field_simp [hcx_ne] at hξ_eq
      -- hξ_eq: deriv f ξ * (c - x) = f c - f x
      -- need: f x - f c = deriv f ξ * (x - c)
      linarith

/-- If ξ is between c and x, and both c and x are in I, then ξ is in I. -/
theorem between_mem_interval (I : IntervalRat) (c x ξ : ℝ)
    (hcI : c ∈ I) (hxI : x ∈ I) (hξ_between : min c x < ξ ∧ ξ < max c x) :
    ξ ∈ I := by
  simp only [IntervalRat.mem_def] at hcI hxI ⊢
  constructor
  · have h1 : (I.lo : ℝ) ≤ min c x := le_min hcI.1 hxI.1
    linarith [hξ_between.1]
  · have h2 : max c x ≤ (I.hi : ℝ) := max_le hcI.2 hxI.2
    linarith [hξ_between.2]

/-- Abstract Newton preservation lemma: if x is a root in I, and we compute
    N = I ∩ (c - fc/dI) where fc contains f(c) and dI contains f'(I),
    then x ∈ N.

    This captures the mathematical essence without dealing with the monadic
    structure of newtonStepTM/newtonStepSimple. -/
theorem newton_operator_preserves_root (e : Expr) (hsupp : ExprSupported e) (_hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (c : ℚ) (fc dI : IntervalRat)
    (hc_in_I : (c : ℝ) ∈ I)
    (hfc : evalFunc1 e c ∈ fc)
    (hdI : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ∈ dI)
    (hdI_nonzero : ¬IntervalRat.containsZero dI)
    (x : ℝ) (hx : x ∈ I) (hroot : evalFunc1 e x = 0) :
    -- x is in the Newton operator interval c - fc/dI
    let dNonzero : IntervalRat.IntervalRatNonzero :=
      { lo := dI.lo, hi := dI.hi, le := dI.le, nonzero := hdI_nonzero }
    let dInv := IntervalRat.invNonzero dNonzero
    let Q := IntervalRat.mul fc dInv
    let Newton : IntervalRat := { lo := c - Q.hi, hi := c - Q.lo, le := by linarith [Q.le] }
    x ∈ Newton := by
  intro dNonzero dInv Q Newton
  -- Case 1: x = c (root is at the center)
  by_cases hxc : x = c
  · -- If x = c, then f(c) = 0, so fc contains 0
    subst hxc
    -- Since f(c) = 0 and 0 ∈ fc, we have Q contains 0/dI = 0
    -- So Newton = [c - Q.hi, c - Q.lo] contains c
    simp only [IntervalRat.mem_def]
    -- fc contains 0, so Q = fc * dInv contains 0
    have hfc_zero : (0 : ℝ) ∈ fc := by simp only [hroot] at hfc; exact hfc
    simp only [IntervalRat.mem_def] at hfc_zero
    -- 0 ∈ Q since 0 * anything = 0 and 0 ∈ fc
    have hQ_zero : (0 : ℝ) ∈ Q := by
      have : (0 : ℝ) = 0 * (dInv.lo : ℝ) := by ring
      rw [this]
      apply IntervalRat.mem_mul
      · simp only [IntervalRat.mem_def]
        exact ⟨hfc_zero.1, hfc_zero.2⟩
      · simp only [IntervalRat.mem_def]
        constructor
        · exact le_refl _
        · exact_mod_cast dInv.le
    simp only [IntervalRat.mem_def] at hQ_zero
    -- Newton.lo = c - Q.hi, Newton.hi = c - Q.lo
    -- Need: Newton.lo ≤ c ≤ Newton.hi
    -- i.e., c - Q.hi ≤ c ≤ c - Q.lo
    -- i.e., -Q.hi ≤ 0 ≤ -Q.lo
    -- i.e., Q.lo ≤ 0 ≤ Q.hi
    simp only [Newton]  -- unfold Newton definition
    simp only [Rat.cast_sub]  -- (c - Q.hi : ℝ) = c - Q.hi
    constructor
    · -- Newton.lo ≤ c, i.e., c - Q.hi ≤ c
      linarith [hQ_zero.2]
    · -- c ≤ Newton.hi, i.e., c ≤ c - Q.lo
      linarith [hQ_zero.1]
  · -- Case 2: x ≠ c, use MVT
    -- By MVT: f(x) - f(c) = f'(ξ)(x - c) for some ξ between c and x
    have hmvt := mvt_for_eval e hsupp I c x hc_in_I hx (Ne.symm hxc)
    obtain ⟨ξ, hξ_between, hξ_eq⟩ := hmvt
    -- ξ is in I (between c and x, both in I)
    have hξ_in_I : ξ ∈ I := between_mem_interval I c x ξ hc_in_I hx hξ_between
    -- f'(ξ) ∈ dI
    have hderiv_in_dI : deriv (evalFunc1 e) ξ ∈ dI := hdI ξ hξ_in_I
    -- From MVT: f(x) - f(c) = f'(ξ)(x - c)
    -- Since f(x) = 0: -f(c) = f'(ξ)(x - c), so x = c - f(c)/f'(ξ)
    have hfc_val : evalFunc1 e c = deriv (evalFunc1 e) ξ * (c - x) := by
      have : evalFunc1 e x - evalFunc1 e c = deriv (evalFunc1 e) ξ * (x - c) := hξ_eq
      simp only [hroot, zero_sub] at this
      linarith
    -- f'(ξ) ≠ 0 (since dI doesn't contain zero and f'(ξ) ∈ dI)
    have hderiv_ne : deriv (evalFunc1 e) ξ ≠ 0 := by
      intro hcontra
      have hmem : (0 : ℝ) ∈ dI := by rw [← hcontra]; exact hderiv_in_dI
      simp only [IntervalRat.mem_def] at hmem
      have hcz := hdI_nonzero
      simp only [IntervalRat.containsZero, not_and, not_le] at hcz
      rcases le_or_gt dI.lo 0 with hlo | hlo
      · have hhi := hcz hlo
        have hhi_cast : (dI.hi : ℝ) < 0 := by exact_mod_cast hhi
        linarith
      · have hlo_cast : (dI.lo : ℝ) > 0 := by exact_mod_cast hlo
        linarith
    -- So x = c - f(c)/f'(ξ)
    have hx_eq : x = c - evalFunc1 e c / deriv (evalFunc1 e) ξ := by
      field_simp [hderiv_ne] at hfc_val ⊢
      linarith
    -- Now show x ∈ Newton = [c - Q.hi, c - Q.lo]
    -- We need: c - Q.hi ≤ x ≤ c - Q.lo
    -- i.e., c - Q.hi ≤ c - f(c)/f'(ξ) ≤ c - Q.lo
    -- i.e., Q.lo ≤ f(c)/f'(ξ) ≤ Q.hi
    -- This follows from f(c) ∈ fc, f'(ξ)⁻¹ ∈ dInv, and Q = fc * dInv
    simp only [IntervalRat.mem_def]
    rw [hx_eq]
    -- Need: c - Q.hi ≤ c - f(c)/f'(ξ) ≤ c - Q.lo
    -- Equiv: Q.lo ≤ f(c)/f'(ξ) ≤ Q.hi
    have hquot_in_Q : evalFunc1 e c / deriv (evalFunc1 e) ξ ∈ Q := by
      have hinv : (deriv (evalFunc1 e) ξ)⁻¹ ∈ dInv := by
        apply IntervalRat.mem_invNonzero
        · exact hderiv_in_dI
        · exact hderiv_ne
      have : evalFunc1 e c / deriv (evalFunc1 e) ξ = evalFunc1 e c * (deriv (evalFunc1 e) ξ)⁻¹ := by
        field_simp
      rw [this]
      exact IntervalRat.mem_mul hfc hinv
    simp only [IntervalRat.mem_def] at hquot_in_Q
    -- Need: Newton.lo ≤ x ≤ Newton.hi
    -- Newton.lo = c - Q.hi, Newton.hi = c - Q.lo, x = c - f(c)/f'(ξ)
    -- So need: c - Q.hi ≤ c - f(c)/f'(ξ) ≤ c - Q.lo
    -- Equiv:   f(c)/f'(ξ) ≤ Q.hi  and  Q.lo ≤ f(c)/f'(ξ)
    simp only [Newton]  -- unfold Newton definition
    simp only [Rat.cast_sub]  -- (c - Q.hi : ℝ) = c - Q.hi
    constructor
    · -- Newton.lo ≤ x, i.e., c - Q.hi ≤ c - f(c)/f'(ξ)
      linarith [hquot_in_Q.2]
    · -- x ≤ Newton.hi, i.e., c - f(c)/f'(ξ) ≤ c - Q.lo
      linarith [hquot_in_Q.1]

/-- If a root exists in I and Newton step produces N, then the root is in N.
    This is the key soundness property: Newton refinement preserves roots.

    Requires `UsesOnlyVar0 e` to connect our AD derivative bounds to actual derivatives.
    This is a reasonable assumption for root finding on single-variable expressions. -/
theorem newton_preserves_root (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I N : IntervalRat)
    (hN : newtonStepTM e I 0 1 = some N ∨ newtonStepSimple e I 0 = some N)
    (x : ℝ) (hx : x ∈ I) (hroot : Expr.eval (fun _ => x) e = 0) :
    x ∈ N := by
  -- Key: we use newton_operator_preserves_root and show the components satisfy the conditions
  -- Both newtonStepTM and newtonStepSimple compute N = I ∩ (c - fc/dI)
  have hroot' : evalFunc1 e x = 0 := hroot
  rcases hN with hTM | hSimple
  · -- Case: newtonStepTM succeeded
    -- newtonStepTM uses Taylor model for fc, AD for dI
    -- Unfold the definition
    simp only [newtonStepTM] at hTM
    -- Extract the Taylor model from the monadic computation
    cases htm : TaylorModel.fromExpr? e I 1 with
    | none =>
      -- If fromExpr? returns none, then newtonStepTM returns none, contradiction with hTM
      simp only [htm, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hTM
    | some tm =>
      simp only [htm] at hTM
      -- Extract the key values
      set dI := derivInterval e (fun _ => I) 0 with hdI_def
      -- Extract that derivative doesn't contain zero
      have hzero : ¬IntervalRat.containsZero dI := by
        intro hcontra
        by_cases h : (derivInterval e (fun _ => I) 0).containsZero
        · simp only [h, ↓reduceDIte, Option.bind_eq_bind, Option.bind_fun_none,
          reduceCtorEq] at hTM
        · exact h hcontra
      -- Define the Newton components
      let c : ℚ := tm.center
      let fc := TaylorModel.valueAtCenterInterval tm
      let dNonzero : IntervalRat.IntervalRatNonzero :=
        { lo := dI.lo, hi := dI.hi, le := dI.le, nonzero := hzero }
      let dInv := IntervalRat.invNonzero dNonzero
      let Q := IntervalRat.mul fc dInv
      let Newton : IntervalRat := { lo := c - Q.hi, hi := c - Q.lo, le := by linarith [Q.le] }
      -- Show that hTM gives us N = intersect I Newton
      have hTM' : IntervalRat.intersect I Newton = some N := by
        by_cases h : (derivInterval e (fun _ => I) 0).containsZero
        · exact absurd h hzero
        · simp only [h] at hTM
          convert hTM using 2
      -- Key: tm.center = I.midpoint (theorem is in LeanCert.Engine namespace, not TaylorModel)
      have hc_eq : c = I.midpoint := fromExpr?_center e I 1 tm htm
      -- Prove the premises for newton_operator_preserves_root
      have hc_in_I : (c : ℝ) ∈ I := by
        rw [hc_eq]
        exact IntervalRat.midpoint_mem I
      -- Prove f(c) ∈ fc using TM correctness
      have hfc_correct : evalFunc1 e c ∈ fc := by
        simp only [fc, evalFunc1]
        -- Use valueAtCenter_correct
        have hEvalSet := fromExpr_evalSet_correct e I 1 tm htm
        have hDomain := fromExpr?_domain e I 1 tm htm
        have hc_in_domain : (c : ℝ) ∈ tm.domain := by
          rw [hDomain]
          rw [hc_eq]
          exact IntervalRat.midpoint_mem I
        exact TaylorModel.valueAtCenter_correct tm (fun y => Expr.eval (fun _ => y) e)
          (hDomain.symm ▸ hEvalSet) hc_in_domain
      have hdI_correct : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ∈ dI := by
        intro ξ hξ
        simp only [hdI_def]
        exact deriv_in_derivInterval e hsupp hvar0 I ξ hξ
      -- Apply the abstract lemma to get x ∈ Newton
      have hx_in_Newton : x ∈ Newton := by
        have := newton_operator_preserves_root e hsupp hvar0 I c fc dI hc_in_I hfc_correct hdI_correct hzero x hx hroot'
        simp only [Newton, Q, dInv, dNonzero]
        convert this using 2
      -- Use mem_intersect: x ∈ I and x ∈ Newton implies x ∈ N
      have hx_in_intersect := IntervalRat.mem_intersect hx hx_in_Newton
      obtain ⟨K, hK_eq, hx_in_K⟩ := hx_in_intersect
      -- Since intersect I Newton = some N = some K, we have N = K
      have hN_eq_K : N = K := by
        rw [hTM'] at hK_eq
        simp only [Option.some.injEq] at hK_eq
        exact hK_eq
      rw [hN_eq_K]
      exact hx_in_K
  · -- Case: newtonStepSimple succeeded
    -- newtonStepSimple uses I.midpoint for c, evalInterval1 for fc
    -- First, extract the key property: the derivative interval doesn't contain zero
    -- (otherwise newtonStepSimple would return none)
    set c : ℚ := I.midpoint with hc_def
    set fc := evalInterval1 e (IntervalRat.singleton c) with hfc_def
    set dI := derivInterval e (fun _ => I) 0 with hdI_def
    have hzero : ¬IntervalRat.containsZero dI := by
      intro hcontra
      -- If dI contains zero, newtonStepSimple returns none
      simp only [newtonStepSimple] at hSimple
      -- Use decidability to split: either containsZero is true or false
      by_cases h : (derivInterval e (fun _ => I) 0).containsZero
      · -- Case: containsZero is true => hSimple : none = some N, contradiction
        simp only [h, ↓reduceDIte, reduceCtorEq] at hSimple
      · -- Case: containsZero is false, but we assumed hcontra says dI.containsZero
        -- dI = derivInterval e (fun _ => I) 0 by definition
        exact h hcontra
    -- Define the Newton components matching the definition
    let dNonzero : IntervalRat.IntervalRatNonzero :=
      { lo := dI.lo, hi := dI.hi, le := dI.le, nonzero := hzero }
    let dInv := IntervalRat.invNonzero dNonzero
    let Q := IntervalRat.mul fc dInv
    let Newton : IntervalRat := { lo := c - Q.hi, hi := c - Q.lo, le := by linarith [Q.le] }
    -- Show that hSimple gives us N = intersect I Newton
    have hSimple' : IntervalRat.intersect I Newton = some N := by
      simp only [newtonStepSimple] at hSimple
      -- Use by_cases to handle the dite
      by_cases h : (derivInterval e (fun _ => I) 0).containsZero
      · -- Case: containsZero is true, contradiction with hzero
        exact absurd h hzero
      · -- Case: containsZero is false, simplify the dite
        simp only [h] at hSimple
        -- Now hSimple : I.intersect {...} = some N
        -- Need to show our Newton equals the one in hSimple
        convert hSimple using 2
    -- Prove the premises for newton_operator_preserves_root
    have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
    have hfc_correct : evalFunc1 e c ∈ fc := by
      simp only [hfc_def, evalFunc1]
      exact evalInterval1_correct e hsupp c (IntervalRat.singleton c) (IntervalRat.mem_singleton c)
    have hdI_correct : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ∈ dI := by
      intro ξ hξ
      simp only [hdI_def]
      exact deriv_in_derivInterval e hsupp hvar0 I ξ hξ
    -- Apply the abstract lemma to get x ∈ Newton
    have hx_in_Newton : x ∈ Newton := by
      have := newton_operator_preserves_root e hsupp hvar0 I c fc dI hc_in_I hfc_correct hdI_correct hzero x hx hroot'
      simp only [Newton, Q, dInv, dNonzero]
      convert this using 2
    -- Use mem_intersect: x ∈ I and x ∈ Newton implies x ∈ N
    have hx_in_intersect := IntervalRat.mem_intersect hx hx_in_Newton
    obtain ⟨K, hK_eq, hx_in_K⟩ := hx_in_intersect
    -- Since intersect I Newton = some N = some K, we have N = K
    have hN_eq_K : N = K := by
      rw [hSimple'] at hK_eq
      simp only [Option.some.injEq] at hK_eq
      exact hK_eq
    rw [hN_eq_K]
    exact hx_in_K

/-- At most one root when Newton step succeeds (regardless of contraction).

    If a Newton step succeeds (returns some N), then the derivative interval excludes zero.
    By MVT, this means f is strictly monotonic on I, hence at most one root.

    This lemma is independent of existence - it just proves uniqueness given any two roots. -/
theorem newton_step_at_most_one_root (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (hN : (∃ N, newtonStepTM e I 0 1 = some N) ∨ (∃ N, newtonStepSimple e I 0 = some N))
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I)
    (hx_root : Expr.eval (fun _ => x) e = 0) (hy_root : Expr.eval (fun _ => y) e = 0) :
    x = y := by
  by_contra hne
  -- Extract that derivative doesn't contain zero from the Newton step succeeding
  have hzero : ¬IntervalRat.containsZero (derivInterval e (fun _ => I) 0) := by
    rcases hN with ⟨N, hTM⟩ | ⟨N, hSimple⟩
    · simp only [newtonStepTM] at hTM
      cases htm : TaylorModel.fromExpr? e I 1 with
      | none => simp only [htm, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hTM;
      | some tm =>
        simp only [htm] at hTM
        by_cases h : (derivInterval e (fun _ => I) 0).containsZero
        · simp only [h, ↓reduceDIte, Option.bind_eq_bind, Option.bind_fun_none,
          reduceCtorEq] at hTM
        · exact h
    · simp only [newtonStepSimple] at hSimple
      by_cases h : (derivInterval e (fun _ => I) 0).containsZero
      · simp only [h, ↓reduceDIte, reduceCtorEq] at hSimple
      · exact h
  -- f' ≠ 0 on I means f is strictly monotonic, so at most one root
  have hmvt := deriv_in_derivInterval e hsupp hvar0 I
  simp only [IntervalRat.mem_def] at hx hy
  -- Use Rolle's theorem: if f(x) = f(y) = 0 and x ≠ y, there's ξ between them with f'(ξ) = 0
  -- Ne.lt_or_lt hne gives: x < y ∨ y < x
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- Case: x < y
    have hIcc_sub : Set.Icc x y ⊆ Set.Icc (I.lo : ℝ) I.hi := by
      intro z ⟨hzlo, hzhi⟩
      constructor
      · linarith [hx.1]
      · linarith [hy.2]
    have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc x y) := hCont.mono hIcc_sub
    have hf_eq : evalFunc1 e x = evalFunc1 e y := by
      simp only [evalFunc1]
      rw [hx_root, hy_root]
    obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) x y hlt hCont' hf_eq
    have hξ_in_I : ξ ∈ I := by
      simp only [IntervalRat.mem_def]
      constructor
      · linarith [hx.1, hξ_mem.1]
      · linarith [hy.2, hξ_mem.2]
    have hderiv_in := hmvt ξ hξ_in_I
    rw [hξ_deriv] at hderiv_in
    simp only [IntervalRat.containsZero] at hzero
    simp only [IntervalRat.mem_def] at hderiv_in
    simp only [not_and_or, not_le] at hzero
    rcases hzero with hlo_pos | hhi_neg
    · have hcast : (0 : ℝ) < (derivInterval e (fun _ => I) 0).lo := by exact_mod_cast hlo_pos
      linarith [hderiv_in.1, hcast]
    · have hcast : ((derivInterval e (fun _ => I) 0).hi : ℝ) < 0 := by exact_mod_cast hhi_neg
      linarith [hderiv_in.2, hcast]
  · -- Case: y < x
    have hIcc_sub : Set.Icc y x ⊆ Set.Icc (I.lo : ℝ) I.hi := by
      intro z ⟨hzlo, hzhi⟩
      constructor
      · linarith [hy.1]
      · linarith [hx.2]
    have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc y x) := hCont.mono hIcc_sub
    have hf_eq : evalFunc1 e y = evalFunc1 e x := by
      simp only [evalFunc1]
      rw [hy_root, hx_root]
    obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) y x hlt hCont' hf_eq
    have hξ_in_I : ξ ∈ I := by
      simp only [IntervalRat.mem_def]
      constructor
      · linarith [hy.1, hξ_mem.1]
      · linarith [hx.2, hξ_mem.2]
    have hderiv_in := hmvt ξ hξ_in_I
    rw [hξ_deriv] at hderiv_in
    simp only [IntervalRat.containsZero] at hzero
    simp only [IntervalRat.mem_def] at hderiv_in
    simp only [not_and_or, not_le] at hzero
    rcases hzero with hlo_pos | hhi_neg
    · have hcast : (0 : ℝ) < (derivInterval e (fun _ => I) 0).lo := by exact_mod_cast hlo_pos
      linarith [hderiv_in.1, hcast]
    · have hcast : ((derivInterval e (fun _ => I) 0).hi : ℝ) < 0 := by exact_mod_cast hhi_neg
      linarith [hderiv_in.2, hcast]

/-! ### Helper lemmas for Newton contraction existence proof -/

/-- Structure extracted from a contracting Newton step.
    When newtonStepSimple contracts, we can extract bounds on the quotient Q = fc/dI. -/
structure NewtonContractionData (I N : IntervalRat) where
  c : ℚ                    -- center (midpoint of I)
  fc : IntervalRat         -- interval containing f(c)
  dI : IntervalRat         -- derivative interval f'(I)
  Q : IntervalRat          -- quotient fc/dI
  hc_eq : c = I.midpoint
  hdI_nonzero : ¬dI.containsZero
  hQ_lo_bound : Q.lo > c - I.hi   -- equivalently Q.lo > -hw
  hQ_hi_bound : Q.hi < c - I.lo   -- equivalently Q.hi < hw
  hN_lo : N.lo = max I.lo (c - Q.hi)
  hN_hi : N.hi = min I.hi (c - Q.lo)

/-- When Newton contracts strictly, the Newton bounds dominate the intersection.
    That is, N.lo = c - Q.hi (not I.lo) and N.hi = c - Q.lo (not I.hi). -/
lemma contraction_newton_bounds {I N : IntervalRat} {c : ℚ} {Q : IntervalRat}
    (hContract : N.lo > I.lo ∧ N.hi < I.hi)
    (hN_lo : N.lo = max I.lo (c - Q.hi))
    (hN_hi : N.hi = min I.hi (c - Q.lo)) :
    N.lo = c - Q.hi ∧ N.hi = c - Q.lo := by
  constructor
  · -- N.lo = c - Q.hi
    -- We have N.lo = max I.lo (c - Q.hi) > I.lo
    -- If max = I.lo, then N.lo = I.lo, contradiction with N.lo > I.lo
    -- So max ≠ I.lo, meaning c - Q.hi > I.lo, hence max = c - Q.hi
    by_cases h : I.lo ≤ c - Q.hi
    · simp only [max_eq_right h, hN_lo]
    · push_neg at h
      have hmax_eq : max I.lo (c - Q.hi) = I.lo := max_eq_left (le_of_lt h)
      rw [hN_lo, hmax_eq] at hContract
      exact absurd hContract.1 (lt_irrefl I.lo)
  · -- N.hi = c - Q.lo
    -- We have N.hi = min I.hi (c - Q.lo) < I.hi
    -- If min = I.hi, then N.hi = I.hi, contradiction with N.hi < I.hi
    -- So min ≠ I.hi, meaning c - Q.lo < I.hi, hence min = c - Q.lo
    by_cases h : c - Q.lo ≤ I.hi
    · -- min I.hi (c - Q.lo) = c - Q.lo since c - Q.lo ≤ I.hi
      simp only [min_eq_right h, hN_hi]
    · push_neg at h
      have hmin_eq : min I.hi (c - Q.lo) = I.hi := min_eq_left (le_of_lt h)
      rw [hN_hi, hmin_eq] at hContract
      exact absurd hContract.2 (lt_irrefl I.hi)

/-- Extract the Newton step structure from newtonStepSimple.
    This lemma isolates the definitional unfolding of newtonStepSimple. -/
lemma newtonStepSimple_extract (e : Expr) (I N : IntervalRat)
    (hSimple : newtonStepSimple e I 0 = some N) :
    let c := I.midpoint
    let fc := evalInterval1 e (IntervalRat.singleton c)
    let dI := derivInterval e (fun _ => I) 0
    ∃ (hdI_nonzero : ¬dI.containsZero),
      let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
      let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
      N.lo = max I.lo (c - Q.hi) ∧ N.hi = min I.hi (c - Q.lo) := by
  -- Unfold the definition of newtonStepSimple
  unfold newtonStepSimple at hSimple
  -- The dite splits on containsZero
  by_cases hzero : (derivInterval e (fun _ => I) 0).containsZero
  · -- If dI contains zero, newtonStepSimple returns none, contradiction
    simp only [hzero, ↓reduceDIte, reduceCtorEq] at hSimple
  · -- If dI doesn't contain zero, we get an intersection
    simp only [hzero, dite_false] at hSimple
    use hzero
    -- hSimple : IntervalRat.intersect I ⟨c - Q.hi, c - Q.lo, _⟩ = some N
    -- When intersect returns some, it means the intersection is non-empty
    -- and the result has lo = max, hi = min
    simp only [IntervalRat.intersect] at hSimple
    -- Now we have a dite on whether lo ≤ hi
    -- Use split to handle the dite (split_ifs version for at hypothesis)
    split at hSimple
    · -- The intersection succeeded (dite was true)
      rename_i hintersect
      simp only [Option.some.injEq] at hSimple
      constructor
      · -- N.lo = max I.lo (c - Q.hi)
        exact congrArg IntervalRat.lo hSimple.symm
      · -- N.hi = min I.hi (c - Q.lo)
        exact congrArg IntervalRat.hi hSimple.symm
    · -- The intersection failed (none), contradiction with hSimple : none = some N
      simp only [reduceCtorEq] at hSimple

/-- Extract structure from newtonStepTM. This extracts the TM and proves the key structural facts. -/
lemma newtonStepTM_structure (e : Expr) (I N : IntervalRat)
    (hTM : newtonStepTM e I 0 1 = some N) :
    ∃ (tm : TaylorModel) (hdI_nonzero : ¬(derivInterval e (fun _ => I) 0).containsZero),
      TaylorModel.fromExpr? e I 1 = some tm ∧
      tm.center = I.midpoint ∧
      let c := I.midpoint
      let fc := TaylorModel.valueAtCenterInterval tm
      let dI := derivInterval e (fun _ => I) 0
      let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
      let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
      N.lo = max I.lo (c - Q.hi) ∧ N.hi = min I.hi (c - Q.lo) := by
  -- Step 1: Unfold newtonStepTM
  unfold newtonStepTM at hTM
  -- Step 2: First case split on fromExpr? result
  match hFrom : TaylorModel.fromExpr? e I 1 with
  | none =>
      -- If fromExpr? returns none, the do-block returns none, contradicting hTM
      simp only [bind, Option.bind, hFrom, reduceCtorEq] at hTM
  | some tm =>
      -- Now the do-block continues with this tm
      simp only [hFrom, bind, Option.bind] at hTM
      -- Step 3: Split on containsZero for dI
      by_cases hzero : (derivInterval e (fun _ => I) 0).containsZero
      · -- If dI contains zero, the branch returns none; contradiction
        simp only [dif_pos hzero, reduceCtorEq] at hTM
      · -- Else branch: we really have an intersection = some N
        simp only [dif_neg hzero] at hTM
        -- Step 4: Build the witness
        have hcenter := fromExpr?_center e I 1 tm hFrom
        refine ⟨tm, hzero, rfl, hcenter, ?_⟩
        -- Extract N.lo and N.hi from the intersect equation
        -- hTM : IntervalRat.intersect I N' = some N
        -- where N' = { lo := tm.center - Q.hi, hi := tm.center - Q.lo, ... }
        simp only [IntervalRat.intersect] at hTM
        split at hTM
        · -- Success branch: intersection returned some
          rename_i hintersect
          simp only [Option.some.injEq] at hTM
          -- hTM : N = ⟨max I.lo (tm.center - Q.hi), min I.hi (tm.center - Q.lo), _⟩
          have hN_lo := congrArg IntervalRat.lo hTM.symm
          have hN_hi := congrArg IntervalRat.hi hTM.symm
          simp only at hN_lo hN_hi
          -- Rewrite tm.center to I.midpoint
          rw [hcenter] at hN_lo hN_hi
          exact ⟨hN_lo, hN_hi⟩
        · -- Failure branch: intersect returned none, contradiction
          simp only [reduceCtorEq] at hTM

/-- Key correctness lemma: for TM Newton step, f(c) ∈ the TM-computed fc interval.
    This is what allows us to use the generic contraction contradiction lemmas. -/
lemma newtonStepTM_fc_correct (e : Expr) (I : IntervalRat)
    (tm : TaylorModel) (htmeq : TaylorModel.fromExpr? e I 1 = some tm) :
    let c := I.midpoint
    let fc := TaylorModel.valueAtCenterInterval tm
    evalFunc1 e c ∈ fc := by
  simp only
  -- tm.domain = I from fromExpr?_domain
  have hdomain := fromExpr?_domain e I 1 tm htmeq
  -- From fromExpr_evalSet_correct: ∀ x ∈ I, f(x) ∈ tm.evalSet x
  have heval : ∀ x ∈ I, Expr.eval (fun _ => x) e ∈ tm.evalSet x :=
    fromExpr_evalSet_correct e I 1 tm htmeq
  -- Convert to ∀ x ∈ tm.domain
  have heval' : ∀ x ∈ tm.domain, Expr.eval (fun _ => x) e ∈ tm.evalSet x := by
    intro x hx
    rw [hdomain] at hx
    exact heval x hx
  -- tm.center = I.midpoint
  have hc_eq := fromExpr?_center e I 1 tm htmeq
  -- center ∈ tm.domain
  have hc_in_domain : (tm.center : ℝ) ∈ tm.domain := by
    rw [hdomain]
    rw [hc_eq]
    exact IntervalRat.midpoint_mem I
  -- From valueAtCenter_correct: f(center) ∈ valueAtCenterInterval tm
  have hfc_correct := TaylorModel.valueAtCenter_correct tm (fun x => Expr.eval (fun _ => x) e) heval' hc_in_domain
  simp only [evalFunc1]
  -- Rewrite center to I.midpoint
  rw [hc_eq] at hfc_correct
  exact hfc_correct

end LeanCert.Engine
