/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Functions

/-!
# Taylor Model Composition and Expression Integration

This file provides composition operations for Taylor models and integration
with the `Expr` AST. It builds on the core Taylor model infrastructure and
function-specific Taylor approximations to enable automatic Taylor model
construction for expression trees.

## Main definitions

* `TaylorModel.sin`, `TaylorModel.cos`, `TaylorModel.exp` - Interval-based composition
* `TaylorModel.fromExpr`, `TaylorModel.fromExpr?` - Expression to Taylor model conversion
* `expIntervalRefined` - Refined exp interval using Taylor models

## Main results

* `fromExpr_evalSet_correct` - Taylor models from expressions are correct
* `fromExpr_correct` - Expression evaluation lies in Taylor model bound
* `mem_expIntervalRefined` - FTIA for refined exp interval
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Interval-based composition operations

Given a TM for an argument, these operations return TMs that bound transcendental
functions of that argument. They use function-level Taylor models for tight bounds.
-/

namespace TaylorModel

/-- Interval-based sin composition.
    Given a TM for the argument, returns a TM that bounds sin of the argument.
    Uses function-level Taylor model for tight bounds. -/
noncomputable def sin (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  -- Get interval bound on the argument
  let argInterval := tm.bound
  -- Get function TM for sin on this interval
  let sinTM := tmSin argInterval degree
  -- Return a constant TM with the sin bound as remainder
  { poly := 0
    remainder := sinTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based cos composition.
    Given a TM for the argument, returns a TM that bounds cos of the argument.
    Uses function-level Taylor model for tight bounds. -/
noncomputable def cos (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let cosTM := tmCos argInterval degree
  { poly := 0
    remainder := cosTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based exp composition.
    Given a TM for the argument, returns a TM that bounds exp of the argument.
    Uses function-level Taylor model for tight bounds. -/
noncomputable def exp (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let expTM := tmExp argInterval degree
  { poly := 0
    remainder := expTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based sinh composition.
    Given a TM for the argument, returns a TM that bounds sinh of the argument.
    Uses function-level Taylor model for tight bounds. -/
noncomputable def sinh (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let sinhTM := tmSinh argInterval degree
  { poly := 0
    remainder := sinhTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based cosh composition.
    Given a TM for the argument, returns a TM that bounds cosh of the argument.
    Uses function-level Taylor model for tight bounds. -/
noncomputable def cosh (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let coshTM := tmCosh argInterval degree
  { poly := 0
    remainder := coshTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based tanh composition.
    Given a TM for the argument, returns a TM that bounds tanh of the argument.
    Uses tanh = sinh / cosh with the fact that cosh ≥ 1 > 0. -/
noncomputable def tanh (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let tanhTM := tmTanh argInterval degree
  { poly := 0
    remainder := tanhTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based atan composition.
    Given a TM for the argument, returns a TM that bounds atan of the argument.
    Uses function-level Taylor model. Valid for |arg| ≤ 1. -/
noncomputable def atan (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let atanTM := tmAtan argInterval degree
  { poly := 0
    remainder := atanTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based atanh composition.
    Given a TM for the argument, returns a TM that bounds atanh of the argument.
    Uses function-level Taylor model. Valid for |arg| < 1. -/
noncomputable def atanh (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let atanhTM := tmAtanh argInterval degree
  { poly := 0
    remainder := atanhTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based asinh composition.
    Given a TM for the argument, returns a TM that bounds asinh of the argument.
    Uses function-level Taylor model. -/
noncomputable def asinh (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let asinhTM := tmAsinh argInterval degree
  { poly := 0
    remainder := asinhTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based sinc composition.
    Given a TM for the argument, returns a TM that bounds sinc of the argument.
    sinc(z) = sin(z)/z for z ≠ 0, sinc(0) = 1. -/
noncomputable def sinc (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let sincTM := tmSinc argInterval degree
  { poly := 0
    remainder := sincTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based erf composition.
    Given a TM for the argument, returns a TM that bounds erf of the argument.
    erf(z) = (2/√π) ∫₀ᶻ e^{-t²} dt. -/
noncomputable def erf (tm : TaylorModel) (degree : ℕ) : TaylorModel :=
  let argInterval := tm.bound
  let erfTM := tmErf argInterval degree
  { poly := 0
    remainder := erfTM.bound
    center := tm.center
    domain := tm.domain }

/-- Interval-based log composition.
    Given a TM for the argument, returns a TM that bounds log of the argument.
    Only valid when the argument interval is strictly positive.
    Returns none if the argument could be ≤ 0. -/
noncomputable def log? (tm : TaylorModel) (degree : ℕ) : Option TaylorModel :=
  match tmLog tm.bound degree with
  | some logTM =>
    some { poly := 0
           remainder := logTM.bound
           center := tm.center
           domain := tm.domain }
  | none => none

/-- Interval-based sqrt composition.
    Given a TM for the argument, returns a TM that bounds sqrt of the argument.
    Uses sqrtIntervalTight for the interval bound. -/
noncomputable def sqrt? (tm : TaylorModel) : Option TaylorModel :=
  some { poly := 0
         remainder := IntervalRat.sqrtIntervalTight tm.bound
         center := tm.center
         domain := tm.domain }

/-- Check if an interval is safe for atanh: max(|lo|, |hi|) ≤ 99/100.
    This ensures we're away from the singularities at ±1. -/
def atanhSafe (I : IntervalRat) : Bool :=
  max (|I.lo|) (|I.hi|) ≤ 99/100

/-- Helper: absolute value is bounded by max of interval endpoints for values in interval. -/
private theorem abs_le_interval_radius {z : ℝ} {I : IntervalRat} (hz : z ∈ I) :
    |z| ≤ max (|(I.lo : ℝ)|) (|(I.hi : ℝ)|) := by
  simp only [IntervalRat.mem_def] at hz
  rcases hz with ⟨hlo, hhi⟩
  by_cases hz_nn : 0 ≤ z
  · -- z ≥ 0: |z| = z ≤ hi ≤ |hi|
    rw [abs_of_nonneg hz_nn]
    calc z ≤ (I.hi : ℝ) := hhi
      _ ≤ |(I.hi : ℝ)| := le_abs_self _
      _ ≤ max (|(I.lo : ℝ)|) (|(I.hi : ℝ)|) := le_max_right _ _
  · -- z < 0: |z| = -z ≤ -lo ≤ |lo|
    push_neg at hz_nn
    rw [abs_of_neg hz_nn]
    calc -z ≤ -(I.lo : ℝ) := by linarith
      _ ≤ |(I.lo : ℝ)| := neg_le_abs _
      _ ≤ max (|(I.lo : ℝ)|) (|(I.hi : ℝ)|) := le_max_left _ _

/-- If an interval is atanh-safe, any value in the interval has |z| < 1. -/
theorem abs_lt_one_of_atanhSafe {I : IntervalRat} (hsafe : atanhSafe I)
    {z : ℝ} (hz : z ∈ I) : |z| < 1 := by
  simp only [atanhSafe, decide_eq_true_eq] at hsafe
  have hle : |z| ≤ max (|(I.lo : ℝ)|) (|(I.hi : ℝ)|) := abs_le_interval_radius hz
  have hradius_le : max (|(I.lo : ℝ)|) (|(I.hi : ℝ)|) ≤ 99/100 := by
    have hlo_q : |I.lo| ≤ 99/100 := le_trans (le_max_left _ _) hsafe
    have hhi_q : |I.hi| ≤ 99/100 := le_trans (le_max_right _ _) hsafe
    have hlo_le : |(I.lo : ℝ)| ≤ 99/100 := by
      have h1 : |(I.lo : ℝ)| = ((|I.lo| : ℚ) : ℝ) := (Rat.cast_abs I.lo).symm
      rw [h1]
      calc (↑(|I.lo|) : ℝ) ≤ (↑(99/100 : ℚ) : ℝ) := by exact_mod_cast hlo_q
        _ = 99/100 := by norm_num
    have hhi_le : |(I.hi : ℝ)| ≤ 99/100 := by
      have h1 : |(I.hi : ℝ)| = ((|I.hi| : ℚ) : ℝ) := (Rat.cast_abs I.hi).symm
      rw [h1]
      calc (↑(|I.hi|) : ℝ) ≤ (↑(99/100 : ℚ) : ℝ) := by exact_mod_cast hhi_q
        _ = 99/100 := by norm_num
    exact max_le hlo_le hhi_le
  linarith

/-- Interval-based atanh composition with domain check.
    Given a TM for the argument, returns a TM that bounds atanh of the argument.
    Returns none if the argument bound could be too close to ±1. -/
noncomputable def atanh? (tm : TaylorModel) (degree : ℕ) : Option TaylorModel :=
  if _ : atanhSafe tm.bound then
    some { poly := 0
           remainder := (tmAtanh tm.bound degree).bound
           center := tm.center
           domain := tm.domain }
  else
    none

/-! ### Building Taylor models from Expr -/

/-- Convert an expression to a Taylor model (total builder used for examples). -/
noncomputable def fromExpr (e : Expr) (domain : IntervalRat) (degree : ℕ) : TaylorModel :=
  match e with
  | Expr.const q => const q domain
  | Expr.var _ => identity domain
  | Expr.add e₁ e₂ => add (fromExpr e₁ domain degree) (fromExpr e₂ domain degree)
  | Expr.mul e₁ e₂ => mul (fromExpr e₁ domain degree) (fromExpr e₂ domain degree) degree
  | Expr.neg e => neg (fromExpr e domain degree)
  | Expr.inv e =>
      let tm := fromExpr e domain degree
      -- Fallback to constant 0 if the bound contains 0 (keeps totality for examples).
      if h : IntervalRat.containsZero tm.bound then
        const 0 domain
      else
        TaylorModel.inv tm h
  | Expr.exp e => exp (fromExpr e domain degree) degree
  | Expr.sin e => sin (fromExpr e domain degree) degree
  | Expr.cos e => cos (fromExpr e domain degree) degree
  | Expr.log e =>
      let tm := fromExpr e domain degree
      match log? tm degree with
      | some logTM => logTM
      | none => const 0 domain  -- Fallback if domain not positive
  | Expr.atan e => atan (fromExpr e domain degree) degree
  | Expr.arsinh e => asinh (fromExpr e domain degree) degree
  | Expr.atanh e => atanh (fromExpr e domain degree) degree
  | Expr.sinc e => sinc (fromExpr e domain degree) degree
  | Expr.erf e => erf (fromExpr e domain degree) degree
  | Expr.sinh e => sinh (fromExpr e domain degree) degree
  | Expr.cosh e => cosh (fromExpr e domain degree) degree
  | Expr.tanh e => tanh (fromExpr e domain degree) degree
  | Expr.sqrt e =>
      -- sqrt? always succeeds, so we can safely extract
      (sqrt? (fromExpr e domain degree)).getD (const 0 domain)
  | Expr.pi =>
      -- Pi is represented as a constant Taylor model with the pi interval as remainder
      -- We use the pi interval [3.14, 3.15] which encloses Real.pi
      { poly := 0
        remainder := LeanCert.Engine.piInterval
        center := domain.lo + (domain.hi - domain.lo) / 2
        domain := domain }

/-- Safe (partial) builder: convert an expression to a Taylor model, returning `none`
    if an inversion would require dividing by an interval that contains 0. -/
noncomputable def fromExpr? (e : Expr) (domain : IntervalRat) (degree : ℕ) :
    Option TaylorModel :=
  match e with
  | Expr.const q => some <| const q domain
  | Expr.var _ => some <| identity domain
  | Expr.add e₁ e₂ => do
      let tm₁ ← fromExpr? e₁ domain degree
      let tm₂ ← fromExpr? e₂ domain degree
      pure <| add tm₁ tm₂
  | Expr.mul e₁ e₂ => do
      let tm₁ ← fromExpr? e₁ domain degree
      let tm₂ ← fromExpr? e₂ domain degree
      pure <| mul tm₁ tm₂ degree
  | Expr.neg e => do
      let tm ← fromExpr? e domain degree
      pure <| neg tm
  | Expr.inv e => do
      let tm ← fromExpr? e domain degree
      if h : IntervalRat.containsZero tm.bound then
        none
      else
        pure <| TaylorModel.inv tm h
  | Expr.exp e => do
      let tm ← fromExpr? e domain degree
      pure <| exp tm degree
  | Expr.sin e => do
      let tm ← fromExpr? e domain degree
      pure <| sin tm degree
  | Expr.cos e => do
      let tm ← fromExpr? e domain degree
      pure <| cos tm degree
  | Expr.log e => do
      let tm ← fromExpr? e domain degree
      log? tm degree
  | Expr.atan _ => none  -- Not supported: atan evalSet proof incomplete
  | Expr.arsinh e => do
      let tm ← fromExpr? e domain degree
      pure <| asinh tm degree
  | Expr.atanh e => do
      let tm ← fromExpr? e domain degree
      atanh? tm degree
  | Expr.sinc e => do
      let tm ← fromExpr? e domain degree
      pure <| sinc tm degree
  | Expr.erf _ => none  -- Not supported: erf evalSet proof incomplete
  | Expr.sinh e => do
      let tm ← fromExpr? e domain degree
      pure <| sinh tm degree
  | Expr.cosh e => do
      let tm ← fromExpr? e domain degree
      pure <| cosh tm degree
  | Expr.tanh e => do
      let tm ← fromExpr? e domain degree
      pure <| tanh tm degree
  | Expr.sqrt e => do
      let tm ← fromExpr? e domain degree
      sqrt? tm
  | Expr.pi =>
      -- Pi is a constant Taylor model with pi interval as remainder
      some { poly := 0
             remainder := LeanCert.Engine.piInterval
             center := domain.midpoint
             domain := domain }

end TaylorModel

/-- Centers produced by `fromExpr?` are always `domain.midpoint`. -/
theorem fromExpr?_center (e : Expr) (domain : IntervalRat) (degree : ℕ)
    (tm : TaylorModel) (h : TaylorModel.fromExpr? e domain degree = some tm) :
    tm.center = domain.midpoint := by
  revert tm
  induction e generalizing degree with
  | const q =>
      intro tm h; simp [TaylorModel.fromExpr?] at h; cases h; simp [TaylorModel.const]
  | var idx =>
      intro tm h; simp [TaylorModel.fromExpr?] at h; cases h; simp [TaylorModel.identity]
  | add e1 e2 ih1 ih2 =>
      intro tm h
      cases h1 : TaylorModel.fromExpr? e1 domain degree with
      | none =>
        simp [TaylorModel.fromExpr?, h1] at h
      | some tm1 =>
        cases h2 : TaylorModel.fromExpr? e2 domain degree with
        | none => simp [TaylorModel.fromExpr?, h1, h2] at h
        | some tm2 =>
          simp [TaylorModel.fromExpr?, h1, h2] at h
          cases h
          have hc := ih1 degree tm1 h1
          simp [TaylorModel.add, hc]
  | mul e1 e2 ih1 ih2 =>
      intro tm h
      cases h1 : TaylorModel.fromExpr? e1 domain degree with
      | none => simp [TaylorModel.fromExpr?, h1] at h
      | some tm1 =>
        cases h2 : TaylorModel.fromExpr? e2 domain degree with
        | none => simp [TaylorModel.fromExpr?, h1, h2] at h
        | some tm2 =>
          simp [TaylorModel.fromExpr?, h1, h2] at h
          cases h
          have hc := ih1 degree tm1 h1
          simp [TaylorModel.mul, hc]
  | neg e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.neg, ih degree tm0 h0]
  | inv e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        by_cases hz : IntervalRat.containsZero tm0.bound
        · have hcontra : False := by simp [TaylorModel.fromExpr?, h0, hz] at h
          exact hcontra.elim
        · simp [TaylorModel.fromExpr?, h0, hz] at h; cases h; simp [TaylorModel.inv, ih degree tm0 h0]
  | exp e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.exp, ih degree tm0 h0]
  | sin e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.sin, ih degree tm0 h0]
  | cos e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.cos, ih degree tm0 h0]
  | log e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp only [TaylorModel.fromExpr?, h0, bind, Option.bind_some] at h
        unfold TaylorModel.log? at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact ih degree tm0 h0
        · simp_all
  | atan _ _ =>
      intro tm h
      simp [TaylorModel.fromExpr?] at h
  | arsinh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.asinh, ih degree tm0 h0]
  | atanh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp only [TaylorModel.fromExpr?, h0, bind, Option.bind_some] at h
        unfold TaylorModel.atanh? at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact ih degree tm0 h0
        · simp_all
  | sinc e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.sinc, ih degree tm0 h0]
  | erf _ _ =>
      intro tm h
      simp [TaylorModel.fromExpr?] at h
  | sinh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.sinh, ih degree tm0 h0]
  | cosh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.cosh, ih degree tm0 h0]
  | tanh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.tanh, ih degree tm0 h0]
  | sqrt e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        unfold TaylorModel.sqrt? at h
        simp only [Option.some.injEq] at h
        cases h
        exact ih degree tm0 h0
  | pi =>
      intro tm h
      simp [TaylorModel.fromExpr?] at h
      cases h
      rfl

namespace TaylorModel

/-- Composition lemma (addition): if sub-evaluations are in their evalSets, the sum is in
the evalSet of the added TM (centers must match). -/
theorem add_evalSet_correct
    (e1 e2 : Expr) (domain : IntervalRat)
    (tm1 tm2 : TaylorModel)
    (hcenter : tm1.center = tm2.center)
    (hf1 : ∀ x ∈ domain, Expr.eval (fun _ => x) e1 ∈ tm1.evalSet x)
    (hf2 : ∀ x ∈ domain, Expr.eval (fun _ => x) e2 ∈ tm2.evalSet x) :
    ∀ x ∈ domain,
      Expr.eval (fun _ => x) (Expr.add e1 e2) ∈ (TaylorModel.add tm1 tm2).evalSet x := by
  intro x hx
  have h1 := hf1 x hx
  have h2 := hf2 x hx
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq] at h1 h2
  rcases h1 with ⟨r1, hr1, hr1eq⟩
  rcases h2 with ⟨r2, hr2, hr2eq⟩
  have hxcent : (x - (tm2.center : ℝ)) = (x - tm1.center) := by
    have hcast : (tm2.center : ℝ) = tm1.center := by exact_mod_cast hcenter.symm
    simp [hcast]
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq, TaylorModel.add]
  refine ⟨r1 + r2, ?_, ?_⟩
  · exact IntervalRat.mem_add hr1 hr2
  · have hmap :
        Polynomial.aeval (x - tm1.center) (tm1.poly + tm2.poly)
          = Polynomial.aeval (x - tm1.center) tm1.poly
            + Polynomial.aeval (x - tm1.center) tm2.poly :=
      (Polynomial.aeval (x - tm1.center)).map_add tm1.poly tm2.poly
    calc
      Expr.eval (fun _ => x) (Expr.add e1 e2)
          = (Polynomial.aeval (x - tm1.center) tm1.poly
              + Polynomial.aeval (x - tm1.center) tm2.poly) + (r1 + r2) := by
            simp [Expr.eval_add, hr1eq, hr2eq,
                  add_comm, add_left_comm, add_assoc, hxcent]
      _ = Polynomial.aeval (x - tm1.center) (tm1.poly + tm2.poly) + (r1 + r2) := by
            simp [hmap]

/-- If `e` evaluates into `tm.evalSet x` on the domain, then `-e` evaluates into
    `(neg tm).evalSet x` on the domain. -/
theorem neg_evalSet_correct
    (e : Expr) (domain : IntervalRat)
    (tm : TaylorModel)
    (hf : ∀ x ∈ domain, Expr.eval (fun _ => x) e ∈ tm.evalSet x) :
    ∀ x ∈ domain, Expr.eval (fun _ => x) (Expr.neg e) ∈ (TaylorModel.neg tm).evalSet x := by
  intro x hx
  have h := hf x hx
  simp only [TaylorModel.evalSet, Set.mem_setOf_eq] at h
  rcases h with ⟨r, hr, hre⟩
  refine ⟨-r, IntervalRat.mem_neg hr, ?eq⟩
  simp [Expr.eval_neg, TaylorModel.neg, hre, map_neg, add_comm]

/-! ### Correctness of transcendental operations -/

/-- sin preserves evalSet membership. -/
theorem sin_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.sin (f x) ∈ (TaylorModel.sin tm degree).evalSet x := by
  intro x hx
  simp only [sin, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.sin (f x), ?_, ?_⟩
  · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
    have hsin_evalSet := tmSin_correct tm.bound degree (f x) hfbound
    have hdomain : (tmSin tm.bound degree).domain = tm.bound := rfl
    have hfx_in_dom : f x ∈ (tmSin tm.bound degree).domain := hdomain ▸ hfbound
    have hsin_bound : Real.sin (f x) ∈ (tmSin tm.bound degree).bound := by
      apply taylorModel_correct (tmSin tm.bound degree) Real.sin
        (fun z hz => tmSin_correct tm.bound degree z hz) (f x) hfx_in_dom
    exact hsin_bound
  · simp only [Polynomial.aeval_zero]; ring

/-- cos preserves evalSet membership. -/
theorem cos_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.cos (f x) ∈ (TaylorModel.cos tm degree).evalSet x := by
  intro x hx
  simp only [cos, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.cos (f x), ?_, ?_⟩
  · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
    have hdomain : (tmCos tm.bound degree).domain = tm.bound := rfl
    have hfx_in_dom : f x ∈ (tmCos tm.bound degree).domain := hdomain ▸ hfbound
    have hcos_bound : Real.cos (f x) ∈ (tmCos tm.bound degree).bound := by
      apply taylorModel_correct (tmCos tm.bound degree) Real.cos
        (fun z hz => tmCos_correct tm.bound degree z hz) (f x) hfx_in_dom
    exact hcos_bound
  · simp only [Polynomial.aeval_zero]; ring

/-- exp preserves evalSet membership. -/
theorem exp_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.exp (f x) ∈ (TaylorModel.exp tm degree).evalSet x := by
  intro x hx
  simp only [exp, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.exp (f x), ?_, ?_⟩
  · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
    have hdomain : (tmExp tm.bound degree).domain = tm.bound := rfl
    have hfx_in_dom : f x ∈ (tmExp tm.bound degree).domain := hdomain ▸ hfbound
    have hexp_bound : Real.exp (f x) ∈ (tmExp tm.bound degree).bound := by
      apply taylorModel_correct (tmExp tm.bound degree) Real.exp
        (fun z hz => tmExp_correct tm.bound degree z hz) (f x) hfx_in_dom
    exact hexp_bound
  · simp only [Polynomial.aeval_zero]; ring

/-- sinh preserves evalSet membership. -/
theorem sinh_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.sinh (f x) ∈ (TaylorModel.sinh tm degree).evalSet x := by
  intro x hx
  simp only [sinh, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.sinh (f x), ?_, ?_⟩
  · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
    have hdomain : (tmSinh tm.bound degree).domain = tm.bound := rfl
    have hfx_in_dom : f x ∈ (tmSinh tm.bound degree).domain := hdomain ▸ hfbound
    have hsinh_bound : Real.sinh (f x) ∈ (tmSinh tm.bound degree).bound := by
      apply taylorModel_correct (tmSinh tm.bound degree) Real.sinh
        (fun z hz => tmSinh_correct tm.bound degree z hz) (f x) hfx_in_dom
    exact hsinh_bound
  · simp only [Polynomial.aeval_zero]; ring

/-- cosh preserves evalSet membership. -/
theorem cosh_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.cosh (f x) ∈ (TaylorModel.cosh tm degree).evalSet x := by
  intro x hx
  simp only [cosh, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.cosh (f x), ?_, ?_⟩
  · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
    have hdomain : (tmCosh tm.bound degree).domain = tm.bound := rfl
    have hfx_in_dom : f x ∈ (tmCosh tm.bound degree).domain := hdomain ▸ hfbound
    have hcosh_bound : Real.cosh (f x) ∈ (tmCosh tm.bound degree).bound := by
      apply taylorModel_correct (tmCosh tm.bound degree) Real.cosh
        (fun z hz => tmCosh_correct tm.bound degree z hz) (f x) hfx_in_dom
    exact hcosh_bound
  · simp only [Polynomial.aeval_zero]; ring

/-- asinh preserves evalSet membership. -/
theorem asinh_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.arsinh (f x) ∈ (TaylorModel.asinh tm degree).evalSet x := by
  intro x hx
  simp only [asinh, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.arsinh (f x), ?_, ?_⟩
  · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
    have hdomain : (tmAsinh tm.bound degree).domain = tm.bound := rfl
    have hfx_in_dom : f x ∈ (tmAsinh tm.bound degree).domain := hdomain ▸ hfbound
    have hasinh_bound : Real.arsinh (f x) ∈ (tmAsinh tm.bound degree).bound := by
      apply taylorModel_correct (tmAsinh tm.bound degree) Real.arsinh
        (fun z hz => tmAsinh_correct tm.bound degree z hz) (f x) hfx_in_dom
    exact hasinh_bound
  · simp only [Polynomial.aeval_zero]; ring

/-- sinc preserves evalSet membership. -/
theorem sinc_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.sinc (f x) ∈ (TaylorModel.sinc tm degree).evalSet x := by
  intro x hx
  simp only [sinc, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.sinc (f x), ?_, ?_⟩
  · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
    have hdomain : (tmSinc tm.bound degree).domain = tm.bound := rfl
    have hfx_in_dom : f x ∈ (tmSinc tm.bound degree).domain := hdomain ▸ hfbound
    have hsinc_bound : Real.sinc (f x) ∈ (tmSinc tm.bound degree).bound := by
      apply taylorModel_correct (tmSinc tm.bound degree) Real.sinc
        (fun z hz => tmSinc_correct tm.bound degree z hz) (f x) hfx_in_dom
    exact hsinc_bound
  · simp only [Polynomial.aeval_zero]; ring

/-- Global bound for tanh: tanh(x) ∈ [-1, 1] for all x. -/
private theorem tanh_mem_Icc (x : ℝ) : Real.tanh x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc, Real.tanh_eq_sinh_div_cosh]
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have habs_sinh_le : |Real.sinh x| ≤ Real.cosh x := abs_sinh_le_cosh x
  constructor
  · rw [le_div_iff₀ hcosh_pos]
    have := neg_abs_le (Real.sinh x)
    linarith [habs_sinh_le]
  · rw [div_le_one hcosh_pos]
    exact le_trans (le_abs_self _) habs_sinh_le

/-- Helper: bound contains values when they're in remainder range and polyBound ≥ 0 -/
private theorem bound_contains_neg_one_one (tm : TaylorModel)
    (y : ℝ) (hlo : -1 ≤ y) (hhi : y ≤ 1)
    (hrem_lo : tm.remainder.lo = -1) (hrem_hi : tm.remainder.hi = 1) :
    y ∈ tm.bound := by
  simp only [bound, IntervalRat.mem_def, IntervalRat.add, polyBoundInterval]
  have hB_nn : 0 ≤ boundPolyAbs tm.poly tm.domain tm.center :=
    boundPolyAbs_nonneg tm.poly tm.domain tm.center
  have hB_nn_real : (0 : ℝ) ≤ (boundPolyAbs tm.poly tm.domain tm.center : ℝ) :=
    Rat.cast_nonneg.mpr hB_nn
  constructor
  · simp only [hrem_lo, Rat.cast_add, Rat.cast_neg, Rat.cast_one]
    linarith
  · simp only [hrem_hi, Rat.cast_add, Rat.cast_one]
    linarith

/-- tanh preserves evalSet membership. -/
theorem tanh_evalSet_correct
    (f : ℝ → ℝ) (tm : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x) :
    ∀ x ∈ tm.domain, Real.tanh (f x) ∈ (TaylorModel.tanh tm degree).evalSet x := by
  intro x hx
  simp only [tanh, evalSet, Set.mem_setOf_eq]
  refine ⟨Real.tanh (f x), ?_, ?_⟩
  · have htanh_bound := tanh_mem_Icc (f x)
    simp only [Set.mem_Icc] at htanh_bound
    simp only [tmTanh]
    split_ifs with h
    · apply bound_contains_neg_one_one _ _ htanh_bound.1 htanh_bound.2 rfl rfl
    · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
      have hsinh_evalSet : Real.sinh (f x) ∈ (tmSinh tm.bound degree).evalSet (f x) :=
        tmSinh_correct tm.bound degree (f x) hfbound
      have hcosh_evalSet : Real.cosh (f x) ∈ (tmCosh tm.bound degree).evalSet (f x) :=
        tmCosh_correct tm.bound degree (f x) hfbound
      have hinv_evalSet : (Real.cosh (f x))⁻¹ ∈ (inv (tmCosh tm.bound degree) h).evalSet (f x) := by
        apply inv_evalSet_correct Real.cosh (tmCosh tm.bound degree) h
        · intro z hz
          exact tmCosh_correct tm.bound degree z hz
        · exact hfbound
      have htanh_eq : Real.tanh (f x) = Real.sinh (f x) * (Real.cosh (f x))⁻¹ := by
        rw [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv]
      rw [htanh_eq]
      have hmul_evalSet := mul_evalSet_correct Real.sinh (fun y => (Real.cosh y)⁻¹)
        (tmSinh tm.bound degree) (inv (tmCosh tm.bound degree) h) degree rfl rfl
        (fun z hz => tmSinh_correct tm.bound degree z hz)
        (fun z hz => inv_evalSet_correct Real.cosh (tmCosh tm.bound degree) h
          (fun w hw => tmCosh_correct tm.bound degree w hw) z hz)
        (f x) hfbound
      exact taylorModel_correct
        (mul (tmSinh tm.bound degree) (inv (tmCosh tm.bound degree) h) degree)
        (fun y => Real.sinh y * (Real.cosh y)⁻¹)
        (fun z hz => mul_evalSet_correct Real.sinh (fun w => (Real.cosh w)⁻¹)
          (tmSinh tm.bound degree) (inv (tmCosh tm.bound degree) h) degree rfl rfl
          (fun w hw => tmSinh_correct tm.bound degree w hw)
          (fun w hw => inv_evalSet_correct Real.cosh (tmCosh tm.bound degree) h
            (fun v hv => tmCosh_correct tm.bound degree v hv) w hw) z hz)
        (f x) hfbound
  · simp only [Polynomial.aeval_zero]; ring

/-- atanh preserves evalSet membership when atanh? succeeds. -/
theorem atanh_evalSet_correct'
    (f : ℝ → ℝ) (tm result : TaylorModel) (degree : ℕ)
    (hf : ∀ x ∈ tm.domain, f x ∈ tm.evalSet x)
    (hatanh : atanh? tm degree = some result) :
    ∀ x ∈ tm.domain, Real.atanh (f x) ∈ result.evalSet x := by
  intro x hx
  -- Extract that the domain is safe from the fact that atanh? succeeded
  unfold atanh? at hatanh
  split at hatanh
  · rename_i hsafe
    simp only [Option.some.injEq] at hatanh
    subst hatanh
    simp only [evalSet, Set.mem_setOf_eq]
    refine ⟨Real.atanh (f x), ?_, ?_⟩
    · have hfbound : f x ∈ tm.bound := taylorModel_correct tm f hf x hx
      have hsafe_bound : max (|tm.bound.lo|) (|tm.bound.hi|) ≤ 99/100 := by
        simp only [atanhSafe, decide_eq_true_eq] at hsafe
        exact_mod_cast hsafe
      have habs : |f x| < 1 := abs_lt_one_of_atanhSafe hsafe hfbound
      have hdomain : (tmAtanh tm.bound degree).domain = tm.bound := rfl
      have hfx_in_dom : f x ∈ (tmAtanh tm.bound degree).domain := hdomain ▸ hfbound
      have hatanh_bound : Real.atanh (f x) ∈ (tmAtanh tm.bound degree).bound := by
        apply taylorModel_correct (tmAtanh tm.bound degree) Real.atanh
          (fun z hz => tmAtanh_correct tm.bound degree hsafe_bound z hz
            (abs_lt_one_of_atanhSafe hsafe hz)) (f x) hfx_in_dom
      exact hatanh_bound
    · simp only [Polynomial.aeval_zero]; ring
  · simp at hatanh

end TaylorModel

/-! ### Main fromExpr correctness -/

/-- Helper: fromExpr? produces TaylorModels with matching domain. -/
theorem fromExpr?_domain (e : Expr) (domain : IntervalRat) (degree : ℕ)
    (tm : TaylorModel) (h : TaylorModel.fromExpr? e domain degree = some tm) :
    tm.domain = domain := by
  revert tm
  induction e generalizing degree with
  | const q =>
      intro tm h; simp [TaylorModel.fromExpr?] at h; cases h; simp [TaylorModel.const]
  | var idx =>
      intro tm h; simp [TaylorModel.fromExpr?] at h; cases h; simp [TaylorModel.identity]
  | add e1 e2 ih1 ih2 =>
      intro tm h
      cases h1 : TaylorModel.fromExpr? e1 domain degree with
      | none => simp [TaylorModel.fromExpr?, h1] at h
      | some tm1 =>
        cases h2 : TaylorModel.fromExpr? e2 domain degree with
        | none => simp [TaylorModel.fromExpr?, h1, h2] at h
        | some tm2 =>
          simp [TaylorModel.fromExpr?, h1, h2] at h
          cases h; simp [TaylorModel.add, ih1 degree tm1 h1]
  | mul e1 e2 ih1 ih2 =>
      intro tm h
      cases h1 : TaylorModel.fromExpr? e1 domain degree with
      | none => simp [TaylorModel.fromExpr?, h1] at h
      | some tm1 =>
        cases h2 : TaylorModel.fromExpr? e2 domain degree with
        | none => simp [TaylorModel.fromExpr?, h1, h2] at h
        | some tm2 =>
          simp [TaylorModel.fromExpr?, h1, h2] at h
          cases h; simp [TaylorModel.mul, ih1 degree tm1 h1]
  | neg e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h; simp [TaylorModel.neg, ih degree tm0 h0]
  | inv e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        by_cases hz : IntervalRat.containsZero tm0.bound
        · have hcontra : False := by simp [TaylorModel.fromExpr?, h0, hz] at h
          exact hcontra.elim
        · simp [TaylorModel.fromExpr?, h0, hz] at h; cases h; simp [TaylorModel.inv, ih degree tm0 h0]
  | exp e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h; simp [TaylorModel.exp, ih degree tm0 h0]
  | sin e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h; simp [TaylorModel.sin, ih degree tm0 h0]
  | cos e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h; simp [TaylorModel.cos, ih degree tm0 h0]
  | log e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp only [TaylorModel.fromExpr?, h0, bind, Option.bind_some] at h
        unfold TaylorModel.log? at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact ih degree tm0 h0
        · simp_all
  | atan _ _ =>
      intro tm h
      simp [TaylorModel.fromExpr?] at h
  | arsinh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.asinh, ih degree tm0 h0]
  | atanh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp only [TaylorModel.fromExpr?, h0, bind, Option.bind_some] at h
        unfold TaylorModel.atanh? at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact ih degree tm0 h0
        · simp_all
  | sinc e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        cases h
        simp [TaylorModel.sinc, ih degree tm0 h0]
  | erf _ _ =>
      intro tm h
      simp [TaylorModel.fromExpr?] at h
  | sinh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h; simp [TaylorModel.sinh, ih degree tm0 h0]
  | cosh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h; simp [TaylorModel.cosh, ih degree tm0 h0]
  | tanh e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h; simp [TaylorModel.tanh, ih degree tm0 h0]
  | sqrt e ih =>
      intro tm h
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        unfold TaylorModel.sqrt? at h
        simp only [Option.some.injEq] at h
        cases h
        exact ih degree tm0 h0
  | pi =>
      intro tm h
      simp [TaylorModel.fromExpr?] at h
      cases h
      rfl

/-- Core evalSet correctness: if fromExpr? succeeds, evaluation is in evalSet. -/
theorem fromExpr_evalSet_correct (e : Expr) (domain : IntervalRat) (degree : ℕ)
    (tm : TaylorModel) (h : TaylorModel.fromExpr? e domain degree = some tm) :
    ∀ x ∈ domain, Expr.eval (fun _ => x) e ∈ tm.evalSet x := by
  induction e generalizing degree tm with
  | const q =>
      simp [TaylorModel.fromExpr?] at h; cases h
      exact TaylorModel.const_evalSet_correct q domain
  | var _ =>
      simp [TaylorModel.fromExpr?] at h; cases h
      exact TaylorModel.identity_evalSet_correct domain
  | add e1 e2 ih1 ih2 =>
      cases h1 : TaylorModel.fromExpr? e1 domain degree with
      | none => simp [TaylorModel.fromExpr?, h1] at h
      | some tm1 =>
        cases h2 : TaylorModel.fromExpr? e2 domain degree with
        | none => simp [TaylorModel.fromExpr?, h1, h2] at h
        | some tm2 =>
          simp [TaylorModel.fromExpr?, h1, h2] at h; cases h
          have hc := fromExpr?_center e1 domain degree tm1 h1
          have hc2 := fromExpr?_center e2 domain degree tm2 h2
          exact TaylorModel.add_evalSet_correct e1 e2 domain tm1 tm2
            (hc.trans hc2.symm)
            (ih1 degree tm1 h1)
            (ih2 degree tm2 h2)
  | mul e1 e2 ih1 ih2 =>
      cases h1 : TaylorModel.fromExpr? e1 domain degree with
      | none => simp [TaylorModel.fromExpr?, h1] at h
      | some tm1 =>
        cases h2 : TaylorModel.fromExpr? e2 domain degree with
        | none => simp [TaylorModel.fromExpr?, h1, h2] at h
        | some tm2 =>
          simp [TaylorModel.fromExpr?, h1, h2] at h; cases h
          have hc := fromExpr?_center e1 domain degree tm1 h1
          have hc2 := fromExpr?_center e2 domain degree tm2 h2
          have hd1 := fromExpr?_domain e1 domain degree tm1 h1
          have hd2 := fromExpr?_domain e2 domain degree tm2 h2
          intro x hx
          simp only [Expr.eval_mul]
          have hx1 : x ∈ tm1.domain := hd1 ▸ hx
          exact TaylorModel.mul_evalSet_correct (fun y => Expr.eval (fun _ => y) e1)
            (fun y => Expr.eval (fun _ => y) e2) tm1 tm2 degree
            (hc.trans hc2.symm) (hd1.trans hd2.symm)
            (hd1.symm ▸ ih1 degree tm1 h1) (hd2.symm ▸ ih2 degree tm2 h2) x hx1
  | neg e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        exact TaylorModel.neg_evalSet_correct e domain tm0 (ih degree tm0 h0)
  | inv e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        by_cases hz : IntervalRat.containsZero tm0.bound
        · have hcontra : False := by simp [TaylorModel.fromExpr?, h0, hz] at h
          exact hcontra.elim
        · simp [TaylorModel.fromExpr?, h0, hz] at h; cases h
          have hd0 := fromExpr?_domain e domain degree tm0 h0
          intro x hx
          simp only [Expr.eval_inv]
          have hx0 : x ∈ tm0.domain := hd0 ▸ hx
          exact TaylorModel.inv_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 hz
            (hd0.symm ▸ ih degree tm0 h0) x hx0
  | exp e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_exp]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.exp_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | sin e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_sin]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.sin_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | cos e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_cos]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.cos_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | log e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp only [TaylorModel.fromExpr?, h0, bind, Option.bind_some] at h
        unfold TaylorModel.log? at h
        split at h
        · rename_i logTM hlog
          simp only [Option.some.injEq] at h
          subst h
          have hd0 := fromExpr?_domain e domain degree tm0 h0
          intro x hx
          simp only [Expr.eval_log]
          -- Log evalSet correctness: need to show Real.log (f x) ∈ logTM.bound
          -- when f x ∈ tm0.bound (which is satisfied by ih)
          have hx0 : x ∈ tm0.domain := hd0 ▸ hx
          have _h_arg_in_evalSet : Expr.eval (fun _ => x) e ∈ tm0.evalSet x := ih degree tm0 h0 x hx
          have _h_arg_in_bound : Expr.eval (fun _ => x) e ∈ tm0.bound :=
            taylorModel_correct tm0 (fun y => Expr.eval (fun _ => y) e) (hd0.symm ▸ ih degree tm0 h0) x hx0
          simp only [TaylorModel.evalSet, Set.mem_setOf_eq]
          refine ⟨Real.log (Expr.eval (fun _ => x) e), ?_, ?_⟩
          · -- Use tmLog_correct: log z ∈ logTM.evalSet z, then taylorModel_correct
            -- logTM.domain = tm0.bound by definition of TaylorModel.tmLog
            have hlogTM_domain : logTM.domain = tm0.bound := by
              unfold TaylorModel.tmLog at hlog
              split_ifs at hlog with hpos
              · simp only [Option.some.injEq] at hlog
                rw [← hlog]
            -- Use tmLog_correct with z ∈ tm0.bound
            have hlog_evalSet := TaylorModel.tmLog_correct tm0.bound degree logTM hlog
              (Expr.eval (fun _ => x) e) _h_arg_in_bound
            -- Convert domain membership for taylorModel_correct
            have hz_in_logTM_domain : Expr.eval (fun _ => x) e ∈ logTM.domain :=
              hlogTM_domain ▸ _h_arg_in_bound
            exact taylorModel_correct logTM Real.log
              (fun w hw => TaylorModel.tmLog_correct tm0.bound degree logTM hlog w
                (hlogTM_domain.symm ▸ hw))
              (Expr.eval (fun _ => x) e) hz_in_logTM_domain
          · simp only [Polynomial.aeval_zero]; ring
        · simp_all
  | atan _ _ =>
      simp [TaylorModel.fromExpr?] at h
  | arsinh e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_arsinh]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.asinh_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | atanh e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp only [TaylorModel.fromExpr?, h0, bind, Option.bind_some] at h
        cases hatanh : TaylorModel.atanh? tm0 degree with
        | none => simp [hatanh] at h
        | some result =>
          simp only [hatanh, Option.some.injEq] at h
          subst h
          have hd0 := fromExpr?_domain e domain degree tm0 h0
          intro x hx
          simp only [Expr.eval_atanh]
          have hx0 : x ∈ tm0.domain := hd0 ▸ hx
          exact TaylorModel.atanh_evalSet_correct' (fun y => Expr.eval (fun _ => y) e) tm0 result degree
            (hd0.symm ▸ ih degree tm0 h0) hatanh x hx0
  | sinc e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_sinc]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.sinc_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | erf _ _ =>
      simp [TaylorModel.fromExpr?] at h
  | sinh e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_sinh]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.sinh_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | cosh e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_cosh]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.cosh_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | tanh e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h; cases h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_tanh]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        exact TaylorModel.tanh_evalSet_correct (fun y => Expr.eval (fun _ => y) e) tm0 degree
          (hd0.symm ▸ ih degree tm0 h0) x hx0
  | sqrt e ih =>
      cases h0 : TaylorModel.fromExpr? e domain degree with
      | none => simp [TaylorModel.fromExpr?, h0] at h
      | some tm0 =>
        simp [TaylorModel.fromExpr?, h0] at h
        unfold TaylorModel.sqrt? at h
        simp only [Option.some.injEq] at h
        subst h
        have hd0 := fromExpr?_domain e domain degree tm0 h0
        intro x hx
        simp only [Expr.eval_sqrt]
        have hx0 : x ∈ tm0.domain := hd0 ▸ hx
        have h_arg_in_bound : Expr.eval (fun _ => x) e ∈ tm0.bound :=
          taylorModel_correct tm0 (fun y => Expr.eval (fun _ => y) e) (hd0.symm ▸ ih degree tm0 h0) x hx0
        simp only [TaylorModel.evalSet, Set.mem_setOf_eq]
        refine ⟨Real.sqrt (Expr.eval (fun _ => x) e), ?_, ?_⟩
        · -- sqrt of argument is in sqrtIntervalTight
          exact IntervalRat.mem_sqrtIntervalTight' h_arg_in_bound
        · simp only [Polynomial.aeval_zero]; ring
  | pi =>
      simp [TaylorModel.fromExpr?] at h
      cases h
      intro x _hx
      simp only [Expr.eval_pi, TaylorModel.evalSet, Set.mem_setOf_eq]
      refine ⟨Real.pi, mem_piInterval, ?_⟩
      simp only [Polynomial.aeval_zero]; ring

/-- fromExpr? produces correct Taylor models when it succeeds. -/
theorem fromExpr_correct (e : Expr) (domain : IntervalRat) (degree : ℕ)
    (tm : TaylorModel) (h : TaylorModel.fromExpr? e domain degree = some tm) :
    ∀ x ∈ domain, Expr.eval (fun _ => x) e ∈ tm.bound := by
  have hd := fromExpr?_domain e domain degree tm h
  have hEval := fromExpr_evalSet_correct e domain degree tm h
  intro x hx
  have hx_tm : x ∈ tm.domain := hd ▸ hx
  exact taylorModel_correct tm (fun y => Expr.eval (fun _ => y) e) (hd.symm ▸ hEval) x hx_tm

/-! ### Refined exp interval using Taylor models -/

/-- Refined interval bound for exp using Taylor models.
    For small intervals (width ≤ 1), uses degree-5 Taylor model which gives tight bounds.
    For larger intervals, falls back to the monotonicity-based coarse bound. -/
noncomputable def expIntervalRefined (I : IntervalRat) : IntervalRat :=
  let w := I.width
  if w ≤ 1 then
    (TaylorModel.tmExp I 5).bound
  else
    IntervalRat.expInterval I

/-- FTIA for refined exp: if x ∈ I, then exp(x) ∈ expIntervalRefined I -/
theorem mem_expIntervalRefined {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.exp x ∈ expIntervalRefined I := by
  unfold expIntervalRefined
  by_cases hw : I.width ≤ 1
  · simp only [hw, ↓reduceIte]
    have hEvalSet := TaylorModel.tmExp_correct I 5 x hx
    exact taylorModel_correct (TaylorModel.tmExp I 5) Real.exp
      (fun z hz => TaylorModel.tmExp_correct I 5 z hz) x hx
  · simp only [hw, ↓reduceIte]
    exact IntervalRat.mem_expInterval hx

end LeanCert.Engine
