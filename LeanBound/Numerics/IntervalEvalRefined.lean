/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.TaylorModel
import LeanBound.Numerics.AD

/-!
# Refined Interval Evaluation using Taylor Models

This file provides interval evaluation functions that use Taylor-model-based
bounds for transcendental functions (exp, sin, cos) when the interval is small,
falling back to coarse bounds for larger intervals.

## Main definitions

* `sinIntervalRefined`, `cosIntervalRefined` - Refined bounds using Taylor models
* `evalIntervalRefined` - Interval evaluation using refined bounds
* `evalDualRefined` - AD evaluation using refined bounds

## Design

The refined evaluators give tighter bounds on small intervals by using
Taylor approximations. For example, `expIntervalRefined` uses a degree-5
Taylor model when the interval width is ≤ 1, which gives much tighter bounds
than the monotonicity-based `expInterval`.

The correctness proofs follow directly from the Taylor model correctness
theorems (`mem_expIntervalRefined`, etc.).
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-! ### Refined transcendental intervals

We define refined versions of sin and cos intervals using Taylor models,
following the same pattern as `expIntervalRefined`.
-/

/-- Refined interval bound for sin using Taylor models.
    For small intervals (width ≤ 1), uses degree-5 Taylor model.
    For larger intervals, uses the global [-1, 1] bound. -/
noncomputable def sinIntervalRefined (I : IntervalRat) : IntervalRat :=
  if I.width ≤ 1 then
    (TaylorModel.tmSin I 5).bound
  else
    sinInterval I

/-- FTIA for refined sin: if x ∈ I, then sin(x) ∈ sinIntervalRefined I -/
theorem mem_sinIntervalRefined {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sin x ∈ sinIntervalRefined I := by
  unfold sinIntervalRefined
  by_cases hw : I.width ≤ 1
  · simp only [hw, ↓reduceIte]
    exact taylorModel_correct (TaylorModel.tmSin I 5) Real.sin
      (fun z hz => TaylorModel.tmSin_correct I 5 z hz) x hx
  · simp only [hw, ↓reduceIte]
    exact mem_sinInterval hx

/-- Refined interval bound for cos using Taylor models.
    For small intervals (width ≤ 1), uses degree-5 Taylor model.
    For larger intervals, uses the global [-1, 1] bound. -/
noncomputable def cosIntervalRefined (I : IntervalRat) : IntervalRat :=
  if I.width ≤ 1 then
    (TaylorModel.tmCos I 5).bound
  else
    cosInterval I

/-- FTIA for refined cos: if x ∈ I, then cos(x) ∈ cosIntervalRefined I -/
theorem mem_cosIntervalRefined {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.cos x ∈ cosIntervalRefined I := by
  unfold cosIntervalRefined
  by_cases hw : I.width ≤ 1
  · simp only [hw, ↓reduceIte]
    exact taylorModel_correct (TaylorModel.tmCos I 5) Real.cos
      (fun z hz => TaylorModel.tmCos_correct I 5 z hz) x hx
  · simp only [hw, ↓reduceIte]
    exact mem_cosInterval hx

/-- Refined interval bound for log using Taylor models.
    For strictly positive intervals with width ≤ 1, uses degree-5 Taylor model.
    For larger intervals or non-positive intervals, falls back to coarse bound. -/
noncomputable def logIntervalRefined (I : IntervalRat.IntervalRatPos) : IntervalRat :=
  if I.width ≤ 1 then
    match TaylorModel.tmLog I.toIntervalRat 5 with
    | some logTM => logTM.bound
    | none => IntervalRat.logInterval I  -- Fallback shouldn't happen for positive intervals
  else
    IntervalRat.logInterval I

/-- FTIA for refined log: if x ∈ I and I is positive, then log(x) ∈ logIntervalRefined I -/
theorem mem_logIntervalRefined {x : ℝ} {I : IntervalRat.IntervalRatPos} (hx : x ∈ I.toIntervalRat) :
    Real.log x ∈ logIntervalRefined I := by
  unfold logIntervalRefined
  by_cases hw : I.width ≤ 1
  · simp only [hw, ↓reduceIte]
    cases hlog : TaylorModel.tmLog I.toIntervalRat 5 with
    | none =>
      -- This case shouldn't happen for positive intervals
      simp only [hlog]
      exact IntervalRat.mem_logInterval hx
    | some logTM =>
      simp only [hlog]
      -- Use tmLog_correct: log x ∈ logTM.evalSet x, then taylorModel_correct gives bound
      have h_evalSet := TaylorModel.tmLog_correct I.toIntervalRat 5 logTM hlog x hx
      -- logTM.domain = I.toIntervalRat from tmLog definition
      have hdom : logTM.domain = I.toIntervalRat := by
        simp only [TaylorModel.tmLog, I.lo_pos, ↓reduceDIte, Option.some.injEq] at hlog
        simp only [← hlog]
      exact taylorModel_correct logTM Real.log
        (fun z hz => TaylorModel.tmLog_correct I.toIntervalRat 5 logTM hlog z (hdom ▸ hz)) x (hdom.symm ▸ hx)
  · simp only [hw, ↓reduceIte]
    exact IntervalRat.mem_logInterval hx

/-- Refined interval bound for atanh using Taylor models.
    For small intervals with |x| < 1 and width ≤ 1, uses degree-5 Taylor model.
    For larger intervals, uses computed bound via monotonicity.
    Requires -1 < I.lo and I.hi < 1 for correctness. -/
noncomputable def atanhIntervalRefined' (I : IntervalRat) (hlo : -1 < I.lo) (hhi : I.hi < 1) : IntervalRat :=
  -- Use Taylor model only when interval is small AND radius is bounded away from 1
  if I.width ≤ 1 ∧ max (|I.lo|) (|I.hi|) ≤ 99/100 then
    (TaylorModel.tmAtanh I 5).bound
  else
    -- Use computed bound via monotonicity
    let Iball : IntervalRat.IntervalRatInUnitBall := ⟨I.lo, I.hi, I.le, hlo, hhi⟩
    IntervalRat.atanhIntervalComputed Iball

/-- Refined interval bound for atanh (version without proof arguments, falls back to default) -/
noncomputable def atanhIntervalRefined (I : IntervalRat) : IntervalRat :=
  if h : -1 < I.lo ∧ I.hi < 1 then
    atanhIntervalRefined' I h.1 h.2
  else
    default  -- Not in valid domain

/-- FTIA for refined atanh: if x ∈ I and I ⊂ (-1, 1), then atanh(x) ∈ atanhIntervalRefined I -/
theorem mem_atanhIntervalRefined {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hlo : -1 < I.lo) (hhi : I.hi < 1) :
    Real.atanh x ∈ atanhIntervalRefined I := by
  unfold atanhIntervalRefined
  simp only [hlo, hhi, and_self, ↓reduceDIte]
  unfold atanhIntervalRefined'
  by_cases hw : I.width ≤ 1 ∧ max (|I.lo|) (|I.hi|) ≤ 99/100
  · -- Use Taylor model approach
    simp only [hw, ↓reduceIte]
    have ⟨_, hradius⟩ := hw
    -- Prove |x| < 1 from interval bounds
    have hx_lo : (I.lo : ℝ) ≤ x := hx.1
    have hx_hi : x ≤ I.hi := hx.2
    have hlo_real : (-1 : ℝ) < I.lo := by exact_mod_cast hlo
    have hhi_real : (I.hi : ℝ) < 1 := by exact_mod_cast hhi
    have hx_abs : |x| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    -- Use tmAtanh_correct
    have hdom : (TaylorModel.tmAtanh I 5).domain = I := rfl
    exact taylorModel_correct (TaylorModel.tmAtanh I 5) Real.atanh
      (fun z hz => TaylorModel.tmAtanh_correct I 5 hradius z (hdom ▸ hz) (by
        have hz' : z ∈ I := hdom ▸ hz
        rw [abs_lt]
        have hlo' : (-1 : ℝ) < I.lo := by exact_mod_cast hlo
        have hhi' : (I.hi : ℝ) < 1 := by exact_mod_cast hhi
        constructor <;> linarith [hz'.1, hz'.2])) x hx
  · -- Fallback to computed bound via monotonicity
    simp only [hw, ↓reduceIte]
    let Iball : IntervalRat.IntervalRatInUnitBall := ⟨I.lo, I.hi, I.le, hlo, hhi⟩
    have hx_ball : x ∈ Iball := by
      simp only [Membership.mem, IntervalRat.IntervalRatInUnitBall.mem_def]
      exact hx
    exact IntervalRat.mem_atanhIntervalComputed hx_ball

/-! ### Refined interval evaluation

Interval evaluation that uses Taylor-model-based bounds for transcendental
functions when the interval is reasonably small.
-/

/-- Interval evaluation using refined bounds for transcendentals.
    Uses Taylor-model-based bounds for exp, sin, cos on small intervals.
    For partial functions (inv, log), returns default. Use evalInterval? instead. -/
noncomputable def evalIntervalRefined (e : Expr) (ρ : IntervalEnv) : IntervalRat :=
  match e with
  | Expr.const q => IntervalRat.singleton q
  | Expr.var i => ρ i
  | Expr.add e₁ e₂ => IntervalRat.add (evalIntervalRefined e₁ ρ) (evalIntervalRefined e₂ ρ)
  | Expr.mul e₁ e₂ => IntervalRat.mul (evalIntervalRefined e₁ ρ) (evalIntervalRefined e₂ ρ)
  | Expr.neg e => IntervalRat.neg (evalIntervalRefined e ρ)
  | Expr.inv _ => default  -- Not supported; safe default
  | Expr.sin e => sinIntervalRefined (evalIntervalRefined e ρ)
  | Expr.cos e => cosIntervalRefined (evalIntervalRefined e ρ)
  | Expr.exp e => expIntervalRefined (evalIntervalRefined e ρ)
  | Expr.log _ => default  -- Not supported; use evalInterval? for log
  | Expr.atan e => atanInterval (evalIntervalRefined e ρ)
  | Expr.arsinh e => arsinhInterval (evalIntervalRefined e ρ)
  | Expr.atanh _ => default  -- Partial function; use evalInterval? for atanh
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf _ => ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
  | Expr.sinh e => sinhInterval (evalIntervalRefined e ρ)
  | Expr.cosh e => coshInterval (evalIntervalRefined e ρ)
  | Expr.tanh e => tanhInterval (evalIntervalRefined e ρ)

/-- Single-variable refined interval evaluation -/
noncomputable def evalIntervalRefined1 (e : Expr) (I : IntervalRat) : IntervalRat :=
  evalIntervalRefined e (fun _ => I)

/-- Refined interval evaluation is correct for supported expressions -/
theorem evalIntervalRefined_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ evalIntervalRefined e ρ_int := by
  induction hsupp with
  | const q =>
    simp only [evalIntervalRefined, Expr.eval_const]
    exact IntervalRat.mem_singleton q
  | var i =>
    simp only [evalIntervalRefined, Expr.eval_var]
    exact hρ i
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [evalIntervalRefined, Expr.eval_add]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
    simp only [evalIntervalRefined, Expr.eval_mul]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg h ih =>
    simp only [evalIntervalRefined, Expr.eval_neg]
    exact IntervalRat.mem_neg ih
  | sin h ih =>
    simp only [evalIntervalRefined, Expr.eval_sin]
    exact mem_sinIntervalRefined ih
  | cos h ih =>
    simp only [evalIntervalRefined, Expr.eval_cos]
    exact mem_cosIntervalRefined ih
  | exp h ih =>
    simp only [evalIntervalRefined, Expr.eval_exp]
    exact mem_expIntervalRefined ih

/-- Single-variable refined evaluation is correct -/
theorem evalIntervalRefined1_correct (e : Expr) (hsupp : ExprSupported e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ evalIntervalRefined1 e I :=
  evalIntervalRefined_correct e hsupp (fun _ => x) (fun _ => I) (fun _ => hx)

/-! ### Refined dual interval (AD) evaluation

Automatic differentiation using refined interval bounds.
-/

/-- Refined dual interval for exp -/
noncomputable def DualInterval.expRefined (d : DualInterval) : DualInterval :=
  { val := expIntervalRefined d.val
    der := IntervalRat.mul (expIntervalRefined d.val) d.der }

/-- Refined dual interval for sin: d/dx sin(f(x)) = cos(f(x)) * f'(x) -/
noncomputable def DualInterval.sinRefined (d : DualInterval) : DualInterval :=
  { val := sinIntervalRefined d.val
    der := IntervalRat.mul (cosIntervalRefined d.val) d.der }

/-- Refined dual interval for cos: d/dx cos(f(x)) = -sin(f(x)) * f'(x) -/
noncomputable def DualInterval.cosRefined (d : DualInterval) : DualInterval :=
  { val := cosIntervalRefined d.val
    der := IntervalRat.mul (IntervalRat.neg (sinIntervalRefined d.val)) d.der }

/-- Refined dual interval evaluation.
    For partial functions (inv, log), returns default. -/
noncomputable def evalDualRefined (e : Expr) (ρ : DualEnv) : DualInterval :=
  match e with
  | Expr.const q => DualInterval.const q
  | Expr.var i => ρ i
  | Expr.add e₁ e₂ => DualInterval.add (evalDualRefined e₁ ρ) (evalDualRefined e₂ ρ)
  | Expr.mul e₁ e₂ => DualInterval.mul (evalDualRefined e₁ ρ) (evalDualRefined e₂ ρ)
  | Expr.neg e => DualInterval.neg (evalDualRefined e ρ)
  | Expr.inv _ => default  -- Not supported; safe default
  | Expr.sin e => DualInterval.sinRefined (evalDualRefined e ρ)
  | Expr.cos e => DualInterval.cosRefined (evalDualRefined e ρ)
  | Expr.exp e => DualInterval.expRefined (evalDualRefined e ρ)
  | Expr.log _ => default  -- Not supported; use partial evaluation instead
  | Expr.atan e => DualInterval.atan (evalDualRefined e ρ)
  | Expr.arsinh e => DualInterval.arsinh (evalDualRefined e ρ)
  | Expr.atanh _ => default  -- Partial function; use partial evaluation instead
  | Expr.sinc e => DualInterval.sinc (evalDualRefined e ρ)
  | Expr.erf e => DualInterval.erf (evalDualRefined e ρ)
  | Expr.sinh e => DualInterval.sinh (evalDualRefined e ρ)
  | Expr.cosh e => DualInterval.cosh (evalDualRefined e ρ)
  | Expr.tanh e => DualInterval.tanh (evalDualRefined e ρ)

/-- Single-variable refined dual evaluation -/
noncomputable def evalDualRefined1 (e : Expr) (I : IntervalRat) : DualInterval :=
  evalDualRefined e (fun _ => DualInterval.varActive I)

/-! ### Correctness of refined dual evaluation -/

/-- Refined exp preserves value correctness -/
theorem DualInterval.expRefined_val_mem {d : DualInterval} {x : ℝ} (hx : x ∈ d.val) :
    Real.exp x ∈ (DualInterval.expRefined d).val := by
  simp only [DualInterval.expRefined]
  exact mem_expIntervalRefined hx

/-- Refined sin preserves value correctness -/
theorem DualInterval.sinRefined_val_mem {d : DualInterval} {x : ℝ} (hx : x ∈ d.val) :
    Real.sin x ∈ (DualInterval.sinRefined d).val := by
  simp only [DualInterval.sinRefined]
  exact mem_sinIntervalRefined hx

/-- Refined cos preserves value correctness -/
theorem DualInterval.cosRefined_val_mem {d : DualInterval} {x : ℝ} (hx : x ∈ d.val) :
    Real.cos x ∈ (DualInterval.cosRefined d).val := by
  simp only [DualInterval.cosRefined]
  exact mem_cosIntervalRefined hx

/-- atan preserves value correctness -/
theorem DualInterval.atan_val_mem {d : DualInterval} {x : ℝ} (hx : x ∈ d.val) :
    Real.arctan x ∈ (DualInterval.atan d).val := by
  simp only [DualInterval.atan]
  exact mem_atanInterval hx

/-- arsinh preserves value correctness -/
theorem DualInterval.arsinh_val_mem {d : DualInterval} {x : ℝ} (hx : x ∈ d.val) :
    Real.arsinh x ∈ (DualInterval.arsinh d).val := by
  simp only [DualInterval.arsinh]
  exact mem_arsinhInterval hx

/-- Refined dual evaluation value is correct for supported expressions -/
theorem evalDualRefined_val_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv) (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ (evalDualRefined e ρ_dual).val := by
  induction hsupp with
  | const q =>
    simp only [evalDualRefined, Expr.eval_const, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var i =>
    simp only [evalDualRefined, Expr.eval_var]
    exact hρ i
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [evalDualRefined, Expr.eval_add, DualInterval.add]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
    simp only [evalDualRefined, Expr.eval_mul, DualInterval.mul]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg h ih =>
    simp only [evalDualRefined, Expr.eval_neg, DualInterval.neg]
    exact IntervalRat.mem_neg ih
  | sin h ih =>
    simp only [evalDualRefined, Expr.eval_sin]
    exact DualInterval.sinRefined_val_mem ih
  | cos h ih =>
    simp only [evalDualRefined, Expr.eval_cos]
    exact DualInterval.cosRefined_val_mem ih
  | exp h ih =>
    simp only [evalDualRefined, Expr.eval_exp]
    exact DualInterval.expRefined_val_mem ih

/-- Single-variable refined dual evaluation is correct for values -/
theorem evalDualRefined1_val_correct (e : Expr) (hsupp : ExprSupported e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ (evalDualRefined1 e I).val := by
  apply evalDualRefined_val_correct e hsupp (fun _ => x) (fun _ => DualInterval.varActive I)
  intro i
  simp only [DualInterval.varActive]
  exact hx

end LeanBound.Numerics
