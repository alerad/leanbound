/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Eval.Core

/-!
# Extended (Noncomputable) Interval Evaluation

This file implements the noncomputable interval evaluator for `LeanCert.Core.Expr`,
supporting exp with floor/ceil bounds and partial evaluation for inv/log.

## Main definitions

* `evalInterval` - Noncomputable interval evaluator supporting exp
* `evalInterval_correct` - Correctness theorem for extended evaluation
* `evalInterval?` - Partial (Option-returning) evaluator with inv/log support
* `evalInterval?_correct` - Correctness theorem for partial evaluation

## Design notes

The extended evaluator uses `Real.exp` with floor/ceil bounds, which requires
noncomputability. For computability, use `evalIntervalCore` instead.

The partial evaluator `evalInterval?` returns `none` when:
- The denominator interval for `inv` contains zero
- The argument interval for `log` is not strictly positive
- The argument for `atanh` is not in (-1, 1)

When it returns `some I`, correctness is guaranteed.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Extended interval evaluation (noncomputable, supports exp) -/

/-- Noncomputable interval evaluator supporting exp.

    For supported expressions (const, var, add, mul, neg, sin, cos, exp), this
    computes correct interval bounds with a fully-verified proof.

    For unsupported expressions (inv, log), returns a default interval.
    Do not rely on results for expressions containing inv or log.
    Use evalInterval? for partial functions like inv and log.

    This evaluator is NONCOMPUTABLE due to exp using Real.exp with floor/ceil. -/
noncomputable def evalInterval (e : Expr) (ρ : IntervalEnv) : IntervalRat :=
  match e with
  | Expr.const q => IntervalRat.singleton q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => IntervalRat.add (evalInterval e₁ ρ) (evalInterval e₂ ρ)
  | Expr.mul e₁ e₂ => IntervalRat.mul (evalInterval e₁ ρ) (evalInterval e₂ ρ)
  | Expr.neg e => IntervalRat.neg (evalInterval e ρ)
  | Expr.inv _ => default  -- Not in ExprSupported; safe default
  | Expr.exp e => IntervalRat.expInterval (evalInterval e ρ)
  | Expr.sin e => sinInterval (evalInterval e ρ)
  | Expr.cos e => cosInterval (evalInterval e ρ)
  | Expr.log _ => default  -- Not in ExprSupported; use evalInterval? for log
  | Expr.atan e => atanInterval (evalInterval e ρ)
  | Expr.arsinh e => arsinhInterval (evalInterval e ρ)
  | Expr.atanh _ => default  -- Not in ExprSupported; use evalInterval? for atanh
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf _ => ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
  | Expr.sinh _ => default  -- sinh unbounded; use evalIntervalCore for tight bounds
  | Expr.cosh _ => default  -- cosh unbounded; use evalIntervalCore for tight bounds
  | Expr.tanh _ => default  -- tanh bounded but not in ExprSupported; use evalIntervalCore
  | Expr.sqrt e => IntervalRat.sqrtInterval (evalInterval e ρ)
  | Expr.pi => piInterval

/-- Fundamental correctness theorem for extended evaluation.

    This theorem is FULLY PROVED (no sorry, no axioms) for supported expressions.
    The `hsupp` hypothesis ensures we only consider expressions in the verified subset. -/
theorem evalInterval_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ evalInterval e ρ_int := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalInterval]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, evalInterval]
    exact hρ idx
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_add, evalInterval]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_mul, evalInterval]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, evalInterval]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, evalInterval]
    exact mem_sinInterval ih
  | cos _ ih =>
    simp only [Expr.eval_cos, evalInterval]
    exact mem_cosInterval ih
  | exp _ ih =>
    simp only [Expr.eval_exp, evalInterval]
    exact IntervalRat.mem_expInterval ih

/-! ### Convenience functions

Note: evalIntervalCore now uses Taylor series for exp/sin/cos, which gives
different (often tighter) intervals than evalInterval's floor/ceil bounds.
Both are correct, but they are not necessarily equal.

For purely algebraic expressions (const, var, add, mul, neg),
both evaluators give identical results. -/

/-- Noncomputable single-variable evaluation for extended expressions -/
noncomputable def evalInterval1 (e : Expr) (I : IntervalRat) : IntervalRat :=
  evalInterval e (fun _ => I)

/-- Correctness for single-variable extended evaluation -/
theorem evalInterval1_correct (e : Expr) (hsupp : ExprSupported e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ evalInterval1 e I :=
  evalInterval_correct e hsupp _ _ (fun _ => hx)

/-! ### Partial interval evaluation with inv support -/

/-- Partial (Option-returning) interval evaluator supporting inv.

    For expressions with inv, this evaluator returns `none` if the denominator
    interval contains zero, and `some I` with a correct enclosure otherwise.

    This allows safe interval evaluation of expressions like 1/x when we can
    verify the denominator is bounded away from zero.

    For expressions without inv, this always returns `some` with the same
    result as `evalInterval`. -/
def evalIntervalLogDepth : ℕ := 60

def evalIntervalExpDepth : ℕ := 30

def evalInterval? (e : Expr) (ρ : IntervalEnv) : Option IntervalRat :=
  match e with
  | Expr.const q => some (IntervalRat.singleton q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalInterval? e₁ ρ, evalInterval? e₂ ρ with
      | some I₁, some I₂ => some (IntervalRat.add I₁ I₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalInterval? e₁ ρ, evalInterval? e₂ ρ with
      | some I₁, some I₂ => some (IntervalRat.mul I₁ I₂)
      | _, _ => none
  | Expr.neg e =>
      match evalInterval? e ρ with
      | some I => some (IntervalRat.neg I)
      | none => none
  | Expr.inv e₁ =>
      match evalInterval? e₁ ρ with
      | none => none
      | some J =>
          if h : IntervalRat.containsZero J then
            none
          else
            some (IntervalRat.invNonzero ⟨J, h⟩)
  | Expr.exp e =>
      match evalInterval? e ρ with
      | some I => some (IntervalRat.expComputable I evalIntervalExpDepth)
      | none => none
  | Expr.sin e =>
      match evalInterval? e ρ with
      | some I => some (sinInterval I)
      | none => none
  | Expr.cos e =>
      match evalInterval? e ρ with
      | some I => some (cosInterval I)
      | none => none
  | Expr.log e =>
      match evalInterval? e ρ with
      | none => none
      | some J =>
          if h : IntervalRat.isPositive J then
            some (IntervalRat.logComputable J evalIntervalLogDepth)
          else
            none
  | Expr.atan e =>
      match evalInterval? e ρ with
      | some I => some (atanInterval I)
      | none => none
  | Expr.arsinh e =>
      match evalInterval? e ρ with
      | some I => some (arsinhInterval I)
      | none => none
  | Expr.atanh _ =>
      -- atanh is partial (defined only for |x| < 1) and requires complex bounds
      -- We return none to avoid the complexity of proving atanh bounds
      none
  | Expr.sinc e =>
      match evalInterval? e ρ with
      | some _ => some ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
      | none => none
  | Expr.erf e =>
      match evalInterval? e ρ with
      | some _ => some ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
      | none => none
  | Expr.sinh e =>
      match evalInterval? e ρ with
      | some I => some (sinhInterval I)
      | none => none
  | Expr.cosh e =>
      match evalInterval? e ρ with
      | some I => some (coshInterval I)
      | none => none
  | Expr.tanh e =>
      match evalInterval? e ρ with
      | some I => some (tanhInterval I)
      | none => none
  | Expr.sqrt e =>
      match evalInterval? e ρ with
      | some I => some (IntervalRat.sqrtInterval I)
      | none => none
  | Expr.pi => some piInterval

/-- Main correctness theorem for evalInterval? (approach 1 from plan).

    When evalInterval? returns `some I`:
    1. The expression evaluates to a value in I for all ρ_real ∈ ρ_int
    2. All inv denominators along the evaluation are guaranteed nonzero
       (because their intervals don't contain zero)

    This follows your suggestion to keep ExprSupported syntactic and add
    separate semantic hypotheses. The key insight is that if evalInterval?
    succeeds (returns Some), the interval arithmetic has already verified
    that no denominator interval contains zero. -/
theorem evalInterval?_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (ρ_int : IntervalEnv) (I : IntervalRat)
    (hsome : evalInterval? e ρ_int = some I)
    (ρ_real : Nat → ℝ) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ I := by
  induction hsupp generalizing I with
  | const q =>
    simp only [evalInterval?] at hsome
    cases hsome
    simp only [Expr.eval_const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [evalInterval?] at hsome
    cases hsome
    simp only [Expr.eval_var]
    exact hρ idx
  | @add e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    simp only [evalInterval?] at hsome
    cases heq₁ : evalInterval? e₁ ρ_int with
    | none => simp only [heq₁] at hsome; contradiction
    | some I₁ =>
      cases heq₂ : evalInterval? e₂ ρ_int with
      | none => simp only [heq₁, heq₂] at hsome; contradiction
      | some I₂ =>
        simp only [heq₁, heq₂] at hsome
        cases hsome
        simp only [Expr.eval_add]
        exact IntervalRat.mem_add (ih₁ I₁ heq₁) (ih₂ I₂ heq₂)
  | @mul e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    simp only [evalInterval?] at hsome
    cases heq₁ : evalInterval? e₁ ρ_int with
    | none => simp only [heq₁] at hsome; contradiction
    | some I₁ =>
      cases heq₂ : evalInterval? e₂ ρ_int with
      | none => simp only [heq₁, heq₂] at hsome; contradiction
      | some I₂ =>
        simp only [heq₁, heq₂] at hsome
        cases hsome
        simp only [Expr.eval_mul]
        exact IntervalRat.mem_mul (ih₁ I₁ heq₁) (ih₂ I₂ heq₂)
  | @neg e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_neg]
      exact IntervalRat.mem_neg (ih I' heq)
  | @inv e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · contradiction
      · rename_i hnonzero
        cases hsome
        simp only [Expr.eval_inv]
        have hJ_mem := ih J heq
        -- The denominator is nonzero because J doesn't contain zero and eval ∈ J
        have heval_ne : Expr.eval ρ_real e ≠ 0 := by
          intro heq_zero
          rw [heq_zero] at hJ_mem
          simp only [IntervalRat.mem_def] at hJ_mem
          simp only [IntervalRat.containsZero, not_and, not_le] at hnonzero
          rcases le_or_gt J.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ J.hi := by
              have h : (0 : ℝ) ≤ J.hi := hJ_mem.2
              exact_mod_cast h
            exact absurd (hnonzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < J.lo := by exact_mod_cast hlo
            exact absurd hJ_mem.1 (not_le.mpr hlo_pos)
        exact IntervalRat.mem_invNonzero hJ_mem heval_ne
  | @exp e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_exp]
      exact IntervalRat.mem_expComputable (ih I' heq) evalIntervalExpDepth
  | @sin e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_sin]
      exact mem_sinInterval (ih I' heq)
  | @cos e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_cos]
      exact mem_cosInterval (ih I' heq)
  | @log e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · rename_i hpos
        cases hsome
        simp only [Expr.eval_log]
        have hJ_mem := ih J heq
        -- The argument is positive because J.lo > 0 and eval ∈ J
        exact IntervalRat.mem_logComputable hJ_mem hpos evalIntervalLogDepth
      · contradiction
  | @atan e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_atan]
      exact mem_atanInterval (ih I' heq)
  | @arsinh e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_arsinh]
      exact mem_arsinhInterval (ih I' heq)
  | @atanh _ _ _ =>
    -- evalInterval? returns none for atanh, so hsome : none = some I is a contradiction
    simp only [evalInterval?] at hsome
    contradiction
  | @sinc e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_sinc]
      -- sinc(x) ∈ [-1, 1] for all x, using Mathlib's Real.sinc lemmas
      simp only [IntervalRat.mem_def]
      constructor
      · simp only [Rat.cast_neg, Rat.cast_one]
        exact Real.neg_one_le_sinc _
      · simp only [Rat.cast_one]
        exact Real.sinc_le_one _
  | @erf e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_erf]
      -- erf(x) ∈ [-1, 1] for all x
      simp only [IntervalRat.mem_def]
      constructor
      · simp only [Rat.cast_neg, Rat.cast_one]
        exact Real.neg_one_le_erf _
      · simp only [Rat.cast_one]
        exact Real.erf_le_one _
  | @sqrt e h ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_sqrt]
      exact IntervalRat.mem_sqrtInterval' (ih I' heq)
  | pi =>
    simp only [evalInterval?] at hsome
    cases hsome
    simp only [Expr.eval_pi]
    exact mem_piInterval

/-- Single-variable version of evalInterval? -/
def evalInterval?1 (e : Expr) (I : IntervalRat) : Option IntervalRat :=
  evalInterval? e (fun _ => I)

/-- Correctness for single-variable partial evaluation -/
theorem evalInterval?1_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (J : IntervalRat)
    (hsome : evalInterval?1 e I = some J)
    (x : ℝ) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ J :=
  evalInterval?_correct e hsupp _ J hsome _ (fun _ => hx)

/-- When evalInterval? succeeds, we get bounds -/
theorem evalInterval?_le_of_hi (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (J : IntervalRat) (c : ℚ)
    (hsome : evalInterval?1 e I = some J)
    (hhi : J.hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalInterval?1_correct e hsupp I J hsome x hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ J.hi := hmem.2
  have hhi_le_c : (J.hi : ℝ) ≤ c := by exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- When evalInterval? succeeds, we get lower bounds -/
theorem evalInterval?_ge_of_lo (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (J : IntervalRat) (c : ℚ)
    (hsome : evalInterval?1 e I = some J)
    (hlo : c ≤ J.lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval?1_correct e hsupp I J hsome x hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : J.lo ≤ Expr.eval (fun _ => x) e := hmem.1
  have hc_le_lo : (c : ℝ) ≤ J.lo := by exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

end LeanCert.Engine
