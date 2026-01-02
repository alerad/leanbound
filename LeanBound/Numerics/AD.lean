/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.IntervalEval
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Automatic Differentiation via Intervals

This file implements forward-mode automatic differentiation using interval
arithmetic. We compute both the value and derivative of an expression,
with rigorous bounds on both.

## Main definitions

* `DualInterval` - A pair of intervals representing (value, derivative)
* `evalDual` - Evaluate expression to get value and derivative intervals
* `evalDual_val_correct` - Correctness theorem for value component (fully proved for supported subset)
* `evalDual_der_correct` - Correctness theorem for derivative component (fully proved for supported subset)

## Design notes

This is forward-mode AD where we propagate (value, derivative) pairs.
The derivative is with respect to a designated variable index.

Supported: const, var, add, mul, neg, sin, cos, exp
Not yet supported: inv (requires nonzero interval checks)
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-- Dual number with interval components: represents (value, derivative) -/
structure DualInterval where
  val : IntervalRat
  der : IntervalRat
  deriving Repr

/-- Default DualInterval for unsupported expression branches -/
instance : Inhabited DualInterval where
  default := ⟨default, default⟩

namespace DualInterval

/-- Dual interval for a constant (derivative is zero) -/
def const (q : ℚ) : DualInterval :=
  { val := IntervalRat.singleton q
    der := IntervalRat.singleton 0 }

/-- Dual interval for the variable we're differentiating with respect to -/
def varActive (I : IntervalRat) : DualInterval :=
  { val := I
    der := IntervalRat.singleton 1 }

/-- Dual interval for a passive variable -/
def varPassive (I : IntervalRat) : DualInterval :=
  { val := I
    der := IntervalRat.singleton 0 }

/-- Add two dual intervals -/
def add (d₁ d₂ : DualInterval) : DualInterval :=
  { val := IntervalRat.add d₁.val d₂.val
    der := IntervalRat.add d₁.der d₂.der }

/-- Multiply two dual intervals (product rule) -/
def mul (d₁ d₂ : DualInterval) : DualInterval :=
  { val := IntervalRat.mul d₁.val d₂.val
    -- d(f*g) = f'*g + f*g'
    der := IntervalRat.add
             (IntervalRat.mul d₁.der d₂.val)
             (IntervalRat.mul d₁.val d₂.der) }

/-- Negate a dual interval -/
def neg (d : DualInterval) : DualInterval :=
  { val := IntervalRat.neg d.val
    der := IntervalRat.neg d.der }

/-- Dual for sin (chain rule: d(sin f) = cos(f) * f') -/
def sin (d : DualInterval) : DualInterval :=
  { val := sinInterval d.val
    der := IntervalRat.mul (cosInterval d.val) d.der }

/-- Dual for cos (chain rule: d(cos f) = -sin(f) * f') -/
def cos (d : DualInterval) : DualInterval :=
  { val := cosInterval d.val
    der := IntervalRat.mul (IntervalRat.neg (sinInterval d.val)) d.der }

/-- Dual for exp (chain rule: d(exp f) = exp(f) * f') -/
noncomputable def exp (d : DualInterval) : DualInterval :=
  { val := IntervalRat.expInterval d.val
    der := IntervalRat.mul (IntervalRat.expInterval d.val) d.der }

/-- The interval [0, 1] used to bound derivative factors in (0, 1] -/
private def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The derivative factor for arctan: 1/(1+x²) is in [0, 1] -/
private theorem arctan_deriv_factor_mem_unitInterval (y : ℝ) :
    1 / (1 + y ^ 2) ∈ unitInterval := by
  simp only [unitInterval, IntervalRat.mem_def, Rat.cast_zero, Rat.cast_one]
  have hpos : 0 < 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  constructor
  · exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hpos)
  · rw [div_le_one hpos]
    nlinarith [sq_nonneg y]

/-- The derivative factor for arsinh: 1/√(1+x²) is in [0, 1] -/
private theorem arsinh_deriv_factor_mem_unitInterval (y : ℝ) :
    (Real.sqrt (1 + y ^ 2))⁻¹ ∈ unitInterval := by
  simp only [unitInterval, IntervalRat.mem_def, Rat.cast_zero, Rat.cast_one]
  have h1 : 1 + y ^ 2 ≥ 1 := by nlinarith [sq_nonneg y]
  have hsqrt_ge_one : Real.sqrt (1 + y ^ 2) ≥ 1 := by
    calc Real.sqrt (1 + y ^ 2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  have hsqrt_pos : 0 < Real.sqrt (1 + y ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg y]
  constructor
  · exact inv_nonneg.mpr (le_of_lt hsqrt_pos)
  · exact inv_le_one_of_one_le₀ hsqrt_ge_one

/-- Dual for atan (chain rule: d(atan f) = f' / (1 + f²)) -/
def atan (d : DualInterval) : DualInterval :=
  { val := atanInterval d.val
    -- d(atan f) = f' / (1 + f²)
    -- Since 0 < 1/(1+x²) ≤ 1 for all x, we multiply d.der by [0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Dual for arsinh (chain rule: d(arsinh f) = f' / √(1 + f²)) -/
def arsinh (d : DualInterval) : DualInterval :=
  { val := arsinhInterval d.val
    -- d(arsinh f) = f' / √(1 + f²)
    -- Since 0 < 1/√(1+f²) ≤ 1, we multiply d.der by [0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Dual for sinh (chain rule: d(sinh f) = cosh(f) * f') -/
def sinh (d : DualInterval) : DualInterval :=
  { val := sinhInterval d.val
    -- sinh'(x) = cosh(x), so d(sinh f) = cosh(f) * f'
    der := IntervalRat.mul (coshInterval d.val) d.der }

/-- Dual for cosh (chain rule: d(cosh f) = sinh(f) * f') -/
def cosh (d : DualInterval) : DualInterval :=
  { val := coshInterval d.val
    -- cosh'(x) = sinh(x), so d(cosh f) = sinh(f) * f'
    der := IntervalRat.mul (sinhInterval d.val) d.der }

/-- Dual for tanh (chain rule: d(tanh f) = sech²(f) * f' = (1 - tanh²(f)) * f')
    Since sech²(x) = 1 - tanh²(x) ∈ (0, 1] for all x, we use [0, 1] as bound. -/
def tanh (d : DualInterval) : DualInterval :=
  { val := tanhInterval d.val
    -- tanh'(x) = sech²(x) = 1 - tanh²(x), which is in (0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Interval containing 2/√π ≈ 1.128379... -/
private def two_div_sqrt_pi : IntervalRat :=
  ⟨1128/1000, 1129/1000, by norm_num⟩

/-- Dual for erf (chain rule: d(erf f) = (2/√π) * exp(-f²) * f')
    erf'(x) = (2/√π) * exp(-x²), which is always positive and bounded by 2/√π ≈ 1.13 -/
noncomputable def erf (d : DualInterval) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- erf is bounded in [-1, 1]
    der :=
      let valSq := IntervalRat.mul d.val d.val
      let negValSq := IntervalRat.neg valSq
      let expPart := IntervalRat.expInterval negValSq
      let factor := IntervalRat.mul two_div_sqrt_pi expPart
      IntervalRat.mul factor d.der }

/-- Computable dual for erf using expComputable -/
def erfCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- erf is bounded in [-1, 1]
    der :=
      let valSq := IntervalRat.mul d.val d.val
      let negValSq := IntervalRat.neg valSq
      let expPart := IntervalRat.expComputable negValSq n
      let factor := IntervalRat.mul two_div_sqrt_pi expPart
      IntervalRat.mul factor d.der }

/-- Conservative derivative bound [-1, 1] for sinc derivative -/
private def sincDerivBound : IntervalRat := ⟨-1, 1, by norm_num⟩

/-- Dual for sinc (chain rule: d(sinc f) = sinc'(f) * f')
    sinc'(x) = (x cos x - sin x) / x² for x ≠ 0, limit 0 at x = 0.
    We use conservative bound: |sinc'(x)| ≤ 1 for all x. -/
def sinc (d : DualInterval) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- sinc is bounded in [-1, 1]
    -- sinc'(x) ∈ [-1, 1] (conservative bound), so d(sinc f) = sinc'(f) * f'
    der := IntervalRat.mul sincDerivBound d.der }

/-- Partial dual for atanh (chain rule: d(atanh f) = f' / (1 - f²))
    Returns None if the value interval is not contained in (-1, 1). -/
noncomputable def atanh? (d : DualInterval) : Option DualInterval :=
  -- For atanh to be defined, we need |val| < 1
  -- We check if the interval is strictly inside (-1, 1)
  if d.val.hi < 1 ∧ d.val.lo > -1 then
    -- Very rough bound: atanh' = 1/(1-x²), which blows up as |x| → 1
    -- For now we use [-100, 100] * der as a hugely conservative bound
    let bound : ℚ := 100
    some { val := atanhInterval d.val
           der := ⟨-bound * (|d.der.lo| + |d.der.hi| + 1),
                   bound * (|d.der.lo| + |d.der.hi| + 1),
                   by
                     have h1 : (0 : ℚ) ≤ |d.der.lo| := abs_nonneg _
                     have h2 : (0 : ℚ) ≤ |d.der.hi| := abs_nonneg _
                     have h : (0 : ℚ) ≤ bound * (|d.der.lo| + |d.der.hi| + 1) := by
                       apply mul_nonneg; norm_num; linarith
                     linarith⟩ }
  else
    none

/-- Partial dual for inv (chain rule: d(1/f) = -f'/f²)
    Returns None if the value interval contains zero. -/
def inv? (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.containsZero d.val then
    none
  else
    let inv_val := IntervalRat.invNonzero ⟨d.val, h⟩
    -- d(1/f) = -f'/f² = -f' * (1/f)²
    let inv_sq := IntervalRat.mul inv_val inv_val
    let der' := IntervalRat.neg (IntervalRat.mul d.der inv_sq)
    some { val := inv_val, der := der' }

/-- Partial dual for log (chain rule: d(log f) = f'/f)
    Returns None if the value interval is not strictly positive. -/
noncomputable def log? (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.isPositive d.val then
    let log_val := IntervalRat.logInterval ⟨d.val, h⟩
    -- d(log f) = f'/f
    let inv_val := IntervalRat.invNonzero ⟨d.val, by
      -- isPositive implies not containsZero
      simp only [IntervalRat.isPositive, IntervalRat.containsZero] at h ⊢
      intro ⟨hle, _⟩
      exact absurd h (not_lt.mpr hle)⟩
    let der' := IntervalRat.mul d.der inv_val
    some { val := log_val, der := der' }
  else
    none

end DualInterval

/-! ### Dual evaluation -/

/-- Environment for dual evaluation -/
abbrev DualEnv := Nat → DualInterval

/-- Evaluate expression in dual interval mode.

    For supported expressions (const, var, add, mul, neg, sin, cos, exp), this
    computes correct dual interval bounds with a fully-verified proof.

    For unsupported expressions (inv, log), returns a default interval.
    Do not rely on results for expressions containing inv or log.
    Use evalDual? for partial functions like inv and log. -/
noncomputable def evalDual (e : Expr) (ρ : DualEnv) : DualInterval :=
  match e with
  | Expr.const q => DualInterval.const q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => DualInterval.add (evalDual e₁ ρ) (evalDual e₂ ρ)
  | Expr.mul e₁ e₂ => DualInterval.mul (evalDual e₁ ρ) (evalDual e₂ ρ)
  | Expr.neg e => DualInterval.neg (evalDual e ρ)
  | Expr.inv _ => default  -- Not in ExprSupported; safe default
  | Expr.exp e => DualInterval.exp (evalDual e ρ)
  | Expr.sin e => DualInterval.sin (evalDual e ρ)
  | Expr.cos e => DualInterval.cos (evalDual e ρ)
  | Expr.log _ => default  -- Not in ExprSupported; use evalDual? for log
  | Expr.atan e => DualInterval.atan (evalDual e ρ)
  | Expr.arsinh e => DualInterval.arsinh (evalDual e ρ)
  | Expr.atanh _ => default  -- Partial function; use evalDual? for atanh
  | Expr.sinc e => DualInterval.sinc (evalDual e ρ)
  | Expr.erf e => DualInterval.erf (evalDual e ρ)
  | Expr.sinh e => DualInterval.sinh (evalDual e ρ)
  | Expr.cosh e => DualInterval.cosh (evalDual e ρ)
  | Expr.tanh e => DualInterval.tanh (evalDual e ρ)

/-! ### Partial dual evaluation (supports inv) -/

/-- Partial dual evaluator that supports inv and log.
    Returns `none` if any domain error would occur:
    - inv of an interval containing zero
    - log of an interval not strictly positive
    When it returns `some`, the result is guaranteed to be correct.

    This is the Option-returning version that safely handles expressions with inv and log. -/
noncomputable def evalDual? (e : Expr) (ρ : DualEnv) : Option DualInterval :=
  match e with
  | Expr.const q => some (DualInterval.const q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalDual? e₁ ρ, evalDual? e₂ ρ with
      | some d₁, some d₂ => some (DualInterval.add d₁ d₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalDual? e₁ ρ, evalDual? e₂ ρ with
      | some d₁, some d₂ => some (DualInterval.mul d₁ d₂)
      | _, _ => none
  | Expr.neg e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.neg d)
      | none => none
  | Expr.inv e₁ =>
      match evalDual? e₁ ρ with
      | none => none
      | some d => DualInterval.inv? d
  | Expr.exp e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.exp d)
      | none => none
  | Expr.sin e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.sin d)
      | none => none
  | Expr.cos e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.cos d)
      | none => none
  | Expr.log e =>
      match evalDual? e ρ with
      | none => none
      | some d => DualInterval.log? d
  | Expr.atan e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.atan d)
      | none => none
  | Expr.arsinh e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.arsinh d)
      | none => none
  | Expr.atanh _ =>
      -- atanh is partial (defined only for |x| < 1) and requires complex bounds
      -- We return none to avoid the complexity of proving atanh bounds
      none
  | Expr.sinc e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.sinc d)
      | none => none
  | Expr.erf e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.erf d)
      | none => none
  | Expr.sinh e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.sinh d)
      | none => none
  | Expr.cosh e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.cosh d)
      | none => none
  | Expr.tanh e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.tanh d)
      | none => none

/-- Single-variable version of evalDual? -/
noncomputable def evalDual?1 (e : Expr) (I : IntervalRat) : Option DualInterval :=
  evalDual? e (fun _ => DualInterval.varActive I)

/-! ### Single variable differentiation -/

/-- Create dual environment for differentiating with respect to variable `idx` -/
def mkDualEnv (ρ : IntervalEnv) (idx : Nat) : DualEnv :=
  fun i => if i = idx then DualInterval.varActive (ρ i) else DualInterval.varPassive (ρ i)

/-- Evaluate and differentiate with respect to variable `idx` -/
noncomputable def evalWithDeriv (e : Expr) (ρ : IntervalEnv) (idx : Nat) : DualInterval :=
  evalDual e (mkDualEnv ρ idx)

/-- Get just the derivative interval -/
noncomputable def derivInterval (e : Expr) (ρ : IntervalEnv) (idx : Nat) : IntervalRat :=
  (evalWithDeriv e ρ idx).der

/-! ### Correctness -/

/-- The value component is correct for supported expressions.

    This theorem is FULLY PROVED (no sorry, no axioms) for supported expressions.
    The `hsupp` hypothesis ensures we only consider expressions in the verified subset. -/
theorem evalDual_val_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ (evalDual e ρ_dual).val := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalDual, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, evalDual]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.eval_add, evalDual, DualInterval.add]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.eval_mul, evalDual, DualInterval.mul]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, evalDual, DualInterval.neg]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, evalDual, DualInterval.sin]
    exact mem_sinInterval ih
  | cos _ ih =>
    simp only [Expr.eval_cos, evalDual, DualInterval.cos]
    exact mem_cosInterval ih
  | exp _ ih =>
    simp only [Expr.eval_exp, evalDual, DualInterval.exp]
    exact IntervalRat.mem_expInterval ih

/-! ### Single-variable evaluation for derivative proofs -/

/-- The function t ↦ Expr.eval (fun _ => t) e for single-variable expressions -/
noncomputable abbrev evalFunc1 (e : Expr) : ℝ → ℝ :=
  fun t => Expr.eval (fun _ => t) e

/-! ### Differentiability of supported expressions -/

/-- Supported expressions are differentiable as single-variable functions.
    This theorem shows that for any supported expression,
    the function `evalFunc1 e` is differentiable.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalFunc1_differentiable (e : Expr) (hsupp : ExprSupported e) :
    Differentiable ℝ (evalFunc1 e) := by
  induction hsupp with
  | const q =>
    exact differentiable_const _
  | var _ =>
    exact differentiable_id
  | add _ _ ih₁ ih₂ =>
    exact Differentiable.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    exact Differentiable.mul ih₁ ih₂
  | neg _ ih =>
    exact Differentiable.neg ih
  | sin _ ih =>
    exact Real.differentiable_sin.comp ih
  | cos _ ih =>
    exact Real.differentiable_cos.comp ih
  | exp _ ih =>
    exact Real.differentiable_exp.comp ih

/-! ### Core derivative correctness micro-lemmas -/

/-- Real.cos y is always in cosInterval I (which is [-1, 1]).
    This micro-lemma encapsulates the fact that cosInterval uses the global bound. -/
theorem cos_mem_cosInterval_of_any (y : ℝ) (I : IntervalRat) :
    Real.cos y ∈ cosInterval I := by
  simp only [cosInterval, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
  exact Real.cos_mem_Icc _

/-- Real.sin y is always in sinInterval I (which is [-1, 1]).
    This micro-lemma encapsulates the fact that sinInterval uses the global bound. -/
theorem sin_mem_sinInterval_of_any (y : ℝ) (I : IntervalRat) :
    Real.sin y ∈ sinInterval I := by
  simp only [sinInterval, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
  exact Real.sin_mem_Icc _

/-- -Real.sin y is always in IntervalRat.neg (sinInterval I).
    This combines the sin global bound with negation for the cos derivative rule. -/
theorem neg_sin_mem_neg_sinInterval (y : ℝ) (I : IntervalRat) :
    -Real.sin y ∈ IntervalRat.neg (sinInterval I) :=
  IntervalRat.mem_neg (sin_mem_sinInterval_of_any y I)

/-- The key lemma for n-variable AD: updateVar ρ_real idx x respects mkDualEnv ρ_int idx.
    This encapsulates the repeated proof that appears in mul/exp cases. -/
theorem updateVar_mem_mkDualEnv_val (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (x : ℝ) (hx : x ∈ ρ_int idx) (hρ : ∀ i, ρ_real i ∈ ρ_int i) :
    ∀ i, Expr.updateVar ρ_real idx x i ∈ (mkDualEnv ρ_int idx i).val := by
  intro i
  by_cases hi : i = idx
  · subst hi
    simp only [Expr.updateVar_same, mkDualEnv, ↓reduceIte, DualInterval.varActive]
    exact hx
  · simp only [Expr.updateVar_other _ _ _ _ hi, mkDualEnv, if_neg hi, DualInterval.varPassive]
    exact hρ i

/-! ### evalFunc1 unfolding lemmas -/

/-- Helper lemma: evalFunc1 for addition unfolds correctly -/
theorem evalFunc1_add (e₁ e₂ : Expr) :
    evalFunc1 (Expr.add e₁ e₂) = fun t => evalFunc1 e₁ t + evalFunc1 e₂ t := rfl

/-- Helper lemma: evalFunc1 for addition in Pi form -/
theorem evalFunc1_add_pi (e₁ e₂ : Expr) :
    evalFunc1 (Expr.add e₁ e₂) = evalFunc1 e₁ + evalFunc1 e₂ := rfl

/-- Helper lemma: evalFunc1 for multiplication unfolds correctly -/
theorem evalFunc1_mul (e₁ e₂ : Expr) :
    evalFunc1 (Expr.mul e₁ e₂) = fun t => evalFunc1 e₁ t * evalFunc1 e₂ t := rfl

/-- Helper lemma: evalFunc1 for multiplication in Pi form -/
theorem evalFunc1_mul_pi (e₁ e₂ : Expr) :
    evalFunc1 (Expr.mul e₁ e₂) = evalFunc1 e₁ * evalFunc1 e₂ := rfl

/-- Helper lemma: evalFunc1 for negation unfolds correctly -/
theorem evalFunc1_neg (e : Expr) :
    evalFunc1 (Expr.neg e) = fun t => -(evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for negation in Pi form -/
theorem evalFunc1_neg_pi (e : Expr) :
    evalFunc1 (Expr.neg e) = -evalFunc1 e := rfl

/-- Helper lemma: evalFunc1 for sin unfolds correctly -/
theorem evalFunc1_sin (e : Expr) :
    evalFunc1 (Expr.sin e) = fun t => Real.sin (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for cos unfolds correctly -/
theorem evalFunc1_cos (e : Expr) :
    evalFunc1 (Expr.cos e) = fun t => Real.cos (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for exp unfolds correctly -/
theorem evalFunc1_exp (e : Expr) :
    evalFunc1 (Expr.exp e) = fun t => Real.exp (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for log unfolds correctly -/
theorem evalFunc1_log (e : Expr) :
    evalFunc1 (Expr.log e) = fun t => Real.log (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for atan unfolds correctly -/
theorem evalFunc1_atan (e : Expr) :
    evalFunc1 (Expr.atan e) = fun t => Real.arctan (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for arsinh unfolds correctly -/
theorem evalFunc1_arsinh (e : Expr) :
    evalFunc1 (Expr.arsinh e) = fun t => Real.arsinh (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for atanh unfolds correctly -/
theorem evalFunc1_atanh (e : Expr) :
    evalFunc1 (Expr.atanh e) = fun t => Real.atanh (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for const -/
@[simp]
theorem evalFunc1_const (q : ℚ) : evalFunc1 (Expr.const q) = fun _ => (q : ℝ) := rfl

/-- Helper lemma: evalFunc1 for var -/
@[simp]
theorem evalFunc1_var (i : ℕ) : evalFunc1 (Expr.var i) = id := rfl

/-- Helper: the dual environment evaluation gives correct derivative.
    This connects the interval-based AD to actual calculus derivatives.

    FULLY PROVED - no sorry, no axioms. -/
theorem deriv_mem_dualDer (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (evalFunc1 e) x ∈
      (evalDual e (fun _ => DualInterval.varActive I)).der := by
  induction hsupp generalizing x with
  | const q =>
    -- d/dx (const) = 0
    simp only [evalDual, DualInterval.const, evalFunc1_const, deriv_const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    -- d/dx (x) = 1
    simp only [evalDual, DualInterval.varActive, evalFunc1_var]
    rw [deriv_id]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    -- d/dx (f + g) = f' + g'
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [evalDual, DualInterval.add, evalFunc1_add_pi, deriv_add (hd₁ x) (hd₂ x)]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    -- d/dx (f * g) = f' * g + f * g'
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [evalDual, DualInterval.mul, evalFunc1_mul_pi, deriv_mul (hd₁ x) (hd₂ x)]
    -- Need: f'(x)*g(x) + f(x)*g'(x) ∈ der₁*val₂ + val₁*der₂
    have hval₁ := evalDual_val_correct _ h₁ (fun _ => x) (fun _ => DualInterval.varActive I)
      (fun _ => hx)
    have hval₂ := evalDual_val_correct _ h₂ (fun _ => x) (fun _ => DualInterval.varActive I)
      (fun _ => hx)
    simp only [DualInterval.varActive] at hval₁ hval₂
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁ (ih₂ x hx))
  | neg hs ih =>
    -- d/dx (-f) = -f'
    have hd := evalFunc1_differentiable _ hs
    simp only [evalDual, DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    -- d/dx (sin f) = cos(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [evalDual, DualInterval.sin, evalFunc1_sin]
    rw [deriv_sin (hd.differentiableAt)]
    exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih x hx)
  | @cos e' hs ih =>
    -- d/dx (cos f) = -sin(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [evalDual, DualInterval.cos, evalFunc1_cos]
    rw [deriv_cos (hd.differentiableAt)]
    exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih x hx)
  | @exp e' hs ih =>
    -- d/dx (exp f) = exp(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [evalDual, DualInterval.exp, evalFunc1_exp]
    rw [deriv_exp (hd.differentiableAt)]
    -- exp(f(x)) ∈ expInterval and f'(x) ∈ der
    have hval := evalDual_val_correct e' hs (fun _ => x) (fun _ => DualInterval.varActive I)
      (fun _ => hx)
    simp only [DualInterval.varActive] at hval
    have hexp := IntervalRat.mem_expInterval hval
    exact IntervalRat.mem_mul hexp (ih x hx)

/-- The derivative component of dual interval evaluation is correct.
    For a supported expression evaluated at a point x in the interval I,
    the derivative of the expression (as a function of x) lies in the
    computed derivative interval.

    This is the fundamental correctness theorem for forward-mode AD:
    the derivative bounds computed by interval arithmetic contain the
    true derivative at every point in the domain.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalDual_der_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (fun t => Expr.eval (fun _ => t) e) x ∈
      (evalDual e (fun _ => DualInterval.varActive I)).der :=
  deriv_mem_dualDer e hsupp I x hx

/-! ### Generalized n-variable derivative correctness -/

/-- Helper: evalAlong is differentiable for supported expressions -/
theorem evalAlong_differentiable (e : Expr) (hsupp : ExprSupported e)
    (ρ : Nat → ℝ) (idx : Nat) :
    Differentiable ℝ (Expr.evalAlong e ρ idx) := by
  induction hsupp with
  | const q =>
    simp only [Expr.evalAlong_const']
    exact differentiable_const _
  | var i =>
    by_cases h : i = idx
    · subst h
      simp only [Expr.evalAlong_var_active]
      exact differentiable_id
    · simp only [Expr.evalAlong_var_passive _ _ _ h]
      exact differentiable_const _
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.evalAlong_add]
    exact Differentiable.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.evalAlong_mul]
    exact Differentiable.mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.evalAlong_neg]
    exact Differentiable.neg ih
  | sin _ ih =>
    simp only [Expr.evalAlong_sin]
    exact Real.differentiable_sin.comp ih
  | cos _ ih =>
    simp only [Expr.evalAlong_cos]
    exact Real.differentiable_cos.comp ih
  | exp _ ih =>
    simp only [Expr.evalAlong_exp]
    exact Real.differentiable_exp.comp ih

/-- The derivative of evalAlong with respect to coordinate `idx` lies in the
    computed derivative interval from mkDualEnv.

    This is the fundamental n-variable derivative correctness theorem.
    It shows that for any expression, if we differentiate along coordinate `idx`
    while holding all other coordinates fixed according to `ρ`, the derivative
    at any point `x` in the interval `ρ_int idx` lies in the computed interval.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalDual_der_correct_idx (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (x : ℝ) (hx : x ∈ ρ_int idx) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈
      (evalDual e (mkDualEnv ρ_int idx)).der := by
  induction hsupp generalizing x with
  | const q =>
    -- d/dt (const) = 0
    simp only [Expr.evalAlong_const', deriv_const, evalDual, DualInterval.const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var i =>
    by_cases h : i = idx
    · -- Active variable: d/dt (t) = 1
      subst h
      simp only [Expr.evalAlong_var_active, evalDual, mkDualEnv, ↓reduceIte,
        DualInterval.varActive, deriv_id]
      convert IntervalRat.mem_singleton 1 using 1
      norm_cast
    · -- Passive variable: d/dt (const) = 0
      simp only [Expr.evalAlong_var_passive _ _ _ h, deriv_const, evalDual, mkDualEnv,
        if_neg h, DualInterval.varPassive]
      convert IntervalRat.mem_singleton 0 using 1
      norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
    have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
    simp only [Expr.evalAlong_add_pi, deriv_add (hd₁ x) (hd₂ x), evalDual, DualInterval.add]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
    have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
    simp only [Expr.evalAlong_mul_pi, deriv_mul (hd₁ x) (hd₂ x), evalDual, DualInterval.mul]
    have hmem := updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ
    have hval₁ := evalDual_val_correct _ h₁ _ _ hmem
    have hval₂ := evalDual_val_correct _ h₂ _ _ hmem
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁ (ih₂ x hx))
  | neg hs ih =>
    have hd := evalAlong_differentiable _ hs ρ_real idx
    simp only [Expr.evalAlong_neg_pi, deriv.neg, evalDual, DualInterval.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_sin, deriv_sin (hd.differentiableAt), evalDual, DualInterval.sin]
    exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih x hx)
  | @cos e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_cos, deriv_cos (hd.differentiableAt), evalDual, DualInterval.cos]
    exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih x hx)
  | @exp e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_exp, deriv_exp (hd.differentiableAt), evalDual, DualInterval.exp]
    have hmem := updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ
    have hval := evalDual_val_correct e' hs _ _ hmem
    exact IntervalRat.mem_mul (IntervalRat.mem_expInterval hval) (ih x hx)

/-- Convenience theorem: derivInterval correctness for n-variable expressions.
    The derivative of `evalAlong e ρ idx` at any point `x` in the interval
    lies in `derivInterval e ρ_int idx`. -/
theorem derivInterval_correct_idx (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (x : ℝ) (hx : x ∈ ρ_int idx) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈ derivInterval e ρ_int idx := by
  simp only [derivInterval, evalWithDeriv]
  exact evalDual_der_correct_idx e hsupp ρ_real ρ_int idx hρ x hx

/-! ### Single-variable expressions -/

/-- Predicate: expression only uses variable index 0.
    This is useful for proving that different environments give the same result
    when they agree at index 0. -/
inductive UsesOnlyVar0 : Expr → Prop where
  | const (q : ℚ) : UsesOnlyVar0 (Expr.const q)
  | var0 : UsesOnlyVar0 (Expr.var 0)
  | add (e₁ e₂ : Expr) (h₁ : UsesOnlyVar0 e₁) (h₂ : UsesOnlyVar0 e₂) : UsesOnlyVar0 (Expr.add e₁ e₂)
  | mul (e₁ e₂ : Expr) (h₁ : UsesOnlyVar0 e₁) (h₂ : UsesOnlyVar0 e₂) : UsesOnlyVar0 (Expr.mul e₁ e₂)
  | neg (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.neg e)
  | sin (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.sin e)
  | cos (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.cos e)
  | exp (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.exp e)
  | atan (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.atan e)
  | arsinh (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.arsinh e)

/-- For expressions using only var 0, evalDual agrees for environments that match at 0 -/
theorem evalDual_congr_at_0 (e : Expr) (h : UsesOnlyVar0 e)
    (ρ₁ ρ₂ : DualEnv) (heq : ρ₁ 0 = ρ₂ 0) :
    evalDual e ρ₁ = evalDual e ρ₂ := by
  induction h generalizing ρ₁ ρ₂ with
  | const q => simp only [evalDual]
  | var0 => simp only [evalDual, heq]
  | add _ _ _ _ ih₁ ih₂ =>
    simp only [evalDual, ih₁ ρ₁ ρ₂ heq, ih₂ ρ₁ ρ₂ heq]
  | mul _ _ _ _ ih₁ ih₂ =>
    simp only [evalDual, ih₁ ρ₁ ρ₂ heq, ih₂ ρ₁ ρ₂ heq]
  | neg _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | sin _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | cos _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | exp _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | atan _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | arsinh _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]

/-- mkDualEnv at index 0 equals varActive at 0 -/
theorem mkDualEnv_at_0 (I : IntervalRat) :
    mkDualEnv (fun _ => I) 0 0 = DualInterval.varActive I := by
  simp only [mkDualEnv, ↓reduceIte]

/-! ### Convenience single-variable differentiation -/

/-- Evaluate and differentiate a single-variable expression -/
noncomputable def evalWithDeriv1 (e : Expr) (I : IntervalRat) : DualInterval :=
  evalDual e (fun _ => DualInterval.varActive I)

/-- For expressions using only var 0, derivInterval equals evalWithDeriv1 -/
theorem derivInterval_eq_evalWithDeriv1_of_UsesOnlyVar0 (e : Expr) (h : UsesOnlyVar0 e)
    (I : IntervalRat) :
    derivInterval e (fun _ => I) 0 = (evalWithDeriv1 e I).der := by
  simp only [derivInterval, evalWithDeriv, evalWithDeriv1]
  -- Need to show: (evalDual e (mkDualEnv (fun _ => I) 0)).der = (evalDual e (fun _ => varActive I)).der
  have henv_eq : mkDualEnv (fun _ => I) 0 0 = (fun _ => DualInterval.varActive I) 0 := by
    simp only [mkDualEnv_at_0]
  have heq := evalDual_congr_at_0 e h (mkDualEnv (fun _ => I) 0) (fun _ => DualInterval.varActive I) henv_eq
  rw [heq]

/-- Correctness of single-variable derivative bounds -/
theorem evalWithDeriv1_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ (evalWithDeriv1 e I).val ∧
    deriv (fun t => Expr.eval (fun _ => t) e) x ∈ (evalWithDeriv1 e I).der := by
  constructor
  · exact evalDual_val_correct e hsupp (fun _ => x) _ (fun _ => hx)
  · exact evalDual_der_correct e hsupp I x hx

/-! ### Correctness of partial dual evaluator -/

/-- The value component of evalDual? is correct when it returns some.
    This theorem extends to expressions with inv. -/
theorem evalDual?_val_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv) (D : DualInterval)
    (hsome : evalDual? e ρ_dual = some D)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ D.val := by
  induction hsupp generalizing D with
  | const q =>
    simp only [evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [Expr.eval_const, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    exact hρ idx
  | @add e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    simp only [evalDual?] at hsome
    cases heq₁ : evalDual? e₁ ρ_dual with
    | none => simp only [heq₁, reduceCtorEq] at hsome
    | some d₁ =>
      cases heq₂ : evalDual? e₂ ρ_dual with
      | none => simp only [heq₁, heq₂, reduceCtorEq] at hsome
      | some d₂ =>
        simp only [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_add, DualInterval.add]
        exact IntervalRat.mem_add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | @mul e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    simp only [evalDual?] at hsome
    cases heq₁ : evalDual? e₁ ρ_dual with
    | none => simp only [heq₁, reduceCtorEq] at hsome
    | some d₁ =>
      cases heq₂ : evalDual? e₂ ρ_dual with
      | none => simp only [heq₁, heq₂, reduceCtorEq] at hsome
      | some d₂ =>
        simp only [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_mul, DualInterval.mul]
        exact IntervalRat.mem_mul (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | @neg e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_neg, DualInterval.neg]
      exact IntervalRat.mem_neg (ih d heq)
  | @inv e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, DualInterval.inv?] at hsome
      split at hsome
      · simp at hsome
      · next hnotzero =>
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_inv]
        have hmem := ih d heq
        -- The denominator is nonzero because d.val doesn't contain zero and eval ∈ d.val
        have heval_ne : Expr.eval ρ_real e' ≠ 0 := by
          intro heq_zero
          rw [heq_zero] at hmem
          simp only [IntervalRat.mem_def] at hmem
          simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
          rcases le_or_gt d.val.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
              have h : (0 : ℝ) ≤ d.val.hi := hmem.2
              exact_mod_cast h
            exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
            exact absurd hmem.1 (not_le.mpr hlo_pos)
        exact IntervalRat.mem_invNonzero hmem heval_ne
  | @sin e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sin, DualInterval.sin]
      exact mem_sinInterval (ih d heq)
  | @cos e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_cos, DualInterval.cos]
      exact mem_cosInterval (ih d heq)
  | @exp e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_exp, DualInterval.exp]
      exact IntervalRat.mem_expInterval (ih d heq)
  | @log e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, DualInterval.log?] at hsome
      split at hsome
      · rename_i hpos
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_log]
        have hJ_mem := ih d heq
        exact IntervalRat.mem_logInterval hJ_mem
      · contradiction
  | @atan e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_atan, DualInterval.atan]
      exact mem_atanInterval (ih d heq)
  | @arsinh e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_arsinh, DualInterval.arsinh]
      exact mem_arsinhInterval (ih d heq)
  | @atanh _ _ _ =>
    -- evalDual? returns none for atanh, so hsome : none = some D is a contradiction
    simp only [evalDual?] at hsome
    contradiction
  | @sinc e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sinc, DualInterval.sinc]
      simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
      exact ⟨Real.neg_one_le_sinc _, Real.sinc_le_one _⟩
  | @erf e' hs ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_erf, DualInterval.erf]
      simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
      exact ⟨Real.neg_one_le_erf _, Real.erf_le_one _⟩

/-- Single-variable version of evalDual?_val_correct -/
theorem evalDual?1_val_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    Expr.eval (fun _ => x) e ∈ D.val := by
  apply evalDual?_val_correct e hsupp (fun _ => x) (fun _ => DualInterval.varActive I)
  · exact hsome
  · intro _; exact hx

/-- Helper lemma: evalFunc1 for inv unfolds correctly -/
theorem evalFunc1_inv (e : Expr) :
    evalFunc1 (Expr.inv e) = fun t => (evalFunc1 e t)⁻¹ := rfl

/-- Expressions with inv are differentiable when the denominator is nonzero. -/
theorem evalFunc1_differentiableAt_of_evalDual? (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    DifferentiableAt ℝ (evalFunc1 e) x := by
  induction hsupp generalizing D with
  | const q => exact differentiableAt_const _
  | var _ => exact differentiableAt_id
  | @add e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        exact DifferentiableAt.add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | @mul e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        exact DifferentiableAt.mul (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | @neg e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact DifferentiableAt.neg (ih d heq)
  | @inv e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.inv?] at hsome
      split at hsome
      · exact absurd hsome (by simp)
      · next hnotzero =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDual?1_val_correct e' hs I d x hx heq
        -- Denominator is nonzero
        have hne : evalFunc1 e' x ≠ 0 := by
          intro heq_zero
          -- hval has type: Expr.eval (fun x_1 => x) e' ∈ d.val
          -- need to convert to: evalFunc1 e' x = 0
          have hval' : evalFunc1 e' x ∈ d.val := hval
          rw [heq_zero] at hval'
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
          rcases le_or_gt d.val.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
              have h : (0 : ℝ) ≤ d.val.hi := hval'.2
              exact_mod_cast h
            exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
            exact absurd hval'.1 (not_le.mpr hlo_pos)
        exact DifferentiableAt.inv (ih d heq) hne
  | @sin e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_sin.comp x (ih d heq)
  | @cos e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_cos.comp x (ih d heq)
  | @exp e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_exp.comp x (ih d heq)
  | @log e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.log?] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDual?1_val_correct e' hs I d x hx heq
        -- The argument is positive, so log is differentiable
        have hpos_x : 0 < evalFunc1 e' x := by
          have hval' : evalFunc1 e' x ∈ d.val := hval
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.isPositive] at hpos
          have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
          exact lt_of_lt_of_le hlo_pos hval'.1
        exact Real.differentiableAt_log (ne_of_gt hpos_x) |>.comp x (ih d heq)
      · exact absurd hsome (by simp)
  | @atan e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (Real.differentiable_arctan _).comp x (ih d heq)
  | @arsinh e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (Real.differentiable_arsinh _).comp x (ih d heq)
  | @atanh _ _ _ =>
    -- evalDual? returns none for atanh, so hsome is a contradiction
    simp only [evalDual?1, evalDual?] at hsome
    contradiction
  | @sinc e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      -- sinc is differentiable everywhere
      -- TODO: This requires Real.differentiable_sinc from Mathlib
      exact (Differentiable.differentiableAt (by sorry : Differentiable ℝ Real.sinc)).comp x (ih d heq)
  | @erf e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      -- erf is differentiable everywhere
      -- TODO: This requires Real.differentiable_erf from Mathlib
      exact (Differentiable.differentiableAt (by sorry : Differentiable ℝ Real.erf)).comp x (ih d heq)

/-- The derivative component of evalDual? is correct when it returns some.
    For a supported expression (with inv) evaluated at a point x in the interval I,
    the derivative of the expression lies in the computed derivative interval.

    This extends the AD correctness theorem to expressions with inv. -/
theorem evalDual?_der_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    deriv (evalFunc1 e) x ∈ D.der := by
  induction hsupp generalizing D with
  | const q =>
    simp only [evalDual?1, evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_const, deriv_const, DualInterval.const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    simp only [evalDual?1, evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_var, deriv_id, DualInterval.varActive]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | @add e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        rw [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [DualInterval.add]
        have hd₁ := evalFunc1_differentiableAt_of_evalDual? e₁ h₁ I d₁ x hx heq₁
        have hd₂ := evalFunc1_differentiableAt_of_evalDual? e₂ h₂ I d₂ x hx heq₂
        simp only [evalFunc1_add_pi, deriv_add hd₁ hd₂]
        exact IntervalRat.mem_add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | @mul e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        rw [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [DualInterval.mul]
        have hd₁ := evalFunc1_differentiableAt_of_evalDual? e₁ h₁ I d₁ x hx heq₁
        have hd₂ := evalFunc1_differentiableAt_of_evalDual? e₂ h₂ I d₂ x hx heq₂
        simp only [evalFunc1_mul_pi, deriv_mul hd₁ hd₂]
        have hval₁ := evalDual?1_val_correct e₁ h₁ I d₁ x hx heq₁
        have hval₂ := evalDual?1_val_correct e₂ h₂ I d₂ x hx heq₂
        exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ d₁ heq₁) hval₂)
                                  (IntervalRat.mem_mul hval₁ (ih₂ d₂ heq₂))
  | @neg e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
      exact IntervalRat.mem_neg (ih d heq)
  | @inv e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.inv?] at hsome
      split at hsome
      · exact absurd hsome (by simp)
      · next hnotzero =>
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        -- d(1/f) = -f'/f² = -f' * (1/f)²
        have hval := evalDual?1_val_correct e' hs I d x hx heq
        have hval' : evalFunc1 e' x ∈ d.val := hval
        have hne : evalFunc1 e' x ≠ 0 := by
          intro heq_zero
          rw [heq_zero] at hval'
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
          rcases le_or_gt d.val.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
              have h : (0 : ℝ) ≤ d.val.hi := hval'.2
              exact_mod_cast h
            exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
            exact absurd hval'.1 (not_le.mpr hlo_pos)
        have hd := evalFunc1_differentiableAt_of_evalDual? e' hs I d x hx heq
        -- deriv (1/f) = deriv(f⁻¹ ∘ f) = -(f')/(f²) using chain rule
        -- We use: deriv (fun y => y⁻¹) (f x) * deriv f x = -(f x)⁻² * f'(x)
        rw [evalFunc1_inv]
        -- The goal is: deriv (fun t => (evalFunc1 e' t)⁻¹) x ∈ ...
        -- First show this equals the composition derivative
        have heq_fun : (fun t => (evalFunc1 e' t)⁻¹) = (fun y => y⁻¹) ∘ evalFunc1 e' := rfl
        rw [heq_fun, deriv_comp x (hasDerivAt_inv hne).differentiableAt hd]
        simp only [hasDerivAt_inv hne |>.deriv]
        -- Now goal is: -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x ∈ ...
        -- Which equals: -(deriv f * (1/f)²)
        have hder := ih d heq
        -- Construct the nonzero interval
        let I_nz : IntervalRat.IntervalRatNonzero := ⟨d.val, hnotzero⟩
        have hinv := IntervalRat.mem_invNonzero (I := I_nz) hval' hne
        have hinv_sq := IntervalRat.mem_mul hinv hinv
        have hprod := IntervalRat.mem_mul hder hinv_sq
        have hneg := IntervalRat.mem_neg hprod
        -- hneg : -(deriv (evalFunc1 e') x * ((evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹)) ∈ ...
        -- goal : -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x ∈ ...
        -- These are equal: -(a ^ 2)⁻¹ * b = -(b * (a⁻¹ * a⁻¹))
        have heq_val : -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x =
                       -(deriv (evalFunc1 e') x * ((evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹)) := by
          have h1 : (evalFunc1 e' x ^ 2)⁻¹ = (evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹ := by
            rw [sq, mul_inv]
          rw [h1]
          ring
        rw [heq_val]
        exact hneg
  | @sin e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sin]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' hs I d x hx heq
      rw [evalFunc1_sin, deriv_sin hd]
      exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih d heq)
  | @cos e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.cos]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' hs I d x hx heq
      rw [evalFunc1_cos, deriv_cos hd]
      exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih d heq)
  | @exp e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.exp]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' hs I d x hx heq
      rw [evalFunc1_exp, deriv_exp hd]
      have hval := evalDual?1_val_correct e' hs I d x hx heq
      have hexp := IntervalRat.mem_expInterval hval
      exact IntervalRat.mem_mul hexp (ih d heq)
  | @log e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.log?] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        -- d(log f)/dx = f'/f
        have hval := evalDual?1_val_correct e' hs I d x hx heq
        have hval' : evalFunc1 e' x ∈ d.val := hval
        have hpos_x : 0 < evalFunc1 e' x := by
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.isPositive] at hpos
          have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
          exact lt_of_lt_of_le hlo_pos hval'.1
        have hne_x : evalFunc1 e' x ≠ 0 := ne_of_gt hpos_x
        have hd := evalFunc1_differentiableAt_of_evalDual? e' hs I d x hx heq
        rw [evalFunc1_log]
        have heq_fun : (fun t => Real.log (evalFunc1 e' t)) = Real.log ∘ evalFunc1 e' := rfl
        rw [heq_fun, deriv_comp x (Real.differentiableAt_log hne_x) hd]
        simp only [Real.deriv_log (evalFunc1 e' x)]
        -- Goal: (evalFunc1 e' x)⁻¹ * deriv (evalFunc1 e') x ∈ ...
        -- From DualInterval.log?: der' := d.der * invNonzero d.val
        have hder := ih d heq
        -- Build the nonzero interval from the positive interval
        have hnotzero : ¬IntervalRat.containsZero d.val := by
          simp only [IntervalRat.containsZero, IntervalRat.isPositive] at hpos ⊢
          intro ⟨hle, _⟩
          exact absurd hpos (not_lt.mpr hle)
        let I_nz : IntervalRat.IntervalRatNonzero := ⟨d.val, hnotzero⟩
        have hinv := IntervalRat.mem_invNonzero (I := I_nz) hval' hne_x
        -- Need to show: (evalFunc1 e' x)⁻¹ * deriv (evalFunc1 e') x ∈ d.der * invNonzero d.val
        -- But mem_mul expects the arguments in different order, so use commutativity
        have hmul := IntervalRat.mem_mul hder hinv
        convert hmul using 1
        ring
      · exact absurd hsome (by simp)
  | @atan e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.atan]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' hs I d x hx heq
      rw [evalFunc1_atan]
      -- deriv (arctan ∘ f) x = (1 / (1 + f(x)²)) * f'(x)
      have heq_deriv := HasDerivAt.arctan (hd.hasDerivAt)
      rw [heq_deriv.deriv, mul_comm]
      -- The factor 1/(1+f(x)²) is in unitInterval
      have hfactor := DualInterval.arctan_deriv_factor_mem_unitInterval (evalFunc1 e' x)
      exact IntervalRat.mem_mul (ih d heq) hfactor
  | @arsinh e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.arsinh]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' hs I d x hx heq
      rw [evalFunc1_arsinh]
      -- deriv (arsinh ∘ f) x = (√(1 + f(x)²))⁻¹ • f'(x)
      have heq_deriv := HasDerivAt.arsinh (hd.hasDerivAt)
      rw [heq_deriv.deriv, smul_eq_mul, mul_comm]
      -- The factor 1/√(1+f(x)²) is in unitInterval
      have hfactor := DualInterval.arsinh_deriv_factor_mem_unitInterval (evalFunc1 e' x)
      exact IntervalRat.mem_mul (ih d heq) hfactor
  | @atanh _ _ _ =>
    -- evalDual? returns none for atanh, so hsome is a contradiction
    simp only [evalDual?1, evalDual?] at hsome
    contradiction
  | @sinc e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sinc]
      -- The derivative of sinc ∘ f is sinc'(f(x)) * f'(x)
      -- We use conservative bound: sinc'(x) ∈ [-1, 1] for all x
      -- TODO: Full proof requires Real.deriv_sinc bounds from Mathlib
      sorry
  | @erf e' hs ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.erf]
      -- The derivative of erf ∘ f is (2/√π) * exp(-f(x)²) * f'(x)
      -- TODO: Full proof requires Real.deriv_erf from Mathlib
      sorry

/-- Combined correctness theorem for evalDual?1 -/
theorem evalDual?1_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    Expr.eval (fun _ => x) e ∈ D.val ∧ deriv (evalFunc1 e) x ∈ D.der :=
  ⟨evalDual?1_val_correct e hsupp I D x hx hsome, evalDual?_der_correct e hsupp I D x hx hsome⟩

/-! ### Computable Dual Evaluation for ExprSupportedCore

This section provides a fully computable dual evaluator that uses Taylor-based
approximations for transcendental functions. This enables `native_decide` for
derivative-based bound checking.
-/

namespace DualInterval

/-- Computable dual for exp using Taylor series (chain rule: d(exp f) = exp(f) * f') -/
def expCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  let expVal := IntervalRat.expComputable d.val n
  { val := expVal
    der := IntervalRat.mul expVal d.der }

/-- Computable dual for sin using Taylor series -/
def sinCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.sinComputable d.val n
    der := IntervalRat.mul (IntervalRat.cosComputable d.val n) d.der }

/-- Computable dual for cos using Taylor series -/
def cosCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.cosComputable d.val n
    der := IntervalRat.mul (IntervalRat.neg (IntervalRat.sinComputable d.val n)) d.der }

/-- Computable dual for sinh using Taylor series (chain rule: d(sinh f) = cosh(f) * f') -/
def sinhCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.sinhComputable d.val n
    der := IntervalRat.mul (IntervalRat.coshComputable d.val n) d.der }

/-- Computable dual for cosh using Taylor series (chain rule: d(cosh f) = sinh(f) * f') -/
def coshCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.coshComputable d.val n
    der := IntervalRat.mul (IntervalRat.sinhComputable d.val n) d.der }

/-- Computable dual for tanh (chain rule: d(tanh f) = sech²(f) * f')
    Since sech²(x) ∈ (0, 1], we use [0, 1] as a conservative bound. -/
def tanhCore (d : DualInterval) (_n : ℕ := 10) : DualInterval :=
  { val := tanhInterval d.val
    -- tanh'(x) = sech²(x) ∈ (0, 1], use [0, 1] as bound
    der := IntervalRat.mul d.der ⟨0, 1, by norm_num⟩ }

end DualInterval

/-- Computable dual interval evaluator for ExprSupportedCore expressions.

    This uses Taylor series approximations for transcendental functions,
    making it fully computable and usable with `native_decide`.

    For unsupported expressions (inv, log, atanh), returns default. -/
def evalDualCore (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : DualInterval :=
  match e with
  | Expr.const q => DualInterval.const q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => DualInterval.add (evalDualCore e₁ ρ cfg) (evalDualCore e₂ ρ cfg)
  | Expr.mul e₁ e₂ => DualInterval.mul (evalDualCore e₁ ρ cfg) (evalDualCore e₂ ρ cfg)
  | Expr.neg e => DualInterval.neg (evalDualCore e ρ cfg)
  | Expr.inv _ => default
  | Expr.exp e => DualInterval.expCore (evalDualCore e ρ cfg) cfg.taylorDepth
  | Expr.sin e => DualInterval.sinCore (evalDualCore e ρ cfg) cfg.taylorDepth
  | Expr.cos e => DualInterval.cosCore (evalDualCore e ρ cfg) cfg.taylorDepth
  | Expr.log _ => default
  | Expr.atan e => DualInterval.atan (evalDualCore e ρ cfg)
  | Expr.arsinh e => DualInterval.arsinh (evalDualCore e ρ cfg)
  | Expr.atanh _ => default
  | Expr.sinc e => DualInterval.sinc (evalDualCore e ρ cfg)
  | Expr.erf e => DualInterval.erfCore (evalDualCore e ρ cfg) cfg.taylorDepth
  | Expr.sinh e => DualInterval.sinhCore (evalDualCore e ρ cfg) cfg.taylorDepth
  | Expr.cosh e => DualInterval.coshCore (evalDualCore e ρ cfg) cfg.taylorDepth
  | Expr.tanh e => DualInterval.tanhCore (evalDualCore e ρ cfg) cfg.taylorDepth

/-- Computable single-variable derivative interval -/
def derivIntervalCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  (evalDualCore e (fun _ => DualInterval.varActive I) cfg).der

/-- Correctness theorem for computable dual value component -/
theorem evalDualCore_val_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv) (cfg : EvalConfig)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ (evalDualCore e ρ_dual cfg).val := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalDualCore, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, evalDualCore]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.eval_add, evalDualCore, DualInterval.add]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.eval_mul, evalDualCore, DualInterval.mul]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, evalDualCore, DualInterval.neg]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, evalDualCore, DualInterval.sinCore]
    exact IntervalRat.mem_sinComputable ih cfg.taylorDepth
  | cos _ ih =>
    simp only [Expr.eval_cos, evalDualCore, DualInterval.cosCore]
    exact IntervalRat.mem_cosComputable ih cfg.taylorDepth
  | exp _ ih =>
    simp only [Expr.eval_exp, evalDualCore, DualInterval.expCore]
    exact IntervalRat.mem_expComputable ih cfg.taylorDepth

/-- Correctness theorem for computable dual derivative component -/
theorem evalDualCore_der_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) (cfg : EvalConfig) :
    deriv (evalFunc1 e) x ∈ (evalDualCore e (fun _ => DualInterval.varActive I) cfg).der := by
  induction hsupp generalizing x with
  | const q =>
    simp only [evalDualCore, DualInterval.const, evalFunc1_const, deriv_const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    simp only [evalDualCore, DualInterval.varActive, evalFunc1_var]
    rw [deriv_id]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalFunc1_differentiable _ h₁.toSupported
    have hd₂ := evalFunc1_differentiable _ h₂.toSupported
    simp only [evalDualCore, DualInterval.add, evalFunc1_add_pi, deriv_add (hd₁ x) (hd₂ x)]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalFunc1_differentiable _ h₁.toSupported
    have hd₂ := evalFunc1_differentiable _ h₂.toSupported
    simp only [evalDualCore, DualInterval.mul, evalFunc1_mul_pi, deriv_mul (hd₁ x) (hd₂ x)]
    have hval₁ := evalDualCore_val_correct _ h₁ (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx)
    have hval₂ := evalDualCore_val_correct _ h₂ (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx)
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁ (ih₂ x hx))
  | neg hs ih =>
    have hd := evalFunc1_differentiable _ hs.toSupported
    simp only [evalDualCore, DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    have hd := evalFunc1_differentiable e' hs.toSupported
    simp only [evalDualCore, DualInterval.sinCore, evalFunc1_sin]
    rw [deriv_sin (hd.differentiableAt)]
    have hval := evalDualCore_val_correct e' hs (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx)
    have hcos := IntervalRat.mem_cosComputable hval cfg.taylorDepth
    exact IntervalRat.mem_mul hcos (ih x hx)
  | @cos e' hs ih =>
    have hd := evalFunc1_differentiable e' hs.toSupported
    simp only [evalDualCore, DualInterval.cosCore, evalFunc1_cos]
    rw [deriv_cos (hd.differentiableAt)]
    have hval := evalDualCore_val_correct e' hs (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx)
    have hsin := IntervalRat.mem_sinComputable hval cfg.taylorDepth
    have hnegsin := IntervalRat.mem_neg hsin
    exact IntervalRat.mem_mul hnegsin (ih x hx)
  | @exp e' hs ih =>
    have hd := evalFunc1_differentiable e' hs.toSupported
    simp only [evalDualCore, DualInterval.expCore, evalFunc1_exp]
    rw [deriv_exp (hd.differentiableAt)]
    have hval := evalDualCore_val_correct e' hs (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx)
    have hexp := IntervalRat.mem_expComputable hval cfg.taylorDepth
    exact IntervalRat.mem_mul hexp (ih x hx)

/-- Convenience theorem: derivIntervalCore correctness -/
theorem derivIntervalCore_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) (cfg : EvalConfig) :
    deriv (evalFunc1 e) x ∈ derivIntervalCore e I cfg :=
  evalDualCore_der_correct e hsupp I x hx cfg

/-- If derivIntervalCore doesn't contain zero, the derivative is nonzero everywhere on I.
    This is a key theorem for Newton contraction analysis. -/
theorem derivIntervalCore_nonzero_implies_deriv_nonzero (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : ¬(derivIntervalCore e I cfg).containsZero) :
    ∀ x ∈ I, deriv (evalFunc1 e) x ≠ 0 := by
  intro x hx hcontra
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  simp only [IntervalRat.containsZero, not_and_or, not_le] at h
  rw [hcontra] at hmem
  rcases h with hlo | hhi
  · exact absurd hmem.1 (not_le.mpr (by exact_mod_cast hlo))
  · exact absurd hmem.2 (not_le.mpr (by exact_mod_cast hhi))

/-- If derivIntervalCore.lo > 0, then the derivative is positive everywhere on I. -/
theorem derivIntervalCore_pos_implies_deriv_pos (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, 0 < deriv (evalFunc1 e) x := by
  intro x hx
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  calc (0 : ℝ) < (derivIntervalCore e I cfg).lo := by exact_mod_cast h
    _ ≤ deriv (evalFunc1 e) x := hmem.1

/-- If derivIntervalCore.hi < 0, then the derivative is negative everywhere on I. -/
theorem derivIntervalCore_neg_implies_deriv_neg (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, deriv (evalFunc1 e) x < 0 := by
  intro x hx
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  calc deriv (evalFunc1 e) x ≤ (derivIntervalCore e I cfg).hi := hmem.2
    _ < 0 := by exact_mod_cast h

/-- Strictly positive derivative (via Core bounds) implies strict monotonicity -/
theorem strictMonoOn_of_derivIntervalCore_pos (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    StrictMonoOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp.toSupported
  have hderiv_pos := derivIntervalCore_pos_implies_deriv_pos e hsupp I cfg hpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_pos x hx_mem

/-- Strictly negative derivative (via Core bounds) implies strict antitonicity -/
theorem strictAntiOn_of_derivIntervalCore_neg (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hneg : (derivIntervalCore e I cfg).hi < 0) :
    StrictAntiOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp.toSupported
  have hderiv_neg := derivIntervalCore_neg_implies_deriv_neg e hsupp I cfg hneg
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_neg x hx_mem

end LeanBound.Numerics
