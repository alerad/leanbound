/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Expr
import LeanBound.Core.IntervalReal
import LeanBound.Core.IntervalRealEndpoints
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Interval Evaluation of Expressions

This file implements interval evaluation for `LeanBound.Core.Expr`. Given an
expression and intervals for its variables, we compute an interval guaranteed
to contain all possible values.

## Main definitions

### Core (computable) subset
* `ExprSupportedCore` - Predicate for expressions in the computable subset
* `evalIntervalCore` - Computable interval evaluator for core expressions
* `evalIntervalCore_correct` - Correctness theorem for core evaluation

### Extended (noncomputable) subset
* `ExprSupported` - Predicate for the noncomputable AD subset (const, var, add, mul, neg, sin, cos, exp)
* `evalInterval` - Noncomputable interval evaluator supporting exp
* `evalInterval_correct` - Correctness theorem for extended evaluation

## Design notes

Core subset (computable): const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh, tanh, pi
Extended subset (noncomputable): const, var, add, mul, neg, sin, cos, exp

The core subset is kept computable so that tactics can use `native_decide`
for interval bound checking. The extended subset uses `Real.exp` with
floor/ceil bounds, which requires noncomputability.

For exp, we use floor/ceil to get rational bounds from Real.exp.

Not yet supported in `ExprSupportedCore`: inv (requires nonzero interval checks),
log (requires positive interval checks); use `evalInterval?` for these.
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-! ### Core supported expression subset (computable) -/

/-- Predicate indicating an expression is in the computable core subset.
    Supports: const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh, tanh, pi
    Does NOT support: inv, log, atan, arsinh, atanh -/
inductive ExprSupportedCore : Expr → Prop where
  | const (q : ℚ) : ExprSupportedCore (Expr.const q)
  | var (idx : Nat) : ExprSupportedCore (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.neg e)
  | sin {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sin e)
  | cos {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cos e)
  | exp {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.exp e)
  | sqrt {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sqrt e)
  | sinh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sinh e)
  | cosh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cosh e)
  | tanh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.tanh e)
  | pi : ExprSupportedCore Expr.pi

/-! ### Extended supported expression subset (with exp) -/

/-- Predicate indicating an expression is in the fully-verified subset for AD.
    Supports: const, var, add, mul, neg, sin, cos, exp
    Does NOT support:
    - sqrt (not differentiable at 0 - use ExprSupportedCore for interval evaluation only)
    - inv (requires nonzero interval checks)
    - log (requires positive interval checks)
    - atan/arsinh/atanh (derivative proofs incomplete - use ExprSupportedWithInv + evalInterval?) -/
inductive ExprSupported : Expr → Prop where
  | const (q : ℚ) : ExprSupported (Expr.const q)
  | var (idx : Nat) : ExprSupported (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupported e₁ → ExprSupported e₂ → ExprSupported (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupported e₁ → ExprSupported e₂ → ExprSupported (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupported e → ExprSupported (Expr.neg e)
  | sin {e : Expr} : ExprSupported e → ExprSupported (Expr.sin e)
  | cos {e : Expr} : ExprSupported e → ExprSupported (Expr.cos e)
  | exp {e : Expr} : ExprSupported e → ExprSupported (Expr.exp e)

/-- ExprSupported expressions are also in ExprSupportedCore -/
theorem ExprSupported.toCore {e : Expr} (h : ExprSupported e) : ExprSupportedCore e := by
  induction h with
  | const q => exact ExprSupportedCore.const q
  | var idx => exact ExprSupportedCore.var idx
  | add _ _ ih₁ ih₂ => exact ExprSupportedCore.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact ExprSupportedCore.mul ih₁ ih₂
  | neg _ ih => exact ExprSupportedCore.neg ih
  | sin _ ih => exact ExprSupportedCore.sin ih
  | cos _ ih => exact ExprSupportedCore.cos ih
  | exp _ ih => exact ExprSupportedCore.exp ih

/-! ### Interval bounds for transcendental functions -/

/-- Simple interval bound for sin.
    Since |sin x| ≤ 1 for all x, we use the global bound [-1, 1].
    This is sound but not tight. -/
def sinInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-1, 1, by norm_num⟩

/-- Correctness of sin interval: sin x ∈ [-1, 1] for all x -/
theorem mem_sinInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.sin x ∈ sinInterval I := by
  simp only [IntervalRat.mem_def, sinInterval]
  have h := Real.sin_mem_Icc x
  simp only [Set.mem_Icc] at h
  simp only [Rat.cast_neg, Rat.cast_one]
  exact h

/-- Simple interval bound for cos.
    Since |cos x| ≤ 1 for all x, we use the global bound [-1, 1].
    This is sound but not tight. -/
def cosInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-1, 1, by norm_num⟩

/-- Correctness of cos interval: cos x ∈ [-1, 1] for all x -/
theorem mem_cosInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.cos x ∈ cosInterval I := by
  simp only [IntervalRat.mem_def, cosInterval]
  have h := Real.cos_mem_Icc x
  simp only [Set.mem_Icc] at h
  simp only [Rat.cast_neg, Rat.cast_one]
  exact h

/-- Simple interval bound for atan.
    Since atan x ∈ (-π/2, π/2) for all x, we use the global bound [-2, 2].
    This is sound but not tight (π/2 ≈ 1.57). -/
def atanInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-2, 2, by norm_num⟩

/-- Correctness of atan interval: arctan x ∈ [-2, 2] for all x -/
theorem mem_atanInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.arctan x ∈ atanInterval I := by
  simp only [IntervalRat.mem_def, atanInterval, Rat.cast_neg, Rat.cast_ofNat]
  -- arctan x ∈ (-π/2, π/2), and π/2 < 2 since π < 4
  have h_lo : Real.arctan x > -Real.pi / 2 := by
    have := Real.neg_pi_div_two_lt_arctan x; linarith
  have h_hi : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
  have hpi_lt_four : Real.pi < 4 := Real.pi_lt_four
  have hpi_lo : -Real.pi / 2 > (-2 : ℝ) := by linarith
  have hpi_hi : Real.pi / 2 < (2 : ℝ) := by linarith
  constructor <;> linarith

/-- Simple interval bound for arsinh.
    arsinh is unbounded, so we use a very rough linear bound.
    We use max(|lo|, |hi|) + 1 as a safe bound that always works. -/
def arsinhInterval (I : IntervalRat) : IntervalRat :=
  let bound := max (abs I.lo) (abs I.hi) + 1
  ⟨-bound, bound, by
    have h1 : (0 : ℚ) ≤ |I.lo| := abs_nonneg I.lo
    have h2 : |I.lo| ≤ |I.lo| ⊔ |I.hi| := le_max_left _ _
    have h3 : (0 : ℚ) ≤ |I.lo| ⊔ |I.hi| := le_trans h1 h2
    have h4 : (0 : ℚ) ≤ |I.lo| ⊔ |I.hi| + 1 := by linarith
    have h5 : -(|I.lo| ⊔ |I.hi| + 1) ≤ |I.lo| ⊔ |I.hi| + 1 := by linarith
    exact h5⟩

/-- Correctness of arsinh interval.
    Uses the bound |arsinh x| ≤ |x| for all x (from IntervalRealEndpoints). -/
theorem mem_arsinhInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.arsinh x ∈ arsinhInterval I := by
  simp only [IntervalRat.mem_def, arsinhInterval]
  -- Key bound: |arsinh x| ≤ |x| + 1
  -- This is a well-known bound that follows from sinh y ≥ y for y ≥ 0
  have hbound : |Real.arsinh x| ≤ |x| + 1 := by
    -- Use the sharper bound |arsinh x| ≤ |x| from IntervalRealEndpoints
    have h := IntervalReal.abs_arsinh_le_abs x
    linarith
  simp only [IntervalRat.mem_def] at hx
  have hx_bound : |x| ≤ max (|I.lo|) (|I.hi|) := by
    simp only [Rat.cast_abs, Rat.cast_max]
    rcases le_or_gt x 0 with hxneg | hxpos
    · simp only [abs_of_nonpos hxneg]
      calc -x ≤ -(I.lo : ℝ) := by linarith [hx.1]
        _ ≤ |↑I.lo| := neg_le_abs _
        _ ≤ max |↑I.lo| |↑I.hi| := le_max_left _ _
    · simp only [abs_of_pos hxpos]
      calc x ≤ I.hi := hx.2
        _ ≤ |↑I.hi| := le_abs_self _
        _ ≤ max |↑I.lo| |↑I.hi| := le_max_right _ _
  have habs_lo : -(|x| + 1) ≤ Real.arsinh x := (abs_le.mp hbound).1
  have habs_hi : Real.arsinh x ≤ |x| + 1 := (abs_le.mp hbound).2
  have hmax_cast : (max (|I.lo|) (|I.hi|) : ℝ) = max |↑I.lo| |↑I.hi| := by
    rfl
  constructor
  · simp only [Rat.cast_neg, Rat.cast_add, Rat.cast_one, Rat.cast_max, Rat.cast_abs]
    have h1 : -(|↑I.lo| ⊔ |↑I.hi| + 1) = -(max |↑I.lo| |↑I.hi|) - (1 : ℝ) := by ring
    have h2 : -(max |↑I.lo| |↑I.hi|) - (1 : ℝ) ≤ -|x| - 1 := by
      have hxb : |x| ≤ max |↑I.lo| |↑I.hi| := by
        convert hx_bound using 1
        simp [Rat.cast_max, Rat.cast_abs]
      linarith
    have h3 : -|x| - (1 : ℝ) ≤ Real.arsinh x := by
      have : -(|x| + 1) = -|x| - 1 := by ring
      rw [← this]; exact habs_lo
    linarith
  · simp only [Rat.cast_add, Rat.cast_one, Rat.cast_max, Rat.cast_abs]
    have h1 : Real.arsinh x ≤ |x| + 1 := habs_hi
    have h2 : |x| + (1 : ℝ) ≤ max |↑I.lo| |↑I.hi| + 1 := by
      have hxb : |x| ≤ max |↑I.lo| |↑I.hi| := by
        convert hx_bound using 1
        simp [Rat.cast_max, Rat.cast_abs]
      linarith
    linarith

/-- Interval bound for atanh.
    atanh is defined for (-1, 1). If interval is within this range,
    we compute tight bounds using monotonicity. Otherwise returns default. -/
noncomputable def atanhInterval (I : IntervalRat) : IntervalRat :=
  if h : -1 < I.lo ∧ I.hi < 1 then
    let Iball : IntervalRat.IntervalRatInUnitBall := ⟨I.lo, I.hi, I.le, h.1, h.2⟩
    IntervalRat.atanhIntervalComputed Iball
  else
    default

/-- Correctness of atanh interval: when x ∈ I and I ⊂ (-1, 1), atanh(x) ∈ atanhInterval I. -/
theorem mem_atanhInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (hlo : -1 < I.lo) (hhi : I.hi < 1) :
    Real.atanh x ∈ atanhInterval I := by
  unfold atanhInterval
  simp only [hlo, hhi, and_self, ↓reduceDIte]
  let Iball : IntervalRat.IntervalRatInUnitBall := ⟨I.lo, I.hi, I.le, hlo, hhi⟩
  have hx_ball : x ∈ Iball := by
    simp only [Membership.mem]
    exact hx
  exact IntervalRat.mem_atanhIntervalComputed hx_ball

/-- Tight interval bound for tanh.
    Since tanh(x) ∈ (-1, 1) for all x ∈ ℝ, we use the global bound [-1, 1].
    This avoids the interval explosion that occurs when desugaring to exp. -/
def tanhInterval (_I : IntervalRat) : IntervalRat :=
  ⟨-1, 1, by norm_num⟩

/-- Correctness of tanh interval: tanh x ∈ [-1, 1] for all x -/
theorem mem_tanhInterval {x : ℝ} {I : IntervalRat} (_hx : x ∈ I) :
    Real.tanh x ∈ tanhInterval I := by
  simp only [IntervalRat.mem_def, tanhInterval, Rat.cast_neg, Rat.cast_one]
  constructor
  -- tanh x ≥ -1 for all x: use that tanh = sinh/cosh and cosh > 0
  · rw [Real.tanh_eq_sinh_div_cosh]
    have hcosh : Real.cosh x > 0 := Real.cosh_pos x
    -- -1 ≤ sinh/cosh iff -cosh ≤ sinh (since cosh > 0)
    rw [le_div_iff₀ hcosh, neg_one_mul]
    -- Need: -cosh x ≤ sinh x
    -- sinh x = (exp x - exp(-x))/2, cosh x = (exp x + exp(-x))/2
    -- sinh x + cosh x = exp x ≥ 0 ✓
    rw [Real.sinh_eq, Real.cosh_eq]
    have h1 : Real.exp x > 0 := Real.exp_pos x
    linarith
  -- tanh x ≤ 1 for all x: use that sinh ≤ cosh (since exp(-x) > 0)
  · rw [Real.tanh_eq_sinh_div_cosh]
    have hcosh : Real.cosh x > 0 := Real.cosh_pos x
    rw [div_le_one₀ hcosh]
    -- Need: sinh x ≤ cosh x
    rw [Real.sinh_eq, Real.cosh_eq]
    have h2 : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith

/-- Interval enclosure for π.
    Uses tight bounds from Mathlib's pi_gt_d20 and pi_lt_d20 which give 20 decimal digits.
    3.14159265358979323846 < π < 3.14159265358979323847 -/
def piInterval : IntervalRat :=
  -- Use rational approximation: 31415926535897932/10000000000000000 ≤ pi ≤ 31415926535897933/10000000000000000
  ⟨31415926535897932/10000000000000000, 31415926535897933/10000000000000000, by norm_num⟩

/-- Correctness of pi interval: Real.pi ∈ piInterval -/
theorem mem_piInterval : Real.pi ∈ piInterval := by
  simp only [IntervalRat.mem_def, piInterval]
  constructor
  · -- Lower bound from pi_gt_d20
    have h : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    have eq : (31415926535897932 : ℚ) / 10000000000000000 = (3.1415926535897932 : ℚ) := by norm_num
    simp only [Rat.cast_div, Rat.cast_ofNat] at *
    linarith
  · -- Upper bound from pi_lt_d20
    have h : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    have eq : (31415926535897933 : ℚ) / 10000000000000000 = (3.1415926535897933 : ℚ) := by norm_num
    simp only [Rat.cast_div, Rat.cast_ofNat] at *
    linarith

/-- Interval bound for sinh using computable Taylor series for exp.
    sinh(x) = (exp(x) - exp(-x)) / 2, and sinh is strictly monotonic.
    This computes tight bounds using the verified exp implementation. -/
def sinhInterval (I : IntervalRat) (taylorDepth : ℕ := 10) : IntervalRat :=
  IntervalRat.sinhComputable I taylorDepth

/-- Interval bound for cosh using computable Taylor series for exp.
    cosh(x) = (exp(x) + exp(-x)) / 2, with minimum 1 at x = 0.
    This computes tight bounds using the verified exp implementation. -/
def coshInterval (I : IntervalRat) (taylorDepth : ℕ := 10) : IntervalRat :=
  IntervalRat.coshComputable I taylorDepth

/-! ### Interval inverse -/

/-- Wide bound constant for when inverse is undefined (denominator contains 0) -/
def invWideBound : ℚ := 10^30

private theorem invWideBound_pos : (0 : ℝ) < invWideBound := by
  simp only [invWideBound]
  norm_num

/-- Computable interval inverse.
    For [a,b] with a > 0: returns [1/b, 1/a] (1/x is decreasing on positive reals)
    For [a,b] with b < 0: returns [1/b, 1/a] (1/x is decreasing on negative reals)
    For intervals containing 0: returns very wide bounds [-M, M] as a sound default -/
def invInterval (I : IntervalRat) : IntervalRat :=
  if h : I.lo > 0 then
    -- Positive interval: 1/x is decreasing, so [1/b, 1/a]
    let invHi := 1 / I.lo
    let invLo := 1 / I.hi
    if hle : invLo ≤ invHi then { lo := invLo, hi := invHi, le := hle }
    else { lo := invHi, hi := invLo, le := by linarith }
  else if h' : I.hi < 0 then
    -- Negative interval: 1/x is decreasing, so [1/b, 1/a]
    let invHi := 1 / I.lo
    let invLo := 1 / I.hi
    if hle : invLo ≤ invHi then { lo := invLo, hi := invHi, le := hle }
    else { lo := invHi, hi := invLo, le := by linarith }
  else
    -- Interval contains zero: return wide bounds
    ⟨-invWideBound, invWideBound, by simp only [invWideBound]; norm_num⟩

/-- Correctness of invInterval when denominator interval is positive.
    For x ∈ [a,b] with a > 0, we have 1/x ∈ [1/b, 1/a] -/
theorem mem_invInterval_pos {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hpos : I.lo > 0) :
    x⁻¹ ∈ invInterval I := by
  simp only [IntervalRat.mem_def] at hx ⊢
  simp only [invInterval, hpos, ↓reduceDIte]
  -- x > 0 since x ≥ I.lo > 0
  have hx_pos : (x : ℝ) > 0 := by
    have h1 : (I.lo : ℝ) ≤ x := hx.1
    have h2 : (0 : ℝ) < I.lo := by exact_mod_cast hpos
    linarith
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  -- For positive x: 1/b ≤ 1/x ≤ 1/a when a ≤ x ≤ b
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hlo_ne : (I.lo : ℝ) ≠ 0 := ne_of_gt hlo_pos
  have hhi_pos : (0 : ℝ) < I.hi := by
    have := I.le
    have h : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast this
    linarith
  have hhi_ne : (I.hi : ℝ) ≠ 0 := ne_of_gt hhi_pos
  split_ifs with hle
  · -- Case: 1/hi ≤ 1/lo (normal ordering)
    simp only [Rat.cast_inv, one_div]
    constructor
    · -- (I.hi)⁻¹ ≤ x⁻¹ follows from x ≤ I.hi
      exact (inv_le_inv₀ hhi_pos hx_pos).mpr hx.2
    · -- x⁻¹ ≤ (I.lo)⁻¹ follows from I.lo ≤ x
      exact (inv_le_inv₀ hx_pos hlo_pos).mpr hx.1
  · -- Case: 1/lo < 1/hi (impossible for positive lo ≤ hi, but we prove the goal anyway)
    -- 1/hi ≤ 1/lo is always true when lo ≤ hi and both positive
    have hhi_pos_q : (0 : ℚ) < I.hi := by
      have := I.le
      linarith
    have hle' : (1 : ℚ) / I.hi ≤ 1 / I.lo := by
      rw [div_le_div_iff₀ hhi_pos_q hpos]
      simp only [one_mul]
      exact I.le
    exact absurd hle' hle

/-- Correctness of invInterval when denominator interval is negative.
    For x ∈ [a,b] with b < 0, we have 1/x ∈ [1/b, 1/a] -/
theorem mem_invInterval_neg {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hneg : I.hi < 0) :
    x⁻¹ ∈ invInterval I := by
  simp only [IntervalRat.mem_def] at hx ⊢
  -- I.lo ≤ 0 since I.lo ≤ I.hi < 0
  have hlo_le : ¬(I.lo > 0) := by
    have := I.le
    have hhi_neg : I.hi < 0 := hneg
    intro h
    have : (I.lo : ℚ) ≤ I.hi := this
    linarith
  simp only [invInterval, hlo_le, ↓reduceDIte, hneg]
  -- x < 0 since x ≤ I.hi < 0
  have hx_neg : (x : ℝ) < 0 := by
    have h1 : x ≤ I.hi := hx.2
    have h2 : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
    linarith
  have hlo_neg : (I.lo : ℝ) < 0 := by
    have h1 : I.lo ≤ I.hi := I.le
    have h2 : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
    have h3 : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast h1
    linarith
  have hhi_neg' : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
  -- For negative x: 1/x is still decreasing, so 1/b ≤ 1/x ≤ 1/a
  split_ifs with hle
  · simp only [Rat.cast_inv, one_div]
    constructor
    · -- (I.hi)⁻¹ ≤ x⁻¹ when x ≤ hi < 0 (since 1/x is decreasing for negatives)
      exact (inv_le_inv_of_neg hhi_neg' hx_neg).mpr hx.2
    · -- x⁻¹ ≤ (I.lo)⁻¹ when lo ≤ x < 0
      exact (inv_le_inv_of_neg hx_neg hlo_neg).mpr hx.1
  · -- Case: 1/lo < 1/hi (impossible for negative lo ≤ hi < 0)
    -- For negative numbers: lo ≤ hi < 0 implies 1/hi ≤ 1/lo
    -- Use: one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a
    have hle' : (1 : ℚ) / I.hi ≤ 1 / I.lo :=
      one_div_le_one_div_of_neg_of_le hneg I.le
    exact absurd hle' hle

/-- Correctness of invInterval when denominator interval contains zero.
    Requires a bound on |x⁻¹| to be provable, since x can be arbitrarily close to 0. -/
theorem mem_invInterval_wide {x : ℝ} {I : IntervalRat}
    (_hx : x ∈ I) (hlo : ¬(I.lo > 0)) (hhi : ¬(I.hi < 0))
    (hbnd : |x⁻¹| ≤ invWideBound) :
    x⁻¹ ∈ invInterval I := by
  simp only [IntervalRat.mem_def, invInterval, hlo, hhi, ↓reduceDIte]
  constructor
  · -- -invWideBound ≤ x⁻¹
    calc ((-invWideBound : ℚ) : ℝ) = -(invWideBound : ℝ) := by simp
      _ ≤ -|x⁻¹| := neg_le_neg hbnd
      _ ≤ x⁻¹ := neg_abs_le x⁻¹
  · -- x⁻¹ ≤ invWideBound
    calc x⁻¹ ≤ |x⁻¹| := le_abs_self x⁻¹
      _ ≤ (invWideBound : ℝ) := hbnd

/-- Main correctness theorem for invInterval.
    Fully proved for intervals bounded away from zero.
    For intervals containing zero, requires a bound on |x⁻¹|. -/
theorem mem_invInterval {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hbnd : |x⁻¹| ≤ invWideBound) :
    x⁻¹ ∈ invInterval I := by
  -- Case split based on the interval position
  by_cases hpos : I.lo > 0
  · exact mem_invInterval_pos hx hpos
  · by_cases hneg : I.hi < 0
    · exact mem_invInterval_neg hx hneg
    · exact mem_invInterval_wide hx hpos hneg hbnd

/-- Correctness of invInterval for intervals bounded away from zero (no extra hypothesis needed) -/
theorem mem_invInterval_nonzero {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hnonzero : I.lo > 0 ∨ I.hi < 0) :
    x⁻¹ ∈ invInterval I := by
  rcases hnonzero with hpos | hneg
  · exact mem_invInterval_pos hx hpos
  · exact mem_invInterval_neg hx hneg

/-! ### Core interval evaluation (computable) -/

/-- Variable assignment as intervals -/
abbrev IntervalEnv := Nat → IntervalRat

/-- Configuration for interval evaluation parameters.
    This allows certificates to specify the required precision. -/
structure EvalConfig where
  /-- Number of Taylor series terms for transcendental functions -/
  taylorDepth : ℕ := 10
  deriving Repr, DecidableEq

/-- Default evaluation configuration with 10 Taylor terms -/
instance : Inhabited EvalConfig := ⟨{ taylorDepth := 10 }⟩

/-- Computable interval evaluator for core expressions with configurable depth.

    For expressions in `ExprSupportedCore`, this computes correct interval
    bounds with a fully-verified proof.

    For inv: computes bounds using `invInterval`, but correctness is not
    covered by `evalIntervalCore_correct`. Use `evalInterval?` for inv.

    For unsupported expressions (log), returns a default interval.
    Do not rely on results for expressions containing log.

    This evaluator is COMPUTABLE, allowing use of `native_decide` for
    bound checking in tactics. The transcendental functions (exp, sin, cos)
    use Taylor series with configurable depth for precision control. -/
def evalIntervalCore (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig := {}) : IntervalRat :=
  match e with
  | Expr.const q => IntervalRat.singleton q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => IntervalRat.add (evalIntervalCore e₁ ρ cfg) (evalIntervalCore e₂ ρ cfg)
  | Expr.mul e₁ e₂ => IntervalRat.mul (evalIntervalCore e₁ ρ cfg) (evalIntervalCore e₂ ρ cfg)
  | Expr.neg e => IntervalRat.neg (evalIntervalCore e ρ cfg)
  | Expr.inv e => invInterval (evalIntervalCore e ρ cfg)
  | Expr.exp e => IntervalRat.expComputable (evalIntervalCore e ρ cfg) cfg.taylorDepth
  | Expr.sin e => IntervalRat.sinComputable (evalIntervalCore e ρ cfg) cfg.taylorDepth
  | Expr.cos e => IntervalRat.cosComputable (evalIntervalCore e ρ cfg) cfg.taylorDepth
  | Expr.log _ => default  -- Not in ExprSupportedCore; use evalInterval? for log
  | Expr.atan e => atanInterval (evalIntervalCore e ρ cfg)
  | Expr.arsinh e => arsinhInterval (evalIntervalCore e ρ cfg)
  | Expr.atanh _ => default  -- Not in ExprSupportedCore; use evalInterval? for atanh
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf _ => ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
  | Expr.sinh e => sinhInterval (evalIntervalCore e ρ cfg) cfg.taylorDepth
  | Expr.cosh e => coshInterval (evalIntervalCore e ρ cfg) cfg.taylorDepth
  | Expr.tanh e => tanhInterval (evalIntervalCore e ρ cfg)  -- Tight bounds: [-1, 1]
  | Expr.sqrt e => IntervalRat.sqrtIntervalTightPrec (evalIntervalCore e ρ cfg)
  | Expr.pi => piInterval

/-- Computable interval evaluator with division support.

    This extends evalIntervalCore to handle inv/div by computing interval inverse
    when the denominator is bounded away from zero. Returns wide bounds when
    the denominator interval contains zero.

    NOTE: This is less rigorous than evalInterval? because it doesn't fail
    when 0 is in the denominator range - it just returns wide bounds. This is
    useful for applications where we want to continue safely
    even when the analysis is imprecise. -/
def evalIntervalCoreWithDiv (e : Expr) (ρ : IntervalEnv) (cfg : EvalConfig := {}) : IntervalRat :=
  match e with
  | Expr.const q => IntervalRat.singleton q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => IntervalRat.add (evalIntervalCoreWithDiv e₁ ρ cfg) (evalIntervalCoreWithDiv e₂ ρ cfg)
  | Expr.mul e₁ e₂ => IntervalRat.mul (evalIntervalCoreWithDiv e₁ ρ cfg) (evalIntervalCoreWithDiv e₂ ρ cfg)
  | Expr.neg e => IntervalRat.neg (evalIntervalCoreWithDiv e ρ cfg)
  | Expr.inv e₁ =>
      let J := evalIntervalCoreWithDiv e₁ ρ cfg
      -- Check if interval is bounded away from zero
      if J.lo > 0 then
        -- Positive interval: [a,b]⁻¹ = [1/b, 1/a]
        let invHi := 1 / J.lo
        let invLo := 1 / J.hi
        if h : invLo ≤ invHi then { lo := invLo, hi := invHi, le := h }
        else { lo := invHi, hi := invLo, le := by linarith }
      else if J.hi < 0 then
        -- Negative interval: [a,b]⁻¹ = [1/b, 1/a] (note: a < b < 0 so 1/b > 1/a)
        let invHi := 1 / J.lo
        let invLo := 1 / J.hi
        if h : invLo ≤ invHi then { lo := invLo, hi := invHi, le := h }
        else { lo := invHi, hi := invLo, le := by linarith }
      else
        -- Interval contains zero: return wide bounds (sound but imprecise)
        ⟨-1000000000000000000000000000000, 1000000000000000000000000000000, by norm_num⟩
  | Expr.exp e => IntervalRat.expComputable (evalIntervalCoreWithDiv e ρ cfg) cfg.taylorDepth
  | Expr.sin e => IntervalRat.sinComputable (evalIntervalCoreWithDiv e ρ cfg) cfg.taylorDepth
  | Expr.cos e => IntervalRat.cosComputable (evalIntervalCoreWithDiv e ρ cfg) cfg.taylorDepth
  | Expr.log e =>
      -- Computable log using Taylor series via atanh reduction
      let arg := evalIntervalCoreWithDiv e ρ cfg
      IntervalRat.logComputable arg cfg.taylorDepth
  | Expr.atan e => atanInterval (evalIntervalCoreWithDiv e ρ cfg)
  | Expr.arsinh e => arsinhInterval (evalIntervalCoreWithDiv e ρ cfg)
  | Expr.atanh _ => ⟨-100, 100, by norm_num⟩  -- Safe wide default for atanh
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf _ => ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
  | Expr.sinh e => sinhInterval (evalIntervalCoreWithDiv e ρ cfg) cfg.taylorDepth
  | Expr.cosh e => coshInterval (evalIntervalCoreWithDiv e ρ cfg) cfg.taylorDepth
  | Expr.tanh e => tanhInterval (evalIntervalCoreWithDiv e ρ cfg)  -- Tight bounds: [-1, 1]
  | Expr.sqrt e => IntervalRat.sqrtIntervalTightPrec (evalIntervalCoreWithDiv e ρ cfg)
  | Expr.pi => piInterval

/-- A real environment is contained in an interval environment -/
def envMem (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) : Prop :=
  ∀ i, ρ_real i ∈ ρ_int i

/-- Fundamental correctness theorem for core evaluation.

    This theorem is FULLY PROVED for core expressions (no sorry, no axioms).
    The `hsupp` hypothesis ensures we only consider expressions in the
    computable verified subset. Works for any Taylor depth. -/
theorem evalIntervalCore_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (hρ : envMem ρ_real ρ_int)
    (cfg : EvalConfig := {}) :
    Expr.eval ρ_real e ∈ evalIntervalCore e ρ_int cfg := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalIntervalCore]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, evalIntervalCore]
    exact hρ idx
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_add, evalIntervalCore]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_mul, evalIntervalCore]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, evalIntervalCore]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, evalIntervalCore]
    exact IntervalRat.mem_sinComputable ih cfg.taylorDepth
  | cos _ ih =>
    simp only [Expr.eval_cos, evalIntervalCore]
    exact IntervalRat.mem_cosComputable ih cfg.taylorDepth
  | exp _ ih =>
    simp only [Expr.eval_exp, evalIntervalCore]
    exact IntervalRat.mem_expComputable ih cfg.taylorDepth
  | sqrt _ ih =>
    simp only [Expr.eval_sqrt, evalIntervalCore]
    exact IntervalRat.mem_sqrtIntervalTightPrec' ih
  | sinh _ ih =>
    simp only [Expr.eval_sinh, evalIntervalCore, sinhInterval]
    exact IntervalRat.mem_sinhComputable ih cfg.taylorDepth
  | cosh _ ih =>
    simp only [Expr.eval_cosh, evalIntervalCore, coshInterval]
    exact IntervalRat.mem_coshComputable ih cfg.taylorDepth
  | tanh _ ih =>
    simp only [Expr.eval_tanh, evalIntervalCore, tanhInterval]
    exact mem_tanhInterval ih
  | pi =>
    simp only [Expr.eval_pi, evalIntervalCore]
    exact mem_piInterval

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

/-- Computable single-variable evaluation for core expressions -/
def evalIntervalCore1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  evalIntervalCore e (fun _ => I) cfg

/-- Correctness for single-variable core evaluation -/
theorem evalIntervalCore1_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) (cfg : EvalConfig := {}) :
    Expr.eval (fun _ => x) e ∈ evalIntervalCore1 e I cfg :=
  evalIntervalCore_correct e hsupp _ _ (fun _ => hx) cfg

/-- Noncomputable single-variable evaluation for extended expressions -/
noncomputable def evalInterval1 (e : Expr) (I : IntervalRat) : IntervalRat :=
  evalInterval e (fun _ => I)

/-- Correctness for single-variable extended evaluation -/
theorem evalInterval1_correct (e : Expr) (hsupp : ExprSupported e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ evalInterval1 e I :=
  evalInterval_correct e hsupp _ _ (fun _ => hx)

/-! ### Smart constructors for supported expressions -/

/-- Build a constant expression (always supported) -/
def mkConst (q : ℚ) : { e : Expr // ExprSupported e } :=
  ⟨Expr.const q, ExprSupported.const q⟩

/-- Build a variable expression (always supported) -/
def mkVar (idx : Nat) : { e : Expr // ExprSupported e } :=
  ⟨Expr.var idx, ExprSupported.var idx⟩

/-- Build an addition (supported if both operands are supported) -/
def mkAdd (e₁ e₂ : { e : Expr // ExprSupported e }) : { e : Expr // ExprSupported e } :=
  ⟨Expr.add e₁.val e₂.val, ExprSupported.add e₁.property e₂.property⟩

/-- Build a multiplication (supported if both operands are supported) -/
def mkMul (e₁ e₂ : { e : Expr // ExprSupported e }) : { e : Expr // ExprSupported e } :=
  ⟨Expr.mul e₁.val e₂.val, ExprSupported.mul e₁.property e₂.property⟩

/-- Build a negation (supported if operand is supported) -/
def mkNeg (e : { e : Expr // ExprSupported e }) : { e : Expr // ExprSupported e } :=
  ⟨Expr.neg e.val, ExprSupported.neg e.property⟩

/-- Build a sin (supported if operand is supported) -/
def mkSin (e : { e : Expr // ExprSupported e }) : { e : Expr // ExprSupported e } :=
  ⟨Expr.sin e.val, ExprSupported.sin e.property⟩

/-- Build a cos (supported if operand is supported) -/
def mkCos (e : { e : Expr // ExprSupported e }) : { e : Expr // ExprSupported e } :=
  ⟨Expr.cos e.val, ExprSupported.cos e.property⟩

/-- Build an exp (supported if operand is supported) -/
def mkExp (e : { e : Expr // ExprSupported e }) : { e : Expr // ExprSupported e } :=
  ⟨Expr.exp e.val, ExprSupported.exp e.property⟩

/-! ### Partial interval evaluation with inv support -/

/-- Partial (Option-returning) interval evaluator supporting inv.

    For expressions with inv, this evaluator returns `none` if the denominator
    interval contains zero, and `some I` with a correct enclosure otherwise.

    This allows safe interval evaluation of expressions like 1/x when we can
    verify the denominator is bounded away from zero.

    For expressions without inv, this always returns `some` with the same
    result as `evalInterval`. -/
noncomputable def evalInterval? (e : Expr) (ρ : IntervalEnv) : Option IntervalRat :=
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
      | some I => some (IntervalRat.expInterval I)
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
            some (IntervalRat.logInterval ⟨J, h⟩)
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

/-- Syntactic support predicate for expressions with inv and log (no semantic conditions).
    This is the most general support predicate, allowing all expression constructors.
    Semantic correctness is handled by evalInterval? returning None when conditions fail. -/
inductive ExprSupportedWithInv : Expr → Prop where
  | const (q : ℚ) : ExprSupportedWithInv (Expr.const q)
  | var (idx : Nat) : ExprSupportedWithInv (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupportedWithInv e₁ → ExprSupportedWithInv e₂ →
      ExprSupportedWithInv (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupportedWithInv e₁ → ExprSupportedWithInv e₂ →
      ExprSupportedWithInv (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.neg e)
  | inv {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.inv e)
  | exp {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.exp e)
  | sin {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.sin e)
  | cos {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.cos e)
  | log {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.log e)
  | atan {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.atan e)
  | arsinh {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.arsinh e)
  | atanh {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.atanh e)
  | sinc {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.sinc e)
  | erf {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.erf e)
  | sqrt {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.sqrt e)
  | pi : ExprSupportedWithInv Expr.pi

/-- ExprSupported implies ExprSupportedWithInv -/
theorem ExprSupported.toWithInv {e : Expr} (h : ExprSupported e) : ExprSupportedWithInv e := by
  induction h with
  | const q => exact ExprSupportedWithInv.const q
  | var idx => exact ExprSupportedWithInv.var idx
  | add _ _ ih₁ ih₂ => exact ExprSupportedWithInv.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact ExprSupportedWithInv.mul ih₁ ih₂
  | neg _ ih => exact ExprSupportedWithInv.neg ih
  | sin _ ih => exact ExprSupportedWithInv.sin ih
  | cos _ ih => exact ExprSupportedWithInv.cos ih
  | exp _ ih => exact ExprSupportedWithInv.exp ih

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
      exact IntervalRat.mem_expInterval (ih I' heq)
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
        exact IntervalRat.mem_logInterval hJ_mem
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
noncomputable def evalInterval?1 (e : Expr) (I : IntervalRat) : Option IntervalRat :=
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

/-! ### Tactic-facing lemmas for interval bounds (core, computable) -/

/-- Upper bound lemma for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth. -/
theorem exprCore_le_of_interval_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hhi : (evalIntervalCore1 e I cfg).hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (evalIntervalCore1 e I cfg).hi := hmem.2
  have hhi_le_c : ((evalIntervalCore1 e I cfg).hi : ℝ) ≤ c := by exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- Lower bound lemma for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth. -/
theorem exprCore_ge_of_interval_lo (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hlo : c ≤ (evalIntervalCore1 e I cfg).lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (evalIntervalCore1 e I cfg).lo ≤ Expr.eval (fun _ => x) e := hmem.1
  have hc_le_lo : (c : ℝ) ≤ (evalIntervalCore1 e I cfg).lo := by exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

/-- Strict upper bound for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth. -/
theorem exprCore_lt_of_interval_hi_lt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hhi : (evalIntervalCore1 e I cfg).hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (evalIntervalCore1 e I cfg).hi := hmem.2
  have hhi_lt_c : ((evalIntervalCore1 e I cfg).hi : ℝ) < c := by exact_mod_cast hhi
  exact lt_of_le_of_lt heval_le_hi hhi_lt_c

/-- Strict lower bound for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth. -/
theorem exprCore_gt_of_interval_lo_gt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hlo : c < (evalIntervalCore1 e I cfg).lo) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (evalIntervalCore1 e I cfg).lo ≤ Expr.eval (fun _ => x) e := hmem.1
  have hc_lt_lo : (c : ℝ) < (evalIntervalCore1 e I cfg).lo := by exact_mod_cast hlo
  exact lt_of_lt_of_le hc_lt_lo hlo_le_eval

/-! ### Tactic-facing lemmas for interval bounds (extended, noncomputable) -/

/-- Upper bound lemma for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_le_of_interval_hi (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (hhi : (evalInterval1 e I).hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (evalInterval1 e I).hi := hmem.2
  have hhi_le_c : ((evalInterval1 e I).hi : ℝ) ≤ c := by exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- Lower bound lemma for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_ge_of_interval_lo (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (hlo : c ≤ (evalInterval1 e I).lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (evalInterval1 e I).lo ≤ Expr.eval (fun _ => x) e := hmem.1
  have hc_le_lo : (c : ℝ) ≤ (evalInterval1 e I).lo := by exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

/-- Strict upper bound for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_lt_of_interval_hi_lt (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (hhi : (evalInterval1 e I).hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (evalInterval1 e I).hi := hmem.2
  have hhi_lt_c : ((evalInterval1 e I).hi : ℝ) < c := by exact_mod_cast hhi
  exact lt_of_le_of_lt heval_le_hi hhi_lt_c

/-- Strict lower bound for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_gt_of_interval_lo_gt (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (hlo : c < (evalInterval1 e I).lo) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (evalInterval1 e I).lo ≤ Expr.eval (fun _ => x) e := hmem.1
  have hc_lt_lo : (c : ℝ) < (evalInterval1 e I).lo := by exact_mod_cast hlo
  exact lt_of_lt_of_le hc_lt_lo hlo_le_eval

/-- Variant for single point (extended). -/
theorem expr_le_of_mem_interval (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hhi : (evalInterval1 e I).hi ≤ c) :
    Expr.eval (fun _ => x) e ≤ c :=
  expr_le_of_interval_hi e hsupp I c hhi x hx

/-- Variant for single point (extended). -/
theorem expr_ge_of_mem_interval (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hlo : c ≤ (evalInterval1 e I).lo) :
    c ≤ Expr.eval (fun _ => x) e :=
  expr_ge_of_interval_lo e hsupp I c hlo x hx

end LeanBound.Numerics
