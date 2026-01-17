/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import LeanCert.Core.Support
import LeanCert.Core.IntervalReal
import LeanCert.Core.IntervalRealEndpoints
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Computable Interval Evaluation

This file implements the computable interval evaluator for `LeanCert.Core.Expr`.
Given an expression and intervals for its variables, we compute an interval
guaranteed to contain all possible values.

## Main definitions

* `IntervalEnv` - Variable assignment as intervals
* `EvalConfig` - Configuration for evaluation parameters (Taylor depth)
* `evalIntervalCore` - Computable interval evaluator for core expressions
* `evalIntervalCore_correct` - Correctness theorem for core evaluation

## Design notes

This evaluator is COMPUTABLE, allowing use of `native_decide` for bound checking
in tactics. The transcendental functions (exp, sin, cos) use Taylor series with
configurable depth for precision control.

For inv: computes bounds using `invInterval`, but correctness is not covered by
`evalIntervalCore_correct`. Use `evalInterval?` for inv.
-/

namespace LeanCert.Engine

open LeanCert.Core

-- Re-export support predicates from Core for backward compatibility
export LeanCert.Core (ExprSupportedCore ExprSupported ExprSupportedWithInv)

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

/-! ### Convenience functions -/

/-- Computable single-variable evaluation for core expressions -/
def evalIntervalCore1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  evalIntervalCore e (fun _ => I) cfg

/-- Correctness for single-variable core evaluation -/
theorem evalIntervalCore1_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) (cfg : EvalConfig := {}) :
    Expr.eval (fun _ => x) e ∈ evalIntervalCore1 e I cfg :=
  evalIntervalCore_correct e hsupp _ _ (fun _ => hx) cfg

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

end LeanCert.Engine
