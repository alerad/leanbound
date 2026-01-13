/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.IntervalRat.Basic
import LeanBound.Core.Expr
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rational Endpoint Intervals - Transcendental Functions

This file provides noncomputable interval bounds for transcendental functions
using floor/ceiling to obtain rational endpoints.

## Main definitions

* `ofRealEndpoints` - Create rational interval from real bounds using floor/ceil
* `expInterval` - Interval bound for exponential
* `logInterval` - Interval bound for logarithm (positive intervals)
* `atanhIntervalComputed` - Interval bound for atanh (intervals in (-1, 1))
* `sqrtInterval` - Interval bound for square root

## Main theorems

* `mem_expInterval` - FTIA for exp
* `mem_logInterval` - FTIA for log
* `mem_atanhIntervalComputed` - FTIA for atanh
* `mem_sqrtInterval` - FTIA for sqrt

## Design notes

All definitions in this file are noncomputable as they use `Real.exp`, `Real.log`,
etc. For computable versions, see `IntervalRat.Taylor`.
-/

namespace LeanBound.Core

namespace IntervalRat

/-! ### Rational enclosure of real intervals -/

/-- Coarse rational enclosure of a real interval using floor/ceil.
    Given a real interval [lo, hi], returns a rational interval [⌊lo⌋, ⌈hi⌉]
    that is guaranteed to contain all points in the original interval. -/
noncomputable def ofRealEndpoints (lo hi : ℝ) (hle : lo ≤ hi) : IntervalRat where
  lo := ⌊lo⌋
  hi := ⌈hi⌉
  le := by
    have h1 : (⌊lo⌋ : ℝ) ≤ lo := Int.floor_le lo
    have h2 : hi ≤ (⌈hi⌉ : ℝ) := Int.le_ceil hi
    have h3 : (⌊lo⌋ : ℝ) ≤ (⌈hi⌉ : ℝ) := le_trans h1 (le_trans hle h2)
    exact_mod_cast h3

/-- Any point in [lo, hi] is in the rational enclosure [⌊lo⌋, ⌈hi⌉] -/
theorem mem_ofRealEndpoints {x lo hi : ℝ} (hle : lo ≤ hi) (hx : lo ≤ x ∧ x ≤ hi) :
    x ∈ ofRealEndpoints lo hi hle := by
  simp only [mem_def, ofRealEndpoints]
  constructor
  · have h := Int.floor_le lo
    exact le_trans h hx.1
  · have h := Int.le_ceil hi
    exact le_trans hx.2 h

/-! ### Exponential interval -/

/-- Interval bound for exp on rational intervals.
    Since exp is strictly increasing, exp([a,b]) ⊆ [⌊exp(a)⌋, ⌈exp(b)⌉].
    This uses Real.exp and floor/ceil to get rational bounds. -/
noncomputable def expInterval (I : IntervalRat) : IntervalRat :=
  ofRealEndpoints (Real.exp I.lo) (Real.exp I.hi)
    (Real.exp_le_exp.mpr (by exact_mod_cast I.le))

/-- FTIA for exp: if x ∈ I, then exp(x) ∈ expInterval(I) -/
theorem mem_expInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.exp x ∈ expInterval I := by
  simp only [expInterval]
  apply mem_ofRealEndpoints
  simp only [mem_def] at hx
  constructor
  · exact Real.exp_le_exp.mpr hx.1
  · exact Real.exp_le_exp.mpr hx.2

/-! ### Positive interval check -/

/-- Check if an interval is strictly positive (lo > 0) -/
def isPositive (I : IntervalRat) : Prop := 0 < I.lo

/-- Decidable isPositive -/
instance (I : IntervalRat) : Decidable (isPositive I) :=
  inferInstanceAs (Decidable (0 < I.lo))

/-- An interval that is guaranteed to be strictly positive -/
structure IntervalRatPos extends IntervalRat where
  lo_pos : 0 < toIntervalRat.lo

/-! ### Logarithm interval (for positive intervals) -/

/-- Interval bound for log on positive rational intervals.
    Since log is strictly increasing on (0, ∞), log([a,b]) ⊆ [⌊log(a)⌋, ⌈log(b)⌉] for a > 0.
    This uses Real.log and floor/ceil to get rational bounds. -/
noncomputable def logInterval (I : IntervalRatPos) : IntervalRat :=
  ofRealEndpoints (Real.log I.lo) (Real.log I.hi)
    (Real.log_le_log (by exact_mod_cast I.lo_pos) (by exact_mod_cast I.le))

/-- FTIA for log: if x ∈ I with lo > 0, then log(x) ∈ logInterval(I) -/
theorem mem_logInterval {x : ℝ} {I : IntervalRatPos} (hx : x ∈ I.toIntervalRat) :
    Real.log x ∈ logInterval I := by
  simp only [logInterval]
  apply mem_ofRealEndpoints
  simp only [mem_def] at hx
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast I.lo_pos
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
  constructor
  · exact Real.log_le_log hlo_pos hx.1
  · exact Real.log_le_log hx_pos hx.2

/-! ### Atanh interval (for intervals in (-1, 1)) -/

/-- An interval strictly contained in (-1, 1), suitable for atanh -/
structure IntervalRatInUnitBall where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi
  lo_gt : -1 < lo
  hi_lt : hi < 1

/-- Convert to standard interval -/
def IntervalRatInUnitBall.toIntervalRat (I : IntervalRatInUnitBall) : IntervalRat :=
  ⟨I.lo, I.hi, I.le⟩

/-- Membership in the underlying interval -/
instance : Membership ℝ IntervalRatInUnitBall where
  mem I x := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

theorem IntervalRatInUnitBall.mem_def {x : ℝ} {I : IntervalRatInUnitBall} :
    x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ I.hi := Iff.rfl

/-- Interval bound for atanh on intervals strictly inside (-1, 1).
    Since atanh is strictly increasing on (-1, 1), atanh([a,b]) ⊆ [⌊atanh(a)⌋, ⌈atanh(b)⌉]. -/
noncomputable def atanhIntervalComputed (I : IntervalRatInUnitBall) : IntervalRat :=
  have hlo : (-1 : ℝ) < I.lo := by exact_mod_cast I.lo_gt
  have hhi : (I.hi : ℝ) < 1 := by exact_mod_cast I.hi_lt
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  ofRealEndpoints (Real.atanh I.lo) (Real.atanh I.hi)
    (Real.atanh_mono
      (by rw [abs_lt]; constructor <;> linarith)
      (by rw [abs_lt]; constructor <;> linarith)
      hle)

/-- FTIA for atanh: if x ∈ I and I ⊂ (-1, 1), then atanh(x) ∈ atanhIntervalComputed(I) -/
theorem mem_atanhIntervalComputed {x : ℝ} {I : IntervalRatInUnitBall} (hx : x ∈ I) :
    Real.atanh x ∈ atanhIntervalComputed I := by
  simp only [atanhIntervalComputed]
  apply mem_ofRealEndpoints
  have hlo : (-1 : ℝ) < I.lo := by exact_mod_cast I.lo_gt
  have hhi : (I.hi : ℝ) < 1 := by exact_mod_cast I.hi_lt
  rw [IntervalRatInUnitBall.mem_def] at hx
  have hx_lo : -1 < x := by linarith [hx.1]
  have hx_hi : x < 1 := by linarith [hx.2]
  have habs_lo : |(I.lo : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_hi : |(I.hi : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_x : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  constructor
  · exact Real.atanh_mono habs_lo habs_x hx.1
  · exact Real.atanh_mono habs_x habs_hi hx.2

/-! ### Square Root Interval -/

/-- Square root interval with conservative bounds.
    For a non-negative interval [lo, hi], sqrt is monotone so:
    sqrt([lo, hi]) ⊆ [0, max(hi, 1)]

    The lower bound is 0 (always sound for sqrt).
    The upper bound uses max(hi, 1) which satisfies sqrt(x) ≤ max(x, 1) for x ≥ 0. -/
def sqrtInterval (I : IntervalRat) : IntervalRat :=
  ⟨0, max I.hi 1, by simp [le_max_iff]⟩

/-- Helper: sqrt(x) ≤ max(x, 1) for x ≥ 0 -/
private theorem sqrt_le_max_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ max x 1 := by
  rcases le_or_gt x 1 with hle | hgt
  · -- x ≤ 1: sqrt(x) ≤ 1 ≤ max(x, 1)
    calc Real.sqrt x ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
      _ ≤ max x 1 := le_max_right x 1
  · -- x > 1: sqrt(x) < x ≤ max(x, 1)
    have hx_pos : 0 < x := lt_trans zero_lt_one hgt
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hsqrt_gt_one : 1 < Real.sqrt x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hgt
    have hsqrt_lt : Real.sqrt x < x := by
      have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
      have h2 : Real.sqrt x * 1 < Real.sqrt x * Real.sqrt x :=
        mul_lt_mul_of_pos_left hsqrt_gt_one hsqrt_pos
      simp only [mul_one] at h2
      linarith
    calc Real.sqrt x ≤ x := le_of_lt hsqrt_lt
      _ ≤ max x 1 := le_max_left x 1

/-- Soundness of sqrt interval: if x ∈ I and x ≥ 0, then sqrt(x) ∈ sqrtInterval I -/
theorem mem_sqrtInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hx_nn : 0 ≤ x) :
    Real.sqrt x ∈ sqrtInterval I := by
  simp only [mem_def, sqrtInterval, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
  constructor
  · exact Real.sqrt_nonneg x
  · calc Real.sqrt x ≤ max x 1 := sqrt_le_max_one hx_nn
      _ ≤ max (I.hi : ℝ) 1 := max_le_max_right 1 hx.2

/-- General soundness of sqrt interval: works for any x ∈ I (including negative).
    When x < 0, Real.sqrt x = 0, which is always in [0, max(hi, 1)]. -/
theorem mem_sqrtInterval' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtInterval I := by
  rcases le_or_gt 0 x with hnn | hneg
  · -- x ≥ 0: use the standard soundness
    exact mem_sqrtInterval hx hnn
  · -- x < 0: sqrt(x) = 0, and 0 ∈ [0, max(hi, 1)]
    simp only [mem_def, sqrtInterval, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
    have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
    rw [hsqrt_zero]
    constructor
    · exact le_refl 0
    · calc (0 : ℝ) ≤ 1 := by norm_num
        _ ≤ max (I.hi : ℝ) 1 := le_max_right _ _

end IntervalRat

end LeanBound.Core
