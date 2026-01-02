/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Interval
import LeanBound.Core.Taylor
import LeanBound.Core.Expr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Rational Endpoint Intervals

This file defines `IntervalRat`, a concrete interval type with rational endpoints
suitable for computation. We prove the Fundamental Theorem of Interval Arithmetic
(FTIA) for each operation.

## Main definitions

* `LeanBound.Core.IntervalRat` - Intervals with rational endpoints
* `LeanBound.Core.IntervalRat.toSet` - Semantic interpretation as a subset of ℝ
* Operations: `add`, `neg`, `sub`, `mul`, `inv`, `div`

## Main theorems

* `mem_add` - FTIA for addition
* `mem_neg` - FTIA for negation
* `mem_sub` - FTIA for subtraction
* `mem_mul` - FTIA for multiplication

## Design notes

All operations maintain the invariant `lo ≤ hi`. Domain restrictions for partial
operations (like `inv`) are encoded via separate types or explicit hypotheses.
-/

namespace LeanBound.Core

/-- An interval with rational endpoints -/
structure IntervalRat where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi
  deriving Repr

/-- Default interval [0, 0] for unsupported expression branches -/
instance : Inhabited IntervalRat where
  default := ⟨0, 0, le_refl 0⟩

namespace IntervalRat

/-- The set of reals contained in this interval -/
def toSet (I : IntervalRat) : Set ℝ := Set.Icc (I.lo : ℝ) (I.hi : ℝ)

/-- Membership in an interval -/
instance : Membership ℝ IntervalRat where
  mem I x := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

@[simp]
theorem mem_def (x : ℝ) (I : IntervalRat) : x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) :=
  Iff.rfl

/-- Membership in IntervalRat is the same as membership in Set.Icc -/
theorem mem_iff_mem_Icc (x : ℝ) (I : IntervalRat) : x ∈ I ↔ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ) := by
  simp only [mem_def, Set.mem_Icc]

/-- Universal quantifier over IntervalRat equals universal over Set.Icc -/
theorem forall_mem_iff_forall_Icc {P : ℝ → Prop} (I : IntervalRat) :
    (∀ x ∈ I, P x) ↔ (∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), P x) := by
  constructor <;> intro h x hx <;> apply h <;> simp only [mem_iff_mem_Icc] at hx ⊢ <;> exact hx

/-- Existence in IntervalRat equals existence in Set.Icc -/
theorem exists_mem_iff_exists_Icc {P : ℝ → Prop} (I : IntervalRat) :
    (∃ x ∈ I, P x) ↔ (∃ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), P x) := by
  constructor <;> intro ⟨x, hx, hp⟩ <;> exact ⟨x, by simp only [mem_iff_mem_Icc] at hx ⊢; exact hx, hp⟩

/-- Create an interval from a single rational -/
def singleton (q : ℚ) : IntervalRat := ⟨q, q, le_refl q⟩

theorem mem_singleton (q : ℚ) : (q : ℝ) ∈ singleton q := by
  simp only [mem_def, singleton, le_refl, and_self]

/-- The width of an interval -/
def width (I : IntervalRat) : ℚ := I.hi - I.lo

theorem width_nonneg (I : IntervalRat) : 0 ≤ I.width := by
  simp only [width, sub_nonneg]
  exact I.le

/-- Midpoint of an interval -/
def midpoint (I : IntervalRat) : ℚ := (I.lo + I.hi) / 2

/-- The midpoint of an interval is contained in the interval -/
theorem midpoint_mem (I : IntervalRat) : (I.midpoint : ℝ) ∈ I := by
  simp only [mem_def, midpoint]
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  constructor
  · -- lo ≤ (lo + hi) / 2
    have : (((I.lo + I.hi) / 2 : ℚ) : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    rw [this]
    linarith
  · -- (lo + hi) / 2 ≤ hi
    have : (((I.lo + I.hi) / 2 : ℚ) : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    rw [this]
    linarith

/-! ### Interval addition -/

/-- Add two intervals -/
def add (I J : IntervalRat) : IntervalRat where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  le := by linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add, Rat.cast_add]
  constructor <;> linarith

/-! ### Interval negation -/

/-- Negate an interval -/
def neg (I : IntervalRat) : IntervalRat where
  lo := -I.hi
  hi := -I.lo
  le := by linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg, Rat.cast_neg]
  constructor <;> linarith

/-! ### Interval subtraction -/

/-- Subtract two intervals -/
def sub (I J : IntervalRat) : IntervalRat := add I (neg J)

/-- FTIA for subtraction -/
theorem mem_sub {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x - y ∈ sub I J := by
  simp only [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

/-! ### Interval multiplication -/

/-- Helper: minimum of four rationals -/
private def min4 (a b c d : ℚ) : ℚ := min (min a b) (min c d)

/-- Helper: maximum of four rationals -/
private def max4 (a b c d : ℚ) : ℚ := max (max a b) (max c d)

private theorem min4_le_all (a b c d : ℚ) :
    min4 a b c d ≤ a ∧ min4 a b c d ≤ b ∧ min4 a b c d ≤ c ∧ min4 a b c d ≤ d := by
  simp only [min4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  · exact le_trans (min_le_left _ _) (min_le_right _ _)
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

private theorem all_le_max4 (a b c d : ℚ) :
    a ≤ max4 a b c d ∧ b ≤ max4 a b c d ∧ c ≤ max4 a b c d ∧ d ≤ max4 a b c d := by
  simp only [max4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

private theorem le_min4_iff (x a b c d : ℚ) :
    x ≤ min4 a b c d ↔ x ≤ a ∧ x ≤ b ∧ x ≤ c ∧ x ≤ d := by
  simp only [min4, le_min_iff, and_assoc]

private theorem max4_le_iff (x a b c d : ℚ) :
    max4 a b c d ≤ x ↔ a ≤ x ∧ b ≤ x ∧ c ≤ x ∧ d ≤ x := by
  simp only [max4, max_le_iff, and_assoc]

/-- Multiply two intervals -/
def mul (I J : IntervalRat) : IntervalRat where
  lo := min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  hi := max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  le := by
    simp only [min4, max4]
    exact le_trans (min_le_of_left_le (min_le_left _ _))
                   (le_max_of_le_left (le_max_left _ _))

/-- Helper: for x ∈ [a₁, a₂], x*y lies between endpoint products.
    When y ≥ 0: a₁*y ≤ x*y ≤ a₂*y
    When y ≤ 0: a₂*y ≤ x*y ≤ a₁*y -/
private theorem mul_mem_endpoints_left {x a₁ a₂ y : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) :
    min (a₁ * y) (a₂ * y) ≤ x * y ∧ x * y ≤ max (a₁ * y) (a₂ * y) := by
  by_cases hy : 0 ≤ y
  · -- y ≥ 0: multiplication preserves order, so a₁*y ≤ x*y ≤ a₂*y
    have h1 : a₁ * y ≤ x * y := mul_le_mul_of_nonneg_right ha.1 hy
    have h2 : x * y ≤ a₂ * y := mul_le_mul_of_nonneg_right ha.2 hy
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · -- y < 0: multiplication reverses order, so a₂*y ≤ x*y ≤ a₁*y
    push_neg at hy
    have hy' := le_of_lt hy
    have h1 : a₂ * y ≤ x * y := mul_le_mul_of_nonpos_right ha.2 hy'
    have h2 : x * y ≤ a₁ * y := mul_le_mul_of_nonpos_right ha.1 hy'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Helper: for y ∈ [b₁, b₂], x*y lies between endpoint products.
    When x ≥ 0: x*b₁ ≤ x*y ≤ x*b₂
    When x ≤ 0: x*b₂ ≤ x*y ≤ x*b₁ -/
private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ}
    (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  by_cases hx : 0 ≤ x
  · -- x ≥ 0: multiplication preserves order, so x*b₁ ≤ x*y ≤ x*b₂
    have h1 : x * b₁ ≤ x * y := mul_le_mul_of_nonneg_left hb.1 hx
    have h2 : x * y ≤ x * b₂ := mul_le_mul_of_nonneg_left hb.2 hx
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · -- x < 0: multiplication reverses order, so x*b₂ ≤ x*y ≤ x*b₁
    push_neg at hx
    have hx' := le_of_lt hx
    have h1 : x * b₂ ≤ x * y := mul_le_mul_of_nonpos_left hb.2 hx'
    have h2 : x * y ≤ x * b₁ := mul_le_mul_of_nonpos_left hb.1 hx'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Lower bound: xy ≥ min of corner products -/
private theorem mul_lower_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y := by
  -- First, x*y ≥ min(a₁*y, a₂*y) from mul_mem_endpoints_left
  have h1 := (mul_mem_endpoints_left (y := y) ha).1
  -- Now we need: min of corners ≤ min(a₁*y, a₂*y)
  -- Case split on whether a₁*y ≤ a₂*y
  by_cases hcmp : a₁ * y ≤ a₂ * y
  · -- min(a₁*y, a₂*y) = a₁*y
    rw [min_eq_left hcmp] at h1
    -- Need: min corners ≤ a₁*y
    -- a₁*y is between a₁*b₁ and a₁*b₂, so min(a₁*b₁, a₁*b₂) ≤ a₁*y
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₁ * b₁) (a₁ * b₂) := min_le_left _ _
      _ ≤ a₁ * y := h2
      _ ≤ x * y := h1
  · -- min(a₁*y, a₂*y) = a₂*y
    push_neg at hcmp
    rw [min_eq_right (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₂ * b₁) (a₂ * b₂) := min_le_right _ _
      _ ≤ a₂ * y := h2
      _ ≤ x * y := h1

/-- Upper bound: xy ≤ max of corner products -/
private theorem mul_upper_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).2
  by_cases hcmp : a₁ * y ≤ a₂ * y
  · rw [max_eq_right hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).2
    calc x * y
        ≤ a₂ * y := h1
      _ ≤ max (a₂ * b₁) (a₂ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_right _ _
  · push_neg at hcmp
    rw [max_eq_left (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).2
    calc x * y
        ≤ a₁ * y := h1
      _ ≤ max (a₁ * b₁) (a₁ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_left _ _

/-- Key lemma: product lies in convex hull of corner products.
    For x ∈ [a₁, a₂] and y ∈ [b₁, b₂], we have
    min{a₁b₁, a₁b₂, a₂b₁, a₂b₂} ≤ xy ≤ max{a₁b₁, a₁b₂, a₂b₁, a₂b₂}

    This is a standard result from interval arithmetic: extrema of bilinear
    functions on rectangles occur at corners. -/
private theorem mul_mem_corners {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y ∧
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) :=
  ⟨mul_lower_bound ha hb, mul_upper_bound ha hb⟩

/-- FTIA for multiplication -/
theorem mem_mul {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mul I J := by
  simp only [mem_def] at *
  simp only [mul, min4, max4, Rat.cast_mul, Rat.cast_min, Rat.cast_max]
  exact mul_mem_corners hx hy

/-! ### Interval containing zero check -/

/-- Check if an interval contains zero -/
def containsZero (I : IntervalRat) : Prop := I.lo ≤ 0 ∧ 0 ≤ I.hi

/-- Decidable containsZero -/
instance (I : IntervalRat) : Decidable (containsZero I) :=
  inferInstanceAs (Decidable (I.lo ≤ 0 ∧ 0 ≤ I.hi))

/-- An interval that is guaranteed not to contain zero -/
structure IntervalRatNonzero extends IntervalRat where
  nonzero : ¬containsZero toIntervalRat

/-! ### Interval inversion (for nonzero intervals) -/

/-- Invert an interval that doesn't contain zero -/
def invNonzero (I : IntervalRatNonzero) : IntervalRat :=
  if h : 0 < I.lo then
    -- Positive interval: [1/hi, 1/lo]
    { lo := I.hi⁻¹
      hi := I.lo⁻¹
      le := by
        have hlo : (0 : ℚ) < I.lo := h
        have hhi : (0 : ℚ) < I.hi := lt_of_lt_of_le hlo I.le
        exact inv_anti₀ hlo I.le }
  else
    -- Negative interval: [1/hi, 1/lo] (both negative)
    { lo := I.hi⁻¹
      hi := I.lo⁻¹
      le := by
        have hlo_le : I.lo ≤ 0 := le_of_not_gt h
        have hhi_neg : I.hi < 0 := by
          have hnz := I.nonzero
          simp only [containsZero, not_and, not_le] at hnz
          exact hnz hlo_le
        have hlo_neg : I.lo < 0 := lt_of_le_of_lt I.le hhi_neg
        exact (inv_le_inv_of_neg hhi_neg hlo_neg).mpr I.le }

/-! ### FTIA for inversion -/

theorem mem_invNonzero {x : ℝ} {I : IntervalRatNonzero} (hx : x ∈ I.toIntervalRat) (_hxne : x ≠ 0) :
    x⁻¹ ∈ invNonzero I := by
  simp only [mem_def] at *
  simp only [invNonzero]
  split_ifs with h
  · -- Positive case: 0 < I.lo
    have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast h
    have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
    have hhi_pos : (0 : ℝ) < I.hi := lt_of_lt_of_le hlo_pos (by exact_mod_cast I.le)
    simp only [Rat.cast_inv]
    constructor
    · exact inv_anti₀ hx_pos hx.2
    · exact inv_anti₀ (by exact_mod_cast h) hx.1
  · -- Negative case
    have hlo_le : I.lo ≤ 0 := le_of_not_gt h
    have hhi_neg : I.hi < 0 := by
      have hnz := I.nonzero
      simp only [containsZero, not_and, not_le] at hnz
      exact hnz hlo_le
    have hlo_neg : I.lo < 0 := lt_of_le_of_lt I.le hhi_neg
    have hx_neg : x < 0 := lt_of_le_of_lt hx.2 (by exact_mod_cast hhi_neg)
    have hhi_neg_r : (I.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
    have hlo_neg_r : (I.lo : ℝ) < 0 := by exact_mod_cast hlo_neg
    simp only [Rat.cast_inv]
    constructor
    · exact (inv_le_inv_of_neg hhi_neg_r hx_neg).mpr hx.2
    · exact (inv_le_inv_of_neg hx_neg hlo_neg_r).mpr hx.1

/-! ### Scalar operations -/

/-- Scale an interval by a rational -/
def scale (q : ℚ) (I : IntervalRat) : IntervalRat :=
  if hq : 0 ≤ q then
    { lo := q * I.lo
      hi := q * I.hi
      le := mul_le_mul_of_nonneg_left I.le hq }
  else
    { lo := q * I.hi
      hi := q * I.lo
      le := mul_le_mul_of_nonpos_left I.le (le_of_lt (not_le.mp hq)) }

/-- FTIA for scaling -/
theorem mem_scale {x : ℝ} {I : IntervalRat} (q : ℚ) (hx : x ∈ I) :
    (q : ℝ) * x ∈ scale q I := by
  simp only [mem_def, scale] at *
  split_ifs with hq
  · simp only [Rat.cast_mul]
    constructor
    · exact mul_le_mul_of_nonneg_left hx.1 (Rat.cast_nonneg.mpr hq)
    · exact mul_le_mul_of_nonneg_left hx.2 (Rat.cast_nonneg.mpr hq)
  · simp only [Rat.cast_mul]
    have hq' : (q : ℝ) ≤ 0 := Rat.cast_nonpos.mpr (le_of_lt (not_le.mp hq))
    constructor
    · exact mul_le_mul_of_nonpos_left hx.2 hq'
    · exact mul_le_mul_of_nonpos_left hx.1 hq'

/-! ### Interval splitting -/

/-- Split an interval at its midpoint -/
def bisect (I : IntervalRat) : IntervalRat × IntervalRat :=
  let m := I.midpoint
  (⟨I.lo, m, by show I.lo ≤ (I.lo + I.hi) / 2; linarith [I.le]⟩,
   ⟨m, I.hi, by show (I.lo + I.hi) / 2 ≤ I.hi; linarith [I.le]⟩)

theorem mem_bisect_left {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hm : x ≤ I.midpoint) :
    x ∈ (bisect I).1 := by
  simp only [mem_def, bisect] at *
  exact ⟨hx.1, hm⟩

theorem mem_bisect_right {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hm : I.midpoint ≤ x) :
    x ∈ (bisect I).2 := by
  simp only [mem_def, bisect] at *
  exact ⟨hm, hx.2⟩

/-- Distance from midpoint to lo is half the width -/
theorem midpoint_sub_lo (I : IntervalRat) :
    (I.midpoint : ℝ) - I.lo = (I.hi - I.lo) / 2 := by
  simp only [midpoint]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  ring

/-- Distance from hi to midpoint is half the width -/
theorem hi_sub_midpoint (I : IntervalRat) :
    (I.hi : ℝ) - I.midpoint = (I.hi - I.lo) / 2 := by
  simp only [midpoint]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  ring

/-- Midpoint is at least lo -/
theorem midpoint_ge_lo (I : IntervalRat) : I.lo ≤ I.midpoint := by
  simp only [midpoint]
  have h := I.le
  linarith

/-- Midpoint is at most hi -/
theorem midpoint_le_hi (I : IntervalRat) : I.midpoint ≤ I.hi := by
  simp only [midpoint]
  have h := I.le
  linarith

/-- Midpoint is at least lo (real version) -/
theorem midpoint_ge_lo_real (I : IntervalRat) : (I.lo : ℝ) ≤ I.midpoint := by
  have := midpoint_ge_lo I
  exact_mod_cast this

/-- Midpoint is at most hi (real version) -/
theorem midpoint_le_hi_real (I : IntervalRat) : (I.midpoint : ℝ) ≤ I.hi := by
  have := midpoint_le_hi I
  exact_mod_cast this

/-- Left bisection is a subset of the original interval -/
theorem mem_of_mem_bisect_left {x : ℝ} {I : IntervalRat} (hx : x ∈ (bisect I).1) : x ∈ I := by
  simp only [mem_def, bisect] at *
  constructor
  · exact hx.1
  · exact le_trans hx.2 (Rat.cast_le.mpr (midpoint_le_hi I))

/-- Right bisection is a subset of the original interval -/
theorem mem_of_mem_bisect_right {x : ℝ} {I : IntervalRat} (hx : x ∈ (bisect I).2) : x ∈ I := by
  simp only [mem_def, bisect] at *
  constructor
  · exact le_trans (Rat.cast_le.mpr (midpoint_ge_lo I)) hx.1
  · exact hx.2

/-- Any point in an interval is in one of its bisected halves -/
theorem mem_bisect_or {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x ∈ (bisect I).1 ∨ x ∈ (bisect I).2 := by
  by_cases hm : x ≤ I.midpoint
  · left; exact mem_bisect_left hx hm
  · right; exact mem_bisect_right hx (le_of_lt (not_le.mp hm))

/-- The default interval [0,0] contains only 0 -/
theorem mem_default (x : ℝ) : x ∈ (default : IntervalRat) ↔ x = 0 := by
  simp only [mem_def, Inhabited.default, Rat.cast_zero]
  constructor
  · intro ⟨h1, h2⟩; linarith
  · intro h; subst h; exact ⟨le_refl _, le_refl _⟩

/-! ### Interval intersection -/

/-- Intersect two intervals. Returns none if they don't intersect. -/
def intersect (I J : IntervalRat) : Option IntervalRat :=
  let lo := max I.lo J.lo
  let hi := min I.hi J.hi
  if h : lo ≤ hi then
    some ⟨lo, hi, h⟩
  else
    none

/-- If intersection succeeds, the result contains any point in both intervals -/
theorem mem_intersect {x : ℝ} {I J : IntervalRat} (hI : x ∈ I) (hJ : x ∈ J) :
    ∃ K, intersect I J = some K ∧ x ∈ K := by
  simp only [mem_def] at hI hJ
  -- Work with the max/min at rational level
  have hle : max I.lo J.lo ≤ min I.hi J.hi := by
    have hmax_le : (I.lo : ℝ) ⊔ (J.lo : ℝ) ≤ x := sup_le hI.1 hJ.1
    have hle_min : x ≤ (I.hi : ℝ) ⊓ (J.hi : ℝ) := le_inf hI.2 hJ.2
    have hR : (I.lo : ℝ) ⊔ (J.lo : ℝ) ≤ (I.hi : ℝ) ⊓ (J.hi : ℝ) := le_trans hmax_le hle_min
    -- Convert back: on ℚ, max = sup and min = inf
    calc max I.lo J.lo = I.lo ⊔ J.lo := rfl
      _ ≤ I.hi ⊓ J.hi := by exact_mod_cast hR
      _ = min I.hi J.hi := rfl
  simp only [intersect, hle, ↓reduceDIte]
  refine ⟨⟨max I.lo J.lo, min I.hi J.hi, hle⟩, rfl, ?_⟩
  simp only [mem_def]
  constructor
  · -- Show (max I.lo J.lo : ℝ) ≤ x
    have h1 : max I.lo J.lo ≤ I.lo ∨ max I.lo J.lo = I.lo ∨ max I.lo J.lo = J.lo := by
      simp only [max_def]; split_ifs <;> simp
    cases le_or_gt I.lo J.lo with
    | inl h => simp only [max_eq_right h]; exact hJ.1
    | inr h => simp only [max_eq_left (le_of_lt h)]; exact hI.1
  · -- Show x ≤ (min I.hi J.hi : ℝ)
    cases le_or_gt I.hi J.hi with
    | inl h => simp only [min_eq_left h]; exact hI.2
    | inr h => simp only [min_eq_right (le_of_lt h)]; exact hJ.2

/-- If intersection returns some K, then K ⊆ I -/
theorem intersect_subset_left {I J K : IntervalRat} (h : intersect I J = some K) :
    K.lo ≥ I.lo ∧ K.hi ≤ I.hi := by
  simp only [intersect] at h
  by_cases hle : max I.lo J.lo ≤ min I.hi J.hi
  · simp only [hle, ↓reduceDIte, Option.some.injEq] at h
    subst h
    exact ⟨le_sup_left, inf_le_left⟩
  · simp only [hle, ↓reduceDIte, reduceCtorEq] at h

/-- If intersection returns some K, then K ⊆ J -/
theorem intersect_subset_right {I J K : IntervalRat} (h : intersect I J = some K) :
    K.lo ≥ J.lo ∧ K.hi ≤ J.hi := by
  simp only [intersect] at h
  by_cases hle : max I.lo J.lo ≤ min I.hi J.hi
  · simp only [hle, ↓reduceDIte, Option.some.injEq] at h
    subst h
    exact ⟨le_sup_right, inf_le_right⟩
  · simp only [hle, ↓reduceDIte, reduceCtorEq] at h

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

/-! ### Computable Taylor series helpers -/

/-- Compute n! as a Rational -/
def ratFactorial (n : ℕ) : ℚ := (Nat.factorial n : ℚ)

/-- Compute the integer power of an interval using repeated multiplication.
    This is a simple but correct implementation. -/
def pow (I : IntervalRat) : ℕ → IntervalRat
  | 0 => singleton 1
  | n + 1 => mul I (pow I n)

/-- Compute the absolute value interval: |I| = [0, max(|lo|, |hi|)] if 0 ∈ I,
    or [min(|lo|,|hi|), max(|lo|,|hi|)] otherwise -/
def absInterval (I : IntervalRat) : IntervalRat :=
  if h1 : I.lo ≥ 0 then
    I
  else if h2 : I.hi ≤ 0 then
    neg I
  else
    ⟨0, max (-I.lo) I.hi, by
      apply le_max_of_le_right
      push_neg at h1 h2
      linarith⟩

/-- Maximum absolute value of an interval -/
def maxAbs (I : IntervalRat) : ℚ := max (|I.lo|) (|I.hi|)

/-- Evaluate Taylor series ∑_{i=0}^{n} c_i * x^i at interval I.
    Uses direct interval arithmetic on each term. -/
def evalTaylorSeries (coeffs : List ℚ) (I : IntervalRat) : IntervalRat :=
  coeffs.zipIdx.foldl (fun acc (c, i) =>
    add acc (scale c (pow I i))
  ) (singleton 0)

/-! ### Computable exp via Taylor series -/

/-- Taylor coefficients for exp: 1/i! for i = 0, 1, ..., n -/
def expTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i => 1 / ratFactorial i)

/-- Computable exp remainder bound using rational arithmetic.
    The Lagrange remainder is exp(ξ) * x^{n+1} / (n+1)! where ξ is between 0 and x.
    We use e < 3, so e^r ≤ 3^(⌈r⌉+1) as a conservative bound.

    Returns an interval [-R, R] where R bounds the remainder. -/
def expRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  -- Crude bound: e < 3, so e^r ≤ 3^(ceil(r)+1)
  let expBound := (3 : ℚ) ^ (Nat.ceil r + 1)
  let xBound := r ^ (n + 1)
  let R := expBound * xBound / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply mul_nonneg
        · apply pow_nonneg; norm_num
        · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for exp using Taylor series.

    exp(x) = ∑_{i=0}^{n} x^i/i! + R where |R| ≤ exp(|x|) * |x|^{n+1} / (n+1)!
    We conservatively bound exp(|x|) by 3^(⌈|x|⌉+1).

    This is fully computable using only rational arithmetic. -/
def expComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := expTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := expRemainderBoundComputable I n
  add polyVal remainder

/-! ### Computable sin via Taylor series -/

/-- Taylor coefficients for sin: 0, 1, 0, -1/6, 0, 1/120, ... -/
def sinTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 1 then  -- odd terms only
      ((-1 : ℚ) ^ ((i - 1) / 2)) / ratFactorial i
    else 0)

/-- Computable sin remainder bound.
    Since |sin^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
def sinRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for sin using Taylor series.

    sin(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k+1}/(2k+1)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of sin are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
def sinComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := sinTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := sinRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-! ### Computable cos via Taylor series -/

/-- Taylor coefficients for cos: 1, 0, -1/2, 0, 1/24, 0, ... -/
def cosTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 0 then  -- even terms only
      ((-1 : ℚ) ^ (i / 2)) / ratFactorial i
    else 0)

/-- Computable cos remainder bound.
    Since |cos^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
def cosRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for cos using Taylor series.

    cos(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k}/(2k)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of cos are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
def cosComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := cosTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := cosRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-! ### Computable sinh and cosh via exp -/

/-- Computable interval enclosure for sinh using exp.

    sinh(x) = (exp(x) - exp(-x)) / 2
    Since sinh is strictly monotonic, sinh([a,b]) = [sinh(a), sinh(b)].
    We compute this using the exp Taylor series. -/
def sinhComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  -- Compute exp(I) and exp(-I)
  let expPos := expComputable I n
  let expNeg := expComputable (neg I) n
  -- sinh = (exp(x) - exp(-x)) / 2
  -- For interval [lo, hi]:
  --   sinh(lo) = (exp(lo) - exp(-lo)) / 2
  --   sinh(hi) = (exp(hi) - exp(-hi)) / 2
  -- Since sinh is monotonic, we can compute at endpoints
  let sinhLo := (expPos.lo - expNeg.hi) / 2  -- Lower bound: use min exp(x), max exp(-x)
  let sinhHi := (expPos.hi - expNeg.lo) / 2  -- Upper bound: use max exp(x), min exp(-x)
  -- Interval validity: sinhLo ≤ sinhHi follows from expPos.lo ≤ expPos.hi and expNeg.lo ≤ expNeg.hi
  if h : sinhLo ≤ sinhHi then
    ⟨sinhLo, sinhHi, h⟩
  else
    -- Fallback for edge cases where Taylor approximation gives unexpected order
    ⟨min sinhLo sinhHi, max sinhLo sinhHi, @min_le_max _ _ sinhLo sinhHi⟩

/-- Computable interval enclosure for cosh using exp.

    cosh(x) = (exp(x) + exp(-x)) / 2
    cosh has minimum 1 at x = 0, and is symmetric: cosh(-x) = cosh(x).
    We compute this using the exp Taylor series. -/
def coshComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  -- Compute exp(I) and exp(-I)
  let expPos := expComputable I n
  let expNeg := expComputable (neg I) n
  -- cosh = (exp(x) + exp(-x)) / 2
  -- Lower bound: minimum of cosh over the interval
  -- Upper bound: maximum of cosh over the interval
  let coshLo := (expPos.lo + expNeg.lo) / 2  -- Lower bound
  let coshHi := (expPos.hi + expNeg.hi) / 2  -- Upper bound
  -- Use 1 as lower bound (cosh x ≥ 1 always), take max with computed value
  -- For valid interval, we need lo ≤ hi
  let safeLo := max 1 coshLo
  if h : safeLo ≤ coshHi then
    ⟨safeLo, coshHi, h⟩
  else
    -- Fallback: if Taylor underestimates, use wide bounds
    ⟨1, max 2 coshHi, by
      have h1 : (1 : ℚ) ≤ 2 := by norm_num
      exact le_trans h1 (le_max_left _ _)⟩

/-! ### FTIA for pow -/

/-- FTIA for interval power -/
theorem mem_pow {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    x ^ n ∈ pow I n := by
  induction n with
  | zero =>
    simp only [pow_zero, pow]
    simp only [mem_def, singleton]
    norm_num
  | succ n ih =>
    simp only [pow_succ, pow]
    -- x^(n+1) = x * x^n ∈ mul I (pow I n)
    have h : x * x ^ n ∈ mul I (pow I n) := mem_mul hx ih
    convert h using 1
    ring

/-! ### Helper lemmas for Taylor series membership -/

/-- Any x in I has |x| ≤ maxAbs I -/
theorem abs_le_maxAbs {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : |x| ≤ maxAbs I := by
  simp only [mem_def, maxAbs] at *
  have hlo : -(max |I.lo| |I.hi|) ≤ I.lo := by
    calc -(max |I.lo| |I.hi|) ≤ -|I.lo| := neg_le_neg (le_max_left _ _)
      _ ≤ I.lo := neg_abs_le _
  have hhi : I.hi ≤ max |I.lo| |I.hi| := le_trans (le_abs_self _) (le_max_right _ _)
  rw [abs_le]
  constructor
  · calc (-(max |I.lo| |I.hi| : ℚ) : ℝ) ≤ I.lo := by exact_mod_cast hlo
      _ ≤ x := hx.1
  · calc x ≤ I.hi := hx.2
      _ ≤ max |I.lo| |I.hi| := by exact_mod_cast hhi

/-- If |x| ≤ R for nonnegative R, then x ∈ [-R, R].
    This is the key micro-lemma for embedding Lagrange remainder bounds into intervals. -/
theorem abs_le_mem_symmetric_interval {x : ℝ} {R : ℚ} (hR : 0 ≤ R) (h : |x| ≤ R) :
    x ∈ (⟨-R, R, by linarith⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  constructor
  · have := neg_abs_le x; linarith
  · exact le_trans (le_abs_self x) h

/-- Domain setup for Taylor theorem: if |x| ≤ r for nonnegative r,
    then x ∈ [-r, r] as an Icc with the required inequalities. -/
theorem domain_from_abs_bound {x : ℝ} {r : ℚ} (_hr : 0 ≤ r) (habs : |x| ≤ r) :
    x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) := by
  simp only [Set.mem_Icc, Rat.cast_neg]
  exact abs_le.mp habs

/-- Combined domain setup from interval membership. -/
theorem domain_from_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    let r := maxAbs I
    (0 : ℝ) ≤ r ∧ |x| ≤ r ∧ x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) ∧
    ((-r : ℚ) : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ (r : ℚ) ∧ ((-r : ℚ) : ℝ) ≤ r := by
  have hr_nonneg : 0 ≤ maxAbs I := le_max_of_le_left (abs_nonneg I.lo)
  have habs_x := abs_le_maxAbs hx
  have hr_nonneg_real : (0 : ℝ) ≤ maxAbs I := by exact_mod_cast hr_nonneg
  have hdom := domain_from_abs_bound hr_nonneg habs_x
  refine ⟨hr_nonneg_real, habs_x, hdom, ?_, hr_nonneg_real, ?_⟩
  · simp only [Rat.cast_neg]; linarith
  · simp only [Rat.cast_neg]; linarith

/-- Convert an absolute value bound |v| ≤ R to interval membership v ∈ [-R, R].
    This is the key micro-lemma for the final step of Taylor remainder bounds. -/
theorem remainder_to_interval {v : ℝ} {R : ℚ} (hbound : |v| ≤ R) :
    v ∈ (⟨-R, R, by
      have h1 : 0 ≤ |v| := abs_nonneg v
      have h2 : (0 : ℝ) ≤ (R : ℚ) := le_trans h1 hbound
      linarith [Rat.cast_nonneg.mp h2]⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  exact abs_le.mp hbound

/-- Key lemma: exp(ξ) ≤ 3^(⌈r⌉+1) for |ξ| ≤ r -/
theorem exp_bound_by_pow3 {r : ℚ} (_hr : 0 ≤ r) {ξ : ℝ} (hξ : |ξ| ≤ r) :
    Real.exp ξ ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
  -- e < 3, using Real.exp_one_lt_d9 which gives exp(1) < 2.7182818286
  have h3 : Real.exp 1 < 3 := by
    have h := Real.exp_one_lt_d9  -- exp(1) < 2.7182818286
    have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
    exact lt_trans h h2
  have hceil : (r : ℝ) ≤ Nat.ceil r := by
    have h : r ≤ (Nat.ceil r : ℚ) := Nat.le_ceil r
    exact_mod_cast h
  calc Real.exp ξ ≤ Real.exp |ξ| := Real.exp_le_exp.mpr (le_abs_self ξ)
    _ ≤ Real.exp r := Real.exp_le_exp.mpr hξ
    _ ≤ Real.exp (Nat.ceil r) := Real.exp_le_exp.mpr hceil
    _ = Real.exp 1 ^ (Nat.ceil r) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ 3 ^ (Nat.ceil r) := by
        rcases Nat.eq_zero_or_pos (Nat.ceil r) with hr0 | hrpos
        · simp [hr0]
        · exact le_of_lt (pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (Nat.pos_iff_ne_zero.mp hrpos))
    _ ≤ 3 ^ (Nat.ceil r + 1) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ _)

/-! ### Coefficient matching lemmas -/

/-- For exp, all iterated derivatives at 0 equal 1. -/
lemma iteratedDeriv_exp_zero (i : ℕ) : iteratedDeriv i Real.exp 0 = 1 := by
  simp [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-- Auxiliary lemma: foldl over zipIdx produces valid interval bounds.
    If y ∈ acc and x ∈ I, then
    y + ∑_{(c,i) ∈ rest} c * x^i ∈ rest.foldl (fun acc (c, i) => add acc (scale c (pow I i))) acc -/
private lemma mem_foldl_zipIdx_aux {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (rest : List (ℚ × ℕ)) (acc : IntervalRat) (y : ℝ) (hy : y ∈ acc) :
    y + (rest.map (fun (c, i) => (c : ℝ) * x ^ i)).sum ∈
      rest.foldl (fun acc (c, i) => add acc (scale c (pow I i))) acc := by
  induction rest generalizing acc y with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    exact hy
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    -- hd = (c, i), need to show y + (c * x^i + rest_sum) ∈ ...
    have hterm : (hd.1 : ℝ) * x ^ hd.2 ∈ scale hd.1 (pow I hd.2) :=
      mem_scale hd.1 (mem_pow hx hd.2)
    have hadd : y + (hd.1 : ℝ) * x ^ hd.2 ∈ add acc (scale hd.1 (pow I hd.2)) :=
      mem_add hy hterm
    have heq : y + ((hd.1 : ℝ) * x ^ hd.2 + (tl.map (fun (c, i) => (c : ℝ) * x ^ i)).sum) =
        (y + (hd.1 : ℝ) * x ^ hd.2) + (tl.map (fun (c, i) => (c : ℝ) * x ^ i)).sum := by ring
    rw [heq]
    exact ih (add acc (scale hd.1 (pow I hd.2))) (y + (hd.1 : ℝ) * x ^ hd.2) hadd

/-- General FTIA for evalTaylorSeries: if coeffs has length n+1, then
    ∑_{i=0}^{n} coeffs[i] * x^i ∈ evalTaylorSeries coeffs I for x ∈ I. -/
theorem mem_evalTaylorSeries {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (coeffs : List ℚ) :
    (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum ∈ evalTaylorSeries coeffs I := by
  simp only [evalTaylorSeries]
  have h0 : (0 : ℝ) ∈ singleton 0 := by
    simp only [mem_def, singleton, Rat.cast_zero, le_refl, and_self]
  have heq : (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum =
      0 + (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum := by ring
  rw [heq]
  exact mem_foldl_zipIdx_aux hx coeffs.zipIdx (singleton 0) 0 h0

/-- Helper: (List.range n).map f).sum = ∑ i ∈ Finset.range n, f i -/
private lemma list_map_sum_eq_finset_sum {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ]
    rw [ih, add_comm]

/-- Helper: zipIdx of List.range just pairs each element with its index (which is itself) -/
private lemma zipIdx_range_map {α : Type*} (f : ℕ → ℕ → α) (n : ℕ) :
    (List.range n).zipIdx.map (fun p => f p.1 p.2) = (List.range n).map (fun i => f i i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.zipIdx_append, List.map_append, List.length_range]
    rw [ih]
    simp only [List.zipIdx_singleton, List.map_singleton, zero_add]

/-- The exp Taylor polynomial value matches our evalTaylorSeries.
    The proof shows that our list-based polynomial evaluation produces the same
    sum as the Finset.sum form used in Mathlib's Taylor theorem. -/
theorem mem_evalTaylorSeries_exp {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i ∈
      evalTaylorSeries (expTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (expTaylorCoeffs n)
  convert hmem using 1
  simp only [expTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (1 / i.factorial : ℝ) * x ^ i) (n + 1)]
  -- The two list maps are equal: both compute [1/0! * x^0, 1/1! * x^1, ...]
  -- LHS: (List.range (n+1)).map (fun i => 1/i! * x^i)
  -- RHS: zipIdx.map with Prod.map composition
  -- For List.range, zipIdx gives [(0,0), (1,1), ...], so they match
  congr 1
  symm
  -- The RHS has type (ℚ × ℕ) from Prod.map applied to zipIdx pairs
  -- Step 1: Simplify the composition
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map (fun i => (1 : ℚ) / i.factorial) id) =
      (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / p.1.factorial : ℝ) * x ^ p.2) := by
    apply List.map_congr_left
    intro ⟨a, b⟩ _
    simp only [Function.comp_apply, Prod.map_apply, id_eq, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  -- Step 2: Use zipIdx_range_map to eliminate zipIdx
  have h2 : (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / p.1.factorial : ℝ) * x ^ p.2) =
      (List.range (n + 1)).map (fun i => ((1 : ℚ) / i.factorial : ℝ) * x ^ i) := by
    convert zipIdx_range_map (fun a b => ((1 : ℚ) / a.factorial : ℝ) * x ^ b) (n + 1) using 2
  -- Step 3: Simplify the casts
  have h3 : (List.range (n + 1)).map (fun i => ((1 : ℚ) / i.factorial : ℝ) * x ^ i) =
      (List.range (n + 1)).map (fun i => (1 / i.factorial : ℝ) * x ^ i) := by
    apply List.map_congr_left
    intro i _
    simp only [Rat.cast_one]
  rw [h1, h2, h3]

/-- The iterated derivative of sin is sin, cos, -sin, -cos in a cycle of 4. -/
private lemma iteratedDeriv_sin (n : ℕ) : iteratedDeriv n Real.sin =
    if n % 4 = 0 then Real.sin
    else if n % 4 = 1 then Real.cos
    else if n % 4 = 2 then fun x => -Real.sin x
    else fun x => -Real.cos x := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv sin = cos
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte, Real.deriv_sin]; norm_num
    · -- n % 4 = 1: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of sin at 0 follows the pattern 0, 1, 0, -1, 0, 1, 0, -1, ... -/
private lemma iteratedDeriv_sin_zero (i : ℕ) : iteratedDeriv i Real.sin 0 =
    if i % 4 = 0 then 0
    else if i % 4 = 1 then 1
    else if i % 4 = 2 then 0
    else -1 := by
  rw [iteratedDeriv_sin]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.sin_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h3]; norm_num [Real.cos_zero]

/-- The sin Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i sin 0 = 0, 1, 0, -1, 0, 1, ... matches sinTaylorCoeffs. -/
theorem mem_evalTaylorSeries_sin {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (sinTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (sinTaylorCoeffs n)
  convert hmem using 1
  simp only [sinTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert zipIdx_range_map
      (fun a b => ((if a % 2 = 1 then (-1 : ℚ) ^ ((a - 1) / 2) / a.factorial else 0 : ℚ) : ℝ) * x ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  -- Need: (iteratedDeriv i sin 0 / i!) * x^i = ((sinCoeff i) : ℝ) * x^i
  -- where sinCoeff i = if i % 2 = 1 then (-1)^((i-1)/2) / i! else 0
  congr 1
  -- Show iteratedDeriv i sin 0 / i! = sinCoeff i (as ℝ)
  rw [iteratedDeriv_sin_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h0, ↓reduceIte, zero_div, if_neg hi_ne, Rat.cast_zero]
  · -- i % 4 = 1: i is odd, iteratedDeriv = 1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h1, ↓reduceIte, if_pos hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    congr 1
    have heven : Even ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    exact heven.neg_one_pow
  · -- i % 4 = 2: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h2, ↓reduceIte, if_neg hi_ne]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = -1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h3, if_pos hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num

/-- The iterated derivative of cos is cos, -sin, -cos, sin in a cycle of 4. -/
private lemma iteratedDeriv_cos (n : ℕ) : iteratedDeriv n Real.cos =
    if n % 4 = 0 then Real.cos
    else if n % 4 = 1 then fun x => -Real.sin x
    else if n % 4 = 2 then fun x => -Real.cos x
    else Real.sin := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 1: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv sin = cos
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of cos at 0 follows the pattern 1, 0, -1, 0, 1, 0, ... -/
private lemma iteratedDeriv_cos_zero (i : ℕ) : iteratedDeriv i Real.cos 0 =
    if i % 4 = 0 then 1
    else if i % 4 = 1 then 0
    else if i % 4 = 2 then -1
    else 0 := by
  rw [iteratedDeriv_cos]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.cos_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h3]; norm_num [Real.sin_zero]

/-- The cos Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i cos 0 = 1, 0, -1, 0, 1, 0, ... matches cosTaylorCoeffs. -/
theorem mem_evalTaylorSeries_cos {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (cosTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (cosTaylorCoeffs n)
  convert hmem using 1
  simp only [cosTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert zipIdx_range_map
      (fun a b => ((if a % 2 = 0 then (-1 : ℚ) ^ (a / 2) / a.factorial else 0 : ℚ) : ℝ) * x ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  congr 1
  -- Show iteratedDeriv i cos 0 / i! = cosCoeff i (as ℝ)
  rw [iteratedDeriv_cos_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h0, ↓reduceIte, one_div, if_pos hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have heven : Even (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [heven.neg_one_pow]
    ring
  · -- i % 4 = 1: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h1, ↓reduceIte, if_neg hi_ne]
    norm_num
  · -- i % 4 = 2: i is even, iteratedDeriv = -1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h2, if_pos hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h3, if_neg hi_ne]
    norm_num

/-! ### Taylor remainder micro-lemmas -/

/-- Unified Taylor remainder bound for exp: given x ∈ I with r = maxAbs I,
    the Taylor remainder |exp x - poly(x)| ≤ 3^(⌈r⌉+1) * r^(n+1) / (n+1)!.
    This encapsulates the domain setup and remainder calculation. -/
theorem exp_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
    ∈ expRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := ((3 : ℚ) ^ (Nat.ceil r + 1) * r ^ (n + 1) / ratFactorial (n + 1))

  -- Apply Taylor theorem
  have hexp_smooth : ContDiff ℝ (n + 1) Real.exp := Real.contDiff_exp.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.exp y‖ ≤ Real.exp r := by
    intro y hy
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
    exact Real.exp_le_exp.mpr hy.2
  have hTaylor := taylor_remainder_bound hab h0a h0b hexp_smooth hderiv_bound
    (Real.exp_pos (r : ℚ)).le x hdom

  -- Compute remainder bound
  have hr_nonneg_rat : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
  have hexp_r_bound : Real.exp (r : ℚ) ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
    apply exp_bound_by_pow3 hr_nonneg_rat
    rw [abs_of_nonneg hr_nonneg]
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : Real.exp (r : ℚ) * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero]
    calc Real.exp (r : ℚ) * |x| ^ (n + 1) / (n + 1).factorial
        ≤ (3 : ℝ) ^ (Nat.ceil r + 1) * (r : ℝ) ^ (n + 1) / (n + 1).factorial := by
          apply div_le_div_of_nonneg_right _ hfact_pos.le
          apply mul_le_mul hexp_r_bound hx_pow_bound (pow_nonneg (abs_nonneg x) _)
          apply pow_nonneg; norm_num
      _ = (R : ℝ) := by
          simp only [R, ratFactorial, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
            Rat.cast_natCast, Rat.cast_ofNat]

  -- Convert to interval membership
  simp only [expRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.exp x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for sin: given x ∈ I with r = maxAbs I,
    the Taylor remainder |sin x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |sin^(k)(x)| ≤ 1 for all k, x. -/
theorem sin_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
    ∈ sinRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))

  -- Apply Taylor theorem with M = 1
  have hsin_smooth : ContDiff ℝ (n + 1) Real.sin := Real.contDiff_sin.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.sin y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).1
  have hTaylor := taylor_remainder_bound hab h0a h0b hsin_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom

  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

  -- Convert to interval membership
  simp only [sinRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.sin x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for cos: given x ∈ I with r = maxAbs I,
    the Taylor remainder |cos x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |cos^(k)(x)| ≤ 1 for all k, x. -/
theorem cos_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
    ∈ cosRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))

  -- Apply Taylor theorem with M = 1
  have hcos_smooth : ContDiff ℝ (n + 1) Real.cos := Real.contDiff_cos.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.cos y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).2
  have hTaylor := taylor_remainder_bound hab h0a h0b hcos_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom

  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

  -- Convert to interval membership
  simp only [cosRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.cos x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-! ### FTIA for computable functions -/

/-- FTIA for expComputable: Real.exp x ∈ expComputable I n for any x ∈ I.

    This theorem establishes that the computable Taylor series evaluation
    correctly bounds the real exponential function. The proof uses the
    Taylor remainder micro-lemma which encapsulates the Lagrange form. -/
theorem mem_expComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x ∈ expComputable I n := by
  simp only [expComputable]
  -- Strategy: exp x = poly(x) + remainder, with both in their respective intervals

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (expTaylorCoeffs n) I := by
    have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i =
        ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i := by
      apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
    rw [hsum_eq]; exact mem_evalTaylorSeries_exp hx n

  -- Remainder part ∈ expRemainderBoundComputable (via micro-lemma)
  have hrem_mem := exp_taylor_remainder_in_interval hx n

  -- Combine: exp x = poly + rem
  have heq : Real.exp x = (∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) +
      (Real.exp x - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) := by ring
  rw [heq]; exact mem_add hpoly_mem hrem_mem

/-- FTIA for sinComputable: Real.sin x ∈ sinComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound sin ∈ [-1, 1]. -/
theorem mem_sinComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x ∈ sinComputable I n := by
  simp only [sinComputable]
  -- Strategy: sin x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (sinTaylorCoeffs n) I := mem_evalTaylorSeries_sin hx n

  -- Remainder part ∈ sinRemainderBoundComputable (via micro-lemma)
  have hrem_mem := sin_taylor_remainder_in_interval hx n

  -- Raw interval membership: sin x ∈ poly + remainder
  have hraw_mem : Real.sin x ∈ add (evalTaylorSeries (sinTaylorCoeffs n) I)
      (sinRemainderBoundComputable I n) := by
    have heq : Real.sin x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) +
        (Real.sin x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem

  -- Global bound: sin x ∈ [-1, 1]
  have hglobal_mem : Real.sin x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_sin x
    · simp only [Rat.cast_one]; exact Real.sin_le_one x

  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

/-- FTIA for cosComputable: Real.cos x ∈ cosComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound cos ∈ [-1, 1]. -/
theorem mem_cosComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x ∈ cosComputable I n := by
  simp only [cosComputable]
  -- Strategy: cos x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (cosTaylorCoeffs n) I := mem_evalTaylorSeries_cos hx n

  -- Remainder part ∈ cosRemainderBoundComputable (via micro-lemma)
  have hrem_mem := cos_taylor_remainder_in_interval hx n

  -- Raw interval membership: cos x ∈ poly + remainder
  have hraw_mem : Real.cos x ∈ add (evalTaylorSeries (cosTaylorCoeffs n) I)
      (cosRemainderBoundComputable I n) := by
    have heq : Real.cos x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) +
        (Real.cos x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem

  -- Global bound: cos x ∈ [-1, 1]
  have hglobal_mem : Real.cos x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_cos x
    · simp only [Rat.cast_one]; exact Real.cos_le_one x

  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

end IntervalRat

end LeanBound.Core
