/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Affine.Basic

/-!
# Affine Arithmetic: Non-Linear Operations

This file extends Affine Arithmetic with division and square root.

## Key Insight

For non-linear functions `f(x)`, we use the **Chebyshev linearization**:
1. Find the best linear approximation `L(x) = α·x + β` over the interval
2. Compute the maximum approximation error `δ = max|f(x) - L(x)|`
3. Result: `α·â + β + [-δ, δ]` where `â` is the affine input

This is sound because for any `x ∈ [lo, hi]`:
  `f(x) ∈ L(x) + [-δ, δ] = α·x + β + [-δ, δ]`

## Main definitions

* `AffineForm.inv` - Interval inversion with linearization
* `AffineForm.sqrt` - Square root using Chebyshev approximation
* `AffineForm.div` - Division via multiplication by inverse
-/

namespace LeanCert.Engine.Affine

open LeanCert.Core

namespace AffineForm

/-! ## Inversion (1/x) -/

/-- Conservative inversion for affine forms.

    For positive intervals [lo, hi]:
    - Linear approx: L(x) = -1/(lo·hi)·x + (lo+hi)/(lo·hi)
    - Max error at endpoints and midpoint

    We use a simpler approach: convert to interval, invert, convert back.
    This loses correlation but is always sound.
-/
def inv (a : AffineForm) : AffineForm :=
  let I := a.toInterval
  -- Only safe if interval doesn't contain zero
  if h : 0 < I.lo then
    -- Positive interval: 1/[lo,hi] = [1/hi, 1/lo]
    let lo_inv := 1 / I.hi
    let hi_inv := 1 / I.lo
    let mid := (lo_inv + hi_inv) / 2
    let rad := (hi_inv - lo_inv) / 2
    -- Use error term (loses correlation, but allows soundness proof)
    { c0 := mid
      coeffs := []
      r := rad
      r_nonneg := by
        -- rad = (1/I.lo - 1/I.hi) / 2 ≥ 0 since I.lo ≤ I.hi and both positive
        have hlo_pos := h
        have hle := I.le
        have hhi_pos : 0 < I.hi := by linarith
        have h1 : 1 / I.hi ≤ 1 / I.lo := one_div_le_one_div_of_le hlo_pos hle
        -- Unfold to help linarith
        show 0 ≤ (1 / I.lo - 1 / I.hi) / 2
        linarith }
  else if h : I.hi < 0 then
    -- Negative interval: 1/[lo,hi] = [1/hi, 1/lo] (since 1/x is decreasing for negative x)
    -- For lo ≤ hi < 0: 1/hi ≤ 1/lo (both are negative, |lo| ≥ |hi| means 1/|lo| ≤ 1/|hi|)
    let lo_inv := 1 / I.hi  -- lower bound of inverse
    let hi_inv := 1 / I.lo  -- upper bound of inverse
    let mid := (lo_inv + hi_inv) / 2
    let rad := (hi_inv - lo_inv) / 2
    { c0 := mid
      coeffs := []
      r := rad
      r_nonneg := by
        -- rad = (1/I.lo - 1/I.hi) / 2 ≥ 0 since for negative numbers 1/lo ≥ 1/hi
        have hhi_neg := h
        have hle := I.le
        have hlo_neg : I.lo < 0 := by linarith
        -- For lo ≤ hi < 0: 1/hi ≤ 1/lo
        have h1 : 1 / I.hi ≤ 1 / I.lo := one_div_le_one_div_of_neg_of_le hhi_neg hle
        -- Unfold to help linarith
        show 0 ≤ (1 / I.lo - 1 / I.hi) / 2
        linarith }
  else
    -- Contains zero - return wide interval
    { c0 := 0
      coeffs := []
      r := 10^30
      r_nonneg := by norm_num }

/-- Chebyshev linearization for 1/x on [lo, hi] with 0 < lo.

    The optimal linear approximation minimizes max error.
    For 1/x, the Chebyshev approximation is:
      L(x) = -1/(lo·hi)·x + (lo+hi)/(lo·hi)
    with error bounded by (√hi - √lo)² / (2·lo·hi)
-/
def invChebyshev (a : AffineForm) (_hpos : 0 < a.toInterval.lo) : AffineForm :=
  let I := a.toInterval
  let lo := I.lo
  let hi := I.hi
  -- Chebyshev coefficients for 1/x on [lo, hi]
  -- α = -1/(lo·hi), β = (lo+hi)/(lo·hi)
  let α := -1 / (lo * hi)
  let β := (lo + hi) / (lo * hi)
  -- Max error δ = (√hi - √lo)² / (2·lo·hi) ≈ (hi-lo)²/(8·lo²·hi)
  -- We use a conservative bound: (hi-lo)/(2·lo·hi) · (hi-lo)/(2·lo)
  let width := hi - lo
  let δ := width * width / (4 * lo * hi)

  -- Apply linearization: α·a + β + δ
  let scaled := scale α a
  let shifted := add scaled (const β)
  { c0 := shifted.c0
    coeffs := shifted.coeffs
    r := shifted.r + |δ|
    r_nonneg := by
      have h1 := shifted.r_nonneg
      have h2 := abs_nonneg δ
      linarith }

/-! ## Square Root -/

/-- Square root using Chebyshev linearization.

    For √x on [lo, hi] with 0 ≤ lo:
    - Optimal linear: L(x) = x/(√lo + √hi) + √(lo·hi)/(√lo + √hi)
    - Error: (√hi - √lo)² / 4

    Simplified approach: use interval sqrt, convert back.
-/
def sqrt (a : AffineForm) : AffineForm :=
  let I := a.toInterval
  if h : 0 ≤ I.lo then
    -- Non-negative interval
    let sqrt_lo := IntervalRat.sqrtInterval ⟨I.lo, I.lo, le_refl _⟩
    let sqrt_hi := IntervalRat.sqrtInterval ⟨I.hi, I.hi, le_refl _⟩
    -- √[lo,hi] ⊆ [√lo_lower, √hi_upper]
    let lo_new := sqrt_lo.lo
    let hi_new := sqrt_hi.hi
    let mid := (lo_new + hi_new) / 2
    let rad := (hi_new - lo_new) / 2
    -- Use error term for soundness proof compatibility
    { c0 := mid
      coeffs := []
      r := |rad|  -- Use abs to ensure non-negativity
      r_nonneg := abs_nonneg _ }
  else
    -- Negative values - return conservative bounds based on I.hi
    -- sqrt v ≤ max I.hi 1 for any v ∈ I with v ≥ 0
    let bound := max I.hi 1
    { c0 := 0, coeffs := [], r := bound, r_nonneg := le_trans (by norm_num : (0:ℚ) ≤ 1) (le_max_right _ _) }

/-- Chebyshev linearization for √x on [lo, hi].

    Optimal approximation: L(x) = x/(2·√m) + √m/2
    where m = (lo + hi)/2 is the midpoint.
    Error ≤ (√hi - √lo)²/4
-/
def sqrtChebyshev (a : AffineForm) (_hpos : 0 < a.toInterval.lo) : AffineForm :=
  let I := a.toInterval
  let lo := I.lo
  let hi := I.hi

  -- Use midpoint linearization (simpler than optimal Chebyshev)
  -- √x ≈ √m + (x-m)/(2·√m) = x/(2·√m) + √m/2
  let m := (lo + hi) / 2
  -- Conservative: √m ≈ (√lo + √hi)/2, so 1/(2√m) ≈ 1/(√lo + √hi)
  let sqrt_lo_I := IntervalRat.sqrtInterval ⟨lo, lo, le_refl _⟩
  let sqrt_hi_I := IntervalRat.sqrtInterval ⟨hi, hi, le_refl _⟩
  let sqrt_lo := sqrt_lo_I.lo  -- Lower bound on √lo
  let sqrt_hi := sqrt_hi_I.hi  -- Upper bound on √hi
  let sum_sqrt := sqrt_lo + sqrt_hi

  -- Avoid division by zero
  if hsum : sum_sqrt > 0 then
    let α := 1 / sum_sqrt  -- Coefficient for x
    let sqrt_m_I := IntervalRat.sqrtInterval ⟨m, m, le_refl _⟩
    let β := sqrt_m_I.lo  -- Lower bound on √m

    -- Error bound: (√hi - √lo)² / 4
    let diff := sqrt_hi - sqrt_lo
    let δ := diff * diff / 4

    let scaled := scale α a
    let shifted := add scaled (const β)
    { c0 := shifted.c0
      coeffs := shifted.coeffs
      r := shifted.r + |δ|
      r_nonneg := by linarith [shifted.r_nonneg, abs_nonneg δ] }
  else
    sqrt a  -- Fall back to simple version

/-! ## Division -/

/-- Division: a / b = a · (1/b) -/
def div (a b : AffineForm) : AffineForm :=
  mul a (inv b)

/-- Division with Chebyshev linearization for the inverse -/
def divChebyshev (a b : AffineForm) (hpos : 0 < b.toInterval.lo) : AffineForm :=
  mul a (invChebyshev b hpos)

/-! ## Power Operations -/

/-- Natural number power -/
def pow (a : AffineForm) : Nat → AffineForm
  | 0 => const 1
  | 1 => a
  | n + 2 =>
    let half := pow a ((n + 2) / 2)
    let sq_half := mul half half
    if (n + 2) % 2 == 0 then sq_half
    else mul sq_half a

/-! ## Soundness (Placeholder) -/

/-- Inversion is sound when interval is positive -/
theorem mem_inv {a : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps)
    (hlen : eps.length = a.coeffs.length)
    (hmem : mem_affine a eps v)
    (_hv_pos : 0 < v)
    (hI_pos : 0 < a.toInterval.lo) :
    mem_affine (inv a) eps (1 / v) := by
  -- First, get v ∈ a.toInterval
  have hv_in_I := mem_toInterval hvalid hlen hmem
  simp only [IntervalRat.mem_def] at hv_in_I

  -- Set up the interval bounds
  let I := a.toInterval
  have hI_le := I.le
  have hhi_pos : 0 < I.hi := by linarith
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hI_pos

  -- v ∈ [I.lo, I.hi] with both positive
  have hv_lo : (I.lo : ℝ) ≤ v := hv_in_I.1
  have hv_hi : v ≤ (I.hi : ℝ) := hv_in_I.2
  have hv_pos' : 0 < v := by linarith

  -- For inv a with positive interval
  simp only [inv, dif_pos hI_pos]

  -- The result has c0 = (1/I.hi + 1/I.lo)/2, r = (1/I.lo - 1/I.hi)/2, coeffs = []
  -- So evalLinear = c0 and we need |1/v - c0| ≤ r

  -- Since 1/v ∈ [1/I.hi, 1/I.lo] and [c0-r, c0+r] = [1/I.hi, 1/I.lo], the result follows
  simp only [mem_affine, evalLinear, linearSum, List.zipWith, List.sum_nil, add_zero]

  -- Let mid = (1/I.hi + 1/I.lo)/2 and rad = (1/I.lo - 1/I.hi)/2
  use 1/v - ((1/I.hi + 1/I.lo)/2 : ℚ)
  constructor
  · -- |1/v - mid| ≤ rad
    -- This follows from 1/I.hi ≤ 1/v ≤ 1/I.lo
    have h1 : (1 : ℝ) / I.hi ≤ 1 / v := by
      apply one_div_le_one_div_of_le hv_pos' hv_hi
    have h2 : (1 : ℝ) / v ≤ 1 / I.lo := by
      apply one_div_le_one_div_of_le hlo_pos hv_lo

    -- Convert rational expressions to their real equivalents
    have hhi_ne : I.hi ≠ 0 := by linarith
    have hlo_ne : I.lo ≠ 0 := by linarith
    have hmid : ((1/I.hi + 1/I.lo)/2 : ℚ) = (((1 : ℝ)/I.hi + 1/I.lo)/2 : ℝ) := by
      push_cast
      ring
    have hrad : (((1/I.lo - 1/I.hi)/2 : ℚ) : ℝ) = ((1 : ℝ)/I.lo - 1/I.hi)/2 := by
      push_cast
      ring

    rw [abs_le, hmid, hrad]
    constructor
    · -- Lower bound: -((1/I.lo - 1/I.hi)/2) ≤ 1/v - (1/I.hi + 1/I.lo)/2
      -- Equivalently: (1/I.hi + 1/I.lo)/2 - (1/I.lo - 1/I.hi)/2 ≤ 1/v
      -- i.e., 1/I.hi ≤ 1/v
      have key : (1 : ℝ)/I.hi = ((1/I.hi + 1/I.lo)/2 : ℝ) - ((1/I.lo - 1/I.hi)/2 : ℝ) := by ring
      linarith
    · -- Upper bound: 1/v - (1/I.hi + 1/I.lo)/2 ≤ (1/I.lo - 1/I.hi)/2
      -- Equivalently: 1/v ≤ (1/I.hi + 1/I.lo)/2 + (1/I.lo - 1/I.hi)/2
      -- i.e., 1/v ≤ 1/I.lo
      have key : (1 : ℝ)/I.lo = ((1/I.hi + 1/I.lo)/2 : ℝ) + ((1/I.lo - 1/I.hi)/2 : ℝ) := by ring
      linarith
  · ring

/-- Square root is sound for non-negative inputs -/
theorem mem_sqrt {a : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps)
    (hlen : eps.length = a.coeffs.length)
    (hmem : mem_affine a eps v)
    (hv_nonneg : 0 ≤ v) :
    mem_affine (sqrt a) eps (Real.sqrt v) := by
  -- Get v ∈ a.toInterval
  have hv_in_I := mem_toInterval hvalid hlen hmem

  -- Set up the interval
  let I := a.toInterval

  -- Get Real.sqrt v ∈ sqrtInterval I = [0, max I.hi 1]
  have hsqrt_in := IntervalRat.mem_sqrtInterval hv_in_I hv_nonneg
  simp only [IntervalRat.sqrtInterval, IntervalRat.mem_def, Rat.cast_zero] at hsqrt_in
  have hsqrt_lo : 0 ≤ Real.sqrt v := hsqrt_in.1
  have hsqrt_hi : Real.sqrt v ≤ max (I.hi : ℝ) 1 := by
    have := hsqrt_in.2
    simp only [Rat.cast_max, Rat.cast_one] at this
    exact this

  -- Case split on whether I.lo ≥ 0
  simp only [sqrt, IntervalRat.sqrtInterval, mem_affine, evalLinear, linearSum]
  split
  · -- Non-negative interval case
    rename_i h
    simp only [List.zipWith, List.sum_nil, add_zero]

    -- Key simplifications
    have hmid : ((0 + max I.hi 1) / 2 : ℚ) = max I.hi 1 / 2 := by ring
    have hrad : ((max I.hi 1 - 0) / 2 : ℚ) = max I.hi 1 / 2 := by ring
    have hrad_nonneg : 0 ≤ (max I.hi 1 - 0) / 2 := by
      have h1 : (1 : ℚ) ≤ max I.hi 1 := le_max_right I.hi 1; linarith
    have habs_rad : |((max I.hi 1 - 0) / 2 : ℚ)| = (max I.hi 1 - 0) / 2 :=
      abs_of_nonneg hrad_nonneg

    use Real.sqrt v - ((0 + max I.hi 1) / 2 : ℚ)
    constructor
    · -- |sqrt v - mid| ≤ |rad|
      rw [habs_rad]
      have hmid_real : (((0 + max I.hi 1) / 2 : ℚ) : ℝ) = max (I.hi : ℝ) 1 / 2 := by
        simp only [Rat.cast_div, Rat.cast_max, Rat.cast_one, zero_add]
        ring
      have hrad_real : (((max I.hi 1 - 0) / 2 : ℚ) : ℝ) = max (I.hi : ℝ) 1 / 2 := by
        simp only [Rat.cast_div, Rat.cast_max, Rat.cast_one, sub_zero]
        ring
      rw [abs_le]
      constructor
      · -- -rad ≤ sqrt v - mid
        rw [hmid_real, hrad_real]
        linarith
      · -- sqrt v - mid ≤ rad
        rw [hmid_real, hrad_real]
        have : max (I.hi : ℝ) 1 = max (I.hi : ℝ) 1 / 2 + max (I.hi : ℝ) 1 / 2 := by ring
        linarith
    · ring
  · -- Negative interval case: return wide bounds with dynamic r = max I.hi 1
    rename_i h
    simp only [List.zipWith, List.sum_nil, add_zero]
    use Real.sqrt v
    constructor
    · -- |sqrt v| ≤ max I.hi 1
      have hsqrt_nonneg := Real.sqrt_nonneg v
      rw [abs_of_nonneg hsqrt_nonneg]
      -- We have hsqrt_hi : sqrt v ≤ max (I.hi : ℝ) 1
      -- Need to show: sqrt v ≤ ↑(max I.hi 1)
      simp only [Rat.cast_max, Rat.cast_one]
      exact hsqrt_hi
    · simp

end AffineForm

end LeanCert.Engine.Affine
