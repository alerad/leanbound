/-
Copyright (c) 2025 LeanCert Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors

Potential Mathlib contribution: Differentiability of sinc and dslope theorems.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiability of sinc and dslope

This file proves that the sinc function is differentiable everywhere, including at 0.

## Main results

* `Real.differentiableAt_sinc`: sinc is differentiable at every point
* `Real.hasDerivAt_sinc_zero`: sinc has derivative 0 at x = 0

## Mathematical background

The sinc function is defined as:
- `sinc x = sin x / x` for `x ≠ 0`
- `sinc 0 = 1`

Equivalently, `sinc = dslope sin 0`.

The derivative of sinc at 0 can be computed using Taylor expansion:
- `sin x = x - x³/6 + x⁵/120 - ...`
- `sinc x = 1 - x²/6 + x⁴/120 - ...`
- `sinc'(0) = 0`
-/

open Filter Topology
open scoped Topology

namespace Real

variable {x : ℝ}

/-- Bound on |sin x - x| in terms of |x|³.
For x > 0: sin x < x and x - x³/4 < sin x, so 0 < x - sin x < x³/4.
By symmetry (sin(-x) = -sin(x)), |sin x - x| ≤ |x|³/4 for all x with |x| ≤ 1. -/
theorem abs_sin_sub_self_le (x : ℝ) (hx : |x| ≤ 1) : |sin x - x| ≤ |x| ^ 3 / 4 := by
  rcases le_or_gt x 0 with hx_neg | hx_pos
  · -- Case x ≤ 0
    have hx' : 0 ≤ -x := neg_nonneg.mpr hx_neg
    have hx'' : -x ≤ 1 := by rwa [abs_of_nonpos hx_neg] at hx
    rcases eq_or_lt_of_le hx' with hx_zero | hx_pos'
    · -- x = 0
      have : x = 0 := neg_eq_zero.mp hx_zero.symm
      simp [this]
    · -- x < 0, i.e., 0 < -x ≤ 1
      have h1 : sin (-x) < -x := sin_lt hx_pos'
      have h2 : -x - (-x) ^ 3 / 4 < sin (-x) := sin_gt_sub_cube hx_pos' hx''
      -- sin x = -sin(-x), so sin x - x = -sin(-x) - x
      -- From h1: sin(-x) < -x, so sin(-x) + x < 0
      -- Therefore -sin(-x) - x = -(sin(-x) + x) > 0
      rw [abs_of_nonpos hx_neg]
      have hsinx : sin x = -sin (-x) := by simp [sin_neg]
      rw [hsinx]
      have hsum_pos : 0 < -sin (-x) - x := by linarith
      rw [abs_of_pos hsum_pos]
      -- Goal: -sin(-x) - x ≤ (-x) ^ 3 / 4
      -- From h2: sin(-x) > -x - (-x)^3/4, so -sin(-x) < x + (-x)^3/4
      -- Therefore -sin(-x) - x < (-x)^3/4
      linarith
  · -- Case x > 0
    have hx' : x ≤ 1 := by rwa [abs_of_pos hx_pos] at hx
    have h1 : sin x < x := sin_lt hx_pos
    have h2 : x - x ^ 3 / 4 < sin x := sin_gt_sub_cube hx_pos hx'
    rw [abs_of_pos hx_pos]
    have hsub_pos : 0 < x - sin x := by linarith
    rw [abs_of_neg (by linarith : sin x - x < 0)]
    linarith

/-- The derivative of sinc at 0 is 0.

The proof uses the squeeze theorem with the bound `|sinc x - 1| ≤ |x|² / 4`,
which follows from sin bounds in Mathlib. -/
theorem hasDerivAt_sinc_zero : HasDerivAt sinc 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  -- Need to show: Tendsto (slope sinc 0) (𝓝[≠] 0) (𝓝 0)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  use min 1 (ε * 4)
  constructor
  · positivity
  intro y hy_ne hy_dist
  simp only [slope, vsub_eq_sub, sinc_zero, smul_eq_mul, dist_eq_norm, sub_zero] at *
  by_cases hy : y = 0
  · exact absurd hy hy_ne
  rw [Real.norm_eq_abs] at hy_dist ⊢
  rw [abs_mul, abs_inv]
  rw [sinc_of_ne_zero hy, div_sub_one hy, abs_div]
  -- Goal: |y|⁻¹ * (|sin y - y| / |y|) < ε
  -- i.e., |sin y - y| / |y|² < ε
  have hy_le_1 : |y| ≤ 1 := (lt_min_iff.mp hy_dist).1.le
  have hy_abs_pos : 0 < |y| := abs_pos.mpr hy
  have hy_sq_pos : 0 < |y| ^ 2 := sq_pos_of_pos hy_abs_pos
  -- |sin y - y| ≤ |y|³/4
  have hbound : |sin y - y| ≤ |y| ^ 3 / 4 := abs_sin_sub_self_le y hy_le_1
  -- |y|⁻¹ * (|sin y - y| / |y|) = |sin y - y| / |y|² ≤ |y|³/4 / |y|² = |y|/4
  calc |y|⁻¹ * (|sin y - y| / |y|)
      = |sin y - y| / |y| ^ 2 := by rw [inv_mul_eq_div, div_div, sq]
    _ ≤ (|y| ^ 3 / 4) / |y| ^ 2 := by
        apply div_le_div_of_nonneg_right hbound
        exact hy_sq_pos.le
    _ = |y| / 4 := by
        have hy_ne : |y| ≠ 0 := ne_of_gt hy_abs_pos
        have hsq : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
        field_simp [hy_ne]
    _ < ε := by
        have h_eps : |y| < ε * 4 := (lt_min_iff.mp hy_dist).2
        linarith

theorem differentiableAt_sinc_zero : DifferentiableAt ℝ sinc 0 :=
  hasDerivAt_sinc_zero.differentiableAt

/-- sinc is differentiable everywhere. -/
theorem differentiableAt_sinc (x : ℝ) : DifferentiableAt ℝ sinc x := by
  by_cases hx : x = 0
  · exact hx ▸ differentiableAt_sinc_zero
  · rw [sinc_eq_dslope, differentiableAt_dslope_of_ne hx]
    exact differentiable_sin.differentiableAt

/-- sinc is a differentiable function. -/
theorem differentiable_sinc : Differentiable ℝ sinc := fun x => differentiableAt_sinc x

/-- The derivative of sinc at a nonzero point. -/
theorem hasDerivAt_sinc_of_ne_zero (hx : x ≠ 0) :
    HasDerivAt sinc ((x * cos x - sin x) / x ^ 2) x := by
  have h1 : HasDerivAt sin (cos x) x := hasDerivAt_sin x
  have h2 : HasDerivAt (fun y => y) 1 x := hasDerivAt_id x
  have h3 : HasDerivAt (fun y => sin y / y) ((cos x * x - sin x * 1) / x ^ 2) x :=
    h1.div h2 hx
  simp only [mul_one] at h3
  have h4 : HasDerivAt (fun y => sin y / y) ((x * cos x - sin x) / x ^ 2) x := by
    convert h3 using 1; ring
  -- sinc agrees with sin/id on a neighborhood of x (since x ≠ 0)
  have heq : sinc =ᶠ[𝓝 x] (fun y => sin y / y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact sinc_of_ne_zero hy
  exact h4.congr_of_eventuallyEq heq

/-- The derivative of sinc. For x = 0, deriv sinc 0 = 0. For x ≠ 0, deriv sinc x = (x cos x - sin x) / x². -/
theorem deriv_sinc : deriv sinc x = if x = 0 then 0 else (x * cos x - sin x) / x ^ 2 := by
  split_ifs with hx
  · exact hx ▸ hasDerivAt_sinc_zero.deriv
  · exact (hasDerivAt_sinc_of_ne_zero hx).deriv

@[simp]
theorem deriv_sinc_zero : deriv sinc 0 = 0 := hasDerivAt_sinc_zero.deriv

/-
The derivative of sinc is bounded: |sinc'(x)| ≤ 1 for all x.

The key insight is that for x ≠ 0:
- sinc'(x) = (x cos x - sin x) / x²
- Let g(x) = x cos x - sin x. Then g(0) = 0 and g'(x) = -x sin x.
- |g(x)| = |∫₀ˣ -t sin t dt| ≤ ∫₀ˣ |t| dt = x²/2
- Therefore |sinc'(x)| = |g(x)|/x² ≤ 1/2 < 1

The proof using integration is mathematically straightforward but requires
formalizing the integral representation. Instead we use a direct monotonicity argument.
-/

/-- Bound: |x cos x - sin x| ≤ x² for all x.
    Proof uses monotonicity of auxiliary functions on [0, ∞). -/
theorem abs_x_mul_cos_sub_sin_le_sq (x : ℝ) : |x * cos x - sin x| ≤ x ^ 2 := by
  suffices ∀ x ≥ 0, |x * cos x - sin x| ≤ x ^ 2 by
    obtain h | h := le_total 0 x
    · exact this x h
    · rw [← abs_neg, ← neg_sq x]
      convert this (-x) (neg_nonneg.mpr h) using 2
      ring_nf
      simp only [cos_neg, sin_neg]
      ring
  intro x hx
  rw [abs_le]
  constructor
  · -- -x^2 ≤ x cos x - sin x, equivalently 0 ≤ x cos x - sin x + x^2
    -- Define g(t) = t * cos t - sin t + t^2, show g is monotone on [0,∞) with g(0) = 0
    let g : ℝ → ℝ := fun t => t * cos t - sin t + t^2
    have hg_diff : ∀ t, HasDerivAt g (t * (2 - sin t)) t := fun t => by
      have h1 : HasDerivAt (fun t => t * cos t) (1 * cos t + t * (-sin t)) t :=
        hasDerivAt_id t |>.mul (hasDerivAt_cos t)
      have h2 : HasDerivAt (fun t => t * cos t - sin t) (1 * cos t + t * (-sin t) - cos t) t :=
        h1.sub (hasDerivAt_sin t)
      have hpow : HasDerivAt (fun t => t^2) (2 * t) t := by
        have := hasDerivAt_pow 2 t
        simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
        exact this
      have h3 : HasDerivAt (fun t => t * cos t - sin t + t^2)
          (1 * cos t + t * (-sin t) - cos t + 2 * t) t :=
        h2.add hpow
      convert h3 using 1
      ring
    have hg_cont : Continuous g :=
      (continuous_id.mul continuous_cos).sub continuous_sin |>.add (continuous_pow 2)
    have hg_diffble : Differentiable ℝ g := fun t => (hg_diff t).differentiableAt
    have hg' : ∀ t, deriv g t = t * (2 - sin t) := fun t => (hg_diff t).deriv
    have hg_nonneg : ∀ t ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv g t := by
      intro t ht
      rw [interior_Ici] at ht
      rw [hg' t]
      apply mul_nonneg (le_of_lt (Set.mem_Ioi.mp ht))
      linarith [sin_le_one t]
    have g_nonneg : 0 ≤ g x := by
      have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hg_cont.continuousOn
        hg_diffble.differentiableOn hg_nonneg
      have hg0 : g 0 = 0 := by simp [g]
      calc 0 = g 0 := hg0.symm
        _ ≤ g x := hmono (by simp : (0:ℝ) ∈ Set.Ici 0) (Set.mem_Ici.mpr hx) hx
    linarith [g_nonneg]
  · -- x cos x - sin x ≤ x^2, equivalently 0 ≤ x^2 - (x cos x - sin x)
    -- Define g(t) = t^2 - (t * cos t - sin t), show g is monotone on [0,∞) with g(0) = 0
    let g : ℝ → ℝ := fun t => t^2 - (t * cos t - sin t)
    have hg_diff : ∀ t, HasDerivAt g (t * (2 + sin t)) t := fun t => by
      have h1 : HasDerivAt (fun t => t * cos t) (1 * cos t + t * (-sin t)) t :=
        hasDerivAt_id t |>.mul (hasDerivAt_cos t)
      have h2 : HasDerivAt (fun t => t * cos t - sin t) (1 * cos t + t * (-sin t) - cos t) t :=
        h1.sub (hasDerivAt_sin t)
      have hpow : HasDerivAt (fun t => t^2) (2 * t) t := by
        have := hasDerivAt_pow 2 t
        simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
        exact this
      have h3 : HasDerivAt (fun t => t^2 - (t * cos t - sin t))
          (2 * t - (1 * cos t + t * (-sin t) - cos t)) t :=
        hpow.sub h2
      convert h3 using 1
      ring
    have hg_cont : Continuous g :=
      (continuous_pow 2).sub ((continuous_id.mul continuous_cos).sub continuous_sin)
    have hg_diffble : Differentiable ℝ g := fun t => (hg_diff t).differentiableAt
    have hg' : ∀ t, deriv g t = t * (2 + sin t) := fun t => (hg_diff t).deriv
    have hg_nonneg : ∀ t ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv g t := by
      intro t ht
      rw [interior_Ici] at ht
      rw [hg' t]
      apply mul_nonneg (le_of_lt (Set.mem_Ioi.mp ht))
      linarith [neg_one_le_sin t]
    have g_nonneg : 0 ≤ g x := by
      have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hg_cont.continuousOn
        hg_diffble.differentiableOn hg_nonneg
      have hg0 : g 0 = 0 := by simp [g]
      calc 0 = g 0 := hg0.symm
        _ ≤ g x := hmono (by simp : (0:ℝ) ∈ Set.Ici 0) (Set.mem_Ici.mpr hx) hx
    linarith [g_nonneg]

theorem abs_deriv_sinc_le_one (x : ℝ) : |deriv sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [(hasDerivAt_sinc_of_ne_zero hx).deriv]
    rw [abs_div]
    have hx_sq : x ^ 2 > 0 := sq_pos_of_ne_zero hx
    have habs_sq : |x ^ 2| = x ^ 2 := abs_of_pos hx_sq
    rw [habs_sq, div_le_one hx_sq]
    exact abs_x_mul_cos_sub_sin_le_sq x

/-- deriv sinc x is in [-1, 1] for all x -/
theorem deriv_sinc_mem_Icc (x : ℝ) : deriv sinc x ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc]
  have h := abs_deriv_sinc_le_one x
  rw [abs_le] at h
  exact h

end Real
