/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.RootFinding.Newton

/-!
# Root Finding: MVT-based bounds for Newton contraction proofs

This file contains Mean Value Theorem-based lemmas used to prove
Newton method correctness, particularly for showing that Newton
contraction implies root existence.

## Main lemmas

* `mvt_lower_bound` - Lower bound from MVT
* `mvt_upper_bound` - Upper bound from MVT
* `newton_positive_increasing_contradicts_contraction` - MVT contradiction lemma
* `newton_negative_increasing_contradicts_contraction` - MVT contradiction lemma
* `quotient_hi_lower_bound` - Quotient bound for positive derivative
* `quotient_lo_upper_bound` - Quotient bound for positive derivative
* `newtonStepSimple_contraction_absurd_hi` - Contraction contradiction
* `newtonStepSimple_contraction_absurd_lo` - Contraction contradiction
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### MVT wrapper lemmas -/

/-- MVT lower bound: if f' ≥ C on interval I, then f(y) - f(x) ≥ C * (y - x) for x ≤ y in I.
    This wraps Mathlib's Convex.mul_sub_le_image_sub_of_le_deriv for our use case. -/
lemma mvt_lower_bound (e : Expr) (hsupp : ExprSupported e) (_hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (C : ℝ)
    (hC : ∀ ξ ∈ I, C ≤ deriv (evalFunc1 e) ξ)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      C * (y - x) ≤ evalFunc1 e y - evalFunc1 e x := by
  intro x y hx hy hxy
  -- Use Convex.mul_sub_le_image_sub_of_le_deriv
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), C ≤ deriv (evalFunc1 e) ξ := by
    intro ξ hξ
    have hξ_in_I : ξ ∈ I := by
      simp only [IntervalRat.mem_def]
      have := interior_subset hξ
      simp only [Set.mem_Icc] at this
      exact this
    exact hC ξ hξ_in_I
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by
    simp only [IntervalRat.mem_def] at hx
    exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by
    simp only [IntervalRat.mem_def] at hy
    exact hy
  exact hConvex.mul_sub_le_image_sub_of_le_deriv hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-- MVT upper bound: if f' ≤ C on interval I, then f(y) - f(x) ≤ C * (y - x) for x ≤ y in I.
    This wraps Mathlib's Convex.image_sub_le_mul_sub_of_deriv_le for our use case. -/
lemma mvt_upper_bound (e : Expr) (hsupp : ExprSupported e) (_hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (C : ℝ)
    (hC : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ C)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      evalFunc1 e y - evalFunc1 e x ≤ C * (y - x) := by
  intro x y hx hy hxy
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), deriv (evalFunc1 e) ξ ≤ C := by
    intro ξ hξ
    have hξ_in_I : ξ ∈ I := by
      simp only [IntervalRat.mem_def]
      have := interior_subset hξ
      simp only [Set.mem_Icc] at this
      exact this
    exact hC ξ hξ_in_I
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by
    simp only [IntervalRat.mem_def] at hx
    exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by
    simp only [IntervalRat.mem_def] at hy
    exact hy
  exact hConvex.image_sub_le_mul_sub_of_deriv_le hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-! ### Contradiction lemmas for increasing functions -/

/-- Contradiction lemma: If f > 0 at I.lo with f' ≥ dI.lo > 0 (increasing),
    then the Newton quotient Q.hi > hw, contradicting strict contraction Q.hi < hw.

    Key argument:
    1. By MVT: f(c) - f(I.lo) ≥ dI.lo * hw, so f(c) ≥ f(I.lo) + dI.lo * hw > dI.lo * hw
    2. fc.hi ≥ f(c) > dI.lo * hw
    3. Q.hi = fc.hi / dI.lo > hw
    4. But contraction requires Q.hi < hw (from N.lo > I.lo)
    5. Contradiction -/
lemma newton_positive_increasing_contradicts_contraction
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (_hI_nonsingleton : I.lo < I.hi)
    (hdI_lo_pos : 0 < (derivInterval e (fun _ => I) 0).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_pos : 0 < evalFunc1 e I.lo) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    let fc := evalInterval1 e (IntervalRat.singleton c)
    -- The Newton quotient violates the contraction bound (in ℝ)
    (fc.hi : ℝ) / dI.lo ≥ hw := by
  intro c hw dI fc
  -- Get derivative bounds
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ => (hderiv ξ hξ).1
  -- Get midpoint membership
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  -- Apply MVT: f(c) - f(I.lo) ≥ dI.lo * (c - I.lo)
  have hmvt := mvt_lower_bound e hsupp hvar0 I dI.lo hderiv_lo hCont I.lo c hIlo_in_I hc_in_I
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast
      ring
    linarith
  specialize hmvt hIlo_le_c
  -- c - I.lo = hw (in ℝ)
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast
      ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast
      ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  -- So f(c) ≥ f(I.lo) + dI.lo * hw > dI.lo * hw (since f(I.lo) > 0)
  have hfc_bound : evalFunc1 e c > (dI.lo : ℝ) * hw := by
    calc evalFunc1 e c ≥ evalFunc1 e I.lo + dI.lo * hw := by linarith
    _ > 0 + dI.lo * hw := by linarith
    _ = dI.lo * hw := by ring
  -- By interval correctness: fc.hi ≥ f(c)
  have hfc_correct := evalInterval1_correct e hsupp (c : ℝ) (IntervalRat.singleton c)
    (IntervalRat.mem_singleton c)
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_hi_ge : (fc.hi : ℝ) ≥ evalFunc1 e c := hfc_correct.2
  -- So fc.hi > dI.lo * hw
  have hfc_hi_bound : (fc.hi : ℝ) > (dI.lo : ℝ) * hw := by linarith
  -- Therefore fc.hi / dI.lo > hw (since dI.lo > 0)
  have hdI_lo_pos_real : (0 : ℝ) < dI.lo := by exact_mod_cast hdI_lo_pos
  have hdiv_bound : (fc.hi : ℝ) / dI.lo > hw := by
    have hpos : (0 : ℝ) < dI.lo := hdI_lo_pos_real
    calc (fc.hi : ℝ) / dI.lo > ((dI.lo : ℝ) * hw) / dI.lo := by {
      apply div_lt_div_of_pos_right hfc_hi_bound hpos
    }
    _ = hw := by field_simp
  linarith

/-- Contradiction lemma: If f < 0 at I.hi with f' ≥ dI.lo > 0 (increasing),
    then the Newton quotient Q.lo < -hw, contradicting strict contraction Q.lo > -hw.

    Key argument:
    1. By MVT: f(I.hi) - f(c) ≥ dI.lo * hw, so f(c) ≤ f(I.hi) - dI.lo * hw < -dI.lo * hw
    2. fc.lo ≤ f(c) < -dI.lo * hw
    3. Q.lo = fc.lo / dI.lo < -hw
    4. But contraction requires Q.lo > -hw (from N.hi < I.hi)
    5. Contradiction -/
lemma newton_negative_increasing_contradicts_contraction
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (_hI_nonsingleton : I.lo < I.hi)
    (hdI_lo_pos : 0 < (derivInterval e (fun _ => I) 0).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_neg : evalFunc1 e I.hi < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    let fc := evalInterval1 e (IntervalRat.singleton c)
    -- The Newton quotient violates the contraction bound (in ℝ)
    (fc.lo : ℝ) / dI.lo ≤ -hw := by
  intro c hw dI fc
  -- Get derivative bounds
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ => (hderiv ξ hξ).1
  -- Get memberships
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  -- Apply MVT: f(I.hi) - f(c) ≥ dI.lo * (I.hi - c)
  have hmvt := mvt_lower_bound e hsupp hvar0 I dI.lo hderiv_lo hCont c I.hi hc_in_I hIhi_in_I
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    linarith
  specialize hmvt hc_le_Ihi
  -- I.hi - c = hw (in ℝ)
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  -- So f(c) ≤ f(I.hi) - dI.lo * hw < -dI.lo * hw (since f(I.hi) < 0)
  have hfc_bound : evalFunc1 e c < -((dI.lo : ℝ) * hw) := by linarith
  -- By interval correctness: fc.lo ≤ f(c)
  have hfc_correct := evalInterval1_correct e hsupp (c : ℝ) (IntervalRat.singleton c)
    (IntervalRat.mem_singleton c)
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_lo_le : (fc.lo : ℝ) ≤ evalFunc1 e c := hfc_correct.1
  -- So fc.lo < -dI.lo * hw
  have hfc_lo_bound : (fc.lo : ℝ) < -((dI.lo : ℝ) * hw) := by linarith
  -- Therefore fc.lo / dI.lo < -hw (since dI.lo > 0)
  have hdI_lo_pos_real : (0 : ℝ) < dI.lo := by exact_mod_cast hdI_lo_pos
  have hdiv_bound : (fc.lo : ℝ) / dI.lo < -(hw : ℝ) := by
    have hpos : (0 : ℝ) < dI.lo := hdI_lo_pos_real
    calc (fc.lo : ℝ) / dI.lo < (-((dI.lo : ℝ) * hw)) / dI.lo := by {
      apply div_lt_div_of_pos_right hfc_lo_bound hpos
    }
    _ = -(hw : ℝ) := by field_simp;
  linarith

/-! ### Quotient bound lemmas -/

/-- When dI.lo > 0, the quotient Q has Q.hi ≥ fc.hi / dI.lo (regardless of fc signs).
    This is because the invNonzero of positive dI is [1/dI.hi, 1/dI.lo], and the max
    includes fc.hi * dI.lo⁻¹ as one of its corners. -/
lemma quotient_hi_lower_bound {fc : IntervalRat} {dI : IntervalRat.IntervalRatNonzero}
    (hdI_pos : 0 < dI.lo) :
    let Q := IntervalRat.mul fc (IntervalRat.invNonzero dI)
    Q.hi ≥ fc.hi / dI.lo := by
  intro Q
  -- invNonzero for positive dI gives [1/dI.hi, 1/dI.lo]
  have hdInv : IntervalRat.invNonzero dI = ⟨dI.hi⁻¹, dI.lo⁻¹, by
    have hlo : (0 : ℚ) < dI.lo := hdI_pos
    have hhi : (0 : ℚ) < dI.hi := lt_of_lt_of_le hlo dI.le
    exact inv_anti₀ hlo dI.le⟩ := by
    unfold IntervalRat.invNonzero
    simp only [hdI_pos, ↓reduceDIte]
  -- Q.hi = max of corners, which is ≥ fc.hi * dI.lo⁻¹
  show (IntervalRat.mul fc (IntervalRat.invNonzero dI)).hi ≥ fc.hi / dI.lo
  rw [hdInv]
  -- IntervalRat.mul.hi = max(max(a*c, a*d), max(b*c, b*d)) where [a,b] = fc, [c,d] = invNonzero
  -- Here d = dI.lo⁻¹, so fc.hi * dI.lo⁻¹ appears in the max
  simp only [IntervalRat.mul, div_eq_mul_inv]
  -- fc.hi * dI.lo⁻¹ ≤ max(fc.hi * dI.hi⁻¹, fc.hi * dI.lo⁻¹) ≤ max(max(..), max(..))
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- When dI.lo > 0, the quotient Q has Q.lo ≤ fc.lo / dI.lo. -/
lemma quotient_lo_upper_bound {fc : IntervalRat} {dI : IntervalRat.IntervalRatNonzero}
    (hdI_pos : 0 < dI.lo) :
    let Q := IntervalRat.mul fc (IntervalRat.invNonzero dI)
    Q.lo ≤ fc.lo / dI.lo := by
  intro Q
  have hdInv : IntervalRat.invNonzero dI = ⟨dI.hi⁻¹, dI.lo⁻¹, by
    have hlo : (0 : ℚ) < dI.lo := hdI_pos
    have hhi : (0 : ℚ) < dI.hi := lt_of_lt_of_le hlo dI.le
    exact inv_anti₀ hlo dI.le⟩ := by
    unfold IntervalRat.invNonzero
    simp only [hdI_pos, ↓reduceDIte]
  -- Q.lo = min of corners, which is ≤ fc.lo * dI.lo⁻¹
  show (IntervalRat.mul fc (IntervalRat.invNonzero dI)).lo ≤ fc.lo / dI.lo
  rw [hdInv]
  simp only [IntervalRat.mul, div_eq_mul_inv]
  -- fc.lo * dI.lo⁻¹ appears in min(...), so min ≤ fc.lo * dI.lo⁻¹
  exact le_trans (min_le_left _ _) (min_le_right _ _)

/-- For negative dI, the quotient Q has Q.hi ≥ fc.lo / dI.hi.
    This is because fc.lo * dI.hi⁻¹ is one of the four corners in Q = fc * inv(dI),
    and Q.hi = max of all corners.
    This bound is used for Newton contraction contradiction when f < 0 at both endpoints. -/
lemma quotient_hi_ge_neg {fc : IntervalRat} {dI : IntervalRat.IntervalRatNonzero}
    (hdI_neg : dI.hi < 0) :
    let Q := IntervalRat.mul fc (IntervalRat.invNonzero dI)
    Q.hi ≥ fc.lo / dI.hi := by
  -- For negative dI: invNonzero dI = ⟨dI.hi⁻¹, dI.lo⁻¹⟩
  -- Q.hi = max4 of all corners. One corner is fc.lo * dI.hi⁻¹.
  intro Q
  have hdI_lo_neg : dI.lo < 0 := lt_of_le_of_lt dI.le hdI_neg
  have hdInv : IntervalRat.invNonzero dI = ⟨dI.hi⁻¹, dI.lo⁻¹, by
    exact (inv_le_inv_of_neg hdI_neg hdI_lo_neg).mpr dI.le⟩ := by
    unfold IntervalRat.invNonzero
    have h1 : ¬(0 : ℚ) < dI.lo := by linarith
    have h2 : ¬(0 : ℚ) < dI.hi := by linarith
    simp only [h1]
    rfl
  show (IntervalRat.mul fc (IntervalRat.invNonzero dI)).hi ≥ fc.lo / dI.hi
  rw [hdInv]
  simp only [IntervalRat.mul, div_eq_mul_inv]
  -- fc.lo * dI.hi⁻¹ is one of the four corners (fc.lo * inv.lo where inv.lo = dI.hi⁻¹)
  exact le_trans (le_max_left _ _) (le_max_left _ _)

/-- For negative dI, the quotient Q has Q.lo ≤ fc.hi / dI.hi.
    This is because fc.hi * dI.hi⁻¹ is one of the four corners in Q = fc * inv(dI),
    and Q.lo = min of all corners.
    This bound is used for Newton contraction contradiction when f > 0 at both endpoints. -/
lemma quotient_lo_le_neg {fc : IntervalRat} {dI : IntervalRat.IntervalRatNonzero}
    (hdI_neg : dI.hi < 0) :
    let Q := IntervalRat.mul fc (IntervalRat.invNonzero dI)
    Q.lo ≤ fc.hi / dI.hi := by
  -- For negative dI: invNonzero dI = ⟨dI.hi⁻¹, dI.lo⁻¹⟩
  -- Q.lo = min4 of all corners. One corner is fc.hi * dI.hi⁻¹.
  intro Q
  have hdI_lo_neg : dI.lo < 0 := lt_of_le_of_lt dI.le hdI_neg
  have hdInv : IntervalRat.invNonzero dI = ⟨dI.hi⁻¹, dI.lo⁻¹, by
    exact (inv_le_inv_of_neg hdI_neg hdI_lo_neg).mpr dI.le⟩ := by
    unfold IntervalRat.invNonzero
    have h1 : ¬(0 : ℚ) < dI.lo := by linarith
    have h2 : ¬(0 : ℚ) < dI.hi := by linarith
    simp only [h1]
    rfl
  show (IntervalRat.mul fc (IntervalRat.invNonzero dI)).lo ≤ fc.hi / dI.hi
  rw [hdInv]
  simp only [IntervalRat.mul, div_eq_mul_inv]
  -- fc.hi * dI.hi⁻¹ is one of the four corners (fc.hi * inv.lo where inv.lo = dI.hi⁻¹)
  exact le_trans (min_le_right _ _) (min_le_left _ _)

/-! ### Generic contraction contradiction lemmas

These lemmas abstract the Newton step structure to work with any interval `fc`
that contains `f(c)`. This allows them to be used with both `newtonStepSimple`
(where `fc = evalInterval1 e (singleton c)`) and `newtonStepTM`
(where `fc = TaylorModel.valueAtCenterInterval tm`). -/

/-- Generic contradiction: if Q is computed from fc/dI with dI.lo > 0, contraction holds,
    and f(c) > dI.lo * hw, then False.

    This abstracts the key Newton contraction argument:
    1. Contraction implies Q.hi < hw (since N.lo > I.lo means c - Q.hi > I.lo)
    2. f(c) > dI.lo * hw implies fc.hi > dI.lo * hw (since fc.hi ≥ f(c))
    3. quotient_hi_lower_bound says Q.hi ≥ fc.hi / dI.lo > hw
    4. Contradiction: Q.hi < hw and Q.hi > hw -/
lemma generic_contraction_absurd_hi
    (I : IntervalRat)
    (c : ℚ) (fc dI : IntervalRat) (N : IntervalRat)
    (hc_eq : c = I.midpoint)
    (hdI_nonzero : ¬dI.containsZero)
    (hdI_pos : 0 < dI.lo)
    (hfc_correct : evalFunc1 e c ∈ fc)  -- f(c) ∈ fc
    (hN_lo_eq : N.lo = max I.lo (c - (IntervalRat.mul fc (IntervalRat.invNonzero ⟨dI, hdI_nonzero⟩)).hi))
    (hContract : N.lo > I.lo)
    (hMVT : evalFunc1 e c > (dI.lo : ℝ) * ((I.hi - I.lo) / 2 : ℚ)) : False := by
  let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
  let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
  let hw : ℚ := (I.hi - I.lo) / 2
  -- From contraction: Q.hi < hw
  have hQ_hi_lt_hw : Q.hi < hw := by
    have hmax_gt : max I.lo (c - Q.hi) > I.lo := by rw [← hN_lo_eq]; exact hContract
    have hright_gt : c - Q.hi > I.lo := by
      by_contra h; push_neg at h
      have : max I.lo (c - Q.hi) = I.lo := max_eq_left h
      rw [this] at hmax_gt; exact lt_irrefl I.lo hmax_gt
    have hc_minus_Ilo : c - I.lo = hw := by rw [hc_eq]; simp only [IntervalRat.midpoint]; ring
    linarith
  -- From hfc_correct: fc.hi ≥ f(c) > dI.lo * hw
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_hi_gt : (fc.hi : ℝ) > (dI.lo : ℝ) * hw := by
    have := hfc_correct.2
    calc (fc.hi : ℝ) ≥ evalFunc1 e c := this
      _ > dI.lo * hw := hMVT
  -- quotient_hi_lower_bound: Q.hi ≥ fc.hi / dI.lo > hw
  have hQ_hi_ge : Q.hi ≥ fc.hi / dI.lo := quotient_hi_lower_bound hdI_pos
  have hdI_lo_pos_real : (0 : ℝ) < dI.lo := by exact_mod_cast hdI_pos
  have hQ_hi_gt_hw : (Q.hi : ℝ) > hw := by
    calc (Q.hi : ℝ) ≥ fc.hi / dI.lo := by exact_mod_cast hQ_hi_ge
      _ > (dI.lo * hw) / dI.lo := by exact div_lt_div_of_pos_right hfc_hi_gt hdI_lo_pos_real
      _ = hw := by field_simp
  have hQ_hi_lt_hw_real : (Q.hi : ℝ) < hw := by exact_mod_cast hQ_hi_lt_hw
  linarith

/-- Generic contradiction for Q.lo case with dI.lo > 0. -/
lemma generic_contraction_absurd_lo
    (I : IntervalRat)
    (c : ℚ) (fc dI : IntervalRat) (N : IntervalRat)
    (hc_eq : c = I.midpoint)
    (hdI_nonzero : ¬dI.containsZero)
    (hdI_pos : 0 < dI.lo)
    (hfc_correct : evalFunc1 e c ∈ fc)
    (hN_hi_eq : N.hi = min I.hi (c - (IntervalRat.mul fc (IntervalRat.invNonzero ⟨dI, hdI_nonzero⟩)).lo))
    (hContract : N.hi < I.hi)
    (hMVT : evalFunc1 e c < -((dI.lo : ℝ) * ((I.hi - I.lo) / 2 : ℚ))) : False := by
  let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
  let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
  let hw : ℚ := (I.hi - I.lo) / 2
  -- From contraction: Q.lo > -hw
  have hQ_lo_gt_neg_hw : Q.lo > -hw := by
    have hmin_lt : min I.hi (c - Q.lo) < I.hi := by rw [← hN_hi_eq]; exact hContract
    have hright_lt : c - Q.lo < I.hi := by
      by_contra h; push_neg at h
      have : min I.hi (c - Q.lo) = I.hi := min_eq_left h
      rw [this] at hmin_lt; exact lt_irrefl I.hi hmin_lt
    have hc_minus_Ihi : c - I.hi = -hw := by rw [hc_eq]; simp only [IntervalRat.midpoint]; ring
    linarith
  -- From hfc_correct: fc.lo ≤ f(c) < -dI.lo * hw
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_lo_lt : (fc.lo : ℝ) < -((dI.lo : ℝ) * hw) := by
    have := hfc_correct.1
    calc (fc.lo : ℝ) ≤ evalFunc1 e c := this
      _ < -(dI.lo * hw) := hMVT
  -- quotient_lo_upper_bound: Q.lo ≤ fc.lo / dI.lo < -hw
  have hQ_lo_le : Q.lo ≤ fc.lo / dI.lo := quotient_lo_upper_bound hdI_pos
  have hdI_lo_pos_real : (0 : ℝ) < dI.lo := by exact_mod_cast hdI_pos
  have hQ_lo_lt_neg_hw : (Q.lo : ℝ) < -hw := by
    calc (Q.lo : ℝ) ≤ fc.lo / dI.lo := by exact_mod_cast hQ_lo_le
      _ < (-(dI.lo * hw)) / dI.lo := by exact div_lt_div_of_pos_right hfc_lo_lt hdI_lo_pos_real
      _ = -hw := by field_simp;
  have hQ_lo_gt_neg_hw_real : (Q.lo : ℝ) > -hw := by exact_mod_cast hQ_lo_gt_neg_hw
  linarith

/-- Generic contradiction for Q.hi case with dI.hi < 0 (decreasing function). -/
lemma generic_contraction_absurd_hi_neg
    (I : IntervalRat)
    (c : ℚ) (fc dI : IntervalRat) (N : IntervalRat)
    (hc_eq : c = I.midpoint)
    (hdI_nonzero : ¬dI.containsZero)
    (hdI_neg : dI.hi < 0)
    (hfc_correct : evalFunc1 e c ∈ fc)
    (hN_lo_eq : N.lo = max I.lo (c - (IntervalRat.mul fc (IntervalRat.invNonzero ⟨dI, hdI_nonzero⟩)).hi))
    (hContract : N.lo > I.lo)
    (hMVT : evalFunc1 e c < (dI.hi : ℝ) * ((I.hi - I.lo) / 2 : ℚ)) : False := by
  let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
  let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
  let hw : ℚ := (I.hi - I.lo) / 2
  -- From contraction: Q.hi < hw
  have hQ_hi_lt_hw : Q.hi < hw := by
    have hmax_gt : max I.lo (c - Q.hi) > I.lo := by rw [← hN_lo_eq]; exact hContract
    have hright_gt : c - Q.hi > I.lo := by
      by_contra h; push_neg at h
      have : max I.lo (c - Q.hi) = I.lo := max_eq_left h
      rw [this] at hmax_gt; exact lt_irrefl I.lo hmax_gt
    have hc_minus_Ilo : c - I.lo = hw := by rw [hc_eq]; simp only [IntervalRat.midpoint]; ring
    linarith
  -- From hfc_correct: fc.lo ≤ f(c) < dI.hi * hw
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_lo_lt : (fc.lo : ℝ) < (dI.hi : ℝ) * hw := by
    have := hfc_correct.1
    calc (fc.lo : ℝ) ≤ evalFunc1 e c := this
      _ < dI.hi * hw := hMVT
  -- quotient_hi_ge_neg: Q.hi ≥ fc.lo / dI.hi
  have hQ_hi_ge : Q.hi ≥ fc.lo / dI.hi := quotient_hi_ge_neg hdI_neg
  -- With dI.hi < 0: fc.lo < dI.hi * hw means fc.lo / dI.hi > hw
  have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_neg
  have hQ_hi_gt_hw : (Q.hi : ℝ) > hw := by
    have hdiv : (fc.lo : ℝ) / dI.hi > hw := by
      rw [gt_iff_lt, lt_div_iff_of_neg hdI_hi_neg_real]
      have h : (hw : ℝ) * dI.hi = (dI.hi : ℝ) * hw := by ring
      rw [h]; exact hfc_lo_lt
    calc (Q.hi : ℝ) ≥ fc.lo / dI.hi := by exact_mod_cast hQ_hi_ge
      _ > hw := hdiv
  have hQ_hi_lt_hw_real : (Q.hi : ℝ) < hw := by exact_mod_cast hQ_hi_lt_hw
  linarith

/-- Generic contradiction for Q.lo case with dI.hi < 0 (decreasing function). -/
lemma generic_contraction_absurd_lo_neg
    (I : IntervalRat)
    (c : ℚ) (fc dI : IntervalRat) (N : IntervalRat)
    (hc_eq : c = I.midpoint)
    (hdI_nonzero : ¬dI.containsZero)
    (hdI_neg : dI.hi < 0)
    (hfc_correct : evalFunc1 e c ∈ fc)
    (hN_hi_eq : N.hi = min I.hi (c - (IntervalRat.mul fc (IntervalRat.invNonzero ⟨dI, hdI_nonzero⟩)).lo))
    (hContract : N.hi < I.hi)
    (hMVT : evalFunc1 e c > -((dI.hi : ℝ) * ((I.hi - I.lo) / 2 : ℚ))) : False := by
  let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
  let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
  let hw : ℚ := (I.hi - I.lo) / 2
  -- From contraction: Q.lo > -hw
  have hQ_lo_gt_neg_hw : Q.lo > -hw := by
    have hmin_lt : min I.hi (c - Q.lo) < I.hi := by rw [← hN_hi_eq]; exact hContract
    have hright_lt : c - Q.lo < I.hi := by
      by_contra h; push_neg at h
      have : min I.hi (c - Q.lo) = I.hi := min_eq_left h
      rw [this] at hmin_lt; exact lt_irrefl I.hi hmin_lt
    have hc_minus_Ihi : c - I.hi = -hw := by rw [hc_eq]; simp only [IntervalRat.midpoint]; ring
    linarith
  -- From hfc_correct: fc.hi ≥ f(c) > -(dI.hi * hw)
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_hi_gt : (fc.hi : ℝ) > -((dI.hi : ℝ) * hw) := by
    have := hfc_correct.2
    calc (fc.hi : ℝ) ≥ evalFunc1 e c := this
      _ > -(dI.hi * hw) := hMVT
  -- quotient_lo_le_neg: Q.lo ≤ fc.hi / dI.hi
  have hQ_lo_le : Q.lo ≤ fc.hi / dI.hi := quotient_lo_le_neg hdI_neg
  -- With dI.hi < 0: fc.hi > -(dI.hi * hw) means fc.hi / dI.hi < -hw
  have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_neg
  have hQ_lo_lt_neg_hw : (Q.lo : ℝ) < -hw := by
    have hdiv : (fc.hi : ℝ) / dI.hi < -hw := by
      rw [div_lt_iff_of_neg hdI_hi_neg_real]
      have h : (-(hw : ℝ)) * dI.hi = -((dI.hi : ℝ) * hw) := by ring
      rw [h]; exact hfc_hi_gt
    calc (Q.lo : ℝ) ≤ fc.hi / dI.hi := by exact_mod_cast hQ_lo_le
      _ < -hw := hdiv
  have hQ_lo_gt_neg_hw_real : (Q.lo : ℝ) > -hw := by exact_mod_cast hQ_lo_gt_neg_hw
  linarith

/-! ### Simple step contradiction lemmas (using generic lemmas) -/

/-- Key contradiction: if newtonStepSimple contracts AND fc.hi/dI.lo ≥ hw (with dI.lo > 0), then False. -/
lemma newtonStepSimple_contraction_absurd_hi
    (e : Expr) (I N : IntervalRat)
    (hSimple : newtonStepSimple e I 0 = some N)
    (hContract : N.lo > I.lo ∧ N.hi < I.hi)
    (hdI_pos : 0 < (derivInterval e (fun _ => I) 0).lo)
    (hMVT : (evalInterval1 e (IntervalRat.singleton I.midpoint)).hi / (derivInterval e (fun _ => I) 0).lo ≥
            (I.hi - I.lo) / 2) : False := by
  -- Extract the structure of newtonStepSimple
  obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepSimple_extract e I N hSimple
  -- Define the key quantities
  let c := I.midpoint
  let fc := evalInterval1 e (IntervalRat.singleton c)
  let dI := derivInterval e (fun _ => I) 0
  let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
  let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
  let hw : ℚ := (I.hi - I.lo) / 2
  -- From contraction: N.lo > I.lo, but N.lo = max I.lo (c - Q.hi)
  -- This means c - Q.hi > I.lo, so Q.hi < c - I.lo = hw
  have hQ_hi_lt_hw : Q.hi < hw := by
    have hmax_gt : max I.lo (c - Q.hi) > I.lo := by
      rw [← hN_lo]; exact hContract.1
    have hright_gt : c - Q.hi > I.lo := by
      by_contra h
      push_neg at h
      have : max I.lo (c - Q.hi) = I.lo := max_eq_left h
      rw [this] at hmax_gt
      exact lt_irrefl I.lo hmax_gt
    -- c - Q.hi > I.lo means Q.hi < c - I.lo
    have hmid : c = (I.lo + I.hi) / 2 := rfl
    have hc_minus_Ilo : c - I.lo = hw := by
      simp [hmid]
      ring
    linarith
  -- But quotient_hi_lower_bound says Q.hi ≥ fc.hi / dI.lo
  have hQ_hi_ge : Q.hi ≥ fc.hi / dI.lo := quotient_hi_lower_bound hdI_pos
  -- And hMVT says fc.hi / dI.lo ≥ hw
  -- So Q.hi ≥ hw, contradicting Q.hi < hw
  have hMVT' : fc.hi / dI.lo ≥ hw := hMVT
  linarith

/-- Key contradiction: if newtonStepSimple contracts AND fc.lo/dI.lo ≤ -hw (with dI.lo > 0), then False. -/
lemma newtonStepSimple_contraction_absurd_lo
    (e : Expr) (I N : IntervalRat)
    (hSimple : newtonStepSimple e I 0 = some N)
    (hContract : N.lo > I.lo ∧ N.hi < I.hi)
    (hdI_pos : 0 < (derivInterval e (fun _ => I) 0).lo)
    (hMVT : (evalInterval1 e (IntervalRat.singleton I.midpoint)).lo / (derivInterval e (fun _ => I) 0).lo ≤
            -((I.hi - I.lo) / 2)) : False := by
  -- Extract the structure of newtonStepSimple
  obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepSimple_extract e I N hSimple
  -- Define the key quantities
  let c := I.midpoint
  let fc := evalInterval1 e (IntervalRat.singleton c)
  let dI := derivInterval e (fun _ => I) 0
  let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
  let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
  let hw : ℚ := (I.hi - I.lo) / 2
  -- From contraction: N.hi < I.hi, but N.hi = min I.hi (c - Q.lo)
  -- This means c - Q.lo < I.hi, so Q.lo > c - I.hi = -hw
  have hQ_lo_gt_neg_hw : Q.lo > -hw := by
    have hmin_lt : min I.hi (c - Q.lo) < I.hi := by
      rw [← hN_hi]; exact hContract.2
    have hright_lt : c - Q.lo < I.hi := by
      by_contra h
      push_neg at h
      have : min I.hi (c - Q.lo) = I.hi := min_eq_left h
      rw [this] at hmin_lt
      exact lt_irrefl I.hi hmin_lt
    -- c - Q.lo < I.hi means Q.lo > c - I.hi
    have hmid : c = (I.lo + I.hi) / 2 := rfl
    have hc_minus_Ihi : c - I.hi = -hw := by
      simp [hmid]
      ring
    linarith
  -- But quotient_lo_upper_bound says Q.lo ≤ fc.lo / dI.lo
  have hQ_lo_le : Q.lo ≤ fc.lo / dI.lo := quotient_lo_upper_bound hdI_pos
  -- And hMVT says fc.lo / dI.lo ≤ -hw
  -- So Q.lo ≤ -hw, contradicting Q.lo > -hw
  have hMVT' : fc.lo / dI.lo ≤ -hw := hMVT
  linarith

/-! ### Contradiction lemmas for decreasing functions -/

/-- Contradiction lemma for decreasing function: If f > 0 at I.hi with f' ≤ dI.hi < 0 (decreasing),
    then the Newton quotient Q.lo = fc.hi/dI.hi ≤ -hw, contradicting strict contraction Q.lo > -hw. -/
lemma newton_positive_decreasing_contradicts_contraction
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (hI_nonsingleton : I.lo < I.hi)
    (hdI_hi_neg : (derivInterval e (fun _ => I) 0).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_pos : 0 < evalFunc1 e I.hi) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    let fc := evalInterval1 e (IntervalRat.singleton c)
    (fc.hi : ℝ) / dI.hi ≤ -hw := by
  intro c hw dI fc
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ => (hderiv ξ hξ).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hmvt := mvt_upper_bound e hsupp hvar0 I dI.hi hderiv_hi hCont (c : ℝ) I.hi hc_in_I hIhi_in_I
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    linarith
  specialize hmvt hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = (hw : ℝ) := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  have hfc_lower : evalFunc1 e c ≥ evalFunc1 e I.hi - (dI.hi : ℝ) * hw := by linarith
  have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_hi_neg
  have hhw_pos : (0 : ℝ) < hw := by
    have h : I.lo < I.hi := hI_nonsingleton
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    rw [hhw_def]
    have hpos : (I.hi : ℝ) - I.lo > 0 := by
      have : (I.lo : ℝ) < I.hi := by exact_mod_cast h
      linarith
    linarith
  have hfc_bound : evalFunc1 e c > -(dI.hi : ℝ) * hw := by linarith
  have hfc_correct := evalInterval1_correct e hsupp (c : ℝ) (IntervalRat.singleton c)
    (IntervalRat.mem_singleton c)
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_hi_ge : (fc.hi : ℝ) ≥ evalFunc1 e c := hfc_correct.2
  have hfc_hi_bound : (fc.hi : ℝ) > -(dI.hi : ℝ) * hw := by linarith
  have h_neg_dI_hw : -((dI.hi : ℝ)) * hw = -(hw : ℝ) * dI.hi := by ring
  rw [h_neg_dI_hw] at hfc_hi_bound
  have hdiv : (fc.hi : ℝ) / dI.hi ≤ -(hw : ℝ) := by
    rw [div_le_iff_of_neg hdI_hi_neg_real]
    linarith
  exact hdiv

/-- Contradiction lemma for decreasing function: If f < 0 at I.lo with f' ≤ dI.hi < 0 (decreasing),
    then the Newton quotient violates contraction bounds. -/
lemma newton_negative_decreasing_contradicts_contraction
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (hI_nonsingleton : I.lo < I.hi)
    (hdI_hi_neg : (derivInterval e (fun _ => I) 0).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_neg : evalFunc1 e I.lo < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    let fc := evalInterval1 e (IntervalRat.singleton c)
    (fc.lo : ℝ) / dI.hi ≥ hw := by
  intro c hw dI fc
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ => (hderiv ξ hξ).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hmvt := mvt_upper_bound e hsupp hvar0 I dI.hi hderiv_hi hCont (I.lo : ℝ) (c : ℝ) hIlo_in_I hc_in_I
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    linarith
  specialize hmvt hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = (hw : ℝ) := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  have hfc_upper : evalFunc1 e c ≤ evalFunc1 e I.lo + (dI.hi : ℝ) * hw := by linarith
  have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_hi_neg
  have hhw_pos : (0 : ℝ) < hw := by
    have h : I.lo < I.hi := hI_nonsingleton
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    rw [hhw_def]
    have hpos : (I.hi : ℝ) - I.lo > 0 := by
      have : (I.lo : ℝ) < I.hi := by exact_mod_cast h
      linarith
    linarith
  have hfc_bound : evalFunc1 e c < (dI.hi : ℝ) * hw := by linarith
  have hfc_correct := evalInterval1_correct e hsupp (c : ℝ) (IntervalRat.singleton c)
    (IntervalRat.mem_singleton c)
  simp only [IntervalRat.mem_def] at hfc_correct
  have hfc_lo_le : (fc.lo : ℝ) ≤ evalFunc1 e c := hfc_correct.1
  have hfc_lo_bound : (fc.lo : ℝ) < (dI.hi : ℝ) * hw := by linarith
  have hdiv : (fc.lo : ℝ) / dI.hi ≥ (hw : ℝ) := by
    rw [ge_iff_le, le_div_iff_of_neg hdI_hi_neg_real]
    have h : (hw : ℝ) * dI.hi = (dI.hi : ℝ) * hw := by ring
    rw [h]
    linarith
  exact hdiv

-- Note: strictMonoOn_of_deriv_pos_interval and strictAntiOn_of_deriv_neg_interval
-- are already defined in LeanCert.Engine.Optimize

/-! ### Generic MVT bounds on f(c)

These lemmas give bounds on `evalFunc1 e c` (the true function value at the midpoint)
rather than on interval enclosures. This allows them to be used with any interval
that contains f(c), whether from `evalInterval1` or `TaylorModel.valueAtCenterInterval`. -/

/-- Generic MVT bound: If f' ≥ dI.lo > 0 (increasing) and f(I.lo) > 0,
    then f(c) > dI.lo * hw where c = midpoint and hw = half-width.
    This is the core analytic fact used for Newton contraction contradictions. -/
lemma mvt_fc_lower_bound_pos_increasing
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (_hdI_lo_pos : 0 < (derivInterval e (fun _ => I) 0).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_pos : 0 < evalFunc1 e I.lo) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    evalFunc1 e c > (dI.lo : ℝ) * hw := by
  intro c hw dI
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ => (hderiv ξ hξ).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hmvt := mvt_lower_bound e hsupp hvar0 I dI.lo hderiv_lo hCont I.lo c hIlo_in_I hc_in_I
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    linarith
  specialize hmvt hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  calc evalFunc1 e c ≥ evalFunc1 e I.lo + dI.lo * hw := by linarith
    _ > 0 + dI.lo * hw := by linarith
    _ = dI.lo * hw := by ring

/-- Generic MVT bound: If f' ≥ dI.lo > 0 (increasing) and f(I.hi) < 0,
    then f(c) < -dI.lo * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_upper_bound_pos_increasing
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (_hdI_lo_pos : 0 < (derivInterval e (fun _ => I) 0).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_neg : evalFunc1 e I.hi < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    evalFunc1 e c < -((dI.lo : ℝ) * hw) := by
  intro c hw dI
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ => (hderiv ξ hξ).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hmvt := mvt_lower_bound e hsupp hvar0 I dI.lo hderiv_lo hCont c I.hi hc_in_I hIhi_in_I
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    linarith
  specialize hmvt hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  calc evalFunc1 e c ≤ evalFunc1 e I.hi - dI.lo * hw := by linarith
    _ < 0 - dI.lo * hw := by linarith
    _ = -(dI.lo * hw) := by ring

/-- Generic MVT bound: If f' ≤ dI.hi < 0 (decreasing) and f(I.lo) < 0,
    then f(c) < dI.hi * hw where c = midpoint and hw = half-width.
    Since dI.hi < 0 and hw > 0, we have dI.hi * hw < 0, so f(c) < 0. -/
lemma mvt_fc_upper_bound_neg_decreasing
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_hi_neg : (derivInterval e (fun _ => I) 0).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_neg : evalFunc1 e I.lo < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    evalFunc1 e c < (dI.hi : ℝ) * hw := by
  intro c hw dI
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ => (hderiv ξ hξ).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hmvt := mvt_upper_bound e hsupp hvar0 I dI.hi hderiv_hi hCont (I.lo : ℝ) (c : ℝ) hIlo_in_I hc_in_I
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    linarith
  specialize hmvt hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = (hw : ℝ) := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  have hfc_upper : evalFunc1 e c ≤ evalFunc1 e I.lo + (dI.hi : ℝ) * hw := by linarith
  calc evalFunc1 e c ≤ evalFunc1 e I.lo + dI.hi * hw := hfc_upper
    _ < 0 + dI.hi * hw := by linarith
    _ = dI.hi * hw := by ring

/-- Generic MVT bound: If f' ≤ dI.hi < 0 (decreasing) and f(I.hi) > 0,
    then f(c) > -dI.hi * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_lower_bound_neg_decreasing
    (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (hI_nonsingleton : I.lo < I.hi)
    (hdI_hi_neg : (derivInterval e (fun _ => I) 0).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_pos : 0 < evalFunc1 e I.hi) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivInterval e (fun _ => I) 0
    evalFunc1 e c > -((dI.hi : ℝ) * hw) := by
  intro c hw dI
  have hderiv := deriv_in_derivInterval e hsupp hvar0 I
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ => (hderiv ξ hξ).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hmvt := mvt_upper_bound e hsupp hvar0 I dI.hi hderiv_hi hCont (c : ℝ) (I.hi : ℝ) hc_in_I hIhi_in_I
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    linarith
  specialize hmvt hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = (hw : ℝ) := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2
      push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  have hfc_lower : evalFunc1 e c ≥ evalFunc1 e I.hi - (dI.hi : ℝ) * hw := by linarith
  have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_hi_neg
  have hhw_pos : (0 : ℝ) < hw := by
    have h : I.lo < I.hi := hI_nonsingleton
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2
      push_cast; ring
    rw [hhw_def]
    have hpos : (I.hi : ℝ) - I.lo > 0 := by
      have : (I.lo : ℝ) < I.hi := by exact_mod_cast h
      linarith
    linarith
  calc evalFunc1 e c ≥ evalFunc1 e I.hi - dI.hi * hw := hfc_lower
    _ > 0 - dI.hi * hw := by linarith
    _ = -(dI.hi * hw) := by ring

end LeanCert.Engine
