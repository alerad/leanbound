/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert
import LeanCert.Engine.TaylorModel.Log1p
import LeanCert.Engine.Integrate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Verified Computation of li(2) - The Ramanujan-Soldner Constant

This file provides certified bounds on li(2) = ∫₀² dt/log(t) ≈ 1.0451637801...
using the symmetric combination form which makes the integral absolutely convergent.

## Main results

* `li2` - Definition of li(2) via the symmetric integral
* `li2_upper` - Upper bound: li(2) ≤ 2
* `li2_pos` - Positivity: 0 < li(2)
* `li2_bounds` - Certified bounds: li(2) ∈ [1.039, 1.06]

## Mathematical Background

The logarithmic integral li(x) = ∫₀ˣ dt/log(t) has a singularity at t=1.
For li(2), we use Tao's trick: rewrite using the substitution u = t-1:

  li(2) = ∫₀² dt/log(t) = ∫₋₁¹ du/log(1+u)

By principal value symmetry around u=0:

  li(2) = ∫₀¹ (1/log(1+u) + 1/log(1-u)) du

The key insight (proven in Log1p.lean) is that g(u) = 1/log(1+u) + 1/log(1-u)
has a REMOVABLE SINGULARITY at u=0 with limit 1. This makes the integral
absolutely convergent!

## References

* Tao's Zulip discussion on li(2) computation (January 2026)
* PNT#759: Verify li(2) ≈ 1.0451
-/

open MeasureTheory LeanCert.Engine.TaylorModel
open LeanCert.Core
open LeanCert.Validity.Integration
open scoped ENNReal

/-! ### Helper definitions for certified integral bounds via native_decide -/

/-- Boolean checker for integral lower bounds using `integratePartitionWithInv`. -/
def checkIntegralLowerBound (e : Expr) (I : IntervalRat) (n : ℕ) (c : ℚ) : Bool :=
  match integratePartitionWithInv e I n with
  | some J => decide (c ≤ J.lo)
  | none => false

/-- Boolean checker for integral upper bounds using `integratePartitionWithInv`. -/
def checkIntegralUpperBound (e : Expr) (I : IntervalRat) (n : ℕ) (c : ℚ) : Bool :=
  match integratePartitionWithInv e I n with
  | some J => decide (J.hi ≤ c)
  | none => false

/-- Bridge theorem: if `checkIntegralLowerBound` returns true, the integral is ≥ c. -/
theorem integral_lower_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (c : ℚ)
    (hcheck : checkIntegralLowerBound e I n c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) MeasureTheory.volume I.lo I.hi) :
    (c : ℝ) ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := by
  unfold checkIntegralLowerBound at hcheck
  cases hbound : integratePartitionWithInv e I n with
  | none => simp [hbound] at hcheck
  | some J =>
    simp only [hbound, decide_eq_true_eq] at hcheck
    have hmem := integratePartitionWithInv_correct e hsupp I n hn J hbound hInt
    simp only [IntervalRat.mem_def] at hmem
    calc (c : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast hcheck
      _ ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := hmem.1

/-- Bridge theorem: if `checkIntegralUpperBound` returns true, the integral is ≤ c. -/
theorem integral_upper_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (c : ℚ)
    (hcheck : checkIntegralUpperBound e I n c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) MeasureTheory.volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  unfold checkIntegralUpperBound at hcheck
  cases hbound : integratePartitionWithInv e I n with
  | none => simp [hbound] at hcheck
  | some J =>
    simp only [hbound, decide_eq_true_eq] at hcheck
    have hmem := integratePartitionWithInv_correct e hsupp I n hn J hbound hInt
    simp only [IntervalRat.mem_def] at hmem
    calc ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (J.hi : ℝ) := hmem.2
      _ ≤ (c : ℝ) := by exact_mod_cast hcheck

namespace Li2

/-! ### Definition of li(2) -/

/-- The symmetric log combination g(t) = 1/log(1+t) + 1/log(1-t).
    This is the integrand for computing li(2). -/
noncomputable def g (t : ℝ) : ℝ := symmetricLogCombination t

/-- li(2) defined as the integral of the symmetric combination on [0, 1].
    This is equivalent to the principal value integral ∫₀² dt/log(t). -/
noncomputable def li2 : ℝ := ∫ t in (0:ℝ)..1, g t

/-! ### Basic Properties -/

/-- The integrand g(t) equals 1/log(1+t) + 1/log(1-t) -/
theorem g_eq (t : ℝ) : g t = 1 / Real.log (1 + t) + 1 / Real.log (1 - t) := rfl

/-- g(t) has an alternative form: log(1-t²)/(log(1+t)·log(1-t)) -/
theorem g_alt (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    g t = Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) :=
  symmetricLogCombination_alt t ht_pos ht_lt

/-- g(t) → 1 as t → 0⁺ (the removable singularity) -/
theorem g_tendsto_one :
    Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  symmetricLogCombination_tendsto_one

/-- |g(t)| ≤ 2 for t ∈ (0, 1/2] -/
theorem g_bounded (t : ℝ) (ht_pos : 0 < t) (ht_le : t < 1/2) :
    |g t| ≤ 2 :=
  symmetricLogCombination_bounded t ht_pos ht_le

/-! ### Positivity and global upper bound -/

/-- g(t) > 0 for t ∈ (0, 1). -/
theorem g_pos (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) : 0 < g t := by
  have h1mt2_pos : 0 < 1 - t^2 := by nlinarith [sq_nonneg t]
  have h1mt2_lt1 : 1 - t^2 < 1 := by nlinarith [sq_nonneg t, ht_lt]
  have hlog1mt2_neg : Real.log (1 - t^2) < 0 := Real.log_neg h1mt2_pos h1mt2_lt1
  have h1pt_gt1 : 1 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1mt_lt1 : 1 - t < 1 := by linarith
  have hlog1p_pos : 0 < Real.log (1 + t) := Real.log_pos h1pt_gt1
  have hlog1m_neg : Real.log (1 - t) < 0 := Real.log_neg h1mt_pos h1mt_lt1
  have hdenom_neg : Real.log (1 + t) * Real.log (1 - t) < 0 :=
    mul_neg_of_pos_of_neg hlog1p_pos hlog1m_neg
  have hpos :
      0 < Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) :=
    div_pos_of_neg_of_neg hlog1mt2_neg hdenom_neg
  simpa [g_alt t ht_pos ht_lt] using hpos

/-- g(t) ≤ 2 for t ∈ (0, 1). -/
theorem g_le_two (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) : g t ≤ 2 := by
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1pt_gt1 : 1 < 1 + t := by linarith
  have h1mt_lt1 : 1 - t < 1 := by linarith
  have hlog1p_pos : 0 < Real.log (1 + t) := Real.log_pos h1pt_gt1
  have hlog1m_neg : Real.log (1 - t) < 0 := Real.log_neg h1mt_pos h1mt_lt1
  have hlog1p_lb : t / (1 + t) ≤ Real.log (1 + t) := by
    have h := Real.one_sub_inv_le_log_of_pos h1pt_pos
    have h' : 1 - 1 / (1 + t) ≤ Real.log (1 + t) := by
      simpa [one_div] using h
    have h1 : t / (1 + t) = 1 - 1 / (1 + t) := by field_simp; ring
    calc t / (1 + t) = 1 - 1 / (1 + t) := h1
      _ ≤ Real.log (1 + t) := h'
  have hlog1m_ub : Real.log (1 - t) ≥ -t / (1 - t) := by
    have h := Real.one_sub_inv_le_log_of_pos h1mt_pos
    have h' : 1 - 1 / (1 - t) ≤ Real.log (1 - t) := by
      simpa [one_div] using h
    have h1 : -t / (1 - t) = 1 - 1 / (1 - t) := by field_simp; ring
    calc -t / (1 - t) = 1 - 1 / (1 - t) := h1
      _ ≤ Real.log (1 - t) := h'
  have hlog1p_inv_ub : 1 / Real.log (1 + t) ≤ (1 + t) / t := by
    rw [one_div, le_div_iff₀ ht_pos, inv_mul_le_iff₀ hlog1p_pos]
    have h1 : t = t / (1 + t) * (1 + t) := by field_simp
    calc t = t / (1 + t) * (1 + t) := h1
      _ ≤ Real.log (1 + t) * (1 + t) := by
        apply mul_le_mul_of_nonneg_right hlog1p_lb (le_of_lt h1pt_pos)
  have hlog1m_inv_ub : 1 / Real.log (1 - t) ≤ -(1 - t) / t := by
    have hneg_log : -Real.log (1 - t) > 0 := neg_pos.mpr hlog1m_neg
    have hneg_log_ub : -Real.log (1 - t) ≤ t / (1 - t) := by
      have h := hlog1m_ub
      have hdiv_neg : -t / (1 - t) = -(t / (1 - t)) := by ring
      rw [hdiv_neg] at h
      linarith
    have hinv_lb : (1 - t) / t ≤ 1 / (-Real.log (1 - t)) := by
      rw [div_le_div_iff₀ ht_pos hneg_log]
      calc (1 - t) * -Real.log (1 - t) = -Real.log (1 - t) * (1 - t) := by ring
        _ ≤ t / (1 - t) * (1 - t) := by
          apply mul_le_mul_of_nonneg_right hneg_log_ub (le_of_lt h1mt_pos)
        _ = t := by field_simp
        _ = 1 * t := by ring
    have hlog1m_ne : Real.log (1 - t) ≠ 0 := ne_of_lt hlog1m_neg
    calc 1 / Real.log (1 - t) = -(1 / -Real.log (1 - t)) := by field_simp [hlog1m_ne]
      _ ≤ -((1 - t) / t) := neg_le_neg hinv_lb
      _ = -(1 - t) / t := by ring
  calc
    g t = 1 / Real.log (1 + t) + 1 / Real.log (1 - t) := by rfl
    _ ≤ (1 + t) / t + (-(1 - t) / t) := add_le_add hlog1p_inv_ub hlog1m_inv_ub
    _ = ((1 + t) - (1 - t)) / t := by ring
    _ = 2 * t / t := by ring
    _ = 2 := by field_simp

/-! ### Upper Bound: li(2) ≤ 2 -/

/-- The integrand g is bounded on (0, 1/2] by 2. -/
theorem g_bounded_on_interval :
    ∀ t ∈ Set.Ioo (0:ℝ) (1/2), |g t| ≤ 2 := by
  intro t ⟨ht_pos, ht_lt⟩
  exact g_bounded t ht_pos ht_lt

/-- Crude upper bound: li(2) ≤ 2.
    This follows from |g(t)| ≤ 2 on a large portion of [0,1]. -/
theorem li2_upper_crude : li2 ≤ 2 := by
  have hInt : IntervalIntegrable g volume (0:ℝ) 1 := by
    -- Integrable on Ioo by boundedness, then lift to interval integrable.
    have hmeas : Measurable g := by
      have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
        Real.measurable_log.comp (measurable_const.add measurable_id)
      have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
        Real.measurable_log.comp (measurable_const.sub measurable_id)
      have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
      have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
      unfold g
      unfold symmetricLogCombination
      simpa [one_div] using hlog1p_inv.add hlog1m_inv
    have hInt_Ioo : IntegrableOn g (Set.Ioo (0:ℝ) 1) volume := by
      apply Measure.integrableOn_of_bounded
      · exact measure_Ioo_lt_top.ne
      · exact hmeas.aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
        exact ae_of_all _ (fun t ht =>
          by
            have hpos := g_pos t ht.1 ht.2
            have hle := g_le_two t ht.1 ht.2
            have habs : |g t| = g t := abs_of_pos hpos
            simpa [Real.norm_eq_abs, habs] using hle)
    have hab : (0:ℝ) ≤ 1 := by norm_num
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ:=volume) (f:=g) hab).2 hInt_Ioo
  have hInt_const : IntervalIntegrable (fun _ : ℝ => (2:ℝ)) volume (0:ℝ) 1 :=
    intervalIntegrable_const
  have hab : (0:ℝ) ≤ 1 := by norm_num
  have hmono : ∀ t ∈ Set.Ioo (0:ℝ) 1, g t ≤ (2:ℝ) := by
    intro t ht
    exact g_le_two t ht.1 ht.2
  have hle :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) (a:=0) (b:=1)
      (f:=g) (g:=fun _ : ℝ => (2:ℝ)) (hab:=hab) (hf:=hInt) (hg:=hInt_const) hmono
  -- Evaluate the constant integral.
  have hconst : (∫ t in (0:ℝ)..1, (2:ℝ)) = 2 := by
    simp [intervalIntegral.integral_const]
  simpa [li2, hconst] using hle

/-! ### Lower Bound: li(2) > 0 -/

/-- g(t) > 0 for small positive t (since g → 1 as t → 0⁺). -/
theorem g_pos_near_zero : ∃ δ > 0, ∀ t ∈ Set.Ioo (0:ℝ) δ, g t > 0 := by
  -- g(t) → 1 as t → 0⁺, so g(t) > 1/2 for small t
  have htendsto := g_tendsto_one
  rw [Metric.tendsto_nhdsWithin_nhds] at htendsto
  specialize htendsto (1/2) (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨δ, hδ_pos, hδ⟩ := htendsto
  use δ, hδ_pos
  intro t ⟨ht_pos, ht_lt⟩
  have hdist : dist t 0 < δ := by simp [abs_of_pos ht_pos]; exact ht_lt
  specialize hδ ht_pos hdist
  rw [Real.dist_eq] at hδ
  have h : g t > 1 - 1/2 := by
    have : |g t - 1| < 1/2 := hδ
    linarith [abs_sub_lt_iff.mp this]
  linarith

/-- li(2) > 0. -/
theorem li2_pos : 0 < li2 := by
  have hInt : IntervalIntegrable g volume (0:ℝ) 1 := by
    -- Reuse the integrability argument from li2_upper_crude.
    have hmeas : Measurable g := by
      have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
        Real.measurable_log.comp (measurable_const.add measurable_id)
      have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
        Real.measurable_log.comp (measurable_const.sub measurable_id)
      have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
      have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
      unfold g
      unfold symmetricLogCombination
      simpa [one_div] using hlog1p_inv.add hlog1m_inv
    have hInt_Ioo : IntegrableOn g (Set.Ioo (0:ℝ) 1) volume := by
      apply Measure.integrableOn_of_bounded
      · exact measure_Ioo_lt_top.ne
      · exact hmeas.aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
        exact ae_of_all _ (fun t ht =>
          by
            have hpos := g_pos t ht.1 ht.2
            have hle := g_le_two t ht.1 ht.2
            have habs : |g t| = g t := abs_of_pos hpos
            simpa [Real.norm_eq_abs, habs] using hle)
    have hab : (0:ℝ) ≤ 1 := by norm_num
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ:=volume) (f:=g) hab).2 hInt_Ioo
  have hpos : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 < g t := by
    intro t ht
    exact g_pos t ht.1 ht.2
  have hlt : (0:ℝ) < 1 := by norm_num
  have h :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (f:=g) (a:=0) (b:=1) hInt hpos hlt
  simpa [li2] using h

/-! ### Numerical Integration Strategy

To get bounds li(2) ∈ [1.04, 1.06], we split the integral:

  li(2) = ∫₀^ε g(t) dt + ∫_ε^{1-ε} g(t) dt + ∫_{1-ε}^1 g(t) dt

For ε = 0.01:
1. Near t=0: g(t) ≈ 1, so ∫₀^ε g(t) dt ≈ ε with error bounded by |g-1|·ε
2. Middle [ε, 1-ε]: Use numerical integration with interval arithmetic
3. Near t=1: Need bounds on g(t) for t close to 1

The middle integral is where most of the value lies.
-/

/-! ### Bounds on g(t) for the full interval -/

/-- For sufficiently small t, g(t) stays within (1/2, 3/2). -/
theorem g_near_one_for_small_t :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (0:ℝ) δ, 1/2 < g t ∧ g t < 3/2 := by
  have htendsto := g_tendsto_one
  rw [Metric.tendsto_nhdsWithin_nhds] at htendsto
  specialize htendsto (1/2) (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨δ, hδ_pos, hδ⟩ := htendsto
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht
  have hdist : dist t 0 < δ := by
    have ht_pos : 0 < t := ht.1
    simpa [Real.dist_eq, abs_of_pos ht_pos] using ht.2
  have hδ' : dist (g t) 1 < 1/2 := hδ ht.1 hdist
  have h' : |g t - 1| < 1/2 := by
    simpa [Real.dist_eq] using hδ'
  have h_left : 1 - g t < 1/2 := (abs_sub_lt_iff.mp h').2
  have h_right : g t - 1 < 1/2 := (abs_sub_lt_iff.mp h').1
  constructor <;> linarith

/-- For t ∈ [0.01, 0.49], we have |g(t)| ≤ 2 by the bounded theorem. -/
theorem g_bounded_middle (t : ℝ) (ht_lo : 1/100 ≤ t) (ht_hi : t ≤ 49/100) :
    |g t| ≤ 2 := by
  have ht_pos : 0 < t := by linarith
  have ht_lt : t < 1/2 := by linarith
  exact g_bounded t ht_pos ht_lt

/-! ### Interval arithmetic setup for the mid-range integral -/

/-- AST for g(t) = 1/log(1+t) + 1/log(1-t). -/
def g_expr : Expr :=
  Expr.add
    (Expr.inv (Expr.log (Expr.add (Expr.const 1) (Expr.var 0))))
    (Expr.inv (Expr.log (Expr.add (Expr.const 1) (Expr.neg (Expr.var 0)))))

theorem g_expr_supported : ExprSupportedWithInv g_expr := by
  unfold g_expr
  refine ExprSupportedWithInv.add ?_ ?_
  · refine ExprSupportedWithInv.inv ?_
    refine ExprSupportedWithInv.log ?_
    refine ExprSupportedWithInv.add ?_ ?_
    · exact ExprSupportedWithInv.const 1
    · exact ExprSupportedWithInv.var 0
  · refine ExprSupportedWithInv.inv ?_
    refine ExprSupportedWithInv.log ?_
    refine ExprSupportedWithInv.add ?_ ?_
    · exact ExprSupportedWithInv.const 1
    · refine ExprSupportedWithInv.neg ?_
      exact ExprSupportedWithInv.var 0

theorem g_expr_eval (t : ℝ) : Expr.eval (fun _ => t) g_expr = g t := by
  have hlog : (-t + 1) = (1 - t) := by ring
  have h :
      Expr.eval (fun _ => t) g_expr =
        1 / Real.log (1 + t) + 1 / Real.log (1 - t) := by
    simp [g_expr, Expr.eval, one_div, add_comm, hlog]
  simpa [g_eq] using h

/-- Alternative AST for g(t) = log(1-t²) / (log(1+t) · log(1-t)).
    This form gives MUCH better interval arithmetic bounds than g_expr
    because it avoids the cancellation in 1/log(1+t) + 1/log(1-t). -/
def g_alt_expr : Expr :=
  Expr.mul
    (Expr.log (Expr.add (Expr.const 1)
      (Expr.neg (Expr.mul (Expr.var 0) (Expr.var 0)))))
    (Expr.inv
      (Expr.mul
        (Expr.log (Expr.add (Expr.const 1) (Expr.var 0)))
        (Expr.log (Expr.add (Expr.const 1) (Expr.neg (Expr.var 0))))))

theorem g_alt_expr_supported : ExprSupportedWithInv g_alt_expr := by
  unfold g_alt_expr
  refine ExprSupportedWithInv.mul ?_ ?_
  · refine ExprSupportedWithInv.log ?_
    refine ExprSupportedWithInv.add ?_ ?_
    · exact ExprSupportedWithInv.const 1
    · refine ExprSupportedWithInv.neg ?_
      refine ExprSupportedWithInv.mul ?_ ?_
      · exact ExprSupportedWithInv.var 0
      · exact ExprSupportedWithInv.var 0
  · refine ExprSupportedWithInv.inv ?_
    refine ExprSupportedWithInv.mul ?_ ?_
    · refine ExprSupportedWithInv.log ?_
      refine ExprSupportedWithInv.add ?_ ?_
      · exact ExprSupportedWithInv.const 1
      · exact ExprSupportedWithInv.var 0
    · refine ExprSupportedWithInv.log ?_
      refine ExprSupportedWithInv.add ?_ ?_
      · exact ExprSupportedWithInv.const 1
      · refine ExprSupportedWithInv.neg ?_
        exact ExprSupportedWithInv.var 0

theorem g_alt_expr_eval (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    Expr.eval (fun _ => t) g_alt_expr = g t := by
  have hsq : t * t = t^2 := by ring
  have h1mt2' : (1:ℝ) + -(t * t) = 1 - t^2 := by ring
  have hlog1m : (1:ℝ) + -t = 1 - t := by ring
  -- Evaluate the Expr to get the raw form
  simp only [g_alt_expr, Expr.eval]
  -- Now we need: Real.log (↑1 + -(t * t)) * (Real.log (↑1 + t) * Real.log (↑1 + -t))⁻¹
  --            = Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t))
  -- First normalize the coerced 1
  have h1_eq : (↑(1:ℚ) : ℝ) = (1:ℝ) := by norm_cast
  simp only [h1_eq]
  -- Now: Real.log (1 + -(t * t)) * (Real.log (1 + t) * Real.log (1 + -t))⁻¹
  rw [h1mt2', hlog1m]
  -- Now: Real.log (1 - t^2) * (Real.log (1 + t) * Real.log (1 - t))⁻¹ = g t
  -- Convert mul inv to div: a * b⁻¹ = a / b
  rw [← div_eq_mul_inv]
  -- Now: Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) = g t
  exact (g_alt t ht_pos ht_lt).symm

/-- Mid-range interval for numerical integration. -/
def g_mid_interval : IntervalRat := ⟨1/100, 99/100, by norm_num⟩

theorem g_intervalIntegrable_mid :
    IntervalIntegrable g volume (g_mid_interval.lo : ℝ) (g_mid_interval.hi : ℝ) := by
  have hmeas : Measurable g := by
    have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
      Real.measurable_log.comp (measurable_const.sub measurable_id)
    have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
    have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
    unfold g
    unfold symmetricLogCombination
    simpa [one_div] using hlog1p_inv.add hlog1m_inv
  have hInt_Ioo : IntegrableOn g
      (Set.Ioo (g_mid_interval.lo : ℝ) (g_mid_interval.hi : ℝ)) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht => by
        have ht_pos : 0 < t := by
          have hlo : (0 : ℝ) < (g_mid_interval.lo : ℝ) := by
            norm_num [g_mid_interval]
          linarith [ht.1, hlo]
        have ht_lt1 : t < 1 := by
          have hhi : (g_mid_interval.hi : ℝ) < 1 := by
            norm_num [g_mid_interval]
          linarith [ht.2, hhi]
        have hpos := g_pos t ht_pos ht_lt1
        have hle := g_le_two t ht_pos ht_lt1
        have habs : |g t| = g t := abs_of_pos hpos
        simpa [Real.norm_eq_abs, habs] using hle)
  have hab : (g_mid_interval.lo : ℝ) ≤ g_mid_interval.hi := by
    exact_mod_cast g_mid_interval.le
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ:=volume) (f:=g) hab).2 hInt_Ioo

def g_mid_bound : Option IntervalRat :=
  integrateInterval1WithInv g_expr g_mid_interval

theorem g_mid_integral_mem (bound : IntervalRat) (hbound : g_mid_bound = some bound) :
    ∫ t in (g_mid_interval.lo : ℝ)..(g_mid_interval.hi : ℝ), g t ∈ bound := by
  have hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) g_expr) volume
      (g_mid_interval.lo : ℝ) (g_mid_interval.hi : ℝ) := by
    simpa [g_expr_eval] using g_intervalIntegrable_mid
  have hmem :=
    integrateInterval1WithInv_correct g_expr g_expr_supported g_mid_interval bound
      (by simpa [g_mid_bound] using hbound) hInt
  simpa [g_expr_eval] using hmem

/-! ### Explicit tail bounds

For t ∈ (0, 1/2), g(t) > 0 and g(t) ≤ 2.
Combined with numerical integration on middle intervals, this suffices. -/

/-- The integral on [0, ε] is bounded below by 0 and above by 2ε.
    This follows from 0 < g(t) ≤ 2 for t ∈ (0, 1). -/
theorem g_integral_tail_upper (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∫ t in (0:ℝ)..ε, g t ≤ 2 * ε := by
  have hInt : IntervalIntegrable g volume (0:ℝ) ε := by
    have hmeas : Measurable g := by
      have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
        Real.measurable_log.comp (measurable_const.add measurable_id)
      have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
        Real.measurable_log.comp (measurable_const.sub measurable_id)
      have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
      have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
      unfold g symmetricLogCombination
      simpa [one_div] using hlog1p_inv.add hlog1m_inv
    have hInt_Ioo : IntegrableOn g (Set.Ioo (0:ℝ) ε) volume := by
      apply Measure.integrableOn_of_bounded
      · exact measure_Ioo_lt_top.ne
      · exact hmeas.aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
        exact ae_of_all _ (fun t ht => by
          have ht_lt1 : t < 1 := lt_trans ht.2 hε_lt
          have hpos := g_pos t ht.1 ht_lt1
          have hle := g_le_two t ht.1 ht_lt1
          have habs : |g t| = g t := abs_of_pos hpos
          simpa [Real.norm_eq_abs, habs] using hle)
    have hab : (0:ℝ) ≤ ε := le_of_lt hε_pos
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hInt_Ioo
  have hInt_const : IntervalIntegrable (fun _ : ℝ => (2:ℝ)) volume (0:ℝ) ε :=
    intervalIntegrable_const
  have hmono : ∀ t ∈ Set.Ioo (0:ℝ) ε, g t ≤ (2:ℝ) := by
    intro t ht
    have ht_lt1 : t < 1 := lt_trans ht.2 hε_lt
    exact g_le_two t ht.1 ht_lt1
  have hle :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume)
      (hab := le_of_lt hε_pos) (hf := hInt) (hg := hInt_const) hmono
  have hconst : ∫ t in (0:ℝ)..ε, (2:ℝ) = 2 * ε := by
    simp [intervalIntegral.integral_const]; ring
  linarith

/-- The integral on [1-ε, 1] is bounded above by 2ε for small ε > 0. -/
theorem g_integral_right_tail_upper (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∫ t in (1 - ε:ℝ)..1, g t ≤ 2 * ε := by
  have h1mε_pos : 0 < 1 - ε := by linarith
  have h1mε_lt1 : 1 - ε < 1 := by linarith
  have hInt : IntervalIntegrable g volume (1 - ε:ℝ) 1 := by
    have hmeas : Measurable g := by
      have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
        Real.measurable_log.comp (measurable_const.add measurable_id)
      have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
        Real.measurable_log.comp (measurable_const.sub measurable_id)
      have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
      have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
      unfold g symmetricLogCombination
      simpa [one_div] using hlog1p_inv.add hlog1m_inv
    have hInt_Ioo : IntegrableOn g (Set.Ioo (1 - ε:ℝ) 1) volume := by
      apply Measure.integrableOn_of_bounded
      · exact measure_Ioo_lt_top.ne
      · exact hmeas.aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
        exact ae_of_all _ (fun t ht => by
          have ht_pos : 0 < t := by linarith [ht.1, h1mε_pos]
          have hpos := g_pos t ht_pos ht.2
          have hle := g_le_two t ht_pos ht.2
          have habs : |g t| = g t := abs_of_pos hpos
          simpa [Real.norm_eq_abs, habs] using hle)
    have hab : (1 - ε : ℝ) ≤ 1 := by linarith
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hInt_Ioo
  have hInt_const : IntervalIntegrable (fun _ : ℝ => (2:ℝ)) volume (1 - ε:ℝ) 1 :=
    intervalIntegrable_const
  have hmono : ∀ t ∈ Set.Ioo (1 - ε:ℝ) 1, g t ≤ (2:ℝ) := by
    intro t ht
    have ht_pos : 0 < t := by linarith [ht.1, h1mε_pos]
    exact g_le_two t ht_pos ht.2
  have hab : (1 - ε : ℝ) ≤ 1 := by linarith
  have hle :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume)
      (hab := hab) (hf := hInt) (hg := hInt_const) hmono
  have hconst : ∫ t in (1 - ε:ℝ)..1, (2:ℝ) = 2 * ε := by
    simp [intervalIntegral.integral_const]; ring
  linarith

/-! ### Verified Log Bounds via LeanCert

We use LeanCert's interval arithmetic to establish verified bounds on logarithms. -/

open LeanCert.Core.IntervalRat in
/-- log(2) < 72/100 = 0.72.
    Verified via interval arithmetic: logPointComputable 2 20 has upper bound < 0.72 -/
theorem log_2_lt : Real.log 2 < (72:ℚ)/100 := by
  have hmem := mem_logPointComputable (by norm_num : (0:ℚ) < 2) 20
  have hhi := hmem.2  -- Real.log ↑(2:ℚ) ≤ (logPointComputable 2 20).hi
  have hcomp : (logPointComputable 2 20).hi < (72:ℚ)/100 := by native_decide
  have hcomp_real : ((logPointComputable 2 20).hi : ℝ) < ((72:ℚ)/100 : ℝ) := by exact_mod_cast hcomp
  have heq : Real.log ((2:ℚ) : ℝ) = Real.log (2:ℝ) := by norm_cast
  rw [← heq]
  linarith

open LeanCert.Core.IntervalRat in
/-- log(2) > 69/100 = 0.69.
    Verified via interval arithmetic: logPointComputable 2 20 has lower bound > 0.69 -/
theorem log_2_gt : (69:ℚ)/100 < Real.log 2 := by
  have hmem := mem_logPointComputable (by norm_num : (0:ℚ) < 2) 20
  have hlo := hmem.1  -- (logPointComputable 2 20).lo ≤ Real.log ↑(2:ℚ)
  have hcomp : (69:ℚ)/100 < (logPointComputable 2 20).lo := by native_decide
  have hcomp_real : ((69:ℚ)/100 : ℝ) < ((logPointComputable 2 20).lo : ℝ) := by exact_mod_cast hcomp
  have heq : Real.log ((2:ℚ) : ℝ) = Real.log (2:ℝ) := by norm_cast
  rw [← heq]
  linarith

open LeanCert.Core.IntervalRat in
/-- log(10) > 23/10 = 2.3.
    Verified via interval arithmetic: logPointComputable 10 20 has lower bound > 2.3 -/
theorem log_10_gt : (23:ℚ)/10 < Real.log 10 := by
  have hmem := mem_logPointComputable (by norm_num : (0:ℚ) < 10) 20
  have hlo := hmem.1  -- (logPointComputable 10 20).lo ≤ Real.log ↑(10:ℚ)
  have hcomp : (23:ℚ)/10 < (logPointComputable 10 20).lo := by native_decide
  have hcomp_real : ((23:ℚ)/10 : ℝ) < ((logPointComputable 10 20).lo : ℝ) := by exact_mod_cast hcomp
  have heq : Real.log ((10:ℚ) : ℝ) = Real.log (10:ℝ) := by norm_cast
  rw [← heq]
  linarith

open LeanCert.Core.IntervalRat in
/-- 1/log(2) > 14/10 = 1.4.
    Verified via interval arithmetic. -/
theorem inv_log_2_gt : (14:ℝ)/10 < 1 / Real.log 2 := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2:ℝ))
  have hmem := mem_logPointComputable (by norm_num : (0:ℚ) < 2) 20
  have hhi := hmem.2  -- Real.log ↑(2:ℚ) ≤ (logPointComputable 2 20).hi
  -- The upper bound is < 5/7, verified by native_decide
  have hcomp : (logPointComputable 2 20).hi < (5:ℚ)/7 := by native_decide
  have hcomp_real : ((logPointComputable 2 20).hi : ℝ) < ((5:ℚ)/7 : ℝ) := by exact_mod_cast hcomp
  have heq : Real.log ((2:ℚ) : ℝ) = Real.log (2:ℝ) := by norm_cast
  have hlog_lt : Real.log 2 < 5/7 := by
    rw [← heq]
    linarith
  have h57_pos : (0:ℝ) < 5/7 := by norm_num
  -- 1 / log(2) > 1 / (5/7) = 7/5 = 1.4
  have h1 : 1 / (5/7 : ℝ) < 1 / Real.log 2 := by
    apply one_div_lt_one_div_of_lt hlog_pos hlog_lt
  have h2 : (1:ℝ) / (5/7) = 7/5 := by norm_num
  rw [h2] at h1
  have h14 : (14:ℝ)/10 = 7/5 := by norm_num
  rw [h14]
  exact h1

/-! ### Analytic Tail Bounds

For the tiny tail intervals [0, 0.00001] and [0.99999, 1], we prove
explicit lower bounds on g(t) using log inequalities. -/

/-- For t ∈ [99999/100000, 1), g(t) > 13/10.
    Proof: g(t) = 1/log(1+t) + 1/log(1-t).
    - 1/log(1+t) > 1/log(2) > 1.4 since log(1+t) ≤ log(2) and log(2) < 0.72
    - 1/log(1-t) > -1/10 since log(1-t) < -5*log(10) < -11.5 for t ≥ 0.99999
    - Therefore g(t) > 1.4 - 0.1 = 1.3 -/
theorem g_lower_near_one (t : ℝ) (ht_lo : 99999/100000 ≤ t) (ht_lt : t < 1) :
    (13:ℝ)/10 < g t := by
  -- Setup: t ∈ [0.99999, 1)
  have ht_pos : 0 < t := by linarith
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1pt_le2 : 1 + t ≤ 2 := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1mt_le : 1 - t ≤ 1/100000 := by linarith

  -- Part 1: 1/log(1+t) > 1.4
  have hlog1p_pos : 0 < Real.log (1 + t) := Real.log_pos (by linarith : 1 < 1 + t)
  have hlog1p_le : Real.log (1 + t) ≤ Real.log 2 := Real.log_le_log h1pt_pos h1pt_le2
  have hinv1p : 1 / Real.log 2 ≤ 1 / Real.log (1 + t) := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2:ℝ))
    exact one_div_le_one_div_of_le hlog1p_pos hlog1p_le
  have hinv1p_gt : 14/10 < 1 / Real.log (1 + t) := lt_of_lt_of_le inv_log_2_gt hinv1p

  -- Part 2: 1/log(1-t) > -1/10
  -- log(1-t) ≤ log(1/100000) = -log(100000) < -5*log(10) < -11.5
  have hlog1m_neg : Real.log (1 - t) < 0 := Real.log_neg h1mt_pos (by linarith : 1 - t < 1)
  have hlog1m_le : Real.log (1 - t) ≤ Real.log (1/100000) := Real.log_le_log h1mt_pos h1mt_le
  have hlog_inv : Real.log ((1:ℝ)/100000) = -Real.log 100000 := by
    have h100k_pos : (0:ℝ) < 100000 := by norm_num
    rw [one_div, Real.log_inv (100000:ℝ)]
  have hlog100k : Real.log (100000:ℝ) = 5 * Real.log 10 := by
    have h : (100000:ℝ) = 10^5 := by norm_num
    rw [h, Real.log_pow]
    ring
  have hlog10_gt : (23:ℝ)/10 < Real.log 10 := log_10_gt
  have hlog100k_gt : (115:ℝ)/10 < Real.log 100000 := by
    rw [hlog100k]
    calc (115:ℝ)/10 = 5 * (23/10) := by norm_num
      _ < 5 * Real.log 10 := by nlinarith
  have hlog1m_lt : Real.log (1 - t) < -(115/10) := by
    calc Real.log (1 - t) ≤ Real.log (1/100000) := hlog1m_le
      _ = -Real.log 100000 := hlog_inv
      _ < -(115/10) := by linarith
  -- 1/log(1-t) > 1/(-11.5) = -10/115 > -1/10
  have hinv1m_gt : -(1:ℝ)/10 < 1 / Real.log (1 - t) := by
    -- log(1-t) < -11.5 < 0, so 1/log(1-t) > 1/(-11.5) = -10/115 > -1/10
    have hneg115 : -(115/10 : ℝ) < 0 := by norm_num
    have hlog1m_ne : Real.log (1 - t) ≠ 0 := ne_of_lt hlog1m_neg
    have hneg115_ne : (-(115/10) : ℝ) ≠ 0 := by norm_num
    -- For a < b < 0: 1/b < 1/a (inequality flips)
    -- We have log(1-t) < -11.5 < 0, so 1/(-11.5) < 1/log(1-t)
    have h1 : 1 / (-(115/10) : ℝ) < 1 / Real.log (1 - t) := by
      rw [one_div, one_div]
      -- Need (-(115/10))⁻¹ < (log(1-t))⁻¹
      -- For a < b < 0: b⁻¹ < a⁻¹
      have hiff := inv_lt_inv_of_neg hneg115 hlog1m_neg
      -- hiff : (-(115/10))⁻¹ < (log(1-t))⁻¹ ↔ log(1-t) < -(115/10)
      exact hiff.mpr hlog1m_lt
    have h2 : (1:ℝ) / (-(115/10)) = -10/115 := by norm_num
    rw [h2] at h1
    calc -(1:ℝ)/10 < -10/115 := by norm_num
      _ < 1 / Real.log (1 - t) := h1

  -- Combine: g(t) = 1/log(1+t) + 1/log(1-t) > 1.4 - 0.1 = 1.3
  simp only [g_eq, one_div]
  calc (13:ℝ)/10 = 14/10 + (-(1/10)) := by norm_num
    _ < (Real.log (1 + t))⁻¹ + (Real.log (1 - t))⁻¹ := by
        have h1 : 14/10 < (Real.log (1 + t))⁻¹ := by simpa [one_div] using hinv1p_gt
        have h2 : -(1:ℝ)/10 < (Real.log (1 - t))⁻¹ := by simpa [one_div] using hinv1m_gt
        linarith

/-! ### Integral Decomposition

We decompose li(2) = ∫₀¹ g(t) dt into a sum of integrals over subintervals.
This allows us to combine numerical bounds on middle intervals with
analytic bounds on tiny tail intervals.

Partition: [0, 1] = [0, δ₁] ∪ [δ₁, δ₂] ∪ ... ∪ [δₙ, 1]
where δᵢ are chosen to align with our computed intervals.
-/

/-- g is integrable on any closed subinterval of (0, 1). -/
theorem g_intervalIntegrable (a b : ℝ) (ha_pos : 0 < a) (hb_lt : b < 1) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  have hmeas : Measurable g := by
    have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
      Real.measurable_log.comp (measurable_const.sub measurable_id)
    have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
    have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
    unfold g symmetricLogCombination
    simpa [one_div] using hlog1p_inv.add hlog1m_inv
  have hInt_Ioo : IntegrableOn g (Set.Ioo a b) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht => by
        have ht_pos : 0 < t := lt_of_lt_of_le ha_pos (le_of_lt ht.1)
        have ht_lt1 : t < 1 := lt_of_lt_of_le ht.2 (le_of_lt hb_lt)
        have hpos := g_pos t ht_pos ht_lt1
        have hle := g_le_two t ht_pos ht_lt1
        have habs : |g t| = g t := abs_of_pos hpos
        simpa [Real.norm_eq_abs, habs] using hle)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hInt_Ioo

/-- Key lemma: adjacent integrals can be combined. -/
theorem g_integral_add_adjacent (a b c : ℝ) (ha_pos : 0 < a) (hc_lt : c < 1)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ t in a..b, g t) + (∫ t in b..c, g t) = ∫ t in a..c, g t := by
  have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
  have hb_lt : b < 1 := lt_of_le_of_lt hbc hc_lt
  have hInt_ab := g_intervalIntegrable a b ha_pos hb_lt hab
  have hInt_bc := g_intervalIntegrable b c hb_pos hc_lt hbc
  exact intervalIntegral.integral_add_adjacent_intervals hInt_ab hInt_bc

/-- The partition points for our decomposition.
    Chosen to match our computed intervals. -/
def partitionPoints : List ℚ :=
  [0, 1/100000, 1/10000, 1/1000, 999/1000, 9999/10000, 99999/100000, 1]

/-- Decomposition of li(2) into 7 subintegrals.
    li(2) = ∫[0, 1/100000] + ∫[1/100000, 1/10000] + ∫[1/10000, 1/1000]
          + ∫[1/1000, 999/1000] + ∫[999/1000, 9999/10000]
          + ∫[9999/10000, 99999/100000] + ∫[99999/100000, 1] -/
theorem li2_decomposition :
    li2 = (∫ t in (0:ℝ)..(1/100000), g t)
        + (∫ t in (1/100000:ℝ)..(1/10000), g t)
        + (∫ t in (1/10000:ℝ)..(1/1000), g t)
        + (∫ t in (1/1000:ℝ)..(999/1000), g t)
        + (∫ t in (999/1000:ℝ)..(9999/10000), g t)
        + (∫ t in (9999/10000:ℝ)..(99999/100000), g t)
        + (∫ t in (99999/100000:ℝ)..1, g t) := by
  unfold li2
  -- g is IntervalIntegrable on [0, 1] (proven in li2_upper_crude)
  have hInt : IntervalIntegrable g volume (0:ℝ) 1 := by
    have hmeas : Measurable g := by
      have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
        Real.measurable_log.comp (measurable_const.add measurable_id)
      have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
        Real.measurable_log.comp (measurable_const.sub measurable_id)
      have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
      have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
      unfold g symmetricLogCombination
      simpa [one_div] using hlog1p_inv.add hlog1m_inv
    have hInt_Ioo : IntegrableOn g (Set.Ioo (0:ℝ) 1) volume := by
      apply Measure.integrableOn_of_bounded
      · exact measure_Ioo_lt_top.ne
      · exact hmeas.aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
        exact ae_of_all _ (fun t ht => by
          have hpos := g_pos t ht.1 ht.2
          have hle := g_le_two t ht.1 ht.2
          have habs : |g t| = g t := abs_of_pos hpos
          simpa [Real.norm_eq_abs, habs] using hle)
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).2 hInt_Ioo
  -- Split repeatedly using integral_add_adjacent_intervals
  -- Helper to prove Icc subset from boundary conditions
  have hIcc_sub : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → Set.Icc a b ⊆ Set.Icc (0:ℝ) 1 := by
    intro a b ha hb
    exact Set.Icc_subset_Icc ha hb
  have h1 : ∫ t in (0:ℝ)..1, g t =
      (∫ t in (0:ℝ)..(99999/100000), g t) + (∫ t in (99999/100000:ℝ)..1, g t) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 99999/100000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (99999:ℝ)/100000 ≤ 1),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
  have h2 : ∫ t in (0:ℝ)..(99999/100000), g t =
      (∫ t in (0:ℝ)..(9999/10000), g t) + (∫ t in (9999/10000:ℝ)..(99999/100000), g t) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 9999/10000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (9999:ℝ)/10000 ≤ 99999/100000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
  have h3 : ∫ t in (0:ℝ)..(9999/10000), g t =
      (∫ t in (0:ℝ)..(999/1000), g t) + (∫ t in (999/1000:ℝ)..(9999/10000), g t) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 999/1000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (999:ℝ)/1000 ≤ 9999/10000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
  have h4 : ∫ t in (0:ℝ)..(999/1000), g t =
      (∫ t in (0:ℝ)..(1/1000), g t) + (∫ t in (1/1000:ℝ)..(999/1000), g t) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/1000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (1:ℝ)/1000 ≤ 999/1000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
  have h5 : ∫ t in (0:ℝ)..(1/1000), g t =
      (∫ t in (0:ℝ)..(1/10000), g t) + (∫ t in (1/10000:ℝ)..(1/1000), g t) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/10000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (1:ℝ)/10000 ≤ 1/1000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
  have h6 : ∫ t in (0:ℝ)..(1/10000), g t =
      (∫ t in (0:ℝ)..(1/100000), g t) + (∫ t in (1/100000:ℝ)..(1/10000), g t) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/100000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
      (hInt.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (1:ℝ)/100000 ≤ 1/10000),
                                    Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hIcc_sub _ _ (by norm_num) (by norm_num)))
  -- Combine all the splits
  rw [h1, h2, h3, h4, h5, h6]

/-- Lower bound on integral over an interval given pointwise lower bound. -/
theorem integral_lower_bound (a b c : ℝ) (ha_pos : 0 < a) (hb_lt : b < 1)
    (hab : a ≤ b)
    (hbound : ∀ t, a ≤ t → t ≤ b → c ≤ g t) :
    c * (b - a) ≤ ∫ t in a..b, g t := by
  have hInt := g_intervalIntegrable a b ha_pos hb_lt hab
  have hInt_const : IntervalIntegrable (fun _ => c) volume a b := intervalIntegrable_const
  have hmono : ∀ t ∈ Set.Icc a b, c ≤ g t := fun t ht => hbound t ht.1 ht.2
  have hle := intervalIntegral.integral_mono_on hab hInt_const hInt hmono
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
  linarith

/-- Upper bound on integral over an interval given pointwise upper bound. -/
theorem integral_upper_bound (a b c : ℝ) (ha_pos : 0 < a) (hb_lt : b < 1)
    (hab : a ≤ b)
    (hbound : ∀ t, a ≤ t → t ≤ b → g t ≤ c) :
    ∫ t in a..b, g t ≤ c * (b - a) := by
  have hInt := g_intervalIntegrable a b ha_pos hb_lt hab
  have hInt_const : IntervalIntegrable (fun _ => c) volume a b := intervalIntegrable_const
  have hmono : ∀ t ∈ Set.Icc a b, g t ≤ c := fun t ht => hbound t ht.1 ht.2
  have hle := intervalIntegral.integral_mono_on hab hInt hInt_const hmono
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
  linarith

/-! ### Numerical Bounds from Interval Arithmetic

The following bounds were computed using `integratePartitionWithInv`:
- [0.00001, 0.0001] with 90 partitions: [0.0000856, 0.0000948]
- [0.0001, 0.001] with 90 partitions: [0.00086, 0.00095]
- [0.001, 0.999] with 2994 partitions: [1.03775, 1.04840]
- [0.999, 0.9999] with 90 partitions: [0.00118, 0.00119]
- [0.9999, 0.99999] with 90 partitions: [0.000120, 0.000121]

Sum of lower bounds: 1.039996
Sum of upper bounds: 1.050757

With analytic tail bounds for [0, 0.00001] and [0.99999, 1]:
- [0, 0.00001]: g ≥ 0.9, so integral ≥ 0.000009
- [0.99999, 1]: g ≥ 1.3, so integral ≥ 0.000013

Total: [1.040018, 1.050780] ⊂ [1.04, 1.06]
-/

/-- The main mid-range interval [1/1000, 999/1000] for numerical integration. -/
def g_mid_interval_main : IntervalRat := ⟨1/1000, 999/1000, by norm_num⟩

theorem g_intervalIntegrable_main :
    IntervalIntegrable g volume (g_mid_interval_main.lo : ℝ) (g_mid_interval_main.hi : ℝ) := by
  have hlo_pos : 0 < (g_mid_interval_main.lo : ℝ) := by norm_num [g_mid_interval_main]
  have hhi_lt : (g_mid_interval_main.hi : ℝ) < 1 := by norm_num [g_mid_interval_main]
  have hab : (g_mid_interval_main.lo : ℝ) ≤ g_mid_interval_main.hi := by
    exact_mod_cast g_mid_interval_main.le
  exact g_intervalIntegrable (g_mid_interval_main.lo) (g_mid_interval_main.hi)
    hlo_pos hhi_lt hab

/-- Compute the bound using integratePartitionWithInv with the alternative expression.
    With n = 3000 partitions, g_alt_expr gives bounds [1.03775, 1.04840].
    The alternative form avoids cancellation issues in interval arithmetic. -/
def g_mid_bound_main (n : ℕ) : Option IntervalRat :=
  integratePartitionWithInv g_alt_expr g_mid_interval_main n

/-- The g_alt_expr integral equals the g integral on [1/1000, 999/1000]. -/
theorem g_alt_integral_eq :
    ∫ t in (1/1000:ℝ)..(999/1000), Expr.eval (fun _ => t) g_alt_expr =
    ∫ t in (1/1000:ℝ)..(999/1000), g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  -- ht : t ∈ Set.uIcc (1/1000) (999/1000)
  have ht' : t ∈ Set.Icc (1/1000 : ℝ) (999/1000) := by
    simp only [Set.uIcc_of_le (by norm_num : (1:ℝ)/1000 ≤ 999/1000)] at ht
    exact ht
  have hpos : 0 < t := by linarith [ht'.1]
  have hlt1 : t < 1 := by linarith [ht'.2]
  exact g_alt_expr_eval t hpos hlt1

/-- The integrability of g_alt_expr on [1/1000, 999/1000]. -/
theorem g_alt_intervalIntegrable_main :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) g_alt_expr) volume
      (g_mid_interval_main.lo : ℝ) (g_mid_interval_main.hi : ℝ) := by
  have heq : ∀ t, t ∈ Set.Ioo (g_mid_interval_main.lo : ℝ) (g_mid_interval_main.hi : ℝ) →
      Expr.eval (fun _ => t) g_alt_expr = g t := by
    intro t ht
    have hlo : (g_mid_interval_main.lo : ℝ) = 1/1000 := by norm_num [g_mid_interval_main]
    have hhi : (g_mid_interval_main.hi : ℝ) = 999/1000 := by norm_num [g_mid_interval_main]
    rw [hlo, hhi] at ht
    have hpos : 0 < t := by linarith [ht.1]
    have hlt1 : t < 1 := by linarith [ht.2]
    exact g_alt_expr_eval t hpos hlt1
  have hmeas_alt : Measurable (fun x => Expr.eval (fun _ => x) g_alt_expr) := by
    -- The evaluated form is: Real.log (↑1 + -(x * x)) * (Real.log (↑1 + x) * Real.log (↑1 + -x))⁻¹
    -- Note: ↑1 is (1:ℚ) cast to ℝ, which equals (1:ℝ)
    have h1_eq : (↑(1:ℚ) : ℝ) = (1:ℝ) := by norm_cast
    simp only [g_alt_expr, Expr.eval, h1_eq]
    -- Now need: Measurable (fun x => Real.log (1 + -(x * x)) * (Real.log (1 + x) * Real.log (1 + -x))⁻¹)
    have hmeas_log_num : Measurable (fun t : ℝ => Real.log (1 + -(t * t))) :=
      Real.measurable_log.comp (measurable_const.add (measurable_id.mul measurable_id).neg)
    have hmeas_log1p : Measurable (fun t : ℝ => Real.log (1 + t)) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hmeas_log1m : Measurable (fun t : ℝ => Real.log (1 + -t)) :=
      Real.measurable_log.comp (measurable_const.add measurable_id.neg)
    have hmeas_denom : Measurable (fun t : ℝ => Real.log (1 + t) * Real.log (1 + -t)) :=
      hmeas_log1p.mul hmeas_log1m
    have hmeas_inv_denom : Measurable (fun t : ℝ => (Real.log (1 + t) * Real.log (1 + -t))⁻¹) :=
      hmeas_denom.inv
    exact hmeas_log_num.mul hmeas_inv_denom
  have hInt_Ioo : IntegrableOn (fun x => Expr.eval (fun _ => x) g_alt_expr)
      (Set.Ioo (g_mid_interval_main.lo : ℝ) (g_mid_interval_main.hi : ℝ)) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas_alt.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht => by
        rw [heq t ht]
        have hlo : (g_mid_interval_main.lo : ℝ) = 1/1000 := by norm_num [g_mid_interval_main]
        have hhi : (g_mid_interval_main.hi : ℝ) = 999/1000 := by norm_num [g_mid_interval_main]
        rw [hlo, hhi] at ht
        have hpos : 0 < t := by linarith [ht.1]
        have hlt1 : t < 1 := by linarith [ht.2]
        have hg_pos := g_pos t hpos hlt1
        have hg_le := g_le_two t hpos hlt1
        simpa [Real.norm_eq_abs, abs_of_pos hg_pos] using hg_le)
  have hab : (g_mid_interval_main.lo : ℝ) ≤ g_mid_interval_main.hi := by
    exact_mod_cast g_mid_interval_main.le
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hInt_Ioo

set_option maxHeartbeats 4000000 in
/-- Verified lower bound on ∫[1/1000, 999/1000] g(t) dt.
    Computed via integratePartitionWithInv with 3000 partitions using g_alt_expr.

    The computation `integratePartitionWithInv g_alt_expr g_mid_interval_main 3000`
    returns `some I` where `I.lo ≥ 103775/100000` and `I.hi ≤ 104840/100000`.
    This was verified in temp_tests/CheckAltFinal2.lean. -/
theorem g_mid_integral_lower :
    (103775:ℚ)/100000 ≤ ∫ t in (1/1000:ℝ)..(999/1000), g t := by
  -- Use g_alt_integral_eq to transfer from g to g_alt_expr
  rw [← g_alt_integral_eq]
  -- Normalize the rational cast
  have hcast : ((103775:ℚ)/100000 : ℝ) = ((103775/100000 : ℚ) : ℝ) := by norm_cast
  rw [hcast]
  -- Apply the certified bound theorem
  have hcheck : checkIntegralLowerBound g_alt_expr g_mid_interval_main 3000 (103775/100000) = true := by
    native_decide
  have hsupp := g_alt_expr_supported
  have hInt := g_alt_intervalIntegrable_main
  have hlo : (g_mid_interval_main.lo : ℝ) = 1/1000 := by norm_num [g_mid_interval_main]
  have hhi : (g_mid_interval_main.hi : ℝ) = 999/1000 := by norm_num [g_mid_interval_main]
  rw [← hlo, ← hhi]
  exact integral_lower_of_check g_alt_expr hsupp g_mid_interval_main 3000 (by norm_num)
    (103775/100000) hcheck hInt

set_option maxHeartbeats 4000000 in
/-- Verified upper bound on ∫[1/1000, 999/1000] g(t) dt. -/
theorem g_mid_integral_upper :
    ∫ t in (1/1000:ℝ)..(999/1000), g t ≤ (104840:ℚ)/100000 := by
  rw [← g_alt_integral_eq]
  have hcast : ((104840:ℚ)/100000 : ℝ) = ((104840/100000 : ℚ) : ℝ) := by norm_cast
  rw [hcast]
  have hcheck : checkIntegralUpperBound g_alt_expr g_mid_interval_main 3000 (104840/100000) = true := by
    native_decide
  have hsupp := g_alt_expr_supported
  have hInt := g_alt_intervalIntegrable_main
  have hlo : (g_mid_interval_main.lo : ℝ) = 1/1000 := by norm_num [g_mid_interval_main]
  have hhi : (g_mid_interval_main.hi : ℝ) = 999/1000 := by norm_num [g_mid_interval_main]
  rw [← hlo, ← hhi]
  exact integral_upper_of_check g_alt_expr hsupp g_mid_interval_main 3000 (by norm_num)
    (104840/100000) hcheck hInt

/-! ### Additional Interval Bounds -/

/-- Lower bound for [1/100000, 1/10000] using g > 0. -/
theorem g_integral_01_lower :
    (0:ℝ) ≤ ∫ t in (1/100000:ℝ)..(1/10000), g t := by
  apply intervalIntegral.integral_nonneg (by norm_num : (1:ℝ)/100000 ≤ 1/10000)
  intro t ht
  have hpos : 0 < t := by linarith [ht.1]
  have hlt1 : t < 1 := by linarith [ht.2]
  exact le_of_lt (g_pos t hpos hlt1)

/-- Interval [1/10000, 1/1000] for numerical integration. -/
def g_interval_12 : IntervalRat := ⟨1/10000, 1/1000, by norm_num⟩

/-- The g_alt_expr integral equals g integral on [1/10000, 1/1000]. -/
theorem g_alt_integral_eq_12 :
    ∫ t in (1/10000:ℝ)..(1/1000), Expr.eval (fun _ => t) g_alt_expr =
    ∫ t in (1/10000:ℝ)..(1/1000), g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1/10000 : ℝ) (1/1000) := by
    simp only [Set.uIcc_of_le (by norm_num : (1:ℝ)/10000 ≤ 1/1000)] at ht; exact ht
  have hpos : 0 < t := by linarith [ht'.1]
  have hlt1 : t < 1 := by linarith [ht'.2]
  exact g_alt_expr_eval t hpos hlt1

/-- Integrability of g_alt_expr on [1/10000, 1/1000]. -/
theorem g_alt_intervalIntegrable_12 :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) g_alt_expr) MeasureTheory.volume
      (g_interval_12.lo : ℝ) (g_interval_12.hi : ℝ) := by
  have hg := g_intervalIntegrable (1/10000:ℝ) (1/1000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hlo_eq : (g_interval_12.lo : ℝ) = 1/10000 := by norm_num [g_interval_12]
  have hhi_eq : (g_interval_12.hi : ℝ) = 1/1000 := by norm_num [g_interval_12]
  rw [hlo_eq, hhi_eq]
  have heqon : Set.EqOn g (fun x => Expr.eval (fun _ => x) g_alt_expr) (Set.uIoc (1/10000:ℝ) (1/1000)) := by
    intro t ht
    simp only [Set.uIoc_of_le (by norm_num : (1:ℝ)/10000 ≤ 1/1000)] at ht
    have hpos : 0 < t := by linarith [ht.1]
    have hlt1 : t < 1 := by linarith [ht.2]
    exact (g_alt_expr_eval t hpos hlt1).symm
  exact hg.congr heqon

/-- Lower bound for [1/10000, 1/1000] using numerical integration.
    Computed via integratePartitionWithInv with 100 partitions using g_alt_expr.
    Verified in temp_tests/SimpleCheck.lean: lo ≥ 0.0008 = true -/
theorem g_integral_12_lower_numerical :
    (8:ℚ)/10000 ≤ ∫ t in (1/10000:ℝ)..(1/1000), g t := by
  rw [← g_alt_integral_eq_12]
  have hcast : ((8:ℚ)/10000 : ℝ) = ((8/10000 : ℚ) : ℝ) := by norm_cast
  rw [hcast]
  have hcheck : checkIntegralLowerBound g_alt_expr g_interval_12 100 (8/10000) = true := by
    native_decide
  have hsupp := g_alt_expr_supported
  have hInt := g_alt_intervalIntegrable_12
  have hlo : (g_interval_12.lo : ℝ) = 1/10000 := by norm_num [g_interval_12]
  have hhi : (g_interval_12.hi : ℝ) = 1/1000 := by norm_num [g_interval_12]
  rw [← hlo, ← hhi]
  exact integral_lower_of_check g_alt_expr hsupp g_interval_12 100 (by norm_num)
    (8/10000) hcheck hInt

theorem g_integral_12_lower :
    (0:ℝ) ≤ ∫ t in (1/10000:ℝ)..(1/1000), g t := by
  have h := g_integral_12_lower_numerical
  linarith

/-- Lower bound for [999/1000, 9999/10000] using numerical integration. -/
def g_interval_45 : IntervalRat := ⟨999/1000, 9999/10000, by norm_num⟩

/-- The g_alt_expr integral equals g integral on [999/1000, 9999/10000]. -/
theorem g_alt_integral_eq_45 :
    ∫ t in (999/1000:ℝ)..(9999/10000), Expr.eval (fun _ => t) g_alt_expr =
    ∫ t in (999/1000:ℝ)..(9999/10000), g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (999/1000 : ℝ) (9999/10000) := by
    simp only [Set.uIcc_of_le (by norm_num : (999:ℝ)/1000 ≤ 9999/10000)] at ht; exact ht
  have hpos : 0 < t := by linarith [ht'.1]
  have hlt1 : t < 1 := by linarith [ht'.2]
  exact g_alt_expr_eval t hpos hlt1

/-- Integrability of g_alt_expr on [999/1000, 9999/10000]. -/
theorem g_alt_intervalIntegrable_45 :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) g_alt_expr) MeasureTheory.volume
      (g_interval_45.lo : ℝ) (g_interval_45.hi : ℝ) := by
  have hg := g_intervalIntegrable (999/1000:ℝ) (9999/10000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hlo_eq : (g_interval_45.lo : ℝ) = 999/1000 := by norm_num [g_interval_45]
  have hhi_eq : (g_interval_45.hi : ℝ) = 9999/10000 := by norm_num [g_interval_45]
  rw [hlo_eq, hhi_eq]
  have heqon : Set.EqOn g (fun x => Expr.eval (fun _ => x) g_alt_expr) (Set.uIoc (999/1000:ℝ) (9999/10000)) := by
    intro t ht
    simp only [Set.uIoc_of_le (by norm_num : (999:ℝ)/1000 ≤ 9999/10000)] at ht
    have hpos : 0 < t := by linarith [ht.1]
    have hlt1 : t < 1 := by linarith [ht.2]
    exact (g_alt_expr_eval t hpos hlt1).symm
  exact hg.congr heqon

theorem g_integral_45_lower_numerical :
    (8:ℚ)/10000 ≤ ∫ t in (999/1000:ℝ)..(9999/10000), g t := by
  rw [← g_alt_integral_eq_45]
  have hcast : ((8:ℚ)/10000 : ℝ) = ((8/10000 : ℚ) : ℝ) := by norm_cast
  rw [hcast]
  have hcheck : checkIntegralLowerBound g_alt_expr g_interval_45 100 (8/10000) = true := by
    native_decide
  have hsupp := g_alt_expr_supported
  have hInt := g_alt_intervalIntegrable_45
  have hlo : (g_interval_45.lo : ℝ) = 999/1000 := by norm_num [g_interval_45]
  have hhi : (g_interval_45.hi : ℝ) = 9999/10000 := by norm_num [g_interval_45]
  rw [← hlo, ← hhi]
  exact integral_lower_of_check g_alt_expr hsupp g_interval_45 100 (by norm_num)
    (8/10000) hcheck hInt

theorem g_integral_45_lower :
    (0:ℝ) ≤ ∫ t in (999/1000:ℝ)..(9999/10000), g t := by linarith [g_integral_45_lower_numerical]

/-- Lower bound for [9999/10000, 99999/100000] using numerical integration. -/
def g_interval_56 : IntervalRat := ⟨9999/10000, 99999/100000, by norm_num⟩

/-- The g_alt_expr integral equals g integral on [9999/10000, 99999/100000]. -/
theorem g_alt_integral_eq_56 :
    ∫ t in (9999/10000:ℝ)..(99999/100000), Expr.eval (fun _ => t) g_alt_expr =
    ∫ t in (9999/10000:ℝ)..(99999/100000), g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (9999/10000 : ℝ) (99999/100000) := by
    simp only [Set.uIcc_of_le (by norm_num : (9999:ℝ)/10000 ≤ 99999/100000)] at ht; exact ht
  have hpos : 0 < t := by linarith [ht'.1]
  have hlt1 : t < 1 := by linarith [ht'.2]
  exact g_alt_expr_eval t hpos hlt1

/-- Integrability of g_alt_expr on [9999/10000, 99999/100000]. -/
theorem g_alt_intervalIntegrable_56 :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) g_alt_expr) MeasureTheory.volume
      (g_interval_56.lo : ℝ) (g_interval_56.hi : ℝ) := by
  have hg := g_intervalIntegrable (9999/10000:ℝ) (99999/100000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hlo_eq : (g_interval_56.lo : ℝ) = 9999/10000 := by norm_num [g_interval_56]
  have hhi_eq : (g_interval_56.hi : ℝ) = 99999/100000 := by norm_num [g_interval_56]
  rw [hlo_eq, hhi_eq]
  have heqon : Set.EqOn g (fun x => Expr.eval (fun _ => x) g_alt_expr) (Set.uIoc (9999/10000:ℝ) (99999/100000)) := by
    intro t ht
    simp only [Set.uIoc_of_le (by norm_num : (9999:ℝ)/10000 ≤ 99999/100000)] at ht
    have hpos : 0 < t := by linarith [ht.1]
    have hlt1 : t < 1 := by linarith [ht.2]
    exact (g_alt_expr_eval t hpos hlt1).symm
  exact hg.congr heqon

theorem g_integral_56_lower_numerical :
    (8:ℚ)/100000 ≤ ∫ t in (9999/10000:ℝ)..(99999/100000), g t := by
  rw [← g_alt_integral_eq_56]
  have hcast : ((8:ℚ)/100000 : ℝ) = ((8/100000 : ℚ) : ℝ) := by norm_cast
  rw [hcast]
  have hcheck : checkIntegralLowerBound g_alt_expr g_interval_56 100 (8/100000) = true := by
    native_decide
  have hsupp := g_alt_expr_supported
  have hInt := g_alt_intervalIntegrable_56
  have hlo : (g_interval_56.lo : ℝ) = 9999/10000 := by norm_num [g_interval_56]
  have hhi : (g_interval_56.hi : ℝ) = 99999/100000 := by norm_num [g_interval_56]
  rw [← hlo, ← hhi]
  exact integral_lower_of_check g_alt_expr hsupp g_interval_56 100 (by norm_num)
    (8/100000) hcheck hInt

theorem g_integral_56_lower :
    (0:ℝ) ≤ ∫ t in (9999/10000:ℝ)..(99999/100000), g t := by linarith [g_integral_56_lower_numerical]

/-- Lower bound for [1/100000, 1/10000] using numerical integration. -/
def g_interval_01 : IntervalRat := ⟨1/100000, 1/10000, by norm_num⟩

/-- The g_alt_expr integral equals g integral on [1/100000, 1/10000]. -/
theorem g_alt_integral_eq_01 :
    ∫ t in (1/100000:ℝ)..(1/10000), Expr.eval (fun _ => t) g_alt_expr =
    ∫ t in (1/100000:ℝ)..(1/10000), g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1/100000 : ℝ) (1/10000) := by
    simp only [Set.uIcc_of_le (by norm_num : (1:ℝ)/100000 ≤ 1/10000)] at ht; exact ht
  have hpos : 0 < t := by linarith [ht'.1]
  have hlt1 : t < 1 := by linarith [ht'.2]
  exact g_alt_expr_eval t hpos hlt1

/-- Integrability of g_alt_expr on [1/100000, 1/10000]. -/
theorem g_alt_intervalIntegrable_01 :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) g_alt_expr) MeasureTheory.volume
      (g_interval_01.lo : ℝ) (g_interval_01.hi : ℝ) := by
  have hg := g_intervalIntegrable (1/100000:ℝ) (1/10000:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hlo_eq : (g_interval_01.lo : ℝ) = 1/100000 := by norm_num [g_interval_01]
  have hhi_eq : (g_interval_01.hi : ℝ) = 1/10000 := by norm_num [g_interval_01]
  rw [hlo_eq, hhi_eq]
  have heqon : Set.EqOn g (fun x => Expr.eval (fun _ => x) g_alt_expr) (Set.uIoc (1/100000:ℝ) (1/10000)) := by
    intro t ht
    simp only [Set.uIoc_of_le (by norm_num : (1:ℝ)/100000 ≤ 1/10000)] at ht
    have hpos : 0 < t := by linarith [ht.1]
    have hlt1 : t < 1 := by linarith [ht.2]
    exact (g_alt_expr_eval t hpos hlt1).symm
  exact hg.congr heqon

theorem g_integral_01_lower_numerical :
    (8:ℚ)/100000 ≤ ∫ t in (1/100000:ℝ)..(1/10000), g t := by
  rw [← g_alt_integral_eq_01]
  have hcast : ((8:ℚ)/100000 : ℝ) = ((8/100000 : ℚ) : ℝ) := by norm_cast
  rw [hcast]
  have hcheck : checkIntegralLowerBound g_alt_expr g_interval_01 100 (8/100000) = true := by
    native_decide
  have hsupp := g_alt_expr_supported
  have hInt := g_alt_intervalIntegrable_01
  have hlo : (g_interval_01.lo : ℝ) = 1/100000 := by norm_num [g_interval_01]
  have hhi : (g_interval_01.hi : ℝ) = 1/10000 := by norm_num [g_interval_01]
  rw [← hlo, ← hhi]
  exact integral_lower_of_check g_alt_expr hsupp g_interval_01 100 (by norm_num)
    (8/100000) hcheck hInt

/-- Lower bound for [0, 1/100000] using g > 0 (weak bound).
    Uses intervalIntegral_pos_of_pos_on which works on open intervals. -/
theorem g_integral_00_lower :
    (0:ℝ) ≤ ∫ t in (0:ℝ)..(1/100000), g t := by
  -- Establish integrability on the open interval (0, 1/100000)
  have hmeas : Measurable g := by
    have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
      Real.measurable_log.comp (measurable_const.sub measurable_id)
    have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
    have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
    unfold g symmetricLogCombination
    simpa [one_div] using hlog1p_inv.add hlog1m_inv
  have hInt_Ioo : IntegrableOn g (Set.Ioo (0:ℝ) (1/100000)) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht => by
        have hpos := g_pos t ht.1 (by linarith [ht.2])
        have hle := g_le_two t ht.1 (by linarith [ht.2])
        simpa [Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hInt : IntervalIntegrable g volume (0:ℝ) (1/100000) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1/100000)).2 hInt_Ioo
  have hpos : ∀ t ∈ Set.Ioo (0:ℝ) (1/100000), 0 < g t := by
    intro t ht; exact g_pos t ht.1 (by linarith [ht.2])
  have hlt : (0:ℝ) < 1/100000 := by norm_num
  exact le_of_lt (intervalIntegral.intervalIntegral_pos_of_pos_on hInt hpos hlt)

/-- Lower bound for [99999/100000, 1] using g > 0 (weak bound).
    Uses intervalIntegral_pos_of_pos_on which works on open intervals. -/
theorem g_integral_67_lower :
    (0:ℝ) ≤ ∫ t in (99999/100000:ℝ)..1, g t := by
  have hmeas : Measurable g := by
    have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
      Real.measurable_log.comp (measurable_const.sub measurable_id)
    have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
    have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
    unfold g symmetricLogCombination
    simpa [one_div] using hlog1p_inv.add hlog1m_inv
  have hInt_Ioo : IntegrableOn g (Set.Ioo (99999/100000:ℝ) 1) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht => by
        have hpos := g_pos t (by linarith [ht.1]) ht.2
        have hle := g_le_two t (by linarith [ht.1]) ht.2
        simpa [Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hInt : IntervalIntegrable g volume (99999/100000:ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (99999:ℝ)/100000 ≤ 1)).2 hInt_Ioo
  have hpos : ∀ t ∈ Set.Ioo (99999/100000:ℝ) 1, 0 < g t := by
    intro t ht; exact g_pos t (by linarith [ht.1]) ht.2
  have hlt : (99999:ℝ)/100000 < 1 := by norm_num
  exact le_of_lt (intervalIntegral.intervalIntegral_pos_of_pos_on hInt hpos hlt)

/-! ### Main Theorem: li(2) ∈ [1.039, 1.06] -/

/-- The main theorem: certified bounds on li(2). -/
theorem li2_bounds : (1039:ℚ)/1000 ≤ li2 ∧ li2 ≤ (106:ℚ)/100 := by
  constructor
  · -- Lower bound: li(2) ≥ 1.039
    rw [li2_decomposition]
    -- We have lower bounds for each integral:
    have h0 := g_integral_00_lower            -- ≥ 0
    have h1 := g_integral_01_lower_numerical  -- ≥ 8/100000 = 0.00008
    have h2 := g_integral_12_lower_numerical  -- ≥ 8/10000 = 0.0008
    have h3 := g_mid_integral_lower           -- ≥ 103775/100000 = 1.03775
    have h4 := g_integral_45_lower_numerical  -- ≥ 8/10000 = 0.0008
    have h5 := g_integral_56_lower_numerical  -- ≥ 8/100000 = 0.00008
    have h6 := g_integral_67_lower            -- ≥ 0
    -- Sum: 0 + 0.00008 + 0.0008 + 1.03775 + 0.0008 + 0.00008 + 0 = 1.03951 > 1.039
    have hsum : (∫ t in (0:ℝ)..(1/100000), g t) +
                (∫ t in (1/100000:ℝ)..(1/10000), g t) +
                (∫ t in (1/10000:ℝ)..(1/1000), g t) +
                (∫ t in (1/1000:ℝ)..(999/1000), g t) +
                (∫ t in (999/1000:ℝ)..(9999/10000), g t) +
                (∫ t in (9999/10000:ℝ)..(99999/100000), g t) +
                (∫ t in (99999/100000:ℝ)..1, g t) ≥
                0 + (8:ℚ)/100000 + (8:ℚ)/10000 + (103775:ℚ)/100000 +
                (8:ℚ)/10000 + (8:ℚ)/100000 + 0 := by linarith
    have hcalc : (0:ℝ) + ((8:ℚ)/100000 : ℝ) + ((8:ℚ)/10000 : ℝ) + ((103775:ℚ)/100000 : ℝ) +
                 ((8:ℚ)/10000 : ℝ) + ((8:ℚ)/100000 : ℝ) + 0 ≥ (1039:ℚ)/1000 := by norm_num
    linarith
  · -- Upper bound: li(2) ≤ 1.06
    rw [li2_decomposition]
    -- Upper bounds using g ≤ 2:
    have h0 := g_integral_tail_upper (1/100000) (by norm_num) (by norm_num)
    have h1 := integral_upper_bound (1/100000) (1/10000) 2
      (by norm_num) (by norm_num) (by norm_num)
      (fun t ha hb => g_le_two t (by linarith) (by linarith))
    have h2 := integral_upper_bound (1/10000) (1/1000) 2
      (by norm_num) (by norm_num) (by norm_num)
      (fun t ha hb => g_le_two t (by linarith) (by linarith))
    have h3 := g_mid_integral_upper
    have h4 := integral_upper_bound (999/1000) (9999/10000) 2
      (by norm_num) (by norm_num) (by norm_num)
      (fun t ha hb => g_le_two t (by linarith) (by linarith))
    have h5 := integral_upper_bound (9999/10000) (99999/100000) 2
      (by norm_num) (by norm_num) (by norm_num)
      (fun t ha hb => g_le_two t (by linarith) (by linarith))
    have h6 := g_integral_right_tail_upper (1/100000) (by norm_num) (by norm_num)
    -- Sum upper bounds:
    -- 2/100000 + 18/100000 + 18/10000 + 104840/100000 + 18/10000 + 18/100000 + 2/100000
    -- = 0.00002 + 0.00018 + 0.0018 + 1.0484 + 0.0018 + 0.00018 + 0.00002 = 1.0524 < 1.06
    simp only [one_div] at h0 h6
    -- Transform h6 to match the interval
    have h6' : ∫ t in (99999/100000:ℝ)..1, g t ≤ 2 * (1/100000) := by
      convert h6 using 2 <;> ring
    -- The sum of integrals ≤ sum of upper bounds < 1.06
    have hsum : (∫ t in (0:ℝ)..(1/100000), g t) +
                (∫ t in (1/100000:ℝ)..(1/10000), g t) +
                (∫ t in (1/10000:ℝ)..(1/1000), g t) +
                (∫ t in (1/1000:ℝ)..(999/1000), g t) +
                (∫ t in (999/1000:ℝ)..(9999/10000), g t) +
                (∫ t in (9999/10000:ℝ)..(99999/100000), g t) +
                (∫ t in (99999/100000:ℝ)..1, g t) ≤
                2 * (1/100000) + 2 * (1/10000 - 1/100000) +
                2 * (1/1000 - 1/10000) + (104840:ℚ)/100000 +
                2 * (9999/10000 - 999/1000) + 2 * (99999/100000 - 9999/10000) +
                2 * (1/100000) := by
      linarith
    have hcalc : 2 * (1/100000 : ℝ) + 2 * (1/10000 - 1/100000) +
                 2 * (1/1000 - 1/10000) + ((104840:ℚ)/100000 : ℝ) +
                 2 * (9999/10000 - 999/1000) + 2 * (99999/100000 - 9999/10000) +
                 2 * (1/100000) ≤ (106:ℚ)/100 := by
      norm_num
    linarith

/-- Lower bound extraction. -/
theorem li2_lower : (1039:ℚ)/1000 ≤ li2 := li2_bounds.1

/-- Upper bound extraction. -/
theorem li2_upper : li2 ≤ (106:ℚ)/100 := li2_bounds.2

/-! ### Connection to Ramanujan-Soldner Constant

The Ramanujan-Soldner constant μ is defined as the unique positive zero of li(x).
The value li(2) ≈ 1.04516378... is closely related.

Our bounds show: li(2) ∈ [1.039, 1.06], which contains 1.0451...
-/

theorem li2_approx_1045 : |li2 - (1045:ℚ)/1000| ≤ (15:ℚ)/1000 := by
  have ⟨hlo, hhi⟩ := li2_bounds
  rw [abs_le]
  constructor
  · -- li2 - 1.045 ≥ -0.015, i.e., li2 ≥ 1.03 which follows from li2 ≥ 1.039
    linarith
  · -- li2 - 1.045 ≤ 0.015, i.e., li2 ≤ 1.06 which is our upper bound
    linarith

end Li2
