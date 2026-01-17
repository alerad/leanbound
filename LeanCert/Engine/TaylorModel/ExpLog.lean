/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Core
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Taylor Models - Exponential and Logarithmic Functions

This file contains Taylor polynomial definitions and remainder bounds for
exp and log functions, along with function-level Taylor models and their
correctness proofs.

## Main definitions

* `expTaylorPoly`, `logTaylorPolyAtCenter` - Taylor polynomials
* `expRemainderBound`, `logRemainderBound` - Remainder bounds
* `tmExp`, `tmLog` - Function-level Taylor models
* `tmExp_correct`, `tmLog_correct` - Correctness theorems
-/

namespace LeanCert.Engine

open LeanCert.Core
open Polynomial

namespace TaylorModel

/-! ### exp Taylor polynomial -/

/-- Taylor polynomial for exp of degree n: ∑_{i=0}^n x^i / i! -/
noncomputable def expTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (1 / (Nat.factorial i : ℚ)) * Polynomial.X ^ i

/-- Remainder bound for exp Taylor series.
    The Lagrange remainder is exp(ξ) * x^{n+1} / (n+1)! where ξ is between 0 and x.
    We use e < 3, so e^r ≤ 3^(⌈r⌉+1) as a conservative bound.
-/
noncomputable def expRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- Crude bound: e ≈ 3, so e^r ≤ 3^(⌈r⌉+1) for r ≥ 0
  let expBound := (3 : ℚ) ^ (Nat.ceil r + 1)
  let xBound := r ^ (n + 1)
  expBound * xBound / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for exp is nonnegative -/
theorem expRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ expRemainderBound domain n := by
  unfold expRemainderBound
  simp only
  apply div_nonneg
  · apply mul_nonneg
    · apply pow_nonneg; norm_num
    · apply pow_nonneg
      exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-- Taylor model for exp z on domain J, centered at 0, degree n.
    This represents the function z ↦ exp(z) directly. -/
noncomputable def tmExp (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := expTaylorPoly n
    remainder := ⟨-expRemainderBound J n, expRemainderBound J n,
      by linarith [expRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-! ### log Taylor polynomial

log(x) at center c > 0:
  log(x) = log(c) + Σ_{k=1}^n [(-1)^(k+1) / (k * c^k)] * (x - c)^k + R_n(x)

The constant term log(c) is transcendental, so we:
1. Approximate log(c) with a rational q using interval bounds
2. Add the approximation error to the remainder

The Lagrange remainder is: R_n(x) = (-1)^n / [(n+1) * ξ^(n+1)] * (x-c)^(n+1)
where ξ is between x and c. For positive domain, |R_n| ≤ r^(n+1) / [(n+1) * min_domain^(n+1)].
-/

/-- Taylor polynomial coefficients for log at center c > 0:
    log(x) = log(c) + (1/c)(x-c) - (1/2c²)(x-c)² + (1/3c³)(x-c)³ - ...
    For k ≥ 1: coeff_k = (-1)^(k+1) / (k * c^k)
    For k = 0: we handle the transcendental log(c) separately in tmLog. -/
noncomputable def logTaylorCoeffs (c : ℚ) (n : ℕ) : ℕ → ℚ := fun i =>
  if i = 0 then 0  -- placeholder, log(c) handled separately
  else if i ≤ n then
    ((-1 : ℚ)^(i + 1)) / (i * c^i)
  else 0

/-- Taylor polynomial for log at center c > 0 (without the log(c) constant term).
    The constant term is added as a rational approximation in tmLog. -/
noncomputable def logTaylorPolyAtCenter (c : ℚ) (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (logTaylorCoeffs c n i) * Polynomial.X ^ i

/-- Lagrange remainder bound for log at center c > 0.
    |R_n(x)| ≤ r^(n+1) / [(n+1) * min_ξ^(n+1)]
    where r = max(|lo - c|, |hi - c|) and min_ξ = min(lo, c) for positive domain.
    Since domain ⊂ (0, ∞) and c is the midpoint, we use domain.lo as min_ξ. -/
noncomputable def logLagrangeRemainder (domain : IntervalRat) (c : ℚ) (n : ℕ) : ℚ :=
  let r := max (|domain.lo - c|) (|domain.hi - c|)
  -- The (n+1)th derivative of log at ξ is (-1)^n * n! / ξ^(n+1)
  -- Lagrange remainder: |R_n| = |f^(n+1)(ξ)| / (n+1)! * |x-c|^(n+1)
  --                          = n! / ξ^(n+1) / (n+1)! * r^(n+1)
  --                          = 1 / [(n+1) * ξ^(n+1)] * r^(n+1)
  -- We bound by using min_ξ = domain.lo (assuming domain is positive)
  let min_xi := domain.lo
  if min_xi ≤ 0 then 1000  -- invalid domain, return large bound
  else r^(n+1) / ((n + 1) * min_xi^(n+1))

/-- Total remainder bound for log: Lagrange remainder + approximation error for log(c). -/
noncomputable def logRemainderBound (domain : IntervalRat) (c : ℚ) (n : ℕ)
    (logc_error : ℚ) : ℚ :=
  logLagrangeRemainder domain c n + logc_error

/-- Remainder bound for log is nonnegative (when domain is positive). -/
theorem logRemainderBound_nonneg (domain : IntervalRat) (c : ℚ) (n : ℕ)
    (logc_error : ℚ) (_hc : c > 0) (herr : logc_error ≥ 0) (hdom : domain.lo > 0) :
    0 ≤ logRemainderBound domain c n logc_error := by
  unfold logRemainderBound logLagrangeRemainder
  have hdom' : ¬(domain.lo ≤ 0) := not_le.mpr hdom
  simp only [hdom', ↓reduceIte]
  apply add_nonneg
  · apply div_nonneg
    · apply pow_nonneg
      exact le_max_of_le_left (abs_nonneg _)
    · apply mul_nonneg
      · have : (0 : ℚ) < n + 1 := by linarith
        linarith
      · apply pow_nonneg; linarith
  · exact herr

/-- Taylor model for log z on domain J, centered at c = midpoint.
    Returns None if the domain is not strictly positive.

    This handles the transcendental log(c) by:
    1. Computing rational bounds [lo, hi] for log(c)
    2. Using midpoint = (lo + hi) / 2 as the polynomial constant
    3. Adding error = (hi - lo) / 2 to the remainder -/
noncomputable def tmLog (J : IntervalRat) (n : ℕ) : Option TaylorModel :=
  if hpos : J.lo > 0 then
    let c := J.midpoint
    -- Get rational bounds for log(c) using the interval log function
    -- Prove c > 0
    have hc_pos : 0 < c := by
      simp only [IntervalRat.midpoint, c]
      apply div_pos
      · linarith [J.le]
      · norm_num
    let c_interval : IntervalRat.IntervalRatPos :=
      { toIntervalRat := IntervalRat.singleton c
        lo_pos := by simp only [IntervalRat.singleton]; exact hc_pos }
    let logc_interval := IntervalRat.logInterval c_interval
    let logc_approx := logc_interval.midpoint
    let logc_error := logc_interval.width / 2

    -- Build polynomial: log(c) + Σ_{k=1}^n coeff_k * X^k
    let base_poly := logTaylorPolyAtCenter c n
    let poly := base_poly + Polynomial.C logc_approx

    -- Total remainder = Lagrange remainder + log(c) approximation error
    let rem := logRemainderBound J c n logc_error

    some {
      poly := poly
      remainder := ⟨-rem, rem, by
        have herr : logc_error ≥ 0 := by
          simp only [logc_error, IntervalRat.width]
          apply div_nonneg
          · apply sub_nonneg.mpr logc_interval.le
          · norm_num
        linarith [logRemainderBound_nonneg J c n logc_error hc_pos herr hpos]⟩
      center := c
      domain := J
    }
  else
    none

/-! ### Helper lemmas -/

/-- Helper: |z| ≤ radius of interval J for z ∈ J -/
private theorem abs_le_interval_radius {z : ℝ} {J : IntervalRat} (hz : z ∈ J) :
    |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
  simp only [IntervalRat.mem_def] at hz
  rw [abs_le]
  constructor
  · have h1 : -|(J.lo : ℝ)| ≤ J.lo := neg_abs_le _
    have h2 : -(max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|)) ≤ -|(J.lo : ℝ)| := by
      simp only [neg_le_neg_iff]; exact le_max_left _ _
    linarith
  · have h1 : (J.hi : ℝ) ≤ |(J.hi : ℝ)| := le_abs_self _
    have h2 : |(J.hi : ℝ)| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := le_max_right _ _
    linarith

/-- Helper: z ∈ J means z ∈ [J.lo, J.hi] as real numbers -/
private theorem mem_Icc_of_mem_interval {z : ℝ} {J : IntervalRat} (hz : z ∈ J) :
    z ∈ Set.Icc (J.lo : ℝ) (J.hi : ℝ) := by
  simp only [IntervalRat.mem_def] at hz
  exact ⟨hz.1, hz.2⟩

/-! ### Correctness theorems -/

/-- expTaylorPoly evaluates to the standard Taylor sum for exp at 0.
    This connects our rational polynomial to Mathlib's Taylor series. -/
theorem expTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (expTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * z ^ i := by
  simp only [expTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i _
  -- iteratedDeriv i exp 0 = exp 0 = 1, so coeff = 1/i!
  have hexp_deriv : iteratedDeriv i Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [hexp_deriv, one_div]
  -- Both sides are equal: algebraMap ℚ ℝ (x⁻¹) * z^i = x⁻¹ * z^i
  -- where x = i.factorial. Just need to show algebraMap ℚ ℝ commutes with Nat cast
  congr 1
  simp only [eq_ratCast, Rat.cast_inv, Rat.cast_natCast]

/-- exp z ∈ (tmExp J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.exp, M = exp(max of interval). -/
theorem tmExp_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.exp z ∈ (tmExp J n).evalSet z := by
  intro z hz
  simp only [tmExp, evalSet, Set.mem_setOf_eq]
  set r := Real.exp z - Polynomial.aeval (z - 0) (expTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hpoly_eq := expTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.exp z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
    -- Apply taylor_remainder_bound with f = exp, c = 0, M = exp b
    set a := min (J.lo : ℝ) 0 with ha_def
    set b := max (J.hi : ℝ) 0 with hb_def
    have hab : a ≤ b := by simp only [ha_def, hb_def]; exact le_trans (min_le_of_right_le (le_refl 0)) (le_max_right _ _)
    have hca : a ≤ 0 := min_le_right _ _
    have hcb : 0 ≤ b := le_max_right _ _
    have hz_ab : z ∈ Set.Icc a b := by
      simp only [Set.mem_Icc, ha_def, hb_def]
      have hmem := mem_Icc_of_mem_interval hz
      constructor
      · exact le_trans (min_le_left _ _) hmem.1
      · exact le_trans hmem.2 (le_max_left _ _)
    set M := Real.exp b with hM_def
    have hM_pos : 0 ≤ M := le_of_lt (Real.exp_pos b)
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.exp x‖ ≤ M := by
      intro x hx
      exact LeanCert.Core.exp_deriv_bound hab (n + 1) x hx
    have hf : ContDiff ℝ (n + 1) Real.exp := Real.contDiff_exp.of_le le_top
    have hTaylor := LeanCert.Core.taylor_remainder_bound hab hca hcb hf hM hM_pos z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ M * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    -- Now show |r| ≤ expRemainderBound J n
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hb_le_radius : b ≤ radius := by
      simp only [hb_def, hradius_real]
      apply max_le
      · calc (J.hi : ℝ) ≤ |(J.hi : ℝ)| := le_abs_self _
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := le_max_right _ _
      · calc (0 : ℝ) ≤ |↑J.lo| := abs_nonneg _
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := le_max_left _ _
    have hexp_b_le : Real.exp b ≤ Real.exp radius := Real.exp_le_exp.mpr hb_le_radius
    have hradius_nn : 0 ≤ (radius : ℝ) := by
      rw [hradius_real]
      exact le_max_of_le_left (abs_nonneg _)
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]; exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hexp_le_three_pow : Real.exp (radius : ℝ) ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := by
      have he_le_3 : Real.exp 1 ≤ 3 := by
        have h := Real.exp_one_lt_d9
        linarith
      calc Real.exp (radius : ℝ)
          ≤ Real.exp (Nat.ceil radius : ℝ) := by
              apply Real.exp_le_exp.mpr
              exact_mod_cast Nat.le_ceil radius
        _ = Real.exp 1 ^ (Nat.ceil radius) := by
              rw [← Real.exp_nat_mul, mul_one]
        _ ≤ 3 ^ (Nat.ceil radius) := by
              apply pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1))
              exact he_le_3
        _ ≤ 3 ^ (Nat.ceil radius + 1) := by
              apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
              exact Nat.le_succ _
    have hM_bound : M ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := by
      calc M = Real.exp b := rfl
        _ ≤ Real.exp radius := hexp_b_le
        _ ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := hexp_le_three_pow
    have hrem_ge : (expRemainderBound J n : ℝ) ≥ M * |z| ^ (n + 1) / (n + 1).factorial := by
      have h1 : M * |z| ^ (n + 1) ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) * (radius : ℝ) ^ (n + 1) := by
        apply mul_le_mul hM_bound hpow_le (pow_nonneg (abs_nonneg z) _) (by linarith)
      calc (expRemainderBound J n : ℝ)
          = (3 : ℝ) ^ (Nat.ceil radius + 1) * (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
            simp only [expRemainderBound, hradius_def, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
              Rat.cast_natCast, Rat.cast_ofNat]
        _ ≥ M * |z| ^ (n + 1) / (n + 1).factorial := by
            apply div_le_div_of_nonneg_right h1 (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ expRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

/-- Helper lemma: log(c) is within logc_error of logc_approx when logc_interval
    is computed from logInterval applied to a singleton interval containing c. -/
theorem log_approx_error_bound {c : ℚ} (hc_pos : 0 < c) :
    let c_interval : IntervalRat.IntervalRatPos :=
      { toIntervalRat := IntervalRat.singleton c
        lo_pos := by simp only [IntervalRat.singleton]; exact hc_pos }
    let logc_interval := IntervalRat.logInterval c_interval
    let logc_approx := logc_interval.midpoint
    let logc_error := logc_interval.width / 2
    |Real.log c - logc_approx| ≤ logc_error := by
  intro c_interval logc_interval logc_approx logc_error
  have hc_real_pos : (0 : ℝ) < c := by exact_mod_cast hc_pos
  have hc_mem : (c : ℝ) ∈ c_interval.toIntervalRat := by
    simp only [c_interval, IntervalRat.singleton, IntervalRat.mem_def]
    constructor <;> linarith
  have hlog_mem := IntervalRat.mem_logInterval hc_mem
  simp only [IntervalRat.mem_def] at hlog_mem
  have h1 : (logc_interval.lo : ℝ) ≤ Real.log c := hlog_mem.1
  have h2 : Real.log c ≤ (logc_interval.hi : ℝ) := hlog_mem.2
  simp only [logc_approx, logc_error, IntervalRat.midpoint, IntervalRat.width]
  rw [abs_le]
  constructor <;> {
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
    linarith
  }

/-- The Taylor remainder for log at center c is bounded by the Lagrange form. -/
theorem log_taylor_remainder_bound' (J : IntervalRat) (c : ℚ) (n : ℕ) (z : ℝ)
    (hpos : J.lo > 0) (hc_lo : (J.lo : ℝ) ≤ c) (hc_hi : (c : ℝ) ≤ J.hi)
    (hz : z ∈ J) :
    |Real.log z - Real.log c -
      Polynomial.aeval (z - (c : ℝ)) (logTaylorPolyAtCenter c n)| ≤
    (logLagrangeRemainder J c n : ℝ) := by
  set a : ℝ := (J.lo : ℝ) with ha_def
  set b : ℝ := (J.hi : ℝ) with hb_def
  have hab : a ≤ b := by simp only [ha_def, hb_def]; exact_mod_cast J.le
  have ha_pos : 0 < a := by simp only [ha_def]; exact_mod_cast hpos
  have hc_pos : 0 < (c : ℝ) := lt_of_lt_of_le ha_pos hc_lo
  have hz_mem : z ∈ Set.Icc a b := by
    simp only [Set.mem_Icc, IntervalRat.mem_def, ha_def, hb_def] at hz ⊢
    exact ⟨hz.1, hz.2⟩

  have hU_open : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hI_sub : Set.Icc a b ⊆ Set.Ioi 0 := by
    intro y hy
    simp only [Set.mem_Ioi]
    exact lt_of_lt_of_le ha_pos hy.1

  have hlog_smooth : ContDiffOn ℝ (n + 1) Real.log (Set.Ioi 0) := by
    apply (Real.contDiffOn_log.of_le le_top).mono
    intro y hy
    simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    exact ne_of_gt hy

  set M : ℝ := n.factorial / a^(n+1) with hM_def
  have hM_nonneg : 0 ≤ M := by
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact pow_nonneg (le_of_lt ha_pos) _

  have hM_bound : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.log y‖ ≤ M := by
    intro y hy
    have hy_pos : 0 < y := lt_of_lt_of_le ha_pos hy.1
    rw [LeanCert.Core.iteratedDeriv_log (Nat.succ_ne_zero n) hy_pos]
    have hn_sub : (n + 1 : ℕ) - 1 = n := Nat.succ_sub_one n
    simp only [Real.norm_eq_abs, hn_sub, zpow_neg, zpow_natCast]
    rw [abs_mul, abs_mul]
    have h_neg_one : |(-1 : ℝ)^n| = 1 := by
      rw [abs_pow]
      simp only [abs_neg, abs_one, one_pow]
    rw [h_neg_one, one_mul]
    have h_fact : |(n.factorial : ℝ)| = n.factorial := abs_of_nonneg (Nat.cast_nonneg _)
    rw [h_fact]
    simp only [abs_inv, abs_pow, abs_of_pos hy_pos]
    rw [← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · exact pow_pos ha_pos _
    · exact pow_le_pow_left₀ (le_of_lt ha_pos) hy.1 _

  have hTaylor := LeanCert.Core.taylor_remainder_bound_on hU_open hI_sub hc_lo hc_hi
    hlog_smooth hM_bound hM_nonneg z hz_mem

  have hcoeffs_match : ∀ i ∈ Finset.range (n + 1), i ≠ 0 →
      (logTaylorCoeffs c n i : ℝ) = iteratedDeriv i Real.log c / i.factorial := by
    intro i hi hi_ne
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_ne
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [logTaylorCoeffs, hi_ne, ite_false, hi_le, ite_true]
    rw [LeanCert.Core.iteratedDeriv_log hi_ne hc_pos]
    have _hsub : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
    have hfact : (i.factorial : ℝ) = i * (i - 1).factorial := by
      have h := Nat.mul_factorial_pred hi_ne
      simp only [← h, Nat.cast_mul]
    simp only [zpow_neg, zpow_natCast]
    rw [hfact]
    have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc_pos
    have hci_ne : (c : ℝ)^i ≠ 0 := pow_ne_zero i hc_ne
    have hi_ne' : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi_ne
    have hfact_ne : ((i - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    push_cast
    rw [div_eq_mul_inv, mul_assoc, mul_assoc ((-1) ^ _), ← mul_one (_ ^ (_ - 1))]
    congr 1
    . grind only
    . grind only
  have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.log c / i.factorial) * (z - c)^i
      = Real.log c + Polynomial.aeval (z - (c : ℝ)) (logTaylorPolyAtCenter c n) := by
    rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_range.mpr (Nat.zero_lt_succ n))]
    simp only [pow_zero, mul_one, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    congr 1
    rw [logTaylorPolyAtCenter]
    rw [map_sum]
    simp only [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    have h0_zero : (algebraMap ℚ ℝ) (logTaylorCoeffs c n 0) * (z - c)^0 = 0 := by
      simp only [logTaylorCoeffs, ite_true, map_zero, zero_mul]
    rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_range.mpr (Nat.zero_lt_succ n))]
    rw [h0_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_mem : i ∈ Finset.range (n + 1) := (Finset.mem_sdiff.mp hi).1
    have hi_ne : i ≠ 0 := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hi).2
    simp only [eq_ratCast]
    rw [← hcoeffs_match i hi_mem hi_ne]

  have hTaylor' : ‖Real.log z - ∑ i ∈ Finset.range (n + 1),
        iteratedDeriv i Real.log c / i.factorial * (z - c)^i‖
      ≤ M * |z - c|^(n + 1) / (n + 1).factorial := hTaylor
  rw [hsum_eq] at hTaylor'
  have h_goal_eq : |Real.log z - Real.log c - Polynomial.aeval (z - (c : ℝ)) (logTaylorPolyAtCenter c n)|
      = ‖Real.log z - (Real.log c + Polynomial.aeval (z - (c : ℝ)) (logTaylorPolyAtCenter c n))‖ := by
    rw [Real.norm_eq_abs]; ring_nf
  rw [h_goal_eq]

  have hbound : M * |z - c|^(n+1) / (n+1).factorial ≤ (logLagrangeRemainder J c n : ℝ) := by
    unfold logLagrangeRemainder
    have hpos' : ¬(J.lo ≤ 0) := not_le.mpr hpos
    simp only [hpos', ite_false]
    have hfact_eq : M / (n+1).factorial = 1 / ((n+1) * a^(n+1)) := by
      rw [hM_def, Nat.factorial_succ]
      have ha_pow_ne : a^(n+1) ≠ 0 := pow_ne_zero _ (ne_of_gt ha_pos)
      have hn1_ne : (n + 1 : ℝ) ≠ 0 := by positivity
      have hfact_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      field_simp
      grind only
    have hstep : M * |z - c|^(n+1) / (n+1).factorial = |z - c|^(n+1) / ((n+1) * a^(n+1)) := by
      have h1 : M * |z - c|^(n+1) / (n+1).factorial = M / (n+1).factorial * |z - c|^(n+1) := by ring
      rw [h1, hfact_eq, one_div, inv_mul_eq_div]
    calc M * |z - c|^(n+1) / (n+1).factorial
        = |z - c|^(n+1) / ((n+1) * a^(n+1)) := hstep
      _ ≤ _ := ?_
    have hz_c_bound : |z - c| ≤ max (|a - c|) (|b - c|) := by
      have hzc : z - c ∈ Set.Icc (a - c) (b - c) := by
        simp only [Set.mem_Icc]
        constructor <;> linarith [hz_mem.1, hz_mem.2]
      exact abs_le_max_abs_abs (Set.mem_Icc.mp hzc).1 (Set.mem_Icc.mp hzc).2
    have ha_eq : a = (J.lo : ℝ) := ha_def
    have hb_eq : b = (J.hi : ℝ) := hb_def
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast, Rat.cast_max,
      Rat.cast_abs, Rat.cast_sub, Rat.cast_add, Rat.cast_one, ha_eq]
    have hJlo_pos : (0 : ℝ) < J.lo := by exact_mod_cast hpos
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hdenom_pos : 0 < (n + 1 : ℝ) * (J.lo : ℝ)^(n+1) := by
      apply mul_pos hn1_pos
      exact pow_pos hJlo_pos _
    apply div_le_div_of_nonneg_right _ (le_of_lt hdenom_pos)
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc |z - ↑c| ≤ max (|a - c|) (|b - c|) := hz_c_bound
      _ = max (|(J.lo : ℝ) - c|) (|(J.hi : ℝ) - c|) := by rw [ha_eq, hb_eq]

  exact le_trans hTaylor' hbound

/-- log z ∈ (tmLog J n).evalSet z for all z in J when J.lo > 0. -/
theorem tmLog_correct (J : IntervalRat) (n : ℕ)
    (tm : TaylorModel) (h : tmLog J n = some tm) :
    ∀ z : ℝ, z ∈ J → Real.log z ∈ tm.evalSet z := by
  intro z hz
  simp only [tmLog] at h
  split_ifs at h with hpos
  simp only [Option.some.injEq] at h
  subst h
  simp only [evalSet, Set.mem_setOf_eq]
  set c := J.midpoint with hc_def
  have hc_pos : 0 < c := by
    simp only [IntervalRat.midpoint, c]
    apply div_pos
    · linarith [J.le]
    · decide
  let c_interval : IntervalRat.IntervalRatPos :=
    { toIntervalRat := IntervalRat.singleton c
      lo_pos := by simp only [IntervalRat.singleton]; exact hc_pos }
  let logc_interval := IntervalRat.logInterval c_interval
  let logc_approx := logc_interval.midpoint
  let logc_error := logc_interval.width / 2
  let base_poly := logTaylorPolyAtCenter c n
  have hbase_poly_def : base_poly = logTaylorPolyAtCenter c n := rfl
  let poly := base_poly + Polynomial.C logc_approx
  have hpoly_def : poly = base_poly + Polynomial.C logc_approx := rfl
  let rem := logRemainderBound J c n logc_error
  have hrem_def : rem = logRemainderBound J c n logc_error := rfl
  let r := Real.log z - Polynomial.aeval (z - (c : ℝ)) poly
  have hr_def : r = Real.log z - Polynomial.aeval (z - (c : ℝ)) poly := rfl
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hr_decomp : r = (Real.log z - Real.log c -
        Polynomial.aeval (z - (c : ℝ)) base_poly) + (Real.log c - (logc_approx : ℝ)) := by
      simp only [hr_def, hpoly_def, map_add, Polynomial.aeval_C, eq_ratCast]
      ring
    have hlog_approx := log_approx_error_bound hc_pos
    have hz_pos : 0 < z := by
      simp only [IntervalRat.mem_def] at hz
      exact lt_of_lt_of_le (by exact_mod_cast hpos) hz.1
    have hrem_eq : (rem : ℝ) = (logLagrangeRemainder J c n : ℝ) + (logc_error : ℝ) := by
      simp only [hrem_def, logRemainderBound, Rat.cast_add]
    have htri : |r| ≤ |Real.log z - Real.log c - Polynomial.aeval (z - (c : ℝ)) base_poly| +
        |Real.log c - logc_approx| := by
      rw [hr_decomp]
      exact abs_add_le _ _
    have hlog_part : |Real.log c - logc_approx| ≤ logc_error := hlog_approx
    have hTaylor_part : |Real.log z - Real.log c - Polynomial.aeval (z - (c : ℝ)) base_poly| ≤
        (logLagrangeRemainder J c n : ℝ) := by
      have hJle : (J.lo : ℝ) ≤ J.hi := by exact_mod_cast J.le
      have hc_lo : (J.lo : ℝ) ≤ c := by
        simp only [IntervalRat.midpoint, c, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
        linarith [hJle]
      have hc_hi : (c : ℝ) ≤ J.hi := by
        simp only [IntervalRat.midpoint, c, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
        linarith [hJle]
      rw [hbase_poly_def]
      exact log_taylor_remainder_bound' J c n z hpos hc_lo hc_hi hz
    have habs_r_le : |r| ≤ rem := by
      calc |r| ≤ |Real.log z - Real.log c - Polynomial.aeval (z - (c : ℝ)) base_poly| +
          |Real.log c - logc_approx| := htri
        _ ≤ (logLagrangeRemainder J c n : ℝ) + (logc_error : ℝ) := by
          apply add_le_add hTaylor_part hlog_part
        _ = (rem : ℝ) := hrem_eq.symm
    rw [abs_le] at habs_r_le
    exact habs_r_le
  · simp only [hr_def]
    ring

end TaylorModel

end LeanCert.Engine
