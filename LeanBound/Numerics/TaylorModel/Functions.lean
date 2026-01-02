/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.TaylorModel.Core
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Taylor Models - Function-Specific Definitions

This file contains Taylor polynomial definitions and remainder bounds for
elementary functions (sin, cos, exp, sinh, cosh, atan, atanh, asinh, sinc, erf),
along with function-level Taylor models and their correctness proofs.

## Main definitions

* `sinTaylorPoly`, `cosTaylorPoly`, `expTaylorPoly`, etc. - Taylor polynomials
* `sinRemainderBound`, `cosRemainderBound`, etc. - Remainder bounds
* `tmSin`, `tmCos`, `tmExp`, etc. - Function-level Taylor models
* `tmSin_correct`, `tmCos_correct`, etc. - Correctness theorems
-/

namespace LeanBound.Numerics

open LeanBound.Core
open Polynomial

namespace TaylorModel

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

/-- Taylor polynomial coefficients for sin at center c = 0:
    sin(x) = x - x³/3! + x⁵/5! - ... -/
noncomputable def sinTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      ((-1 : ℚ) ^ ((i - 1) / 2)) / (Nat.factorial i : ℚ)
    else 0
  else 0

/-- Taylor polynomial for sin of degree n -/
noncomputable def sinTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (sinTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for sin: |sin(x) - T_n(x)| ≤ |x|^{n+1} / (n+1)! since |sin^{(k)}| ≤ 1 -/
noncomputable def sinRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for sin is nonnegative -/
theorem sinRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ sinRemainderBound domain n := by
  unfold sinRemainderBound
  apply div_nonneg
  · apply pow_nonneg
    exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-- Taylor polynomial coefficients for cos at center c = 0:
    cos(x) = 1 - x²/2! + x⁴/4! - ... -/
noncomputable def cosTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 0 then  -- even terms only
      ((-1 : ℚ) ^ (i / 2)) / (Nat.factorial i : ℚ)
    else 0
  else 0

/-- Taylor polynomial for cos of degree n -/
noncomputable def cosTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (cosTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for cos: |cos(x) - T_n(x)| ≤ |x|^{n+1} / (n+1)! since |cos^{(k)}| ≤ 1 -/
noncomputable def cosRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for cos is nonnegative -/
theorem cosRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ cosRemainderBound domain n := by
  unfold cosRemainderBound
  apply div_nonneg
  · apply pow_nonneg
    exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-- Taylor polynomial coefficients for sinh at center c = 0:
    sinh(x) = x + x³/3! + x⁵/5! + ... -/
noncomputable def sinhTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      1 / (Nat.factorial i : ℚ)
    else 0
  else 0

/-- Taylor polynomial for sinh of degree n -/
noncomputable def sinhTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (sinhTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for sinh: |sinh(x) - T_n(x)| ≤ cosh(r) * |x|^{n+1} / (n+1)!
    where r = max(|lo|, |hi|). We use cosh(r) ≤ exp(r) ≤ 3^(⌈r⌉+1). -/
noncomputable def sinhRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  let coshBound := (3 : ℚ) ^ (Nat.ceil r + 1)
  coshBound * r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for sinh is nonnegative -/
theorem sinhRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ sinhRemainderBound domain n := by
  unfold sinhRemainderBound
  simp only
  apply div_nonneg
  · apply mul_nonneg
    · apply pow_nonneg; norm_num
    · apply pow_nonneg
      exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-- Taylor polynomial coefficients for cosh at center c = 0:
    cosh(x) = 1 + x²/2! + x⁴/4! + ... -/
noncomputable def coshTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 0 then  -- even terms only
      1 / (Nat.factorial i : ℚ)
    else 0
  else 0

/-- Taylor polynomial for cosh of degree n -/
noncomputable def coshTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (coshTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for cosh: |cosh(x) - T_n(x)| ≤ cosh(r) * |x|^{n+1} / (n+1)!
    where r = max(|lo|, |hi|). We use cosh(r) ≤ exp(r) ≤ 3^(⌈r⌉+1). -/
noncomputable def coshRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  let coshBound := (3 : ℚ) ^ (Nat.ceil r + 1)
  coshBound * r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for cosh is nonnegative -/
theorem coshRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ coshRemainderBound domain n := by
  unfold coshRemainderBound
  simp only
  apply div_nonneg
  · apply mul_nonneg
    · apply pow_nonneg; norm_num
    · apply pow_nonneg
      exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-! ### atan Taylor polynomial

atan(x) = x - x³/3 + x⁵/5 - x⁷/7 + ... = ∑_{k=0}^∞ (-1)^k x^{2k+1} / (2k+1)

Converges for |x| ≤ 1 (inclusive at endpoints by Abel's theorem).
For |x| > 1, we'd need a different expansion or range reduction.
-/

/-- Taylor polynomial coefficients for atan at center 0:
    atan(x) = x - x³/3 + x⁵/5 - ... = ∑ (-1)^k x^{2k+1} / (2k+1) -/
noncomputable def atanTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      let k := (i - 1) / 2
      ((-1 : ℚ) ^ k) / (2 * k + 1 : ℚ)
    else 0
  else 0

/-- Taylor polynomial for atan of degree n -/
noncomputable def atanTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (atanTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for atan: for |x| ≤ r < 1,
    |atan(x) - T_n(x)| ≤ r^{n+1} / ((n+1) * (1 - r²))
    We use a simplified bound that's safe when r ≤ 1. -/
noncomputable def atanRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- For safety, clamp r to be < 1 by using min(r, 99/100)
  let r_safe := min r (99/100)
  -- Bound: r^{n+1} / ((n+1) * (1 - r²))
  -- Since 1 - r² ≥ 1 - (99/100)² = 199/10000 > 0, this is safe
  let denom := max ((1 - r_safe^2) * (n + 1)) (1/100 : ℚ)
  r_safe ^ (n + 1) / denom

/-- Remainder bound for atan is nonnegative -/
theorem atanRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ atanRemainderBound domain n := by
  unfold atanRemainderBound
  simp only
  apply div_nonneg
  · apply pow_nonneg
    apply le_min
    · exact le_max_of_le_left (abs_nonneg _)
    · norm_num
  · exact le_max_of_le_right (by norm_num)

/-! ### atanh Taylor polynomial

atanh(x) = x + x³/3 + x⁵/5 + x⁷/7 + ... = ∑_{k=0}^∞ x^{2k+1} / (2k+1)

Converges for |x| < 1.
-/

/-- Taylor polynomial coefficients for atanh at center 0:
    atanh(x) = x + x³/3 + x⁵/5 + ... = ∑ x^{2k+1} / (2k+1) -/
noncomputable def atanhTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      let k := (i - 1) / 2
      1 / (2 * k + 1 : ℚ)
    else 0
  else 0

/-- Taylor polynomial for atanh of degree n -/
noncomputable def atanhTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (atanhTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for atanh: for |x| ≤ r < 1,
    |atanh(x) - T_n(x)| ≤ r^{n+1} / (1 - r²)

    Note: A tighter bound with an extra (n+1) factor in the denominator is mathematically
    valid, but we use this looser bound to match what `atanh_series_remainder_bound` proves. -/
noncomputable def atanhRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  let r_safe := min r (99/100)
  let denom := max (1 - r_safe^2) (1/100 : ℚ)
  r_safe ^ (n + 1) / denom

/-- Remainder bound for atanh is nonnegative -/
theorem atanhRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ atanhRemainderBound domain n := by
  unfold atanhRemainderBound
  simp only
  apply div_nonneg
  · apply pow_nonneg
    apply le_min
    · exact le_max_of_le_left (abs_nonneg _)
    · norm_num
  · exact le_max_of_le_right (by norm_num)

/-- The atanh Taylor polynomial evaluates to the partial sum of the atanh series.
    atanh(x) = x + x³/3 + x⁵/5 + ... for |x| < 1 -/
theorem atanhTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    Polynomial.aeval z (atanhTaylorPoly n) =
    ∑ i ∈ Finset.range (n + 1), (atanhTaylorCoeffs n i : ℝ) * z ^ i := by
  simp only [atanhTaylorPoly, map_sum]
  congr 1
  funext i
  simp only [map_mul, aeval_C, map_pow, aeval_X]
  rfl

/-- The atanh series representation: atanh(x) = Σ x^(2k+1)/(2k+1) for |x| < 1.
    Derived from Mathlib's hasSum_log_sub_log_of_abs_lt_one. -/
theorem Real.atanh_hasSum {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ (2 * k + 1) / (2 * k + 1)) (Real.atanh x) := by
  have hlog := Real.hasSum_log_sub_log_of_abs_lt_one hx
  -- log(1+x) - log(1-x) = Σ 2 * x^(2k+1) / (2k+1)
  -- atanh(x) = (1/2)(log(1+x) - log(1-x)) = Σ x^(2k+1) / (2k+1)
  have h1 : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have h2 : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have h_eq : Real.atanh x = (1 / 2) * (Real.log (1 + x) - Real.log (1 - x)) := by
    rw [Real.atanh, Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
  rw [h_eq]
  -- Need: HasSum (fun k => x^(2k+1)/(2k+1)) ((1/2) * (log(1+x) - log(1-x)))
  convert hlog.mul_left (1 / 2) using 1
  funext k
  field_simp

/-- Remainder bound for the atanh series: for |x| < 1, the tail after degree n is bounded.
    Uses the geometric series bound on the tail.

    Proof sketch:
    1. atanh(x) = Σ_{k=0}^∞ x^(2k+1)/(2k+1) by Real.atanh_hasSum
    2. The polynomial computes partial sum of odd terms up to degree n
    3. Remainder = tail = Σ_{k: 2k+1 > n} x^(2k+1)/(2k+1)
    4. |tail| ≤ Σ_{k: 2k+1 > n} |x|^(2k+1) ≤ |x|^(n+1)/(1-x²) by geometric series -/
theorem atanh_series_remainder_bound {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    |Real.atanh x - ∑ k ∈ Finset.range (n + 1), (atanhTaylorCoeffs n k : ℝ) * x ^ k|
      ≤ |x| ^ (n + 1) / (1 - x ^ 2) := by
  -- Get the series representation
  have hseries := Real.atanh_hasSum hx
  -- Key facts about x
  have hx_sq : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
  have h_denom_pos : 0 < 1 - x ^ 2 := by linarith
  have hx_abs_sq : |x| ^ 2 < 1 := by rwa [sq_abs]
  have hx_abs_nonneg : 0 ≤ |x| := abs_nonneg x
  have hx_abs_le : |x| ≤ 1 := le_of_lt hx

  -- Define the series term and the split point m
  let term := fun k : ℕ => x ^ (2 * k + 1) / (2 * k + 1)
  -- m = number of terms with 2k+1 ≤ n, i.e., k ≤ (n-1)/2
  let m := (n + 1) / 2

  -- Key: 2m ≥ n (so 2m+1 ≥ n+1)
  have hm_bound : 2 * m ≥ n := by
    simp only [m]
    omega

  -- Step 1: Show polynomial sum equals partial series sum up to m terms
  have h_poly_eq_partial :
      ∑ i ∈ Finset.range (n + 1), (atanhTaylorCoeffs n i : ℝ) * x ^ i =
      ∑ k ∈ Finset.range m, term k := by
    -- The polynomial has nonzero coefficients only at odd indices 2k+1 ≤ n
    -- which corresponds to k < m = (n+1)/2
    -- We rewrite LHS by filtering to odd terms and reindexing
    have h_even_zero : ∀ i ∈ Finset.range (n + 1), ¬(i % 2 = 1) →
        (atanhTaylorCoeffs n i : ℝ) * x ^ i = 0 := by
      intro i hi hi_not_odd
      have hi_range : i < n + 1 := Finset.mem_range.mp hi
      unfold atanhTaylorCoeffs
      have h_le : i ≤ n := Nat.lt_succ_iff.mp hi_range
      simp only [h_le, ite_true]
      simp only [hi_not_odd, ite_false, Rat.cast_zero, zero_mul]
    -- Split sum into even and odd parts
    conv_lhs =>
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) (fun i => i % 2 = 1)]
    simp only [Finset.sum_eq_zero (fun i hi => h_even_zero i (Finset.mem_filter.mp hi).1
      (Finset.mem_filter.mp hi).2), add_zero]
    -- Reindex: odd i in [0, n] correspond to k in [0, m) where k = (i-1)/2, i = 2k+1
    -- The bijection shows the polynomial sum equals the partial series sum
    symm
    apply Finset.sum_bij (i := fun k _ => 2 * k + 1)
    -- hi: 2k+1 is in filter
    case hi => intro k hk
               simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
               exact ⟨by omega, by omega⟩
    -- h: terms match
    case h => intro k hk
              simp only [Finset.mem_range] at hk
              have h_odd : (2 * k + 1) % 2 = 1 := by omega
              have h_le : 2 * k + 1 ≤ n := by omega
              unfold atanhTaylorCoeffs
              have h_div : (2 * k + 1 - 1) / 2 = k := by omega
              simp only [h_le, ite_true, h_odd, Nat.add_sub_cancel, h_div]
              push_cast
              have h_ne : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
              simp only [term]
              field_simp
    -- i_inj: injective
    case i_inj => intro k₁ _ k₂ _ h; omega
    -- i_surj: surjective
    case i_surj => intro i hi
                   simp only [Finset.mem_filter, Finset.mem_range] at hi
                   exact ⟨(i - 1) / 2, Finset.mem_range.mpr (by omega), by omega⟩

  -- Step 2: The remainder is the tail of the series starting at m
  have h_summable := hseries.summable
  have h_tail_summable : Summable fun k => term (k + m) := (summable_nat_add_iff m).mpr h_summable
  have h_tail_eq : Real.atanh x - ∑ k ∈ Finset.range m, term k = ∑' k, term (k + m) := by
    have h_split := h_summable.sum_add_tsum_nat_add m
    -- h_split : (∑ i ∈ range m, term i) + ∑' i, term (i + m) = ∑' i, term i
    have h_tsum_eq : ∑' i, term i = Real.atanh x := hseries.tsum_eq
    linarith [h_split, h_tsum_eq]

  rw [h_poly_eq_partial, h_tail_eq]

  -- Step 3: Bound the tail by geometric series
  -- |term (k + m)| = |x|^(2(k+m)+1) / (2(k+m)+1) ≤ |x|^(2(k+m)+1) ≤ |x|^(2m+1) * |x|^(2k)
  let geo_term := fun k : ℕ => |x| ^ (2 * m + 1) * (|x| ^ 2) ^ k

  have h_geo_summable : Summable geo_term := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (sq_nonneg _) hx_abs_sq

  have h_term_bound : ∀ k, |term (k + m)| ≤ geo_term k := by
    intro k
    simp only [term, geo_term]
    rw [abs_div, abs_pow]
    have h_pow_eq : |x| ^ (2 * (k + m) + 1) = |x| ^ (2 * m + 1) * (|x| ^ 2) ^ k := by
      have : 2 * (k + m) + 1 = 2 * m + 1 + 2 * k := by ring
      rw [this, pow_add, pow_mul]
    rw [h_pow_eq]
    -- The denominator |2*(k+m)+1| ≥ 1, so dividing makes the numerator smaller
    have h_denom_pos' : (0 : ℝ) < 2 * (k + m : ℕ) + 1 := by positivity
    have h_denom_ge_one : (1 : ℝ) ≤ |(2 : ℝ) * (k + m : ℕ) + 1| := by
      rw [abs_of_pos h_denom_pos']
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      push_cast
      linarith
    calc |x| ^ (2 * m + 1) * (|x| ^ 2) ^ k / |(2 : ℝ) * (k + m : ℕ) + 1|
        ≤ |x| ^ (2 * m + 1) * (|x| ^ 2) ^ k / 1 := by
          apply div_le_div_of_nonneg_left _ (by positivity) h_denom_ge_one
          positivity
      _ = |x| ^ (2 * m + 1) * (|x| ^ 2) ^ k := by ring

  -- Apply the bound
  have h_norm_sum : ‖∑' k, term (k + m)‖ ≤ ∑' k, ‖term (k + m)‖ :=
    norm_tsum_le_tsum_norm h_tail_summable.norm
  simp only [Real.norm_eq_abs] at h_norm_sum
  calc |∑' k, term (k + m)|
      ≤ ∑' k, |term (k + m)| := h_norm_sum
    _ ≤ ∑' k, geo_term k := h_tail_summable.abs.tsum_le_tsum h_term_bound h_geo_summable
    _ = |x| ^ (2 * m + 1) * ∑' k, (|x| ^ 2) ^ k := by
        simp only [geo_term]
        rw [tsum_mul_left]
    _ = |x| ^ (2 * m + 1) / (1 - |x| ^ 2) := by
        rw [tsum_geometric_of_lt_one (sq_nonneg _) hx_abs_sq]
        ring
    _ = |x| ^ (2 * m + 1) / (1 - x ^ 2) := by rw [sq_abs]
    _ ≤ |x| ^ (n + 1) / (1 - x ^ 2) := by
        -- 2m + 1 ≥ n + 1 since 2m ≥ n (from hm_bound)
        -- For 0 ≤ |x| ≤ 1, larger exponent means smaller value
        have h_exp_le : n + 1 ≤ 2 * m + 1 := by omega
        have h_pow_le : |x| ^ (2 * m + 1) ≤ |x| ^ (n + 1) :=
          pow_le_pow_of_le_one hx_abs_nonneg hx_abs_le h_exp_le
        exact div_le_div_of_nonneg_right h_pow_le (by linarith)

/-! ### asinh Taylor polynomial

asinh(x) = x - (1/2) x³/3 + (1·3)/(2·4) x⁵/5 - ...
         = ∑_{k=0}^∞ (-1)^k (2k)! / (4^k (k!)² (2k+1)) x^{2k+1}
-/

/-- Taylor polynomial coefficients for asinh at center 0 -/
noncomputable def asinhTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      let k := (i - 1) / 2
      let num : ℚ := Nat.factorial (2 * k)
      let denom : ℚ := (4 : ℚ) ^ k * (Nat.factorial k) ^ 2 * (2 * k + 1)
      ((-1 : ℚ) ^ k) * (num / denom)
    else 0
  else 0

/-- Taylor polynomial for asinh of degree n -/
noncomputable def asinhTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (asinhTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for asinh: uses derivative bound 1/√(1+x²) ≤ 1 on any interval -/
noncomputable def asinhRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- Crude bound using 2^n as coefficient bound
  (2 : ℚ) ^ (n + 1) * r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for asinh is nonnegative -/
theorem asinhRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ asinhRemainderBound domain n := by
  unfold asinhRemainderBound
  simp only
  apply div_nonneg
  · apply mul_nonneg
    · apply pow_nonneg; norm_num
    · apply pow_nonneg
      exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-! ### sinc Taylor polynomial

sinc(x) = sin(x)/x for x ≠ 0, sinc(0) = 1
       = 1 - x²/6 + x⁴/120 - x⁶/5040 + ...
       = Σ_{n=0}^∞ (-1)^n x^{2n} / (2n+1)!

Note: sinc is entire (analytic everywhere), so the series converges for all x.
-/

/-- Taylor polynomial coefficients for sinc at center 0:
    sinc(x) = 1 - x²/6 + x⁴/120 - ... = Σ (-1)^k x^{2k} / (2k+1)! -/
noncomputable def sincTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 0 then  -- even terms only
      let k := i / 2
      ((-1 : ℚ) ^ k) / (Nat.factorial (2 * k + 1) : ℚ)
    else 0
  else 0

/-- Taylor polynomial for sinc of degree n -/
noncomputable def sincTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (sincTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for sinc: uses the fact that |sinc^(n+1)(ξ)| ≤ 1 for all ξ.
    This follows from |sinc(x)| ≤ 1 and derivatives being bounded.
    We use a crude but safe exponential bound. -/
noncomputable def sincRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- Crude bound: r^{n+1} / (n+1)! (similar to sin remainder)
  r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)

/-- Remainder bound for sinc is nonnegative -/
theorem sincRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ sincRemainderBound domain n := by
  unfold sincRemainderBound
  simp only
  apply div_nonneg
  · apply pow_nonneg
    exact le_max_of_le_left (abs_nonneg _)
  · exact Nat.cast_nonneg _

/-! ### erf Taylor polynomial

erf(x) = (2/√π) ∫₀ˣ e^{-t²} dt
       = (2/√π) Σ_{n=0}^∞ (-1)^n x^{2n+1} / (n! (2n+1))
       = (2/√π) (x - x³/3 + x⁵/10 - x⁷/42 + ...)

We use rational approximations for 2/√π ≈ 1.128379...
-/

/-- Rational approximation of 2/√π (lower bound) -/
def erfCoeff_lo : ℚ := 1128 / 1000  -- ~1.128

/-- Rational approximation of 2/√π (upper bound) -/
def erfCoeff_hi : ℚ := 1129 / 1000  -- ~1.129

/-- Taylor polynomial coefficients for erf at center 0 (using middle approximation):
    erf(x) ≈ (2/√π) Σ (-1)^k x^{2k+1} / (k! (2k+1)) -/
noncomputable def erfTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      let k := (i - 1) / 2
      let coeff := (erfCoeff_lo + erfCoeff_hi) / 2  -- middle approximation
      coeff * ((-1 : ℚ) ^ k) / ((Nat.factorial k : ℚ) * (2 * k + 1))
    else 0
  else 0

/-- Taylor polynomial for erf of degree n -/
noncomputable def erfTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (erfTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for erf: |erf(x)| ≤ 1 for all x, so we use Taylor remainder
    plus coefficient approximation error. -/
noncomputable def erfRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- Taylor remainder plus approximation error for 2/√π
  let taylor_rem := r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)
  -- Coefficient error: |true - approx| ≤ (erfCoeff_hi - erfCoeff_lo)/2 * sum of poly terms
  let coeff_err := (erfCoeff_hi - erfCoeff_lo) / 2 * r  -- simplified upper bound
  taylor_rem + coeff_err

/-- Remainder bound for erf is nonnegative -/
theorem erfRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ erfRemainderBound domain n := by
  unfold erfRemainderBound
  simp only [erfCoeff_hi, erfCoeff_lo]
  apply add_nonneg
  · apply div_nonneg
    · apply pow_nonneg
      exact le_max_of_le_left (abs_nonneg _)
    · exact Nat.cast_nonneg _
  · apply mul_nonneg
    · norm_num
    · exact le_max_of_le_left (abs_nonneg _)

/-! ### Function-level Taylor models

These Taylor models represent functions of a single variable z (not compositions).
The key insight: a TM for g(z) on domain J with center c means:

  ∀ z ∈ J, g(z) ∈ evalSet z = {poly.aeval(z - c) + r : r ∈ remainder}

The polynomial variable is the *same* as the function argument variable.
This makes `taylor_remainder_bound` directly applicable.
-/

/-- Taylor model for sin z on domain J, centered at 0, degree n.
    This represents the function z ↦ sin(z) directly. -/
noncomputable def tmSin (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := sinTaylorPoly n
    remainder := ⟨-sinRemainderBound J n, sinRemainderBound J n,
      by linarith [sinRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for cos z on domain J, centered at 0, degree n.
    This represents the function z ↦ cos(z) directly. -/
noncomputable def tmCos (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := cosTaylorPoly n
    remainder := ⟨-cosRemainderBound J n, cosRemainderBound J n,
      by linarith [cosRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for exp z on domain J, centered at 0, degree n.
    This represents the function z ↦ exp(z) directly. -/
noncomputable def tmExp (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := expTaylorPoly n
    remainder := ⟨-expRemainderBound J n, expRemainderBound J n,
      by linarith [expRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for sinh z on domain J, centered at 0, degree n.
    This represents the function z ↦ sinh(z) directly. -/
noncomputable def tmSinh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := sinhTaylorPoly n
    remainder := ⟨-sinhRemainderBound J n, sinhRemainderBound J n,
      by linarith [sinhRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for cosh z on domain J, centered at 0, degree n.
    This represents the function z ↦ cosh(z) directly. -/
noncomputable def tmCosh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := coshTaylorPoly n
    remainder := ⟨-coshRemainderBound J n, coshRemainderBound J n,
      by linarith [coshRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Function-level Taylor model for tanh at center 0.
    Uses tanh = sinh / cosh with the fact that cosh(x) ≥ 1 > 0 for all x.
    Since cosh bound is always positive, the division is safe. -/
noncomputable def tmTanh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  let tmS := tmSinh J n
  let tmC := tmCosh J n
  -- cosh(x) ≥ 1 for all x, so cosh bound is always positive (lo ≥ 1 - remainder)
  -- We use a conservative approach: if cosh bound somehow contains 0 (shouldn't happen
  -- with reasonable degree), fall back to [-1, 1] which is always valid for tanh.
  if h : IntervalRat.containsZero tmC.bound then
    -- Fallback: tanh ∈ [-1, 1] always
    { poly := 0
      remainder := ⟨-1, 1, by norm_num⟩
      center := 0
      domain := J }
  else
    -- Safe to divide: compute sinh / cosh
    let tmInvC := TaylorModel.inv tmC h
    TaylorModel.mul tmS tmInvC n

/-- Taylor model for atan z on domain J, centered at 0, degree n.
    Valid for |z| ≤ 1 (the series converges there). -/
noncomputable def tmAtan (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := atanTaylorPoly n
    remainder := ⟨-atanRemainderBound J n, atanRemainderBound J n,
      by linarith [atanRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for atanh z on domain J, centered at 0, degree n.
    Valid for |z| < 1. -/
noncomputable def tmAtanh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := atanhTaylorPoly n
    remainder := ⟨-atanhRemainderBound J n, atanhRemainderBound J n,
      by linarith [atanhRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Helper: |z| ≤ radius of interval J for z ∈ J -/
private theorem abs_le_interval_radius' {z : ℝ} {J : IntervalRat} (hz : z ∈ J) :
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

/-- atanh z ∈ (tmAtanh J n).evalSet z for all z in J with |z| < 1.
    Uses the geometric series expansion: atanh(x) = Σ x^(2k+1)/(2k+1) for |x| < 1.

    Precondition: The domain radius must be ≤ 99/100 to ensure the bound formula works.
    This is a reasonable restriction since atanh(x) approaches infinity as x → ±1. -/
theorem tmAtanh_correct (J : IntervalRat) (n : ℕ)
    (hJ_radius : max (|J.lo|) (|J.hi|) ≤ 99/100) :
    ∀ z : ℝ, z ∈ J → |z| < 1 → Real.atanh z ∈ (tmAtanh J n).evalSet z := by
  intro z hz hz_bound
  simp only [tmAtanh, evalSet, Set.mem_setOf_eq]
  -- The remainder r = atanh(z) - P(z) where P is the Taylor polynomial
  set r := Real.atanh z - Polynomial.aeval (z - 0) (atanhTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · -- Show r is in the remainder interval [-bound, bound]
    simp only [IntervalRat.mem_def, Rat.cast_neg]
    -- Rewrite to use our polynomial evaluation lemma
    have hpoly_eq := atanhTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.atanh z -
        ∑ k ∈ Finset.range (n + 1), (atanhTaylorCoeffs n k : ℝ) * z ^ k := by
      rw [hr_def, hpoly_eq]
    -- Apply the series remainder bound
    have hrem := atanh_series_remainder_bound hz_bound n
    rw [← hr_rewrite] at hrem
    -- Now need: |r| ≤ atanhRemainderBound J n
    -- We have: |r| ≤ |z|^(n+1) / (1 - z²)
    -- Need to show this ≤ atanhRemainderBound J n
    have habs_le : |r| ≤ (atanhRemainderBound J n : ℝ) := by
      calc |r| ≤ |z| ^ (n + 1) / (1 - z ^ 2) := hrem
        _ ≤ (atanhRemainderBound J n : ℝ) := by
          -- Key facts:
          -- 1. |z| ≤ max(|J.lo|, |J.hi|) = radius
          -- 2. radius ≤ 99/100 (from hJ_radius)
          -- 3. r_safe = min(radius, 99/100) = radius (since radius ≤ 99/100)
          -- 4. So |z| ≤ r_safe
          have hz_le_radius : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) :=
            abs_le_interval_radius' hz
          have hradius_real : max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) =
              (max (|J.lo|) (|J.hi|) : ℚ) := by simp [Rat.cast_max, Rat.cast_abs]
          set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
          have hr_safe_eq : min radius (99/100) = radius := min_eq_left hJ_radius
          -- Key bounds
          have hradius_le : (radius : ℝ) ≤ 99/100 := by
            calc (radius : ℝ) ≤ ((99/100 : ℚ) : ℝ) := by exact_mod_cast hJ_radius
              _ = 99/100 := by norm_num
          have hradius_lt_one : (radius : ℝ) < 1 := by linarith
          have hrad_nonneg : 0 ≤ (radius : ℝ) := by
            calc (0 : ℝ) ≤ |z| := abs_nonneg z
              _ ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := hz_le_radius
              _ = (radius : ℝ) := hradius_real
          have hz_le_rad : |z| ≤ (radius : ℝ) := by rw [hradius_real] at hz_le_radius; exact hz_le_radius
          -- z² ≤ radius²
          have hz_sq_le : z ^ 2 ≤ (radius : ℝ) ^ 2 := by
            have h1 : |z| ^ 2 ≤ (radius : ℝ) ^ 2 := by
              apply sq_le_sq'
              · calc -(radius : ℝ) ≤ 0 := by linarith
                  _ ≤ |z| := abs_nonneg z
              · exact hz_le_rad
            rwa [sq_abs] at h1
          have h1_minus_z_ge : 1 - z ^ 2 ≥ 1 - (radius : ℝ) ^ 2 := by linarith
          have h1_minus_z_pos : 0 < 1 - z ^ 2 := by nlinarith [sq_nonneg z, sq_abs z]
          have h1_minus_rad_pos : 0 < 1 - (radius : ℝ) ^ 2 := by nlinarith [sq_nonneg (radius : ℝ)]
          -- |z|^(n+1) ≤ radius^(n+1)
          have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) :=
            pow_le_pow_left₀ (abs_nonneg z) hz_le_rad (n + 1)
          have hpow_nonneg : 0 ≤ |z| ^ (n + 1) := pow_nonneg (abs_nonneg z) _
          -- Combine: |z|^(n+1)/(1-z²) ≤ radius^(n+1)/(1-radius²)
          have hbound1 : |z| ^ (n + 1) / (1 - z ^ 2) ≤ (radius : ℝ) ^ (n + 1) / (1 - (radius : ℝ) ^ 2) := by
            gcongr
          -- denom = max(1 - radius², 1/100) = 1 - radius² since radius ≤ 99/100
          have hdenom_eq : max (1 - radius ^ 2) (1/100 : ℚ) = 1 - radius ^ 2 := by
            apply max_eq_left
            have h1 : radius ^ 2 ≤ (99/100 : ℚ) ^ 2 := by
              have hr_nonneg : 0 ≤ radius := le_trans (abs_nonneg J.lo) (le_max_left _ _)
              nlinarith [sq_nonneg radius]
            have h2 : (99/100 : ℚ) ^ 2 = 9801/10000 := by norm_num
            have h3 : 1 - (9801/10000 : ℚ) = 199/10000 := by norm_num
            have h4 : (199/10000 : ℚ) ≥ 1/100 := by norm_num
            linarith
          -- Compute atanhRemainderBound J n = radius^(n+1) / (1 - radius²)
          have hbound_val : atanhRemainderBound J n = radius ^ (n + 1) / (1 - radius ^ 2) := by
            unfold atanhRemainderBound
            simp only [← hradius_def, hr_safe_eq, hdenom_eq]
          -- Cast and conclude
          have hdenom_pos : 0 < (1 - radius ^ 2 : ℚ) := by
            have h1 : radius ^ 2 ≤ (99/100 : ℚ) ^ 2 := by
              have hr_nonneg : 0 ≤ radius := le_trans (abs_nonneg J.lo) (le_max_left _ _)
              nlinarith [sq_nonneg radius]
            have h2 : (99/100 : ℚ) ^ 2 < 1 := by norm_num
            linarith
          calc |z| ^ (n + 1) / (1 - z ^ 2)
              ≤ (radius : ℝ) ^ (n + 1) / (1 - (radius : ℝ) ^ 2) := hbound1
            _ = (atanhRemainderBound J n : ℝ) := by
                rw [hbound_val]
                simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one]
    constructor
    · calc -(atanhRemainderBound J n : ℝ) ≤ -|r| := by linarith [abs_nonneg r]
        _ ≤ r := neg_abs_le r
    · calc r ≤ |r| := le_abs_self r
        _ ≤ (atanhRemainderBound J n : ℝ) := habs_le
  · simp only [hr_def, sub_zero]; ring

/-- Taylor model for asinh z on domain J, centered at 0, degree n. -/
noncomputable def tmAsinh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := asinhTaylorPoly n
    remainder := ⟨-asinhRemainderBound J n, asinhRemainderBound J n,
      by linarith [asinhRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for sinc z on domain J, centered at 0, degree n.
    sinc(z) = sin(z)/z for z ≠ 0, sinc(0) = 1. -/
noncomputable def tmSinc (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := sincTaylorPoly n
    remainder := ⟨-sincRemainderBound J n, sincRemainderBound J n,
      by linarith [sincRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for erf z on domain J, centered at 0, degree n.
    erf(z) = (2/√π) ∫₀ᶻ e^{-t²} dt. -/
noncomputable def tmErf (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := erfTaylorPoly n
    remainder := ⟨-erfRemainderBound J n, erfRemainderBound J n,
      by linarith [erfRemainderBound_nonneg J n]⟩
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

/-- log z ∈ (tmLog J n).evalSet z for all z in J when J.lo > 0.
    Uses the fact that log(z) = log(c) + Taylor expansion around c,
    where log(c) is approximated by a rational interval. -/
theorem tmLog_correct (J : IntervalRat) (n : ℕ)
    (tm : TaylorModel) (h : tmLog J n = some tm) :
    ∀ z : ℝ, z ∈ J → Real.log z ∈ tm.evalSet z := by
  intro z hz
  -- tmLog only returns Some when J.lo > 0
  simp only [tmLog] at h
  split_ifs at h with hpos
  simp only [Option.some.injEq] at h
  subst h
  simp only [evalSet, Set.mem_setOf_eq]
  -- The key insight: we need to show that Real.log z can be written as
  -- P(z - c) + r where P is our polynomial and r is in the remainder interval
  -- For now, use sorry - full proof requires Taylor remainder theorem for log
  -- and showing that the constant term approximation error is bounded
  sorry

/-! ### Helper lemmas for Taylor polynomial correctness -/

/-- iteratedDeriv n sin/cos at 0 cycle together. We prove both simultaneously.
    The pattern follows: sin(0)=0, cos(0)=1 and derivatives cycle sin→cos→-sin→-cos→sin -/
private theorem iteratedDeriv_sin_cos_zero (n : ℕ) :
    (iteratedDeriv n Real.sin 0 =
      if n % 4 = 0 then 0
      else if n % 4 = 1 then 1
      else if n % 4 = 2 then 0
      else -1) ∧
    (iteratedDeriv n Real.cos 0 =
      if n % 4 = 0 then 1
      else if n % 4 = 1 then 0
      else if n % 4 = 2 then -1
      else 0) := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Real.sin_zero, Real.cos_zero, Nat.zero_mod, ↓reduceIte]
    trivial
  | succ n ih =>
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    constructor
    · -- sin case: deriv sin = cos, so iteratedDeriv (n+1) sin = iteratedDeriv n cos
      rw [iteratedDeriv_succ', Real.deriv_sin, ih.2]
      rcases hmod with h | h | h | h <;> (split_ifs <;> simp_all <;> omega)
    · -- cos case: deriv cos = -sin, so iteratedDeriv (n+1) cos = -iteratedDeriv n sin
      rw [iteratedDeriv_succ', Real.deriv_cos', iteratedDeriv_fun_neg, ih.1]
      rcases hmod with h | h | h | h <;> (split_ifs <;> simp_all <;> omega)

/-- iteratedDeriv n sin at 0 -/
theorem iteratedDeriv_sin_zero (n : ℕ) :
    iteratedDeriv n Real.sin 0 =
      if n % 4 = 0 then 0
      else if n % 4 = 1 then 1
      else if n % 4 = 2 then 0
      else -1 :=
  (iteratedDeriv_sin_cos_zero n).1

/-- iteratedDeriv n cos at 0 -/
theorem iteratedDeriv_cos_zero (n : ℕ) :
    iteratedDeriv n Real.cos 0 =
      if n % 4 = 0 then 1
      else if n % 4 = 1 then 0
      else if n % 4 = 2 then -1
      else 0 :=
  (iteratedDeriv_sin_cos_zero n).2

/-- For even n, iteratedDeriv n sin 0 = 0 -/
theorem iteratedDeriv_sin_zero_even {n : ℕ} (hn : n % 2 = 0) :
    iteratedDeriv n Real.sin 0 = 0 := by
  rw [iteratedDeriv_sin_zero]
  have h : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rcases h with h | h <;> simp [h]

/-- For odd n, iteratedDeriv n sin 0 = (-1)^((n-1)/2) -/
theorem iteratedDeriv_sin_zero_odd {n : ℕ} (hn : n % 2 = 1) :
    iteratedDeriv n Real.sin 0 = (-1 : ℝ) ^ ((n - 1) / 2) := by
  rw [iteratedDeriv_sin_zero]
  have h : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h with h | h
  · simp only [h]; norm_num
    have heven : Even ((n - 1) / 2) := by rw [Nat.even_iff]; omega
    rw [Even.neg_one_pow heven]
  · simp only [h]; norm_num
    have hodd : Odd ((n - 1) / 2) := by rw [Nat.odd_iff]; omega
    rw [Odd.neg_one_pow hodd]

/-- The sinTaylorCoeffs match the Mathlib Taylor coefficients for sin at 0 -/
theorem sinTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (sinTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.sin 0 / i.factorial := by
  simp only [sinTaylorCoeffs, hi, ↓reduceIte]
  by_cases hodd : i % 2 = 1
  · -- Odd i: coefficient is (-1)^((i-1)/2) / i!
    simp only [hodd, ↓reduceIte]
    rw [iteratedDeriv_sin_zero_odd hodd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
  · -- Even i: coefficient is 0, and iteratedDeriv i sin 0 = 0
    have heven : i % 2 = 0 := by omega
    simp only [hodd]; norm_num
    rw [iteratedDeriv_sin_zero_even heven, zero_div]

/-- For even n, iteratedDeriv n cos 0 = (-1)^(n/2) -/
theorem iteratedDeriv_cos_zero_even {n : ℕ} (hn : n % 2 = 0) :
    iteratedDeriv n Real.cos 0 = (-1 : ℝ) ^ (n / 2) := by
  rw [iteratedDeriv_cos_zero]
  have h : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rcases h with h | h
  · simp only [h]; norm_num
    have heven : Even (n / 2) := by rw [Nat.even_iff]; omega
    rw [Even.neg_one_pow heven]
  · simp only [h]; norm_num
    have hodd : Odd (n / 2) := by rw [Nat.odd_iff]; omega
    rw [Odd.neg_one_pow hodd]

/-- For odd n, iteratedDeriv n cos 0 = 0 -/
theorem iteratedDeriv_cos_zero_odd {n : ℕ} (hn : n % 2 = 1) :
    iteratedDeriv n Real.cos 0 = 0 := by
  rw [iteratedDeriv_cos_zero]
  have h : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h with h | h <;> simp [h]

/-- The cosTaylorCoeffs match the Mathlib Taylor coefficients for cos at 0 -/
theorem cosTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (cosTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.cos 0 / i.factorial := by
  simp only [cosTaylorCoeffs, hi, ↓reduceIte]
  by_cases heven : i % 2 = 0
  · -- Even i: coefficient is (-1)^(i/2) / i!
    simp only [heven, ↓reduceIte]
    rw [iteratedDeriv_cos_zero_even heven]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
  · -- Odd i: coefficient is 0, and iteratedDeriv i cos 0 = 0
    have hodd : i % 2 = 1 := by omega
    simp only [heven, ↓reduceIte, Rat.cast_zero]
    rw [iteratedDeriv_cos_zero_odd hodd, zero_div]

/-- iteratedDeriv for sinh and cosh at 0, proved together.
    sinh: even n → 0, odd n → 1
    cosh: even n → 1, odd n → 0 -/
theorem iteratedDeriv_sinh_cosh_zero (n : ℕ) :
    iteratedDeriv n Real.sinh 0 = (if n % 2 = 0 then 0 else 1) ∧
    iteratedDeriv n Real.cosh 0 = (if n % 2 = 0 then 1 else 0) := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Real.sinh_zero, Real.cosh_zero, Nat.zero_mod, ↓reduceIte]
    trivial
  | succ n ih =>
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    constructor
    · -- sinh case: deriv sinh = cosh, so iteratedDeriv (n+1) sinh = iteratedDeriv n cosh
      rw [iteratedDeriv_succ', Real.deriv_sinh, ih.2]
      rcases hmod with h | h <;> simp [h, Nat.succ_mod_two_eq_zero_iff]
    · -- cosh case: deriv cosh = sinh, so iteratedDeriv (n+1) cosh = iteratedDeriv n sinh
      rw [iteratedDeriv_succ', Real.deriv_cosh, ih.1]
      rcases hmod with h | h <;> simp [h, Nat.succ_mod_two_eq_zero_iff]

/-- iteratedDeriv n sinh at 0 -/
theorem iteratedDeriv_sinh_zero (n : ℕ) :
    iteratedDeriv n Real.sinh 0 = if n % 2 = 0 then 0 else 1 :=
  (iteratedDeriv_sinh_cosh_zero n).1

/-- iteratedDeriv n cosh at 0 -/
theorem iteratedDeriv_cosh_zero (n : ℕ) :
    iteratedDeriv n Real.cosh 0 = if n % 2 = 0 then 1 else 0 :=
  (iteratedDeriv_sinh_cosh_zero n).2

/-- The sinhTaylorCoeffs match the Mathlib Taylor coefficients for sinh at 0 -/
theorem sinhTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (sinhTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.sinh 0 / i.factorial := by
  simp only [sinhTaylorCoeffs, hi, ↓reduceIte]
  by_cases hodd : i % 2 = 1
  · -- Odd i: coefficient is 1/i!
    have hne : i % 2 ≠ 0 := by omega
    simp only [hodd, ↓reduceIte]
    rw [iteratedDeriv_sinh_zero]
    simp only [hne, ↓reduceIte, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  · -- Even i: coefficient is 0
    have heven : i % 2 = 0 := by omega
    simp only [hodd]; norm_num
    rw [iteratedDeriv_sinh_zero]
    simp only [heven, ↓reduceIte, zero_div]

/-- The coshTaylorCoeffs match the Mathlib Taylor coefficients for cosh at 0 -/
theorem coshTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (coshTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.cosh 0 / i.factorial := by
  simp only [coshTaylorCoeffs, hi, ↓reduceIte]
  by_cases heven : i % 2 = 0
  · -- Even i: coefficient is 1/i!
    simp only [heven, ↓reduceIte]
    rw [iteratedDeriv_cosh_zero]
    simp only [heven, ↓reduceIte, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  · -- Odd i: coefficient is 0
    have hodd : i % 2 = 1 := by omega
    simp only [heven]; norm_num
    rw [iteratedDeriv_cosh_zero]
    simp only [heven, ↓reduceIte, zero_div]

/-- sinhTaylorPoly evaluates to the standard Taylor sum for sinh at 0. -/
theorem sinhTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (sinhTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sinh 0 / i.factorial) * z ^ i := by
  simp only [sinhTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have h := sinhTaylorCoeffs_eq_iteratedDeriv n i hi_le
  change (sinhTaylorCoeffs n i : ℝ) * z ^ i = _
  rw [h]

/-- coshTaylorPoly evaluates to the standard Taylor sum for cosh at 0. -/
theorem coshTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (coshTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cosh 0 / i.factorial) * z ^ i := by
  simp only [coshTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have h := coshTaylorCoeffs_eq_iteratedDeriv n i hi_le
  change (coshTaylorCoeffs n i : ℝ) * z ^ i = _
  rw [h]

/-- sinTaylorPoly evaluates to the standard Taylor sum for sin at 0.
    This connects our rational polynomial to Mathlib's Taylor series. -/
theorem sinTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (sinTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * z ^ i := by
  simp only [sinTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have h := sinTaylorCoeffs_eq_iteratedDeriv n i hi_le
  -- algebraMap ℚ ℝ is definitionally equal to Rat.cast
  change (sinTaylorCoeffs n i : ℝ) * z ^ i = _
  rw [h]

/-- cosTaylorPoly evaluates to the standard Taylor sum for cos at 0. -/
theorem cosTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (cosTaylorPoly n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * z ^ i := by
  simp only [cosTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
  have h := cosTaylorCoeffs_eq_iteratedDeriv n i hi_le
  change (cosTaylorCoeffs n i : ℝ) * z ^ i = _
  rw [h]

/-! ### Correctness of function-level Taylor models

These theorems use `taylor_remainder_bound` from Core/Taylor.lean directly.
The polynomial variable and function argument are the same, so the Taylor
remainder bound applies without composition issues.
-/

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

/-- sin z ∈ (tmSin J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.sin, c = 0, M = 1. -/
theorem tmSin_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.sin z ∈ (tmSin J n).evalSet z := by
  intro z hz
  simp only [tmSin, evalSet, Set.mem_setOf_eq]
  set r := Real.sin z - Polynomial.aeval (z - 0) (sinTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    -- Rewrite polynomial to Mathlib form
    have hpoly_eq := sinTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    -- The remainder r = sin z - ∑ (iteratedDeriv i sin 0 / i!) * z^i
    have hr_rewrite : r = Real.sin z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sin 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
    -- Apply taylor_remainder_bound with f = sin, c = 0, M = 1
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
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.sin x‖ ≤ 1 := by
      intro x _
      exact (LeanBound.Core.sin_cos_deriv_bound (n + 1) x).1
    have hf : ContDiff ℝ (n + 1) Real.sin := Real.contDiff_sin.of_le le_top
    have hTaylor := LeanBound.Core.taylor_remainder_bound hab hca hcb hf hM (by norm_num : (0 : ℝ) ≤ 1) z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ 1 * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    simp only [one_mul] at hr_bound
    -- |r| ≤ sinRemainderBound since |z| ≤ radius
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hrem_eq : (sinRemainderBound J n : ℝ) = (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
      simp only [sinRemainderBound, hradius_def, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]
      exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hrem_ge : (sinRemainderBound J n : ℝ) ≥ |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hrem_eq]
      apply div_le_div_of_nonneg_right hpow_le (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ sinRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

/-- cos z ∈ (tmCos J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.cos, c = 0, M = 1. -/
theorem tmCos_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.cos z ∈ (tmCos J n).evalSet z := by
  intro z hz
  simp only [tmCos, evalSet, Set.mem_setOf_eq]
  set r := Real.cos z - Polynomial.aeval (z - 0) (cosTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hpoly_eq := cosTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.cos z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.cos 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
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
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.cos x‖ ≤ 1 := by
      intro x _
      exact (LeanBound.Core.sin_cos_deriv_bound (n + 1) x).2
    have hf : ContDiff ℝ (n + 1) Real.cos := Real.contDiff_cos.of_le le_top
    have hTaylor := LeanBound.Core.taylor_remainder_bound hab hca hcb hf hM (by norm_num : (0 : ℝ) ≤ 1) z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ 1 * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    simp only [one_mul] at hr_bound
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hrem_eq : (cosRemainderBound J n : ℝ) = (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
      simp only [cosRemainderBound, hradius_def, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]
      exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hrem_ge : (cosRemainderBound J n : ℝ) ≥ |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hrem_eq]
      apply div_le_div_of_nonneg_right hpow_le (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ cosRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

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
      exact LeanBound.Core.exp_deriv_bound hab (n + 1) x hx
    have hf : ContDiff ℝ (n + 1) Real.exp := Real.contDiff_exp.of_le le_top
    have hTaylor := LeanBound.Core.taylor_remainder_bound hab hca hcb hf hM hM_pos z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ M * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    -- Now show |r| ≤ expRemainderBound J n
    -- expRemainderBound J n = 3^(⌈radius⌉+1) * radius^{n+1} / (n+1)!
    -- We need M * |z|^{n+1}/(n+1)! ≤ expRemainderBound
    -- Since M = exp(b) ≤ exp(radius) ≤ 3^(⌈radius⌉+1) and |z| ≤ radius
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    -- b ≤ radius since b = max(J.hi, 0) and J.hi ≤ |J.hi| ≤ radius
    have hb_le_radius : b ≤ radius := by
      simp only [hb_def, hradius_real]
      apply max_le
      · calc (J.hi : ℝ) ≤ |(J.hi : ℝ)| := le_abs_self _
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := le_max_right _ _
      · calc (0 : ℝ) ≤ |↑J.lo| := abs_nonneg _
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := le_max_left _ _
    -- exp(b) ≤ exp(radius)
    have hexp_b_le : Real.exp b ≤ Real.exp radius := Real.exp_le_exp.mpr hb_le_radius
    -- For exp(radius), we use the crude bound exp(r) ≤ 3^(⌈r⌉+1) for r ≥ 0
    -- Note: expRemainderBound uses this conservative bound
    have hradius_nn : 0 ≤ (radius : ℝ) := by
      rw [hradius_real]
      exact le_max_of_le_left (abs_nonneg _)
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]; exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    -- The remainder bound
    have hrem_def : expRemainderBound J n =
        (3 : ℚ) ^ (Nat.ceil radius + 1) * radius ^ (n + 1) / (Nat.factorial (n + 1) : ℚ) := by
      simp only [expRemainderBound, hradius_def]
    -- exp(radius) ≤ 3^(⌈radius⌉+1) - this is a crude but sound bound
    -- For radius ≥ 0: exp(radius) ≤ e^⌈radius⌉ ≤ 3^⌈radius⌉ ≤ 3^(⌈radius⌉+1)
    have hexp_le_three_pow : Real.exp (radius : ℝ) ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := by
      -- exp(1) < 2.72 < 3 (from Mathlib's exp_one_lt_d9)
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
    -- Combine: M * |z|^{n+1}/(n+1)! ≤ 3^{ceil+1} * radius^{n+1}/(n+1)!
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

/-- sinh z ∈ (tmSinh J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.sinh, M = exp(max(|lo|,|hi|)). -/
theorem tmSinh_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.sinh z ∈ (tmSinh J n).evalSet z := by
  intro z hz
  simp only [tmSinh, evalSet, Set.mem_setOf_eq]
  set r := Real.sinh z - Polynomial.aeval (z - 0) (sinhTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hpoly_eq := sinhTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.sinh z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sinh 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
    -- Apply taylor_remainder_bound with f = sinh, c = 0, M = exp(max(|a|,|b|))
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
    set M := Real.exp (max (|a|) (|b|)) with hM_def
    have hM_pos : 0 ≤ M := le_of_lt (Real.exp_pos _)
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.sinh x‖ ≤ M := by
      intro x hx
      exact (LeanBound.Core.sinh_cosh_deriv_bound hab (n + 1) x hx).1
    have hf : ContDiff ℝ (n + 1) Real.sinh := Real.contDiff_sinh.of_le le_top
    have hTaylor := LeanBound.Core.taylor_remainder_bound hab hca hcb hf hM hM_pos z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ M * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    -- Now show |r| ≤ sinhRemainderBound J n
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    -- M = exp(max(|a|,|b|)) ≤ exp(radius) since max(|a|,|b|) ≤ radius
    have hab_le_radius : max (|a|) (|b|) ≤ radius := by
      simp only [ha_def, hb_def, hradius_real]
      apply max_le
      · -- |min(J.lo, 0)| ≤ max(|J.lo|, |J.hi|)
        calc |min (J.lo : ℝ) 0| ≤ max |(J.lo : ℝ)| |(0 : ℝ)| := abs_min_le_max_abs_abs
          _ = max |(J.lo : ℝ)| 0 := by simp
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := max_le_max_left _ (abs_nonneg _)
      · -- |max(J.hi, 0)| ≤ max(|J.lo|, |J.hi|)
        calc |max (J.hi : ℝ) 0| ≤ max |(J.hi : ℝ)| |(0 : ℝ)| := abs_max_le_max_abs_abs
          _ = max |(J.hi : ℝ)| 0 := by simp
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := max_le (le_max_right _ _) (le_max_of_le_left (abs_nonneg _))
    have hM_le : M ≤ Real.exp radius := Real.exp_le_exp.mpr hab_le_radius
    have hradius_nn : 0 ≤ (radius : ℝ) := by
      rw [hradius_real]; exact le_max_of_le_left (abs_nonneg _)
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]; exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    -- exp(radius) ≤ 3^(⌈radius⌉+1)
    have hexp_le_three_pow : Real.exp (radius : ℝ) ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := by
      have he_le_3 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
      calc Real.exp (radius : ℝ)
          ≤ Real.exp (Nat.ceil radius : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast Nat.le_ceil radius)
        _ = Real.exp 1 ^ (Nat.ceil radius) := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ 3 ^ (Nat.ceil radius) := by
            apply pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1))
            exact he_le_3
        _ ≤ 3 ^ (Nat.ceil radius + 1) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ _)
    have hM_bound : M ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := le_trans hM_le hexp_le_three_pow
    have hrem_ge : (sinhRemainderBound J n : ℝ) ≥ M * |z| ^ (n + 1) / (n + 1).factorial := by
      have h1 : M * |z| ^ (n + 1) ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) * (radius : ℝ) ^ (n + 1) :=
        mul_le_mul hM_bound hpow_le (pow_nonneg (abs_nonneg z) _) (by linarith)
      calc (sinhRemainderBound J n : ℝ)
          = (3 : ℝ) ^ (Nat.ceil radius + 1) * (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
            simp only [sinhRemainderBound, hradius_def, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
              Rat.cast_natCast, Rat.cast_ofNat]
        _ ≥ M * |z| ^ (n + 1) / (n + 1).factorial :=
            div_le_div_of_nonneg_right h1 (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ sinhRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

/-- cosh z ∈ (tmCosh J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.cosh, M = exp(max(|lo|,|hi|)). -/
theorem tmCosh_correct (J : IntervalRat) (n : ℕ) :
    ∀ z : ℝ, z ∈ J → Real.cosh z ∈ (tmCosh J n).evalSet z := by
  intro z hz
  simp only [tmCosh, evalSet, Set.mem_setOf_eq]
  set r := Real.cosh z - Polynomial.aeval (z - 0) (coshTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hpoly_eq := coshTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.cosh z - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.cosh 0 / i.factorial) * z ^ i := by
      rw [hr_def, hpoly_eq]
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
    set M := Real.exp (max (|a|) (|b|)) with hM_def
    have hM_pos : 0 ≤ M := le_of_lt (Real.exp_pos _)
    have hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv (n + 1) Real.cosh x‖ ≤ M := by
      intro x hx
      exact (LeanBound.Core.sinh_cosh_deriv_bound hab (n + 1) x hx).2
    have hf : ContDiff ℝ (n + 1) Real.cosh := Real.contDiff_cosh.of_le le_top
    have hTaylor := LeanBound.Core.taylor_remainder_bound hab hca hcb hf hM hM_pos z hz_ab
    simp only [sub_zero] at hTaylor
    have hr_bound : ‖r‖ ≤ M * |z| ^ (n + 1) / (n + 1).factorial := by
      rw [hr_rewrite]
      exact hTaylor
    rw [Real.norm_eq_abs] at hr_bound
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hab_le_radius : max (|a|) (|b|) ≤ radius := by
      simp only [ha_def, hb_def, hradius_real]
      apply max_le
      · -- |min(J.lo, 0)| ≤ max(|J.lo|, |J.hi|)
        calc |min (J.lo : ℝ) 0| ≤ max |(J.lo : ℝ)| |(0 : ℝ)| := abs_min_le_max_abs_abs
          _ = max |(J.lo : ℝ)| 0 := by simp
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := max_le_max_left _ (abs_nonneg _)
      · -- |max(J.hi, 0)| ≤ max(|J.lo|, |J.hi|)
        calc |max (J.hi : ℝ) 0| ≤ max |(J.hi : ℝ)| |(0 : ℝ)| := abs_max_le_max_abs_abs
          _ = max |(J.hi : ℝ)| 0 := by simp
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := max_le (le_max_right _ _) (le_max_of_le_left (abs_nonneg _))
    have hM_le : M ≤ Real.exp radius := Real.exp_le_exp.mpr hab_le_radius
    have hradius_nn : 0 ≤ (radius : ℝ) := by
      rw [hradius_real]; exact le_max_of_le_left (abs_nonneg _)
    have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) := by
      apply pow_le_pow_left₀ (abs_nonneg z)
      rw [hradius_real]; exact habs_z_le
    have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hexp_le_three_pow : Real.exp (radius : ℝ) ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := by
      have he_le_3 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
      calc Real.exp (radius : ℝ)
          ≤ Real.exp (Nat.ceil radius : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast Nat.le_ceil radius)
        _ = Real.exp 1 ^ (Nat.ceil radius) := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ 3 ^ (Nat.ceil radius) := by
            apply pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1))
            exact he_le_3
        _ ≤ 3 ^ (Nat.ceil radius + 1) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ _)
    have hM_bound : M ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) := le_trans hM_le hexp_le_three_pow
    have hrem_ge : (coshRemainderBound J n : ℝ) ≥ M * |z| ^ (n + 1) / (n + 1).factorial := by
      have h1 : M * |z| ^ (n + 1) ≤ (3 : ℝ) ^ (Nat.ceil radius + 1) * (radius : ℝ) ^ (n + 1) :=
        mul_le_mul hM_bound hpow_le (pow_nonneg (abs_nonneg z) _) (by linarith)
      calc (coshRemainderBound J n : ℝ)
          = (3 : ℝ) ^ (Nat.ceil radius + 1) * (radius : ℝ) ^ (n + 1) / (n + 1).factorial := by
            simp only [coshRemainderBound, hradius_def, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
              Rat.cast_natCast, Rat.cast_ofNat]
        _ ≥ M * |z| ^ (n + 1) / (n + 1).factorial :=
            div_le_div_of_nonneg_right h1 (le_of_lt hfact_pos)
    have hr_le_rem : |r| ≤ coshRemainderBound J n := le_trans hr_bound hrem_ge
    constructor
    · have := neg_abs_le r; linarith
    · exact le_trans (le_abs_self r) hr_le_rem
  · simp only [hr_def, sub_zero]; ring_nf

end TaylorModel

end LeanBound.Numerics
