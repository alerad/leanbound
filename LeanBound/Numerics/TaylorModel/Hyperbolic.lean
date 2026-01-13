/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.TaylorModel.Core
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Taylor Models - Hyperbolic Functions

This file contains Taylor polynomial definitions and remainder bounds for
hyperbolic functions (sinh, cosh, tanh, atan, atanh, asinh), along with
function-level Taylor models and their correctness proofs.

## Main definitions

* `sinhTaylorPoly`, `coshTaylorPoly`, etc. - Taylor polynomials
* `sinhRemainderBound`, `coshRemainderBound`, etc. - Remainder bounds
* `tmSinh`, `tmCosh`, `tmTanh`, `tmAtan`, `tmAtanh`, `tmAsinh` - Taylor models
* `tmSinh_correct`, `tmCosh_correct`, `tmAtanh_correct` - Correctness theorems
-/

namespace LeanBound.Numerics

open LeanBound.Core
open Polynomial

namespace TaylorModel

/-! ### sinh Taylor polynomial -/

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

/-! ### cosh Taylor polynomial -/

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
-/

/-- Taylor polynomial coefficients for atan at center 0 -/
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

/-- Remainder bound for atan -/
noncomputable def atanRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  let r_safe := min r (99/100)  -- clamp to avoid issues near |x|=1
  let denom := max (1 - r_safe^2) (1/100)
  r_safe^(n+1) / denom

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
  · apply le_max_of_le_right; norm_num

/-! ### atanh Taylor polynomial

atanh(x) = x + x³/3 + x⁵/5 + ... = ∑_{k=0}^∞ x^{2k+1} / (2k+1)

Converges for |x| < 1.
-/

/-- Taylor polynomial coefficients for atanh at center 0 -/
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

/-- Remainder bound for atanh -/
noncomputable def atanhRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  let r_safe := min r (99/100)
  let denom := max (1 - r_safe^2) (1/100)
  r_safe^(n+1) / denom

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
  · apply le_max_of_le_right; norm_num

/-! ### asinh Taylor polynomial -/

/-- Taylor polynomial coefficients for asinh at center 0 -/
noncomputable def asinhTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then
      let k := (i - 1) / 2
      ((-1 : ℚ)^k) * (Nat.factorial (2*k)) /
        ((4 : ℚ)^k * ((Nat.factorial k)^2 : ℚ) * (2*k + 1 : ℚ))
    else 0
  else 0

/-- Taylor polynomial for asinh of degree n -/
noncomputable def asinhTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (asinhTaylorCoeffs n i) * Polynomial.X ^ i

/-- Remainder bound for asinh -/
noncomputable def asinhRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
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

/-! ### Function-level Taylor models -/

/-- Taylor model for sinh z on domain J, centered at 0, degree n. -/
noncomputable def tmSinh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := sinhTaylorPoly n
    remainder := ⟨-sinhRemainderBound J n, sinhRemainderBound J n,
      by linarith [sinhRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Taylor model for cosh z on domain J, centered at 0, degree n. -/
noncomputable def tmCosh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := coshTaylorPoly n
    remainder := ⟨-coshRemainderBound J n, coshRemainderBound J n,
      by linarith [coshRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-- Function-level Taylor model for tanh at center 0.
    Uses tanh = sinh / cosh with the fact that cosh(x) ≥ 1 > 0 for all x. -/
noncomputable def tmTanh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  let tmS := tmSinh J n
  let tmC := tmCosh J n
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
    Valid for |z| ≤ 1. -/
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

/-- Taylor model for asinh z on domain J, centered at 0, degree n. -/
noncomputable def tmAsinh (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := asinhTaylorPoly n
    remainder := ⟨-asinhRemainderBound J n, asinhRemainderBound J n,
      by linarith [asinhRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }

/-! ### Helper lemmas -/

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

/-- Helper: z ∈ J means z ∈ [J.lo, J.hi] as real numbers -/
private theorem mem_Icc_of_mem_interval {z : ℝ} {J : IntervalRat} (hz : z ∈ J) :
    z ∈ Set.Icc (J.lo : ℝ) (J.hi : ℝ) := by
  simp only [IntervalRat.mem_def] at hz
  exact ⟨hz.1, hz.2⟩

/-- Helper: |z| ≤ radius of interval J for z ∈ J (duplicate for consistency) -/
private theorem abs_le_interval_radius {z : ℝ} {J : IntervalRat} (hz : z ∈ J) :
    |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius' hz

/-! ### Helper lemmas for iterated derivatives -/

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
    · -- sinh case: deriv sinh = cosh
      rw [iteratedDeriv_succ', Real.deriv_sinh, ih.2]
      rcases hmod with h | h <;> simp [h, Nat.succ_mod_two_eq_zero_iff]
    · -- cosh case: deriv cosh = sinh
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
  · have hne : i % 2 ≠ 0 := by omega
    simp only [hodd, ↓reduceIte]
    rw [iteratedDeriv_sinh_zero]
    simp only [hne, ↓reduceIte, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  · have heven : i % 2 = 0 := by omega
    simp only [hodd]; norm_num
    rw [iteratedDeriv_sinh_zero]
    simp only [heven, ↓reduceIte, zero_div]

/-- The coshTaylorCoeffs match the Mathlib Taylor coefficients for cosh at 0 -/
theorem coshTaylorCoeffs_eq_iteratedDeriv (n i : ℕ) (hi : i ≤ n) :
    (coshTaylorCoeffs n i : ℝ) = iteratedDeriv i Real.cosh 0 / i.factorial := by
  simp only [coshTaylorCoeffs, hi, ↓reduceIte]
  by_cases heven : i % 2 = 0
  · simp only [heven, ↓reduceIte]
    rw [iteratedDeriv_cosh_zero]
    simp only [heven, ↓reduceIte, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  · have hodd : i % 2 = 1 := by omega
    simp only [heven]; norm_num
    rw [iteratedDeriv_cosh_zero]
    simp only [heven, ↓reduceIte, zero_div]

/-! ### Polynomial evaluation lemmas -/

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

/-! ### atanh correctness helper -/

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

/-- atanhTaylorPoly evaluates to the standard sum. -/
theorem atanhTaylorPoly_aeval_eq (n : ℕ) (z : ℝ) :
    (Polynomial.aeval z (atanhTaylorPoly n) : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (atanhTaylorCoeffs n k : ℝ) * z ^ k := by
  simp only [atanhTaylorPoly, map_sum, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eq_ratCast]

/-- Remainder bound for the atanh series: for |z| < 1, the tail after degree n is bounded.
    Uses the geometric series bound on the tail.

    Proof sketch:
    1. atanh(z) = Σ_{k=0}^∞ z^(2k+1)/(2k+1) by Real.atanh_hasSum
    2. The polynomial computes partial sum of odd terms up to degree n
    3. Remainder = tail = Σ_{k: 2k+1 > n} z^(2k+1)/(2k+1)
    4. |tail| ≤ Σ_{k: 2k+1 > n} |z|^(2k+1) ≤ |z|^(n+1)/(1-z²) by geometric series -/
theorem atanh_series_remainder_bound {z : ℝ} (hz : |z| < 1) (n : ℕ) :
    |Real.atanh z - ∑ k ∈ Finset.range (n + 1), (atanhTaylorCoeffs n k : ℝ) * z ^ k| ≤
    |z| ^ (n + 1) / (1 - z ^ 2) := by
  -- Get the series representation
  have hseries := Real.atanh_hasSum hz
  -- Key facts about z
  have hz_sq : z ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one z).mpr hz
  have h_denom_pos : 0 < 1 - z ^ 2 := by linarith
  have hz_abs_sq : |z| ^ 2 < 1 := by rwa [sq_abs]
  have hz_abs_nonneg : 0 ≤ |z| := abs_nonneg z
  have hz_abs_le : |z| ≤ 1 := le_of_lt hz

  -- Define the series term and the split point m
  let term := fun k : ℕ => z ^ (2 * k + 1) / (2 * k + 1)
  -- m = number of terms with 2k+1 ≤ n, i.e., k ≤ (n-1)/2
  let m := (n + 1) / 2

  -- Key: 2m ≥ n (so 2m+1 ≥ n+1)
  have hm_bound : 2 * m ≥ n := by
    simp only [m]
    omega

  -- Step 1: Show polynomial sum equals partial series sum up to m terms
  have h_poly_eq_partial :
      ∑ i ∈ Finset.range (n + 1), (atanhTaylorCoeffs n i : ℝ) * z ^ i =
      ∑ k ∈ Finset.range m, term k := by
    -- The polynomial has nonzero coefficients only at odd indices 2k+1 ≤ n
    -- which corresponds to k < m = (n+1)/2
    -- We rewrite LHS by filtering to odd terms and reindexing
    have h_even_zero : ∀ i ∈ Finset.range (n + 1), ¬(i % 2 = 1) →
        (atanhTaylorCoeffs n i : ℝ) * z ^ i = 0 := by
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
  have h_tail_eq : Real.atanh z - ∑ k ∈ Finset.range m, term k = ∑' k, term (k + m) := by
    have h_split := h_summable.sum_add_tsum_nat_add m
    -- h_split : (∑ i ∈ range m, term i) + ∑' i, term (i + m) = ∑' i, term i
    have h_tsum_eq : ∑' i, term i = Real.atanh z := hseries.tsum_eq
    linarith [h_split, h_tsum_eq]

  rw [h_poly_eq_partial, h_tail_eq]

  -- Step 3: Bound the tail by geometric series
  -- |term (k + m)| = |z|^(2(k+m)+1) / (2(k+m)+1) ≤ |z|^(2(k+m)+1) ≤ |z|^(2m+1) * |z|^(2k)
  let geo_term := fun k : ℕ => |z| ^ (2 * m + 1) * (|z| ^ 2) ^ k

  have h_geo_summable : Summable geo_term := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (sq_nonneg _) hz_abs_sq

  have h_term_bound : ∀ k, |term (k + m)| ≤ geo_term k := by
    intro k
    simp only [term, geo_term]
    rw [abs_div, abs_pow]
    have h_pow_eq : |z| ^ (2 * (k + m) + 1) = |z| ^ (2 * m + 1) * (|z| ^ 2) ^ k := by
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
    calc |z| ^ (2 * m + 1) * (|z| ^ 2) ^ k / |(2 : ℝ) * (k + m : ℕ) + 1|
        ≤ |z| ^ (2 * m + 1) * (|z| ^ 2) ^ k / 1 := by
          apply div_le_div_of_nonneg_left _ (by positivity) h_denom_ge_one
          positivity
      _ = |z| ^ (2 * m + 1) * (|z| ^ 2) ^ k := by ring

  -- Apply the bound
  have h_norm_sum : ‖∑' k, term (k + m)‖ ≤ ∑' k, ‖term (k + m)‖ :=
    norm_tsum_le_tsum_norm h_tail_summable.norm
  simp only [Real.norm_eq_abs] at h_norm_sum
  calc |∑' k, term (k + m)|
      ≤ ∑' k, |term (k + m)| := h_norm_sum
    _ ≤ ∑' k, geo_term k := h_tail_summable.abs.tsum_le_tsum h_term_bound h_geo_summable
    _ = |z| ^ (2 * m + 1) * ∑' k, (|z| ^ 2) ^ k := by
        simp only [geo_term]
        rw [tsum_mul_left]
    _ = |z| ^ (2 * m + 1) / (1 - |z| ^ 2) := by
        rw [tsum_geometric_of_lt_one (sq_nonneg _) hz_abs_sq]
        ring
    _ = |z| ^ (2 * m + 1) / (1 - z ^ 2) := by rw [sq_abs]
    _ ≤ |z| ^ (n + 1) / (1 - z ^ 2) := by
        -- 2m + 1 ≥ n + 1 since 2m ≥ n (from hm_bound)
        -- For 0 ≤ |z| ≤ 1, larger exponent means smaller value
        have h_exp_le : n + 1 ≤ 2 * m + 1 := by omega
        have h_pow_le : |z| ^ (2 * m + 1) ≤ |z| ^ (n + 1) :=
          pow_le_pow_of_le_one hz_abs_nonneg hz_abs_le h_exp_le
        exact div_le_div_of_nonneg_right h_pow_le (by linarith)

/-! ### Correctness theorems -/

/-- atanh z ∈ (tmAtanh J n).evalSet z for all z in J with |z| < 1.
    Precondition: The domain radius must be ≤ 99/100. -/
theorem tmAtanh_correct (J : IntervalRat) (n : ℕ)
    (hJ_radius : max (|J.lo|) (|J.hi|) ≤ 99/100) :
    ∀ z : ℝ, z ∈ J → |z| < 1 → Real.atanh z ∈ (tmAtanh J n).evalSet z := by
  intro z hz hz_bound
  simp only [tmAtanh, evalSet, Set.mem_setOf_eq]
  set r := Real.atanh z - Polynomial.aeval (z - 0) (atanhTaylorPoly n) with hr_def
  refine ⟨r, ?_, ?_⟩
  · simp only [IntervalRat.mem_def, Rat.cast_neg]
    have hpoly_eq := atanhTaylorPoly_aeval_eq n z
    simp only [sub_zero] at hr_def hpoly_eq
    have hr_rewrite : r = Real.atanh z -
        ∑ k ∈ Finset.range (n + 1), (atanhTaylorCoeffs n k : ℝ) * z ^ k := by
      rw [hr_def, hpoly_eq]
    have hrem := atanh_series_remainder_bound hz_bound n
    rw [← hr_rewrite] at hrem
    have habs_le : |r| ≤ (atanhRemainderBound J n : ℝ) := by
      calc |r| ≤ |z| ^ (n + 1) / (1 - z ^ 2) := hrem
        _ ≤ (atanhRemainderBound J n : ℝ) := by
          have hz_le_radius : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) :=
            abs_le_interval_radius' hz
          have hradius_real : max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) =
              (max (|J.lo|) (|J.hi|) : ℚ) := by simp [Rat.cast_max, Rat.cast_abs]
          set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
          have hr_safe_eq : min radius (99/100) = radius := min_eq_left hJ_radius
          have hradius_le : (radius : ℝ) ≤ 99/100 := by
            calc (radius : ℝ) ≤ ((99/100 : ℚ) : ℝ) := by exact_mod_cast hJ_radius
              _ = 99/100 := by norm_num
          have hradius_lt_one : (radius : ℝ) < 1 := by linarith
          have hrad_nonneg : 0 ≤ (radius : ℝ) := by
            calc (0 : ℝ) ≤ |z| := abs_nonneg z
              _ ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := hz_le_radius
              _ = (radius : ℝ) := hradius_real
          have hz_le_rad : |z| ≤ (radius : ℝ) := by rw [hradius_real] at hz_le_radius; exact hz_le_radius
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
          have hpow_le : |z| ^ (n + 1) ≤ (radius : ℝ) ^ (n + 1) :=
            pow_le_pow_left₀ (abs_nonneg z) hz_le_rad (n + 1)
          have hpow_nonneg : 0 ≤ |z| ^ (n + 1) := pow_nonneg (abs_nonneg z) _
          have hbound1 : |z| ^ (n + 1) / (1 - z ^ 2) ≤ (radius : ℝ) ^ (n + 1) / (1 - (radius : ℝ) ^ 2) := by
            gcongr
          have hdenom_eq : max (1 - radius ^ 2) (1/100 : ℚ) = 1 - radius ^ 2 := by
            apply max_eq_left
            have h1 : radius ^ 2 ≤ (99/100 : ℚ) ^ 2 := by
              have hr_nonneg : 0 ≤ radius := le_trans (abs_nonneg J.lo) (le_max_left _ _)
              nlinarith [sq_nonneg radius]
            have h2 : (99/100 : ℚ) ^ 2 = 9801/10000 := by norm_num
            have h3 : 1 - (9801/10000 : ℚ) = 199/10000 := by norm_num
            have h4 : (199/10000 : ℚ) ≥ 1/100 := by norm_num
            linarith
          have hbound_val : atanhRemainderBound J n = radius ^ (n + 1) / (1 - radius ^ 2) := by
            unfold atanhRemainderBound
            simp only [← hradius_def, hr_safe_eq, hdenom_eq]
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

/-- sinh z ∈ (tmSinh J n).evalSet z for all z in J.
    Uses taylor_remainder_bound with f = Real.sinh. -/
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
    have habs_z_le : |z| ≤ max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := abs_le_interval_radius hz
    set radius : ℚ := max (|J.lo|) (|J.hi|) with hradius_def
    have hradius_real : (radius : ℝ) = max (|(J.lo : ℝ)|) (|(J.hi : ℝ)|) := by
      simp only [hradius_def, Rat.cast_max, Rat.cast_abs]
    have hab_le_radius : max (|a|) (|b|) ≤ radius := by
      simp only [ha_def, hb_def, hradius_real]
      apply max_le
      · calc |min (J.lo : ℝ) 0| ≤ max |(J.lo : ℝ)| |(0 : ℝ)| := abs_min_le_max_abs_abs
          _ = max |(J.lo : ℝ)| 0 := by simp
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := max_le_max_left _ (abs_nonneg _)
      · calc |max (J.hi : ℝ) 0| ≤ max |(J.hi : ℝ)| |(0 : ℝ)| := abs_max_le_max_abs_abs
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

/-- cosh z ∈ (tmCosh J n).evalSet z for all z in J. -/
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
      · calc |min (J.lo : ℝ) 0| ≤ max |(J.lo : ℝ)| |(0 : ℝ)| := abs_min_le_max_abs_abs
          _ = max |(J.lo : ℝ)| 0 := by simp
          _ ≤ max |(J.lo : ℝ)| |(J.hi : ℝ)| := max_le_max_left _ (abs_nonneg _)
      · calc |max (J.hi : ℝ) 0| ≤ max |(J.hi : ℝ)| |(0 : ℝ)| := abs_max_le_max_abs_abs
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
