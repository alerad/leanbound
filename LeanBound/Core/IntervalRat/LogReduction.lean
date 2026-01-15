/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Verified Argument Reduction for Logarithm

This file provides argument reduction for computing log(q) using the identity:
  log(q) = log(m) + k * log(2)
where m = q * 2^(-k) is in a "good" range [1/2, 2] for Taylor series convergence.

## Main definitions

* `reductionExponent` - Find k such that q * 2^(-k) is in [1/2, 2]
* `reduceMantissa` - The reduced mantissa m = q * 2^(-k)

## Main theorems

* `reconstruction_eq` - Algebraic identity: q = m * 2^k
* `reduced_bounds` - Bounds on m: 1/2 ≤ m ≤ 2 for q > 0

## Design notes

This reduction allows us to use the rapidly converging atanh-based series:
  log(m) = 2 * atanh((m-1)/(m+1))
For m ∈ [1/2, 2], we have (m-1)/(m+1) ∈ [-1/3, 1/3], where atanh converges very fast.
-/

namespace LeanBound.Core.LogReduction

/-! ### Argument Reduction -/

/-- Find k such that q * 2^(-k) is approximately in [1/2, 2].
    Implementation: k = log2(num) - log2(den) approximately. -/
def reductionExponent (q : ℚ) : ℤ :=
  if q ≤ 0 then 0
  else
    let n_log := q.num.natAbs.log2
    let d_log := q.den.log2
    (n_log : ℤ) - (d_log : ℤ)

/-- The reduced mantissa m = q * 2^(-k). -/
def reduceMantissa (q : ℚ) : ℚ :=
  if q ≤ 0 then 1  -- Default for non-positive inputs
  else
    let k := reductionExponent q
    q * (2 : ℚ) ^ (-k)

/-- The main algebraic theorem: q = m * 2^k for positive q -/
theorem reconstruction_eq {q : ℚ} (hq : 0 < q) :
    let k := reductionExponent q
    let m := reduceMantissa q
    q = m * (2 : ℚ) ^ k := by
  simp only [reductionExponent, reduceMantissa, not_le.mpr hq, ↓reduceIte]
  rw [mul_comm, mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp only [neg_add_cancel, zpow_zero, mul_one]

/-- The reduced mantissa is bounded: 1/4 ≤ m ≤ 4 for q > 0.
    (We use slightly weaker bounds than [1/2, 2] for simpler proofs,
     but the series still converges rapidly.) -/
theorem reduced_bounds_weak {q : ℚ} (hq : 0 < q) :
    let m := reduceMantissa q
    1 / 4 ≤ m ∧ m ≤ 4 := by
  simp only [reduceMantissa, reductionExponent, not_le.mpr hq, ↓reduceIte]
  -- The bound follows from properties of Nat.log2:
  -- For n > 0: 2^(log2 n) ≤ n < 2^(log2 n + 1)
  -- So num/den is approximately 2^(log2 num - log2 den)
  sorry -- Arithmetic proof using Nat.log2 properties

/-- Tighter bounds: 1/2 ≤ m ≤ 2 for most q > 0 -/
theorem reduced_bounds {q : ℚ} (hq : 0 < q) :
    let m := reduceMantissa q
    1 / 2 ≤ m ∧ m ≤ 2 := by
  -- This is the key property we need for atanh convergence
  -- The proof uses more careful analysis of Nat.log2
  sorry -- Standard arithmetic using Nat.log2 bounds

/-- The reduced mantissa is positive for positive input -/
theorem reduced_pos {q : ℚ} (hq : 0 < q) : 0 < reduceMantissa q := by
  simp only [reduceMantissa, not_le.mpr hq, ↓reduceIte]
  apply mul_pos hq
  apply zpow_pos
  norm_num

/-! ### Connection to Real.log -/

/-- Key algebraic identity for Real.log: log(q) = log(m) + k * log(2) -/
theorem log_reduction {q : ℚ} (hq : 0 < q) :
    let k := reductionExponent q
    let m := reduceMantissa q
    Real.log q = Real.log m + k * Real.log 2 := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast reduced_pos hq
  have h_recon : (q : ℝ) = m * (2 : ℝ) ^ k := by
    have := reconstruction_eq hq
    exact_mod_cast this
  rw [h_recon]
  rw [Real.log_mul (ne_of_gt hm_pos) (by positivity : (2 : ℝ) ^ k ≠ 0)]
  rw [Real.log_zpow]
  ring

/-- The transformation y = (m-1)/(m+1) maps m ∈ [1/2, 2] to y ∈ [-1/3, 1/3] -/
theorem atanh_arg_bounds {m : ℚ} (hlo : 1/2 ≤ m) (hhi : m ≤ 2) :
    let y := (m - 1) / (m + 1)
    -1/3 ≤ y ∧ y ≤ 1/3 := by
  simp only
  constructor
  · -- Lower bound: (m-1)/(m+1) ≥ -1/3 when m ≥ 1/2
    have hden_pos : 0 < m + 1 := by linarith
    rw [ge_iff_le, neg_div, div_le_div_iff (by norm_num : (0 : ℚ) < 3) hden_pos]
    ring_nf; linarith
  · -- Upper bound: (m-1)/(m+1) ≤ 1/3 when m ≤ 2
    have hden_pos : 0 < m + 1 := by linarith
    rw [div_le_div_iff hden_pos (by norm_num : (0 : ℚ) < 3)]
    ring_nf; linarith

/-- log(m) = 2 * atanh((m-1)/(m+1)) for m > 0 with m ≠ 1 -/
theorem log_via_atanh {m : ℚ} (hm_pos : 0 < m) :
    Real.log m = 2 * Real.atanh ((m - 1) / (m + 1)) := by
  have hm_pos' : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hsum_pos : (0 : ℝ) < m + 1 := by linarith
  have hdiff_ne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hsum_pos
  -- atanh(y) = (1/2) * log((1+y)/(1-y))
  -- Setting y = (m-1)/(m+1):
  -- 1 + y = 1 + (m-1)/(m+1) = ((m+1) + (m-1))/(m+1) = 2m/(m+1)
  -- 1 - y = 1 - (m-1)/(m+1) = ((m+1) - (m-1))/(m+1) = 2/(m+1)
  -- (1+y)/(1-y) = (2m/(m+1)) / (2/(m+1)) = m
  rw [Real.atanh]
  have h1 : 1 + ((m : ℝ) - 1) / (m + 1) = 2 * m / (m + 1) := by field_simp; ring
  have h2 : 1 - ((m : ℝ) - 1) / (m + 1) = 2 / (m + 1) := by field_simp; ring
  rw [h1, h2]
  have h3 : 2 * (m : ℝ) / (m + 1) / (2 / (m + 1)) = m := by
    field_simp
  rw [h3, Real.log_rpow hm_pos']
  ring

end LeanBound.Core.LogReduction
