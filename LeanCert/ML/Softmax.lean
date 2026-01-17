/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.IntervalVector
import LeanCert.Engine.TaylorModel

/-!
# Verified Softmax and LogSumExp

This module implements tight interval bounds for Softmax using algebraic
cancellation to handle the numerator-denominator dependency.

## The Problem
Naive Interval Softmax: [e^l, e^u] / [Σe^l, Σe^u].
If width is large, the lower bound of the result approaches 0 and upper > 1.

## The Solution (Algebraic Substitution)
We compute: y_i = 1 / (1 + Σ_{j≠i} exp(x_j - x_i))

This explicitly models the dependency, ensuring the result is always in (0, 1)
and providing much tighter bounds for the dominant token.
-/

namespace LeanCert.ML.Softmax

open LeanCert.Core
open LeanCert.Engine
open LeanCert.ML.IntervalVector

/-! ### Helper: Interval Exponentiation -/

/-- Vectorized exponential using Taylor refined intervals -/
def expVector (v : IntervalVector) (prec : Int) : IntervalVector :=
  v.map (fun I =>
    let res := IntervalRat.expComputable I.toIntervalRat 10 -- Depth 10
    IntervalDyadic.ofIntervalRat res prec
  )

/-! ### Verified LogSumExp -/

/--
  LogSumExp: log(Σ e^x_i)
  Computed as: max(x) + log(Σ e^(x_i - max(x)))
  This is the "Shift-Invariance" property used for numerical stability.
  It also keeps intervals small (inputs to exp are ≤ 0).
-/
noncomputable def logSumExp (x : IntervalVector) (prec : Int) : IntervalDyadic :=
  -- 1. Find approximate max (center of intervals) to shift by
  -- We don't need the exact max for correctness, just for stability/tightness
  let shift := x.foldl (fun m I => max m I.toIntervalRat.hi) (-1000 : ℚ)
  let shiftI := IntervalDyadic.ofIntervalRat (IntervalRat.singleton shift) prec

  -- 2. Compute shifted vector: x - shift
  let shifted := x.map (fun I => IntervalDyadic.sub I shiftI)

  -- 3. Exponentiate
  let exps := expVector shifted prec

  -- 4. Sum
  let zeroInterval := IntervalDyadic.singleton (Core.Dyadic.ofInt 0)
  let sum_exp := exps.foldl (fun acc I => IntervalDyadic.add acc I) zeroInterval

  -- 5. Log
  -- Note: We need a log wrapper for Dyadic. Using Rational fallback for now.
  let sum_rat := sum_exp.toIntervalRat
  -- sum_exp is sum of exponentials, so strictly positive. Safe to log.
  let log_sum := if h : sum_rat.lo > 0 then
      IntervalRat.logInterval ⟨sum_rat, h⟩
    else
      default -- Should not happen given exp output

  -- 6. Add shift back: shift + log(sum)
  let result := IntervalRat.add (IntervalRat.singleton shift) log_sum
  IntervalDyadic.ofIntervalRat result prec

/-! ### Verified Softmax -/

/--
  Optimized Softmax for index `k` of vector `x`.
  Computes 1 / (1 + Σ_{j≠k} exp(x_j - x_k))
-/
def softmaxComponent (x : IntervalVector) (k : Nat) (prec : Int) : IntervalDyadic :=
  if hk : k < x.length then
    let x_k := x[k]

    -- 1. Compute differences x_j - x_k
    let diffs := x.map (fun x_j => IntervalDyadic.sub x_j x_k)

    -- 2. Exponentiate
    let exps := expVector diffs prec

    -- 3. Sum (this includes j=k where exp(0)=1, which is correct)
    let zeroInterval := IntervalDyadic.singleton (Core.Dyadic.ofInt 0)
    let sum_exps := exps.foldl (fun acc I => IntervalDyadic.add acc I) zeroInterval

    -- 4. Invert: 1 / sum
    let sum_rat := sum_exps.toIntervalRat
    -- Sum of exponentials is always positive
    if h_pos : sum_rat.lo > 0 then
       -- [1/hi, 1/lo]
       let inv := IntervalRat.invNonzero
          ⟨sum_rat, fun hcz => not_lt.mpr hcz.1 h_pos⟩
       IntervalDyadic.ofIntervalRat inv prec
    else
       -- Fallback: When interval arithmetic is too loose to prove sum > 0,
       -- we use the conservative bound [0, 1] since softmax ∈ (0, 1) always.
       ⟨Core.Dyadic.ofInt 0, Core.Dyadic.ofInt 1, by simp [Core.Dyadic.toRat_ofInt]⟩
  else
    default

/-- Full Softmax layer -/
def softmax (x : IntervalVector) (prec : Int) : IntervalVector :=
  List.range x.length |>.map (fun k => softmaxComponent x k prec)

/-! ### Soundness Proofs -/

/-- Helper: foldl add preserves interval membership.
    If acc_real ∈ acc_interval and for each i, xs_real[i] ∈ xs_interval[i],
    then (xs_real.foldl (+) acc_real) ∈ (xs_interval.foldl add acc_interval).

    Proof by induction on xs_real, using mem_add at each step. -/
theorem mem_foldl_add {xs_real : List ℝ} {xs_interval : List IntervalDyadic}
    {acc_real : ℝ} {acc_interval : IntervalDyadic}
    (_hlen : xs_real.length = xs_interval.length)
    (hacc : acc_real ∈ acc_interval)
    (_hmem : ∀ i (hi : i < xs_real.length),
      xs_real[i] ∈ xs_interval[i]'(_hlen ▸ hi)) :
    xs_real.foldl (· + ·) acc_real ∈
    xs_interval.foldl IntervalDyadic.add acc_interval := by
  -- Induction proof: at each step we add a real to the accumulator
  -- and an interval to the interval accumulator, using mem_add.
  induction xs_real generalizing xs_interval acc_real acc_interval with
  | nil =>
    cases xs_interval with
    | nil => simp only [List.foldl_nil]; exact hacc
    | cons _ _ => simp at _hlen
  | cons x xs ih =>
    cases xs_interval with
    | nil => simp at _hlen
    | cons I Is =>
      simp only [List.foldl_cons]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at _hlen
      -- The new accumulator: acc + x ∈ acc_interval.add I
      have hacc' : acc_real + x ∈ IntervalDyadic.add acc_interval I :=
        IntervalDyadic.mem_add hacc (_hmem 0 (by simp))
      -- Membership for the tail
      have hmem' : ∀ i (hi : i < xs.length), xs[i] ∈ Is[i]'(_hlen ▸ hi) := fun i hi =>
        _hmem (i + 1) (by simp; omega)
      exact ih _hlen hacc' hmem'

/-- Real Softmax function -/
noncomputable def Real.softmax (x : List ℝ) (k : Nat) : ℝ :=
  Real.exp x[k]! / (x.map Real.exp).sum

/-- Algebraic Identity: e^xk / Σ e^xj = 1 / Σ e^(xj - xk)

This is the key insight that allows tight interval bounds:
by dividing both numerator and denominator by e^xk, we cancel the
correlation and get an expression where all terms are differences.

Proof sketch:
  e^xk / Σe^xj = (e^xk * e^{-xk}) / (Σe^xj * e^{-xk})
              = 1 / Σ(e^xj * e^{-xk})
              = 1 / Σe^{xj - xk}
-/
theorem softmax_algebraic_identity (x : List ℝ) (k : Nat) (hk : k < x.length)
    (hsum : (x.map Real.exp).sum ≠ 0) :
    Real.softmax x k = 1 / ((x.map (fun xj => Real.exp (xj - x[k]!))).sum) := by
  unfold Real.softmax
  -- Key facts about exp
  have hexp_pos : Real.exp (x[k]!) > 0 := Real.exp_pos _
  have hexp_ne : Real.exp (x[k]!) ≠ 0 := ne_of_gt hexp_pos
  -- Sum of shifted exponentials is positive
  have hsum_shift_pos : (x.map (fun xj => Real.exp (xj - x[k]!))).sum > 0 := by
    apply List.sum_pos
    · intro y hy
      obtain ⟨xj, _, rfl⟩ := List.mem_map.mp hy
      exact Real.exp_pos _
    · intro hempty
      have hnil := List.map_eq_nil_iff.mp hempty
      simp [List.length_eq_zero_iff.mpr hnil] at hk
  have hsum_shift_ne : (x.map (fun xj => Real.exp (xj - x[k]!))).sum ≠ 0 :=
    ne_of_gt hsum_shift_pos
  -- Main calculation: exp(xk) / Σexp(xj) = 1 / Σexp(xj - xk)
  -- Key: Σexp(xj) / exp(xk) = Σ(exp(xj) / exp(xk)) = Σexp(xj - xk)
  have key : (x.map Real.exp).sum / Real.exp (x[k]!) =
             (x.map (fun xj => Real.exp (xj - x[k]!))).sum := by
    rw [div_eq_iff hexp_ne]
    rw [← List.sum_map_mul_right]
    congr 1
    simp_rw [Real.exp_sub, div_mul_cancel₀ _ hexp_ne]
  calc Real.exp x[k]! / (x.map Real.exp).sum
      = 1 / ((x.map Real.exp).sum / Real.exp x[k]!) := by field_simp
    _ = 1 / (x.map (fun xj => Real.exp (xj - x[k]!))).sum := by rw [key]

/--
  **Main Theorem: Softmax Soundness**

  If inputs `v` are within `I`, then `softmax(v)` is within `softmax(I)`.
-/
theorem mem_softmax {v : List ℝ} {I : IntervalVector}
    (hdim : v.length = I.length)
    (hmem : ∀ i (hi : i < I.length), v[i]'(hdim ▸ hi) ∈ I[i]'hi)
    (prec : Int) (_hprec : prec ≤ 0) :
    ∀ k (hk : k < I.length),
      Real.softmax v k ∈ (softmax I prec)[k]'(by simp [softmax]; exact hk) := by
  intro k hk
  simp only [softmax, List.getElem_map, List.getElem_range]

  -- 1. Apply Algebraic Identity to Real.softmax
  have hsum : (v.map Real.exp).sum ≠ 0 := by
    apply ne_of_gt
    apply List.sum_pos
    · intro y hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
      exact Real.exp_pos _
    · intro h
      have hnil := List.map_eq_nil_iff.mp h
      have hlen : v.length = 0 := List.length_eq_zero_iff.mpr hnil
      rw [hlen] at hdim
      exact Nat.not_lt_zero k (hdim ▸ hk)
  rw [softmax_algebraic_identity v k (hdim ▸ hk) hsum]

  -- 2. We now need to prove membership for 1 / Σ exp(v_j - v_k)
  -- versus the computed softmaxComponent I k prec
  unfold softmaxComponent
  simp only [hk, ↓reduceDIte]

  -- Set up the interval computations
  let I_k := I[k]'hk
  let diffs := I.map (fun I_j => IntervalDyadic.sub I_j I_k)
  let exps := expVector diffs prec
  let zeroInterval := IntervalDyadic.singleton (Core.Dyadic.ofInt 0)
  let sum_exps := exps.foldl (fun acc I => IntervalDyadic.add acc I) zeroInterval

  -- A. v_j - v_k ∈ I_j - I_k (subtraction soundness)
  have h_diff : ∀ j (hj : j < I.length),
      v[j]'(hdim ▸ hj) - v[k]'(hdim ▸ hk) ∈ diffs[j]'(by simp [diffs]; exact hj) := by
    intro j hj
    simp only [diffs, List.getElem_map]
    exact IntervalDyadic.mem_sub (hmem j hj) (hmem k hk)

  -- B. exp(v_j - v_k) ∈ exps[j] (exp soundness)
  have h_exp : ∀ j (hj : j < I.length),
      Real.exp (v[j]'(hdim ▸ hj) - v[k]'(hdim ▸ hk)) ∈
        exps[j]'(by simp only [exps, expVector, diffs, List.length_map]; exact hj) := by
    intro j hj
    simp only [exps, expVector, diffs, List.getElem_map]
    -- Get difference membership directly
    have hdiff_mem : v[j]'(hdim ▸ hj) - v[k]'(hdim ▸ hk) ∈ IntervalDyadic.sub (I[j]'hj) I_k :=
      IntervalDyadic.mem_sub (hmem j hj) (hmem k hk)
    -- Convert to IntervalRat for expComputable
    have hdiff_rat : v[j]'(hdim ▸ hj) - v[k]'(hdim ▸ hk) ∈ (IntervalDyadic.sub (I[j]'hj) I_k).toIntervalRat :=
      IntervalDyadic.mem_toIntervalRat.mpr hdiff_mem
    have hexp_rat := IntervalRat.mem_expComputable hdiff_rat 10
    exact IntervalDyadic.mem_ofIntervalRat hexp_rat prec _hprec

  -- C. Σ exp(v_j - v_k) ∈ sum_exps (sum soundness via foldl)
  have h_sum : (v.map (fun xj => Real.exp (xj - v[k]!))).sum ∈ sum_exps := by
    -- v[k]! = v[k] when k < v.length
    have hk_bound : k < v.length := hdim ▸ hk
    have hgetelem_eq : v[k]! = v[k]'hk_bound := getElem!_pos v k hk_bound
    -- Rewrite the sum to use v[k] instead of v[k]!
    simp only [hgetelem_eq]
    -- Now prove: (v.map (fun xj => Real.exp (xj - v[k]))).sum ∈ sum_exps
    -- The real sum equals foldl (+) 0 over the mapped list
    have hlen_eq : (v.map (fun xj => Real.exp (xj - v[k]))).length = exps.length := by
      simp [exps, expVector, diffs, hdim]
    -- 0 ∈ zeroInterval
    have h_zero : (0 : ℝ) ∈ zeroInterval := by
      simp only [zeroInterval, IntervalDyadic.mem_def, Core.Dyadic.toRat_ofInt,
                 IntervalDyadic.singleton]
      constructor <;> norm_num
    -- Apply the foldl lemma
    -- List.sum is foldl (+) 0
    rw [List.sum_eq_foldl]
    apply mem_foldl_add hlen_eq h_zero
    intro i hi
    -- Need: exp(v[i] - v[k]) ∈ exps[i]
    have hi' : i < I.length := by
      simp only [List.length_map] at hi
      omega
    simp only [List.getElem_map]
    exact h_exp i hi'

  -- D. Handle the positivity check for inversion
  -- The sum of exponentials is always positive
  have h_sum_pos : (v.map (fun xj => Real.exp (xj - v[k]!))).sum > 0 := by
    apply List.sum_pos
    · intro y hy
      obtain ⟨xj, _, rfl⟩ := List.mem_map.mp hy
      exact Real.exp_pos _
    · intro hempty
      have hnil := List.map_eq_nil_iff.mp hempty
      simp [List.length_eq_zero_iff.mpr hnil] at hdim
      exact Nat.not_lt_zero k (hdim ▸ hk)

  -- The sum_rat.lo > 0 condition should hold (intervals contain positive sums)
  -- For now, we handle both cases using split on the dite
  split
  · -- Case: sum_rat.lo > 0 (normal case)
    rename_i h_pos
    -- 1 / sum_real ∈ inv(sum_interval)
    have h_sum_rat : (v.map (fun xj => Real.exp (xj - v[k]!))).sum ∈ sum_exps.toIntervalRat :=
      IntervalDyadic.mem_toIntervalRat.mpr h_sum
    have h_sum_ne : (v.map (fun xj => Real.exp (xj - v[k]!))).sum ≠ 0 := ne_of_gt h_sum_pos
    -- Construct the nonzero interval
    let sum_nz : IntervalRat.IntervalRatNonzero :=
      ⟨sum_exps.toIntervalRat, fun hcz => not_lt.mpr hcz.1 h_pos⟩
    have h_inv := IntervalRat.mem_invNonzero (I := sum_nz) h_sum_rat h_sum_ne
    -- Convert 1/x = x⁻¹
    rw [one_div]
    exact IntervalDyadic.mem_ofIntervalRat h_inv prec _hprec
  · -- Case: sum_rat.lo ≤ 0 (fallback to conservative [0, 1] bound)
    -- We need to show: 1 / sum ∈ [0, 1]
    -- Since sum = Σ exp(v_j - v_k) includes exp(0) = 1 and all terms are positive,
    -- we have sum ≥ 1, so 0 < 1/sum ≤ 1.
    simp only [IntervalDyadic.mem_def, Dyadic.toRat_ofInt]
    constructor
    · -- 0 ≤ 1/sum (since sum > 0)
      norm_cast
      exact le_of_lt (one_div_pos.mpr h_sum_pos)
    · -- 1/sum ≤ 1 (since sum ≥ 1)
      norm_cast
      rw [div_le_one h_sum_pos]
      -- sum = Σ exp(v_j - v_k) ≥ exp(0) = 1 (the j=k term)
      -- The sum includes exp(v_k - v_k) = exp(0) = 1
      have hk_bound : k < v.length := hdim ▸ hk
      have hgetelem_eq : v[k]! = v[k]'hk_bound := getElem!_pos v k hk_bound
      -- The k-th term is exp(v[k] - v[k]) = exp(0) = 1
      have h_one_in_sum : Real.exp (v[k]'hk_bound - v[k]'hk_bound) ≤
          (v.map (fun xj => Real.exp (xj - v[k]!))).sum := by
        simp only [sub_self, Real.exp_zero, hgetelem_eq]
        apply List.single_le_sum
        · intro y hy
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
          exact le_of_lt (Real.exp_pos _)
        · apply List.mem_map.mpr
          exact ⟨v[k]'hk_bound, List.getElem_mem hk_bound, by simp⟩
      simp only [sub_self, Real.exp_zero] at h_one_in_sum
      exact h_one_in_sum

end LeanCert.ML.Softmax
