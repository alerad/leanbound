/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Verified Numerical Integration

This file implements numerical integration with rigorous error bounds.
Given an expression and an interval, we compute an interval guaranteed
to contain the definite integral.

## Main definitions

* `integrateInterval` - Compute bounds on ∫_a^b f(x) dx
* `integrateInterval_correct_n1` - Correctness theorem for n=1 (FULLY PROVED)

## Algorithm

We use uniform partitioning with interval evaluation:
1. Partition [a, b] into n subintervals
2. On each subinterval, bound f using interval arithmetic
3. Sum the bounds: ∫ ≤ Σ (width * upper_bound)

## Verification status

The `integrateInterval_correct_n1` theorem is fully proved for `ExprSupported` expressions.
This demonstrates the end-to-end verification pipeline.
-/

namespace LeanCert.Engine

open LeanCert.Core
open MeasureTheory
open scoped ENNReal

/-! ### Auxiliary lemmas for integration bounds -/

/-- If lo ≤ f(x) ≤ hi for all x ∈ [a, b], then lo * (b - a) ≤ ∫_a^b f ≤ hi * (b - a).
    This is the fundamental lemma for bounding integrals. -/
theorem integral_bounds_of_bounds {a b lo hi : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hlo : ∀ x ∈ Set.Icc a b, lo ≤ f x)
    (hhi : ∀ x ∈ Set.Icc a b, f x ≤ hi) :
    lo * (b - a) ≤ ∫ x in a..b, f x ∧ ∫ x in a..b, f x ≤ hi * (b - a) := by
  constructor
  · -- Lower bound: lo * (b - a) ≤ ∫ f
    have h1 : ∫ _ in a..b, lo = (b - a) * lo := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    calc lo * (b - a) = (b - a) * lo := by ring
         _ = ∫ _ in a..b, lo := h1.symm
         _ ≤ ∫ x in a..b, f x := by
           apply intervalIntegral.integral_mono_on hab
             (intervalIntegrable_const) hf
           intro x hx
           exact hlo x hx
  · -- Upper bound: ∫ f ≤ hi * (b - a)
    have h2 : ∫ _ in a..b, hi = (b - a) * hi := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    calc ∫ x in a..b, f x ≤ ∫ _ in a..b, hi := by
           apply intervalIntegral.integral_mono_on hab hf
             (intervalIntegrable_const)
           intro x hx
           exact hhi x hx
         _ = (b - a) * hi := h2
         _ = hi * (b - a) := by ring

/-! ### Uniform partition integration -/

/-- Partition an interval into n equal parts -/
def uniformPartition (I : IntervalRat) (n : ℕ) (hn : 0 < n) : List IntervalRat :=
  let width := (I.hi - I.lo) / n
  List.ofFn fun i : Fin n =>
    { lo := I.lo + width * i
      hi := I.lo + width * (i + 1)
      le := by
        simp only [add_le_add_iff_left]
        apply mul_le_mul_of_nonneg_left
        · have : (i : ℚ) ≤ (i : ℚ) + 1 := le_add_of_nonneg_right (by norm_num)
          exact this
        · apply div_nonneg
          · linarith [I.le]
          · have : (0 : ℚ) < n := by exact_mod_cast hn
            linarith }

/-- Sum of interval bounds over a partition -/
noncomputable def sumIntervalBounds (e : Expr) (parts : List IntervalRat) : IntervalRat :=
  parts.foldl
    (fun acc I =>
      let fBound := evalInterval1 e I
      let contribution := IntervalRat.mul
        (IntervalRat.singleton I.width)
        fBound
      IntervalRat.add acc contribution)
    (IntervalRat.singleton 0)

/-- Compute interval bounds on ∫_a^b f(x) dx using uniform partitioning -/
noncomputable def integrateInterval (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n) : IntervalRat :=
  sumIntervalBounds e (uniformPartition I n hn)

/-! ### Integration correctness for n = 1 -/

/-- For single-interval integration (n=1), we can compute the result directly. -/
noncomputable def integrateInterval1 (e : Expr) (I : IntervalRat) : IntervalRat :=
  let fBound := evalInterval1 e I
  IntervalRat.mul (IntervalRat.singleton I.width) fBound

/-- The single-interval integration is contained in the general integration for n=1 -/
theorem integrateInterval1_eq (e : Expr) (I : IntervalRat) :
    integrateInterval e I 1 (by norm_num) = IntervalRat.add (IntervalRat.singleton 0) (integrateInterval1 e I) := by
  unfold integrateInterval uniformPartition sumIntervalBounds integrateInterval1
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, CharP.cast_eq_zero,
             mul_zero, add_zero, Nat.cast_one, div_one, List.foldl_cons,
             List.foldl_nil]
  congr 1
  -- The singleton width is the same
  congr 1
  · simp only [IntervalRat.width]; ring_nf
  · -- evalInterval1 is the same since the interval is the same
    unfold evalInterval1
    congr 1
    funext _
    ring_nf

/-- The single-interval correctness theorem.
    This is FULLY PROVED - no sorry, no axioms. -/
theorem integrateInterval1_correct (e : Expr) (hsupp : ExprSupported e) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1 e I := by
  unfold integrateInterval1
  -- Get bounds from interval evaluation
  set fBound := evalInterval1 e I with hfBound_def
  have hbounds : ∀ x : ℝ, x ∈ I → Expr.eval (fun _ => x) e ∈ fBound := fun x hx =>
    evalInterval1_correct e hsupp x I hx
  have hlo : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), (fBound.lo : ℝ) ≤ Expr.eval (fun _ => x) e := by
    intro x hx; exact (hbounds x hx).1
  have hhi : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (fBound.hi : ℝ) := by
    intro x hx; exact (hbounds x hx).2
  have hIle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have ⟨h_lower, h_upper⟩ := integral_bounds_of_bounds hIle hInt hlo hhi
  -- Show membership in the product interval
  have hwidth : (I.width : ℝ) = (I.hi : ℝ) - (I.lo : ℝ) := by
    simp only [IntervalRat.width, Rat.cast_sub]
  have hwidth_nn : (0 : ℝ) ≤ I.width := by exact_mod_cast IntervalRat.width_nonneg I
  have hfBound_le : (fBound.lo : ℝ) ≤ fBound.hi := by exact_mod_cast fBound.le
  -- The product interval singleton(width) * fBound = [width * fBound.lo, width * fBound.hi]
  -- since width ≥ 0
  -- First, convert integral bounds to width-first form
  have h_lo' : (I.width : ℝ) * fBound.lo ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := by
    calc (I.width : ℝ) * fBound.lo = fBound.lo * I.width := by ring
       _ = fBound.lo * ((I.hi : ℝ) - I.lo) := by rw [hwidth]
       _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lower
  have h_hi' : ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e ≤ (I.width : ℝ) * fBound.hi := by
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
       ≤ fBound.hi * ((I.hi : ℝ) - I.lo) := h_upper
     _ = fBound.hi * I.width := by rw [hwidth]
     _ = (I.width : ℝ) * fBound.hi := by ring
  -- Show membership in IntervalRat.mul (singleton width) fBound
  -- Use mem_mul directly: if w ∈ singleton(width) and v ∈ fBound, then w*v ∈ mul
  -- We have: integral ∈ [width * fBound.lo, width * fBound.hi]
  -- We need: integral ∈ mul (singleton width) fBound
  -- The key insight: width ∈ singleton(width) and the integral/width ∈ fBound isn't quite right
  -- Instead, we prove membership directly using the structure of mul for singletons
  have h1 : (I.width : ℝ) * fBound.lo ≤ I.width * fBound.hi :=
    mul_le_mul_of_nonneg_left hfBound_le hwidth_nn
  -- The result interval is mul (singleton width) fBound
  -- For a singleton [w,w] times [lo,hi], the corners are all w*lo or w*hi
  -- So the result is [min(w*lo, w*hi), max(w*lo, w*hi)] = [w*lo, w*hi] when w ≥ 0
  have hwidth_mem : (I.width : ℝ) ∈ IntervalRat.singleton I.width :=
    IntervalRat.mem_singleton I.width
  -- We construct a value in fBound such that width * that_value = integral
  -- But this is backwards. Instead, we show the integral is in the interval directly.
  rw [IntervalRat.mem_def]
  -- Need to show: (mul (singleton width) fBound).lo ≤ integral ≤ (mul ...).hi
  -- The mul computes min/max of corners. For singleton * interval:
  -- corners are: w*lo, w*hi, w*lo, w*hi (since singleton has lo=hi=w)
  -- So min = min(w*lo, w*hi), max = max(w*lo, w*hi)
  -- When w ≥ 0: min = w*lo, max = w*hi
  constructor
  · -- Lower bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).lo =
        min (min (I.width * fBound.lo) (I.width * fBound.hi))
            (min (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, min_self, Rat.cast_min, Rat.cast_mul]
    calc (↑I.width * ↑fBound.lo) ⊓ (↑I.width * ↑fBound.hi)
        = ↑I.width * ↑fBound.lo := min_eq_left h1
      _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lo'
  · -- Upper bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).hi =
        max (max (I.width * fBound.lo) (I.width * fBound.hi))
            (max (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, max_self, Rat.cast_max, Rat.cast_mul]
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
        ≤ ↑I.width * ↑fBound.hi := h_hi'
      _ = (↑I.width * ↑fBound.lo) ⊔ (↑I.width * ↑fBound.hi) := (max_eq_right h1).symm

/-- Adding zero on the left preserves interval membership -/
theorem add_zero_left_mem {r : ℝ} {I : IntervalRat} (hr : r ∈ I) :
    r ∈ IntervalRat.add (IntervalRat.singleton 0) I := by
  simp only [IntervalRat.mem_def, IntervalRat.add, IntervalRat.singleton] at hr ⊢
  simp only [zero_add]
  exact hr

/-- Correctness for n = 1 (single interval, no partition).
    This is FULLY PROVED - no sorry, no axioms. -/
theorem integrateInterval_correct_n1 (e : Expr) (hsupp : ExprSupported e) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
    integrateInterval e I 1 (by norm_num) := by
  rw [integrateInterval1_eq]
  exact add_zero_left_mem (integrateInterval1_correct e hsupp I hInt)

/-! ### Integration correctness for general n -/

/-- The real sequence of partition points for uniform partition.
    x_i = I.lo + (I.hi - I.lo) * i / n -/
noncomputable def partitionPoints (I : IntervalRat) (n : ℕ) (i : ℕ) : ℝ :=
  I.lo + (I.hi - I.lo) * i / n

/-- x_0 = I.lo -/
theorem partitionPoints_zero (I : IntervalRat) (n : ℕ) (_hn : 0 < n) :
    partitionPoints I n 0 = I.lo := by
  simp only [partitionPoints, Nat.cast_zero, mul_zero, zero_div, add_zero]

/-- x_n = I.hi -/
theorem partitionPoints_n (I : IntervalRat) (n : ℕ) (hn : 0 < n) :
    partitionPoints I n n = I.hi := by
  simp only [partitionPoints]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  field_simp
  grind only

/-- The partition points are monotone -/
theorem partitionPoints_mono (I : IntervalRat) (n : ℕ) (_hn : 0 < n) (i j : ℕ)
    (hij : i ≤ j) (_hjn : j ≤ n) :
    partitionPoints I n i ≤ partitionPoints I n j := by
  simp only [partitionPoints]
  gcongr
  have : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  linarith

/-- The i-th subinterval of the uniform partition -/
def partitionInterval (I : IntervalRat) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) : IntervalRat :=
  (uniformPartition I n hn).get ⟨k, by simp [uniformPartition]; exact hk⟩

/-- The lo of the k-th partition interval -/
theorem partitionInterval_lo (I : IntervalRat) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    (partitionInterval I n hn k hk).lo = I.lo + (I.hi - I.lo) / n * k := by
  simp only [partitionInterval, uniformPartition, List.get_ofFn]
  grind only [= Fin.val_cast]

/-- The hi of the k-th partition interval -/
theorem partitionInterval_hi (I : IntervalRat) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    (partitionInterval I n hn k hk).hi = I.lo + (I.hi - I.lo) / n * (k + 1) := by
  simp only [partitionInterval, uniformPartition, List.get_ofFn]
  simp only [Fin.val_cast]

/-- Partition points match partition interval bounds (real version) -/
theorem partitionPoints_eq_lo (I : IntervalRat) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    partitionPoints I n k = ((partitionInterval I n hn k hk).lo : ℝ) := by
  simp only [partitionPoints, partitionInterval_lo, Rat.cast_add, Rat.cast_mul,
             Rat.cast_div, Rat.cast_natCast, Rat.cast_sub]
  ring

theorem partitionPoints_eq_hi (I : IntervalRat) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    partitionPoints I n (k + 1) = ((partitionInterval I n hn k hk).hi : ℝ) := by
  simp only [partitionPoints, partitionInterval_hi, Rat.cast_add, Rat.cast_mul,
             Rat.cast_div, Rat.cast_natCast, Rat.cast_sub, Nat.cast_add, Nat.cast_one]
  ring

/-- Integrability on a subinterval -/
theorem intervalIntegrable_on_partition (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi)
    (k : ℕ) (hk : k < n) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      ((partitionInterval I n hn k hk).lo : ℝ) ((partitionInterval I n hn k hk).hi : ℝ) := by
  apply hInt.mono_set
  simp only [Set.uIcc_of_le (by exact_mod_cast (partitionInterval I n hn k hk).le :
    ((partitionInterval I n hn k hk).lo : ℝ) ≤ (partitionInterval I n hn k hk).hi)]
  simp only [Set.uIcc_of_le (by exact_mod_cast I.le : (I.lo : ℝ) ≤ I.hi)]
  intro x ⟨hxlo, hxhi⟩
  constructor
  · calc (I.lo : ℝ) ≤ ((partitionInterval I n hn k hk).lo : ℝ) := by
           rw [partitionInterval_lo]
           simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_sub]
           apply le_add_of_nonneg_right
           apply mul_nonneg
           · apply div_nonneg
             · have := I.le
               have h : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast this
               linarith
             · exact Nat.cast_nonneg n
           · exact Nat.cast_nonneg k
       _ ≤ x := hxlo
  · calc x ≤ ((partitionInterval I n hn k hk).hi : ℝ) := hxhi
       _ ≤ I.hi := by
           rw [partitionInterval_hi]
           simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_sub]
           have hi_bound : (k : ℚ) + 1 ≤ n := by
             have : k + 1 ≤ n := hk
             exact_mod_cast this
           have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn
           have hwidth_nn : (0 : ℝ) ≤ ((I.hi : ℝ) - I.lo) / n := by
             apply div_nonneg
             · have := I.le
               have h : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast this
               linarith
             · exact Nat.cast_nonneg n
           have hkp1_le : (k : ℝ) + 1 ≤ n := by exact_mod_cast hi_bound
           calc (I.lo : ℝ) + ((I.hi : ℝ) - I.lo) / n * ((k : ℕ) + (1 : ℕ))
               ≤ I.lo + (I.hi - I.lo) / n * n := by
                   gcongr
                   grind only
             _ = I.lo + (I.hi - I.lo) := by
                   have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
                   field_simp
             _ = I.hi := by ring

/-- Integrability using partition points -/
theorem intervalIntegrable_partitionPoints (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi)
    (k : ℕ) (hk : k < n) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      (partitionPoints I n k) (partitionPoints I n (k + 1)) := by
  rw [partitionPoints_eq_lo I n hn k hk, partitionPoints_eq_hi I n hn k hk]
  exact intervalIntegrable_on_partition e I n hn hInt k hk

/-- The integral decomposes over the partition -/
theorem integral_partition_sum (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e =
    ∑ k ∈ Finset.range n, ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
        Expr.eval (fun _ => x) e := by
  have h0 := partitionPoints_zero I n hn
  have hn_eq := partitionPoints_n I n hn
  conv_lhs => rw [← h0, ← hn_eq]
  symm
  apply intervalIntegral.sum_integral_adjacent_intervals
  intro k hk
  exact intervalIntegrable_partitionPoints e I n hn hInt k hk

/-! ### Summing interval bounds over partitions -/

/-- Each subinterval integral is bounded by integrateInterval1 on that subinterval -/
theorem integral_subinterval_bounded (e : Expr) (hsupp : ExprSupported e) (I : IntervalRat)
    (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
      Expr.eval (fun _ => x) e ∈ integrateInterval1 e (partitionInterval I n hn k hk) := by
  rw [partitionPoints_eq_lo I n hn k hk, partitionPoints_eq_hi I n hn k hk]
  exact integrateInterval1_correct e hsupp (partitionInterval I n hn k hk)
    (intervalIntegrable_on_partition e I n hn hInt k hk)

/-- IntervalRat.add is associative -/
theorem IntervalRat_add_assoc (I J K : IntervalRat) :
    IntervalRat.add (IntervalRat.add I J) K = IntervalRat.add I (IntervalRat.add J K) := by
  simp only [IntervalRat.add]
  congr 1 <;> ring

/-- Helper: foldl add distributes: foldl (acc.add I) Is = acc.add (foldl I Is) -/
theorem foldl_add_concat (acc : IntervalRat) (I : IntervalRat) (Is : List IntervalRat) :
    Is.foldl IntervalRat.add (IntervalRat.add acc I) =
    IntervalRat.add acc (Is.foldl IntervalRat.add I) := by
  induction Is generalizing acc I with
  | nil => rfl
  | cons J Js ih =>
    simp only [List.foldl_cons]
    -- LHS: Js.foldl add (add (add acc I) J)
    -- RHS: add acc (Js.foldl add (add I J))
    rw [IntervalRat_add_assoc acc I J]
    -- LHS: Js.foldl add (add acc (add I J))
    rw [ih acc (IntervalRat.add I J)]

/-- Adding singleton 0 on the left is identity -/
theorem add_singleton_zero_left (I : IntervalRat) :
    IntervalRat.add (IntervalRat.singleton 0) I = I := by
  simp only [IntervalRat.add, IntervalRat.singleton]
  congr 1 <;> simp

/-- Adding singleton 0 on the right is identity -/
theorem add_singleton_zero_right (I : IntervalRat) :
    IntervalRat.add I (IntervalRat.singleton 0) = I := by
  simp only [IntervalRat.add, IntervalRat.singleton]
  congr 1 <;> simp

/-- Helper: the sum of values in intervals is in the foldl of interval sums -/
theorem sum_mem_foldl_add {values : List ℝ} {intervals : List IntervalRat}
    (hlen : values.length = intervals.length)
    (hmem : ∀ i (hi : i < values.length), values[i] ∈ intervals[i]'(hlen ▸ hi)) :
    values.sum ∈ intervals.foldl IntervalRat.add (IntervalRat.singleton 0) := by
  induction intervals generalizing values with
  | nil =>
    simp only [List.length_nil] at hlen
    have hvals : values = [] := List.eq_nil_of_length_eq_zero hlen
    simp only [hvals, List.sum_nil, List.foldl_nil]
    simp only [IntervalRat.mem_def, IntervalRat.singleton]
    simp only [Rat.cast_zero, le_refl, and_self]
  | cons I Is ih =>
    cases values with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.foldl_cons, List.sum_cons]
      have h0 : v ∈ I := by
        have := hmem 0 (by simp)
        simp at this
        exact this
      have hrec : ∀ i (hi : i < vs.length), vs[i] ∈ Is[i]'(hlen ▸ hi) := by
        intro i hi
        have := hmem (i + 1) (by simp; omega)
        simp at this
        exact this
      have hsum := ih hlen hrec
      -- Goal: v + vs.sum ∈ foldl add (add (singleton 0) I) Is
      rw [add_singleton_zero_left I]
      -- Goal: v + vs.sum ∈ foldl add I Is
      -- We have: hsum : vs.sum ∈ foldl add (singleton 0) Is
      -- Use: foldl add I Is = add I (foldl add (singleton 0) Is)
      have heq : Is.foldl IntervalRat.add I =
          IntervalRat.add I (Is.foldl IntervalRat.add (IntervalRat.singleton 0)) := by
        conv_lhs => rw [← add_singleton_zero_right I]
        rw [foldl_add_concat I (IntervalRat.singleton 0) Is]
      rw [heq]
      -- Goal: v + vs.sum ∈ add I (foldl add (singleton 0) Is)
      exact IntervalRat.mem_add h0 hsum

/-- Helper: generalized foldl lemma relating sumIntervalBounds-style fold with add fold -/
theorem foldl_sumBound_eq_foldl_add (e : Expr) (parts : List IntervalRat) (acc : IntervalRat) :
    parts.foldl (fun a I => IntervalRat.add a (IntervalRat.mul (IntervalRat.singleton I.width) (evalInterval1 e I))) acc =
    (parts.map (integrateInterval1 e)).foldl IntervalRat.add acc := by
  induction parts generalizing acc with
  | nil => rfl
  | cons J Js ih =>
    simp only [List.foldl_cons, List.map_cons]
    unfold integrateInterval1
    exact ih _

/-- sumIntervalBounds equals foldl over mapped integrateInterval1 -/
theorem sumIntervalBounds_eq_foldl_map (e : Expr) (parts : List IntervalRat) :
    sumIntervalBounds e parts =
    (parts.map (integrateInterval1 e)).foldl IntervalRat.add (IntervalRat.singleton 0) := by
  unfold sumIntervalBounds
  exact foldl_sumBound_eq_foldl_add e parts (IntervalRat.singleton 0)

/-- Main theorem: the integral lies in integrateInterval for general n -/
theorem integrateInterval_correct (e : Expr) (hsupp : ExprSupported e) (I : IntervalRat)
    (n : ℕ) (hn : 0 < n)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
    integrateInterval e I n hn := by
  -- Decompose integral into sum over subintervals
  rw [integral_partition_sum e I n hn hInt]
  -- integrateInterval is sumIntervalBounds applied to uniformPartition
  unfold integrateInterval
  rw [sumIntervalBounds_eq_foldl_map]
  -- Express the Finset sum as a List sum
  have hsum_eq : ∑ k ∈ Finset.range n, ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
        Expr.eval (fun _ => x) e =
      (List.ofFn (fun k : Fin n => ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
        Expr.eval (fun _ => x) e)).sum := by
    simp only [Finset.sum_range, List.sum_ofFn]
  rw [hsum_eq]
  -- Create the lists
  set integrals := List.ofFn (fun k : Fin n =>
    ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
      Expr.eval (fun _ => x) e) with hintegrals_def
  set bounds := (uniformPartition I n hn).map (integrateInterval1 e) with hbounds_def
  -- Show lengths match
  have hlen : integrals.length = bounds.length := by
    simp [hintegrals_def, hbounds_def, uniformPartition]
  -- Each integral is bounded
  have hmem : ∀ i (hi : i < integrals.length), integrals[i] ∈ bounds[i]'(hlen ▸ hi) := by
    intro i hi
    simp only [hintegrals_def, List.length_ofFn] at hi
    simp only [hintegrals_def]
    rw [List.getElem_ofFn]
    simp only [hbounds_def, List.getElem_map]
    have hpart_eq : (uniformPartition I n hn)[i]'(by simp [uniformPartition]; exact hi) =
        partitionInterval I n hn i hi := by
      simp [partitionInterval, uniformPartition]
    rw [hpart_eq]
    exact integral_subinterval_bounded e hsupp I n hn i hi hInt
  -- Apply sum_mem_foldl_add
  exact sum_mem_foldl_add hlen hmem

/-! ### Adaptive integration -/

/-! #### Interval operations for error estimation -/

/-- Interval intersection (returns the tighter bound).
    If intervals don't overlap, returns the first one (conservative). -/
def intervalInter (I J : IntervalRat) : IntervalRat :=
  let lo := max I.lo J.lo
  let hi := min I.hi J.hi
  if h : lo ≤ hi then
    ⟨lo, hi, h⟩
  else
    -- If no intersection, return the narrower interval
    if I.width ≤ J.width then I else J

/-- Intersection is sound: if x ∈ I and x ∈ J, then x ∈ inter I J -/
theorem mem_intervalInter {x : ℝ} {I J : IntervalRat}
    (hI : x ∈ I) (hJ : x ∈ J) : x ∈ intervalInter I J := by
  simp only [intervalInter]
  simp only [IntervalRat.mem_def] at hI hJ ⊢
  have hlo : (I.lo : ℝ) ⊔ J.lo ≤ x := sup_le hI.1 hJ.1
  have hhi : x ≤ (I.hi : ℝ) ⊓ J.hi := le_inf hI.2 hJ.2
  by_cases h : max I.lo J.lo ≤ min I.hi J.hi
  · simp only [h, ↓reduceDIte]
    constructor
    · simp only [Rat.cast_max]
      exact hlo
    · simp only [Rat.cast_min]
      exact hhi
  · simp only [h, ↓reduceDIte]
    split_ifs with hw
    · exact hI
    · exact hJ

/-- Union of intervals (convex hull) -/
def intervalUnion (I J : IntervalRat) : IntervalRat where
  lo := min I.lo J.lo
  hi := max I.hi J.hi
  le := le_trans (min_le_left _ _) (le_trans I.le (le_max_left _ _))

/-- Union is sound: if x ∈ I then x ∈ union I J -/
theorem mem_intervalUnion_left {x : ℝ} {I J : IntervalRat} (hI : x ∈ I) :
    x ∈ intervalUnion I J := by
  simp only [intervalUnion, IntervalRat.mem_def] at hI ⊢
  simp only [Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_left _ _) hI.1
  · exact le_trans hI.2 (le_max_left _ _)

/-- Union is sound: if x ∈ J then x ∈ union I J -/
theorem mem_intervalUnion_right {x : ℝ} {I J : IntervalRat} (hJ : x ∈ J) :
    x ∈ intervalUnion I J := by
  simp only [intervalUnion, IntervalRat.mem_def] at hJ ⊢
  simp only [Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_right _ _) hJ.1
  · exact le_trans hJ.2 (le_max_right _ _)

/-! #### Splitting intervals -/

/-- Midpoint definition helper -/
theorem midpoint_def (I : IntervalRat) : I.midpoint = (I.lo + I.hi) / 2 := rfl

/-- Midpoint is at least lo -/
theorem midpoint_lo_le (I : IntervalRat) : I.lo ≤ I.midpoint := by
  rw [midpoint_def]
  have h : I.lo ≤ I.hi := I.le
  linarith

/-- Midpoint is at most hi -/
theorem midpoint_le_hi' (I : IntervalRat) : I.midpoint ≤ I.hi := by
  rw [midpoint_def]
  have h : I.lo ≤ I.hi := I.le
  linarith

/-- Split an interval at its midpoint -/
def splitMid (I : IntervalRat) : IntervalRat × IntervalRat :=
  (⟨I.lo, I.midpoint, midpoint_lo_le I⟩, ⟨I.midpoint, I.hi, midpoint_le_hi' I⟩)

/-- The left half of a split covers [lo, mid] -/
theorem splitMid_left_lo (I : IntervalRat) :
    (splitMid I).1.lo = I.lo := rfl

theorem splitMid_left_hi (I : IntervalRat) :
    (splitMid I).1.hi = I.midpoint := rfl

/-- The right half of a split covers [mid, hi] -/
theorem splitMid_right_lo (I : IntervalRat) :
    (splitMid I).2.lo = I.midpoint := rfl

theorem splitMid_right_hi (I : IntervalRat) :
    (splitMid I).2.hi = I.hi := rfl

/-- Splitting preserves coverage: any x in I is in one of the halves -/
theorem mem_splitMid {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x ∈ (splitMid I).1 ∨ x ∈ (splitMid I).2 := by
  simp only [splitMid, IntervalRat.mem_def, midpoint_def]
  simp only [IntervalRat.mem_def] at hx
  by_cases h : x ≤ (((I.lo + I.hi) / 2 : ℚ) : ℝ)
  · left
    constructor
    · exact hx.1
    · exact h
  · right
    push_neg at h
    constructor
    · exact le_of_lt h
    · exact hx.2

/-! #### Adaptive integration result and algorithm -/

/-- Adaptive integration result -/
structure AdaptiveResult where
  /-- Interval containing the integral -/
  bound : IntervalRat
  /-- Number of function evaluations used -/
  evals : ℕ

/-- Compute integration bound for a single interval using n=2 panels -/
noncomputable def integrateRefined (e : Expr) (I : IntervalRat) : IntervalRat :=
  integrateInterval e I 2 (by norm_num)

/-- Compute integration bound for a single interval using n=1 panel (coarse) -/
noncomputable def integrateCoarse (e : Expr) (I : IntervalRat) : IntervalRat :=
  integrateInterval e I 1 (by norm_num)

/-- Error estimate: width of the refined bound
    (Conservative: could use intersection, but width of refined is simpler) -/
def errorEstimate (refined : IntervalRat) : ℚ := refined.width

/-- Recursive adaptive integration.
    At each level, computes refined bound and either:
    - Returns if error ≤ tol or maxDepth = 0
    - Subdivides and recurses -/
noncomputable def integrateAdaptiveAux (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) : AdaptiveResult :=
  match maxDepth with
  | 0 =>
    -- Base case: return the best bound we can compute
    let refined := integrateRefined e I
    { bound := refined, evals := 2 }
  | n + 1 =>
    let refined := integrateRefined e I
    if errorEstimate refined ≤ tol then
      -- Error is acceptable, return
      { bound := refined, evals := 2 }
    else
      -- Subdivide and recurse
      let (I₁, I₂) := splitMid I
      let localTol := tol / 2  -- Split tolerance between halves
      let r₁ := integrateAdaptiveAux e I₁ localTol n
      let r₂ := integrateAdaptiveAux e I₂ localTol n
      { bound := IntervalRat.add r₁.bound r₂.bound
        evals := r₁.evals + r₂.evals + 2 }  -- +2 for the initial refined check

/-- Adaptive integration with error tolerance.
    Keeps subdividing until the uncertainty is below `tol`. -/
noncomputable def integrateAdaptive (e : Expr) (I : IntervalRat) (tol : ℚ) (_htol : 0 < tol)
    (maxDepth : ℕ) : AdaptiveResult :=
  integrateAdaptiveAux e I tol maxDepth

/-! #### Correctness proofs for adaptive integration -/

/-- integrateRefined is correct (direct from integrateInterval_correct) -/
theorem integrateRefined_correct (e : Expr) (hsupp : ExprSupported e) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateRefined e I :=
  integrateInterval_correct e hsupp I 2 (by norm_num) hInt

/-- integrateCoarse is correct -/
theorem integrateCoarse_correct (e : Expr) (hsupp : ExprSupported e) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateCoarse e I :=
  integrateInterval_correct e hsupp I 1 (by norm_num) hInt

/-- Helper: midpoint is between lo and hi (real version) -/
theorem midpoint_ge_lo_real (I : IntervalRat) : (I.lo : ℝ) ≤ I.midpoint := by
  have := midpoint_lo_le I
  exact_mod_cast this

theorem midpoint_le_hi_real (I : IntervalRat) : (I.midpoint : ℝ) ≤ I.hi := by
  have := midpoint_le_hi' I
  exact_mod_cast this

/-- Midpoint is in the interval -/
theorem midpoint_mem_uIcc (I : IntervalRat) :
    (I.midpoint : ℝ) ∈ Set.uIcc (I.lo : ℝ) I.hi := by
  rw [Set.mem_uIcc]
  left
  exact ⟨midpoint_ge_lo_real I, midpoint_le_hi_real I⟩

/-- Helper: integral over split interval equals sum of integrals over halves -/
theorem integral_split_mid (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e =
    (∫ x in (I.lo : ℝ)..(I.midpoint : ℝ), Expr.eval (fun _ => x) e) +
    (∫ x in (I.midpoint : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e) := by
  have hInt1 : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.midpoint :=
    hInt.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (midpoint_mem_uIcc I))
  have hInt2 : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.midpoint I.hi :=
    hInt.mono_set (Set.uIcc_subset_uIcc (midpoint_mem_uIcc I) (Set.right_mem_uIcc))
  exact (intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2).symm

/-- Integrability on left half -/
theorem intervalIntegrable_splitMid_left (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      (splitMid I).1.lo (splitMid I).1.hi := by
  simp only [splitMid_left_lo, splitMid_left_hi]
  exact hInt.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (midpoint_mem_uIcc I))

/-- Integrability on right half -/
theorem intervalIntegrable_splitMid_right (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      (splitMid I).2.lo (splitMid I).2.hi := by
  simp only [splitMid_right_lo, splitMid_right_hi]
  exact hInt.mono_set (Set.uIcc_subset_uIcc (midpoint_mem_uIcc I) (Set.right_mem_uIcc))

/-- Main soundness theorem: adaptive integration returns a bound containing the true integral.
    This is proved by induction on maxDepth. -/
theorem integrateAdaptiveAux_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
    (integrateAdaptiveAux e I tol maxDepth).bound := by
  induction maxDepth generalizing I tol with
  | zero =>
    -- Base case: returns integrateRefined, which is correct
    simp only [integrateAdaptiveAux]
    exact integrateRefined_correct e hsupp I hInt
  | succ n ih =>
    simp only [integrateAdaptiveAux]
    split_ifs with herr
    · -- Error acceptable: returns integrateRefined
      exact integrateRefined_correct e hsupp I hInt
    · -- Subdivide case
      -- Split the integral
      have hsplit := integral_split_mid e I hInt
      rw [hsplit]
      -- Get bounds for each half
      have hInt₁ := intervalIntegrable_splitMid_left e I hInt
      have hInt₂ := intervalIntegrable_splitMid_right e I hInt
      have h1 := ih (splitMid I).1 (tol / 2) hInt₁
      have h2 := ih (splitMid I).2 (tol / 2) hInt₂
      -- The bounds are correct, so their sum contains the sum of integrals
      simp only [splitMid_left_lo, splitMid_left_hi,
                 splitMid_right_lo, splitMid_right_hi] at h1 h2
      exact IntervalRat.mem_add h1 h2

/-- Soundness of the main adaptive integration function -/
theorem integrateAdaptive_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (tol : ℚ) (htol : 0 < tol) (maxDepth : ℕ)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
    (integrateAdaptive e I tol htol maxDepth).bound :=
  integrateAdaptiveAux_correct e hsupp I tol maxDepth hInt

end LeanCert.Engine
