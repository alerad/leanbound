/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.IntervalRat.Basic
import LeanBound.Core.Taylor
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Rational Endpoint Intervals - Computable Taylor Series

This file provides computable interval enclosures for transcendental functions
using Taylor series with rational coefficients and rigorous remainder bounds.

## Main definitions

* `ratFactorial` - Compute n! as a rational
* `pow` - Compute interval power
* `absInterval`, `maxAbs` - Absolute value helpers
* `evalTaylorSeries` - Evaluate Taylor polynomial on an interval
* `expComputable`, `sinComputable`, `cosComputable` - Computable transcendental functions
* `sinhComputable`, `coshComputable` - Computable hyperbolic functions

## Main theorems

* `mem_pow` - FTIA for interval power
* `mem_evalTaylorSeries` - General FTIA for Taylor series
* `mem_expComputable`, `mem_sinComputable`, `mem_cosComputable` - FTIA for computable functions

## Design notes

All definitions in this file use only rational arithmetic and are fully computable.
The proofs connect these to the real-valued functions via Taylor's theorem.
-/

namespace LeanBound.Core

namespace IntervalRat

/-! ### Computable Taylor series helpers -/

/-- Compute n! as a Rational -/
def ratFactorial (n : ℕ) : ℚ := (Nat.factorial n : ℚ)

/-- Compute the integer power of an interval using repeated multiplication.
    This is a simple but correct implementation. -/
def pow (I : IntervalRat) : ℕ → IntervalRat
  | 0 => singleton 1
  | n + 1 => mul I (pow I n)

/-- Compute the absolute value interval: |I| = [0, max(|lo|, |hi|)] if 0 ∈ I,
    or [min(|lo|,|hi|), max(|lo|,|hi|)] otherwise -/
def absInterval (I : IntervalRat) : IntervalRat :=
  if h1 : I.lo ≥ 0 then
    I
  else if h2 : I.hi ≤ 0 then
    neg I
  else
    ⟨0, max (-I.lo) I.hi, by
      apply le_max_of_le_right
      push_neg at h1 h2
      linarith⟩

/-- Maximum absolute value of an interval -/
def maxAbs (I : IntervalRat) : ℚ := max (|I.lo|) (|I.hi|)

/-- Evaluate Taylor series ∑_{i=0}^{n} c_i * x^i at interval I.
    Uses direct interval arithmetic on each term. -/
def evalTaylorSeries (coeffs : List ℚ) (I : IntervalRat) : IntervalRat :=
  coeffs.zipIdx.foldl (fun acc (c, i) =>
    add acc (scale c (pow I i))
  ) (singleton 0)

/-! ### Computable exp via Taylor series -/

/-- Taylor coefficients for exp: 1/i! for i = 0, 1, ..., n -/
def expTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i => 1 / ratFactorial i)

/-- Computable exp remainder bound using rational arithmetic.
    The Lagrange remainder is exp(ξ) * x^{n+1} / (n+1)! where ξ is between 0 and x.
    We use e < 3, so e^r ≤ 3^(⌈r⌉+1) as a conservative bound.

    Returns an interval [-R, R] where R bounds the remainder. -/
def expRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  -- Crude bound: e < 3, so e^r ≤ 3^(ceil(r)+1)
  let expBound := (3 : ℚ) ^ (Nat.ceil r + 1)
  let xBound := r ^ (n + 1)
  let R := expBound * xBound / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply mul_nonneg
        · apply pow_nonneg; norm_num
        · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for exp using Taylor series.

    exp(x) = ∑_{i=0}^{n} x^i/i! + R where |R| ≤ exp(|x|) * |x|^{n+1} / (n+1)!
    We conservatively bound exp(|x|) by 3^(⌈|x|⌉+1).

    This is fully computable using only rational arithmetic. -/
def expComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := expTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := expRemainderBoundComputable I n
  add polyVal remainder

/-! ### Computable sin via Taylor series -/

/-- Taylor coefficients for sin: 0, 1, 0, -1/6, 0, 1/120, ... -/
def sinTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 1 then  -- odd terms only
      ((-1 : ℚ) ^ ((i - 1) / 2)) / ratFactorial i
    else 0)

/-- Computable sin remainder bound.
    Since |sin^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
def sinRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for sin using Taylor series.

    sin(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k+1}/(2k+1)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of sin are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
def sinComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := sinTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := sinRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-! ### Computable cos via Taylor series -/

/-- Taylor coefficients for cos: 1, 0, -1/2, 0, 1/24, 0, ... -/
def cosTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 0 then  -- even terms only
      ((-1 : ℚ) ^ (i / 2)) / ratFactorial i
    else 0)

/-- Computable cos remainder bound.
    Since |cos^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
def cosRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for cos using Taylor series.

    cos(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k}/(2k)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of cos are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
def cosComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := cosTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := cosRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-! ### Computable sinh and cosh via exp -/

/-- Computable interval enclosure for sinh using exp.

    sinh(x) = (exp(x) - exp(-x)) / 2
    Since sinh is strictly monotonic, sinh([a,b]) = [sinh(a), sinh(b)].
    We compute this using the exp Taylor series. -/
def sinhComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  -- Compute exp(I) and exp(-I)
  let expPos := expComputable I n
  let expNeg := expComputable (neg I) n
  -- sinh = (exp(x) - exp(-x)) / 2
  -- For interval [lo, hi]:
  --   sinh(lo) = (exp(lo) - exp(-lo)) / 2
  --   sinh(hi) = (exp(hi) - exp(-hi)) / 2
  -- Since sinh is monotonic, we can compute at endpoints
  let sinhLo := (expPos.lo - expNeg.hi) / 2  -- Lower bound: use min exp(x), max exp(-x)
  let sinhHi := (expPos.hi - expNeg.lo) / 2  -- Upper bound: use max exp(x), min exp(-x)
  -- Interval validity: sinhLo ≤ sinhHi follows from expPos.lo ≤ expPos.hi and expNeg.lo ≤ expNeg.hi
  if h : sinhLo ≤ sinhHi then
    ⟨sinhLo, sinhHi, h⟩
  else
    -- Fallback for edge cases where Taylor approximation gives unexpected order
    ⟨min sinhLo sinhHi, max sinhLo sinhHi, @min_le_max _ _ sinhLo sinhHi⟩

/-- Computable interval enclosure for cosh using exp.

    cosh(x) = (exp(x) + exp(-x)) / 2
    cosh has minimum 1 at x = 0, and is symmetric: cosh(-x) = cosh(x).
    We compute this using the exp Taylor series. -/
def coshComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  -- Compute exp(I) and exp(-I)
  let expPos := expComputable I n
  let expNeg := expComputable (neg I) n
  -- cosh = (exp(x) + exp(-x)) / 2
  -- Lower bound: minimum of cosh over the interval
  -- Upper bound: maximum of cosh over the interval
  let coshLo := (expPos.lo + expNeg.lo) / 2  -- Lower bound
  let coshHi := (expPos.hi + expNeg.hi) / 2  -- Upper bound
  -- Use 1 as lower bound (cosh x ≥ 1 always), take max with computed value
  -- For valid interval, we need lo ≤ hi
  let safeLo := max 1 coshLo
  if h : safeLo ≤ coshHi then
    ⟨safeLo, coshHi, h⟩
  else
    -- Fallback: if Taylor underestimates, use wide bounds
    ⟨1, max 2 coshHi, by
      have h1 : (1 : ℚ) ≤ 2 := by norm_num
      exact le_trans h1 (le_max_left _ _)⟩

/-! ### FTIA for pow -/

/-- FTIA for interval power -/
theorem mem_pow {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    x ^ n ∈ pow I n := by
  induction n with
  | zero =>
    simp only [_root_.pow_zero, pow]
    simp only [mem_def, singleton]
    norm_num
  | succ n ih =>
    simp only [_root_.pow_succ, pow]
    -- x^(n+1) = x * x^n ∈ mul I (pow I n)
    have h : x * x ^ n ∈ mul I (pow I n) := mem_mul hx ih
    convert h using 1
    ring

/-! ### Helper lemmas for Taylor series membership -/

/-- Any x in I has |x| ≤ maxAbs I -/
theorem abs_le_maxAbs {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : |x| ≤ maxAbs I := by
  simp only [mem_def, maxAbs] at *
  have hlo : -(max |I.lo| |I.hi|) ≤ I.lo := by
    calc -(max |I.lo| |I.hi|) ≤ -|I.lo| := neg_le_neg (le_max_left _ _)
      _ ≤ I.lo := neg_abs_le _
  have hhi : I.hi ≤ max |I.lo| |I.hi| := le_trans (le_abs_self _) (le_max_right _ _)
  rw [abs_le]
  constructor
  · calc (-(max |I.lo| |I.hi| : ℚ) : ℝ) ≤ I.lo := by exact_mod_cast hlo
      _ ≤ x := hx.1
  · calc x ≤ I.hi := hx.2
      _ ≤ max |I.lo| |I.hi| := by exact_mod_cast hhi

/-- If |x| ≤ R for nonnegative R, then x ∈ [-R, R].
    This is the key micro-lemma for embedding Lagrange remainder bounds into intervals. -/
theorem abs_le_mem_symmetric_interval {x : ℝ} {R : ℚ} (hR : 0 ≤ R) (h : |x| ≤ R) :
    x ∈ (⟨-R, R, by linarith⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  constructor
  · have := neg_abs_le x; linarith
  · exact le_trans (le_abs_self x) h

/-- Domain setup for Taylor theorem: if |x| ≤ r for nonnegative r,
    then x ∈ [-r, r] as an Icc with the required inequalities. -/
theorem domain_from_abs_bound {x : ℝ} {r : ℚ} (_hr : 0 ≤ r) (habs : |x| ≤ r) :
    x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) := by
  simp only [Set.mem_Icc, Rat.cast_neg]
  exact abs_le.mp habs

/-- Combined domain setup from interval membership. -/
theorem domain_from_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    let r := maxAbs I
    (0 : ℝ) ≤ r ∧ |x| ≤ r ∧ x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) ∧
    ((-r : ℚ) : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ (r : ℚ) ∧ ((-r : ℚ) : ℝ) ≤ r := by
  have hr_nonneg : 0 ≤ maxAbs I := le_max_of_le_left (abs_nonneg I.lo)
  have habs_x := abs_le_maxAbs hx
  have hr_nonneg_real : (0 : ℝ) ≤ maxAbs I := by exact_mod_cast hr_nonneg
  have hdom := domain_from_abs_bound hr_nonneg habs_x
  refine ⟨hr_nonneg_real, habs_x, hdom, ?_, hr_nonneg_real, ?_⟩
  · simp only [Rat.cast_neg]; linarith
  · simp only [Rat.cast_neg]; linarith

/-- Convert an absolute value bound |v| ≤ R to interval membership v ∈ [-R, R].
    This is the key micro-lemma for the final step of Taylor remainder bounds. -/
theorem remainder_to_interval {v : ℝ} {R : ℚ} (hbound : |v| ≤ R) :
    v ∈ (⟨-R, R, by
      have h1 : 0 ≤ |v| := abs_nonneg v
      have h2 : (0 : ℝ) ≤ (R : ℚ) := le_trans h1 hbound
      linarith [Rat.cast_nonneg.mp h2]⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  exact abs_le.mp hbound

/-- Key lemma: exp(ξ) ≤ 3^(⌈r⌉+1) for |ξ| ≤ r -/
theorem exp_bound_by_pow3 {r : ℚ} (_hr : 0 ≤ r) {ξ : ℝ} (hξ : |ξ| ≤ r) :
    Real.exp ξ ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
  -- e < 3, using Real.exp_one_lt_d9 which gives exp(1) < 2.7182818286
  have h3 : Real.exp 1 < 3 := by
    have h := Real.exp_one_lt_d9  -- exp(1) < 2.7182818286
    have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
    exact lt_trans h h2
  have hceil : (r : ℝ) ≤ Nat.ceil r := by
    have h : r ≤ (Nat.ceil r : ℚ) := Nat.le_ceil r
    exact_mod_cast h
  calc Real.exp ξ ≤ Real.exp |ξ| := Real.exp_le_exp.mpr (le_abs_self ξ)
    _ ≤ Real.exp r := Real.exp_le_exp.mpr hξ
    _ ≤ Real.exp (Nat.ceil r) := Real.exp_le_exp.mpr hceil
    _ = Real.exp 1 ^ (Nat.ceil r) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ 3 ^ (Nat.ceil r) := by
        rcases Nat.eq_zero_or_pos (Nat.ceil r) with hr0 | hrpos
        · simp [hr0]
        · exact le_of_lt (pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (Nat.pos_iff_ne_zero.mp hrpos))
    _ ≤ 3 ^ (Nat.ceil r + 1) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ _)

/-! ### Coefficient matching lemmas -/

/-- For exp, all iterated derivatives at 0 equal 1. -/
lemma iteratedDeriv_exp_zero (i : ℕ) : iteratedDeriv i Real.exp 0 = 1 := by
  simp [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-- Auxiliary lemma: foldl over zipIdx produces valid interval bounds.
    If y ∈ acc and x ∈ I, then
    y + ∑_{(c,i) ∈ rest} c * x^i ∈ rest.foldl (fun acc (c, i) => add acc (scale c (pow I i))) acc -/
private lemma mem_foldl_zipIdx_aux {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (rest : List (ℚ × ℕ)) (acc : IntervalRat) (y : ℝ) (hy : y ∈ acc) :
    y + (rest.map (fun (c, i) => (c : ℝ) * x ^ i)).sum ∈
      rest.foldl (fun acc (c, i) => add acc (scale c (pow I i))) acc := by
  induction rest generalizing acc y with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    exact hy
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    -- hd = (c, i), need to show y + (c * x^i + rest_sum) ∈ ...
    have hterm : (hd.1 : ℝ) * x ^ hd.2 ∈ scale hd.1 (pow I hd.2) :=
      mem_scale hd.1 (mem_pow hx hd.2)
    have hadd : y + (hd.1 : ℝ) * x ^ hd.2 ∈ add acc (scale hd.1 (pow I hd.2)) :=
      mem_add hy hterm
    have heq : y + ((hd.1 : ℝ) * x ^ hd.2 + (tl.map (fun (c, i) => (c : ℝ) * x ^ i)).sum) =
        (y + (hd.1 : ℝ) * x ^ hd.2) + (tl.map (fun (c, i) => (c : ℝ) * x ^ i)).sum := by ring
    rw [heq]
    exact ih (add acc (scale hd.1 (pow I hd.2))) (y + (hd.1 : ℝ) * x ^ hd.2) hadd

/-- General FTIA for evalTaylorSeries: if coeffs has length n+1, then
    ∑_{i=0}^{n} coeffs[i] * x^i ∈ evalTaylorSeries coeffs I for x ∈ I. -/
theorem mem_evalTaylorSeries {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (coeffs : List ℚ) :
    (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum ∈ evalTaylorSeries coeffs I := by
  simp only [evalTaylorSeries]
  have h0 : (0 : ℝ) ∈ singleton 0 := by
    simp only [mem_def, singleton, Rat.cast_zero, le_refl, and_self]
  have heq : (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum =
      0 + (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum := by ring
  rw [heq]
  exact mem_foldl_zipIdx_aux hx coeffs.zipIdx (singleton 0) 0 h0

/-- Helper: (List.range n).map f).sum = ∑ i ∈ Finset.range n, f i -/
private lemma list_map_sum_eq_finset_sum {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ]
    rw [ih, add_comm]

/-- Helper: zipIdx of List.range just pairs each element with its index (which is itself) -/
private lemma zipIdx_range_map {α : Type*} (f : ℕ → ℕ → α) (n : ℕ) :
    (List.range n).zipIdx.map (fun p => f p.1 p.2) = (List.range n).map (fun i => f i i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.zipIdx_append, List.map_append, List.length_range]
    rw [ih]
    simp only [List.zipIdx_singleton, List.map_singleton, zero_add]

/-- The exp Taylor polynomial value matches our evalTaylorSeries.
    The proof shows that our list-based polynomial evaluation produces the same
    sum as the Finset.sum form used in Mathlib's Taylor theorem. -/
theorem mem_evalTaylorSeries_exp {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i ∈
      evalTaylorSeries (expTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (expTaylorCoeffs n)
  convert hmem using 1
  simp only [expTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (1 / i.factorial : ℝ) * x ^ i) (n + 1)]
  -- The two list maps are equal: both compute [1/0! * x^0, 1/1! * x^1, ...]
  -- LHS: (List.range (n+1)).map (fun i => 1/i! * x^i)
  -- RHS: zipIdx.map with Prod.map composition
  -- For List.range, zipIdx gives [(0,0), (1,1), ...], so they match
  congr 1
  symm
  -- The RHS has type (ℚ × ℕ) from Prod.map applied to zipIdx pairs
  -- Step 1: Simplify the composition
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map (fun i => (1 : ℚ) / i.factorial) id) =
      (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / p.1.factorial : ℝ) * x ^ p.2) := by
    apply List.map_congr_left
    intro ⟨a, b⟩ _
    simp only [Function.comp_apply, Prod.map_apply, id_eq, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  -- Step 2: Use zipIdx_range_map to eliminate zipIdx
  have h2 : (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / p.1.factorial : ℝ) * x ^ p.2) =
      (List.range (n + 1)).map (fun i => ((1 : ℚ) / i.factorial : ℝ) * x ^ i) := by
    convert zipIdx_range_map (fun a b => ((1 : ℚ) / a.factorial : ℝ) * x ^ b) (n + 1) using 2
  -- Step 3: Simplify the casts
  have h3 : (List.range (n + 1)).map (fun i => ((1 : ℚ) / i.factorial : ℝ) * x ^ i) =
      (List.range (n + 1)).map (fun i => (1 / i.factorial : ℝ) * x ^ i) := by
    apply List.map_congr_left
    intro i _
    simp only [Rat.cast_one]
  rw [h1, h2, h3]

/-- The iterated derivative of sin is sin, cos, -sin, -cos in a cycle of 4. -/
private lemma iteratedDeriv_sin (n : ℕ) : iteratedDeriv n Real.sin =
    if n % 4 = 0 then Real.sin
    else if n % 4 = 1 then Real.cos
    else if n % 4 = 2 then fun x => -Real.sin x
    else fun x => -Real.cos x := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv sin = cos
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte, Real.deriv_sin]; norm_num
    · -- n % 4 = 1: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of sin at 0 follows the pattern 0, 1, 0, -1, 0, 1, 0, -1, ... -/
private lemma iteratedDeriv_sin_zero (i : ℕ) : iteratedDeriv i Real.sin 0 =
    if i % 4 = 0 then 0
    else if i % 4 = 1 then 1
    else if i % 4 = 2 then 0
    else -1 := by
  rw [iteratedDeriv_sin]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.sin_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h3]; norm_num [Real.cos_zero]

/-- The sin Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i sin 0 = 0, 1, 0, -1, 0, 1, ... matches sinTaylorCoeffs. -/
theorem mem_evalTaylorSeries_sin {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (sinTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (sinTaylorCoeffs n)
  convert hmem using 1
  simp only [sinTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert zipIdx_range_map
      (fun a b => ((if a % 2 = 1 then (-1 : ℚ) ^ ((a - 1) / 2) / a.factorial else 0 : ℚ) : ℝ) * x ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  -- Need: (iteratedDeriv i sin 0 / i!) * x^i = ((sinCoeff i) : ℝ) * x^i
  -- where sinCoeff i = if i % 2 = 1 then (-1)^((i-1)/2) / i! else 0
  congr 1
  -- Show iteratedDeriv i sin 0 / i! = sinCoeff i (as ℝ)
  rw [iteratedDeriv_sin_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h0, ↓reduceIte, zero_div, if_neg hi_ne, Rat.cast_zero]
  · -- i % 4 = 1: i is odd, iteratedDeriv = 1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h1, ↓reduceIte, if_pos hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    congr 1
    have heven : Even ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    exact heven.neg_one_pow
  · -- i % 4 = 2: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h2, ↓reduceIte, if_neg hi_ne]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = -1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h3, if_pos hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num

/-- The iterated derivative of cos is cos, -sin, -cos, sin in a cycle of 4. -/
private lemma iteratedDeriv_cos (n : ℕ) : iteratedDeriv n Real.cos =
    if n % 4 = 0 then Real.cos
    else if n % 4 = 1 then fun x => -Real.sin x
    else if n % 4 = 2 then fun x => -Real.cos x
    else Real.sin := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 1: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv sin = cos
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of cos at 0 follows the pattern 1, 0, -1, 0, 1, 0, ... -/
private lemma iteratedDeriv_cos_zero (i : ℕ) : iteratedDeriv i Real.cos 0 =
    if i % 4 = 0 then 1
    else if i % 4 = 1 then 0
    else if i % 4 = 2 then -1
    else 0 := by
  rw [iteratedDeriv_cos]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.cos_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h3]; norm_num [Real.sin_zero]

/-- The cos Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i cos 0 = 1, 0, -1, 0, 1, 0, ... matches cosTaylorCoeffs. -/
theorem mem_evalTaylorSeries_cos {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (cosTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (cosTaylorCoeffs n)
  convert hmem using 1
  simp only [cosTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert zipIdx_range_map
      (fun a b => ((if a % 2 = 0 then (-1 : ℚ) ^ (a / 2) / a.factorial else 0 : ℚ) : ℝ) * x ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  congr 1
  -- Show iteratedDeriv i cos 0 / i! = cosCoeff i (as ℝ)
  rw [iteratedDeriv_cos_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h0, ↓reduceIte, one_div, if_pos hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have heven : Even (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [heven.neg_one_pow]
    ring
  · -- i % 4 = 1: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h1, ↓reduceIte, if_neg hi_ne]
    norm_num
  · -- i % 4 = 2: i is even, iteratedDeriv = -1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h2, if_pos hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h3, if_neg hi_ne]
    norm_num

/-! ### Taylor remainder micro-lemmas -/

/-- Unified Taylor remainder bound for exp: given x ∈ I with r = maxAbs I,
    the Taylor remainder |exp x - poly(x)| ≤ 3^(⌈r⌉+1) * r^(n+1) / (n+1)!.
    This encapsulates the domain setup and remainder calculation. -/
theorem exp_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
    ∈ expRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := ((3 : ℚ) ^ (Nat.ceil r + 1) * r ^ (n + 1) / ratFactorial (n + 1))

  -- Apply Taylor theorem
  have hexp_smooth : ContDiff ℝ (n + 1) Real.exp := Real.contDiff_exp.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.exp y‖ ≤ Real.exp r := by
    intro y hy
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
    exact Real.exp_le_exp.mpr hy.2
  have hTaylor := taylor_remainder_bound hab h0a h0b hexp_smooth hderiv_bound
    (Real.exp_pos (r : ℚ)).le x hdom

  -- Compute remainder bound
  have hr_nonneg_rat : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
  have hexp_r_bound : Real.exp (r : ℚ) ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
    apply exp_bound_by_pow3 hr_nonneg_rat
    rw [abs_of_nonneg hr_nonneg]
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : Real.exp (r : ℚ) * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero]
    calc Real.exp (r : ℚ) * |x| ^ (n + 1) / (n + 1).factorial
        ≤ (3 : ℝ) ^ (Nat.ceil r + 1) * (r : ℝ) ^ (n + 1) / (n + 1).factorial := by
          apply div_le_div_of_nonneg_right _ hfact_pos.le
          apply mul_le_mul hexp_r_bound hx_pow_bound (pow_nonneg (abs_nonneg x) _)
          apply pow_nonneg; norm_num
      _ = (R : ℝ) := by
          simp only [R, ratFactorial, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
            Rat.cast_natCast, Rat.cast_ofNat]

  -- Convert to interval membership
  simp only [expRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.exp x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for sin: given x ∈ I with r = maxAbs I,
    the Taylor remainder |sin x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |sin^(k)(x)| ≤ 1 for all k, x. -/
theorem sin_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
    ∈ sinRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))

  -- Apply Taylor theorem with M = 1
  have hsin_smooth : ContDiff ℝ (n + 1) Real.sin := Real.contDiff_sin.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.sin y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).1
  have hTaylor := taylor_remainder_bound hab h0a h0b hsin_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom

  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

  -- Convert to interval membership
  simp only [sinRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.sin x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for cos: given x ∈ I with r = maxAbs I,
    the Taylor remainder |cos x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |cos^(k)(x)| ≤ 1 for all k, x. -/
theorem cos_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
    ∈ cosRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))

  -- Apply Taylor theorem with M = 1
  have hcos_smooth : ContDiff ℝ (n + 1) Real.cos := Real.contDiff_cos.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.cos y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).2
  have hTaylor := taylor_remainder_bound hab h0a h0b hcos_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom

  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

  -- Convert to interval membership
  simp only [cosRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.cos x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-! ### FTIA for computable functions -/

/-- FTIA for expComputable: Real.exp x ∈ expComputable I n for any x ∈ I.

    This theorem establishes that the computable Taylor series evaluation
    correctly bounds the real exponential function. The proof uses the
    Taylor remainder micro-lemma which encapsulates the Lagrange form. -/
theorem mem_expComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x ∈ expComputable I n := by
  simp only [expComputable]
  -- Strategy: exp x = poly(x) + remainder, with both in their respective intervals

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (expTaylorCoeffs n) I := by
    have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i =
        ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i := by
      apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
    rw [hsum_eq]; exact mem_evalTaylorSeries_exp hx n

  -- Remainder part ∈ expRemainderBoundComputable (via micro-lemma)
  have hrem_mem := exp_taylor_remainder_in_interval hx n

  -- Combine: exp x = poly + rem
  have heq : Real.exp x = (∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) +
      (Real.exp x - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) := by ring
  rw [heq]; exact mem_add hpoly_mem hrem_mem

/-- FTIA for sinComputable: Real.sin x ∈ sinComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound sin ∈ [-1, 1]. -/
theorem mem_sinComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x ∈ sinComputable I n := by
  simp only [sinComputable]
  -- Strategy: sin x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (sinTaylorCoeffs n) I := mem_evalTaylorSeries_sin hx n

  -- Remainder part ∈ sinRemainderBoundComputable (via micro-lemma)
  have hrem_mem := sin_taylor_remainder_in_interval hx n

  -- Raw interval membership: sin x ∈ poly + remainder
  have hraw_mem : Real.sin x ∈ add (evalTaylorSeries (sinTaylorCoeffs n) I)
      (sinRemainderBoundComputable I n) := by
    have heq : Real.sin x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) +
        (Real.sin x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem

  -- Global bound: sin x ∈ [-1, 1]
  have hglobal_mem : Real.sin x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_sin x
    · simp only [Rat.cast_one]; exact Real.sin_le_one x

  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

/-- FTIA for cosComputable: Real.cos x ∈ cosComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound cos ∈ [-1, 1]. -/
theorem mem_cosComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x ∈ cosComputable I n := by
  simp only [cosComputable]
  -- Strategy: cos x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (cosTaylorCoeffs n) I := mem_evalTaylorSeries_cos hx n

  -- Remainder part ∈ cosRemainderBoundComputable (via micro-lemma)
  have hrem_mem := cos_taylor_remainder_in_interval hx n

  -- Raw interval membership: cos x ∈ poly + remainder
  have hraw_mem : Real.cos x ∈ add (evalTaylorSeries (cosTaylorCoeffs n) I)
      (cosRemainderBoundComputable I n) := by
    have heq : Real.cos x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) +
        (Real.cos x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem

  -- Global bound: cos x ∈ [-1, 1]
  have hglobal_mem : Real.cos x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_cos x
    · simp only [Rat.cast_one]; exact Real.cos_le_one x

  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

end IntervalRat

end LeanBound.Core
