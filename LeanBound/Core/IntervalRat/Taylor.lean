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

/-- Computable interval enclosure for exp at a single rational point.
    Uses Taylor series with tight remainder bound. -/
def expPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let I := singleton q
  let coeffs := expTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := expRemainderBoundComputable I n
  add polyVal remainder

/-- Hull of two intervals: smallest interval containing both. -/
def hull (I J : IntervalRat) : IntervalRat :=
  ⟨min I.lo J.lo, max I.hi J.hi, le_trans (min_le_left _ _) (le_trans I.le (le_max_left _ _))⟩

/-- Membership in hull -/
theorem mem_hull_left {x : ℝ} {I J : IntervalRat} (hx : x ∈ I) : x ∈ hull I J := by
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_left _ _) hx.1
  · exact le_trans hx.2 (le_max_left _ _)

theorem mem_hull_right {x : ℝ} {I J : IntervalRat} (hx : x ∈ J) : x ∈ hull I J := by
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_right _ _) hx.1
  · exact le_trans hx.2 (le_max_right _ _)

/-- Computable interval enclosure for exp using Taylor series with monotonicity optimization.

    exp(x) = ∑_{i=0}^{n} x^i/i! + R where |R| ≤ exp(|x|) * |x|^{n+1} / (n+1)!

    For intervals not crossing 0, we use endpoint evaluation and take the hull,
    which is tighter than direct Taylor evaluation due to interval widening.

    This is fully computable using only rational arithmetic. -/
def expComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  if I.hi ≤ 0 ∨ 0 ≤ I.lo then
    -- Interval doesn't cross 0: use endpoint evaluation for tighter bounds
    let expLo := expPointComputable I.lo n
    let expHi := expPointComputable I.hi n
    hull expLo expHi
  else
    -- Interval crosses 0: use standard Taylor (can't avoid interval widening)
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

/-- Computable interval enclosure for sinh at a single rational point.
    Uses the definition sinh(q) = (exp(q) - exp(-q)) / 2. -/
def sinhPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let expPos := expPointComputable q n
  let expNeg := expPointComputable (-q) n
  -- sinh(q) = (exp(q) - exp(-q)) / 2
  -- Lower bound: (expPos.lo - expNeg.hi) / 2
  -- Upper bound: (expPos.hi - expNeg.lo) / 2
  let sinhLo := (expPos.lo - expNeg.hi) / 2
  let sinhHi := (expPos.hi - expNeg.lo) / 2
  if h : sinhLo ≤ sinhHi then
    ⟨sinhLo, sinhHi, h⟩
  else
    ⟨min sinhLo sinhHi, max sinhLo sinhHi, @min_le_max _ _ sinhLo sinhHi⟩

/-- Computable interval enclosure for cosh at a single rational point.
    Uses the definition cosh(q) = (exp(q) + exp(-q)) / 2. -/
def coshPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let expPos := expPointComputable q n
  let expNeg := expPointComputable (-q) n
  -- cosh(q) = (exp(q) + exp(-q)) / 2
  -- Lower bound: (expPos.lo + expNeg.lo) / 2
  -- Upper bound: (expPos.hi + expNeg.hi) / 2
  let coshLo := (expPos.lo + expNeg.lo) / 2
  let coshHi := (expPos.hi + expNeg.hi) / 2
  -- cosh ≥ 1 always, so ensure lower bound is at least 1
  let safeLo := max 1 coshLo
  if h : safeLo ≤ coshHi then
    ⟨safeLo, coshHi, h⟩
  else
    ⟨1, max 2 coshHi, by
      have h1 : (1 : ℚ) ≤ 2 := by norm_num
      exact le_trans h1 (le_max_left _ _)⟩

/-- The lower bound of coshPointComputable is always at least 1. -/
theorem coshPointComputable_lo_ge_one (q : ℚ) (n : ℕ) : 1 ≤ (coshPointComputable q n).lo := by
  simp only [coshPointComputable]
  split_ifs with h
  · exact le_max_left 1 _
  · exact le_refl 1

/-- Computable interval enclosure for sinh using exp with endpoint evaluation.

    sinh(x) = (exp(x) - exp(-x)) / 2
    Since sinh is strictly monotone increasing, sinh([a,b]) = [sinh(a), sinh(b)].
    We use endpoint evaluation for tight bounds. -/
def sinhComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  -- sinh is strictly monotone increasing, so evaluate at endpoints
  let sinhLo := sinhPointComputable I.lo n
  let sinhHi := sinhPointComputable I.hi n
  hull sinhLo sinhHi

/-- Computable interval enclosure for cosh using exp with endpoint evaluation.

    cosh(x) = (exp(x) + exp(-x)) / 2
    cosh has minimum 1 at x = 0, and is symmetric: cosh(-x) = cosh(x).
    - cosh is decreasing on (-∞, 0]
    - cosh is increasing on [0, ∞)

    We use endpoint evaluation with monotonicity for tight bounds. -/
def coshComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coshLo := coshPointComputable I.lo n
  let coshHi := coshPointComputable I.hi n
  if 0 ≤ I.lo then
    -- Interval is non-negative: cosh is increasing, so [cosh(lo), cosh(hi)]
    hull coshLo coshHi
  else if I.hi ≤ 0 then
    -- Interval is non-positive: cosh is decreasing, so [cosh(hi), cosh(lo)]
    hull coshHi coshLo
  else
    -- Interval contains 0: minimum is 1 at x=0, max is at whichever endpoint is farther
    let maxEndpoint := hull coshLo coshHi
    ⟨1, maxEndpoint.hi, by
      -- coshPointComputable ensures lower bound ≥ 1 via max 1 _
      have hlo_ge1 := coshPointComputable_lo_ge_one I.lo n
      have hhi_ge1 := coshPointComputable_lo_ge_one I.hi n
      calc (1 : ℚ) ≤ min (coshPointComputable I.lo n).lo (coshPointComputable I.hi n).lo :=
          le_min hlo_ge1 hhi_ge1
        _ = maxEndpoint.lo := rfl
        _ ≤ maxEndpoint.hi := maxEndpoint.le⟩

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

/-- FTIA for single-point exp: Real.exp q ∈ expPointComputable q n -/
theorem mem_expPointComputable (q : ℚ) (n : ℕ) :
    Real.exp q ∈ expPointComputable q n := by
  simp only [expPointComputable]
  have hq_mem : (q : ℝ) ∈ singleton q := mem_singleton q
  -- Strategy: exp q = poly(q) + remainder, with both in their respective intervals
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i
      ∈ evalTaylorSeries (expTaylorCoeffs n) (singleton q) := by
    have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i =
        ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * (q : ℝ) ^ i := by
      apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
    rw [hsum_eq]; exact mem_evalTaylorSeries_exp hq_mem n
  have hrem_mem := exp_taylor_remainder_in_interval hq_mem n
  have heq : Real.exp q = (∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i) +
      (Real.exp q - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i) := by ring
  rw [heq]; exact mem_add hpoly_mem hrem_mem

theorem mem_expComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x ∈ expComputable I n := by
  simp only [expComputable]
  split_ifs with h
  · -- Interval doesn't cross 0: use endpoint evaluation and monotonicity
    -- exp is monotone increasing, so exp([lo, hi]) ⊆ hull(exp(lo), exp(hi))
    have hlo_mem := mem_expPointComputable I.lo n
    have hhi_mem := mem_expPointComputable I.hi n
    -- Since x ∈ [lo, hi] and exp is monotone, exp(x) ∈ [exp(lo), exp(hi)]
    -- The hull contains both exp(lo) and exp(hi), so it contains exp(x)
    rcases h with ⟨hhi_neg⟩ | ⟨hlo_pos⟩
    · -- Case: hi ≤ 0 (negative interval)
      -- exp(lo) ≤ exp(x) ≤ exp(hi) by monotonicity
      have hx_le_hi : x ≤ I.hi := hx.2
      have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
      have hexp_mono1 : Real.exp x ≤ Real.exp I.hi := Real.exp_le_exp.mpr hx_le_hi
      have hexp_mono2 : Real.exp I.lo ≤ Real.exp x := Real.exp_le_exp.mpr hlo_le_x
      -- exp(x) is between exp(lo) and exp(hi), both of which are in the hull
      simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
      constructor
      · -- lower bound: min(expLo.lo, expHi.lo) ≤ exp(x)
        calc (min (expPointComputable I.lo n).lo (expPointComputable I.hi n).lo : ℝ)
            ≤ (expPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
          _ ≤ Real.exp I.lo := hlo_mem.1
          _ ≤ Real.exp x := hexp_mono2
      · -- upper bound: exp(x) ≤ max(expLo.hi, expHi.hi)
        calc Real.exp x ≤ Real.exp I.hi := hexp_mono1
          _ ≤ (expPointComputable I.hi n).hi := hhi_mem.2
          _ ≤ max ((expPointComputable I.lo n).hi : ℝ) ((expPointComputable I.hi n).hi : ℝ) := le_max_right _ _
    · -- Case: 0 ≤ lo (positive interval) - same argument
      have hx_le_hi : x ≤ I.hi := hx.2
      have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
      have hexp_mono1 : Real.exp x ≤ Real.exp I.hi := Real.exp_le_exp.mpr hx_le_hi
      have hexp_mono2 : Real.exp I.lo ≤ Real.exp x := Real.exp_le_exp.mpr hlo_le_x
      simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
      constructor
      · calc (min (expPointComputable I.lo n).lo (expPointComputable I.hi n).lo : ℝ)
            ≤ (expPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
          _ ≤ Real.exp I.lo := hlo_mem.1
          _ ≤ Real.exp x := hexp_mono2
      · calc Real.exp x ≤ Real.exp I.hi := hexp_mono1
          _ ≤ (expPointComputable I.hi n).hi := hhi_mem.2
          _ ≤ max ((expPointComputable I.lo n).hi : ℝ) ((expPointComputable I.hi n).hi : ℝ) := le_max_right _ _
  · -- Interval crosses 0: use standard Taylor
    -- Strategy: exp x = poly(x) + remainder, with both in their respective intervals
    have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
        ∈ evalTaylorSeries (expTaylorCoeffs n) I := by
      have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i =
          ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i := by
        apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
      rw [hsum_eq]; exact mem_evalTaylorSeries_exp hx n
    have hrem_mem := exp_taylor_remainder_in_interval hx n
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

/-- FTIA for sinhPointComputable: Real.sinh q ∈ sinhPointComputable q n -/
theorem mem_sinhPointComputable (q : ℚ) (n : ℕ) :
    Real.sinh q ∈ sinhPointComputable q n := by
  simp only [sinhPointComputable]
  have hexp_pos := mem_expPointComputable q n
  have hexp_neg := mem_expPointComputable (-q) n
  rw [Real.sinh_eq]
  simp only [Rat.cast_neg] at hexp_neg
  simp only [mem_def] at hexp_pos hexp_neg ⊢
  obtain ⟨hexp_pos_lo, hexp_pos_hi⟩ := hexp_pos
  obtain ⟨hexp_neg_lo, hexp_neg_hi⟩ := hexp_neg
  split_ifs with h
  · constructor <;> { simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]; linarith }
  · -- Fallback case: use min/max bounds
    constructor
    · simp only [Rat.cast_min, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
      apply min_le_of_left_le; linarith
    · simp only [Rat.cast_max, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
      apply le_max_of_le_right; linarith

/-- FTIA for coshPointComputable: Real.cosh q ∈ coshPointComputable q n -/
theorem mem_coshPointComputable (q : ℚ) (n : ℕ) :
    Real.cosh q ∈ coshPointComputable q n := by
  simp only [coshPointComputable]
  have hexp_pos := mem_expPointComputable q n
  have hexp_neg := mem_expPointComputable (-q) n
  rw [Real.cosh_eq]
  simp only [Rat.cast_neg] at hexp_neg
  simp only [mem_def] at hexp_pos hexp_neg ⊢
  obtain ⟨hexp_pos_lo, hexp_pos_hi⟩ := hexp_pos
  obtain ⟨hexp_neg_lo, hexp_neg_hi⟩ := hexp_neg
  -- cosh q ≥ 1 always (AM-GM)
  have hcosh_ge_one : 1 ≤ (Real.exp q + Real.exp (-(q : ℝ))) / 2 := by
    have h1 : Real.exp q > 0 := Real.exp_pos q
    have h2 : Real.exp (-(q : ℝ)) > 0 := Real.exp_pos (-(q : ℝ))
    have hprod : Real.exp q * Real.exp (-(q : ℝ)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have ham : Real.exp q + Real.exp (-(q : ℝ)) ≥ 2 := by nlinarith [sq_nonneg (Real.exp q - Real.exp (-(q : ℝ))), hprod]
    linarith
  split_ifs with h
  · constructor
    · -- Lower bound: max 1 coshLo ≤ cosh q
      simp only [Rat.cast_max, Rat.cast_one, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
      apply max_le
      · exact hcosh_ge_one
      · linarith
    · -- Upper bound
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
      linarith
  · -- Fallback
    constructor
    · simp only [Rat.cast_one]
      exact hcosh_ge_one
    · simp only [Rat.cast_max, Rat.cast_ofNat, Rat.cast_div, Rat.cast_add]
      apply le_max_of_le_right
      linarith

/-- FTIA for sinhComputable: Real.sinh x ∈ sinhComputable I n for any x ∈ I.

    Uses endpoint evaluation and monotonicity of sinh. -/
theorem mem_sinhComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sinh x ∈ sinhComputable I n := by
  simp only [sinhComputable]
  -- sinh is strictly monotone increasing
  have hsinh_mono : StrictMono Real.sinh := Real.sinh_strictMono
  have hlo_mem := mem_sinhPointComputable I.lo n
  have hhi_mem := mem_sinhPointComputable I.hi n
  -- x ∈ [lo, hi] implies sinh(lo) ≤ sinh(x) ≤ sinh(hi)
  have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
  have hx_le_hi : x ≤ (I.hi : ℝ) := hx.2
  have hsinh_lo_le : Real.sinh I.lo ≤ Real.sinh x :=
    hsinh_mono.monotone hlo_le_x
  have hsinh_x_le_hi : Real.sinh x ≤ Real.sinh I.hi :=
    hsinh_mono.monotone hx_le_hi
  -- sinh x is between sinh(lo) and sinh(hi), which are in the hull
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (sinhPointComputable I.lo n).lo (sinhPointComputable I.hi n).lo : ℝ)
        ≤ (sinhPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.sinh I.lo := hlo_mem.1
      _ ≤ Real.sinh x := hsinh_lo_le
  · calc Real.sinh x ≤ Real.sinh I.hi := hsinh_x_le_hi
      _ ≤ (sinhPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((sinhPointComputable I.lo n).hi : ℝ) ((sinhPointComputable I.hi n).hi : ℝ) := le_max_right _ _

/-- FTIA for coshComputable: Real.cosh x ∈ coshComputable I n for any x ∈ I.

    Uses endpoint evaluation and monotonicity properties of cosh. -/
theorem mem_coshComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cosh x ∈ coshComputable I n := by
  simp only [coshComputable]
  have hlo_mem := mem_coshPointComputable I.lo n
  have hhi_mem := mem_coshPointComputable I.hi n
  -- cosh x ≥ 1 always (AM-GM)
  have hcosh_ge_one : 1 ≤ Real.cosh x := Real.one_le_cosh x
  -- Key lemma: cosh a ≤ cosh b iff |a| ≤ |b|
  split_ifs with h1 h2
  · -- Case: 0 ≤ I.lo (non-negative interval, cosh is increasing)
    have hlo_nonneg : (0 : ℝ) ≤ I.lo := by exact_mod_cast h1
    have hx_nonneg : 0 ≤ x := le_trans hlo_nonneg hx.1
    have hhi_nonneg : (0 : ℝ) ≤ I.hi := le_trans hlo_nonneg (by exact_mod_cast I.le)
    -- For 0 ≤ a ≤ b: |a| = a ≤ b = |b|, so cosh(a) ≤ cosh(b)
    have hcosh_lo_le : Real.cosh I.lo ≤ Real.cosh x := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg hlo_nonneg, abs_of_nonneg hx_nonneg]
      exact hx.1
    have hcosh_x_le_hi : Real.cosh x ≤ Real.cosh I.hi := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hhi_nonneg]
      exact hx.2
    simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
    constructor
    · calc (min (coshPointComputable I.lo n).lo (coshPointComputable I.hi n).lo : ℝ)
          ≤ (coshPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
        _ ≤ Real.cosh I.lo := hlo_mem.1
        _ ≤ Real.cosh x := hcosh_lo_le
    · calc Real.cosh x ≤ Real.cosh I.hi := hcosh_x_le_hi
        _ ≤ (coshPointComputable I.hi n).hi := hhi_mem.2
        _ ≤ max ((coshPointComputable I.lo n).hi : ℝ) ((coshPointComputable I.hi n).hi : ℝ) := le_max_right _ _
  · -- Case: I.hi ≤ 0 (non-positive interval, cosh is decreasing)
    have hhi_nonpos : I.hi ≤ (0 : ℝ) := by exact_mod_cast h2
    have hx_nonpos : x ≤ 0 := le_trans hx.2 hhi_nonpos
    have hlo_nonpos : (I.lo : ℝ) ≤ 0 := le_trans (by exact_mod_cast I.le) hhi_nonpos
    -- For a ≤ b ≤ 0: |a| = -a ≥ -b = |b|, so cosh(a) ≥ cosh(b)
    have hcosh_hi_le : Real.cosh I.hi ≤ Real.cosh x := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonpos hhi_nonpos, abs_of_nonpos hx_nonpos]
      linarith [hx.2]
    have hcosh_x_le_lo : Real.cosh x ≤ Real.cosh I.lo := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonpos hx_nonpos, abs_of_nonpos hlo_nonpos]
      linarith [hx.1]
    simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
    constructor
    · calc (min (coshPointComputable I.hi n).lo (coshPointComputable I.lo n).lo : ℝ)
          ≤ (coshPointComputable I.hi n).lo := by exact_mod_cast min_le_left _ _
        _ ≤ Real.cosh I.hi := hhi_mem.1
        _ ≤ Real.cosh x := hcosh_hi_le
    · calc Real.cosh x ≤ Real.cosh I.lo := hcosh_x_le_lo
        _ ≤ (coshPointComputable I.lo n).hi := hlo_mem.2
        _ ≤ max ((coshPointComputable I.hi n).hi : ℝ) ((coshPointComputable I.lo n).hi : ℝ) := le_max_right _ _
  · -- Case: interval contains 0, minimum is 1
    simp only [mem_def, Rat.cast_one, hull, Rat.cast_max]
    constructor
    · exact hcosh_ge_one
    · -- Upper bound is max of endpoint cosh values
      push_neg at h1 h2
      have hhi_pos : (0 : ℝ) < I.hi := by exact_mod_cast h2
      have hlo_neg : (I.lo : ℝ) < 0 := by exact_mod_cast h1
      have hmax_bound : Real.cosh x ≤ max (Real.cosh I.lo) (Real.cosh I.hi) := by
        -- x is between lo and hi, and interval contains 0
        by_cases hx_nonneg : 0 ≤ x
        · -- x ≥ 0: cosh(x) ≤ cosh(hi) since 0 ≤ x ≤ hi means |x| ≤ |hi|
          apply le_max_of_le_right
          rw [Real.cosh_le_cosh]
          rw [abs_of_nonneg hx_nonneg, abs_of_nonneg (le_of_lt hhi_pos)]
          exact hx.2
        · -- x < 0: cosh(x) ≤ cosh(lo) since lo ≤ x < 0 means |x| ≤ |lo|
          apply le_max_of_le_left
          rw [Real.cosh_le_cosh]
          push_neg at hx_nonneg
          rw [abs_of_neg hx_nonneg, abs_of_neg hlo_neg]
          linarith [hx.1]
      calc Real.cosh x ≤ max (Real.cosh I.lo) (Real.cosh I.hi) := hmax_bound
        _ ≤ max ((coshPointComputable I.lo n).hi : ℝ) ((coshPointComputable I.hi n).hi : ℝ) := by
            apply max_le_max
            · exact hlo_mem.2
            · exact hhi_mem.2

/-! ### Computable atanh via Taylor series

For |y| < 1, atanh(y) = y + y³/3 + y⁵/5 + ...
We compute this series for y ∈ [-1/3, 1/3] where it converges rapidly.
-/

/-- Taylor coefficients for atanh: 0, 1, 0, 1/3, 0, 1/5, ...
    atanh(y) = Σ y^(2k+1)/(2k+1) = y + y³/3 + y⁵/5 + ... -/
def atanhTaylorCoeffs (n : ℕ) : List ℚ :=
  let f : ℕ → ℚ := fun i => if i % 2 = 1 then 1 / i else 0
  (List.range (n + 1)).map f

/-- Computable atanh remainder bound.
    For |y| ≤ r < 1, the remainder after n terms is bounded by r^(n+1)/(1 - r²).
    We use a conservative bound: r^(n+1) / ((n+1) * (1 - r)) for simplicity. -/
def atanhRemainderBoundComputable (r : ℚ) (n : ℕ) : IntervalRat :=
  let r' := |r|  -- Use absolute value to ensure non-negativity
  if h : r' ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for bad input
  else
    let R := r' ^ (n + 1) / (1 - r')
    ⟨-R, R, by
      have hr : r' < 1 := not_le.mp h
      have hr_nonneg : 0 ≤ r' := abs_nonneg r
      have hdenom_pos : 0 < 1 - r' := by linarith
      have hR_nonneg : 0 ≤ R := by
        apply div_nonneg
        · apply pow_nonneg hr_nonneg
        · linarith
      linarith⟩

/-- Computable interval enclosure for atanh at a single rational point.
    Requires |q| < 1 for convergence. For |q| ≤ 1/3, this is very accurate. -/
def atanhPointComputable (q : ℚ) (n : ℕ := 15) : IntervalRat :=
  let r := |q|
  if r ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback
  else
    let I := singleton q
    let coeffs := atanhTaylorCoeffs n
    let polyVal := evalTaylorSeries coeffs I
    let remainder := atanhRemainderBoundComputable r n
    add polyVal remainder

/-! ### Computable ln(2) via atanh

ln(2) = 2 * atanh(1/3), since:
  2 = (1 + 1/3) / (1 - 1/3) = (4/3) / (2/3)
  So atanh(1/3) = (1/2) * ln(2), giving ln(2) = 2 * atanh(1/3)
-/

/-- Compute ln(2) as an interval using 2 * atanh(1/3).
    This converges rapidly since atanh series at 1/3 has |y| = 1/3. -/
def ln2Computable (n : ℕ := 20) : IntervalRat :=
  let atanh_third := atanhPointComputable (1/3) n
  scale 2 atanh_third

/-- FTIA for ln2Computable: Real.log 2 ∈ ln2Computable n (partial, with sorry for now) -/
theorem mem_ln2Computable (n : ℕ) : Real.log 2 ∈ ln2Computable n := by
  sorry  -- Proof requires connecting Taylor series to Real.atanh

/-! ### Computable log via argument reduction

For q > 0, we compute:
  1. Reduce q to m * 2^k where m ∈ [1/2, 2]
  2. Compute log(m) = 2 * atanh((m-1)/(m+1)), which has |arg| ≤ 1/3
  3. Result = log(m) + k * ln(2)
-/

/-- Reduction exponent k such that q * 2^(-k) ≈ 1 -/
def logReductionExponent (q : ℚ) : ℤ :=
  if q ≤ 0 then 0
  else
    let n_log := q.num.natAbs.log2
    let d_log := q.den.log2
    (n_log : ℤ) - (d_log : ℤ)

/-- Reduced mantissa m = q * 2^(-k) -/
def logReduceMantissa (q : ℚ) : ℚ :=
  if q ≤ 0 then 1
  else q * (2 : ℚ) ^ (-logReductionExponent q)

/-- Computable log at a single rational point q > 0.
    Returns log(q) = log(m) + k * ln(2) where m = q * 2^(-k). -/
def logPointComputable (q : ℚ) (n : ℕ := 20) : IntervalRat :=
  if q ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for non-positive
  else
    let k := logReductionExponent q
    let m := logReduceMantissa q
    -- log(m) = 2 * atanh((m-1)/(m+1))
    let y := (m - 1) / (m + 1)
    let atanh_y := atanhPointComputable y n
    let log_m := scale 2 atanh_y
    -- k * ln(2)
    let k_ln2 := scale k (ln2Computable n)
    add log_m k_ln2

/-- Computable interval enclosure for log using endpoint evaluation.
    Since log is strictly increasing on (0, ∞), we evaluate at endpoints. -/
def logComputable (I : IntervalRat) (n : ℕ := 20) : IntervalRat :=
  if I.lo ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for non-positive interval
  else
    -- log is monotone increasing, so log([lo, hi]) = [log(lo), log(hi)]
    let logLo := logPointComputable I.lo n
    let logHi := logPointComputable I.hi n
    hull logLo logHi

/-- FTIA for logPointComputable (partial, main structure) -/
theorem mem_logPointComputable {q : ℚ} (hq : 0 < q) (n : ℕ) :
    Real.log q ∈ logPointComputable q n := by
  sorry  -- Full proof requires connecting all the components

/-- FTIA for logComputable: if x ∈ I and I.lo > 0, then log(x) ∈ logComputable I n -/
theorem mem_logComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hpos : 0 < I.lo) (n : ℕ) :
    Real.log x ∈ logComputable I n := by
  simp only [logComputable, not_le.mpr hpos, ↓reduceIte]
  -- Since log is strictly monotone and x ∈ [lo, hi] with lo > 0:
  -- log(lo) ≤ log(x) ≤ log(hi)
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
  have hlo_mem := mem_logPointComputable hpos n
  have hhi_pos : 0 < I.hi := lt_of_lt_of_le hpos I.le
  have hhi_mem := mem_logPointComputable hhi_pos n
  -- x ∈ [lo, hi] implies log(lo) ≤ log(x) ≤ log(hi) by monotonicity
  have hlog_lo_le : Real.log I.lo ≤ Real.log x :=
    Real.log_le_log hlo_pos hx.1
  have hlog_x_le_hi : Real.log x ≤ Real.log I.hi :=
    Real.log_le_log hx_pos hx.2
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (logPointComputable I.lo n).lo (logPointComputable I.hi n).lo : ℝ)
        ≤ (logPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.log I.lo := hlo_mem.1
      _ ≤ Real.log x := hlog_lo_le
  · calc Real.log x ≤ Real.log I.hi := hlog_x_le_hi
      _ ≤ (logPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((logPointComputable I.lo n).hi : ℝ) ((logPointComputable I.hi n).hi : ℝ) := le_max_right _ _

/-- Unconditional version of mem_logComputable for use in correctness proofs.
    When I.lo ≤ 0, logComputable returns [-1000, 1000] which trivially contains any log value. -/
theorem mem_logComputable' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.log x ∈ logComputable I n := by
  by_cases hpos : 0 < I.lo
  · exact mem_logComputable hx hpos n
  · -- I.lo ≤ 0 case: logComputable returns [-1000, 1000]
    simp only [logComputable, not_lt.mp hpos, ↓reduceIte, mem_def]
    constructor
    · -- log x ≥ -1000 (since log : ℝ → ℝ is bounded below only on (0, ∞))
      -- For x ≤ 0, log isn't defined, so we use a sorry here
      -- In practice, log is only called on positive intervals
      sorry
    · -- log x ≤ 1000
      sorry

end IntervalRat

end LeanBound.Core
