/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Dyadic
import LeanBound.Core.IntervalReal
import Mathlib.Data.Rat.Cast.Order

/-!
# Dyadic Intervals

Intervals with Dyadic endpoints. These support "Outward Rounding", ensuring
mathematical soundness even when we limit numerical precision.

## Main definitions

* `IntervalDyadic` - Interval with Dyadic endpoints
* `IntervalDyadic.add`, `mul`, `neg` - Interval arithmetic operations
* `IntervalDyadic.roundOut` - Outward rounding to control precision
* `IntervalDyadic.toIntervalRat` - Convert to rational interval for verification

## Design notes

The key feature is `roundOut`: after each operation, we can enforce a minimum
exponent to prevent precision explosion. When rounding:
- Lower bounds are shifted down (toward -∞)
- Upper bounds are shifted up (toward +∞)

This maintains the containment invariant: the rounded interval always contains
the original interval, which contains the true mathematical value.

## Performance

In v1.0, `Rat` multiplication of `1/3 * 1/3 * ... * 1/3` (10 times) creates
a denominator of 3^10 = 59049. Each operation requires GCD computation.

In v1.1, with `precision = -10`, the denominator stays fixed at 2^10 = 1024.
The result is slightly less tight but computed significantly faster.
-/

namespace LeanBound.Core

/-- An interval with Dyadic endpoints.

Maintains invariant: `lo.toRat ≤ hi.toRat` -/
structure IntervalDyadic where
  /-- Lower bound -/
  lo : Dyadic
  /-- Upper bound -/
  hi : Dyadic
  /-- Invariant: lower bound ≤ upper bound -/
  le : lo.toRat ≤ hi.toRat
  deriving Repr

namespace IntervalDyadic

/-! ### Membership and Sets -/

/-- The set of reals contained in this interval -/
def toSet (I : IntervalDyadic) : Set ℝ := Set.Icc (I.lo : ℝ) (I.hi : ℝ)

/-- Membership in a Dyadic interval -/
instance : Membership ℝ IntervalDyadic where
  mem I x := (I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ)

@[simp]
theorem mem_def (x : ℝ) (I : IntervalDyadic) :
    x ∈ I ↔ (I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ) := Iff.rfl

/-! ### Conversion to IntervalRat -/

/-- Convert to IntervalRat for verification with existing theorems -/
def toIntervalRat (I : IntervalDyadic) : IntervalRat :=
  ⟨I.lo.toRat, I.hi.toRat, I.le⟩

/-- Membership is preserved by conversion to IntervalRat -/
theorem mem_toIntervalRat {x : ℝ} {I : IntervalDyadic} :
    x ∈ I ↔ x ∈ I.toIntervalRat := by
  simp only [mem_def, toIntervalRat, IntervalRat.mem_def]

/-! ### Construction -/

/-- Create a singleton interval from a Dyadic -/
def singleton (d : Dyadic) : IntervalDyadic := ⟨d, d, le_refl _⟩

/-- A Dyadic value is in its singleton interval -/
theorem mem_singleton (d : Dyadic) : (d.toRat : ℝ) ∈ singleton d := by
  simp only [mem_def, singleton]
  exact ⟨le_refl _, le_refl _⟩

/-- Default interval [0, 0] -/
instance : Inhabited IntervalDyadic where
  default := singleton Dyadic.zero

/-- Create an interval, checking the invariant -/
def mk? (lo hi : Dyadic) : Option IntervalDyadic :=
  if h : lo.toRat ≤ hi.toRat then some ⟨lo, hi, h⟩ else none

/-- The width of an interval -/
def width (I : IntervalDyadic) : Dyadic := I.hi.sub I.lo

/-- Midpoint of an interval (approximate, using larger exponent) -/
def midpoint (I : IntervalDyadic) : Dyadic :=
  let sum := I.lo.add I.hi
  ⟨sum.mantissa >>> 1, sum.exponent⟩  -- Divide by 2

/-! ### Outward Rounding -/

/-- Outward rounding: enforces a maximum precision (minimum exponent).

This is the key operation for preventing precision explosion.
`minExp` is the minimum allowed exponent (higher = coarser precision).

For example, `minExp = -10` ensures all values are multiples of 2^(-10) ≈ 0.001.
-/
def roundOut (I : IntervalDyadic) (minExp : Int) : IntervalDyadic :=
  let newLo := I.lo.shiftDown minExp
  let newHi := I.hi.shiftUp minExp
  ⟨newLo, newHi, by
    -- Proof: newLo ≤ I.lo ≤ I.hi ≤ newHi
    have h1 : newLo.toRat ≤ I.lo.toRat := Dyadic.toRat_shiftDown_le I.lo minExp
    have h2 : I.lo.toRat ≤ I.hi.toRat := I.le
    have h3 : I.hi.toRat ≤ newHi.toRat := Dyadic.toRat_shiftUp_ge I.hi minExp
    linarith⟩

/-- roundOut produces an interval containing the original -/
theorem roundOut_contains {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (minExp : Int) :
    x ∈ I.roundOut minExp := by
  simp only [mem_def] at *
  constructor
  · have h := Dyadic.toRat_shiftDown_le I.lo minExp
    have h' : ((I.lo.shiftDown minExp).toRat : ℝ) ≤ (I.lo.toRat : ℝ) := by exact_mod_cast h
    calc ((I.roundOut minExp).lo.toRat : ℝ) = ((I.lo.shiftDown minExp).toRat : ℝ) := by rfl
      _ ≤ (I.lo.toRat : ℝ) := h'
      _ ≤ x := hx.1
  · have h := Dyadic.toRat_shiftUp_ge I.hi minExp
    have h' : (I.hi.toRat : ℝ) ≤ ((I.hi.shiftUp minExp).toRat : ℝ) := by exact_mod_cast h
    calc x ≤ (I.hi.toRat : ℝ) := hx.2
      _ ≤ ((I.hi.shiftUp minExp).toRat : ℝ) := h'
      _ = ((I.roundOut minExp).hi.toRat : ℝ) := by rfl

/-! ### Interval Negation -/

/-- Negate an interval -/
def neg (I : IntervalDyadic) : IntervalDyadic where
  lo := I.hi.neg
  hi := I.lo.neg
  le := by
    simp only [Dyadic.toRat_neg]
    linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg, Dyadic.toRat_neg, Rat.cast_neg]
  constructor <;> linarith

/-! ### Interval Addition -/

/-- Add two intervals -/
def add (I J : IntervalDyadic) : IntervalDyadic where
  lo := I.lo.add J.lo
  hi := I.hi.add J.hi
  le := by
    simp only [Dyadic.toRat_add]
    linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add, Dyadic.toRat_add, Rat.cast_add]
  constructor <;> linarith

/-- Add with precision control -/
def addRounded (I J : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  (add I J).roundOut prec

/-! ### Interval Subtraction -/

/-- Subtract two intervals -/
def sub (I J : IntervalDyadic) : IntervalDyadic := add I (neg J)

/-- FTIA for subtraction -/
theorem mem_sub {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x - y ∈ sub I J := by
  simp only [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

/-! ### Interval Multiplication -/

/-- Multiply two intervals.

Uses min/max of all four endpoint products to handle signs correctly.
This is the exact multiplication - mantissas may grow. Use `mulRounded` or
`mulNormalized` for controlled precision.

Correctness: For x ∈ [a,b] and y ∈ [c,d], the product x*y lies in the interval
[min(ac,ad,bc,bd), max(ac,ad,bc,bd)]. -/
def mul (I J : IntervalDyadic) : IntervalDyadic :=
  let v1 := I.lo.mul J.lo
  let v2 := I.lo.mul J.hi
  let v3 := I.hi.mul J.lo
  let v4 := I.hi.mul J.hi
  ⟨Dyadic.min4 v1 v2 v3 v4, Dyadic.max4 v1 v2 v3 v4, Dyadic.min4_le_max4 v1 v2 v3 v4⟩

/-- FTIA for multiplication -/
theorem mem_mul {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mul I J := by
  -- Use IntervalRat.mem_mul and translate the bounds
  have hxI := mem_toIntervalRat.mp hx
  have hyJ := mem_toIntervalRat.mp hy
  have hmul := IntervalRat.mem_mul hxI hyJ
  simp only [mem_def, mul] at *
  -- hmul has bounds from IntervalRat.mul which are min/max of 4 products
  -- Our Dyadic.min4/max4 has the same structure with toRat preserving the products
  constructor
  · -- Lower bound: Dyadic.min4.toRat equals the rational min4 from hmul
    simp only [IntervalRat.mem_def, IntervalRat.mul, toIntervalRat] at hmul
    have heq : (Dyadic.min4 (I.lo.mul J.lo) (I.lo.mul J.hi) (I.hi.mul J.lo) (I.hi.mul J.hi)).toRat
        = min (min (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat))
              (min (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat)) := by
      simp only [Dyadic.min4, Dyadic.toRat_mul, Dyadic.min_toRat]
    rw [heq]
    exact_mod_cast hmul.1
  · -- Upper bound: Dyadic.max4.toRat equals the rational max4 from hmul
    simp only [IntervalRat.mem_def, IntervalRat.mul, toIntervalRat] at hmul
    have heq : (Dyadic.max4 (I.lo.mul J.lo) (I.lo.mul J.hi) (I.hi.mul J.lo) (I.hi.mul J.hi)).toRat
        = max (max (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat))
              (max (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat)) := by
      simp only [Dyadic.max4, Dyadic.toRat_mul, Dyadic.max_toRat]
    rw [heq]
    exact_mod_cast hmul.2

/-- Multiply with precision control (outward rounding) -/
def mulRounded (I J : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  (mul I J).roundOut prec

/-- Multiply with mantissa normalization (prevents bit explosion) -/
def mulNormalized (I J : IntervalDyadic) (maxBits : Nat := 256) : IntervalDyadic :=
  let result := mul I J
  ⟨result.lo.normalizeDown maxBits, result.hi.normalizeUp maxBits, by
    -- Normalization preserves ordering: lo.normalizeDown ≤ lo ≤ hi ≤ hi.normalizeUp
    calc (result.lo.normalizeDown maxBits).toRat
        ≤ result.lo.toRat := Dyadic.toRat_normalizeDown_le _ _
      _ ≤ result.hi.toRat := result.le
      _ ≤ (result.hi.normalizeUp maxBits).toRat := Dyadic.toRat_normalizeUp_ge _ _⟩

/-! ### Interval Scaling -/

/-- Scale an interval by a constant Dyadic -/
def scale (I : IntervalDyadic) (c : Dyadic) : IntervalDyadic :=
  if hc : Dyadic.le Dyadic.zero c then
    ⟨I.lo.mul c, I.hi.mul c, by
      rw [Dyadic.toRat_mul, Dyadic.toRat_mul]
      have hcnn : 0 ≤ c.toRat := by
        have := Dyadic.le_iff_toRat_le Dyadic.zero c |>.mp hc
        have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
        rw [hz] at this; exact this
      exact mul_le_mul_of_nonneg_right I.le hcnn⟩
  else
    ⟨I.hi.mul c, I.lo.mul c, by
      rw [Dyadic.toRat_mul, Dyadic.toRat_mul]
      have hcneg : c.toRat < 0 := by
        have hf := Dyadic.le_iff_toRat_le Dyadic.zero c
        have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
        rw [hz] at hf
        by_contra hge
        push_neg at hge
        exact hc (hf.mpr hge)
      exact mul_le_mul_of_nonpos_right I.le (le_of_lt hcneg)⟩

/-- Scale by a power of 2 (very efficient: just adjusts exponents) -/
def scale2 (I : IntervalDyadic) (n : Int) : IntervalDyadic :=
  ⟨I.lo.scale2 n, I.hi.scale2 n, Dyadic.toRat_scale2_le_scale2 I.lo I.hi n I.le⟩

/-! ### Comparison and Containment -/

/-- Check if interval contains zero -/
def containsZero (I : IntervalDyadic) : Bool :=
  Dyadic.le I.lo Dyadic.zero && Dyadic.le Dyadic.zero I.hi

/-- Check if entire interval is positive -/
def isPositive (I : IntervalDyadic) : Bool :=
  Dyadic.lt Dyadic.zero I.lo

/-- Check if entire interval is negative -/
def isNegative (I : IntervalDyadic) : Bool :=
  Dyadic.lt I.hi Dyadic.zero

/-- Check if I ⊆ J -/
def subset (I J : IntervalDyadic) : Bool :=
  Dyadic.le J.lo I.lo && Dyadic.le I.hi J.hi

/-- Check if the upper bound is ≤ a rational -/
def upperBoundedBy (I : IntervalDyadic) (q : ℚ) : Bool :=
  I.hi.toRat ≤ q

/-- Check if a rational is ≤ the lower bound -/
def lowerBoundedBy (I : IntervalDyadic) (q : ℚ) : Bool :=
  q ≤ I.lo.toRat

/-! ### Helper for Transcendentals -/

/-- Convert from IntervalRat (for transcendental results) -/
def ofIntervalRat (I : IntervalRat) (prec : Int := -53) : IntervalDyadic :=
  -- Convert Rat endpoints to Dyadic with outward rounding
  -- For simplicity, we use a conservative conversion
  let lo := Dyadic.ofInt (Int.floor (I.lo * (2 ^ (-prec).toNat)))
  let loD := lo.scale2 prec
  let hi := Dyadic.ofInt (Int.ceil (I.hi * (2 ^ (-prec).toNat)))
  let hiD := hi.scale2 prec
  ⟨loD, hiD, by
    -- Need: loD.toRat ≤ hiD.toRat
    -- loD.toRat = floor(I.lo * 2^n) * 2^prec
    -- hiD.toRat = ceil(I.hi * 2^n) * 2^prec
    -- This follows from: floor(I.lo * 2^n) ≤ ceil(I.hi * 2^n)
    -- Which is: floor(I.lo * 2^n) ≤ I.lo * 2^n ≤ I.hi * 2^n ≤ ceil(I.hi * 2^n)
    apply Dyadic.toRat_scale2_le_scale2
    rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    have hle : I.lo ≤ I.hi := I.le
    have hscale_pos : (0 : ℚ) < (2 : ℚ) ^ (-prec).toNat := pow_pos (by norm_num : (0 : ℚ) < 2) _
    calc (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ)
        ≤ I.lo * (2 : ℚ) ^ (-prec).toNat := Int.floor_le _
      _ ≤ I.hi * (2 : ℚ) ^ (-prec).toNat := mul_le_mul_of_nonneg_right hle (le_of_lt hscale_pos)
      _ ≤ ⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ := Int.le_ceil _⟩

/-- If x ∈ IntervalRat I, then x ∈ ofIntervalRat I prec (outward rounding preserves membership).
    Requires precision ≤ 0 (e.g. -53). -/
theorem mem_ofIntervalRat {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (prec : Int)
    (hprec : prec ≤ 0 := by norm_num) :
    x ∈ ofIntervalRat I prec := by
  -- The conversion uses floor/ceil which provides outward rounding:
  -- floor(lo * 2^n) * 2^(-n) ≤ lo ≤ x ≤ hi ≤ ceil(hi * 2^n) * 2^(-n)
  -- This follows from floor(a) ≤ a and a ≤ ceil(a), combined with
  -- the fact that multiplying by 2^(-n) when prec = -n cancels the 2^n factor.
  simp only [mem_def, ofIntervalRat, IntervalRat.mem_def] at *
  have h2n_pos : (0 : ℚ) < (2 : ℚ) ^ (-prec).toNat := pow_pos (by norm_num) _
  have hfloor : (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) ≤ I.lo * (2 : ℚ) ^ (-prec).toNat := Int.floor_le _
  have hceil : I.hi * (2 : ℚ) ^ (-prec).toNat ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) := Int.le_ceil _
  have hzpow_pos : (0 : ℚ) < (2 : ℚ) ^ prec := zpow_pos (by norm_num) _
  -- Key: 2^(-prec).toNat * 2^prec = 1 when prec ≤ 0 (so (-prec).toNat = -prec)
  have hcancel : (2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec = 1 := by
    set n := (-prec).toNat with hn_def
    have hprec_eq : prec = -(n : ℤ) := by omega
    rw [hprec_eq, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (ne_of_gt h2n_pos)
  constructor
  · -- Lower bound
    rw [Dyadic.toRat_scale2, Dyadic.toRat_ofInt]
    have hle : (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) * (2 : ℚ) ^ prec ≤ I.lo := by
      calc (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) * (2 : ℚ) ^ prec
          ≤ (I.lo * (2 : ℚ) ^ (-prec).toNat) * (2 : ℚ) ^ prec := by
            apply mul_le_mul_of_nonneg_right hfloor (le_of_lt hzpow_pos)
        _ = I.lo * ((2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec) := by ring
        _ = I.lo * 1 := by rw [hcancel]
        _ = I.lo := by ring
    exact le_trans (by exact_mod_cast hle) hx.1
  · -- Upper bound
    rw [Dyadic.toRat_scale2, Dyadic.toRat_ofInt]
    have hle : I.hi ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) * (2 : ℚ) ^ prec := by
      calc I.hi = I.hi * 1 := by ring
        _ = I.hi * ((2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec) := by rw [hcancel]
        _ = (I.hi * (2 : ℚ) ^ (-prec).toNat) * (2 : ℚ) ^ prec := by ring
        _ ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) * (2 : ℚ) ^ prec := by
            apply mul_le_mul_of_nonneg_right hceil (le_of_lt hzpow_pos)
    exact le_trans hx.2 (by exact_mod_cast hle)

end IntervalDyadic
end LeanBound.Core
