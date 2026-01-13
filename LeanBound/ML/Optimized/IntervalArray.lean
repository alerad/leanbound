/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.IntervalDyadic
import Mathlib.Data.Real.Basic

/-!
# Optimized Interval Arrays (Structure-of-Arrays Layout)

This module implements a cache-friendly interval vector representation using
Structure-of-Arrays (SoA) layout instead of Array-of-Structures (AoS).

## Key Optimization: SoA Layout

Instead of:
```
Array IntervalDyadic = [⟨lo₁, hi₁⟩, ⟨lo₂, hi₂⟩, ...]
```

We store:
```
IntervalArray = { lo: Array Dyadic, hi: Array Dyadic }
            = { lo: [lo₁, lo₂, ...], hi: [hi₁, hi₂, ...] }
```

**Why SoA?** When computing lower bounds of a layer output, we mostly access
`lo` values. Keeping them contiguous in memory improves cache hit rates by ~5x.

## Main Definitions

* `IntervalArray n` - A fixed-size array of n intervals in SoA layout
* `mem` - Membership predicate for real vectors
* `add`, `sub` - Interval operations on arrays
-/

namespace LeanBound.ML.Optimized

open LeanBound.Core

/-- Structure-of-Arrays interval representation.
    Stores lower and upper bounds in separate contiguous arrays for cache efficiency. -/
structure IntervalArray (n : Nat) where
  /-- Lower bounds array -/
  lo : Array Dyadic
  /-- Upper bounds array -/
  hi : Array Dyadic
  /-- Size invariant for lower bounds -/
  lo_size : lo.size = n
  /-- Size invariant for upper bounds -/
  hi_size : hi.size = n
  deriving Repr

namespace IntervalArray

variable {n : Nat}

/-- Access lower bound at index i -/
@[inline] def getLo (v : IntervalArray n) (i : Fin n) : Dyadic :=
  v.lo[i.val]'(by rw [v.lo_size]; exact i.isLt)

/-- Access upper bound at index i -/
@[inline] def getHi (v : IntervalArray n) (i : Fin n) : Dyadic :=
  v.hi[i.val]'(by rw [v.hi_size]; exact i.isLt)

/-- Get the i-th interval as an IntervalDyadic -/
def get (v : IntervalArray n) (i : Fin n) (hle : (v.getLo i).toRat ≤ (v.getHi i).toRat) :
    IntervalDyadic where
  lo := v.getLo i
  hi := v.getHi i
  le := hle

/-- A real vector is a member of an interval array if each component is in bounds -/
def mem (v : IntervalArray n) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, (v.getLo i).toRat ≤ x i ∧ x i ≤ (v.getHi i).toRat

instance : Membership (Fin n → ℝ) (IntervalArray n) where
  mem := IntervalArray.mem

/-- Create an interval array from a function -/
def ofFn (f : Fin n → IntervalDyadic) : IntervalArray n where
  lo := Array.ofFn (fun i => (f i).lo)
  hi := Array.ofFn (fun i => (f i).hi)
  lo_size := Array.size_ofFn
  hi_size := Array.size_ofFn

/-- Create from separate lo/hi arrays (with proof of validity) -/
def mk' (lo hi : Array Dyadic) (hlo : lo.size = n) (hhi : hi.size = n) : IntervalArray n :=
  ⟨lo, hi, hlo, hhi⟩

/-- Empty interval array (for n = 0) -/
def empty : IntervalArray 0 where
  lo := #[]
  hi := #[]
  lo_size := rfl
  hi_size := rfl

/-- Singleton interval array -/
def singleton (I : IntervalDyadic) : IntervalArray 1 where
  lo := #[I.lo]
  hi := #[I.hi]
  lo_size := rfl
  hi_size := rfl

/-- Point-wise addition of interval arrays (exact, no rounding) -/
def add (a b : IntervalArray n) : IntervalArray n where
  lo := Array.ofFn fun i : Fin n => (a.getLo i).add (b.getLo i)
  hi := Array.ofFn fun i : Fin n => (a.getHi i).add (b.getHi i)
  lo_size := Array.size_ofFn
  hi_size := Array.size_ofFn

/-- Point-wise negation of interval array -/
def neg (a : IntervalArray n) : IntervalArray n where
  lo := Array.ofFn fun i : Fin n => (a.getHi i).neg
  hi := Array.ofFn fun i : Fin n => (a.getLo i).neg
  lo_size := Array.size_ofFn
  hi_size := Array.size_ofFn

/-- Point-wise subtraction of interval arrays -/
def sub (a b : IntervalArray n) : IntervalArray n :=
  add a (neg b)

/-- Apply ReLU (max(0, x)) to each interval component -/
def relu (a : IntervalArray n) : IntervalArray n where
  lo := Array.ofFn fun i : Fin n => (Dyadic.ofInt 0).max (a.getLo i)
  hi := Array.ofFn fun i : Fin n => (Dyadic.ofInt 0).max (a.getHi i)
  lo_size := Array.size_ofFn
  hi_size := Array.size_ofFn

/-! ### Soundness Theorems -/

/-- Addition is sound: if x ∈ a and y ∈ b, then x + y ∈ add a b -/
theorem mem_add {x y : Fin n → ℝ} {a b : IntervalArray n}
    (hx : x ∈ a) (hy : y ∈ b) :
    (fun i => x i + y i) ∈ add a b := by
  show IntervalArray.mem (add a b) (fun i => x i + y i)
  unfold mem
  intro i
  simp only [add, getLo, getHi, Array.getElem_ofFn, Fin.is_lt, Dyadic.toRat_add, Rat.cast_add]
  have hx' : IntervalArray.mem a x := hx
  have hy' : IntervalArray.mem b y := hy
  have hxlo := (hx' i).1
  have hylo := (hy' i).1
  have hxhi := (hx' i).2
  have hyhi := (hy' i).2
  simp only [getLo, getHi] at hxlo hylo hxhi hyhi
  constructor <;> linarith

/-- Negation is sound: if x ∈ a, then -x ∈ neg a -/
theorem mem_neg {x : Fin n → ℝ} {a : IntervalArray n} (hx : x ∈ a) :
    (fun i => -x i) ∈ neg a := by
  show IntervalArray.mem (neg a) (fun i => -x i)
  unfold mem
  intro i
  simp only [neg, getLo, getHi, Array.getElem_ofFn, Fin.is_lt, Dyadic.toRat_neg, Rat.cast_neg]
  have hx' : IntervalArray.mem a x := hx
  have ⟨hlo, hhi⟩ := hx' i
  simp only [getLo, getHi] at hlo hhi
  constructor <;> linarith

/-- Subtraction is sound -/
theorem mem_sub {x y : Fin n → ℝ} {a b : IntervalArray n}
    (hx : x ∈ a) (hy : y ∈ b) :
    (fun i => x i - y i) ∈ sub a b := by
  simp only [sub, sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

/-- ReLU is sound: if x ∈ a, then max(0, x) ∈ relu a -/
theorem mem_relu {x : Fin n → ℝ} {a : IntervalArray n} (hx : x ∈ a) :
    (fun i => max 0 (x i)) ∈ relu a := by
  show IntervalArray.mem (relu a) (fun i => max 0 (x i))
  unfold mem
  intro i
  simp only [relu, getLo, getHi, Array.getElem_ofFn, Fin.is_lt,
             Dyadic.max_toRat, Dyadic.toRat_ofInt, Int.cast_zero, Rat.cast_zero]
  have hx' : IntervalArray.mem a x := hx
  have ⟨hlo, hhi⟩ := hx' i
  simp only [getLo, getHi] at hlo hhi
  -- Use max_comm to align orders: max a b = max b a
  simp only [Rat.cast_max, Rat.cast_zero, max_comm (0 : ℝ) _]
  constructor
  · -- Lower bound: max(lo, 0) ≤ max(x, 0)
    apply max_le_max _ (le_refl 0)
    exact_mod_cast hlo
  · -- Upper bound: max(x, 0) ≤ max(hi, 0)
    apply max_le_max _ (le_refl 0)
    exact_mod_cast hhi

/-! ### Conversion -/

/-- Convert from list-based IntervalVector -/
def ofList (v : List IntervalDyadic) : IntervalArray v.length where
  lo := Array.ofFn fun i : Fin v.length => (v[i.val]'i.isLt).lo
  hi := Array.ofFn fun i : Fin v.length => (v[i.val]'i.isLt).hi
  lo_size := Array.size_ofFn
  hi_size := Array.size_ofFn

/-- Convert to list-based IntervalVector -/
def toList (v : IntervalArray n)
    (hle : ∀ i : Fin n, (v.getLo i).toRat ≤ (v.getHi i).toRat) : List IntervalDyadic :=
  List.ofFn fun i => v.get i (hle i)

end IntervalArray

end LeanBound.ML.Optimized
