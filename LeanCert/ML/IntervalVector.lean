/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalVector

/-!
# ML-Specific Interval Operations

This file provides activation functions for neural network interval propagation,
building on the general interval vector operations from `Engine.IntervalVector`.

## Main definitions

* `relu` - ReLU activation for intervals
* `sigmoid` - Sigmoid activation (conservative [0, 1] bound)
* `reluVector` - Apply ReLU to each component
* `sigmoidVector` - Apply sigmoid to each component

## Main theorems

* `mem_relu` - Soundness of ReLU
* `mem_sigmoid` - Soundness of sigmoid
-/

namespace LeanCert.ML

open LeanCert.Core
open LeanCert.Engine

-- Re-export IntervalVector from Numerics for convenience
export LeanCert.Engine (
  IntervalVector
)

export LeanCert.Engine.IntervalVector (
  scalarMulInterval
  mem_scalarMulInterval
  dotProduct
  realDotProduct
  mem_dotProduct
  add
  mem_add_component
  zero
  mem_zero
  matVecMul
  realMatVecMul
  mem_matVecMul
  addBias
  realAddBias
  mem_addBias
)

namespace IntervalVector

/-! ### ReLU Activation -/

/-- ReLU applied to an interval: max(0, x) for all x in the interval.
    Returns [max(0, lo), max(0, hi)] -/
def relu (I : IntervalDyadic) : IntervalDyadic where
  lo := Dyadic.max (Core.Dyadic.ofInt 0) I.lo
  hi := Dyadic.max (Core.Dyadic.ofInt 0) I.hi
  le := by
    simp only [Dyadic.max_toRat, Dyadic.toRat_ofInt, Int.cast_zero]
    exact max_le_max (le_refl (0 : ℚ)) I.le

/-- Soundness of ReLU: if x ∈ I, then max(0, x) ∈ relu I -/
theorem mem_relu {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    max 0 x ∈ relu I := by
  simp only [IntervalDyadic.mem_def, relu] at *
  simp only [Dyadic.max_toRat, Dyadic.toRat_ofInt, Int.cast_zero]
  constructor
  · -- Lower bound: (max 0 lo : ℚ) ≤ max 0 x
    -- We have lo ≤ x (as reals), need max(0,lo) ≤ max(0,x)
    have hlo := hx.1  -- (I.lo.toRat : ℝ) ≤ x
    -- max is monotone in both arguments
    calc (↑(max (0 : ℚ) I.lo.toRat) : ℝ)
        = max (0 : ℝ) (I.lo.toRat : ℝ) := by simp [Rat.cast_max]
      _ ≤ max 0 x := max_le_max (le_refl 0) hlo
  · -- Upper bound: max 0 x ≤ (max 0 hi : ℚ)
    have hhi := hx.2  -- x ≤ (I.hi.toRat : ℝ)
    calc max 0 x
        ≤ max (0 : ℝ) (I.hi.toRat : ℝ) := max_le_max (le_refl 0) hhi
      _ = (↑(max (0 : ℚ) I.hi.toRat) : ℝ) := by simp [Rat.cast_max]

/-- Apply ReLU to each component of an interval vector -/
def reluVector (Is : IntervalVector) : IntervalVector :=
  Is.map relu

/-- Soundness of vector ReLU -/
theorem mem_reluVector_component {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    max 0 x ∈ relu I := mem_relu hx

/-! ### Sigmoid Activation -/

/-- Sigmoid interval: conservative bound [0, 1].
    Since sigmoid(x) = 1/(1 + exp(-x)) ∈ (0, 1) for all x,
    [0, 1] is a sound overapproximation for any input interval. -/
def sigmoid (_I : IntervalDyadic) : IntervalDyadic where
  lo := Core.Dyadic.ofInt 0
  hi := Core.Dyadic.ofInt 1
  le := by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num

/-- Real sigmoid function -/
noncomputable def Real.sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- Sigmoid is bounded in (0, 1) -/
theorem Real.sigmoid_pos (x : ℝ) : 0 < Real.sigmoid x := by
  unfold Real.sigmoid
  apply div_pos one_pos
  linarith [Real.exp_pos (-x)]

theorem Real.sigmoid_lt_one (x : ℝ) : Real.sigmoid x < 1 := by
  unfold Real.sigmoid
  rw [div_lt_one (by linarith [Real.exp_pos (-x)] : 0 < 1 + Real.exp (-x))]
  linarith [Real.exp_pos (-x)]

/-- Soundness of sigmoid: sigmoid(x) ∈ [0, 1] for all x -/
theorem mem_sigmoid {x : ℝ} {I : IntervalDyadic} (_hx : x ∈ I) :
    Real.sigmoid x ∈ sigmoid I := by
  simp only [IntervalDyadic.mem_def, sigmoid]
  simp only [Dyadic.toRat_ofInt, Int.cast_zero, Int.cast_one, Rat.cast_zero, Rat.cast_one]
  exact ⟨le_of_lt (Real.sigmoid_pos x), le_of_lt (Real.sigmoid_lt_one x)⟩

/-- Apply sigmoid to each component of an interval vector -/
def sigmoidVector (Is : IntervalVector) : IntervalVector :=
  Is.map sigmoid

end IntervalVector

end LeanCert.ML
