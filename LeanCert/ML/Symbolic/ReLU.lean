/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalDyadic

/-!
# Verified DeepPoly ReLU Relaxation

This module implements the "Triangle Relaxation" for ReLU activation.
This is the mathematical core of Symbolic Interval Propagation (SIP).

## The Dependency Problem

Standard interval arithmetic fails on expressions like `x - x` because it treats
each occurrence of `x` independently, returning `[lo - hi, hi - lo]` instead of `0`.

Symbolic Interval Propagation solves this by tracking variables as linear functions
of the inputs: `xₖ = Σ wᵢ · inputᵢ + b`

## The Geometry

For a neuron with pre-activation bounds `[l, u]`, we bound `ReLU(x) = max(0, x)`
using linear functions:

1. **Lower Linear Bound:**
   - If l ≥ 0: y = x (always active)
   - If u ≤ 0: y = 0 (always inactive)
   - If l < 0 < u: y ≥ 0 (simplest valid choice)

2. **Upper Linear Bound (The DeepPoly Line):**
   - If l < 0 < u: The line passing through (l, 0) and (u, u).
     Slope λ = u / (u - l)
     Equation: y ≤ λ · (x - l)

## Main Results

* `upper_bound_valid` - The triangle upper bound contains ReLU in the crossing case
* `relu_relaxation_sound` - Complete soundness theorem for all cases
-/

namespace LeanCert.ML.Symbolic

open LeanCert.Core

/-- Represents a linear function y = slope · x + bias -/
structure LinearBound where
  slope : ℚ
  bias : ℚ
  deriving Repr, DecidableEq

/-- Evaluate linear bound at x -/
def LinearBound.eval (f : LinearBound) (x : ℝ) : ℝ :=
  (f.slope : ℝ) * x + f.bias

/-- The DeepPoly upper bound line for the crossing case (l < 0 < u).
    Line passing through (l, 0) and (u, u).
    Slope = u / (u - l)
    Using point-slope form at (l, 0): y = slope · (x - l) -/
def crossingUpperBound (l u : ℚ) : LinearBound :=
  let slope := u / (u - l)
  { slope := slope,
    bias := -slope * l }

/-- Key lemma: The crossing upper bound evaluates to slope · (x - l) -/
theorem crossingUpperBound_eval (l u : ℚ) (x : ℝ) (h_ne : u - l ≠ 0) :
    (crossingUpperBound l u).eval x = (u : ℝ) / ((u : ℝ) - l) * (x - l) := by
  simp only [crossingUpperBound, LinearBound.eval]
  have h_ne' : (u : ℝ) - l ≠ 0 := by exact_mod_cast h_ne
  push_cast
  rw [mul_sub_left_distrib]
  field_simp
  ring_nf

/-- The Triangle Theorem: The DeepPoly upper bound contains ReLU.

    For x ∈ [l, u] where l < 0 < u, we prove max(0, x) ≤ λ · (x - l)
    where λ = u / (u - l).

    Geometric intuition: ReLU is convex, and the line connecting
    (l, ReLU(l)) = (l, 0) and (u, ReLU(u)) = (u, u) lies above the graph. -/
theorem upper_bound_valid (l u : ℚ) (x : ℝ)
    (hl : l < 0) (hu : 0 < u) (hx_mem : (l : ℝ) ≤ x ∧ x ≤ u) :
    max 0 x ≤ (crossingUpperBound l u).eval x := by
  -- Key facts
  have h_diff_pos : (0 : ℚ) < u - l := sub_pos.mpr (lt_trans hl hu)
  have h_diff_ne : u - l ≠ 0 := ne_of_gt h_diff_pos
  have h_diff_pos' : (0 : ℝ) < (u : ℝ) - l := by exact_mod_cast h_diff_pos
  have h_slope_pos : (0 : ℝ) < (u : ℝ) / ((u : ℝ) - l) := div_pos (by exact_mod_cast hu) h_diff_pos'

  rw [crossingUpperBound_eval l u x h_diff_ne]

  -- Case split on whether x ≤ 0
  rcases le_or_gt x 0 with hx_neg | hx_pos

  · -- Case 1: x ≤ 0, so max(0, x) = 0
    rw [max_eq_left hx_neg]
    -- Need: 0 ≤ (u/(u-l)) · (x - l)
    -- Since u/(u-l) > 0 and x - l ≥ 0 (as x ≥ l), product is ≥ 0
    apply mul_nonneg (le_of_lt h_slope_pos)
    linarith [hx_mem.1]

  · -- Case 2: x > 0, so max(0, x) = x
    rw [max_eq_right (le_of_lt hx_pos)]
    -- Need: x ≤ (u/(u-l)) · (x - l)
    -- Algebra: x · (u - l) ≤ u · (x - l)
    --          x·u - x·l ≤ u·x - u·l
    --          -x·l ≤ -u·l
    --          u·l ≤ x·l
    --          l·(u - x) ≤ 0  ✓ (since l < 0 and u ≥ x)
    rw [div_mul_eq_mul_div, le_div_iff₀ h_diff_pos']
    have hl' : (l : ℝ) < 0 := by exact_mod_cast hl
    have hu' : (0 : ℝ) < u := by exact_mod_cast hu
    -- Key: x(u-l) ≤ u(x-l) ⟺ l(u-x) ≤ 0
    have key : x * ((u : ℝ) - l) - (u : ℝ) * (x - l) = (l : ℝ) * ((u : ℝ) - x) := by ring
    have h_factor_nonpos : (l : ℝ) * ((u : ℝ) - x) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg (le_of_lt hl')
      linarith [hx_mem.2]
    linarith

/-- The Symbolic Bound structure for a single variable.
    Represents the constraint: lower.eval(x) ≤ y ≤ upper.eval(x) -/
structure SymbolicBound where
  /-- Linear lower bound: y ≥ slope · x + bias -/
  lower : LinearBound
  /-- Linear upper bound: y ≤ slope · x + bias -/
  upper : LinearBound
  deriving Repr, DecidableEq

/-- Compute the verified relaxation for ReLU given concrete bounds [l, u] -/
def getReLURelaxation (l u : ℚ) : SymbolicBound :=
  if 0 ≤ l then
    -- Always active: ReLU(x) = x. Both bounds are y = x.
    { lower := ⟨1, 0⟩, upper := ⟨1, 0⟩ }
  else if u ≤ 0 then
    -- Always inactive: ReLU(x) = 0. Both bounds are y = 0.
    { lower := ⟨0, 0⟩, upper := ⟨0, 0⟩ }
  else
    -- Crossing case: Triangle relaxation
    -- Lower: y ≥ 0 (simplest valid lower bound)
    -- Upper: DeepPoly line through (l, 0) and (u, u)
    { lower := ⟨0, 0⟩,
      upper := crossingUpperBound l u }

/-- Lower bound for crossing case: 0 ≤ max(0, x) -/
theorem lower_bound_crossing (x : ℝ) : (0 : ℝ) ≤ max 0 x :=
  le_max_left 0 x

/-- Main Soundness Theorem: The ReLU relaxation is mathematically correct.

    For any x in the interval [l, u], the computed linear bounds contain ReLU(x):
    lower.eval(x) ≤ max(0, x) ≤ upper.eval(x)

    This is the foundation of verified neural network verification. -/
theorem relu_relaxation_sound (l u : ℚ) (x : ℝ) (h : (l : ℝ) ≤ x ∧ x ≤ u) :
    let sb := getReLURelaxation l u
    sb.lower.eval x ≤ max 0 x ∧ max 0 x ≤ sb.upper.eval x := by
  unfold getReLURelaxation
  split_ifs with h_active h_inactive

  · -- Case: l ≥ 0 (always active)
    -- x ≥ l ≥ 0, so max(0, x) = x
    simp only [LinearBound.eval]
    have hx_nonneg : 0 ≤ x := le_trans (by exact_mod_cast h_active) h.1
    rw [max_eq_right hx_nonneg]
    simp

  · -- Case: u ≤ 0 (always inactive)
    -- x ≤ u ≤ 0, so max(0, x) = 0
    simp only [LinearBound.eval]
    have hx_nonpos : x ≤ 0 := le_trans h.2 (by exact_mod_cast h_inactive)
    rw [max_eq_left hx_nonpos]
    simp

  · -- Case: l < 0 < u (crossing)
    push_neg at h_active h_inactive
    simp only
    constructor
    · -- Lower bound: 0 ≤ max(0, x)
      simp only [LinearBound.eval]
      have : ((0 : ℚ) : ℝ) * x + ((0 : ℚ) : ℝ) = (0 : ℝ) := by simp
      rw [this]
      exact lower_bound_crossing x
    · -- Upper bound: Triangle theorem
      exact upper_bound_valid l u x h_active h_inactive h

/-! ## Properties of Linear Bounds -/

/-- Identity bound: y = x -/
def LinearBound.identity : LinearBound := ⟨1, 0⟩

/-- Zero bound: y = 0 -/
def LinearBound.zero : LinearBound := ⟨0, 0⟩

@[simp]
theorem LinearBound.eval_identity (x : ℝ) : LinearBound.identity.eval x = x := by
  simp [identity, eval]

@[simp]
theorem LinearBound.eval_zero (x : ℝ) : LinearBound.zero.eval x = 0 := by
  simp [zero, eval]

/-- Compose linear bounds: if y = ax + b and z = cy + d, then z = c(ax+b) + d = (ca)x + (cb+d) -/
def LinearBound.compose (outer inner : LinearBound) : LinearBound :=
  { slope := outer.slope * inner.slope,
    bias := outer.slope * inner.bias + outer.bias }

theorem LinearBound.eval_compose (outer inner : LinearBound) (x : ℝ) :
    (outer.compose inner).eval x = outer.eval (inner.eval x) := by
  simp only [compose, eval]
  push_cast
  ring

/-! ## Interval Width after ReLU -/

/-- The output interval width after applying ReLU relaxation.
    For crossing case, width = λ · (u - l) = u · (u - l) / (u - l) = u -/
def outputWidth (l u : ℚ) : ℚ :=
  if 0 ≤ l then u - l      -- Active: width preserved
  else if u ≤ 0 then 0      -- Inactive: width = 0
  else u                     -- Crossing: upper bound is u at x = u

/-- In the crossing case, evaluating upper bound at u gives exactly u -/
theorem crossingUpperBound_at_u (l u : ℚ) (hl : l < 0) (hu : 0 < u) :
    (crossingUpperBound l u).eval (u : ℝ) = u := by
  have h_diff_ne : u - l ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hl hu))
  rw [crossingUpperBound_eval l u u h_diff_ne]
  have h_diff_ne' : (u : ℝ) - l ≠ 0 := by exact_mod_cast h_diff_ne
  field_simp

/-- In the crossing case, evaluating upper bound at l gives exactly 0 -/
theorem crossingUpperBound_at_l (l u : ℚ) (hl : l < 0) (hu : 0 < u) :
    (crossingUpperBound l u).eval (l : ℝ) = 0 := by
  have h_diff_ne : u - l ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hl hu))
  rw [crossingUpperBound_eval l u l h_diff_ne]
  simp

end LeanCert.ML.Symbolic
