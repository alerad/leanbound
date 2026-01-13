/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Tactic.Interval
import LeanBound.Discovery
import LeanBound.Numerics.IntervalEvalDyadic
import LeanBound.Numerics.Optimization.Global

/-!
# Edge Case Stress Tests

This file tests boundary conditions, singularities, and "tricky" mathematical
scenarios to ensure the library behaves safely (soundly) even when exact
answers are impossible.
-/

namespace LeanBound.Examples.EdgeCases

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Optimization

/-! ## 1. The "Division by Zero" Singularity

The interval evaluator `evalIntervalCoreWithDiv` has a fallback for intervals containing 0.
It should return a massive safe interval rather than crashing or proving False.
-/

def I_cross_zero : IntervalRat := ⟨-1, 1, by norm_num⟩

-- 1/x on [-1, 1] is undefined at 0. The system should return safe wide bounds.
-- Test that evalIntervalCoreWithDiv gives very wide bounds for inv at zero.
theorem inv_zero_safe :
    let result := evalIntervalCoreWithDiv (Expr.inv (Expr.var 0)) (fun _ => I_cross_zero) {}
    -- The implementation should return very wide bounds for zero division
    result.lo ≤ -1000000 ∧ 1000000 ≤ result.hi := by
  native_decide

/-! ## 2. The "Square Root of Negative" Edge Case

Mathlib defines `Real.sqrt x = 0` for `x < 0`. LeanBound's interval arithmetic
must respect this convention to remain sound with respect to the standard library.
-/

def I_negative : IntervalRat := ⟨-5, -1, by norm_num⟩

-- sqrt(x) on [-5, -1] should contain 0 since Real.sqrt returns 0 for negative inputs
def exprSqrt : Expr := Expr.sqrt (Expr.var 0)
def exprSqrt_core : ExprSupportedCore exprSqrt :=
  ExprSupportedCore.sqrt (ExprSupportedCore.var 0)

-- The interval for sqrt on negative domain should be [0, something]
theorem sqrt_neg_contains_zero :
    let result := evalIntervalCore1 exprSqrt I_negative {}
    result.lo = 0 := by
  native_decide

-- sqrt(x) on [-1, 4] should evaluate to [0, ≤ 5] (conservative bound)
def I_mixed : IntervalRat := ⟨-1, 4, by norm_num⟩

theorem sqrt_mixed_contains_two :
    let result := evalIntervalCore1 exprSqrt I_mixed {}
    result.lo = 0 ∧ result.hi ≥ 2 := by
  native_decide

/-! ## 3. Root Finding: Tangential Roots (Multiplicity > 1)

Bisection relies on sign change (IVT). It works for crossings (x³) but fails
for touching roots (x²). This test confirms the library handles "no sign change"
correctly.

NOTE: Interval arithmetic overestimates: [-1, 1] * [-1, 1] = [-1, 1], not [0, 1].
So x² on [-1, 1] gives interval [-1, 1], which includes negative values.
This is sound (conservative) but not tight.
-/

-- x² touches 0 at x=0, but f(-1) > 0 and f(1) > 0.
def exprX2 : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

-- Check that x² is bounded above by 1 on [-1, 1]
def exprX2_core : ExprSupportedCore exprX2 :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)

theorem x_sq_bounded_above : ∀ x ∈ I_cross_zero, Expr.eval (fun _ => x) exprX2 ≤ (1 : ℚ) := by
  interval_le exprX2, exprX2_core, I_cross_zero, 1

-- On a non-negative interval, x² is correctly bounded below
def I_positive : IntervalRat := ⟨0, 1, by norm_num⟩

theorem x_sq_nonneg_on_positive : ∀ x ∈ I_positive, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprX2 := by
  interval_ge exprX2, exprX2_core, I_positive, 0

-- x³ on [-1, 1] spans zero
def exprX3 : Expr := Expr.mul (Expr.var 0) (Expr.mul (Expr.var 0) (Expr.var 0))
def exprX3_core : ExprSupportedCore exprX3 :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0)
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))

-- x³ can be positive or negative on [-1, 1]
theorem x_cube_spans_zero :
    let result := evalIntervalCore1 exprX3 I_cross_zero {}
    result.lo < 0 ∧ 0 < result.hi := by
  native_decide

/-! ## 4. The "Sinc" Singularity at 0

sin(x)/x has a removable singularity at 0.
`Expr.div (sin x) x` will give wide bounds at 0, but `Expr.sinc x` is safe.

NOTE: sinc is not in ExprSupportedCore, so we test using ExprSupportedWithInv
or direct evaluation.
-/

-- Method 1: Explicit division (unsafe at 0) - gives wide bounds
def exprSinDivX : Expr := Expr.mul (Expr.sin (Expr.var 0)) (Expr.inv (Expr.var 0))

theorem sin_div_x_wide_at_zero :
    let result := evalIntervalCoreWithDiv exprSinDivX (fun _ => I_cross_zero) {}
    -- Should give wide fallback bounds due to 1/x at 0
    result.hi > 1000 ∨ result.lo < -1000 := by
  native_decide

-- Method 2: Sinc intrinsic (safe at 0) - tested via direct evaluation
def exprSinc : Expr := Expr.sinc (Expr.var 0)

-- Verify sinc(0) = 1 semantically
theorem sinc_at_zero : Expr.eval (fun _ => 0) exprSinc = 1 := by
  simp only [exprSinc, Expr.eval_sinc, Expr.eval_var, Real.sinc_zero]

-- Verify sinc is bounded using evalIntervalCoreWithDiv (which supports sinc)
theorem sinc_bounded_check :
    let result := evalIntervalCoreWithDiv exprSinc (fun _ => I_cross_zero) {}
    result.lo ≥ -2 ∧ result.hi ≤ 2 := by
  native_decide

/-! ## 5. Precision Stress Test (Deep Polynomial)

Deep composition of polynomials causes rational denominators to explode in size.
We test if the evaluator can handle depths that might choke naive implementations.
-/

-- A polynomial x^16 on [0.5, 1.0]
def exprDeepPoly : Expr :=
  let x := Expr.var 0
  let x2 := Expr.mul x x
  let x4 := Expr.mul x2 x2
  let x8 := Expr.mul x4 x4
  Expr.mul x8 x8 -- x^16

def exprDeepPoly_core : ExprSupportedCore exprDeepPoly :=
  let xc := ExprSupportedCore.var 0
  let x2c := ExprSupportedCore.mul xc xc
  let x4c := ExprSupportedCore.mul x2c x2c
  let x8c := ExprSupportedCore.mul x4c x4c
  ExprSupportedCore.mul x8c x8c

def I_half_one : IntervalRat := ⟨1/2, 1, by norm_num⟩

-- x^16 on [0.5, 1] should be in [0, 1]
theorem deep_poly_bounded :
    ∀ x ∈ I_half_one, Expr.eval (fun _ => x) exprDeepPoly ≤ (1 : ℚ) := by
  interval_le exprDeepPoly, exprDeepPoly_core, I_half_one, 1

theorem deep_poly_nonneg :
    ∀ x ∈ I_half_one, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprDeepPoly := by
  interval_ge exprDeepPoly, exprDeepPoly_core, I_half_one, 0

/-! ## 6. The "Wiggle" Function

Test a function with oscillating behavior: x · sin(10x) on [0.1, 1].
-/

def exprWiggle : Expr :=
  Expr.mul (Expr.var 0) (Expr.sin (Expr.mul (Expr.const 10) (Expr.var 0)))

def exprWiggle_core : ExprSupportedCore exprWiggle :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0)
    (ExprSupportedCore.sin
      (ExprSupportedCore.mul (ExprSupportedCore.const 10) (ExprSupportedCore.var 0)))

def I_wiggle : IntervalRat := ⟨1/10, 1, by norm_num⟩

-- The wiggle function is bounded: |x · sin(10x)| ≤ |x| ≤ 1
theorem wiggle_bounded :
    ∀ x ∈ I_wiggle, Expr.eval (fun _ => x) exprWiggle ≤ (1 : ℚ) := by
  interval_le exprWiggle, exprWiggle_core, I_wiggle, 1

theorem wiggle_bounded_below :
    ∀ x ∈ I_wiggle, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprWiggle := by
  interval_ge exprWiggle, exprWiggle_core, I_wiggle, (-1)

/-! ## 7. Type Safety of IntervalRat

The `IntervalRat` structure requires `lo ≤ hi` as a field, so invalid intervals
cannot be constructed. This is proven by the type system itself.
-/

-- This demonstrates that IntervalRat is always valid by construction
example : ∀ I : IntervalRat, I.lo ≤ I.hi := fun I => I.le

/-! ## 8. Zero-Dimensional Evaluation

Evaluating a constant expression (0 variables) on an empty domain.
-/

def exprConst5 : Expr := Expr.const 5
def exprConst5_core : ExprSupportedCore exprConst5 :=
  ExprSupportedCore.const 5

-- A constant function evaluates correctly
theorem const_eval_correct :
    Expr.eval (fun _ => 0) exprConst5 = 5 := by
  simp only [exprConst5, Expr.eval_const, Rat.cast_ofNat]

-- Constant interval evaluation
def I_any : IntervalRat := ⟨0, 1, by norm_num⟩

theorem const_interval_correct :
    let result := evalIntervalCore1 exprConst5 I_any {}
    result.lo = 5 ∧ result.hi = 5 := by
  native_decide

/-! ## 9. Dyadic Interval Evaluation

Test the dyadic (floating-point style) evaluator for performance comparison.
-/

-- Create a dyadic interval [0, 1]
def I_unit_dyadic : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨1, 0⟩, by native_decide⟩  -- Dyadic 0 = 0 * 2^0, Dyadic 1 = 1 * 2^0

-- Evaluate using dyadic arithmetic (faster for deep expressions)
theorem dyadic_x2_bounded :
    let result := evalIntervalDyadic exprX2 (fun _ => I_unit_dyadic) {}
    result.lo.toRat ≥ 0 := by
  native_decide

/-! ## 10. Global Optimization Edge Cases -/

-- Minimize x² on [-1, 1] - interval arithmetic gives conservative lower bound
def box_sym : Box := [I_cross_zero]

-- Due to interval overestimation, the computed lower bound may be negative
-- But the upper bound should be correct
theorem x2_max_correct :
    let result := globalMaximizeCore exprX2 box_sym {}
    result.bound.hi ≤ 1 := by
  native_decide

-- Test on a box where optimization is more precise
def box_positive : Box := [I_positive]

theorem x2_min_on_positive :
    let result := globalMinimizeCore exprX2 box_positive {}
    result.bound.lo ≥ 0 := by
  native_decide

-- Minimize x³ on [-1, 1] - minimum is at x = -1, value = -1
theorem x3_min_at_neg_one :
    let result := globalMinimizeCore exprX3 box_sym {}
    result.bound.lo ≥ -1 := by
  native_decide

end LeanBound.Examples.EdgeCases
