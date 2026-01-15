/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Tactic.IntervalAuto

/-!
# Tests for Automated Interval Bound Tactic

This file tests the `interval_bound` tactic.
-/

namespace LeanBound.Tactic.TestAuto

open LeanBound.Core
open LeanBound.Numerics

/-- The unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

-- Test 1: Simple x² ≤ 1 on [0, 1]
theorem test_xsq_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) ≤ (1 : ℚ) := by
  interval_bound

-- Test 2: 0 ≤ x² on [0, 1]
theorem test_zero_le_xsq : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) := by
  interval_bound

-- Test 3: sin(x) ≤ 1 on [0, 1]
theorem test_sin_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) (Expr.sin (Expr.var 0)) ≤ (1 : ℚ) := by
  interval_bound

-- Test 4: -1 ≤ sin(x) on [0, 1]
theorem test_neg_one_le_sin : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) (Expr.sin (Expr.var 0)) := by
  interval_bound

-- Test 5: x² + sin(x) ≤ 2 on [0, 1]
theorem test_xsq_plus_sin : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.sin (Expr.var 0))) ≤ (2 : ℚ) := by
  interval_bound

-- Test 6: x² - 2 < 0 on [0, 1]
theorem test_xsq_minus_two_lt_zero : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) < (0 : ℚ) := by
  interval_bound

-- Test 7: exp(x) ≤ 3 on [0, 1] (needs higher Taylor depth)
theorem test_exp_le_three : ∀ x ∈ I01, Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) ≤ (3 : ℚ) := by
  interval_bound 15

-- Test 8: 0.9 ≤ exp(x) on [0, 1]
-- (A weaker bound that works without monotonicity)
theorem test_point_nine_le_exp : ∀ x ∈ I01, (9/10 : ℚ) ≤ Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) := by
  interval_bound 15

-- Test 9: 1 ≤ exp(x) on [0, 1] - THE BOUNDARY CASE
-- This tests the smart bound checker with monotonicity.
-- exp is strictly increasing on [0, 1], so min(exp(x)) = exp(0) = 1.
-- The smart checker evaluates exp at the left endpoint to get the tight bound.
theorem test_one_le_exp : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) := by
  interval_bound 15

-- Test 10: exp(x) ≤ e on [0, 1] - upper bound at boundary
-- exp is strictly increasing, so max(exp(x)) = exp(1) ≈ 2.718
-- 11/4 = 2.75 > e, so this should pass with monotonicity
theorem test_exp_le_e_approx : ∀ x ∈ I01, Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) ≤ (11/4 : ℚ) := by
  interval_bound 15

/-! ## Raw Lean Expression Tests

These tests use raw Lean math syntax (x * x, Real.sin x, etc.)
instead of the pre-reified Expr.eval form.
The tactic should automatically reify these expressions.
-/

-- Test 11: Raw x * x ≤ 1 on [0, 1]
theorem test_raw_xsq_le_one : ∀ x ∈ I01, x * x ≤ (1 : ℚ) := by
  interval_bound

-- Test 12: Raw 0 ≤ x * x on [0, 1]
theorem test_raw_zero_le_xsq : ∀ x ∈ I01, (0 : ℚ) ≤ x * x := by
  interval_bound

-- Test 13: Raw sin(x) ≤ 1 on [0, 1]
theorem test_raw_sin_le_one : ∀ x ∈ I01, Real.sin x ≤ (1 : ℚ) := by
  interval_bound

-- Test 14: Raw exp(x) ≤ 3 on [0, 1]
theorem test_raw_exp_le_three : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by
  interval_bound 15

-- Test 15: Raw 1 ≤ exp(x) on [0, 1] - boundary case with reification
theorem test_raw_one_le_exp : ∀ x ∈ I01, (1 : ℚ) ≤ Real.exp x := by
  interval_bound 15

-- Test 16: Raw x² + sin(x) ≤ 2 on [0, 1]
theorem test_raw_xsq_plus_sin : ∀ x ∈ I01, x * x + Real.sin x ≤ (2 : ℚ) := by
  interval_bound

/-! ## Global Optimization - Manual Usage

The global optimization theorems are proven and can be used manually.
The automatic `opt_bound` tactic is a work in progress for full automation.
Below are examples of how to use the verification theorems directly.
-/

open LeanBound.Numerics.Optimization in
/-- A 1D box [0, 1] for single variable optimization -/
def B01 : Box := [I01]

open LeanBound.Numerics.Optimization in
/-- A 2D box [0, 1] × [0, 1] -/
def B01_2D : Box := [I01, I01]

-- Example: Using verify_global_upper_bound manually
-- This demonstrates that the verification theorems work correctly
open LeanBound.Numerics.Optimization in
open LeanBound.Numerics.Certificate.GlobalOpt in
theorem test_opt_xsq_le_one : ∀ ρ, Box.envMem ρ B01 → (∀ i, i ≥ B01.length → ρ i = 0) →
    Expr.eval ρ (Expr.mul (Expr.var 0) (Expr.var 0)) ≤ (1 : ℚ) :=
  verify_global_upper_bound
    (Expr.mul (Expr.var 0) (Expr.var 0))
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
    B01 1 ⟨1000, 1/1000, false, 10⟩
    (by native_decide)

-- Example: Using verify_global_lower_bound manually for 0 ≤ x²
open LeanBound.Numerics.Optimization in
open LeanBound.Numerics.Certificate.GlobalOpt in
theorem test_opt_zero_le_xsq : ∀ ρ, Box.envMem ρ B01 → (∀ i, i ≥ B01.length → ρ i = 0) →
    (0 : ℚ) ≤ Expr.eval ρ (Expr.mul (Expr.var 0) (Expr.var 0)) :=
  verify_global_lower_bound
    (Expr.mul (Expr.var 0) (Expr.var 0))
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
    B01 0 ⟨1000, 1/1000, false, 10⟩
    (by native_decide)

-- Example: 2D optimization: x² + y² ≤ 2 on [0,1]²
open LeanBound.Numerics.Optimization in
open LeanBound.Numerics.Certificate.GlobalOpt in
theorem test_opt_2d_sum_sq : ∀ ρ, Box.envMem ρ B01_2D → (∀ i, i ≥ B01_2D.length → ρ i = 0) →
    Expr.eval ρ (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                          (Expr.mul (Expr.var 1) (Expr.var 1))) ≤ (2 : ℚ) :=
  verify_global_upper_bound
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.mul (Expr.var 1) (Expr.var 1)))
    (ExprSupportedCore.add
      (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
      (ExprSupportedCore.mul (ExprSupportedCore.var 1) (ExprSupportedCore.var 1)))
    B01_2D 2 ⟨1000, 1/1000, false, 10⟩
    (by native_decide)

/-! ## Root Finding Tests

These tests verify the `root_bound` tactic for proving absence of roots.
Note: The 0 must be of type ℝ (not ℚ coerced to ℝ) since Expr.eval returns ℝ.
-/

-- Test 17: x² + 1 ≠ 0 on [0, 1] (always positive)
theorem test_xsq_plus_one_ne_zero : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const 1)) ≠ (0 : ℝ) := by
  root_bound

-- Test 18: exp(x) ≠ 0 on [0, 1] (always positive)
theorem test_exp_ne_zero : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) ≠ (0 : ℝ) := by
  root_bound 15

-- Test 19: x + 2 ≠ 0 on [0, 1] (always positive on this interval)
theorem test_x_plus_two_ne_zero : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.var 0) (Expr.const 2)) ≠ (0 : ℝ) := by
  root_bound

-- Test 20: x² - 2 ≠ 0 on [0, 1] (√2 ≈ 1.41 is outside [0,1])
-- This tests that a function with roots elsewhere has no roots in [0,1]
theorem test_xsq_minus_two_ne_zero : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) ≠ (0 : ℝ) := by
  root_bound

/-! ## Multivariate Bounds Tests

These tests verify the `multivariate_bound` tactic for proving bounds over multi-variable domains.
The multivariate_bound tactic is currently under development.

NOTE: The full automatic bridging from `∀ x ∈ Set.Icc ...` to the internal Box form requires
additional work. For now, use the `opt_bound` tactic for global optimization goals that are
already in the `Box.envMem` form.
-/

-- Tests using opt_bound (the working approach for Box.envMem form)
-- See test_opt_2d_sum_sq above for example usage

end LeanBound.Tactic.TestAuto
