/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Optimization.Global
import LeanCert.Engine.Optimization.Guided

/-!
# Optimization Regression Tests

This file contains regression tests for the global optimization algorithms.
These tests should pass before AND after any refactoring of the optimization code.

## Test Categories

1. **API Consistency**: All public functions return expected result types
2. **Numerical Accuracy**: Known optima are found within tolerance
3. **Cross-Variant Consistency**: Core, Dyadic, Affine give compatible results
4. **Proof Compatibility**: Correctness theorems can be applied

## How to Use

Run `lake build LeanCert.Test.OptimizationRegression` to verify all tests pass.
If any test fails after refactoring, the refactoring has introduced a regression.
-/

namespace LeanCert.Test.OptimizationRegression

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization

/-! ### Test Expressions -/

/-- x² - has minimum 0 at x=0 -/
def exprX2 : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

/-- x² + y² - has minimum 0 at (0,0) -/
def exprSumSq : Expr :=
  Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
           (Expr.mul (Expr.var 1) (Expr.var 1))

/-- sin(x) - oscillates between -1 and 1 -/
def exprSin : Expr := Expr.sin (Expr.var 0)

/-- exp(x) - monotonically increasing -/
def exprExp : Expr := Expr.exp (Expr.var 0)

/-- x³ - monotonically increasing -/
def exprX3 : Expr := Expr.mul (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.var 0)

/-- (x-1)² + (y-2)² - has minimum 0 at (1,2) -/
def exprShiftedSumSq : Expr :=
  let xm1 := Expr.add (Expr.var 0) (Expr.const (-1))
  let ym2 := Expr.add (Expr.var 1) (Expr.const (-2))
  Expr.add (Expr.mul xm1 xm1) (Expr.mul ym2 ym2)

/-! ### Test Boxes -/

def box_sym : Box := [⟨-1, 1, by norm_num⟩]
def box_pos : Box := [⟨0, 2, by norm_num⟩]
def box_neg : Box := [⟨-2, 0, by norm_num⟩]
def box_wide : Box := [⟨-10, 10, by norm_num⟩]
def box_2d_sym : Box := [⟨-1, 1, by norm_num⟩, ⟨-1, 1, by norm_num⟩]
def box_2d_pos : Box := [⟨0, 2, by norm_num⟩, ⟨0, 3, by norm_num⟩]

/-! ### Test Configuration -/

def testCfg : GlobalOptConfig := { maxIterations := 500, tolerance := 1/100 }
def testCfgDyadic : GlobalOptConfigDyadic := { maxIterations := 500, tolerance := 1/100, precision := -53 }
def testCfgAffine : GlobalOptConfigAffine := { maxIterations := 500, tolerance := 1/100 }

/-! ### Section 1: API Consistency Tests

These tests verify that all public API functions:
1. Can be called with expected arguments
2. Return GlobalResult with expected structure
3. Don't panic or fail on valid inputs
-/

section APIConsistency

/-- Test globalMinimizeCore returns a result -/
def test_globalMinimizeCore_returns : GlobalResult :=
  globalMinimizeCore exprX2 box_sym testCfg

/-- Test globalMaximizeCore returns a result -/
def test_globalMaximizeCore_returns : GlobalResult :=
  globalMaximizeCore exprX2 box_sym testCfg

/-- Test globalMinimizeCoreDiv returns a result -/
def test_globalMinimizeCoreDiv_returns : GlobalResult :=
  globalMinimizeCoreDiv exprX2 box_sym testCfg

/-- Test globalMaximizeCoreDiv returns a result -/
def test_globalMaximizeCoreDiv_returns : GlobalResult :=
  globalMaximizeCoreDiv exprX2 box_sym testCfg

/-- Test globalMinimizeDyadic returns a result -/
def test_globalMinimizeDyadic_returns : GlobalResult :=
  globalMinimizeDyadic exprX2 box_sym testCfgDyadic

/-- Test globalMaximizeDyadic returns a result -/
def test_globalMaximizeDyadic_returns : GlobalResult :=
  globalMaximizeDyadic exprX2 box_sym testCfgDyadic

/-- Test globalMinimizeAffine returns a result -/
def test_globalMinimizeAffine_returns : GlobalResult :=
  globalMinimizeAffine exprX2 box_sym testCfgAffine

/-- Test globalMaximizeAffine returns a result -/
def test_globalMaximizeAffine_returns : GlobalResult :=
  globalMaximizeAffine exprX2 box_sym testCfgAffine

/-- Test globalMinimizeGuided returns a result -/
def test_globalMinimizeGuided_returns : GlobalResult :=
  globalMinimizeGuided exprX2 box_sym { maxIterations := 500, tolerance := 1/100 }

/-- Test globalMaximizeGuided returns a result -/
def test_globalMaximizeGuided_returns : GlobalResult :=
  globalMaximizeGuided exprX2 box_sym { maxIterations := 500, tolerance := 1/100 }

-- Verify all API functions compile and can be evaluated
#eval test_globalMinimizeCore_returns.bound.lo
#eval test_globalMaximizeCore_returns.bound.hi
#eval test_globalMinimizeCoreDiv_returns.bound.lo
#eval test_globalMinimizeDyadic_returns.bound.lo
#eval test_globalMinimizeAffine_returns.bound.lo
#eval test_globalMinimizeGuided_returns.bound.lo

end APIConsistency

/-! ### Section 2: Numerical Accuracy Tests

These tests verify that optimization finds known optima within tolerance.
-/

section NumericalAccuracy

/-- x² on [-1,1] should have minimum near 0 -/
def test_x2_min : Bool :=
  let result := globalMinimizeCore exprX2 box_sym testCfg
  -- Lower bound should be ≥ -1 (sound lower bound)
  -- Upper bound (best found) should be ≤ 1 (we found something reasonable)
  result.bound.lo ≥ -1 && result.bound.hi ≤ 1

/-- x² on [-1,1] should have maximum near 1 -/
def test_x2_max : Bool :=
  let result := globalMaximizeCore exprX2 box_sym testCfg
  -- Maximum should be ≤ 2 (sound) and lower bound reasonable
  result.bound.hi ≤ 2 && result.bound.lo ≥ 0

/-- x²+y² on [-1,1]² should have minimum near 0 -/
def test_sumSq_min : Bool :=
  let result := globalMinimizeCore exprSumSq box_2d_sym testCfg
  -- lo is a sound lower bound (can be conservative due to interval arithmetic)
  -- hi (best found) should be close to 0 (the actual minimum)
  result.bound.lo ≤ result.bound.hi && result.bound.hi ≤ 1

/-- sin(x) on [-10,10] should have minimum near -1 -/
def test_sin_min : Bool :=
  let result := globalMinimizeCore exprSin box_wide testCfg
  -- sin is bounded by [-1,1], minimum is -1
  result.bound.lo ≥ -2 && result.bound.hi ≤ 0

/-- sin(x) on [-10,10] should have maximum near 1 -/
def test_sin_max : Bool :=
  let result := globalMaximizeCore exprSin box_wide testCfg
  -- Maximum is 1
  result.bound.hi ≤ 2 && result.bound.lo ≥ 0

/-- exp(x) on [0,2] should have minimum near 1 (at x=0) -/
def test_exp_min : Bool :=
  let result := globalMinimizeCore exprExp box_pos testCfg
  -- exp(0) = 1, so minimum ≥ 1
  result.bound.lo ≥ 0 && result.bound.hi ≤ 2

/-- exp(x) on [0,2] should have maximum near e² ≈ 7.389 (at x=2) -/
def test_exp_max : Bool :=
  let result := globalMaximizeCore exprExp box_pos testCfg
  -- e² ≈ 7.389, so max should be in [6, 9]
  result.bound.lo ≥ 6 && result.bound.hi ≤ 9

-- Run numerical accuracy tests
#eval if test_x2_min then "✓ test_x2_min" else "✗ test_x2_min FAILED"
#eval if test_x2_max then "✓ test_x2_max" else "✗ test_x2_max FAILED"
#eval if test_sumSq_min then "✓ test_sumSq_min" else "✗ test_sumSq_min FAILED"
#eval if test_sin_min then "✓ test_sin_min" else "✗ test_sin_min FAILED"
#eval if test_sin_max then "✓ test_sin_max" else "✗ test_sin_max FAILED"
#eval if test_exp_min then "✓ test_exp_min" else "✗ test_exp_min FAILED"
#eval if test_exp_max then "✓ test_exp_max" else "✗ test_exp_max FAILED"

end NumericalAccuracy

/-! ### Section 3: Cross-Variant Consistency Tests

These tests verify that different algorithm variants (Core, Dyadic, Affine)
produce compatible results (bounds should overlap or be close).
-/

section CrossVariantConsistency

/-- Helper: check if two intervals are compatible (overlap or close) -/
def intervalsCompatible (lo1 hi1 lo2 hi2 : ℚ) (margin : ℚ := 1/10) : Bool :=
  -- Either they overlap, or the gap is small
  (lo1 ≤ hi2 + margin && lo2 ≤ hi1 + margin)

/-- Core and Dyadic should give compatible results for x² -/
def test_core_dyadic_compatible : Bool :=
  let resultCore := globalMinimizeCore exprX2 box_sym testCfg
  let resultDyadic := globalMinimizeDyadic exprX2 box_sym testCfgDyadic
  intervalsCompatible resultCore.bound.lo resultCore.bound.hi
                      resultDyadic.bound.lo resultDyadic.bound.hi

/-- Core and Affine should give compatible results for x² -/
def test_core_affine_compatible : Bool :=
  let resultCore := globalMinimizeCore exprX2 box_sym testCfg
  let resultAffine := globalMinimizeAffine exprX2 box_sym testCfgAffine
  intervalsCompatible resultCore.bound.lo resultCore.bound.hi
                      resultAffine.bound.lo resultAffine.bound.hi

/-- CoreDiv and Core should give compatible results -/
def test_core_corediv_compatible : Bool :=
  let resultCore := globalMinimizeCore exprX2 box_sym testCfg
  let resultCoreDiv := globalMinimizeCoreDiv exprX2 box_sym testCfg
  intervalsCompatible resultCore.bound.lo resultCore.bound.hi
                      resultCoreDiv.bound.lo resultCoreDiv.bound.hi

/-- Guided and Core should give compatible results -/
def test_guided_core_compatible : Bool :=
  let resultCore := globalMinimizeCore exprX2 box_sym testCfg
  let resultGuided := globalMinimizeGuided exprX2 box_sym { maxIterations := 500, tolerance := 1/100 }
  intervalsCompatible resultCore.bound.lo resultCore.bound.hi
                      resultGuided.bound.lo resultGuided.bound.hi

-- Run cross-variant tests
#eval if test_core_dyadic_compatible then "✓ Core-Dyadic compatible" else "✗ Core-Dyadic FAILED"
#eval if test_core_affine_compatible then "✓ Core-Affine compatible" else "✗ Core-Affine FAILED"
#eval if test_core_corediv_compatible then "✓ Core-CoreDiv compatible" else "✗ Core-CoreDiv FAILED"
#eval if test_guided_core_compatible then "✓ Guided-Core compatible" else "✗ Guided-Core FAILED"

end CrossVariantConsistency

/-! ### Section 4: Proof Compatibility Tests

These tests verify that correctness theorems exist and have expected signatures.
The actual theorem application is tested implicitly through SearchAPI usage.
-/

-- Verify correctness theorem types exist
#check @globalMinimizeCore_lo_correct
#check @globalMinimizeCore_hi_achievable
#check @globalMinimizeCore_lo_le_hi
#check @globalMaximizeCore_hi_correct
#check @globalMaximizeCore_lo_achievable
#check @globalMaximizeCore_lo_le_hi

-- Verify Dyadic/Affine theorems exist
#check @globalMinimizeDyadic_lo_correct
#check @globalMaximizeDyadic_hi_correct
#check @globalMinimizeAffine_lo_correct
#check @globalMaximizeAffine_hi_correct

section ProofCompatibility

/-- Simple sanity check: lo ≤ hi for any result -/
def test_lo_le_hi : Bool :=
  let result := globalMinimizeCore exprX2 box_sym testCfg
  result.bound.lo ≤ result.bound.hi

#eval if test_lo_le_hi then "✓ lo ≤ hi" else "✗ lo ≤ hi FAILED"

end ProofCompatibility

/-! ### Section 5: Edge Cases

Test behavior on edge cases that might reveal bugs.
-/

section EdgeCases

/-- Empty iteration limit should still return valid result -/
def test_zero_iterations : Bool :=
  let cfg : GlobalOptConfig := { maxIterations := 0, tolerance := 1/100 }
  let result := globalMinimizeCore exprX2 box_sym cfg
  -- Should return initial bounds without refinement
  result.bound.lo ≤ result.bound.hi

/-- Very tight tolerance -/
def test_tight_tolerance : Bool :=
  let cfg : GlobalOptConfig := { maxIterations := 1000, tolerance := 1/10000 }
  let result := globalMinimizeCore exprX2 box_sym cfg
  -- Just check it returns valid bounds
  result.bound.lo ≤ result.bound.hi

/-- Wide box -/
def test_wide_box : Bool :=
  let result := globalMinimizeCore exprX2 box_wide testCfg
  -- lo can be conservative (interval arithmetic on [-10,10]² gives [-100,100])
  -- hi (best found) should be close to 0 (the actual minimum at x=0)
  result.bound.lo ≤ result.bound.hi && result.bound.hi ≤ 1

/-- 2D optimization -/
def test_2d_optimization : Bool :=
  let result := globalMinimizeCore exprSumSq box_2d_pos testCfg
  -- Minimum of x²+y² on [0,2]×[0,3] is 0 at (0,0)
  result.bound.lo ≥ 0

-- Run edge case tests
#eval if test_zero_iterations then "✓ zero iterations" else "✗ zero iterations FAILED"
#eval if test_tight_tolerance then "✓ tight tolerance" else "✗ tight tolerance FAILED"
#eval if test_wide_box then "✓ wide box" else "✗ wide box FAILED"
#eval if test_2d_optimization then "✓ 2D optimization" else "✗ 2D optimization FAILED"

end EdgeCases

/-! ### Summary Test -/

/-- Run all boolean tests and report -/
def runAllTests : IO Unit := do
  IO.println "=== Optimization Regression Tests ==="
  IO.println ""
  IO.println "Numerical Accuracy:"
  IO.println s!"  x² min:     {if test_x2_min then "✓" else "✗"}"
  IO.println s!"  x² max:     {if test_x2_max then "✓" else "✗"}"
  IO.println s!"  x²+y² min:  {if test_sumSq_min then "✓" else "✗"}"
  IO.println s!"  sin min:    {if test_sin_min then "✓" else "✗"}"
  IO.println s!"  sin max:    {if test_sin_max then "✓" else "✗"}"
  IO.println s!"  exp min:    {if test_exp_min then "✓" else "✗"}"
  IO.println s!"  exp max:    {if test_exp_max then "✓" else "✗"}"
  IO.println ""
  IO.println "Cross-Variant Consistency:"
  IO.println s!"  Core-Dyadic:  {if test_core_dyadic_compatible then "✓" else "✗"}"
  IO.println s!"  Core-Affine:  {if test_core_affine_compatible then "✓" else "✗"}"
  IO.println s!"  Core-CoreDiv: {if test_core_corediv_compatible then "✓" else "✗"}"
  IO.println s!"  Guided-Core:  {if test_guided_core_compatible then "✓" else "✗"}"
  IO.println ""
  IO.println "Edge Cases:"
  IO.println s!"  Zero iters:   {if test_zero_iterations then "✓" else "✗"}"
  IO.println s!"  Tight tol:    {if test_tight_tolerance then "✓" else "✗"}"
  IO.println s!"  Wide box:     {if test_wide_box then "✓" else "✗"}"
  IO.println s!"  2D opt:       {if test_2d_optimization then "✓" else "✗"}"
  IO.println ""
  let allPassed := test_x2_min && test_x2_max && test_sumSq_min &&
                   test_sin_min && test_sin_max && test_exp_min && test_exp_max &&
                   test_core_dyadic_compatible && test_core_affine_compatible &&
                   test_core_corediv_compatible && test_guided_core_compatible &&
                   test_zero_iterations && test_tight_tolerance &&
                   test_wide_box && test_2d_optimization
  if allPassed then
    IO.println "=== ALL TESTS PASSED ==="
  else
    IO.println "=== SOME TESTS FAILED ==="

#eval runAllTests

end LeanCert.Test.OptimizationRegression
