/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEvalAffine
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalReal
import LeanCert.Engine.Eval.Core
import LeanCert.Engine.Eval.Extended

/-!
# Evaluator Regression Tests

This file contains regression tests for the interval evaluator implementations.
These tests should pass before AND after any refactoring of the evaluator code.

## Test Categories

1. **API Consistency**: All evaluators accept the same expressions
2. **Numerical Accuracy**: Evaluations contain correct values
3. **Cross-Evaluator Consistency**: Dyadic and Core give compatible intervals
4. **Correctness Theorems**: Theorems remain accessible and applicable

## How to Use

Run `lake build LeanCert.Test.EvaluatorRegression` to verify all tests pass.
If any test fails after refactoring, the refactoring has introduced a regression.
-/

namespace LeanCert.Test.EvaluatorRegression

open LeanCert.Core
open LeanCert.Engine
open Affine in open AffineForm in

/-! ### Test Expressions -/

-- Simple polynomial: x²
def exprX2 : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

-- Two-variable: x² + y²
def exprSumSq : Expr :=
  Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
           (Expr.mul (Expr.var 1) (Expr.var 1))

-- Transcendental: sin(x)
def exprSin : Expr := Expr.sin (Expr.var 0)

-- Transcendental: cos(x)
def exprCos : Expr := Expr.cos (Expr.var 0)

-- Transcendental: exp(x)
def exprExp : Expr := Expr.exp (Expr.var 0)

-- Transcendental: sinh(x)
def exprSinh : Expr := Expr.sinh (Expr.var 0)

-- Transcendental: cosh(x)
def exprCosh : Expr := Expr.cosh (Expr.var 0)

-- Bounded: tanh(x)
def exprTanh : Expr := Expr.tanh (Expr.var 0)

-- Constant: π
def exprPi : Expr := Expr.pi

-- Composed: sin(x) + cos(x)
def exprSinCos : Expr := Expr.add (Expr.sin (Expr.var 0)) (Expr.cos (Expr.var 0))

-- Composed: exp(sin(x))
def exprExpSin : Expr := Expr.exp (Expr.sin (Expr.var 0))

-- Linear: 2x + 1
def exprLinear : Expr :=
  Expr.add (Expr.mul (Expr.const 2) (Expr.var 0)) (Expr.const 1)

/-! ### Test Environments -/

-- Unit interval environment for single variable [0, 1]
def unitEnvDyadic : IntervalDyadicEnv := fun i =>
  if i = 0 then IntervalDyadic.ofIntervalRat ⟨0, 1, by norm_num⟩ (-53)
  else IntervalDyadic.ofIntervalRat (IntervalRat.singleton 0) (-53)

def unitEnvCore : IntervalEnv := fun i =>
  if i = 0 then ⟨0, 1, by norm_num⟩
  else IntervalRat.singleton 0

-- Symmetric interval [-1, 1] environment
def symEnvDyadic : IntervalDyadicEnv := fun i =>
  if i = 0 then IntervalDyadic.ofIntervalRat ⟨-1, 1, by norm_num⟩ (-53)
  else IntervalDyadic.ofIntervalRat (IntervalRat.singleton 0) (-53)

def symEnvCore : IntervalEnv := fun i =>
  if i = 0 then ⟨-1, 1, by norm_num⟩
  else IntervalRat.singleton 0

-- Two-variable environment for x,y ∈ [0,1]
def twoVarEnvDyadic : IntervalDyadicEnv := fun i =>
  if i < 2 then IntervalDyadic.ofIntervalRat ⟨0, 1, by norm_num⟩ (-53)
  else IntervalDyadic.ofIntervalRat (IntervalRat.singleton 0) (-53)

def twoVarEnvCore : IntervalEnv := fun i =>
  if i < 2 then ⟨0, 1, by norm_num⟩
  else IntervalRat.singleton 0

/-! ### Default Configurations -/

def defaultDyadicCfg : DyadicConfig := {}
def defaultCoreCfg : EvalConfig := {}

/-! ### Section 1: API Consistency Tests

Verify that all evaluators can evaluate the same expressions.
These are compilation tests - if they compile, the API is consistent.
-/

section APIConsistency

-- Test: Evaluators handle polynomial expressions
#check (evalIntervalDyadic exprX2 unitEnvDyadic defaultDyadicCfg : IntervalDyadic)
#check (evalIntervalCore exprX2 unitEnvCore defaultCoreCfg : IntervalRat)

-- Test: Evaluators handle transcendental expressions
#check (evalIntervalDyadic exprSin unitEnvDyadic defaultDyadicCfg : IntervalDyadic)
#check (evalIntervalCore exprSin unitEnvCore defaultCoreCfg : IntervalRat)

-- Test: Evaluators handle composed expressions
#check (evalIntervalDyadic exprExpSin unitEnvDyadic defaultDyadicCfg : IntervalDyadic)
#check (evalIntervalCore exprExpSin unitEnvCore defaultCoreCfg : IntervalRat)

-- Test: Multi-variable expressions
#check (evalIntervalDyadic exprSumSq twoVarEnvDyadic defaultDyadicCfg : IntervalDyadic)
#check (evalIntervalCore exprSumSq twoVarEnvCore defaultCoreCfg : IntervalRat)

-- Test: Affine evaluator type signature
#check @evalIntervalAffine

end APIConsistency

/-! ### Section 2: Numerical Accuracy Tests

Verify that evaluations produce correct numerical bounds.
-/

section NumericalAccuracy

-- Test x² on [0,1] should give interval containing [0,1]
def test_x2_dyadic : IntervalRat :=
  (evalIntervalDyadic exprX2 unitEnvDyadic defaultDyadicCfg).toIntervalRat

def test_x2_core : IntervalRat :=
  evalIntervalCore exprX2 unitEnvCore defaultCoreCfg

-- Verify bounds are reasonable (lo ≤ 0, hi ≥ 1 due to conservative interval arithmetic)
#guard test_x2_dyadic.lo ≤ 0
#guard test_x2_dyadic.hi ≥ 1
#guard test_x2_core.lo ≤ 0
#guard test_x2_core.hi ≥ 1

-- Test sin on [-1,1] should contain sin values
def test_sin_dyadic : IntervalRat :=
  (evalIntervalDyadic exprSin symEnvDyadic defaultDyadicCfg).toIntervalRat

def test_sin_core : IntervalRat :=
  evalIntervalCore exprSin symEnvCore defaultCoreCfg

-- sin([-1,1]) should contain sin(-1) ≈ -0.84 and sin(1) ≈ 0.84
#guard test_sin_dyadic.lo ≤ -1/2
#guard test_sin_dyadic.hi ≥ 1/2
#guard test_sin_core.lo ≤ -1/2
#guard test_sin_core.hi ≥ 1/2

-- Test exp on [0,1] should give interval containing [1, e] ≈ [1, 2.718]
def test_exp_dyadic : IntervalRat :=
  (evalIntervalDyadic exprExp unitEnvDyadic defaultDyadicCfg).toIntervalRat

def test_exp_core : IntervalRat :=
  evalIntervalCore exprExp unitEnvCore defaultCoreCfg

#guard test_exp_dyadic.lo ≤ 1
#guard test_exp_dyadic.hi ≥ 2      -- e ≈ 2.718
#guard test_exp_core.lo ≤ 1
#guard test_exp_core.hi ≥ 2

-- Test tanh gives bounded interval [-1, 1]
def test_tanh_dyadic : IntervalRat :=
  (evalIntervalDyadic exprTanh symEnvDyadic defaultDyadicCfg).toIntervalRat

#guard test_tanh_dyadic.lo ≥ -1
#guard test_tanh_dyadic.hi ≤ 1

-- Test π gives interval containing 3.14...
def test_pi_dyadic : IntervalRat :=
  (evalIntervalDyadic exprPi unitEnvDyadic defaultDyadicCfg).toIntervalRat

def test_pi_core : IntervalRat :=
  evalIntervalCore exprPi unitEnvCore defaultCoreCfg

#guard test_pi_dyadic.lo ≤ 22/7   -- π ≈ 3.14159
#guard test_pi_dyadic.hi ≥ 3
#guard test_pi_core.lo ≤ 22/7
#guard test_pi_core.hi ≥ 3

-- Print results for verification
#eval IO.println s!"x² Dyadic: [{test_x2_dyadic.lo}, {test_x2_dyadic.hi}]"
#eval IO.println s!"x² Core:   [{test_x2_core.lo}, {test_x2_core.hi}]"
#eval IO.println s!"sin Dyadic: [{test_sin_dyadic.lo}, {test_sin_dyadic.hi}]"
#eval IO.println s!"exp Dyadic: [{test_exp_dyadic.lo}, {test_exp_dyadic.hi}]"
#eval IO.println s!"tanh Dyadic: [{test_tanh_dyadic.lo}, {test_tanh_dyadic.hi}]"
#eval IO.println s!"π Dyadic: [{test_pi_dyadic.lo}, {test_pi_dyadic.hi}]"

end NumericalAccuracy

/-! ### Section 3: Cross-Evaluator Consistency Tests

Verify that different evaluators give compatible (overlapping) results.
Due to different rounding strategies, exact equality isn't expected,
but intervals should overlap significantly.
-/

section CrossEvaluatorConsistency

-- Helper: check if two intervals overlap
def intervalsOverlap (I1 I2 : IntervalRat) : Bool :=
  I1.lo ≤ I2.hi && I2.lo ≤ I1.hi

-- Test: x² evaluations should overlap
def x2_dyadic := (evalIntervalDyadic exprX2 unitEnvDyadic defaultDyadicCfg).toIntervalRat
def x2_core := evalIntervalCore exprX2 unitEnvCore defaultCoreCfg

#guard intervalsOverlap x2_dyadic x2_core

-- Test: sin evaluations should overlap
def sin_dyadic := (evalIntervalDyadic exprSin symEnvDyadic defaultDyadicCfg).toIntervalRat
def sin_core := evalIntervalCore exprSin symEnvCore defaultCoreCfg

#guard intervalsOverlap sin_dyadic sin_core

-- Test: exp evaluations should overlap
def exp_dyadic := (evalIntervalDyadic exprExp unitEnvDyadic defaultDyadicCfg).toIntervalRat
def exp_core := evalIntervalCore exprExp unitEnvCore defaultCoreCfg

#guard intervalsOverlap exp_dyadic exp_core

-- Test: composed expression (exp(sin(x))) should overlap
def expsin_dyadic := (evalIntervalDyadic exprExpSin unitEnvDyadic defaultDyadicCfg).toIntervalRat
def expsin_core := evalIntervalCore exprExpSin unitEnvCore defaultCoreCfg

#guard intervalsOverlap expsin_dyadic expsin_core

#eval IO.println "✓ Cross-evaluator consistency tests passed"

end CrossEvaluatorConsistency

/-! ### Section 4: Correctness Theorem Accessibility

Verify that correctness theorems are still accessible and have the expected types.
These are type-checking tests - if they compile, the theorems are correctly defined.
-/

section CorrectnessTheorems

-- Dyadic correctness theorem
#check @evalIntervalDyadic_correct
-- Expected signature: ExprSupportedCore e → envMemDyadic → evalDomainValidDyadic → membership

-- Affine correctness theorem
#check @evalIntervalAffine_correct
-- Expected signature: ExprSupportedCore e → validNoise → envMemAffine → membership

-- Affine to interval correctness theorem
#check @evalIntervalAffine_toInterval_correct

-- Core correctness theorem
#check @evalIntervalCore_correct
-- Expected signature: ExprSupportedCore e → envMem → evalDomainValid → membership

-- Real evaluator correctness (noncomputable)
#check @evalIntervalReal_correct
-- Expected signature: ExprSupportedExt e → envMemReal → membership

-- Domain validity theorems
#check @evalDomainValidDyadic_of_ExprSupported
#check @evalDomainValidAffine_of_ExprSupported

-- Environment membership definitions
#check @envMemDyadic
#check @envMemAffine
#check @envMem
#check @envMemReal

end CorrectnessTheorems

/-! ### Section 5: Expression Support Tests

Verify that support predicates work correctly for our test expressions.
-/

section ExpressionSupport

-- Polynomial is supported in Core
example : ExprSupportedCore exprX2 := by
  unfold exprX2
  apply ExprSupportedCore.mul
  · exact ExprSupportedCore.var 0
  · exact ExprSupportedCore.var 0

-- sin is supported in Core
example : ExprSupportedCore exprSin := by
  unfold exprSin
  apply ExprSupportedCore.sin
  exact ExprSupportedCore.var 0

-- exp(sin(x)) is supported in Core
example : ExprSupportedCore exprExpSin := by
  unfold exprExpSin
  apply ExprSupportedCore.exp
  apply ExprSupportedCore.sin
  exact ExprSupportedCore.var 0

-- Multi-variable expression is supported
example : ExprSupportedCore exprSumSq := by
  unfold exprSumSq
  apply ExprSupportedCore.add
  · apply ExprSupportedCore.mul
    · exact ExprSupportedCore.var 0
    · exact ExprSupportedCore.var 0
  · apply ExprSupportedCore.mul
    · exact ExprSupportedCore.var 1
    · exact ExprSupportedCore.var 1

end ExpressionSupport

/-! ### Section 6: Domain Validity Definition Structure Tests

Verify the evalDomainValid predicates have the expected recursive structure.
-/

section DomainValidityStructure

-- Test that domain validity predicates can be pattern matched
-- This verifies their definition structure

-- For constants and vars, domain validity is True
example : evalDomainValidDyadic (Expr.const 1) unitEnvDyadic = True := rfl
example : evalDomainValidDyadic (Expr.var 0) unitEnvDyadic = True := rfl
example : evalDomainValid (Expr.const 1) unitEnvCore = True := rfl
example : evalDomainValid (Expr.var 0) unitEnvCore = True := rfl

-- For binary ops, domain validity is conjunction of subexpressions
example : evalDomainValidDyadic (Expr.add (Expr.var 0) (Expr.var 1)) twoVarEnvDyadic =
          (evalDomainValidDyadic (Expr.var 0) twoVarEnvDyadic ∧
           evalDomainValidDyadic (Expr.var 1) twoVarEnvDyadic) := rfl

example : evalDomainValid (Expr.add (Expr.var 0) (Expr.var 1)) twoVarEnvCore =
          (evalDomainValid (Expr.var 0) twoVarEnvCore ∧
           evalDomainValid (Expr.var 1) twoVarEnvCore) := rfl

-- For unary transcendentals, domain validity recurses
example : evalDomainValidDyadic (Expr.sin (Expr.var 0)) unitEnvDyadic =
          evalDomainValidDyadic (Expr.var 0) unitEnvDyadic := rfl

example : evalDomainValid (Expr.sin (Expr.var 0)) unitEnvCore =
          evalDomainValid (Expr.var 0) unitEnvCore := rfl

end DomainValidityStructure

/-! ### Section 7: Print Summary -/

#eval IO.println "═══════════════════════════════════════════════════════"
#eval IO.println "  Evaluator Regression Tests - All Checks Passed!"
#eval IO.println "═══════════════════════════════════════════════════════"
#eval IO.println ""
#eval IO.println "Tested evaluators:"
#eval IO.println "  • evalIntervalDyadic (IntervalEvalDyadic.lean)"
#eval IO.println "  • evalIntervalAffine (IntervalEvalAffine.lean)"
#eval IO.println "  • evalIntervalCore   (Eval/Core.lean)"
#eval IO.println "  • evalIntervalReal   (IntervalEvalReal.lean)"
#eval IO.println ""
#eval IO.println "Test categories:"
#eval IO.println "  ✓ API Consistency"
#eval IO.println "  ✓ Numerical Accuracy"
#eval IO.println "  ✓ Cross-Evaluator Consistency"
#eval IO.println "  ✓ Correctness Theorems"
#eval IO.println "  ✓ Expression Support"
#eval IO.println "  ✓ Domain Validity Structure"

end LeanCert.Test.EvaluatorRegression
