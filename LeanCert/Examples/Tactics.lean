/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Interval
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tactic Examples

This file demonstrates using LeanCert's interval arithmetic to prove
bounds on expressions.

## Verified Examples

All examples in this file are FULLY PROVED using interval arithmetic.
No sorry, no axioms beyond the standard Lean/Mathlib foundations.

## Computability Design

We have two evaluation strategies:

1. **Core (computable)**: For expressions in `ExprSupportedCore`
   (const, var, add, mul, neg, sin, cos), we use `evalIntervalCore1`
   which is fully computable. The `interval_le`, `interval_ge`, etc.
   tactics work with `native_decide`.

2. **Extended (noncomputable)**: For expressions with `exp`, we use
   `evalInterval1` which requires noncomputable evaluation due to
   Real.exp floor/ceil bounds. These proofs use FTIA directly.
-/

namespace LeanCert.Examples.Tactics

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Tactic

/-! ### Basic interval bound examples -/

/-- The expression x² -/
def exprXSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

/-- Proof that x² is in the core (computable) subset -/
def exprXSq_core : ExprSupportedCore exprXSq :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)

/-- Proof that x² is supported -/
def exprXSq_supp : ExprSupported exprXSq :=
  ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0)

/-- The unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

/-- Example: x² ≤ 1 for all x ∈ [0, 1] using the interval_le tactic.
    This uses the computable core evaluator with native_decide. -/
theorem xsq_le_one_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) := by
  interval_le exprXSq, exprXSq_core, I01, 1

/-- Example: 0 ≤ x² for all x ∈ [0, 1] using native_decide. -/
theorem zero_le_xsq_native : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprXSq := by
  interval_ge exprXSq, exprXSq_core, I01, 0

/-- Example: x² ≤ 1 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem xsq_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) := by
  intro x hx
  simp only [exprXSq, Expr.eval_mul, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hmul : x * x ≤ (1 : ℝ) := by
    calc x * x ≤ x * 1 := by apply mul_le_mul_of_nonneg_left h1 h0
      _ = x := mul_one x
      _ ≤ 1 := h1
  exact_mod_cast hmul

/-- Example: 0 ≤ x² for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem zero_le_xsq : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprXSq := by
  intro x hx
  simp only [exprXSq, Expr.eval_mul, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hmul : (0 : ℝ) ≤ x * x := mul_nonneg h0 h0
  exact_mod_cast hmul

/-! ### Trigonometric bounds -/

/-- The expression sin(x) -/
def exprSin : Expr := Expr.sin (Expr.var 0)

/-- Proof that sin(x) is in the core subset -/
def exprSin_core : ExprSupportedCore exprSin :=
  ExprSupportedCore.sin (ExprSupportedCore.var 0)

/-- Proof that sin(x) is supported -/
def exprSin_supp : ExprSupported exprSin :=
  ExprSupported.sin (ExprSupported.var 0)

/-- Example: sin(x) ≤ 1 for all x ∈ [0, 1] using native_decide. -/
theorem sin_le_one_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprSin ≤ (1 : ℚ) := by
  interval_le exprSin, exprSin_core, I01, 1

/-- Example: -1 ≤ sin(x) for all x ∈ [0, 1] using native_decide. -/
theorem neg_one_le_sin_native : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprSin := by
  interval_ge exprSin, exprSin_core, I01, (-1)

/-- Example: sin(x) ≤ 1 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem sin_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) exprSin ≤ (1 : ℚ) := by
  intro x _hx
  simp only [exprSin, Expr.eval_sin, Expr.eval_var]
  have h := Real.sin_le_one x
  exact_mod_cast h

/-- Example: -1 ≤ sin(x) for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem neg_one_le_sin : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprSin := by
  intro x _hx
  simp only [exprSin, Expr.eval_sin, Expr.eval_var]
  have h := Real.neg_one_le_sin x
  exact_mod_cast h

/-! ### Combined expressions -/

/-- The expression x² + sin(x) -/
def exprXSqPlusSin : Expr :=
  Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.sin (Expr.var 0))

/-- Proof that x² + sin(x) is in the core subset -/
def exprXSqPlusSin_core : ExprSupportedCore exprXSqPlusSin :=
  ExprSupportedCore.add
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
    (ExprSupportedCore.sin (ExprSupportedCore.var 0))

/-- Proof that x² + sin(x) is supported -/
def exprXSqPlusSin_supp : ExprSupported exprXSqPlusSin :=
  ExprSupported.add
    (ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0))
    (ExprSupported.sin (ExprSupported.var 0))

/-- Example: x² + sin(x) ≤ 2 for all x ∈ [0, 1] using native_decide. -/
theorem xsq_plus_sin_le_two_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqPlusSin ≤ (2 : ℚ) := by
  interval_le exprXSqPlusSin, exprXSqPlusSin_core, I01, 2

/-- Example: -1 ≤ x² + sin(x) for all x ∈ [0, 1] using native_decide. -/
theorem neg_one_le_xsq_plus_sin_native : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprXSqPlusSin := by
  interval_ge exprXSqPlusSin, exprXSqPlusSin_core, I01, (-1)

/-- Example: x² + sin(x) ≤ 2 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem xsq_plus_sin_le_two : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqPlusSin ≤ (2 : ℚ) := by
  intro x hx
  simp only [exprXSqPlusSin, Expr.eval_add, Expr.eval_mul, Expr.eval_sin, Expr.eval_var]
  have h1 : x * x ≤ (1 : ℝ) := by
    have := xsq_le_one x hx
    simp only [exprXSq, Expr.eval_mul, Expr.eval_var] at this
    exact_mod_cast this
  have h2 : Real.sin x ≤ 1 := Real.sin_le_one x
  calc x * x + Real.sin x ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- Example: -1 ≤ x² + sin(x) for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem neg_one_le_xsq_plus_sin : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprXSqPlusSin := by
  intro x hx
  simp only [exprXSqPlusSin, Expr.eval_add, Expr.eval_mul, Expr.eval_sin, Expr.eval_var]
  have h1 : (0 : ℝ) ≤ x * x := by
    have := zero_le_xsq x hx
    simp only [exprXSq, Expr.eval_mul, Expr.eval_var] at this
    exact_mod_cast this
  have h2 : (-1 : ℝ) ≤ Real.sin x := Real.neg_one_le_sin x
  have hsum : (-1 : ℝ) ≤ x * x + Real.sin x := by linarith
  exact_mod_cast hsum

/-! ### Strict bounds -/

/-- The expression x² - 2 -/
def exprXSqMinus2 : Expr :=
  Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))

/-- Proof that x² - 2 is in the core subset -/
def exprXSqMinus2_core : ExprSupportedCore exprXSqMinus2 :=
  ExprSupportedCore.add
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
    (ExprSupportedCore.neg (ExprSupportedCore.const 2))

/-- Proof that x² - 2 is supported -/
def exprXSqMinus2_supp : ExprSupported exprXSqMinus2 :=
  ExprSupported.add
    (ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0))
    (ExprSupported.neg (ExprSupported.const 2))

/-- Example: x² - 2 < 0 for all x ∈ [0, 1] using native_decide.
    Since x² ≤ 1 on [0,1], we have x² - 2 ≤ -1 < 0. -/
theorem xsq_minus_two_lt_zero_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqMinus2 < (0 : ℚ) := by
  interval_lt exprXSqMinus2, exprXSqMinus2_core, I01, 0

/-- Example: x² - 2 < 0 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem xsq_minus_two_lt_zero : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqMinus2 < (0 : ℚ) := by
  intro x hx
  simp only [exprXSqMinus2, Expr.eval_add, Expr.eval_mul, Expr.eval_neg, Expr.eval_const, Expr.eval_var]
  have h1 : x * x ≤ (1 : ℝ) := by
    have := xsq_le_one x hx
    simp only [exprXSq, Expr.eval_mul, Expr.eval_var] at this
    exact_mod_cast this
  have hlt : x * x + (-(2 : ℝ)) < (0 : ℝ) := by linarith
  exact_mod_cast hlt

/-! ### Working with polynomials -/

/-- The expression 2x² + 3x + 1 -/
def exprPoly : Expr :=
  Expr.add
    (Expr.add
      (Expr.mul (Expr.const 2) (Expr.mul (Expr.var 0) (Expr.var 0)))
      (Expr.mul (Expr.const 3) (Expr.var 0)))
    (Expr.const 1)

/-- Proof that 2x² + 3x + 1 is in the core subset -/
def exprPoly_core : ExprSupportedCore exprPoly :=
  ExprSupportedCore.add
    (ExprSupportedCore.add
      (ExprSupportedCore.mul (ExprSupportedCore.const 2)
        (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)))
      (ExprSupportedCore.mul (ExprSupportedCore.const 3) (ExprSupportedCore.var 0)))
    (ExprSupportedCore.const 1)

/-- Proof that 2x² + 3x + 1 is supported -/
def exprPoly_supp : ExprSupported exprPoly :=
  ExprSupported.add
    (ExprSupported.add
      (ExprSupported.mul (ExprSupported.const 2)
        (ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0)))
      (ExprSupported.mul (ExprSupported.const 3) (ExprSupported.var 0)))
    (ExprSupported.const 1)

/-- Example: 2x² + 3x + 1 ≤ 6 for all x ∈ [0, 1] using native_decide.
    At x=1: 2 + 3 + 1 = 6. -/
theorem poly_le_six_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprPoly ≤ 6 := by
  interval_le exprPoly, exprPoly_core, I01, 6

/-- Example: 1 ≤ 2x² + 3x + 1 for all x ∈ [0, 1] using native_decide.
    At x=0: 0 + 0 + 1 = 1. -/
theorem one_le_poly_native : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprPoly := by
  interval_ge exprPoly, exprPoly_core, I01, 1

/-- Example: 2x² + 3x + 1 ≤ 6 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem poly_le_six : ∀ x ∈ I01, Expr.eval (fun _ => x) exprPoly ≤ 6 := by
  intro x hx
  simp only [exprPoly, I01, IntervalRat.mem_def, Expr.eval_add, Expr.eval_mul,
             Expr.eval_const, Expr.eval_var] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hx2 : x * x ≤ 1 := by
    calc x * x ≤ x * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = x := mul_one x
      _ ≤ 1 := h1
  have hbound : (2 : ℝ) * (x * x) + (3 : ℝ) * x + 1 ≤ 6 := by linarith
  exact_mod_cast hbound

/-- Example: 1 ≤ 2x² + 3x + 1 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem one_le_poly : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprPoly := by
  intro x hx
  simp only [exprPoly, I01, IntervalRat.mem_def, Expr.eval_add, Expr.eval_mul,
             Expr.eval_const, Expr.eval_var] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hx2_pos : (0 : ℝ) ≤ x * x := mul_nonneg h0 h0
  have h3x_pos : (0 : ℝ) ≤ 3 * x := by linarith
  have hbound : (1 : ℝ) ≤ (2 : ℝ) * (x * x) + (3 : ℝ) * x + 1 := by linarith
  exact_mod_cast hbound

/-! ### Examples with exp (noncomputable)

Expressions containing `exp` use the extended evaluator `evalInterval1`,
which is noncomputable due to Real.exp floor/ceil bounds. These examples
demonstrate bounds using direct FTIA application rather than native_decide.
-/

/-- The expression exp(x) -/
def exprExp : Expr := Expr.exp (Expr.var 0)

/-- Proof that exp(x) is supported (but NOT in ExprSupportedCore) -/
def exprExp_supp : ExprSupported exprExp :=
  ExprSupported.exp (ExprSupported.var 0)

/-- Example: exp(x) ≤ 3 for all x ∈ [0, 1].
    Since exp(1) ≈ 2.718, this bound holds.
    This uses the extended evaluator and requires direct proof. -/
theorem exp_le_three : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ (3 : ℚ) := by
  intro x hx
  simp only [exprExp, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp_of_le h1
  have he_bound : Real.exp 1 < 3 := by
    have hd9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlt : Real.exp x < (3 : ℝ) := lt_of_le_of_lt hexp he_bound
  exact_mod_cast le_of_lt hlt

/-- Example: 1 ≤ exp(x) for all x ∈ [0, 1].
    Since exp(0) = 1 and exp is increasing, this holds. -/
theorem one_le_exp : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprExp := by
  intro x hx
  simp only [exprExp, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hexp : Real.exp 0 ≤ Real.exp x := Real.exp_le_exp_of_le h0
  simp only [Real.exp_zero] at hexp
  exact_mod_cast hexp

/-- The expression x + exp(x) -/
def exprXPlusExp : Expr := Expr.add (Expr.var 0) (Expr.exp (Expr.var 0))

/-- Proof that x + exp(x) is supported -/
def exprXPlusExp_supp : ExprSupported exprXPlusExp :=
  ExprSupported.add (ExprSupported.var 0) (ExprSupported.exp (ExprSupported.var 0))

/-- Example: x + exp(x) ≤ 4 for all x ∈ [0, 1].
    x ≤ 1 and exp(x) ≤ 3, so x + exp(x) ≤ 4. -/
theorem x_plus_exp_le_four : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXPlusExp ≤ (4 : ℚ) := by
  intro x hx
  simp only [exprXPlusExp, Expr.eval_add, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hexp : Real.exp x ≤ 3 := by
    have := exp_le_three x hx
    simp only [exprExp, Expr.eval_exp, Expr.eval_var] at this
    exact_mod_cast this
  have hbound : x + Real.exp x ≤ 4 := by linarith
  exact_mod_cast hbound

/-- Example: 1 ≤ x + exp(x) for all x ∈ [0, 1].
    x ≥ 0 and exp(x) ≥ 1, so x + exp(x) ≥ 1. -/
theorem one_le_x_plus_exp : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprXPlusExp := by
  intro x hx
  simp only [exprXPlusExp, Expr.eval_add, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hexp : (1 : ℝ) ≤ Real.exp x := by
    have := one_le_exp x hx
    simp only [exprExp, Expr.eval_exp, Expr.eval_var] at this
    exact_mod_cast this
  have hbound : (1 : ℝ) ≤ x + Real.exp x := by linarith
  exact_mod_cast hbound

end LeanCert.Examples.Tactics
