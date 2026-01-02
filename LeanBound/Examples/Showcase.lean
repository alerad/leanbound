/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Tactic.IntervalAuto
import LeanBound.Tactic.Discovery

/-!
# LeanBound Showcase

Demonstrations of verified numerical computation in Lean 4.

## What This Library Does

LeanBound proves facts about real-valued functions using **interval arithmetic**.
The key idea: compute with rational intervals, get proofs about reals.

## Highlights

1. **Transcendental bounds**: exp, sin, cos with Taylor model error bounds
2. **Root existence**: Prove √2 exists via sign change
3. **Root absence**: Prove functions stay away from zero
4. **Composition**: Combine operations freely

## The Golden Theorem Pattern

Each verified result follows this pattern:
1. Build an `Expr` (expression AST) or use raw Lean syntax
2. Run interval evaluation → get rational bounds
3. Use `native_decide` to check the bound
4. Golden theorem lifts to a proof about reals
-/

namespace LeanBound.Examples.Showcase

open LeanBound.Core
open LeanBound.Numerics

/-! ## Intervals -/

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def I_sym : IntervalRat := ⟨-1, 1, by norm_num⟩

/-! ## Section 1: Basic Polynomial Bounds

Simple examples showing interval_bound on polynomials.
-/

/-- x² ≤ 1 on [0, 1] -/
theorem xsq_le_one : ∀ x ∈ I01, x * x ≤ (1 : ℚ) := by
  interval_bound

/-- 0 ≤ x² on [0, 1] -/
theorem zero_le_xsq : ∀ x ∈ I01, (0 : ℚ) ≤ x * x := by
  interval_bound

/-- x² ≤ 1 on [-1, 1] -/
theorem xsq_le_one_sym : ∀ x ∈ I_sym, x * x ≤ (1 : ℚ) := by
  interval_bound

/-! ## Section 2: Transcendental Functions

exp, sin, cos with verified Taylor series bounds.
-/

/-- sin(x) ≤ 1 on [0, 1] -/
theorem sin_le_one : ∀ x ∈ I01, Real.sin x ≤ (1 : ℚ) := by
  interval_bound

/-- -1 ≤ sin(x) on [0, 1] -/
theorem neg_one_le_sin : ∀ x ∈ I01, (-1 : ℚ) ≤ Real.sin x := by
  interval_bound

/-- cos(x) ≤ 1 on [0, 1] -/
theorem cos_le_one : ∀ x ∈ I01, Real.cos x ≤ (1 : ℚ) := by
  interval_bound

/-- exp(x) ≤ 3 on [0, 1] -/
theorem exp_le_three : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by
  interval_bound 15

/-- 1 ≤ exp(x) on [0, 1] - boundary case with monotonicity -/
theorem one_le_exp : ∀ x ∈ I01, (1 : ℚ) ≤ Real.exp x := by
  interval_bound 15

/-! ## Section 3: Combined Expressions

Mixing polynomials with transcendentals.
-/

/-- x² + sin(x) ≤ 2 on [0, 1] -/
theorem xsq_plus_sin_le_two : ∀ x ∈ I01, x * x + Real.sin x ≤ (2 : ℚ) := by
  interval_bound

/-- x² - 2 < 0 on [0, 1] (since √2 > 1) -/
theorem xsq_minus_two_neg : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) < (0 : ℚ) := by
  interval_bound

/-! ## Section 4: Root Absence

Prove functions have no roots by showing they stay strictly positive/negative.
-/

/-- x² + 1 ≠ 0 on [0, 1] (always positive) -/
theorem xsq_plus_one_no_root : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.const 1)) ≠ (0 : ℝ) := by
  root_bound

/-- exp(x) ≠ 0 on [0, 1] (always positive) -/
theorem exp_no_root : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) ≠ (0 : ℝ) := by
  root_bound 15

/-- x + 2 ≠ 0 on [0, 1] (always positive) -/
theorem x_plus_two_no_root : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.var 0) (Expr.const 2)) ≠ (0 : ℝ) := by
  root_bound

/-- x² - 2 ≠ 0 on [0, 1] (√2 ≈ 1.41 is outside [0,1]) -/
theorem xsq_minus_two_no_root : ∀ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) ≠ (0 : ℝ) := by
  root_bound

/-! ## Section 5: Root Existence

Prove roots exist via sign change (Intermediate Value Theorem).
-/

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

/-- √2 exists: there is an x ∈ [1, 2] with x² = 2 -/
theorem sqrt2_exists : ∃ x ∈ I12,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

/-- π/2 exists: there is an x ∈ [1, 2] with cos(x) = 0 -/
theorem pi_half_exists : ∃ x ∈ I12,
    Expr.eval (fun _ => x) (Expr.cos (Expr.var 0)) = 0 := by
  interval_roots

/-- ln(2) exists: there is an x ∈ [0, 1] with exp(x) = 2 -/
theorem ln2_exists : ∃ x ∈ I01,
    Expr.eval (fun _ => x) (Expr.add (Expr.exp (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots 15

/-! ## Why This Matters

1. **Verified**: Every bound is machine-checked by Lean's kernel
2. **Computational**: Bounds computed at compile time via `native_decide`
3. **Composable**: Build complex proofs from simple pieces
4. **Automated**: Tactics handle boilerplate

The library automates numerical verification where symbolic methods are tedious.
-/

end LeanBound.Examples.Showcase
