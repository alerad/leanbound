/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.AD.Computable
import Mathlib.Topology.Order.Monotone

/-!
# Golden Theorems for Monotonicity Verification

This file provides Golden Theorems for proving monotonicity properties of expressions
using automatic differentiation with interval arithmetic.

## Main definitions

### Boolean Checkers
* `checkStrictlyIncreasing` - Check if f'(x) > 0 for all x in I (strictly increasing)
* `checkStrictlyDecreasing` - Check if f'(x) < 0 for all x in I (strictly decreasing)

### Golden Theorems
* `verify_strictly_increasing` - Proves `StrictMonoOn f I` from positive derivative bounds
* `verify_strictly_decreasing` - Proves `StrictAntiOn f I` from negative derivative bounds

## Design

The approach uses automatic differentiation to compute interval bounds on derivatives:
1. Compute `dI := derivIntervalCore e I cfg` (interval containing all derivatives)
2. If `dI.lo > 0`, then f'(x) > 0 for all x ∈ I, so f is strictly increasing
3. If `dI.hi < 0`, then f'(x) < 0 for all x ∈ I, so f is strictly decreasing

The mathematical foundation is the Mean Value Theorem: if f' has consistent sign,
then f is monotonic.

## Usage

```lean
-- Prove exp is strictly increasing on [0, 1]
example : StrictMonoOn (fun x => Real.exp x) (Set.Icc 0 1) :=
  verify_strictly_increasing' Expr.exp.var0 (by decide)
    ⟨0, 1, by norm_num⟩ {} (by native_decide)
```
-/

namespace LeanCert.Validity

open LeanCert.Core LeanCert.Engine

/-! ### Boolean Checkers for Monotonicity -/

/-- Check if an expression is strictly increasing on an interval.
    Returns true if the derivative lower bound is strictly positive. -/
def checkStrictlyIncreasing (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  0 < (derivIntervalCore e I cfg).lo

/-- Check if an expression is strictly decreasing on an interval.
    Returns true if the derivative upper bound is strictly negative. -/
def checkStrictlyDecreasing (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  (derivIntervalCore e I cfg).hi < 0

/-! ### Golden Theorems for Monotonicity -/

/-- **Golden Theorem for Strictly Increasing Functions**

    If `checkStrictlyIncreasing e I cfg = true`, then the function defined by `e`
    is strictly increasing on `I`.

    This uses the Mean Value Theorem: if f'(x) > 0 for all x in the interior of I,
    then f is strictly monotone on I. -/
theorem verify_strictly_increasing (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    StrictMonoOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  simp only [checkStrictlyIncreasing, decide_eq_true_eq] at h_check
  have hpos : 0 < (derivIntervalCore e I cfg).lo := by exact_mod_cast h_check
  exact strictMonoOn_of_derivIntervalCore_pos e hsupp I cfg hpos

/-- **Golden Theorem for Strictly Decreasing Functions**

    If `checkStrictlyDecreasing e I cfg = true`, then the function defined by `e`
    is strictly decreasing on `I`. -/
theorem verify_strictly_decreasing (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e I cfg = true) :
    StrictAntiOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  simp only [checkStrictlyDecreasing, decide_eq_true_eq] at h_check
  have hneg : (derivIntervalCore e I cfg).hi < 0 := by exact_mod_cast h_check
  exact strictAntiOn_of_derivIntervalCore_neg e hsupp I cfg hneg

/-! ### Alternative Formulations

These theorems provide the monotonicity result in the form
`∀ x y ∈ I, x < y → f(x) < f(y)`, which may be more convenient for some applications. -/

/-- Strictly increasing: x < y implies f(x) < f(y) -/
theorem verify_strictly_increasing_lt (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi, ∀ y ∈ Set.Icc (I.lo : ℝ) I.hi,
      x < y → Expr.eval (fun _ => x) e < Expr.eval (fun _ => y) e := by
  have hmono := verify_strictly_increasing e hsupp I cfg h_check
  intro x hx y hy hxy
  exact hmono hx hy hxy

/-- Strictly decreasing: x < y implies f(x) > f(y) -/
theorem verify_strictly_decreasing_lt (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e I cfg = true) :
    ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi, ∀ y ∈ Set.Icc (I.lo : ℝ) I.hi,
      x < y → Expr.eval (fun _ => y) e < Expr.eval (fun _ => x) e := by
  have hmono := verify_strictly_decreasing e hsupp I cfg h_check
  intro x hx y hy hxy
  exact hmono hx hy hxy

/-! ### Weak Monotonicity from Strict Monotonicity

For completeness, we provide theorems that derive weak monotonicity (≤) from
the strict monotonicity checks. -/

/-- Monotone (weak): x ≤ y implies f(x) ≤ f(y) -/
theorem verify_monotone (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    MonotoneOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  have hstrict := verify_strictly_increasing e hsupp I cfg h_check
  exact hstrict.monotoneOn

/-- Antitone (weak): x ≤ y implies f(x) ≥ f(y) -/
theorem verify_antitone (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e I cfg = true) :
    AntitoneOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  have hstrict := verify_strictly_decreasing e hsupp I cfg h_check
  exact hstrict.antitoneOn

/-! ### Convenience Versions with Rational Endpoints

These versions take rational endpoints directly, avoiding the need to construct
an IntervalRat explicitly. -/

/-- Convenience version with explicit rational endpoints -/
theorem verify_strictly_increasing_rat (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e ⟨lo, hi, hle⟩ cfg = true) :
    StrictMonoOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (lo : ℝ) hi) :=
  verify_strictly_increasing e hsupp ⟨lo, hi, hle⟩ cfg h_check

/-- Convenience version with explicit rational endpoints -/
theorem verify_strictly_decreasing_rat (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e ⟨lo, hi, hle⟩ cfg = true) :
    StrictAntiOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (lo : ℝ) hi) :=
  verify_strictly_decreasing e hsupp ⟨lo, hi, hle⟩ cfg h_check

end LeanCert.Validity
