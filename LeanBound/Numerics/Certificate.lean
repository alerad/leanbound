/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.IntervalEval
import LeanBound.Numerics.AD
import LeanBound.Numerics.Optimization.Global
import LeanBound.Numerics.RootFinding.Main
import LeanBound.Numerics.Integrate
import LeanBound.Meta.ProveContinuous

/-!
# Certificate-Driven Verification

This file provides the infrastructure for certificate-driven verification of
numerical bounds. Instead of Lean searching for a proof, an external agent
(e.g., Python) provides a **Certificate** containing:
- `Expr`: The function f(x)
- `Domain`: The interval I
- `Claim`: E.g., f(I) ⊆ [a, b]
- `ProofParams`: Parameters like Taylor series depth

If the agent determines that exp(x) needs 20 Taylor terms to satisfy a bound,
it passes `taylorDepth := 20` to Lean. Lean runs the computation with that
depth and checks the boolean result via `native_decide`.

## Main definitions

### Boolean Checkers
* `checkUpperBound` - Check if `∀ x ∈ I, f(x) ≤ c` via interval arithmetic
* `checkLowerBound` - Check if `∀ x ∈ I, c ≤ f(x)` via interval arithmetic
* `checkStrictUpperBound` - Check if `∀ x ∈ I, f(x) < c`
* `checkStrictLowerBound` - Check if `∀ x ∈ I, c < f(x)`

### Golden Theorems
* `verify_upper_bound` - Converts `checkUpperBound = true` to semantic proof
* `verify_lower_bound` - Converts `checkLowerBound = true` to semantic proof
* `verify_strict_upper_bound` - Converts `checkStrictUpperBound = true` to semantic proof
* `verify_strict_lower_bound` - Converts `checkStrictLowerBound = true` to semantic proof

## Design

The boolean checkers are fully computable and can be evaluated by `native_decide`.
The golden theorems bridge the gap between the boolean result and the semantic
proof about real numbers.

## Usage

### Manual usage (before tactic implementation):
```lean
example : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ 3 :=
  verify_upper_bound exprExp exprExp_core I01 3 { taylorDepth := 15 } (by native_decide)
```

### RPC workflow:
1. Python receives a request: "Prove x·e^x ≤ 5 on [0, 1.2]"
2. Python runs its own fast implementation to find sufficient depth (e.g., 15)
3. Python generates Lean code with the certificate:
   ```lean
   verify_upper_bound myExpr myExpr_core I_0_1_2 5 { taylorDepth := 15 } (by native_decide)
   ```
4. Lean executes, running `evalIntervalCore` with depth 15, checks boolean, closes goal
-/

namespace LeanBound.Numerics.Certificate

open LeanBound.Core
open LeanBound.Numerics

/-! ### Boolean Checkers

These are the functions `native_decide` will execute. They return `Bool`, not `Prop`.
-/

/-- Check if an expression is bounded above by `c` on interval `I`.
    Returns `true` iff the computed upper bound of `evalIntervalCore1 e I cfg` is ≤ c. -/
def checkUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  decide ((evalIntervalCore1 e I cfg).hi ≤ c)

/-- Check if an expression is bounded below by `c` on interval `I`.
    Returns `true` iff the computed lower bound of `evalIntervalCore1 e I cfg` is ≥ c. -/
def checkLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  decide (c ≤ (evalIntervalCore1 e I cfg).lo)

/-- Check if an expression is strictly bounded above by `c` on interval `I`.
    Returns `true` iff the computed upper bound of `evalIntervalCore1 e I cfg` is < c. -/
def checkStrictUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  decide ((evalIntervalCore1 e I cfg).hi < c)

/-- Check if an expression is strictly bounded below by `c` on interval `I`.
    Returns `true` iff the computed lower bound of `evalIntervalCore1 e I cfg` is > c. -/
def checkStrictLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  decide (c < (evalIntervalCore1 e I cfg).lo)

/-! ### Golden Theorems

These theorems convert the boolean `true` from the checkers into semantic proofs
about Real numbers. They are the theorems a tactic will `apply`.
-/

/-- **Golden Theorem for Upper Bounds**

    If `checkUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c`.

    This is the key theorem for certificate-driven verification of upper bounds.
    The proof uses:
    1. The boolean check ensures `(evalIntervalCore1 e I cfg).hi ≤ c`
    2. The fundamental correctness theorem ensures `Expr.eval ... e ≤ hi`
    3. Transitivity gives `Expr.eval ... e ≤ c` -/
theorem verify_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  -- Unpack the boolean check
  simp only [checkUpperBound, decide_eq_true_eq] at h_cert
  -- Apply the tactic-facing lemma which handles the FTIA + transitivity
  exact exprCore_le_of_interval_hi e hsupp I c cfg h_cert

/-- **Golden Theorem for Lower Bounds**

    If `checkLowerBound e I c cfg = true`, then `∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e`.

    This is the key theorem for certificate-driven verification of lower bounds.
    The proof uses:
    1. The boolean check ensures `c ≤ (evalIntervalCore1 e I cfg).lo`
    2. The fundamental correctness theorem ensures `lo ≤ Expr.eval ... e`
    3. Transitivity gives `c ≤ Expr.eval ... e` -/
theorem verify_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBound, decide_eq_true_eq] at h_cert
  exact exprCore_ge_of_interval_lo e hsupp I c cfg h_cert

/-- **Golden Theorem for Strict Upper Bounds**

    If `checkStrictUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e < c`. -/
theorem verify_strict_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBound, decide_eq_true_eq] at h_cert
  exact exprCore_lt_of_interval_hi_lt e hsupp I c cfg h_cert

/-- **Golden Theorem for Strict Lower Bounds**

    If `checkStrictLowerBound e I c cfg = true`, then `∀ x ∈ I, c < Expr.eval (fun _ => x) e`. -/
theorem verify_strict_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e I c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBound, decide_eq_true_eq] at h_cert
  exact exprCore_gt_of_interval_lo_gt e hsupp I c cfg h_cert

/-! ### Convenience lemmas for pointwise bounds -/

/-- Pointwise upper bound: if check passes and x ∈ I, then f(x) ≤ c -/
theorem verify_upper_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkUpperBound e I c cfg = true) :
    Expr.eval (fun _ => x) e ≤ c :=
  verify_upper_bound e hsupp I c cfg h_cert x hx

/-- Pointwise lower bound: if check passes and x ∈ I, then c ≤ f(x) -/
theorem verify_lower_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkLowerBound e I c cfg = true) :
    c ≤ Expr.eval (fun _ => x) e :=
  verify_lower_bound e hsupp I c cfg h_cert x hx

/-! ### Two-sided bounds -/

/-- Check both lower and upper bounds simultaneously -/
def checkBounds (e : Expr) (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig) : Bool :=
  checkLowerBound e I lo cfg && checkUpperBound e I hi cfg

/-- Two-sided bound verification: if both checks pass, then lo ≤ f(x) ≤ hi for all x ∈ I -/
theorem verify_bounds (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig)
    (h_cert : checkBounds e I lo hi cfg = true) :
    ∀ x ∈ I, lo ≤ Expr.eval (fun _ => x) e ∧ Expr.eval (fun _ => x) e ≤ hi := by
  simp only [checkBounds, Bool.and_eq_true] at h_cert
  intro x hx
  exact ⟨verify_lower_bound e hsupp I lo cfg h_cert.1 x hx,
         verify_upper_bound e hsupp I hi cfg h_cert.2 x hx⟩

/-! ### Smart Bounds with Monotonicity

These checkers use derivative information to get tighter bounds at interval endpoints.
If the function is monotonic on the interval, we can evaluate at the appropriate
endpoint to get an exact bound, avoiding Taylor series remainder widening.
-/

/-- Smart lower bound check using monotonicity.
    1. Tries standard interval check first (fastest).
    2. If fails, computes derivative interval.
    3. If derivative > 0 (increasing), checks if f(I.lo) ≥ c.
    4. If derivative < 0 (decreasing), checks if f(I.hi) ≥ c. -/
def checkLowerBoundSmart (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  -- 1. Try standard check first (fastest)
  if checkLowerBound e I c cfg then true
  else
    -- 2. Compute derivative bounds
    let dI := derivIntervalCore e I cfg
    if 0 < dI.lo then
      -- Strictly increasing: minimum is at lo
      -- Evaluate at singleton lo
      c ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo
    else if dI.hi < 0 then
      -- Strictly decreasing: minimum is at hi
      c ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo
    else
      false

/-- Smart upper bound check using monotonicity.
    1. Tries standard interval check first.
    2. If fails, computes derivative interval.
    3. If derivative > 0 (increasing), checks if f(I.hi) ≤ c.
    4. If derivative < 0 (decreasing), checks if f(I.lo) ≤ c. -/
def checkUpperBoundSmart (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  if checkUpperBound e I c cfg then true
  else
    let dI := derivIntervalCore e I cfg
    if 0 < dI.lo then
      -- Increasing: max at hi
      (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi ≤ c
    else if dI.hi < 0 then
      -- Decreasing: max at lo
      (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi ≤ c
    else
      false

/-! ### Smart Golden Theorems -/

/-- Helper: For increasing functions, the minimum is at the left endpoint -/
theorem increasing_min_at_left_core (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => I.lo) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  -- Use the MVT: f(x) - f(lo) = f'(ξ) * (x - lo) for some ξ ∈ (lo, x)
  -- Since f' > 0 and x ≥ lo, we have f(x) ≥ f(lo)
  have hsupp' := hsupp.toSupported
  have hdiff := evalFunc1_differentiable e hsupp'
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · -- x > lo since x ∈ I and x ≠ lo
    have hlo_le_x : (I.lo : ℝ) ≤ x := by
      simp only [IntervalRat.mem_def] at hx; exact hx.1
    have hlo_lt_x : (I.lo : ℝ) < x := lt_of_le_of_ne hlo_le_x heq
    -- Apply MVT
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hlo_lt_x
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    -- ξ ∈ (lo, x) ⊆ I, so deriv f ξ ∈ derivIntervalCore
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_of_lt hξ_mem.1
      · exact le_trans (le_of_lt hξ_mem.2) hx.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    -- deriv f ξ > 0
    have hderiv_pos : deriv (evalFunc1 e) ξ > 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≥ (derivIntervalCore e I cfg).lo := hderiv.1
        _ > 0 := by exact_mod_cast hpos
    -- slope = deriv f ξ > 0, so f(x) > f(lo)
    have hslope_pos : (evalFunc1 e x - evalFunc1 e I.lo) / (x - I.lo) > 0 := by
      rw [← hξ_eq]; exact hderiv_pos
    have hdiff_pos : x - (I.lo : ℝ) > 0 := sub_pos.mpr hlo_lt_x
    have hnum_pos : evalFunc1 e x - evalFunc1 e I.lo > 0 := by
      have := div_pos_iff.mp hslope_pos
      cases this with
      | inl h => exact h.1
      | inr h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
    simp only [evalFunc1] at hnum_pos ⊢
    linarith

/-- Helper: For decreasing functions, the minimum is at the right endpoint -/
theorem decreasing_min_at_right_core (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => I.hi) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hsupp' := hsupp.toSupported
  have hdiff := evalFunc1_differentiable e hsupp'
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · have hx_le_hi : x ≤ (I.hi : ℝ) := by
      simp only [IntervalRat.mem_def] at hx; exact hx.2
    have hx_lt_hi : x < (I.hi : ℝ) := lt_of_le_of_ne hx_le_hi heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hx_lt_hi
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_trans hx.1 (le_of_lt hξ_mem.1)
      · exact le_of_lt hξ_mem.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_neg : deriv (evalFunc1 e) ξ < 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≤ (derivIntervalCore e I cfg).hi := hderiv.2
        _ < 0 := by exact_mod_cast hneg
    have hslope_neg : (evalFunc1 e I.hi - evalFunc1 e x) / ((I.hi : ℝ) - x) < 0 := by
      rw [← hξ_eq]; exact hderiv_neg
    have hdiff_pos : (I.hi : ℝ) - x > 0 := sub_pos.mpr hx_lt_hi
    have hnum_neg : evalFunc1 e I.hi - evalFunc1 e x < 0 := by
      have := div_neg_iff.mp hslope_neg
      cases this with
      | inl h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
      | inr h => exact h.1
    simp only [evalFunc1] at hnum_neg ⊢
    linarith

/-- Smart lower bound verification using monotonicity -/
theorem verify_lower_bound_smart (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  unfold checkLowerBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_lower_bound e hsupp I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing)
      rename_i h_pos
      intro x hx
      have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
      have heval := evalIntervalCore1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_mem cfg
      simp only [IntervalRat.mem_def] at heval
      have hmono := increasing_min_at_left_core e hsupp I cfg h_pos x hx
      simp only [decide_eq_true_eq] at h_cert
      calc (c : ℝ) ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo := by exact_mod_cast h_cert
        _ ≤ Expr.eval (fun _ => I.lo) e := heval.1
        _ ≤ Expr.eval (fun _ => x) e := hmono
    · -- Not increasing, split on decreasing condition
      rename_i h_pos_neg
      split at h_cert
      · -- Case 3: Derivative strictly negative (decreasing)
        rename_i h_neg
        intro x hx
        have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
        have heval := evalIntervalCore1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_mem cfg
        simp only [IntervalRat.mem_def] at heval
        have hmono := decreasing_min_at_right_core e hsupp I cfg h_neg x hx
        simp only [decide_eq_true_eq] at h_cert
        calc (c : ℝ) ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo := by exact_mod_cast h_cert
          _ ≤ Expr.eval (fun _ => I.hi) e := heval.1
          _ ≤ Expr.eval (fun _ => x) e := hmono
      · -- Neither increasing nor decreasing => impossible since h_cert = true
        exact absurd h_cert Bool.false_ne_true

/-- Helper: For increasing functions, the maximum is at the right endpoint -/
theorem increasing_max_at_right_core (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.hi) e := by
  intro x hx
  have hsupp' := hsupp.toSupported
  have hdiff := evalFunc1_differentiable e hsupp'
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · have hx_le_hi : x ≤ (I.hi : ℝ) := by
      simp only [IntervalRat.mem_def] at hx; exact hx.2
    have hx_lt_hi : x < (I.hi : ℝ) := lt_of_le_of_ne hx_le_hi heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hx_lt_hi
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_trans hx.1 (le_of_lt hξ_mem.1)
      · exact le_of_lt hξ_mem.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_pos : deriv (evalFunc1 e) ξ > 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≥ (derivIntervalCore e I cfg).lo := hderiv.1
        _ > 0 := by exact_mod_cast hpos
    have hslope_pos : (evalFunc1 e I.hi - evalFunc1 e x) / ((I.hi : ℝ) - x) > 0 := by
      rw [← hξ_eq]; exact hderiv_pos
    have hdiff_pos : (I.hi : ℝ) - x > 0 := sub_pos.mpr hx_lt_hi
    have hnum_pos : evalFunc1 e I.hi - evalFunc1 e x > 0 := by
      have := div_pos_iff.mp hslope_pos
      cases this with
      | inl h => exact h.1
      | inr h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
    simp only [evalFunc1] at hnum_pos ⊢
    linarith

/-- Helper: For decreasing functions, the maximum is at the left endpoint -/
theorem decreasing_max_at_left_core (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.lo) e := by
  intro x hx
  have hsupp' := hsupp.toSupported
  have hdiff := evalFunc1_differentiable e hsupp'
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · have hlo_le_x : (I.lo : ℝ) ≤ x := by
      simp only [IntervalRat.mem_def] at hx; exact hx.1
    have hlo_lt_x : (I.lo : ℝ) < x := lt_of_le_of_ne hlo_le_x heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hlo_lt_x
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_of_lt hξ_mem.1
      · exact le_trans (le_of_lt hξ_mem.2) hx.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_neg : deriv (evalFunc1 e) ξ < 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≤ (derivIntervalCore e I cfg).hi := hderiv.2
        _ < 0 := by exact_mod_cast hneg
    have hslope_neg : (evalFunc1 e x - evalFunc1 e I.lo) / (x - I.lo) < 0 := by
      rw [← hξ_eq]; exact hderiv_neg
    have hdiff_pos : x - (I.lo : ℝ) > 0 := sub_pos.mpr hlo_lt_x
    have hnum_neg : evalFunc1 e x - evalFunc1 e I.lo < 0 := by
      have := div_neg_iff.mp hslope_neg
      cases this with
      | inl h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
      | inr h => exact h.1
    simp only [evalFunc1] at hnum_neg ⊢
    linarith

/-- Smart upper bound verification using monotonicity -/
theorem verify_upper_bound_smart (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  unfold checkUpperBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_upper_bound e hsupp I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing), max at hi
      rename_i h_pos
      intro x hx
      have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
      have heval := evalIntervalCore1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_mem cfg
      simp only [IntervalRat.mem_def] at heval
      have hmono := increasing_max_at_right_core e hsupp I cfg h_pos x hx
      simp only [decide_eq_true_eq] at h_cert
      calc Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.hi) e := hmono
        _ ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi := heval.2
        _ ≤ c := by exact_mod_cast h_cert
    · -- Not increasing, split on decreasing condition
      rename_i h_pos_neg
      split at h_cert
      · -- Case 3: Derivative strictly negative (decreasing), max at lo
        rename_i h_neg
        intro x hx
        have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
        have heval := evalIntervalCore1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_mem cfg
        simp only [IntervalRat.mem_def] at heval
        have hmono := decreasing_max_at_left_core e hsupp I cfg h_neg x hx
        simp only [decide_eq_true_eq] at h_cert
        calc Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.lo) e := hmono
          _ ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi := heval.2
          _ ≤ c := by exact_mod_cast h_cert
      · -- Neither increasing nor decreasing => impossible since h_cert = true
        exact absurd h_cert Bool.false_ne_true

/-! ### Set.Icc Bridge Theorems

These theorems bridge between IntervalRat-based proofs and Set.Icc goals,
allowing tactics to work with the more natural Set.Icc syntax.
-/

/-- Bridge from IntervalRat proof to Set.Icc upper bound goal -/
theorem verify_upper_bound_Icc (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc lower bound goal -/
theorem verify_lower_bound_Icc (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

end LeanBound.Numerics.Certificate

/-! ## Global Optimization Certificates

These checkers and theorems extend the certificate pattern to multivariate
global optimization over n-dimensional boxes.
-/

namespace LeanBound.Numerics.Certificate.GlobalOpt

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Optimization

/-! ### Boolean Checkers for Global Optimization -/

/-- Check if `c` is a lower bound for `e` over box `B`.
    Returns `true` iff `globalMinimizeCore(e, B, cfg).bound.lo ≥ c`. -/
def checkGlobalLowerBound (e : Expr) (B : Box) (c : ℚ) (cfg : GlobalOptConfig) : Bool :=
  decide (c ≤ (globalMinimizeCore e B cfg).bound.lo)

/-- Check if `c` is an upper bound for `e` over box `B`.
    Returns `true` iff `globalMaximizeCore(e, B, cfg).bound.hi ≤ c`.
    (i.e., the upper bound on max(e) is ≤ c, which proves ∀ρ, e(ρ) ≤ c)

    Note: bound.hi = -globalMinimizeCore(-e).bound.lo, and by correctness
    globalMinimizeCore(-e).bound.lo ≤ -e(ρ) for all ρ, so e(ρ) ≤ bound.hi. -/
def checkGlobalUpperBound (e : Expr) (B : Box) (c : ℚ) (cfg : GlobalOptConfig) : Bool :=
  decide ((globalMaximizeCore e B cfg).bound.hi ≤ c)

/-- Check both lower and upper bounds for global optimization -/
def checkGlobalBounds (e : Expr) (B : Box) (lo hi : ℚ) (cfg : GlobalOptConfig) : Bool :=
  checkGlobalLowerBound e B lo cfg && checkGlobalUpperBound e B hi cfg

/-! ### Golden Theorems for Global Optimization -/

/-- **Golden Theorem for Global Lower Bounds**

    If `checkGlobalLowerBound e B c cfg = true`, then `∀ ρ ∈ B, c ≤ Expr.eval ρ e`.

    This converts the boolean certificate into a semantic proof about all points
    in the box.

    Note: This uses ExprSupportedCore (the computable subset) rather than ExprSupported,
    since the checker uses globalMinimizeCore which uses evalIntervalCore. -/
theorem verify_global_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (c : ℚ) (cfg : GlobalOptConfig)
    (h_cert : checkGlobalLowerBound e B c cfg = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      c ≤ Expr.eval ρ e := by
  simp only [checkGlobalLowerBound, decide_eq_true_eq] at h_cert
  intro ρ hρ hzero
  -- Use globalMinimizeCore correctness theorem directly
  have hlo := globalMinimizeCore_lo_correct e hsupp B cfg ρ hρ hzero
  calc (c : ℝ) ≤ (globalMinimizeCore e B cfg).bound.lo := by exact_mod_cast h_cert
    _ ≤ Expr.eval ρ e := hlo

/-- **Golden Theorem for Global Upper Bounds**

    If `checkGlobalUpperBound e B c cfg = true`, then `∀ ρ ∈ B, Expr.eval ρ e ≤ c`.

    The maximization problem is reduced to minimization of -e.

    Note: This uses ExprSupportedCore (the computable subset) rather than ExprSupported,
    since the checker uses globalMaximizeCore which uses evalIntervalCore. -/
theorem verify_global_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (c : ℚ) (cfg : GlobalOptConfig)
    (h_cert : checkGlobalUpperBound e B c cfg = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ c := by
  simp only [checkGlobalUpperBound, decide_eq_true_eq] at h_cert
  intro ρ hρ hzero
  -- h_cert : globalMaximizeCore(e).bound.hi ≤ c
  -- globalMaximizeCore(e).bound.hi = -globalMinimizeCore(-e).bound.lo
  -- From globalMinimizeCore_lo_correct for -e:
  --   globalMinimizeCore(-e).bound.lo ≤ -e(ρ) for all ρ
  --   i.e., e(ρ) ≤ -globalMinimizeCore(-e).bound.lo = globalMaximizeCore(e).bound.hi
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hlo_neg := globalMinimizeCore_lo_correct (Expr.neg e) hneg_supp B cfg ρ hρ hzero
  simp only [Expr.eval_neg] at hlo_neg
  -- hlo_neg : globalMinimizeCore(-e).bound.lo ≤ -e(ρ)
  -- i.e., e(ρ) ≤ -globalMinimizeCore(-e).bound.lo = globalMaximizeCore(e).bound.hi
  -- From hlo_neg: (lo : ℝ) ≤ -Expr.eval ρ e, so Expr.eval ρ e ≤ -(lo : ℝ)
  have heval_bound : Expr.eval ρ e ≤ -((globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := by
    linarith
  -- globalMaximizeCore(e).bound.hi = -(globalMinimizeCore(-e).bound.lo)
  have hhi_eq : ((globalMaximizeCore e B cfg).bound.hi : ℝ) =
                -((globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := by
    simp only [globalMaximizeCore]
    push_cast
    ring
  calc Expr.eval ρ e
      ≤ -((globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := heval_bound
    _ = ((globalMaximizeCore e B cfg).bound.hi : ℝ) := hhi_eq.symm
    _ ≤ c := by exact_mod_cast h_cert

/-- Two-sided global bound verification -/
theorem verify_global_bounds (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (lo hi : ℚ) (cfg : GlobalOptConfig)
    (h_cert : checkGlobalBounds e B lo hi cfg = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      lo ≤ Expr.eval ρ e ∧ Expr.eval ρ e ≤ hi := by
  simp only [checkGlobalBounds, Bool.and_eq_true] at h_cert
  intro ρ hρ hzero
  exact ⟨verify_global_lower_bound e hsupp B lo cfg h_cert.1 ρ hρ hzero,
         verify_global_upper_bound e hsupp B hi cfg h_cert.2 ρ hρ hzero⟩

end LeanBound.Numerics.Certificate.GlobalOpt

/-! ## Root Finding Certificates

These checkers and theorems provide certificate-driven verification for
root existence and uniqueness.
-/

namespace LeanBound.Numerics.Certificate.RootFinding

open LeanBound.Core
open LeanBound.Numerics

/-! ### Configuration for root finding certificates -/

/-- Configuration for root-finding checks -/
structure RootConfig where
  /-- Maximum bisection depth -/
  maxDepth : Nat := 20
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr, Inhabited

/-- Configuration for Newton uniqueness checks -/
structure NewtonConfig where
  /-- Number of Newton iterations -/
  iterations : Nat := 5
  /-- Taylor model degree -/
  tmDegree : Nat := 1
  deriving Repr, Inhabited

/-! ### Boolean Checkers for Root Finding -/

/-- Check if expression has a sign change on interval (indicating a root).
    Uses interval arithmetic to check if f(lo) and f(hi) have opposite signs. -/
def checkSignChange (e : Expr) (I : IntervalRat) (cfg : EvalConfig) : Bool :=
  -- Evaluate f at endpoints
  let f_lo := evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg
  let f_hi := evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg
  -- Opposite signs: f_lo.hi < 0 and f_hi.lo > 0, or f_lo.lo > 0 and f_hi.hi < 0
  (f_lo.hi < 0 && 0 < f_hi.lo) || (f_hi.hi < 0 && 0 < f_lo.lo)

/-- Check if interval definitely has no root (function has constant sign).
    Returns `true` if the function's interval evaluation doesn't contain 0. -/
def checkNoRoot (e : Expr) (I : IntervalRat) (cfg : EvalConfig) : Bool :=
  let fI := evalIntervalCore1 e I cfg
  fI.hi < 0 || 0 < fI.lo

/-! ### Computable Newton Step for Unique Root Verification -/

/-- Computable Newton step using `evalIntervalCore1` and `derivIntervalCore`.

    This is the computable equivalent of `newtonStepSimple`. It performs one
    interval Newton iteration: N(I) = c - f(c)/f'(I) where c = midpoint(I).

    Returns `none` if the derivative interval contains 0 (can't safely divide).
    Returns `some (I ∩ N)` otherwise. -/
def newtonStepCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Option IntervalRat :=
  let c := I.midpoint
  -- Evaluate f(c) using singleton interval
  let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
  -- Get derivative interval on I
  let dI := derivIntervalCore e I cfg
  -- If derivative interval contains zero, we can't safely divide
  if hzero : IntervalRat.containsZero dI then
    none
  else
    let dNonzero : IntervalRat.IntervalRatNonzero :=
      { lo := dI.lo, hi := dI.hi, le := dI.le, nonzero := hzero }
    let dInv := IntervalRat.invNonzero dNonzero
    let Q := IntervalRat.mul fc dInv
    let N : IntervalRat :=
      { lo := c - Q.hi
        hi := c - Q.lo
        le := by linarith [Q.le] }
    IntervalRat.intersect I N

/-- Extract structure from newtonStepCore. -/
lemma newtonStepCore_extract (e : Expr) (I N : IntervalRat) (cfg : EvalConfig)
    (hCore : newtonStepCore e I cfg = some N) :
    let c := I.midpoint
    let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
    let dI := derivIntervalCore e I cfg
    ∃ (hdI_nonzero : ¬dI.containsZero),
      let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
      let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
      N.lo = max I.lo (c - Q.hi) ∧ N.hi = min I.hi (c - Q.lo) := by
  -- Unfold the definition of newtonStepCore
  unfold newtonStepCore at hCore
  -- The dite splits on containsZero
  by_cases hzero : (derivIntervalCore e I cfg).containsZero
  · -- If dI contains zero, newtonStepCore returns none, contradiction
    simp only [hzero, dite_true] at hCore
    exact Option.noConfusion hCore
  · -- If dI doesn't contain zero, we get an intersection
    simp only [hzero, dite_false] at hCore
    use hzero
    -- hCore : IntervalRat.intersect I ⟨c - Q.hi, c - Q.lo, _⟩ = some N
    simp only [IntervalRat.intersect] at hCore
    split at hCore
    · -- The intersection succeeded
      rename_i hintersect
      simp only [Option.some.injEq] at hCore
      constructor
      · exact congrArg IntervalRat.lo hCore.symm
      · exact congrArg IntervalRat.hi hCore.symm
    · -- The intersection failed, contradiction
      exact Option.noConfusion hCore

/-- Computable check if Newton iteration contracts.
    Returns `true` if `newtonStepCore` produces N with I.lo < N.lo and N.hi < I.hi.

    This can be used with `native_decide` for unique root verification. -/
def checkNewtonContractsCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  match newtonStepCore e I cfg with
  | none => false
  | some N => decide (I.lo < N.lo && N.hi < I.hi)

/-- Check if Newton iteration contracts, indicating unique root existence.
    Returns `true` if the Newton step from I gives N ⊂ interior(I).

    Note: This is noncomputable because newtonStepSimple uses derivInterval
    which uses evalInterval (noncomputable). For native_decide, we would need
    a fully computable version using evalIntervalCore. -/
noncomputable def checkNewtonContracts (e : Expr) (I : IntervalRat) (_cfg : NewtonConfig) : Bool :=
  match newtonStepSimple e I 0 with
  | none => false  -- Newton step failed (derivative interval contains 0)
  | some N =>
    -- Check strict contraction: N.lo > I.lo and N.hi < I.hi
    decide (I.lo < N.lo && N.hi < I.hi)

/-! ### Golden Theorems for Root Finding -/

/-- **Golden Theorem for No Root**

    If `checkNoRoot e I cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e ≠ 0`. -/
theorem verify_no_root (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_cert : checkNoRoot e I cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≠ 0 := by
  simp only [checkNoRoot, Bool.or_eq_true, decide_eq_true_eq] at h_cert
  intro x hx hcontra
  have heval := evalIntervalCore1_correct e hsupp x I hx cfg
  simp only [IntervalRat.mem_def] at heval
  cases h_cert with
  | inl hhi =>
    -- f's interval hi < 0, so f(x) ≤ hi < 0, contradiction with f(x) = 0
    have hhi_real : ((evalIntervalCore1 e I cfg).hi : ℝ) < 0 := by exact_mod_cast hhi
    have hf_neg : Expr.eval (fun _ => x) e < 0 := lt_of_le_of_lt heval.2 hhi_real
    rw [hcontra] at hf_neg
    exact absurd hf_neg (lt_irrefl 0)
  | inr hlo =>
    -- 0 < f's interval lo, so 0 < lo ≤ f(x), contradiction with f(x) = 0
    have hlo_real : (0 : ℝ) < (evalIntervalCore1 e I cfg).lo := by exact_mod_cast hlo
    have hf_pos : 0 < Expr.eval (fun _ => x) e := lt_of_lt_of_le hlo_real heval.1
    rw [hcontra] at hf_pos
    exact absurd hf_pos (lt_irrefl 0)

/-- **Golden Theorem for Newton Contraction (Unique Root Existence)**

    If `checkNewtonContracts e I cfg = true`, then there exists a unique root in I.

    This theorem requires additional hypotheses that the external checker must verify:
    - The expression is supported
    - The expression uses only variable 0
    - The function is continuous on I -/
theorem verify_unique_root_newton (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat) (cfg : NewtonConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkNewtonContracts e I cfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  simp only [checkNewtonContracts] at h_cert
  -- Extract the Newton step result
  split at h_cert
  · -- Newton step returned none
    exact absurd h_cert Bool.false_ne_true
  · -- Newton step returned some N
    rename_i N hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
    -- We have contraction: I.lo < N.lo and N.hi < I.hi
    have hContract : N.lo > I.lo ∧ N.hi < I.hi := ⟨h_cert.1, h_cert.2⟩
    -- Apply newton_contraction_unique_root directly
    -- This theorem already proves ∃! x, x ∈ I ∧ ... (uniqueness in I, not just N)
    exact newton_contraction_unique_root e hsupp hvar0 I N (Or.inr hN) hContract hCont

/-! ### Core MVT Lemmas for Newton Contraction Contradiction

These lemmas prove that if Newton contraction holds but f has constant sign at both
endpoints, we get a contradiction via MVT bounds.

Key insight: If f doesn't change sign on I (both endpoints positive or both negative),
then by monotonicity (from nonzero derivative), f has constant sign throughout I.
But Newton contraction requires specific quotient bounds that MVT proves are violated. -/

/-- MVT lower bound using derivIntervalCore: if f'(ξ) ∈ [dI.lo, dI.hi] for all ξ ∈ I,
    then f(y) - f(x) ≥ dI.lo * (y - x) for x ≤ y in I. -/
lemma mvt_lower_bound_core (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      ((derivIntervalCore e I cfg).lo : ℝ) * (y - x) ≤ evalFunc1 e y - evalFunc1 e x := by
  intro x y hx hy hxy
  set dI := derivIntervalCore e I cfg
  have hderiv_bound : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  -- Use Mathlib's MVT
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp.toSupported
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := by
    intro ξ hξ
    apply hderiv_bound
    exact @interior_subset ℝ _ (Set.Icc I.lo I.hi) ξ hξ
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hx; exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hy; exact hy
  exact hConvex.mul_sub_le_image_sub_of_le_deriv hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-- MVT upper bound using derivIntervalCore: if f'(ξ) ∈ [dI.lo, dI.hi] for all ξ ∈ I,
    then f(y) - f(x) ≤ dI.hi * (y - x) for x ≤ y in I. -/
lemma mvt_upper_bound_core (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      evalFunc1 e y - evalFunc1 e x ≤ ((derivIntervalCore e I cfg).hi : ℝ) * (y - x) := by
  intro x y hx hy hxy
  set dI := derivIntervalCore e I cfg
  have hderiv_bound : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp.toSupported
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := by
    intro ξ hξ
    apply hderiv_bound
    exact @interior_subset ℝ _ (Set.Icc I.lo I.hi) ξ hξ
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hx; exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hy; exact hy
  exact hConvex.image_sub_le_mul_sub_of_deriv_le hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-- **Golden Theorem for Computable Newton Contraction (Unique Root Existence)**

    This version assumes *both*:
    1. Core contraction check (computable, used by search/external tools)
    2. Non-core contraction check (used for the formal proof, via
       `verify_unique_root_newton`).

    The formal proof only relies on the non-core checker; the core checker
    can be used by the external agent for optimization but is not needed
    logically. This avoids the need to prove complex MVT-based contradiction
    lemmas for the Core interval functions.

    Note: The `h_cert_core` hypothesis is not used in the proof but is kept
    in the signature so the certificate format can include it for external
    tooling purposes. -/
theorem verify_unique_root_core (e : Expr) (hsupp : ExprSupportedCore e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat)
    (evalCfg : EvalConfig) (newtonCfg : NewtonConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (_h_cert_core : checkNewtonContractsCore e I evalCfg = true)
    (h_cert_newton : checkNewtonContracts e I newtonCfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  -- We only *use* `h_cert_newton`. The core certificate is present for external tooling.
  have hsupp' : ExprSupported e := hsupp.toSupported
  exact verify_unique_root_newton e hsupp' hvar0 I newtonCfg hCont h_cert_newton

/-! ### Sign Change Root Existence -/

/-- **Golden Theorem for Sign Change Root Existence**

    If `checkSignChange e I cfg = true`, then there exists a root in I.

    This uses the Intermediate Value Theorem: if f(lo) and f(hi) have opposite signs,
    and f is continuous on I, then f has a root in I. -/
theorem verify_sign_change (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkSignChange e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0 := by
  simp only [checkSignChange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  -- Define f for convenience
  set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf
  -- Get singleton memberships
  have hlo_sing : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
  have hhi_sing : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
  -- Apply evalIntervalCore1_correct to get bounds on f(lo) and f(hi)
  have hflo := evalIntervalCore1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_sing cfg
  have hfhi := evalIntervalCore1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_sing cfg
  simp only [IntervalRat.mem_def] at hflo hfhi
  -- Get the interval bound
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  -- Handle the two cases of signChange
  cases h_cert with
  | inl hcase =>
    -- Case: f(lo).hi < 0 ∧ 0 < f(hi).lo, meaning f(lo) < 0 < f(hi)
    have hflo_neg : f I.lo < 0 := by
      have hbound : f I.lo ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi := hflo.2
      have hcast : ((evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hfhi_pos : 0 < f I.hi := by
      have hbound : (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo ≤ f I.hi := hfhi.1
      have hcast : (0 : ℝ) < (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo := by
        exact_mod_cast hcase.2
      linarith
    -- Apply IVT: since f(lo) < 0 < f(hi), 0 ∈ Icc (f lo) (f hi) ⊆ f '' Icc lo hi
    have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.lo) (f I.hi) := ⟨le_of_lt hflo_neg, le_of_lt hfhi_pos⟩
    have hivt := intermediate_value_Icc (α := ℝ) (δ := ℝ) hle hCont
    have h0_in_image := hivt h0_in_range
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_image
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem
  | inr hcase =>
    -- Case: f(hi).hi < 0 ∧ 0 < f(lo).lo, meaning f(hi) < 0 < f(lo)
    have hfhi_neg : f I.hi < 0 := by
      have hbound : f I.hi ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi := hfhi.2
      have hcast : ((evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hflo_pos : 0 < f I.lo := by
      have hbound : (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo ≤ f I.lo := hflo.1
      have hcast : (0 : ℝ) < (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo := by
        exact_mod_cast hcase.2
      linarith
    -- f '' [lo, hi] is an interval containing both f(lo) and f(hi)
    have hflo_in_image : f I.lo ∈ f '' Set.Icc (↑I.lo) (↑I.hi) :=
      Set.mem_image_of_mem f (Set.left_mem_Icc.mpr hle)
    have hfhi_in_image : f I.hi ∈ f '' Set.Icc (↑I.lo) (↑I.hi) :=
      Set.mem_image_of_mem f (Set.right_mem_Icc.mpr hle)
    -- The image is connected (as continuous image of connected set)
    have hconn : IsConnected (f '' Set.Icc (↑I.lo) (↑I.hi)) :=
      (isConnected_Icc hle).image f hCont
    -- Use IsConnected.Icc_subset: the image contains [f(hi), f(lo)] since it's connected
    have hsub := hconn.Icc_subset hfhi_in_image hflo_in_image
    have h0_mem : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hfhi_neg, le_of_lt hflo_pos⟩
    have h0_in_img := hsub h0_mem
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_img
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem

/-! ### Bisection-Based Root Existence -/

/-- Check if bisection finds a root (returns hasRoot for some sub-interval).
    This runs the bisection algorithm and checks if any interval has hasRoot status.

    Note: This is noncomputable because bisectRoot uses evalInterval1. -/
noncomputable def checkHasRoot (e : Expr) (I : IntervalRat) (cfg : RootConfig) : Bool :=
  let tol : ℚ := (1 : ℚ) / (2 ^ cfg.maxDepth)
  let htol : 0 < tol := by positivity
  let result := bisectRoot e I cfg.maxDepth tol htol
  result.intervals.any fun (_, s) => s == RootStatus.hasRoot

/-- **Golden Theorem for Bisection Root Existence**

    If `checkHasRoot e I cfg = true`, then there exists a root in I.

    This uses bisectRoot_hasRoot_correct which proves that if bisection returns
    hasRoot for a sub-interval J ⊆ I, then there exists a root in J (hence in I). -/
theorem verify_has_root (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : RootConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkHasRoot e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0 := by
  simp only [checkHasRoot] at h_cert
  -- Extract the interval with hasRoot status
  have htol : (0 : ℚ) < 1 / 2 ^ cfg.maxDepth := by positivity
  set result := bisectRoot e I cfg.maxDepth (1 / 2 ^ cfg.maxDepth) htol with hresult
  -- h_cert says some interval has hasRoot status
  simp only [List.any_eq_true, beq_iff_eq] at h_cert
  obtain ⟨⟨J, s⟩, hmem, hs⟩ := h_cert
  -- Apply bisectRoot_hasRoot_correct
  have hroot := bisectRoot_hasRoot_correct e hsupp I cfg.maxDepth (1 / 2 ^ cfg.maxDepth) htol hCont
  have hroot_J := hroot J s hmem hs
  -- hroot_J : ∃ x ∈ J, f(x) = 0
  -- We need to show x ∈ I
  obtain ⟨x, hxJ, hx_root⟩ := hroot_J
  -- Show J ⊆ I using go_subinterval (implicitly used in bisectRoot_hasRoot_correct)
  -- Actually, bisectRoot_hasRoot_correct proves x ∈ J, and we need x ∈ I
  -- The proof in bisectRoot_hasRoot_correct shows J is a sub-interval of I
  -- and applies signChange_correct with continuity on J
  -- So x ∈ J ⊆ I
  refine ⟨x, ?_, hx_root⟩
  -- Need to show x ∈ I given x ∈ J and J is a sub-interval of I
  -- From go_subinterval in the bisectRoot_hasRoot_correct proof
  have hJsub : I.lo ≤ J.lo ∧ J.hi ≤ I.hi := by
    -- This follows from go_subinterval applied in the bisectRoot_hasRoot_correct proof
    -- We need to extract this lemma
    have hSub := go_subinterval e (1 / 2 ^ cfg.maxDepth) cfg.maxDepth I
      [(I, RootStatus.unknown)] cfg.maxDepth []
      (subinterval_inv_initial I)
      (fun _ _ h => by simp only [List.mem_nil_iff] at h)
    exact hSub J s hmem
  simp only [IntervalRat.mem_def] at hxJ ⊢
  constructor
  · calc (I.lo : ℝ) ≤ J.lo := by exact_mod_cast hJsub.1
      _ ≤ x := hxJ.1
  · calc x ≤ J.hi := hxJ.2
      _ ≤ I.hi := by exact_mod_cast hJsub.2

end LeanBound.Numerics.Certificate.RootFinding

/-! ## Integration Certificates -/

namespace LeanBound.Numerics.Certificate.Integration

open LeanBound.Core
open MeasureTheory

/-! ### Computable Integration Infrastructure

For `interval_integrate` tactic, we need:
1. A computable integration function using `evalIntervalCore1`
2. A theorem that `ExprSupportedCore` implies `IntervalIntegrable`
3. A verification theorem linking the computation to the real integral
-/

/-- Computable uniform partition using evalIntervalCore1 -/
def uniformPartitionCore (I : IntervalRat) (n : ℕ) (hn : 0 < n) : List IntervalRat :=
  let width := (I.hi - I.lo) / n
  List.ofFn fun i : Fin n =>
    { lo := I.lo + width * i
      hi := I.lo + width * (i + 1)
      le := by
        simp only [add_le_add_iff_left]
        apply mul_le_mul_of_nonneg_left
        · have : (i : ℚ) ≤ (i : ℚ) + 1 := le_add_of_nonneg_right (by norm_num)
          exact this
        · apply div_nonneg
          · linarith [I.le]
          · have : (0 : ℚ) < n := by exact_mod_cast hn
            linarith }

/-- Sum of interval bounds over a partition using computable evalIntervalCore1 -/
def sumIntervalBoundsCore (e : Expr) (parts : List IntervalRat) (cfg : EvalConfig) : IntervalRat :=
  parts.foldl
    (fun acc I =>
      let fBound := evalIntervalCore1 e I cfg
      let contribution := IntervalRat.mul
        (IntervalRat.singleton I.width)
        fBound
      IntervalRat.add acc contribution)
    (IntervalRat.singleton 0)

/-- Computable interval bounds on ∫_a^b f(x) dx using uniform partitioning -/
def integrateIntervalCore (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : EvalConfig := {}) : IntervalRat :=
  sumIntervalBoundsCore e (uniformPartitionCore I n hn) cfg

/-- For single-interval integration (n=1), computable version -/
def integrateInterval1Core (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  let fBound := evalIntervalCore1 e I cfg
  IntervalRat.mul (IntervalRat.singleton I.width) fBound

/-! ### IntervalIntegrable from ExprSupportedCore

All `ExprSupportedCore` expressions are continuous, hence integrable on compact intervals. -/

/-- All ExprSupportedCore expressions are interval integrable on any compact interval.

This follows because ExprSupportedCore expressions are continuous (see exprSupportedCore_continuousOn),
and continuous functions on compact intervals are integrable. -/
theorem exprSupportedCore_intervalIntegrable (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi := by
  have hCont := LeanBound.Meta.exprSupportedCore_continuousOn e hsupp (s := Set.Icc I.lo I.hi)
  -- Continuous functions on compact intervals are integrable
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  exact hCont.intervalIntegrable_of_Icc hle

/-! ### Correctness of Computable Integration -/

/-- Single-interval integration correctness for ExprSupportedCore.

This is proved directly using the same structure as integrateInterval1_correct but
with the computable evalIntervalCore1 instead of noncomputable evalInterval1. -/
theorem integrateInterval1Core_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg := by
  unfold integrateInterval1Core
  -- Get bounds from interval evaluation
  set fBound := evalIntervalCore1 e I cfg with hfBound_def
  have hbounds : ∀ x : ℝ, x ∈ I → Expr.eval (fun _ => x) e ∈ fBound := fun x hx =>
    evalIntervalCore1_correct e hsupp x I hx cfg
  have hlo : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), (fBound.lo : ℝ) ≤ Expr.eval (fun _ => x) e := by
    intro x hx; exact (hbounds x hx).1
  have hhi : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (fBound.hi : ℝ) := by
    intro x hx; exact (hbounds x hx).2
  have hIle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have hInt := exprSupportedCore_intervalIntegrable e hsupp I
  have ⟨h_lower, h_upper⟩ := LeanBound.Numerics.integral_bounds_of_bounds hIle hInt hlo hhi
  -- Show membership in the product interval
  have hwidth : (I.width : ℝ) = (I.hi : ℝ) - (I.lo : ℝ) := by
    simp only [IntervalRat.width, Rat.cast_sub]
  have hwidth_nn : (0 : ℝ) ≤ I.width := by exact_mod_cast IntervalRat.width_nonneg I
  have hfBound_le : (fBound.lo : ℝ) ≤ fBound.hi := by exact_mod_cast fBound.le
  -- Convert integral bounds to width-first form
  have h_lo' : (I.width : ℝ) * fBound.lo ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := by
    calc (I.width : ℝ) * fBound.lo = fBound.lo * I.width := by ring
       _ = fBound.lo * ((I.hi : ℝ) - I.lo) := by rw [hwidth]
       _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lower
  have h_hi' : ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e ≤ (I.width : ℝ) * fBound.hi := by
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
       ≤ fBound.hi * ((I.hi : ℝ) - I.lo) := h_upper
     _ = fBound.hi * I.width := by rw [hwidth]
     _ = (I.width : ℝ) * fBound.hi := by ring
  -- Show membership
  have h1 : (I.width : ℝ) * fBound.lo ≤ I.width * fBound.hi :=
    mul_le_mul_of_nonneg_left hfBound_le hwidth_nn
  rw [IntervalRat.mem_def]
  constructor
  · -- Lower bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).lo =
        min (min (I.width * fBound.lo) (I.width * fBound.hi))
            (min (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, min_self, Rat.cast_min, Rat.cast_mul]
    calc (↑I.width * ↑fBound.lo) ⊓ (↑I.width * ↑fBound.hi)
        = ↑I.width * ↑fBound.lo := min_eq_left h1
      _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lo'
  · -- Upper bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).hi =
        max (max (I.width * fBound.lo) (I.width * fBound.hi))
            (max (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, max_self, Rat.cast_max, Rat.cast_mul]
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
        ≤ ↑I.width * ↑fBound.hi := h_hi'
      _ = (↑I.width * ↑fBound.lo) ⊔ (↑I.width * ↑fBound.hi) := (max_eq_right h1).symm

/-- Check if the integral bound contains a given rational value.
    Returns true if the computed integral bound contains the target value. -/
def checkIntegralBoundsCore (e : Expr) (I : IntervalRat) (target : ℚ)
    (cfg : EvalConfig := {}) : Bool :=
  let bound := integrateInterval1Core e I cfg
  decide (bound.lo ≤ target && target ≤ bound.hi)

/-- **Golden Theorem for Integration Bounds**

If `checkIntegralBoundsCore e I target cfg = true`, then the integral is bounded by the
computed interval.

Note: The `target` parameter and `h_cert` hypothesis are used for the `native_decide` workflow
where we verify at compile time that target is in the computed interval. The actual proof
of interval membership uses `integrateInterval1Core_correct` directly.

This theorem allows proving statements like "∫_a^b f(x) dx ∈ [lo, hi]". -/
theorem verify_integral_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (_target : ℚ) (cfg : EvalConfig)
    (_h_cert : checkIntegralBoundsCore e I _target cfg = true) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg := by
  exact integrateInterval1Core_correct e hsupp I cfg

/-- Extract the computed integral bound as an interval -/
def getIntegralBound (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  integrateInterval1Core e I cfg

/-- The integral lies within the computed bound (computable version) -/
theorem integral_in_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) :
    (getIntegralBound e I cfg).lo ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∧
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (getIntegralBound e I cfg).hi := by
  have hmem := integrateInterval1Core_correct e hsupp I cfg
  simp only [IntervalRat.mem_def, getIntegralBound] at hmem ⊢
  exact hmem

end LeanBound.Numerics.Certificate.Integration
