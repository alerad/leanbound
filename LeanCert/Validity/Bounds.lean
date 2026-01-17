/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.AD
import LeanCert.Engine.Optimization.Global
import LeanCert.Engine.RootFinding.Main
import LeanCert.Engine.Integrate
import LeanCert.Meta.ProveContinuous

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

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

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

/-! ### Argmax/Argmin Verification

These theorems support proving `∀ y ∈ I, f(y) ≤ f(x)` (argmax) and
`∀ y ∈ I, f(x) ≤ f(y)` (argmin) via a concrete rational bound.
-/

/-- Check that evaluating f at a point x gives a value ≥ c.
    We evaluate on the point interval [x, x] and check the lower bound.
    This gives us c ≤ f(x) when x is rational. -/
def checkPointLowerBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  decide (c ≤ (evalIntervalCore1 e Ipt cfg).lo)

/-- Check that evaluating f at a point x gives a value ≤ c. -/
def checkPointUpperBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  decide ((evalIntervalCore1 e Ipt cfg).hi ≤ c)

/-- Verify that c ≤ f(x) at a specific point x. -/
theorem verify_point_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointLowerBound e x c cfg = true) :
    c ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  simp only [checkPointLowerBound, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_ge_of_interval_lo e hsupp Ipt c cfg h_cert (x : ℝ) hx_mem

/-- Verify that f(x) ≤ c at a specific point x. -/
theorem verify_point_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointUpperBound e x c cfg = true) :
    Expr.eval (fun _ => (x : ℝ)) e ≤ c := by
  simp only [checkPointUpperBound, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_le_of_interval_hi e hsupp Ipt c cfg h_cert (x : ℝ) hx_mem

/-- **Argmax Verification Theorem**

    Proves `∀ y ∈ I, f(y) ≤ f(x)` (x is a maximizer) by:
    1. Checking that `∀ y ∈ I, f(y) ≤ c` (the max over I is at most c)
    2. Checking that `c ≤ f(x)` (the value at x is at least c)
    This implies `f(y) ≤ c ≤ f(x)` by transitivity. -/
theorem verify_argmax (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_upper : checkUpperBound e I c cfg = true)
    (h_point : checkPointLowerBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => y) e ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => y) e ≤ c := verify_upper_bound e hsupp I c cfg h_upper y hy
  have h2 : c ≤ Expr.eval (fun _ => (x : ℝ)) e := verify_point_lower_bound e hsupp x c cfg h_point
  exact le_trans h1 h2

/-- **Argmin Verification Theorem**

    Proves `∀ y ∈ I, f(x) ≤ f(y)` (x is a minimizer) by:
    1. Checking that `∀ y ∈ I, c ≤ f(y)` (the min over I is at least c)
    2. Checking that `f(x) ≤ c` (the value at x is at most c)
    This implies `f(x) ≤ c ≤ f(y)` by transitivity. -/
theorem verify_argmin (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_lower : checkLowerBound e I c cfg = true)
    (h_point : checkPointUpperBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => (x : ℝ)) e ≤ Expr.eval (fun _ => y) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => (x : ℝ)) e ≤ c := verify_point_upper_bound e hsupp x c cfg h_point
  have h2 : c ≤ Expr.eval (fun _ => y) e := verify_lower_bound e hsupp I c cfg h_lower y hy
  exact le_trans h1 h2

/-! ### ExprSupportedWithInv bounds

Support for expressions with inv, log, atan, arsinh, atanh. These use the
`evalInterval?` evaluator which may return `none` for invalid inputs.

NOTE: These are noncomputable because `evalInterval?` uses Real Taylor approximations.
They cannot be used with `native_decide`. Use the verification theorems directly
in term proofs or with explicit computation.
-/

/-- Check upper bound for ExprSupportedWithInv expressions.
    Returns `true` iff evalInterval?1 succeeds and the upper bound is ≤ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
noncomputable def checkUpperBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi ≤ c)
  | none => false

/-- Check lower bound for ExprSupportedWithInv expressions.
    Returns `true` iff evalInterval?1 succeeds and the lower bound is ≥ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
noncomputable def checkLowerBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c ≤ J.lo)
  | none => false

/-- Check strict upper bound for ExprSupportedWithInv expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
noncomputable def checkStrictUpperBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi < c)
  | none => false

/-- Check strict lower bound for ExprSupportedWithInv expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
noncomputable def checkStrictLowerBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c < J.lo)
  | none => false

/-- Verification theorem for upper bounds with ExprSupportedWithInv. -/
theorem verify_upper_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkUpperBoundWithInv e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkUpperBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_le_of_hi e hsupp I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for lower bounds with ExprSupportedWithInv. -/
theorem verify_lower_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkLowerBoundWithInv e I c = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_ge_of_lo e hsupp I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for strict upper bounds with ExprSupportedWithInv. -/
theorem verify_strict_upper_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictUpperBoundWithInv e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hle := evalInterval?_le_of_hi e hsupp I J J.hi hsome (le_refl _) x hx
    have hJ_hi : Expr.eval (fun _ => x) e ≤ J.hi := hle
    calc Expr.eval (fun _ => x) e ≤ J.hi := hJ_hi
      _ < c := by exact_mod_cast h_cert
  · simp at h_cert

/-- Verification theorem for strict lower bounds with ExprSupportedWithInv. -/
theorem verify_strict_lower_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictLowerBoundWithInv e I c = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hge := evalInterval?_ge_of_lo e hsupp I J J.lo hsome (le_refl _) x hx
    have hJ_lo : (J.lo : ℝ) ≤ Expr.eval (fun _ => x) e := hge
    have hc_lt_lo : (c : ℝ) < (J.lo : ℝ) := by exact_mod_cast h_cert
    exact lt_of_lt_of_le hc_lt_lo hJ_lo
  · simp at h_cert

/-- Bridge theorem for Set.Icc upper bounds with ExprSupportedWithInv. -/
theorem verify_upper_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkUpperBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc lower bounds with ExprSupportedWithInv. -/
theorem verify_lower_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkLowerBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict upper bounds with ExprSupportedWithInv. -/
theorem verify_strict_upper_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictUpperBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict lower bounds with ExprSupportedWithInv. -/
theorem verify_strict_lower_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictLowerBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

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
theorem increasing_min_at_left_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => I.lo) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  -- Use the MVT: f(x) - f(lo) = f'(ξ) * (x - lo) for some ξ ∈ (lo, x)
  -- Since f' > 0 and x ≥ lo, we have f(x) ≥ f(lo)
  have hdiff := evalFunc1_differentiable e hsupp
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
theorem decreasing_min_at_right_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => I.hi) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
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
theorem verify_lower_bound_smart (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  unfold checkLowerBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_lower_bound e hsupp.toCore I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing)
      rename_i h_pos
      intro x hx
      have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
      have heval := evalIntervalCore1_correct e hsupp.toCore I.lo (IntervalRat.singleton I.lo) hlo_mem cfg
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
        have heval := evalIntervalCore1_correct e hsupp.toCore I.hi (IntervalRat.singleton I.hi) hhi_mem cfg
        simp only [IntervalRat.mem_def] at heval
        have hmono := decreasing_min_at_right_core e hsupp I cfg h_neg x hx
        simp only [decide_eq_true_eq] at h_cert
        calc (c : ℝ) ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo := by exact_mod_cast h_cert
          _ ≤ Expr.eval (fun _ => I.hi) e := heval.1
          _ ≤ Expr.eval (fun _ => x) e := hmono
      · -- Neither increasing nor decreasing => impossible since h_cert = true
        exact absurd h_cert Bool.false_ne_true

/-- Helper: For increasing functions, the maximum is at the right endpoint -/
theorem increasing_max_at_right_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.hi) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
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
theorem decreasing_max_at_left_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.lo) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
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
theorem verify_upper_bound_smart (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  unfold checkUpperBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_upper_bound e hsupp.toCore I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing), max at hi
      rename_i h_pos
      intro x hx
      have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
      have heval := evalIntervalCore1_correct e hsupp.toCore I.hi (IntervalRat.singleton I.hi) hhi_mem cfg
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
        have heval := evalIntervalCore1_correct e hsupp.toCore I.lo (IntervalRat.singleton I.lo) hlo_mem cfg
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
theorem verify_upper_bound_Icc (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc lower bound goal -/
theorem verify_lower_bound_Icc (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc upper bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkUpperBound (no monotonicity). -/
theorem verify_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc lower bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkLowerBound (no monotonicity). -/
theorem verify_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc strict upper bound goal (Core version). -/
theorem verify_strict_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc strict lower bound goal (Core version). -/
theorem verify_strict_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-! ### Subdivision Theorems

These theorems allow combining bounds from interval subdivisions.
When interval arithmetic gives overly wide bounds, subdividing the domain
and proving bounds on each piece can help.
-/

/-- Combine upper bounds from two halves using splitMid.
    If f ≤ c on both halves, then f ≤ c on the whole interval. -/
theorem verify_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine lower bounds from two halves using splitMid. -/
theorem verify_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine strict upper bounds from two halves. -/
theorem verify_strict_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine strict lower bounds from two halves. -/
theorem verify_strict_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Bridge from subdivision to Set.Icc upper bound goal. -/
theorem verify_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc lower bound goal. -/
theorem verify_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc strict upper bound goal. -/
theorem verify_strict_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc strict lower bound goal. -/
theorem verify_strict_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-! ### General Split Theorems

These theorems work with arbitrary split points, not just midpoints.
Useful for adaptive subdivision algorithms.
-/

/-- Any x in [lo, hi] is in [lo, mid] or [mid, hi] for any mid in between -/
theorem mem_split_general {lo mid hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ))
    (_hLeMid : lo ≤ mid) (_hMidLe : mid ≤ hi) :
    x ∈ Set.Icc (lo : ℝ) (mid : ℝ) ∨ x ∈ Set.Icc (mid : ℝ) (hi : ℝ) := by
  simp only [Set.mem_Icc] at hx ⊢
  by_cases h : x ≤ mid
  · left; exact ⟨hx.1, h⟩
  · right
    push_neg at h
    exact ⟨le_of_lt h, hx.2⟩

/-- Combine upper bounds from two arbitrary adjacent intervals.
    If f ≤ c on [lo, mid] and f ≤ c on [mid, hi], then f ≤ c on [lo, hi]. -/
theorem verify_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine lower bounds from two arbitrary adjacent intervals. -/
theorem verify_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine strict upper bounds from two arbitrary adjacent intervals. -/
theorem verify_strict_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine strict lower bounds from two arbitrary adjacent intervals. -/
theorem verify_strict_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

end LeanCert.Validity

/-! ## Global Optimization Certificates

These checkers and theorems extend the certificate pattern to multivariate
global optimization over n-dimensional boxes.
-/

namespace LeanCert.Validity.GlobalOpt

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization

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

end LeanCert.Validity.GlobalOpt

/-! ## Root Finding Certificates

These checkers and theorems provide certificate-driven verification for
root existence and uniqueness.
-/

namespace LeanCert.Validity.RootFinding

open LeanCert.Core
open LeanCert.Engine

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
def newtonStepCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : Option IntervalRat :=
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
    simp only [hzero, ↓reduceDIte, reduceCtorEq] at hCore
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
      simp only [reduceCtorEq] at hCore

/-- Computable check if Newton iteration contracts.
    Returns `true` if `newtonStepCore` produces N with I.lo < N.lo and N.hi < I.hi.

    This can be used with `native_decide` for unique root verification. -/
def checkNewtonContractsCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : Bool :=
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
lemma mvt_lower_bound_core (e : Expr) (hsupp : ExprSupported e)
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
    have hdiff := evalFunc1_differentiable e hsupp
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
lemma mvt_upper_bound_core (e : Expr) (hsupp : ExprSupported e)
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
    have hdiff := evalFunc1_differentiable e hsupp
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
theorem verify_unique_root_core (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat)
    (evalCfg : EvalConfig) (newtonCfg : NewtonConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (_h_cert_core : checkNewtonContractsCore e I evalCfg = true)
    (h_cert_newton : checkNewtonContracts e I newtonCfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  -- We only *use* `h_cert_newton`. The core certificate is present for external tooling.
  exact verify_unique_root_newton e hsupp hvar0 I newtonCfg hCont h_cert_newton

/-! ### Fully Computable Unique Root Verification

The following theorems provide a **fully computable** path to proving unique root existence
using only `checkNewtonContractsCore`. This allows `native_decide` to work without requiring
noncomputable functions like `Real.exp` or `Real.log`. -/

/-- Newton step preserves roots when using Core evaluation functions.
    If x is a root in I and newtonStepCore produces N, then x ∈ N. -/
theorem newton_preserves_root_core (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I N : IntervalRat) (cfg : EvalConfig)
    (hStep : newtonStepCore e I cfg = some N)
    (x : ℝ) (hx : x ∈ I) (hroot : Expr.eval (fun _ => x) e = 0) :
    x ∈ N := by
  -- Extract structure from newtonStepCore
  obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepCore_extract e I N cfg hStep

  -- Define components matching abstract theorem
  let c := I.midpoint
  let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
  let dI := derivIntervalCore e I cfg

  -- Verify premises for abstract theorem
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I

  -- 1. f(c) ∈ fc via evalIntervalCore1_correct
  have hfc_correct : evalFunc1 e c ∈ fc := by
    simp only [evalFunc1]
    exact evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg

  -- 2. f'(ξ) ∈ dI for all ξ ∈ I via derivIntervalCore_correct
  have hdI_correct : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ∈ dI := fun ξ hξ =>
    derivIntervalCore_correct e hsupp I ξ hξ cfg

  -- Apply abstract preservation lemma
  have hroot' : evalFunc1 e x = 0 := hroot
  have h_in_Newton := newton_operator_preserves_root e hsupp hvar0
    I c fc dI hc_in_I hfc_correct hdI_correct hdI_nonzero x hx hroot'

  -- Now we need to show x ∈ N where N = I ∩ Newton
  -- h_in_Newton shows x is in the Newton interval [c - Q.hi, c - Q.lo]
  -- Combined with hx : x ∈ I, we get x ∈ I ∩ Newton = N
  have hx_in_intersect := IntervalRat.mem_intersect hx h_in_Newton
  obtain ⟨K, hK_eq, hx_in_K⟩ := hx_in_intersect

  -- Show x ∈ N by using the intersection logic
  -- Both hStep and hK_eq refer to the same intersect
  unfold newtonStepCore at hStep
  simp only [hdI_nonzero, dite_false] at hStep
  -- Now hStep : IntervalRat.intersect I (I.newtonInterval fc dI) = some N
  -- And hK_eq : IntervalRat.intersect I (I.newtonInterval fc dI) = some K
  have hN_eq_K : N = K := by
    rw [hStep] at hK_eq
    simp only [Option.some.injEq] at hK_eq
    exact hK_eq
  rw [hN_eq_K]
  exact hx_in_K

/-- If Newton step succeeds, there's at most one root in I (via Rolle's theorem).
    This uses the fact that if dI doesn't contain zero, the derivative is nonzero
    everywhere on I, so f is strictly monotonic. -/
theorem newton_step_core_at_most_one_root (e : Expr) (hsupp : ExprSupported e) (_hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hStep : ∃ N, newtonStepCore e I cfg = some N)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I)
    (hx_root : Expr.eval (fun _ => x) e = 0) (hy_root : Expr.eval (fun _ => y) e = 0) :
    x = y := by
  obtain ⟨N, hN⟩ := hStep
  -- If step succeeds, dI doesn't contain zero
  set dI := derivIntervalCore e I cfg with hdI_def
  by_cases hzero : dI.containsZero
  · -- If dI contains zero, newtonStepCore returns none, but hN says it's some N
    unfold newtonStepCore at hN
    simp only [← hdI_def, dif_pos hzero, reduceCtorEq] at hN
  · -- dI doesn't contain zero, so derivative is nonzero everywhere on I
    simp only [IntervalRat.containsZero, not_and_or, not_le] at hzero

    by_contra hne
    -- If x ≠ y, Rolle's theorem gives ξ between them with f'(ξ) = 0
    simp only [IntervalRat.mem_def] at hx hy
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- x < y case
      have hIcc_sub : Set.Icc x y ⊆ Set.Icc (I.lo : ℝ) I.hi := by
        intro z ⟨hzlo, hzhi⟩
        exact ⟨le_trans hx.1 hzlo, le_trans hzhi hy.2⟩
      have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc x y) := hCont.mono hIcc_sub
      have hf_eq : evalFunc1 e x = evalFunc1 e y := by
        simp only [evalFunc1]; rw [hx_root, hy_root]
      obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) x y hlt hCont' hf_eq
      -- ξ ∈ (x, y) ⊆ I
      have hξ_in_I : ξ ∈ I := by
        simp only [IntervalRat.mem_def]
        exact ⟨le_trans hx.1 (le_of_lt hξ_mem.1), le_trans (le_of_lt hξ_mem.2) hy.2⟩
      -- f'(ξ) ∈ dI but f'(ξ) = 0
      have hderiv_in := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
      rw [hξ_deriv] at hderiv_in
      simp only [IntervalRat.mem_def] at hderiv_in
      rcases hzero with hlo_pos | hhi_neg
      · have hcast : (0 : ℝ) < dI.lo := by exact_mod_cast hlo_pos
        linarith [hderiv_in.1]
      · have hcast : (dI.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
        linarith [hderiv_in.2]
    · -- y < x case (symmetric)
      have hIcc_sub : Set.Icc y x ⊆ Set.Icc (I.lo : ℝ) I.hi := by
        intro z ⟨hzlo, hzhi⟩
        exact ⟨le_trans hy.1 hzlo, le_trans hzhi hx.2⟩
      have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc y x) := hCont.mono hIcc_sub
      have hf_eq : evalFunc1 e y = evalFunc1 e x := by
        simp only [evalFunc1]; rw [hy_root, hx_root]
      obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) y x hlt hCont' hf_eq
      have hξ_in_I : ξ ∈ I := by
        simp only [IntervalRat.mem_def]
        exact ⟨le_trans hy.1 (le_of_lt hξ_mem.1), le_trans (le_of_lt hξ_mem.2) hx.2⟩
      have hderiv_in := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
      rw [hξ_deriv] at hderiv_in
      simp only [IntervalRat.mem_def] at hderiv_in
      rcases hzero with hlo_pos | hhi_neg
      · have hcast : (0 : ℝ) < dI.lo := by exact_mod_cast hlo_pos
        linarith [hderiv_in.1]
      · have hcast : (dI.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
        linarith [hderiv_in.2]

/-- MVT bound using Core functions: If f' ≥ dI.lo > 0 (increasing) and f(I.lo) > 0,
    then f(c) > dI.lo * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_lower_bound_pos_increasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_lo_pos : 0 < (derivIntervalCore e I cfg).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_pos : 0 < evalFunc1 e I.lo) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c > (dI.lo : ℝ) * hw := by
  intro c hw dI
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_lower_bound_core e hsupp I cfg hCont I.lo c hIlo_in_I hc_in_I hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  calc evalFunc1 e c ≥ evalFunc1 e I.lo + dI.lo * hw := by linarith
    _ > 0 + dI.lo * hw := by linarith
    _ = dI.lo * hw := by ring

/-- MVT bound using Core functions: If f' ≥ dI.lo > 0 (increasing) and f(I.hi) < 0,
    then f(c) < -dI.lo * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_upper_bound_pos_increasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_lo_pos : 0 < (derivIntervalCore e I cfg).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_neg : evalFunc1 e I.hi < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c < -((dI.lo : ℝ) * hw) := by
  intro c hw dI
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_lower_bound_core e hsupp I cfg hCont c I.hi hc_in_I hIhi_in_I hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  calc evalFunc1 e c ≤ evalFunc1 e I.hi - dI.lo * hw := by linarith
    _ < 0 - dI.lo * hw := by linarith
    _ = -(dI.lo * hw) := by ring

/-- MVT bound using Core functions: If f' ≤ dI.hi < 0 (decreasing) and f(I.lo) < 0,
    then f(c) < 0 and more specifically, fc.lo / dI.hi ≥ hw. -/
lemma mvt_fc_upper_bound_neg_decreasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_hi_neg : (derivIntervalCore e I cfg).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_neg : evalFunc1 e I.lo < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c < (dI.hi : ℝ) * hw := by
  intro c hw dI
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_upper_bound_core e hsupp I cfg hCont I.lo c hIlo_in_I hc_in_I hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  calc evalFunc1 e c ≤ evalFunc1 e I.lo + dI.hi * hw := by linarith
    _ < 0 + dI.hi * hw := by linarith
    _ = dI.hi * hw := by ring

/-- MVT bound using Core functions: If f' ≤ dI.hi < 0 (decreasing) and f(I.hi) > 0,
    then f(c) > 0 and more specifically, fc.hi / dI.hi ≤ -hw. -/
lemma mvt_fc_lower_bound_neg_decreasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_hi_neg : (derivIntervalCore e I cfg).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_pos : 0 < evalFunc1 e I.hi) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c > -((dI.hi : ℝ) * hw) := by
  intro c hw dI
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_upper_bound_core e hsupp I cfg hCont c I.hi hc_in_I hIhi_in_I hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  calc evalFunc1 e c ≥ evalFunc1 e I.hi - dI.hi * hw := by linarith
    _ > 0 - dI.hi * hw := by linarith
    _ = -(dI.hi * hw) := by ring

/-- **Golden Theorem for Computable Unique Root (Fully Computable)**

    If `checkNewtonContractsCore e I cfg = true`, then there exists a unique root in I.

    This theorem uses ONLY computable functions (no Real.exp, Real.log, etc.),
    making it suitable for `native_decide` verification. -/
theorem verify_unique_root_computable (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkNewtonContractsCore e I cfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  simp only [checkNewtonContractsCore] at h_cert
  split at h_cert
  · exact absurd h_cert Bool.false_ne_true
  · rename_i N hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
    have hContract : N.lo > I.lo ∧ N.hi < I.hi := ⟨h_cert.1, h_cert.2⟩

    -- Extract structure
    obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepCore_extract e I N cfg hN
    let c := I.midpoint
    let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
    let dI := derivIntervalCore e I cfg
    let hw : ℚ := (I.hi - I.lo) / 2

    -- From contraction bounds, extract Q bounds
    -- N.lo = max I.lo (c - Q.hi), N.hi = min I.hi (c - Q.lo)
    -- Contraction means: N.lo > I.lo and N.hi < I.hi
    -- So N.lo = c - Q.hi (not I.lo) and N.hi = c - Q.lo (not I.hi)
    have hbounds := contraction_newton_bounds hContract hN_lo hN_hi

    -- Q.hi < c - I.lo = hw and Q.lo > c - I.hi = -hw
    have hQ_hi_lt : (c : ℚ) - N.lo < hw := by
      rw [hbounds.1]
      have hc_minus_Ilo : c - I.lo = hw := by
        show I.midpoint - I.lo = (I.hi - I.lo) / 2
        simp only [IntervalRat.midpoint]; ring
      linarith [hContract.1]
    have hQ_lo_gt : (c : ℚ) - N.hi > -hw := by
      rw [hbounds.2]
      have hc_minus_Ihi : c - I.hi = -hw := by
        show I.midpoint - I.hi = -((I.hi - I.lo) / 2)
        simp only [IntervalRat.midpoint]; ring
      linarith [hContract.2]

    -- Use sign analysis to prove existence
    simp only [IntervalRat.containsZero, not_and_or, not_le] at hdI_nonzero

    -- Contraction + MVT logic mirrors newton_contraction_has_root
    -- Key: if f doesn't change sign, MVT bounds on the quotient contradict contraction
    have hI_nonsingleton : I.lo < I.hi := by
      have h1 : (I.lo : ℝ) < N.lo := by exact_mod_cast hContract.1
      have h2 : (N.hi : ℝ) < I.hi := by exact_mod_cast hContract.2
      have h3 : (N.lo : ℝ) ≤ N.hi := by exact_mod_cast N.le
      have h4 : I.lo < I.hi := by
        have : (I.lo : ℝ) < I.hi := by linarith
        exact_mod_cast this
      exact h4

    set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf_def

    -- Case split on derivative sign
    rcases hdI_nonzero with hdI_pos | hdI_neg
    · -- Case: dI.lo > 0 (strictly increasing)
      by_cases hlo : f I.lo ≥ 0
      · by_cases hhi : f I.hi ≤ 0
        · -- f(lo) ≥ 0 and f(hi) ≤ 0 with f increasing is a contradiction
          -- Because f' ≥ dI.lo > 0 implies f(hi) - f(lo) > 0, so f(hi) > f(lo)
          -- Combined with f(lo) ≥ 0 ≥ f(hi), this is impossible
          exfalso
          have hIlo_in_I : (I.lo : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨le_refl _, by exact_mod_cast I.le⟩
          have hIhi_in_I : (I.hi : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨by exact_mod_cast I.le, le_refl _⟩
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          -- MVT: f(hi) - f(lo) ≥ dI.lo * (hi - lo) > 0
          have hmvt := mvt_lower_bound_core e hsupp I cfg hCont I.lo I.hi hIlo_in_I hIhi_in_I hle
          have hdI_lo_pos_real : (0 : ℝ) < dI.lo := by exact_mod_cast hdI_pos
          have hwidth_pos : (I.hi : ℝ) - I.lo > 0 := by
            have h : (I.lo : ℝ) < I.hi := by exact_mod_cast hI_nonsingleton
            linarith
          have hdiff_pos : (dI.lo : ℝ) * ((I.hi : ℝ) - I.lo) > 0 := mul_pos hdI_lo_pos_real hwidth_pos
          -- hmvt : evalFunc1 e ↑I.hi - evalFunc1 e ↑I.lo ≥ ↑dI.lo * (↑I.hi - ↑I.lo)
          -- hdiff_pos : (dI.lo : ℝ) * ((I.hi : ℝ) - I.lo) > 0
          -- So evalFunc1 e I.hi > evalFunc1 e I.lo
          -- hlo : 0 ≤ f I.lo = evalFunc1 e I.lo
          -- hhi : f I.hi ≤ 0 = evalFunc1 e I.hi ≤ 0
          -- This gives: 0 ≤ evalFunc1 e I.lo < evalFunc1 e I.hi ≤ 0, contradiction
          have hstrictly_increasing : evalFunc1 e I.hi > evalFunc1 e I.lo := by linarith
          linarith
        · -- f(lo) ≥ 0 and f(hi) > 0 with f increasing → f > 0 on I
          push_neg at hhi
          by_cases hlo_eq : f I.lo = 0
          · use I.lo
            have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            constructor
            · exact ⟨hIlo_in_I, hlo_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.lo hy_in_I hIlo_in_I hy_root hlo_eq
          · -- f(lo) > 0, get contradiction via MVT
            have hlo_pos : 0 < f I.lo := lt_of_le_of_ne hlo (Ne.symm hlo_eq)
            exfalso
            -- MVT: fc.hi / dI.lo ≥ hw (half-width)
            have hMVT := mvt_fc_lower_bound_pos_increasing_core e hsupp I cfg hI_nonsingleton hdI_pos hCont hlo_pos
            -- Apply generic contraction contradiction
            exact generic_contraction_absurd_hi I c fc dI N rfl hdI_nonzero hdI_pos
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg)
              hN_lo hContract.1 hMVT
      · push_neg at hlo
        by_cases hhi : f I.hi ≤ 0
        · by_cases hhi_eq : f I.hi = 0
          · use I.hi
            have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            constructor
            · exact ⟨hIhi_in_I, hhi_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.hi hy_in_I hIhi_in_I hy_root hhi_eq
          · -- f(hi) < 0, get contradiction via MVT
            have hhi_neg : f I.hi < 0 := lt_of_le_of_ne hhi hhi_eq
            exfalso
            have hMVT := mvt_fc_upper_bound_pos_increasing_core e hsupp I cfg hI_nonsingleton hdI_pos hCont hhi_neg
            exact generic_contraction_absurd_lo I c fc dI N rfl hdI_nonzero hdI_pos
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg)
              hN_hi hContract.2 hMVT
        · -- f(lo) < 0 and f(hi) > 0: SIGN CHANGE! Apply IVT.
          push_neg at hhi
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.lo) (f I.hi) := ⟨le_of_lt hlo, le_of_lt hhi⟩
          have hivt := intermediate_value_Icc hle hCont h0_in_range
          obtain ⟨x, hx_mem, hx_root⟩ := hivt
          use x
          constructor
          · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact ⟨hx_in_I, hx_root⟩
          · intro y ⟨hy_in_I, hy_root⟩
            have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y x hy_in_I hx_in_I hy_root hx_root
    · -- Case: dI.hi < 0 (strictly decreasing) - symmetric logic
      by_cases hlo : f I.lo ≤ 0
      · by_cases hhi : f I.hi ≥ 0
        · -- f(lo) ≤ 0 ≤ f(hi) with f decreasing is a contradiction
          -- Because f' ≤ dI.hi < 0 implies f(hi) - f(lo) < 0, so f(hi) < f(lo)
          -- Combined with f(lo) ≤ 0 ≤ f(hi), this is impossible
          exfalso
          have hIlo_in_I : (I.lo : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨le_refl _, by exact_mod_cast I.le⟩
          have hIhi_in_I : (I.hi : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨by exact_mod_cast I.le, le_refl _⟩
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          -- MVT: f(hi) - f(lo) ≤ dI.hi * (hi - lo) < 0
          have hmvt := mvt_upper_bound_core e hsupp I cfg hCont I.lo I.hi hIlo_in_I hIhi_in_I hle
          have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_neg
          have hwidth_pos : (I.hi : ℝ) - I.lo > 0 := by
            have h : (I.lo : ℝ) < I.hi := by exact_mod_cast hI_nonsingleton
            linarith
          have hdiff_neg : (dI.hi : ℝ) * ((I.hi : ℝ) - I.lo) < 0 := mul_neg_of_neg_of_pos hdI_hi_neg_real hwidth_pos
          -- hmvt : evalFunc1 e ↑I.hi - evalFunc1 e ↑I.lo ≤ ↑dI.hi * (↑I.hi - ↑I.lo)
          -- hdiff_neg : (dI.hi : ℝ) * ((I.hi : ℝ) - I.lo) < 0
          -- So evalFunc1 e I.hi < evalFunc1 e I.lo
          -- hlo : f I.lo ≤ 0 = evalFunc1 e I.lo ≤ 0
          -- hhi : f I.hi ≥ 0 = evalFunc1 e I.hi ≥ 0
          -- This gives: 0 ≤ evalFunc1 e I.hi < evalFunc1 e I.lo ≤ 0, contradiction
          have hstrictly_decreasing : evalFunc1 e I.hi < evalFunc1 e I.lo := by linarith
          linarith
        · push_neg at hhi
          by_cases hlo_eq : f I.lo = 0
          · use I.lo
            have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            constructor
            · exact ⟨hIlo_in_I, hlo_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.lo hy_in_I hIlo_in_I hy_root hlo_eq
          · -- f(lo) < 0 and f(hi) < 0 with f decreasing → contradiction via MVT
            have hlo_neg : f I.lo < 0 := lt_of_le_of_ne hlo hlo_eq
            exfalso
            have hMVT := mvt_fc_upper_bound_neg_decreasing_core e hsupp I cfg hI_nonsingleton hdI_neg hCont hlo_neg
            exact generic_contraction_absurd_hi_neg I c fc dI N rfl hdI_nonzero hdI_neg
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg)
              hN_lo hContract.1 hMVT
      · push_neg at hlo
        by_cases hhi : f I.hi ≥ 0
        · by_cases hhi_eq : f I.hi = 0
          · use I.hi
            have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            constructor
            · exact ⟨hIhi_in_I, hhi_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.hi hy_in_I hIhi_in_I hy_root hhi_eq
          · -- f(hi) > 0 and f(lo) > 0 with f decreasing → contradiction via MVT
            have hhi_pos : 0 < f I.hi := lt_of_le_of_ne hhi (Ne.symm hhi_eq)
            exfalso
            have hMVT := mvt_fc_lower_bound_neg_decreasing_core e hsupp I cfg hI_nonsingleton hdI_neg hCont hhi_pos
            exact generic_contraction_absurd_lo_neg I c fc dI N rfl hdI_nonzero hdI_neg
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg)
              hN_hi hContract.2 hMVT
        · -- f(lo) > 0 and f(hi) < 0: SIGN CHANGE for decreasing function!
          push_neg at hhi
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hhi, le_of_lt hlo⟩
          have hivt := intermediate_value_Icc' hle hCont h0_in_range
          obtain ⟨x, hx_mem, hx_root⟩ := hivt
          use x
          constructor
          · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact ⟨hx_in_I, hx_root⟩
          · intro y ⟨hy_in_I, hy_root⟩
            have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y x hy_in_I hx_in_I hy_root hx_root

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

end LeanCert.Validity.RootFinding

/-! ## Integration Certificates -/

namespace LeanCert.Validity.Integration

open LeanCert.Core
open LeanCert.Engine
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
    (cfg : EvalConfig := default) : IntervalRat :=
  sumIntervalBoundsCore e (uniformPartitionCore I n hn) cfg

/-- For single-interval integration (n=1), computable version -/
def integrateInterval1Core (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : IntervalRat :=
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
  have hCont := LeanCert.Meta.exprSupportedCore_continuousOn e hsupp (s := Set.Icc I.lo I.hi)
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
  have ⟨h_lower, h_upper⟩ := LeanCert.Engine.integral_bounds_of_bounds hIle hInt hlo hhi
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
    (cfg : EvalConfig := default) : Bool :=
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
def getIntegralBound (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : IntervalRat :=
  integrateInterval1Core e I cfg

/-- The integral lies within the computed bound (computable version) -/
theorem integral_in_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) :
    (getIntegralBound e I cfg).lo ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∧
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (getIntegralBound e I cfg).hi := by
  have hmem := integrateInterval1Core_correct e hsupp I cfg
  simp only [IntervalRat.mem_def, getIntegralBound] at hmem ⊢
  exact hmem

end LeanCert.Validity.Integration
