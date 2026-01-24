/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Optimization.Global

/-!
# Adaptive Bound Verification via Branch-and-Bound

This file provides adaptive bound verification functions that use the branch-and-bound
global optimization algorithm to verify bounds on expressions. Unlike single-shot
interval evaluation, these functions automatically subdivide the domain until the
bound can be verified or the iteration limit is reached.

## Main definitions

* `verifyUpperBound` - Verify f(x) ≤ bound for all x in box using adaptive subdivision
* `verifyLowerBound` - Verify f(x) ≥ bound for all x in box using adaptive subdivision
* `verifyUpperBound1` - Single-variable version
* `verifyLowerBound1` - Single-variable version

## Main theorems

* `verifyUpperBound_correct` - If `verifyUpperBound` returns true, the bound holds
* `verifyLowerBound_correct` - If `verifyLowerBound` returns true, the bound holds

## Usage

These functions are intended to be used as fallbacks when single-shot interval
evaluation fails due to over-approximation. They provide better precision at the
cost of increased computation.

```lean
-- Single-shot fails on tight bounds, but adaptive succeeds
example : verifyUpperBound1 (Expr.sin (Expr.var 0)) ⟨0, 11/10, by norm_num⟩ (85/100) = true := by
  native_decide
```
-/

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine

/-! ### Configuration for bound verification -/

/-- Configuration for adaptive bound verification -/
structure BoundVerifyConfig where
  /-- Maximum number of subdivisions -/
  maxIterations : Nat := 200
  /-- Stop when box width is below this threshold -/
  tolerance : ℚ := 1/10000
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 15
  /-- Use monotonicity-based pruning (symbolic pre-pass for gradient signs) -/
  useMonotonicity : Bool := true
  deriving Repr, DecidableEq

instance : Inhabited BoundVerifyConfig := ⟨{}⟩

/-- Convert BoundVerifyConfig to GlobalOptConfig -/
def BoundVerifyConfig.toGlobalOptConfig (cfg : BoundVerifyConfig) : GlobalOptConfig :=
  { maxIterations := cfg.maxIterations
    tolerance := cfg.tolerance
    useMonotonicity := cfg.useMonotonicity
    taylorDepth := cfg.taylorDepth }

/-! ### Witness/Epsilon-argmax structures -/

/-- A witness point for an optimization result -/
structure WitnessPoint where
  /-- The coordinates of the witness point -/
  coords : List ℚ
  /-- The function value at this point (interval containing true value) -/
  value : IntervalRat
  deriving Repr

/-- Result of bound verification with witness information -/
structure BoundVerifyResult where
  /-- Whether the bound was verified -/
  verified : Bool
  /-- The computed bound (lo for min, hi for max) -/
  computedBound : ℚ
  /-- Approximate argmin/argmax (midpoint of best box) -/
  witness : WitnessPoint
  /-- Width of the best box (epsilon for ε-approximate argmin/argmax) -/
  epsilon : ℚ
  /-- Number of iterations used -/
  iterations : Nat
  deriving Repr

/-- Extract witness point from a box (midpoint of each interval) -/
def Box.midpoint (B : Box) : List ℚ :=
  B.map fun I => I.midpoint

/-- Compute maximum width of a box (the ε in ε-approximate) -/
def Box.maxWidthQ (B : Box) : ℚ :=
  B.foldl (fun acc I => max acc (I.hi - I.lo)) 0

/-- Evaluate expression at a rational point (using singleton intervals) -/
def evalAtPoint (e : Expr) (point : List ℚ) (cfg : EvalConfig := {}) : IntervalRat :=
  let env : IntervalEnv := fun i =>
    match point[i]? with
    | some q => IntervalRat.singleton q
    | none => IntervalRat.singleton 0
  evalIntervalCore e env cfg

/-! ### Computable bound verification functions -/

/-- Verify f(x) ≤ bound for all x in box using adaptive subdivision.
    Returns true if the maximum of f over the box is ≤ bound. -/
def verifyUpperBound (e : Expr) (B : Box) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  let result := globalMaximizeCore e B cfg.toGlobalOptConfig
  result.bound.hi ≤ bound

/-- Verify f(x) ≥ bound for all x in box using adaptive subdivision.
    Returns true if the minimum of f over the box is ≥ bound. -/
def verifyLowerBound (e : Expr) (B : Box) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  let result := globalMinimizeCore e B cfg.toGlobalOptConfig
  result.bound.lo ≥ bound

/-- Verify f(x) < bound for all x in box using adaptive subdivision.
    Returns true if the maximum of f over the box is < bound. -/
def verifyUpperBoundStrict (e : Expr) (B : Box) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  let result := globalMaximizeCore e B cfg.toGlobalOptConfig
  result.bound.hi < bound

/-- Verify f(x) > bound for all x in box using adaptive subdivision.
    Returns true if the minimum of f over the box is > bound. -/
def verifyLowerBoundStrict (e : Expr) (B : Box) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  let result := globalMinimizeCore e B cfg.toGlobalOptConfig
  result.bound.lo > bound

/-! ### Epsilon-argmax/argmin functions with witness information -/

/-- Find the maximum of f over a box, returning result with witness information.
    The witness is an ε-approximate argmax: a point where f(witness) is within
    ε of the true maximum, where ε = bestBox.maxWidth. -/
def findMaxWithWitness (e : Expr) (B : Box) (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  let result := globalMaximizeCore e B cfg.toGlobalOptConfig
  let midpt := Box.midpoint result.bound.bestBox
  let value := evalAtPoint e midpt { taylorDepth := cfg.taylorDepth }
  { verified := true  -- Always "verified" since we're finding, not checking
    computedBound := result.bound.hi
    witness := { coords := midpt, value := value }
    epsilon := Box.maxWidthQ result.bound.bestBox
    iterations := result.bound.iterations }

/-- Find the minimum of f over a box, returning result with witness information.
    The witness is an ε-approximate argmin: a point where f(witness) is within
    ε of the true minimum, where ε = bestBox.maxWidth. -/
def findMinWithWitness (e : Expr) (B : Box) (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  let result := globalMinimizeCore e B cfg.toGlobalOptConfig
  let midpt := Box.midpoint result.bound.bestBox
  let value := evalAtPoint e midpt { taylorDepth := cfg.taylorDepth }
  { verified := true
    computedBound := result.bound.lo
    witness := { coords := midpt, value := value }
    epsilon := Box.maxWidthQ result.bound.bestBox
    iterations := result.bound.iterations }

/-- Verify f(x) ≤ bound with witness information.
    Returns the verification result along with an ε-approximate argmax. -/
def verifyUpperBoundWithWitness (e : Expr) (B : Box) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  let result := globalMaximizeCore e B cfg.toGlobalOptConfig
  let midpt := Box.midpoint result.bound.bestBox
  let value := evalAtPoint e midpt { taylorDepth := cfg.taylorDepth }
  { verified := result.bound.hi ≤ bound
    computedBound := result.bound.hi
    witness := { coords := midpt, value := value }
    epsilon := Box.maxWidthQ result.bound.bestBox
    iterations := result.bound.iterations }

/-- Verify f(x) ≥ bound with witness information.
    Returns the verification result along with an ε-approximate argmin. -/
def verifyLowerBoundWithWitness (e : Expr) (B : Box) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  let result := globalMinimizeCore e B cfg.toGlobalOptConfig
  let midpt := Box.midpoint result.bound.bestBox
  let value := evalAtPoint e midpt { taylorDepth := cfg.taylorDepth }
  { verified := result.bound.lo ≥ bound
    computedBound := result.bound.lo
    witness := { coords := midpt, value := value }
    epsilon := Box.maxWidthQ result.bound.bestBox
    iterations := result.bound.iterations }

/-! ### Single-variable convenience functions -/

/-- Convert a single interval to a 1D box -/
def intervalToBox (I : IntervalRat) : Box := [I]

/-- Single-variable version of verifyUpperBound -/
def verifyUpperBound1 (e : Expr) (I : IntervalRat) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  verifyUpperBound e (intervalToBox I) bound cfg

/-- Single-variable version of verifyLowerBound -/
def verifyLowerBound1 (e : Expr) (I : IntervalRat) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  verifyLowerBound e (intervalToBox I) bound cfg

/-- Single-variable version of verifyUpperBoundStrict -/
def verifyUpperBound1Strict (e : Expr) (I : IntervalRat) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  verifyUpperBoundStrict e (intervalToBox I) bound cfg

/-- Single-variable version of verifyLowerBoundStrict -/
def verifyLowerBound1Strict (e : Expr) (I : IntervalRat) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : Bool :=
  verifyLowerBoundStrict e (intervalToBox I) bound cfg

/-- Single-variable version of findMaxWithWitness -/
def findMax1WithWitness (e : Expr) (I : IntervalRat) (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  findMaxWithWitness e (intervalToBox I) cfg

/-- Single-variable version of findMinWithWitness -/
def findMin1WithWitness (e : Expr) (I : IntervalRat) (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  findMinWithWitness e (intervalToBox I) cfg

/-- Single-variable version of verifyUpperBoundWithWitness -/
def verifyUpperBound1WithWitness (e : Expr) (I : IntervalRat) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  verifyUpperBoundWithWitness e (intervalToBox I) bound cfg

/-- Single-variable version of verifyLowerBoundWithWitness -/
def verifyLowerBound1WithWitness (e : Expr) (I : IntervalRat) (bound : ℚ)
    (cfg : BoundVerifyConfig := {}) : BoundVerifyResult :=
  verifyLowerBoundWithWitness e (intervalToBox I) bound cfg

/-! ### Correctness theorems (noncomputable proofs) -/

/-- Helper: convert single-variable environment to box membership -/
theorem intervalToBox_envMem (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    Box.envMem (fun _ => x) (intervalToBox I) := by
  intro ⟨i, hi⟩
  simp only [intervalToBox, List.length_singleton] at hi
  have hi' : i = 0 := Nat.lt_one_iff.mp hi
  subst hi'
  simp only [intervalToBox, List.getElem_cons_zero]
  exact hx

/-- Helper: if i ≥ 1, then (fun _ => x) i = 0 is vacuously satisfiable for our purposes -/
theorem intervalToBox_zero (I : IntervalRat) (x : ℝ) :
    ∀ i, i ≥ (intervalToBox I).length → (fun _ => x) i = x := by
  intro i _; rfl

/-- If verifyUpperBound succeeds, the upper bound holds for all points in the box.
    Note: This uses the noncomputable globalMaximize for the proof, but the
    computable globalMaximizeCore is used for execution. -/
theorem verifyUpperBound_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (bound : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMaximize e B cfg.toGlobalOptConfig).bound.hi ≤ bound) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ bound := by
  intro ρ hρ hzero
  -- globalMaximize returns -globalMinimize(-e), so hi = -lo of minimization
  -- We have: for all ρ, globalMinimize(-e).lo ≤ -eval ρ e
  -- Therefore: eval ρ e ≤ -globalMinimize(-e).lo = globalMaximize(e).hi
  have hmax := globalMinimize_lo_correct (Expr.neg e) (ExprSupported.neg hsupp) B cfg.toGlobalOptConfig ρ hρ hzero
  simp only [Expr.eval_neg] at hmax ⊢
  -- hmax : (globalMinimize (Expr.neg e) B cfg.toGlobalOptConfig).bound.lo ≤ -Expr.eval ρ e
  -- Goal : Expr.eval ρ e ≤ bound
  -- We have: globalMaximize.hi = -(globalMinimize (neg e)).lo
  have hhi_eq : (globalMaximize e B cfg.toGlobalOptConfig).bound.hi =
      -(globalMinimize (Expr.neg e) B cfg.toGlobalOptConfig).bound.lo := by
    simp only [globalMaximize]
  rw [hhi_eq] at hverify
  -- hverify : -(globalMinimize (Expr.neg e) ...).bound.lo ≤ bound
  -- hmax : (globalMinimize (Expr.neg e) ...).bound.lo ≤ -Expr.eval ρ e
  have h1 : Expr.eval ρ e ≤ -(globalMinimize (Expr.neg e) B cfg.toGlobalOptConfig).bound.lo := by
    linarith [hmax]
  calc Expr.eval ρ e
    ≤ -(globalMinimize (Expr.neg e) B cfg.toGlobalOptConfig).bound.lo := h1
    _ ≤ bound := by exact_mod_cast hverify

/-- If verifyLowerBound succeeds, the lower bound holds for all points in the box. -/
theorem verifyLowerBound_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (bound : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMinimize e B cfg.toGlobalOptConfig).bound.lo ≥ bound) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      bound ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  have hmin := globalMinimize_lo_correct e hsupp B cfg.toGlobalOptConfig ρ hρ hzero
  calc (bound : ℝ)
    ≤ (globalMinimize e B cfg.toGlobalOptConfig).bound.lo := by exact_mod_cast hverify
    _ ≤ Expr.eval ρ e := hmin

/-! ### Expression uses only var 0 -/

/-- Predicate: expression only uses variable index 0 -/
def Expr.usesOnlyVar0 : Expr → Bool
  | .const _ => true
  | .var i => i == 0
  | .add e1 e2 => e1.usesOnlyVar0 && e2.usesOnlyVar0
  | .mul e1 e2 => e1.usesOnlyVar0 && e2.usesOnlyVar0
  | .neg e => e.usesOnlyVar0
  | .inv e => e.usesOnlyVar0
  | .exp e => e.usesOnlyVar0
  | .sin e => e.usesOnlyVar0
  | .cos e => e.usesOnlyVar0
  | .log e => e.usesOnlyVar0
  | .atan e => e.usesOnlyVar0
  | .arsinh e => e.usesOnlyVar0
  | .atanh e => e.usesOnlyVar0
  | .sinc e => e.usesOnlyVar0
  | .erf e => e.usesOnlyVar0
  | .sinh e => e.usesOnlyVar0
  | .cosh e => e.usesOnlyVar0
  | .tanh e => e.usesOnlyVar0
  | .sqrt e => e.usesOnlyVar0
  | .pi => true

/-- If an expression uses only var 0, evaluation depends only on ρ 0 -/
theorem Expr.eval_usesOnlyVar0 (e : Expr) (he : e.usesOnlyVar0 = true)
    (ρ ρ' : Nat → ℝ) (h0 : ρ 0 = ρ' 0) : Expr.eval ρ e = Expr.eval ρ' e := by
  induction e with
  | const q => rfl
  | var i =>
    -- usesOnlyVar0 (var i) = (i == 0), so he : (i == 0) = true
    have hi : i = 0 := by
      change (i == 0) = true at he
      exact beq_iff_eq.mp he
    simp only [Expr.eval, hi, h0]
  | add e1 e2 ih1 ih2 =>
    -- usesOnlyVar0 (add e1 e2) = e1.usesOnlyVar0 && e2.usesOnlyVar0
    have he' : e1.usesOnlyVar0 = true ∧ e2.usesOnlyVar0 = true := by
      change (e1.usesOnlyVar0 && e2.usesOnlyVar0) = true at he
      exact Bool.and_eq_true_iff.mp he
    simp only [Expr.eval, ih1 he'.1, ih2 he'.2]
  | mul e1 e2 ih1 ih2 =>
    have he' : e1.usesOnlyVar0 = true ∧ e2.usesOnlyVar0 = true := by
      change (e1.usesOnlyVar0 && e2.usesOnlyVar0) = true at he
      exact Bool.and_eq_true_iff.mp he
    simp only [Expr.eval, ih1 he'.1, ih2 he'.2]
  | neg e ih => simp only [Expr.eval, ih he]
  | inv e ih => simp only [Expr.eval, ih he]
  | exp e ih => simp only [Expr.eval, ih he]
  | sin e ih => simp only [Expr.eval, ih he]
  | cos e ih => simp only [Expr.eval, ih he]
  | log e ih => simp only [Expr.eval, ih he]
  | atan e ih => simp only [Expr.eval, ih he]
  | arsinh e ih => simp only [Expr.eval, ih he]
  | atanh e ih => simp only [Expr.eval, ih he]
  | sinc e ih => simp only [Expr.eval, ih he]
  | erf e ih => simp only [Expr.eval, ih he]
  | sinh e ih => simp only [Expr.eval, ih he]
  | cosh e ih => simp only [Expr.eval, ih he]
  | tanh e ih => simp only [Expr.eval, ih he]
  | sqrt e ih => simp only [Expr.eval, ih he]
  | pi => rfl

/-! ### Tactic-facing lemmas for adaptive bound verification -/

/-- Tactic-facing lemma: if adaptive verification succeeds, upper bound holds.
    This is the key lemma that tactics use to close goals.
    Requires that the expression uses only var 0. -/
theorem adaptive_upper_bound (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (I : IntervalRat) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMaximize e [I] cfg.toGlobalOptConfig).bound.hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  -- Construct ρ' : Nat → ℝ with ρ' 0 = x and ρ' i = 0 for i ≥ 1
  let ρ' : Nat → ℝ := fun i => if i = 0 then x else 0
  have hρ'mem : Box.envMem ρ' [I] := by
    intro ⟨i, hi⟩
    simp only [List.length_singleton] at hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    simp only [List.getElem_cons_zero, ρ', ↓reduceIte]
    exact hx
  have hρ'zero : ∀ i, i ≥ ([I] : Box).length → ρ' i = 0 := by
    intro i hi
    simp only [List.length_singleton] at hi
    simp only [ρ']
    split_ifs with h
    · omega
    · rfl
  have h := verifyUpperBound_correct e hsupp [I] c cfg hverify ρ' hρ'mem hρ'zero
  -- Use the fact that e only uses var 0 to relate the two evaluations
  have heq : Expr.eval (fun _ => x) e = Expr.eval ρ' e := by
    apply Expr.eval_usesOnlyVar0 e he
    simp only [ρ', ↓reduceIte]
  rw [heq]
  exact h

/-- Tactic-facing lemma: if adaptive verification succeeds, lower bound holds.
    Requires that the expression uses only var 0. -/
theorem adaptive_lower_bound (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (I : IntervalRat) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMinimize e [I] cfg.toGlobalOptConfig).bound.lo ≥ c) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  let ρ' : Nat → ℝ := fun i => if i = 0 then x else 0
  have hρ'mem : Box.envMem ρ' [I] := by
    intro ⟨i, hi⟩
    simp only [List.length_singleton] at hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    simp only [List.getElem_cons_zero, ρ', ↓reduceIte]
    exact hx
  have hρ'zero : ∀ i, i ≥ ([I] : Box).length → ρ' i = 0 := by
    intro i hi
    simp only [List.length_singleton] at hi
    simp only [ρ']
    split_ifs with h
    · omega
    · rfl
  have h := verifyLowerBound_correct e hsupp [I] c cfg hverify ρ' hρ'mem hρ'zero
  have heq : Expr.eval (fun _ => x) e = Expr.eval ρ' e := by
    apply Expr.eval_usesOnlyVar0 e he
    simp only [ρ', ↓reduceIte]
  rw [heq]
  exact h

/-- Strict upper bound version -/
theorem adaptive_upper_bound_strict (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (I : IntervalRat) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMaximize e [I] cfg.toGlobalOptConfig).bound.hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  let ρ' : Nat → ℝ := fun i => if i = 0 then x else 0
  have hρ'mem : Box.envMem ρ' [I] := by
    intro ⟨i, hi⟩
    simp only [List.length_singleton] at hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    simp only [List.getElem_cons_zero, ρ', ↓reduceIte]
    exact hx
  have hρ'zero : ∀ i, i ≥ ([I] : Box).length → ρ' i = 0 := by
    intro i hi
    simp only [List.length_singleton] at hi
    simp only [ρ']
    split_ifs with h; omega; rfl
  -- Use strict bound from verification
  have hmax := globalMinimize_lo_correct (Expr.neg e) (ExprSupported.neg hsupp) [I] cfg.toGlobalOptConfig ρ' hρ'mem hρ'zero
  simp only [Expr.eval_neg] at hmax
  have hhi_eq : (globalMaximize e [I] cfg.toGlobalOptConfig).bound.hi =
      -(globalMinimize (Expr.neg e) [I] cfg.toGlobalOptConfig).bound.lo := by
    simp only [globalMaximize]
  have heq : Expr.eval (fun _ => x) e = Expr.eval ρ' e := by
    apply Expr.eval_usesOnlyVar0 e he
    simp only [ρ', ↓reduceIte]
  rw [heq]
  have hbound : Expr.eval ρ' e ≤ -(globalMinimize (Expr.neg e) [I] cfg.toGlobalOptConfig).bound.lo := by
    linarith [hmax]
  have hhi_lt : (-(globalMinimize (Expr.neg e) [I] cfg.toGlobalOptConfig).bound.lo : ℝ) < c := by
    have : ((globalMaximize e [I] cfg.toGlobalOptConfig).bound.hi : ℝ) < c := by exact_mod_cast hverify
    simp only [globalMaximize, Rat.cast_neg] at this
    exact this
  calc Expr.eval ρ' e
    ≤ -(globalMinimize (Expr.neg e) [I] cfg.toGlobalOptConfig).bound.lo := hbound
    _ < c := hhi_lt

/-- Strict lower bound version -/
theorem adaptive_lower_bound_strict (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (I : IntervalRat) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMinimize e [I] cfg.toGlobalOptConfig).bound.lo > c) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  let ρ' : Nat → ℝ := fun i => if i = 0 then x else 0
  have hρ'mem : Box.envMem ρ' [I] := by
    intro ⟨i, hi⟩
    simp only [List.length_singleton] at hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    simp only [List.getElem_cons_zero, ρ', ↓reduceIte]
    exact hx
  have hρ'zero : ∀ i, i ≥ ([I] : Box).length → ρ' i = 0 := by
    intro i hi
    simp only [List.length_singleton] at hi
    simp only [ρ']
    split_ifs with h; omega; rfl
  have hmin := globalMinimize_lo_correct e hsupp [I] cfg.toGlobalOptConfig ρ' hρ'mem hρ'zero
  have heq : Expr.eval (fun _ => x) e = Expr.eval ρ' e := by
    apply Expr.eval_usesOnlyVar0 e he
    simp only [ρ', ↓reduceIte]
  rw [heq]
  calc (c : ℝ)
    < (globalMinimize e [I] cfg.toGlobalOptConfig).bound.lo := by exact_mod_cast hverify
    _ ≤ Expr.eval ρ' e := hmin

/-! ### Theorem versions for Set.Icc (for tactic compatibility) -/

/-- Adaptive upper bound for Set.Icc membership -/
theorem adaptive_upper_bound_Icc (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMaximize e [⟨lo, hi, hle⟩] cfg.toGlobalOptConfig).bound.hi ≤ c) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hxI : x ∈ (⟨lo, hi, hle⟩ : IntervalRat) := by
    simp only [IntervalRat.mem_def]
    exact ⟨hx.1, hx.2⟩
  exact adaptive_upper_bound e hsupp he ⟨lo, hi, hle⟩ c cfg hverify x hxI

/-- Adaptive lower bound for Set.Icc membership -/
theorem adaptive_lower_bound_Icc (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMinimize e [⟨lo, hi, hle⟩] cfg.toGlobalOptConfig).bound.lo ≥ c) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hxI : x ∈ (⟨lo, hi, hle⟩ : IntervalRat) := by
    simp only [IntervalRat.mem_def]
    exact ⟨hx.1, hx.2⟩
  exact adaptive_lower_bound e hsupp he ⟨lo, hi, hle⟩ c cfg hverify x hxI

/-- Strict upper bound for Set.Icc -/
theorem adaptive_upper_bound_Icc_strict (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMaximize e [⟨lo, hi, hle⟩] cfg.toGlobalOptConfig).bound.hi < c) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hxI : x ∈ (⟨lo, hi, hle⟩ : IntervalRat) := by
    simp only [IntervalRat.mem_def]
    exact ⟨hx.1, hx.2⟩
  exact adaptive_upper_bound_strict e hsupp he ⟨lo, hi, hle⟩ c cfg hverify x hxI

/-- Strict lower bound for Set.Icc -/
theorem adaptive_lower_bound_Icc_strict (e : Expr) (hsupp : ExprSupported e)
    (he : e.usesOnlyVar0 = true)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : BoundVerifyConfig)
    (hverify : (globalMinimize e [⟨lo, hi, hle⟩] cfg.toGlobalOptConfig).bound.lo > c) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hxI : x ∈ (⟨lo, hi, hle⟩ : IntervalRat) := by
    simp only [IntervalRat.mem_def]
    exact ⟨hx.1, hx.2⟩
  exact adaptive_lower_bound_strict e hsupp he ⟨lo, hi, hle⟩ c cfg hverify x hxI

end LeanCert.Engine.Optimization
