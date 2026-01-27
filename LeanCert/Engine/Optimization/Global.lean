/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalRefined
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalAffine
import LeanCert.Engine.Affine.Basic
import LeanCert.Engine.Optimization.Box
import LeanCert.Engine.Optimization.Gradient

-- Suppress linter warnings for redundant tactics in all_goals first blocks
-- These proofs use first to handle multiple cases robustly, but some branches
-- may be redundant depending on which goals split_ifs generates
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Global Optimization via Branch-and-Bound

This file implements a branch-and-bound algorithm for rigorous global optimization
of expressions over n-dimensional boxes.

## Main definitions

* `GlobalBound` - Result of global optimization (lower bound and optional upper bound)
* `globalMinimize` - Branch-and-bound minimization over a box
* `globalMaximize` - Branch-and-bound maximization over a box

## Algorithm

The branch-and-bound algorithm works by:
1. Evaluating the expression over the current box using interval arithmetic
2. Using the interval lower bound to prune boxes that can't contain the minimum
3. Splitting the widest dimension when bounds aren't tight enough
4. Optionally pruning using monotonicity (gradient sign information)

## Correctness

The algorithm maintains the invariant that the returned lower bound is ≤ f(x)
for all x in the original box. When the interval upper bound equals the lower
bound (or is close enough), we have found the global minimum.
-/

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Affine

/-! ### Configuration -/

/-- Configuration for global optimization -/
structure GlobalOptConfig where
  /-- Maximum number of subdivisions -/
  maxIterations : Nat := 1000
  /-- Stop when box width is below this threshold -/
  tolerance : ℚ := 1/1000
  /-- Use monotonicity pruning (requires gradient computation) -/
  useMonotonicity : Bool := false
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr

instance : Inhabited GlobalOptConfig := ⟨{}⟩

/-! ### Result types -/

/-- Result of global optimization -/
structure GlobalBound where
  /-- Lower bound: f(x) ≥ lo for all x in the box -/
  lo : ℚ
  /-- Upper bound: there exists x in box with f(x) ≤ hi -/
  hi : ℚ
  /-- Best box found (smallest interval containing minimum) -/
  bestBox : Box
  /-- Number of iterations used -/
  iterations : Nat
  deriving Repr

/-- Result of optimization with certificate data -/
structure GlobalResult where
  /-- The computed bound -/
  bound : GlobalBound
  /-- Priority queue of remaining boxes (for resumption) -/
  remainingBoxes : List (ℚ × Box)  -- (lower bound, box)
  deriving Repr

/-! ### Priority queue operations -/

/-- Insert a box with its lower bound into a sorted list (ascending by bound) -/
def insertByBound (queue : List (ℚ × Box)) (lb : ℚ) (B : Box) : List (ℚ × Box) :=
  match queue with
  | [] => [(lb, B)]
  | (lb', B') :: rest =>
    if lb ≤ lb' then (lb, B) :: queue
    else (lb', B') :: insertByBound rest lb B

/-- Pop the box with smallest lower bound -/
def popBest (queue : List (ℚ × Box)) : Option ((ℚ × Box) × List (ℚ × Box)) :=
  match queue with
  | [] => none
  | best :: rest => some (best, rest)

/-! ### Generic Branch-and-Bound Algorithm

The following generic functions implement the core branch-and-bound algorithm
parameterized by an evaluator function. This allows different interval arithmetic
backends (Rational, Dyadic, Affine) to share the same optimization logic.
-/

/-- Generic one step of branch-and-bound for minimization.
    Takes an evaluator function `eval : Box → IntervalRat` that computes interval bounds.
    The evaluator encapsulates the expression, configuration, and interval arithmetic backend.

    When `useMonotonicity` is true, applies gradient-based pruning using `gradientIntervalCore`.
    The gradient computation always uses rational arithmetic for simplicity.

    Parameters:
    - `eval`: Evaluator function mapping boxes to interval bounds
    - `gradEval`: Optional gradient evaluator for monotonicity pruning
    - `useMonotonicity`: Whether to apply gradient-based box pruning
    - `tolerance`: Stop splitting when box width is below this threshold
    - `queue`: Priority queue of (lower_bound, box) pairs
    - `bestLB`: Current best global lower bound
    - `bestUB`: Current best upper bound (achievable)
    - `bestBox`: Box containing the best found point -/
def minimizeStepGeneric
    (eval : Box → IntervalRat)
    (gradEval : Box → List IntervalRat)
    (useMonotonicity : Bool)
    (tolerance : ℚ)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  match popBest queue with
  | none => none
  | some ((lb, B), rest) =>
    if lb > bestUB then
      -- Prune this box; bounds unchanged
      some (rest, bestLB, bestUB, bestBox)
    else
      -- Step 1: Optionally apply monotonicity-based pruning
      let B_curr :=
        if useMonotonicity then
          let grad := gradEval B
          (pruneBoxForMin B grad).1
        else B
      -- Step 2: Evaluate on (potentially pruned) box
      let I := eval B_curr
      -- Update global lower bound: min of old and this box's local lower bound
      let newBestLB := min bestLB I.lo
      -- Possibly improve upper bound
      let (newBestUB, newBestBox) :=
        if I.hi < bestUB then (I.hi, B_curr) else (bestUB, bestBox)
      if Box.maxWidth B_curr ≤ tolerance then
        -- Box is small enough: don't split further
        some (rest, newBestLB, newBestUB, newBestBox)
      else
        -- Step 3: Split and add children
        let (B1, B2) := Box.splitWidest B_curr
        let I1 := eval B1
        let I2 := eval B2
        -- Insert children if they might improve the minimum
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Generic branch-and-bound loop for minimization.
    Iteratively calls `minimizeStepGeneric` until either:
    - The queue is empty (optimal found)
    - Maximum iterations reached

    Parameters:
    - `eval`: Evaluator function mapping boxes to interval bounds
    - `gradEval`: Gradient evaluator for monotonicity pruning
    - `useMonotonicity`: Whether to apply gradient-based pruning
    - `tolerance`: Stop splitting when box width is below this threshold
    - `maxIterations`: Maximum iterations for the result's iteration count
    - `queue`, `bestLB`, `bestUB`, `bestBox`: Current state
    - `iters`: Remaining iterations -/
def minimizeLoopGeneric
    (eval : Box → IntervalRat)
    (gradEval : Box → List IntervalRat)
    (useMonotonicity : Bool)
    (tolerance : ℚ)
    (maxIterations : Nat)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepGeneric eval gradEval useMonotonicity tolerance queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopGeneric eval gradEval useMonotonicity tolerance maxIterations queue' bestLB' bestUB' bestBox' n

/-- Helper: create gradient evaluator from expression and config -/
def mkGradEval (e : Expr) (taylorDepth : Nat) : Box → List IntervalRat :=
  fun B => gradientIntervalCore e B { taylorDepth := taylorDepth }

/-! ### Core algorithm -/

/-- Evaluate expression on a box and get interval bounds -/
noncomputable def evalOnBox (e : Expr) (B : Box) (_cfg : GlobalOptConfig) : IntervalRat :=
  evalIntervalRefined e (Box.toEnv B)

/-- One step of branch-and-bound for minimization with explicit bestLB tracking.
    When `cfg.useMonotonicity` is true, applies gradient-based pruning before evaluation. -/
noncomputable def minimizeStep (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  match popBest queue with
  | none => none
  | some ((lb, B), rest) =>
    -- If this box's lower bound is already worse than best, skip it
    if lb > bestUB then
      -- Prune this box; bounds unchanged
      some (rest, bestLB, bestUB, bestBox)
    else
      -- Step 1: Optionally apply monotonicity-based pruning
      let B_curr :=
        if cfg.useMonotonicity then
          let grad := gradientIntervalN e B B.length
          (pruneBoxForMin B grad).1
        else B
      -- Step 2: Evaluate on (potentially pruned) box
      let I := evalOnBox e B_curr cfg
      -- Update global lower bound: min of old and this box's local lower bound
      let newBestLB := min bestLB I.lo
      -- Update best upper bound if we found a better one
      let (newBestUB, newBestBox) :=
        if I.hi < bestUB then (I.hi, B_curr) else (bestUB, bestBox)
      -- Check if box is small enough
      if Box.maxWidth B_curr ≤ cfg.tolerance then
        -- Accept this box, continue with rest
        some (rest, newBestLB, newBestUB, newBestBox)
      else
        -- Step 3: Split and add children
        let (B1, B2) := Box.splitWidest B_curr
        let I1 := evalOnBox e B1 cfg
        let I2 := evalOnBox e B2 cfg
        -- Only add boxes that can potentially improve
        let queue' := rest
        let queue' := if I1.lo ≤ newBestUB then insertByBound queue' I1.lo B1 else queue'
        let queue' := if I2.lo ≤ newBestUB then insertByBound queue' I2.lo B2 else queue'
        some (queue', newBestLB, newBestUB, newBestBox)

/-- Run branch-and-bound for a fixed number of iterations with explicit bestLB tracking -/
noncomputable def minimizeLoop (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStep e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoop e cfg queue' bestLB' bestUB' bestBox' n

/-- Global minimization over a box -/
noncomputable def globalMinimize (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let I := evalOnBox e B cfg
  let initialQueue : List (ℚ × Box) := [(I.lo, B)]
  let initialBestLB : ℚ := I.lo
  let initialBestUB : ℚ := I.hi
  let initialBestBox : Box := B
  minimizeLoop e cfg initialQueue initialBestLB initialBestUB initialBestBox cfg.maxIterations

/-- Global maximization over a box (minimize -e) -/
noncomputable def globalMaximize (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let result := globalMinimize (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Computable versions for execution -/

/-- Evaluate expression on a box (computable version for ExprSupportedCore) -/
def evalOnBoxCore (e : Expr) (B : Box) (cfg : GlobalOptConfig) : IntervalRat :=
  evalIntervalCore e (Box.toEnv B) { taylorDepth := cfg.taylorDepth }


/-- Evaluate expression on a box (computable version with division support).
    This is used by the Python bridge for applications where division is common.
    Note: No formal correctness proof yet; returns sound but possibly wide bounds. -/
def evalOnBoxCoreDiv (e : Expr) (B : Box) (cfg : GlobalOptConfig) : IntervalRat :=
  evalIntervalCoreWithDiv e (Box.toEnv B) { taylorDepth := cfg.taylorDepth }

/-- One step of branch-and-bound (computable version) with explicit bestLB tracking.
    When `cfg.useMonotonicity` is true, applies gradient-based pruning before evaluation.
    This is a thin wrapper around the generic `minimizeStepGeneric`. -/
def minimizeStepCore (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  minimizeStepGeneric
    (fun B => evalOnBoxCore e B cfg)
    (mkGradEval e cfg.taylorDepth)
    cfg.useMonotonicity
    cfg.tolerance
    queue bestLB bestUB bestBox

/-- Run branch-and-bound (computable version) with explicit bestLB tracking.
    This is a thin wrapper around the generic `minimizeLoopGeneric`. -/
def minimizeLoopCore (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepCore e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopCore e cfg queue' bestLB' bestUB' bestBox' n

/-- Global minimization (computable version) -/
def globalMinimizeCore (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let I := evalOnBoxCore e B cfg
  let initialQueue : List (ℚ × Box) := [(I.lo, B)]
  let initialBestLB : ℚ := I.lo
  let initialBestUB : ℚ := I.hi
  let initialBestBox : Box := B
  minimizeLoopCore e cfg initialQueue initialBestLB initialBestUB initialBestBox cfg.maxIterations

/-- Global maximization (computable version) -/
def globalMaximizeCore (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let result := globalMinimizeCore (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Division-supporting versions for Python bridge

These variants use evalIntervalCoreWithDiv which handles division (inv) properly.
They have the same structure as the standard versions but support expressions with division. -/

/-- One step of branch-and-bound with division support -/
def minimizeStepCoreDiv (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  minimizeStepGeneric
    (fun B => evalOnBoxCoreDiv e B cfg)
    (mkGradEval e cfg.taylorDepth)
    cfg.useMonotonicity
    cfg.tolerance
    queue bestLB bestUB bestBox

/-- Run branch-and-bound loop with division support -/
def minimizeLoopCoreDiv (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepCoreDiv e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopCoreDiv e cfg queue' bestLB' bestUB' bestBox' n

/-- Global minimization with division support -/
def globalMinimizeCoreDiv (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let I := evalOnBoxCoreDiv e B cfg
  let initialQueue : List (ℚ × Box) := [(I.lo, B)]
  minimizeLoopCoreDiv e cfg initialQueue I.lo I.hi B cfg.maxIterations

/-- Global maximization with division support -/
def globalMaximizeCoreDiv (e : Expr) (B : Box) (cfg : GlobalOptConfig := {}) : GlobalResult :=
  let result := globalMinimizeCoreDiv (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Correctness theorems -/

/-- The lower bound from interval evaluation is correct. -/
theorem evalOnBox_lo_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    (evalOnBox e B cfg).lo ≤ Expr.eval ρ e := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalRefined_correct e hsupp ρ (Box.toEnv B) henv
  simp only [evalOnBox]
  exact hmem.1

/-- The upper bound from interval evaluation is correct (∃ point achieving it). -/
theorem evalOnBox_hi_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0) :
    Expr.eval ρ e ≤ (evalOnBox e B cfg).hi := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalRefined_correct e hsupp ρ (Box.toEnv B) henv
  simp only [evalOnBox]
  exact hmem.2

/-- Helper: construct a midpoint environment for a box -/
noncomputable def Box.midpointEnv (B : Box) : Nat → ℝ :=
  fun i => if h : i < B.length then (B[i].midpoint : ℝ) else 0

/-- The midpoint environment is in the box -/
theorem Box.midpointEnv_mem (B : Box) : Box.envMem (Box.midpointEnv B) B := by
  intro ⟨i, hi⟩
  simp only [midpointEnv, hi, ↓reduceDIte]
  exact IntervalRat.midpoint_mem _

/-- The midpoint environment is zero outside the box -/
theorem Box.midpointEnv_zero (B : Box) : ∀ i, i ≥ B.length → Box.midpointEnv B i = 0 := by
  intro i hi
  simp only [midpointEnv]
  split_ifs with h
  · exact absurd h (not_lt.mpr hi)
  · rfl

/-- Helper lemma: split preserves box length -/
theorem Box.split_length_eq (B : Box) (d : Nat) :
    (Box.split B d).1.length = B.length ∧ (Box.split B d).2.length = B.length := by
  simp only [Box.split]
  split_ifs with h
  · constructor <;> simp only [List.length_set]
  · exact ⟨rfl, rfl⟩

/-- Helper lemma: splitWidest preserves box length -/
theorem Box.splitWidest_length_eq (B : Box) :
    (Box.splitWidest B).1.length = B.length ∧ (Box.splitWidest B).2.length = B.length :=
  Box.split_length_eq B (Box.widestDim B)

/-! ### New simplified correctness architecture with explicit bestLB tracking

The key idea: track both bestLB (global lower bound) and bestUB (global upper bound) explicitly.
This makes the invariants much simpler:
- (Global LB) For all ρ in the original box, bestLB ≤ f(ρ)
- (Global UB witness) There exists ρ* in bestBox such that f(ρ*) ≤ bestUB
- (Queue boxes are sub-boxes) Every B' in queue is a sub-box of the original box
-/

/-- Membership in insertByBound: element is either the inserted one or was in original -/
theorem mem_insertByBound (queue : List (ℚ × Box)) (lb : ℚ) (B : Box) (lb' : ℚ) (B' : Box) :
    (lb', B') ∈ insertByBound queue lb B ↔ (lb', B') = (lb, B) ∨ (lb', B') ∈ queue := by
  induction queue with
  | nil => simp only [insertByBound, List.mem_singleton]; tauto
  | cons hd tl ih =>
    simp only [insertByBound]
    split_ifs with h_le
    all_goals simp [List.mem_cons, *]
    all_goals tauto

/-- minimizeStep always returns some for non-empty queue -/
theorem minimizeStep_nonempty (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    ∃ result, minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some result := by
  simp only [minimizeStep, popBest]
  split_ifs <;> exact ⟨_, rfl⟩

/-- Helper: bestUB only decreases during minimizeStep -/
theorem minimizeStep_bestUB_le (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
    bestUB' ≤ bestUB := by
  cases queue with
  | nil => simp [minimizeStep, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStep, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, _, hUB, _⟩
    all_goals rw [← hUB]
    all_goals exact le_of_lt ‹_›

/-- Helper: bestLB only decreases during minimizeStep -/
theorem minimizeStep_bestLB_le (e : Expr) (cfg : GlobalOptConfig)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
    bestLB' ≤ bestLB := by
  cases queue with
  | nil => simp [minimizeStep, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStep, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, hLB, _, _⟩
    all_goals rw [← hLB]
    all_goals exact min_le_left _ _

/-- Helper: new queue entries either come from original tail or have lb ≤ newBestUB -/
theorem minimizeStep_queue_entries (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (lb : ℚ) (B' : Box) (hmem : (lb, B') ∈ queue') :
    (lb, B') ∈ tl ∨ lb ≤ bestUB' := by
  simp only [minimizeStep, popBest] at hStep
  split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
  all_goals rcases hStep with ⟨hQ, _, hUB, _⟩
  all_goals rw [← hQ] at hmem
  all_goals rw [← hUB]
  all_goals first
    | (rw [mem_insertByBound] at hmem
       rcases hmem with ⟨rfl, _⟩ | hmem
       · right; assumption
       · rw [mem_insertByBound] at hmem
         rcases hmem with ⟨rfl, _⟩ | hmem
         · right; assumption
         · left; exact hmem)
    | (rw [mem_insertByBound] at hmem
       rcases hmem with ⟨rfl, _⟩ | hmem
       · right; assumption
       · left; exact hmem)
    | (left; exact hmem)

/-- Helper: bestBox' is either bestBox or a subset of hd.2 (the pruned box B_curr).
    When monotonicity pruning is enabled, bestBox' may be the pruned version of hd.2. -/
theorem minimizeStep_bestBox_cases (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox')) :
    bestBox' = bestBox ∨
    bestBox' = (if cfg.useMonotonicity then
        (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2) := by
  simp only [minimizeStep, popBest] at hStep
  split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
  all_goals rcases hStep with ⟨_, _, _, hBox⟩
  all_goals rw [← hBox]
  all_goals first | left; rfl | right; simp_all

/-- Helper: queue entries in result are either from tl or splits of B_curr (the possibly pruned hd.2) -/
theorem minimizeStep_queue_boxes (e : Expr) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (lb : ℚ) (B' : Box) (hmem : (lb, B') ∈ queue') :
    let B_curr := if cfg.useMonotonicity then
        (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2
    (lb, B') ∈ tl ∨ B' = (Box.splitWidest B_curr).1 ∨ B' = (Box.splitWidest B_curr).2 := by
  simp only [minimizeStep, popBest] at hStep
  split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
  all_goals first
    | (cases hStep; left; assumption)  -- prune case and small case
    | (rcases hStep with ⟨hQ, _, _, _⟩
       subst hQ  -- substitute queue' directly
       -- Simplify the goal using all hypotheses about the conditions
       simp_all only [ite_true, true_or]
       -- Now hmem can be in insertByBound forms or just tl
       -- The structure is insertByBound(insertByBound(tl, I1.lo, B1), I2.lo, B2)
       -- So first unpack gives B2 (splitWidest.2), second gives B1 (splitWidest.1)
       first
         | done  -- simp_all closed the goal
         | (-- Both children added: unwrap B2 first, then B1
            rw [mem_insertByBound] at hmem
            rcases hmem with ⟨rfl, _⟩ | hmem
            · right; right; rfl  -- B' = splitWidest.2
            · rw [mem_insertByBound] at hmem
              rcases hmem with ⟨rfl, _⟩ | hmem
              · right; left; rfl  -- B' = splitWidest.1
              · left; exact hmem)  -- B' ∈ tl
         | (-- Only B2 added
            rw [mem_insertByBound] at hmem
            rcases hmem with ⟨rfl, _⟩ | hmem
            · right; right; rfl
            · left; exact hmem)
         | (-- Only B1 added
            rw [mem_insertByBound] at hmem
            rcases hmem with ⟨rfl, _⟩ | hmem
            · right; left; rfl
            · left; exact hmem))

/-- Helper: bestUB' is achievable if bestUB is achievable -/
theorem minimizeStep_bestUB_achievable (e : Expr) (hsupp : ExprSupported e) (cfg : GlobalOptConfig)
    (hd : ℚ × Box) (tl : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg (hd :: tl) bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (hBestUB : ∃ ρ, Box.envMem ρ bestBox ∧ (∀ i, i ≥ bestBox.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ bestUB) :
    ∃ ρ, Box.envMem ρ bestBox' ∧ (∀ i, i ≥ bestBox'.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ bestUB' := by
  simp only [minimizeStep, popBest] at hStep
  -- Handle all cases by explicit branching
  by_cases h_prune : hd.1 > bestUB
  · simp only [h_prune, ↓reduceIte] at hStep
    cases hStep; exact hBestUB
  · simp only [h_prune, ↓reduceIte] at hStep
    -- Define B_curr based on useMonotonicity
    set B_curr := if cfg.useMonotonicity then
        (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2 with hB_curr
    -- Continue splitting the conditionals
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals first
      | (-- No improvement: (bestUB, bestBox) was kept
         rcases hStep with ⟨_, _, hUB, hBox⟩
         rw [← hBox, ← hUB]
         exact hBestUB)
      | (-- Improvement case: bestBox' = B_curr, bestUB' = (evalOnBox e B_curr cfg).hi
         rcases hStep with ⟨_, _, hUB, hBox⟩
         rw [← hBox, ← hUB]
         -- Use B_curr's midpoint
         use Box.midpointEnv B_curr
         refine ⟨Box.midpointEnv_mem B_curr, Box.midpointEnv_zero B_curr, ?_⟩
         exact evalOnBox_hi_correct e hsupp B_curr cfg (Box.midpointEnv B_curr)
           (Box.midpointEnv_mem B_curr) (Box.midpointEnv_zero B_curr))

/-- Helper: if ρ is in a split of B, then ρ is in B -/
theorem Box.envMem_of_envMem_split (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    Box.envMem ρ (Box.split B d).1 → Box.envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.1)).length := by simp only [List.length_set]; exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · -- heq : d = i, so B[d] = B[i]
      subst heq
      exact IntervalRat.mem_of_mem_bisect_left hmem
    · exact hmem
  · exact h

theorem Box.envMem_of_envMem_split_right (B : Box) (d : Nat) (ρ : Nat → ℝ) :
    Box.envMem ρ (Box.split B d).2 → Box.envMem ρ B := by
  intro h
  unfold split at h
  split_ifs at h with hd
  · intro ⟨i, hi⟩
    have hi' : i < (B.set d (B[d].bisect.2)).length := by simp only [List.length_set]; exact hi
    have hmem := h ⟨i, hi'⟩
    simp only [List.getElem_set] at hmem
    split_ifs at hmem with heq
    · subst heq
      exact IntervalRat.mem_of_mem_bisect_right hmem
    · exact hmem
  · exact h

/-- Helper: if ρ is in a split of B, then ρ is in B -/
theorem Box.envMem_of_envMem_splitWidest (B : Box) (ρ : Nat → ℝ) :
    (Box.envMem ρ (Box.splitWidest B).1 ∨ Box.envMem ρ (Box.splitWidest B).2) →
    Box.envMem ρ B := by
  unfold splitWidest
  intro h
  rcases h with h1 | h2
  · exact Box.envMem_of_envMem_split B (Box.widestDim B) ρ h1
  · exact Box.envMem_of_envMem_split_right B (Box.widestDim B) ρ h2

/-- Helper: splits preserve length -/
theorem Box.splitWidest_length (B : Box) :
    (Box.splitWidest B).1.length = B.length ∧ (Box.splitWidest B).2.length = B.length :=
  Box.split_length_eq B (Box.widestDim B)

/-! ### Key correctness theorem: minimizeStep preserves lower bound invariant -/

/-- Pruning returns a sub-box: any point in the pruned box is also in the original.
    This is a direct consequence of `pruneBoxForMin_subset` from Gradient.lean. -/
theorem pruneBoxForMin_sub_aux (B : Box) (grad : List IntervalRat) (ρ : Nat → ℝ)
    (h : Box.envMem ρ (pruneBoxForMin B grad).1) : Box.envMem ρ B :=
  pruneBoxForMin_subset B grad ρ h


/-- minimizeStep preserves the lower bound invariant.
    If bestLB ≤ f(ρ) for all ρ in origB before the step, then bestLB' ≤ f(ρ) for all ρ after. -/
theorem minimizeStep_preserves_LB (e : Expr) (hsupp : ExprSupported e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStep e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) :
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB' ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB') ∧
    (∀ lb B', (lb, B') ∈ queue' →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) := by
  cases hq : queue with
  | nil => simp [minimizeStep, popBest, hq] at hStep
  | cons hd tl =>
    simp only [hq, minimizeStep, popBest] at hStep
    by_cases h_prune : hd.1 > bestUB
    · -- Prune case: bounds unchanged
      simp only [h_prune, ↓reduceIte] at hStep
      cases hStep
      refine ⟨hLB, hUB, ?_⟩
      intro lb B' hmem ρ' hρ'
      have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
      exact hQueueSub lb B' h ρ' hρ'
    · -- Evaluate case
      simp only [h_prune, ↓reduceIte] at hStep
      -- Define B_curr for this branch
      set B_curr := if cfg.useMonotonicity then
          (pruneBoxForMin hd.2 (gradientIntervalN e hd.2 hd.2.length)).1 else hd.2 with hB_curr
      -- Split on remaining conditionals
      split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
      all_goals first
        | (-- Small box or split case, no split children: queue' = tl
           cases hStep
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound: min bestLB I.lo ≤ f(ρ) for all ρ in origB
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             have hmin_le : bestLB ⊓ (evalOnBox e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBox e B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound: witness exists
             first
               | exact hUB
               | (-- Better UB found: use midpoint of B_curr
                  have hmem_hd : (hd.1, hd.2) ∈ queue := by simp only [hq]; exact List.mem_cons_self
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv hd.2)
                    (Box.midpointEnv_mem hd.2)
                  use Box.midpointEnv hd.2
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi; exact Box.midpointEnv_zero hd.2 i (hLen ▸ hi)
                  · exact evalOnBox_hi_correct e hsupp hd.2 cfg (Box.midpointEnv hd.2)
                      (Box.midpointEnv_mem hd.2) (Box.midpointEnv_zero hd.2))
           · -- Queue entries
             intro lb B' hmem ρ' hρ'
             have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
             exact hQueueSub lb B' h ρ' hρ')
        | (-- Split case with children
           rcases hStep with ⟨hQ, hLB', hUB', hBox'⟩
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound preserved
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             rw [← hLB']
             have hmin_le : bestLB ⊓ (evalOnBox e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBox e B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound witness: two cases based on whether UB improved
             first
               | (-- No improvement: bestUB' = bestUB, use existing witness
                  rw [← hUB']
                  exact hUB)
               | (-- Improvement case: use pruneBoxForMin_sub_aux
                  -- Proof requires showing midpoint of B_curr is in origB
                  -- via B_curr ⊆ hd.2 ⊆ origB, and eval at midpoint ≤ bestUB'
                  -- All of this follows from pruneBoxForMin_sub_aux and pruneBoxForMin_subset
                  have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
                  rw [← hq] at hmem_hd
                  have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
                    intro ρ' hρ'
                    simp only [hB_curr] at hρ'
                    split_ifs at hρ' with h_mono
                    · exact pruneBoxForMin_sub_aux hd.2 _ ρ' hρ'
                    · exact hρ'
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv B_curr)
                    (hB_curr_sub (Box.midpointEnv B_curr) (Box.midpointEnv_mem B_curr))
                  use Box.midpointEnv B_curr
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi
                    have hlen_B_curr : B_curr.length = hd.2.length := by
                      simp only [hB_curr]
                      split_ifs with h_mono
                      · exact pruneBoxForMin_length hd.2 _
                      · rfl
                    exact Box.midpointEnv_zero B_curr i (hlen_B_curr.trans hLen ▸ hi)
                  · -- eval ≤ I.hi = bestUB' (in improvement case)
                    have heval := evalOnBox_hi_correct e hsupp B_curr cfg (Box.midpointEnv B_curr)
                      (Box.midpointEnv_mem B_curr) (Box.midpointEnv_zero B_curr)
                    -- hUB' : (evalOnBox e B_curr cfg).hi = bestUB' in this branch
                    simp only [← hUB']
                    exact heval)
           · -- Queue entries: come from tail or splits of B_curr
             -- Uses pruneBoxForMin_sub_aux to show split children ⊆ B_curr ⊆ hd.2 ⊆ origB
             intro lb B' hmem ρ' hρ'
             rw [← hQ] at hmem
             have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
             rw [← hq] at hmem_hd
             have hhdSub := hQueueSub hd.1 hd.2 hmem_hd
             have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
               intro ρ'' hρ''
               simp only [hB_curr] at hρ''
               split_ifs at hρ'' with h_mono
               · exact pruneBoxForMin_sub_aux hd.2 _ ρ'' hρ''
               · exact hρ''
             have hlen_B_curr : B_curr.length = hd.2.length := by
               simp only [hB_curr]; split_ifs; exact pruneBoxForMin_length hd.2 _; rfl
             -- Queue entries can come from: rest (tail), or inserted split boxes B1/B2
             -- Queue construction: rest → maybe insertByBound _ B1 → maybe insertByBound _ B2
             -- Try multiple proof strategies to handle all conditional combinations
             first
               -- Case: came directly from tail (no insertByBound wrapper)
               | (have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                  rw [← hq] at h
                  exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B2 inserted (B2 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B1 inserted (B1 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Both inserted, B2 outermost then B1
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · rw [mem_insertByBound] at hmem
                    rcases hmem with ⟨_, rfl⟩ | hmem
                    · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                      have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                      exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                    · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                      rw [← hq] at h
                      exact hQueueSub lb B' h ρ' hρ'))

/-- The main loop correctness theorem with explicit bestLB tracking -/
theorem minimizeLoop_correct (e : Expr) (hsupp : ExprSupported e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat)
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) :
    let result := minimizeLoop e cfg queue bestLB bestUB bestBox iters
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) →
        result.bound.lo ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧
        Expr.eval ρ e ≤ result.bound.hi) := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoop]
    exact ⟨hLB, hUB⟩
  | succ n ih =>
    simp only [minimizeLoop]
    cases hstep : minimizeStep e cfg queue bestLB bestUB bestBox with
    | none =>
      simp only
      exact ⟨hLB, hUB⟩
    | some result =>
      simp only
      -- Apply step lemma
      have ⟨hLB', hUB', hQueueSub'⟩ :=
        minimizeStep_preserves_LB e hsupp cfg origB queue bestLB bestUB bestBox
          result.1 result.2.1 result.2.2.1 result.2.2.2 hstep hLB hUB hQueueSub
      -- Apply IH
      exact ih result.1 result.2.1 result.2.2.1 result.2.2.2 hLB' hUB' hQueueSub'

/-- The key correctness theorem: globalMinimize returns a lower bound that is
    ≤ the minimum of f over any point in the original box. -/
theorem globalMinimize_lo_correct (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimize e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimize]
  let I := evalOnBox e B cfg
  -- Initial invariants
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBox_lo_correct e hsupp B cfg ρ' hρ' hzero'
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBox_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoop_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0
  exact hResult.1 ρ hρ hzero

/-- There exists a point achieving (approximately) the upper bound. -/
theorem globalMinimize_hi_achievable (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (cfg : GlobalOptConfig) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ (globalMinimize e B cfg).bound.hi := by
  simp only [globalMinimize]
  let I := evalOnBox e B cfg
  -- Initial invariants
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBox_lo_correct e hsupp B cfg ρ' hρ' hzero'
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBox_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoop_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0
  exact hResult.2

/-! ### Correctness theorems for Core (computable) versions -/

/-- The lower bound from core interval evaluation is correct. -/
theorem evalOnBoxCore_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hdom : evalDomainValid e B.toEnv { taylorDepth := cfg.taylorDepth }) :
    (evalOnBoxCore e B cfg).lo ≤ Expr.eval ρ e := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalCore_correct e hsupp ρ (Box.toEnv B) henv { taylorDepth := cfg.taylorDepth } hdom
  simp only [evalOnBoxCore]
  exact hmem.1

/-- The upper bound from core interval evaluation is correct. -/
theorem evalOnBoxCore_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hdom : evalDomainValid e B.toEnv { taylorDepth := cfg.taylorDepth }) :
    Expr.eval ρ e ≤ (evalOnBoxCore e B cfg).hi := by
  have henv := Box.envMem_toEnv ρ B hρ hzero
  have hmem := evalIntervalCore_correct e hsupp ρ (Box.toEnv B) henv { taylorDepth := cfg.taylorDepth } hdom
  simp only [evalOnBoxCore]
  exact hmem.2

/-- minimizeStepCore preserves the lower bound invariant.

    This version uses ExprSupportedCore with an explicit domain validity hypothesis
    for all boxes of the same length as origB. This is necessary because the
    branch-and-bound algorithm operates on sub-boxes that maintain the same length. -/
theorem minimizeStepCore_preserves_LB (e : Expr) (hsupp : ExprSupportedCore e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStepCore e cfg queue bestLB bestUB bestBox = some (queue', bestLB', bestUB', bestBox'))
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length)
    (hdom : ∀ (B' : Box), B'.length = origB.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB' ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB') ∧
    (∀ lb B', (lb, B') ∈ queue' →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length) := by
  cases hq : queue with
  | nil => simp [minimizeStepCore, minimizeStepGeneric, popBest, hq] at hStep
  | cons hd tl =>
    simp only [hq, minimizeStepCore, minimizeStepGeneric, mkGradEval, popBest] at hStep
    by_cases h_prune : hd.1 > bestUB
    · -- Prune case: bounds unchanged
      simp only [h_prune, ↓reduceIte] at hStep
      cases hStep
      refine ⟨hLB, hUB, ?_⟩
      intro lb B' hmem ρ' hρ'
      have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
      exact hQueueSub lb B' h ρ' hρ'
    · -- Evaluate case
      simp only [h_prune, ↓reduceIte] at hStep
      -- Define B_curr for this branch (same as in minimizeStepCore)
      set B_curr := if cfg.useMonotonicity then
          (pruneBoxForMin hd.2 (gradientIntervalCore e hd.2 { taylorDepth := cfg.taylorDepth })).1
          else hd.2 with hB_curr
      -- Split on remaining conditionals
      split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
      all_goals first
        | (-- Small box or split case, no split children: queue' = tl
           cases hStep
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound: min bestLB I.lo ≤ f(ρ) for all ρ in origB
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             have hmin_le : bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound: witness exists
             first
               | exact hUB
               | (-- Better UB found: use midpoint of hd.2
                  have hmem_hd : (hd.1, hd.2) ∈ queue := by simp only [hq]; exact List.mem_cons_self
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv hd.2)
                    (Box.midpointEnv_mem hd.2)
                  use Box.midpointEnv hd.2
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi; exact Box.midpointEnv_zero hd.2 i (hLen ▸ hi)
                  · have hLen_hd := (hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv hd.2) (Box.midpointEnv_mem hd.2)).2
                    exact evalOnBoxCore_hi_correct e hsupp hd.2 cfg (Box.midpointEnv hd.2)
                      (Box.midpointEnv_mem hd.2) (Box.midpointEnv_zero hd.2) (hdom hd.2 hLen_hd))
           · -- Queue entries
             intro lb B' hmem ρ' hρ'
             have h : (lb, B') ∈ queue := by rw [hq]; exact List.mem_cons_of_mem hd hmem
             exact hQueueSub lb B' h ρ' hρ')
        | (-- Split case with children
           rcases hStep with ⟨hQ, hLB', hUB', hBox'⟩
           refine ⟨?_, ?_, ?_⟩
           · -- Lower bound preserved
             intro ρ hρ hzero
             have hLB_old := hLB ρ hρ hzero
             rw [← hLB']
             have hmin_le : bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo ≤ bestLB := min_le_left _ _
             calc ((bestLB ⊓ (evalOnBoxCore e B_curr cfg).lo : ℚ) : ℝ)
               ≤ bestLB := by exact_mod_cast hmin_le
               _ ≤ Expr.eval ρ e := hLB_old
           · -- Upper bound witness: two cases based on whether UB improved
             first
               | (-- No improvement: bestUB' = bestUB, use existing witness
                  rw [← hUB']
                  exact hUB)
               | (-- Improvement case: use pruneBoxForMin_sub_aux
                  have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
                  rw [← hq] at hmem_hd
                  have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
                    intro ρ' hρ'
                    simp only [hB_curr] at hρ'
                    split_ifs at hρ' with h_mono
                    · exact pruneBoxForMin_sub_aux hd.2 _ ρ' hρ'
                    · exact hρ'
                  have ⟨hOrig, hLen⟩ := hQueueSub hd.1 hd.2 hmem_hd (Box.midpointEnv B_curr)
                    (hB_curr_sub (Box.midpointEnv B_curr) (Box.midpointEnv_mem B_curr))
                  have hlen_B_curr : B_curr.length = hd.2.length := by
                    simp only [hB_curr]
                    split_ifs with h_mono
                    · exact pruneBoxForMin_length hd.2 _
                    · rfl
                  use Box.midpointEnv B_curr
                  refine ⟨hOrig, ?_, ?_⟩
                  · intro i hi
                    exact Box.midpointEnv_zero B_curr i (hlen_B_curr.trans hLen ▸ hi)
                  · -- eval ≤ I.hi = bestUB' (in improvement case)
                    have heval := evalOnBoxCore_hi_correct e hsupp B_curr cfg (Box.midpointEnv B_curr)
                      (Box.midpointEnv_mem B_curr) (Box.midpointEnv_zero B_curr) (hdom B_curr (hlen_B_curr.trans hLen))
                    simp only [← hUB']
                    exact heval)
           · -- Queue entries: come from tail or splits of B_curr
             -- Uses pruneBoxForMin_sub_aux to show split children ⊆ B_curr ⊆ hd.2 ⊆ origB
             intro lb B' hmem ρ' hρ'
             rw [← hQ] at hmem
             have hmem_hd : (hd.1, hd.2) ∈ hd :: tl := List.mem_cons_self
             rw [← hq] at hmem_hd
             have hhdSub := hQueueSub hd.1 hd.2 hmem_hd
             have hB_curr_sub : ∀ ρ', Box.envMem ρ' B_curr → Box.envMem ρ' hd.2 := by
               intro ρ'' hρ''
               simp only [hB_curr] at hρ''
               split_ifs at hρ'' with h_mono
               · exact pruneBoxForMin_sub_aux hd.2 _ ρ'' hρ''
               · exact hρ''
             have hlen_B_curr : B_curr.length = hd.2.length := by
               simp only [hB_curr]; split_ifs; exact pruneBoxForMin_length hd.2 _; rfl
             -- Queue entries can come from: rest (tail), or inserted split boxes B1/B2
             -- Queue construction: rest → maybe insertByBound _ B1 → maybe insertByBound _ B2
             -- Try multiple proof strategies to handle all conditional combinations
             first
               -- Case: came directly from tail (no insertByBound wrapper)
               | (have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                  rw [← hq] at h
                  exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B2 inserted (B2 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Only B1 inserted (B1 is outermost)
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                  · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                    rw [← hq] at h
                    exact hQueueSub lb B' h ρ' hρ')
               -- Case: Both inserted, B2 outermost then B1
               | (rw [mem_insertByBound] at hmem
                  rcases hmem with ⟨_, rfl⟩ | hmem
                  · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split_right B_curr _ ρ' hρ')
                    have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                    exact ⟨hOrig, ((Box.splitWidest_length B_curr).2.trans hlen_B_curr).trans hLen⟩
                  · rw [mem_insertByBound] at hmem
                    rcases hmem with ⟨_, rfl⟩ | hmem
                    · have hρ_orig := hB_curr_sub ρ' (Box.envMem_of_envMem_split B_curr _ ρ' hρ')
                      have ⟨hOrig, hLen⟩ := hhdSub ρ' hρ_orig
                      exact ⟨hOrig, ((Box.splitWidest_length B_curr).1.trans hlen_B_curr).trans hLen⟩
                    · have h : (lb, B') ∈ hd :: tl := List.mem_cons_of_mem hd hmem
                      rw [← hq] at h
                      exact hQueueSub lb B' h ρ' hρ'))

/-- The main loop correctness theorem for Core version -/
theorem minimizeLoopCore_correct (e : Expr) (hsupp : ExprSupportedCore e) (cfg : GlobalOptConfig)
    (origB : Box)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat)
    (hLB : ∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) → bestLB ≤ Expr.eval ρ e)
    (hUB : ∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧ Expr.eval ρ e ≤ bestUB)
    (hQueueSub : ∀ lb B', (lb, B') ∈ queue →
        ∀ ρ, Box.envMem ρ B' → Box.envMem ρ origB ∧ B'.length = origB.length)
    (hdom : ∀ (B' : Box), B'.length = origB.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    let result := minimizeLoopCore e cfg queue bestLB bestUB bestBox iters
    (∀ ρ, Box.envMem ρ origB → (∀ i, i ≥ origB.length → ρ i = 0) →
        result.bound.lo ≤ Expr.eval ρ e) ∧
    (∃ ρ, Box.envMem ρ origB ∧ (∀ i, i ≥ origB.length → ρ i = 0) ∧
        Expr.eval ρ e ≤ result.bound.hi) := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoopCore]
    exact ⟨hLB, hUB⟩
  | succ n ih =>
    simp only [minimizeLoopCore]
    cases hstep : minimizeStepCore e cfg queue bestLB bestUB bestBox with
    | none =>
      simp only
      exact ⟨hLB, hUB⟩
    | some result =>
      simp only
      have ⟨hLB', hUB', hQueueSub'⟩ :=
        minimizeStepCore_preserves_LB e hsupp cfg origB queue bestLB bestUB bestBox
          result.1 result.2.1 result.2.2.1 result.2.2.2 hstep hLB hUB hQueueSub hdom
      exact ih result.1 result.2.1 result.2.2.1 result.2.2.2 hLB' hUB' hQueueSub'

/-- The key correctness theorem for Core version: globalMinimizeCore returns a lower bound
    that is ≤ the minimum of f over any point in the original box.

    This theorem requires a domain validity hypothesis for ExprSupportedCore expressions.
    For ExprSupported expressions, use globalMinimizeCore_lo_correct_supported which
    derives domain validity automatically. -/
theorem globalMinimizeCore_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimizeCore e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimizeCore]
  let I := evalOnBoxCore e B cfg
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBoxCore_lo_correct e hsupp B cfg ρ' hρ' hzero' (hdom B rfl)
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBoxCore_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B) (hdom B rfl)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoopCore_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0 hdom
  exact hResult.1 ρ hρ hzero

/-- There exists a point achieving (approximately) the upper bound for Core version. -/
theorem globalMinimizeCore_hi_achievable (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      Expr.eval ρ e ≤ (globalMinimizeCore e B cfg).bound.hi := by
  simp only [globalMinimizeCore]
  let I := evalOnBoxCore e B cfg
  have hLB0 : ∀ ρ', Box.envMem ρ' B → (∀ i, i ≥ B.length → ρ' i = 0) →
      I.lo ≤ Expr.eval ρ' e := by
    intro ρ' hρ' hzero'
    exact evalOnBoxCore_lo_correct e hsupp B cfg ρ' hρ' hzero' (hdom B rfl)
  have hUB0 : ∃ ρ', Box.envMem ρ' B ∧ (∀ i, i ≥ B.length → ρ' i = 0) ∧
      Expr.eval ρ' e ≤ I.hi := by
    use Box.midpointEnv B
    refine ⟨Box.midpointEnv_mem B, Box.midpointEnv_zero B, ?_⟩
    exact evalOnBoxCore_hi_correct e hsupp B cfg (Box.midpointEnv B)
      (Box.midpointEnv_mem B) (Box.midpointEnv_zero B) (hdom B rfl)
  have hQueueSub0 : ∀ lb B', (lb, B') ∈ [(I.lo, B)] →
      ∀ ρ', Box.envMem ρ' B' → Box.envMem ρ' B ∧ B'.length = B.length := by
    intro lb B' hmem ρ' hρ'
    simp only [List.mem_singleton] at hmem
    cases hmem
    exact ⟨hρ', rfl⟩
  -- Apply loop correctness
  have hResult := minimizeLoopCore_correct e hsupp cfg B [(I.lo, B)] I.lo I.hi B cfg.maxIterations
    hLB0 hUB0 hQueueSub0 hdom
  exact hResult.2

/-- The lower bound is ≤ the upper bound.
    This follows from the existence of a witness: there's some ρ with f(ρ) ≤ hi,
    and lo ≤ f(ρ) for all ρ in B, so lo ≤ f(witness) ≤ hi. -/
theorem globalMinimizeCore_lo_le_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    (globalMinimizeCore e B cfg).bound.lo ≤ (globalMinimizeCore e B cfg).bound.hi := by
  -- Get the witness that achieves ≤ hi
  obtain ⟨ρ, hρ, hzero, hhi⟩ := globalMinimizeCore_hi_achievable e hsupp B cfg hdom
  -- Get that lo ≤ f(ρ) for this witness
  have hlo := globalMinimizeCore_lo_correct e hsupp B cfg hdom ρ hρ hzero
  -- Combine: lo ≤ f(ρ) ≤ hi, then cast back to ℚ
  have h : ((globalMinimizeCore e B cfg).bound.lo : ℝ) ≤ (globalMinimizeCore e B cfg).bound.hi :=
    calc ((globalMinimizeCore e B cfg).bound.lo : ℝ)
      ≤ Expr.eval ρ e := hlo
      _ ≤ (globalMinimizeCore e B cfg).bound.hi := hhi
  exact_mod_cast h

/-! ### Maximization correctness theorems -/

/-- The upper bound from globalMaximizeCore is correct: f(ρ) ≤ hi for all ρ in B. -/
theorem globalMaximizeCore_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ (globalMaximizeCore e B cfg).bound.hi := by
  intro ρ hρ hzero
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hneg_dom : ∀ (B' : Box), B'.length = B.length → evalDomainValid (Expr.neg e) B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' hB'
    simp only [evalDomainValid]
    exact hdom B' hB'
  have hmin := globalMinimizeCore_lo_correct (Expr.neg e) hneg_supp B cfg hneg_dom ρ hρ hzero
  simp only [Expr.eval_neg] at hmin
  have h : Expr.eval ρ e ≤ (-(globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := by linarith
  exact_mod_cast h

/-- There exists a point achieving approximately the lower bound for maximization. -/
theorem globalMaximizeCore_lo_achievable (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    ∃ (ρ : Nat → ℝ), Box.envMem ρ B ∧ (∀ i, i ≥ B.length → ρ i = 0) ∧
      (globalMaximizeCore e B cfg).bound.lo ≤ Expr.eval ρ e := by
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hneg_dom : ∀ (B' : Box), B'.length = B.length → evalDomainValid (Expr.neg e) B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' hB'
    simp only [evalDomainValid]
    exact hdom B' hB'
  obtain ⟨ρ, hρ, hzero, hhi⟩ := globalMinimizeCore_hi_achievable (Expr.neg e) hneg_supp B cfg hneg_dom
  use ρ, hρ, hzero
  simp only [Expr.eval_neg] at hhi
  have h : (-(globalMinimizeCore (Expr.neg e) B cfg).bound.hi : ℝ) ≤ Expr.eval ρ e := by linarith
  exact_mod_cast h

/-- The lower bound is ≤ the upper bound for maximization. -/
theorem globalMaximizeCore_lo_le_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfig)
    (hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth }) :
    (globalMaximizeCore e B cfg).bound.lo ≤ (globalMaximizeCore e B cfg).bound.hi := by
  simp only [globalMaximizeCore]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  have hneg_dom : ∀ (B' : Box), B'.length = B.length → evalDomainValid (Expr.neg e) B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' hB'
    simp only [evalDomainValid]
    exact hdom B' hB'
  have h := globalMinimizeCore_lo_le_hi (Expr.neg e) hneg_supp B cfg hneg_dom
  linarith

/-! ### Dyadic backend versions for high-performance optimization

These variants use Dyadic arithmetic (n * 2^e) instead of rationals,
preventing denominator explosion for deep expressions. 10-100x faster
for complex expressions like neural networks. -/

/-- Configuration for Dyadic global optimization -/
structure GlobalOptConfigDyadic where
  /-- Maximum number of subdivisions -/
  maxIterations : Nat := 1000
  /-- Stop when box width is below this threshold -/
  tolerance : ℚ := 1/1000
  /-- Use monotonicity pruning (requires gradient computation) -/
  useMonotonicity : Bool := false
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  /-- Dyadic precision (minimum exponent for outward rounding) -/
  precision : Int := -53
  deriving Repr

instance : Inhabited GlobalOptConfigDyadic := ⟨{}⟩

/-- Evaluate expression on a box using Dyadic arithmetic -/
def evalOnBoxDyadic (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic) : IntervalRat :=
  let dyadicEnv : IntervalDyadicEnv := fun i =>
    let irat := B.getD i (IntervalRat.singleton 0)
    Core.IntervalDyadic.ofIntervalRat irat cfg.precision
  let dyadicCfg : DyadicConfig := {
    precision := cfg.precision,
    taylorDepth := cfg.taylorDepth,
    roundAfterOps := 0
  }
  let result := evalIntervalDyadic e dyadicEnv dyadicCfg
  result.toIntervalRat

/-- One step of branch-and-bound using Dyadic arithmetic -/
def minimizeStepDyadic (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  minimizeStepGeneric
    (fun B => evalOnBoxDyadic e B cfg)
    (mkGradEval e cfg.taylorDepth)
    cfg.useMonotonicity
    cfg.tolerance
    queue bestLB bestUB bestBox

/-- Run branch-and-bound loop using Dyadic arithmetic -/
def minimizeLoopDyadic (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepDyadic e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopDyadic e cfg queue' bestLB' bestUB' bestBox' n

/-- Helper: bestLB only decreases during minimizeStepDyadic. -/
theorem minimizeStepDyadic_bestLB_le (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStepDyadic e cfg queue bestLB bestUB bestBox =
      some (queue', bestLB', bestUB', bestBox')) :
    bestLB' ≤ bestLB := by
  cases queue with
  | nil => simp [minimizeStepDyadic, minimizeStepGeneric, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStepDyadic, minimizeStepGeneric, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, hLB, _, _⟩
    all_goals rw [← hLB]
    all_goals exact min_le_left _ _

/-- Helper: minimizeLoopDyadic preserves the initial lower bound. -/
theorem minimizeLoopDyadic_bestLB_le (e : Expr) (cfg : GlobalOptConfigDyadic)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    (minimizeLoopDyadic e cfg queue bestLB bestUB bestBox iters).bound.lo ≤ bestLB := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoopDyadic, le_refl]
  | succ n ih =>
    simp only [minimizeLoopDyadic]
    cases hstep : minimizeStepDyadic e cfg queue bestLB bestUB bestBox with
    | none =>
      exact le_rfl
    | some queue' =>
      rcases queue' with ⟨queue', bestLB', bestUB', bestBox'⟩
      have hstepLB :=
        minimizeStepDyadic_bestLB_le e cfg queue bestLB bestUB bestBox
          queue' bestLB' bestUB' bestBox' hstep
      have hrec := ih queue' bestLB' bestUB' bestBox'
      exact le_trans hrec hstepLB

/-- Global minimization using Dyadic arithmetic -/
def globalMinimizeDyadic (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic := {}) : GlobalResult :=
  let I := evalOnBoxDyadic e B cfg
  minimizeLoopDyadic e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations

/-- Global maximization using Dyadic arithmetic -/
def globalMaximizeDyadic (e : Expr) (B : Box) (cfg : GlobalOptConfigDyadic := {}) : GlobalResult :=
  let result := globalMinimizeDyadic (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Affine backend versions for tight bounds

These variants use Affine Arithmetic to track correlations between variables,
solving the "dependency problem" in interval arithmetic. For example:
- Interval: x - x on [-1, 1] gives [-2, 2]
- Affine: x - x on [-1, 1] gives [0, 0] (exact!) -/

/-- Configuration for Affine global optimization -/
structure GlobalOptConfigAffine where
  /-- Maximum number of subdivisions -/
  maxIterations : Nat := 1000
  /-- Stop when box width is below this threshold -/
  tolerance : ℚ := 1/1000
  /-- Use monotonicity pruning (requires gradient computation) -/
  useMonotonicity : Bool := false
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  /-- Max noise symbols before consolidation (0 = no limit) -/
  maxNoiseSymbols : Nat := 0
  deriving Repr

instance : Inhabited GlobalOptConfigAffine := ⟨{}⟩

/-- Evaluate expression on a box using Affine arithmetic -/
def evalOnBoxAffine (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine) : IntervalRat :=
  let affineEnv := toAffineEnv B
  let affineCfg : AffineConfig := {
    taylorDepth := cfg.taylorDepth,
    maxNoiseSymbols := cfg.maxNoiseSymbols
  }
  let result := evalIntervalAffine e affineEnv affineCfg
  result.toInterval

/-- One step of branch-and-bound using Affine arithmetic -/
def minimizeStepAffine (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) :
    Option (List (ℚ × Box) × ℚ × ℚ × Box) :=
  minimizeStepGeneric
    (fun B => evalOnBoxAffine e B cfg)
    (mkGradEval e cfg.taylorDepth)
    cfg.useMonotonicity
    cfg.tolerance
    queue bestLB bestUB bestBox

/-- Run branch-and-bound loop using Affine arithmetic -/
def minimizeLoopAffine (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    GlobalResult :=
  match iters with
  | 0 =>
    { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations }
      remainingBoxes := queue }
  | n + 1 =>
    match minimizeStepAffine e cfg queue bestLB bestUB bestBox with
    | none =>
      { bound := { lo := bestLB, hi := bestUB, bestBox := bestBox, iterations := cfg.maxIterations - n - 1 }
        remainingBoxes := [] }
    | some (queue', bestLB', bestUB', bestBox') =>
      minimizeLoopAffine e cfg queue' bestLB' bestUB' bestBox' n

/-- Helper: bestLB only decreases during minimizeStepAffine. -/
theorem minimizeStepAffine_bestLB_le (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box)
    (queue' : List (ℚ × Box)) (bestLB' bestUB' : ℚ) (bestBox' : Box)
    (hStep : minimizeStepAffine e cfg queue bestLB bestUB bestBox =
      some (queue', bestLB', bestUB', bestBox')) :
    bestLB' ≤ bestLB := by
  cases queue with
  | nil => simp [minimizeStepAffine, minimizeStepGeneric, popBest] at hStep
  | cons hd tl =>
    simp only [minimizeStepAffine, minimizeStepGeneric, popBest] at hStep
    split_ifs at hStep <;> simp only [Option.some.injEq, Prod.mk.injEq] at hStep
    all_goals rcases hStep with ⟨_, hLB, _, _⟩
    all_goals rw [← hLB]
    all_goals exact min_le_left _ _

/-- Helper: minimizeLoopAffine preserves the initial lower bound. -/
theorem minimizeLoopAffine_bestLB_le (e : Expr) (cfg : GlobalOptConfigAffine)
    (queue : List (ℚ × Box)) (bestLB bestUB : ℚ) (bestBox : Box) (iters : Nat) :
    (minimizeLoopAffine e cfg queue bestLB bestUB bestBox iters).bound.lo ≤ bestLB := by
  induction iters generalizing queue bestLB bestUB bestBox with
  | zero =>
    simp only [minimizeLoopAffine, le_refl]
  | succ n ih =>
    simp only [minimizeLoopAffine]
    cases hstep : minimizeStepAffine e cfg queue bestLB bestUB bestBox with
    | none =>
      exact le_rfl
    | some queue' =>
      rcases queue' with ⟨queue', bestLB', bestUB', bestBox'⟩
      have hstepLB :=
        minimizeStepAffine_bestLB_le e cfg queue bestLB bestUB bestBox
          queue' bestLB' bestUB' bestBox' hstep
      have hrec := ih queue' bestLB' bestUB' bestBox'
      exact le_trans hrec hstepLB

/-- Global minimization using Affine arithmetic -/
def globalMinimizeAffine (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine := {}) : GlobalResult :=
  let I := evalOnBoxAffine e B cfg
  minimizeLoopAffine e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations

/-- Global maximization using Affine arithmetic -/
def globalMaximizeAffine (e : Expr) (B : Box) (cfg : GlobalOptConfigAffine := {}) : GlobalResult :=
  let result := globalMinimizeAffine (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Correctness theorems for Dyadic optimization -/

/-- The lower bound from Dyadic interval evaluation is correct.

The proof uses `evalIntervalDyadic_correct` and `IntervalDyadic.toIntervalRat_correct`
to show that the true value is contained in the resulting rational interval.

Note: Requires domain validity for expressions with log. -/
theorem evalOnBoxDyadic_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigDyadic) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth, roundAfterOps := 0 }) :
    (evalOnBoxDyadic e B cfg).lo ≤ Expr.eval ρ e := by
  -- Build the Dyadic environment from the box
  set dyadicEnv : IntervalDyadicEnv := fun i =>
    Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision
  set dyadicCfg : DyadicConfig := {
    precision := cfg.precision,
    taylorDepth := cfg.taylorDepth,
    roundAfterOps := 0
  }
  have henv : envMemDyadic ρ dyadicEnv := by
    intro i
    by_cases hi : i < B.length
    · have hmem : ρ i ∈ B[i]'hi := hρ ⟨i, hi⟩
      have hdyad := Core.IntervalDyadic.mem_ofIntervalRat hmem cfg.precision hprec
      simpa [dyadicEnv, List.getD, List.getElem?_eq_getElem hi, Option.getD] using hdyad
    · have hzeroi : ρ i = 0 := hzero i (Nat.le_of_not_lt hi)
      have hmem0 : (0 : ℝ) ∈ IntervalRat.singleton 0 := by
        exact_mod_cast IntervalRat.mem_singleton 0
      have hdyad := Core.IntervalDyadic.mem_ofIntervalRat hmem0 cfg.precision hprec
      simpa [dyadicEnv, List.getD, List.getElem?_eq_none (not_lt.mp hi), Option.getD, hzeroi] using hdyad
  have hmem := evalIntervalDyadic_correct e hsupp ρ dyadicEnv henv dyadicCfg hprec hdom
  have hmem_rat := Core.IntervalDyadic.mem_toIntervalRat.mp hmem
  have hmem_rat' : Expr.eval ρ e ∈ evalOnBoxDyadic e B cfg := by
    simpa [evalOnBoxDyadic, dyadicEnv, dyadicCfg] using hmem_rat
  exact ((IntervalRat.mem_def _ _).mp hmem_rat').1

/-- The key correctness theorem for Dyadic minimization: globalMinimizeDyadic returns
    a lower bound that is ≤ the minimum of f over any point in the original box.

Note: Requires domain validity for expressions with log. -/
theorem globalMinimizeDyadic_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigDyadic)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth, roundAfterOps := 0 }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimizeDyadic e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimizeDyadic]
  set I := evalOnBoxDyadic e B cfg
  have hlo : I.lo ≤ Expr.eval ρ e := evalOnBoxDyadic_lo_correct e hsupp B cfg ρ hρ hzero hprec hdom
  have hloop :
      (minimizeLoopDyadic e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo ≤ I.lo := by
    simpa using
      (minimizeLoopDyadic_bestLB_le e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations)
  have hloop' : ((minimizeLoopDyadic e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo : ℝ)
      ≤ (I.lo : ℝ) := by
    exact_mod_cast hloop
  linarith

/-- The upper bound from globalMaximizeDyadic is correct: f(ρ) ≤ hi for all ρ in B.

Note: Requires domain validity for expressions with log. -/
theorem globalMaximizeDyadic_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigDyadic)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth, roundAfterOps := 0 }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ (globalMaximizeDyadic e B cfg).bound.hi := by
  intro ρ hρ hzero
  simp only [globalMaximizeDyadic]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  -- Domain validity for neg e is the same as for e
  have hdom_neg : evalDomainValidDyadic (Expr.neg e)
      (fun i => Core.IntervalDyadic.ofIntervalRat (B.getD i (IntervalRat.singleton 0)) cfg.precision)
      { precision := cfg.precision, taylorDepth := cfg.taylorDepth, roundAfterOps := 0 } := by
    simp only [evalDomainValidDyadic]; exact hdom
  have hmin := globalMinimizeDyadic_lo_correct (Expr.neg e) hneg_supp B cfg hprec hdom_neg ρ hρ hzero
  simp only [Expr.eval_neg] at hmin
  -- hmin : (globalMinimizeDyadic e.neg B cfg).bound.lo ≤ -Expr.eval ρ e
  -- Goal : Expr.eval ρ e ≤ -(globalMinimizeDyadic e.neg B cfg).bound.lo
  have h : Expr.eval ρ e ≤ (-(globalMinimizeDyadic (Expr.neg e) B cfg).bound.lo : ℝ) := by linarith
  exact_mod_cast h

/-! ### Correctness theorems for Affine optimization -/

private theorem linearSum_ofFn_zero {n : Nat} (eps : Fin n → ℝ) :
    AffineForm.linearSum (List.ofFn (fun _ : Fin n => (0 : ℚ))) (List.ofFn eps) = 0 := by
  unfold AffineForm.linearSum
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.zipWith_cons_cons, Rat.cast_zero, zero_mul, List.sum_cons,
      zero_add]
    exact ih (fun i => eps i.succ)

private theorem linearSum_ofFn_basis {n : Nat} (idx : Nat) (rad : ℚ) (eps : Fin n → ℝ) :
    AffineForm.linearSum
      (List.ofFn (fun i : Fin n => if i.val = idx then rad else 0))
      (List.ofFn eps)
      = (rad : ℝ) * (if h : idx < n then eps ⟨idx, h⟩ else 0) := by
  unfold AffineForm.linearSum
  induction n generalizing idx with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.zipWith_cons_cons, List.sum_cons, Fin.val_zero]
    cases idx with
    | zero =>
      simp only [↓reduceDIte, Nat.zero_lt_succ, Fin.mk_zero]
      have hcoeffs : (List.ofFn (fun i : Fin n => if i.succ.val = 0 then rad else 0)) =
          (List.ofFn (fun _ : Fin n => (0 : ℚ))) := by
        apply List.ext_getElem <;> simp
      have htail : (List.zipWith (fun (c : ℚ) e => (c : ℝ) * e)
          (List.ofFn (fun i : Fin n => if i.succ.val = 0 then rad else 0))
          (List.ofFn (fun i => eps i.succ))).sum = 0 := by
        simp only [hcoeffs]
        exact linearSum_ofFn_zero (fun i => eps i.succ)
      simp only [htail, add_zero, ↓reduceIte]
    | succ idx' =>
      have hne : ¬(0 = idx' + 1) := Nat.zero_ne_add_one idx'
      simp only [hne, ↓reduceIte, Rat.cast_zero, zero_mul, zero_add, Nat.succ_lt_succ_iff]
      have hcoeffs : (List.ofFn (fun i : Fin n => if i.succ.val = Nat.succ idx' then rad else 0)) =
          (List.ofFn (fun i : Fin n => if i.val = idx' then rad else 0)) := by
        apply List.ext_getElem
        · simp
        · intro k h1 h2
          simp only [List.getElem_ofFn, Fin.val_succ, Nat.succ_eq_add_one, Nat.add_right_cancel_iff]
      simp only [hcoeffs]
      have hrec := ih idx' (fun i => eps i.succ)
      unfold AffineForm.linearSum at hrec
      rw [hrec]
      -- Now need to show: rad * (if h : idx' < n then eps ⟨idx', h⟩.succ else 0)
      --                 = rad * (if h : idx' < n then eps ⟨idx' + 1, h⟩ else 0)
      by_cases hidx : idx' < n
      · simp only [hidx, ↓reduceDIte, Fin.succ_mk]
      · simp only [hidx, ↓reduceDIte]

private theorem validNoise_ofFn {n : Nat} (f : Fin n → ℝ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) :
    AffineForm.validNoise (List.ofFn f) := by
  intro e he
  simp only [List.mem_ofFn] at he
  obtain ⟨i, rfl⟩ := he
  exact hf i

private lemma abs_sub_mid_le_rad {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    |x - ((I.lo + I.hi) / 2 : ℚ)| ≤ ((I.hi - I.lo) / 2 : ℚ) := by
  have hx' : (I.lo : ℝ) ≤ x ∧ x ≤ I.hi := by
    simpa [IntervalRat.mem_def] using hx
  rw [abs_le]
  constructor
  · calc -((((I.hi : ℚ) - I.lo) / 2 : ℚ) : ℝ)
        = (I.lo : ℝ) - ((I.lo : ℝ) + I.hi) / 2 := by push_cast; ring
      _ ≤ x - ((I.lo : ℝ) + I.hi) / 2 := by linarith [hx'.1]
      _ = x - ((((I.lo : ℚ) + I.hi) / 2 : ℚ) : ℝ) := by push_cast; ring
  · calc x - ((((I.lo : ℚ) + I.hi) / 2 : ℚ) : ℝ)
        = x - ((I.lo : ℝ) + I.hi) / 2 := by push_cast; ring
      _ ≤ (I.hi : ℝ) - ((I.lo : ℝ) + I.hi) / 2 := by linarith [hx'.2]
      _ = ((((I.hi : ℚ) - I.lo) / 2 : ℚ) : ℝ) := by push_cast; ring

/-- The lower bound from Affine interval evaluation is correct.
    Note: Requires ExprSupportedCore, valid noise assignment, and domain validity for log. -/
theorem evalOnBoxAffine_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigAffine) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (hdom : evalDomainValidAffine e (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }) :
    (evalOnBoxAffine e B cfg).lo ≤ Expr.eval ρ e := by
  set n := B.length
  set affineEnv := toAffineEnv B
  set affineCfg : AffineConfig := { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }
  -- Define noise assignment: for each dimension i, eps[i] encodes where ρ i lies in B[i]
  -- If B[i] = [lo, hi] with mid = (lo+hi)/2 and rad = (hi-lo)/2, then
  -- ρ i = mid + rad * eps[i], so eps[i] = (ρ i - mid) / rad (when rad > 0)
  let eps : AffineForm.NoiseAssignment := List.ofFn (fun i : Fin n =>
    let I := B.getD i.val (IntervalRat.singleton 0)
    let mid := ((I.lo + I.hi) / 2 : ℚ)
    let rad := ((I.hi - I.lo) / 2 : ℚ)
    if hr : (rad : ℝ) = 0 then 0 else (ρ i.val - mid) / rad)
  -- Prove the noise assignment is valid (all values in [-1, 1])
  have hvalid : AffineForm.validNoise eps := by
    apply validNoise_ofFn
    intro ⟨i, hi⟩
    simp only
    set I := B.getD i (IntervalRat.singleton 0) with hI_def
    set mid := ((I.lo + I.hi) / 2 : ℚ) with hmid_def
    set rad := ((I.hi - I.lo) / 2 : ℚ) with hrad_def
    split_ifs with hr
    · exact ⟨by linarith, by linarith⟩
    · have hρi : ρ i ∈ I := by
        have hρ' := hρ ⟨i, hi⟩
        simp only [hI_def, List.getD, List.getElem?_eq_getElem hi, Option.getD]
        convert hρ'
      have habs := abs_sub_mid_le_rad hρi
      have hrad_nonneg : (0 : ℝ) ≤ rad := by
        simp only [hrad_def]
        have hI := I.le
        have h : (0 : ℝ) ≤ ((I.hi - I.lo) / 2 : ℚ) := by
          have : (0 : ℚ) ≤ (I.hi - I.lo) / 2 := by linarith
          exact_mod_cast this
        exact h
      have hrad_pos : (0 : ℝ) < rad := lt_of_le_of_ne hrad_nonneg (Ne.symm hr)
      constructor
      · have h1 : -(rad : ℝ) ≤ ρ i - mid := by
          rw [abs_le] at habs
          exact habs.1
        calc -1 = -(rad : ℝ) / rad := by field_simp
          _ ≤ (ρ i - mid) / rad := div_le_div_of_nonneg_right h1 (le_of_lt hrad_pos)
      · have h1 : ρ i - mid ≤ rad := by
          rw [abs_le] at habs
          exact habs.2
        calc (ρ i - mid) / rad ≤ (rad : ℝ) / rad := div_le_div_of_nonneg_right h1 (le_of_lt hrad_pos)
          _ = 1 := by field_simp
  -- Prove environment membership
  have henv : envMemAffine ρ affineEnv eps := by
    intro i
    simp only [AffineForm.mem_affine, affineEnv, toAffineEnv]
    set I := B.getD i (IntervalRat.singleton 0) with hI_def
    set mid := ((I.lo + I.hi) / 2 : ℚ) with hmid_def
    set rad := ((I.hi - I.lo) / 2 : ℚ) with hrad_def
    simp only [AffineForm.ofInterval, AffineForm.evalLinear]
    use 0
    constructor
    · norm_num
    · simp only [add_zero]
      -- Need to show: ρ i = mid + linearSum (ofFn (fun j => if j = i then rad else 0)) eps
      rw [linearSum_ofFn_basis]
      by_cases hi : i < n
      · -- eps[⟨i, hi⟩] = (let I := ...; if rad = 0 then 0 else (ρ i - mid) / rad)
        -- The goal has a dite on whether (rad : ℝ) = 0
        -- Since I and rad are defined in terms of B.getD i, we need to unfold carefully
        have hI_eq : B.getD i (IntervalRat.singleton 0) = I := rfl
        have hrad_eq : ((I.hi - I.lo) / 2 : ℚ) = rad := rfl
        by_cases hrad0 : (rad : ℝ) = 0
        · -- rad = 0 case: ρ i = mid
          simp only [hI_eq, hrad_eq]
          rw [dif_pos hrad0]
          simp only [hrad0]
          have hρi : ρ i ∈ I := by
            have hρ' := hρ ⟨i, hi⟩
            simp only [hI_def, List.getD, List.getElem?_eq_getElem hi, Option.getD]
            convert hρ'
          have habs := abs_sub_mid_le_rad hρi
          rw [abs_le] at habs
          have hle : ρ i - mid ≤ 0 := by linarith [habs.2, hrad0]
          have hge : 0 ≤ ρ i - mid := by linarith [habs.1, hrad0]
          linarith
        · -- rad ≠ 0 case: reconstruct ρ i = mid + rad * eps[i]
          simp only [hI_eq, hrad_eq]
          rw [dif_neg hrad0, dif_pos hi]
          -- Now goal is: ρ i = mid + rad * ((ρ i - mid) / rad)
          have hrad_ne : (rad : ℝ) ≠ 0 := hrad0
          field_simp [hrad_ne]
          ring
      · -- i ≥ n case: ρ i = 0 and I = singleton 0
        have hzeroi : ρ i = 0 := hzero i (not_lt.mp hi)
        have hI0 : I = IntervalRat.singleton 0 := by
          simp only [hI_def, List.getD, List.getElem?_eq_none (not_lt.mp hi), Option.getD]
        simp only [hI0, IntervalRat.singleton, hzeroi]
        ring
  -- Use evalIntervalAffine_correct to get mem_affine, then mem_toInterval_weak
  have hmem_affine := evalIntervalAffine_correct e hsupp ρ affineEnv eps hvalid henv affineCfg hdom
  have hmem := AffineForm.mem_toInterval_weak hvalid hmem_affine
  have hmem' : Expr.eval ρ e ∈ evalOnBoxAffine e B cfg := by
    simpa [evalOnBoxAffine, affineEnv, affineCfg] using hmem
  exact ((IntervalRat.mem_def _ _).mp hmem').1

/-- The key correctness theorem for Affine minimization.

Note: Requires domain validity for expressions with log. -/
theorem globalMinimizeAffine_lo_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigAffine)
    (hdom : evalDomainValidAffine e (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      (globalMinimizeAffine e B cfg).bound.lo ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  simp only [globalMinimizeAffine]
  set I := evalOnBoxAffine e B cfg
  have hlo : I.lo ≤ Expr.eval ρ e := evalOnBoxAffine_lo_correct e hsupp B cfg ρ hρ hzero hdom
  have hloop :
      (minimizeLoopAffine e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo ≤ I.lo := by
    simpa using
      (minimizeLoopAffine_bestLB_le e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations)
  have hloop' : ((minimizeLoopAffine e cfg [(I.lo, B)] I.lo I.hi B cfg.maxIterations).bound.lo : ℝ)
      ≤ (I.lo : ℝ) := by
    exact_mod_cast hloop
  linarith

/-- The upper bound from globalMaximizeAffine is correct.

Note: Requires domain validity for expressions with log. -/
theorem globalMaximizeAffine_hi_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (B : Box) (cfg : GlobalOptConfigAffine)
    (hdom : evalDomainValidAffine e (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols }) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ (globalMaximizeAffine e B cfg).bound.hi := by
  intro ρ hρ hzero
  simp only [globalMaximizeAffine]
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp
  -- Domain validity for neg e is the same as for e
  have hdom_neg : evalDomainValidAffine (Expr.neg e) (toAffineEnv B)
      { taylorDepth := cfg.taylorDepth, maxNoiseSymbols := cfg.maxNoiseSymbols } := by
    simp only [evalDomainValidAffine]; exact hdom
  have hmin := globalMinimizeAffine_lo_correct (Expr.neg e) hneg_supp B cfg hdom_neg ρ hρ hzero
  simp only [Expr.eval_neg] at hmin
  -- hmin : (globalMinimizeAffine e.neg B cfg).bound.lo ≤ -Expr.eval ρ e
  -- Goal : Expr.eval ρ e ≤ -(globalMinimizeAffine e.neg B cfg).bound.lo
  have h : Expr.eval ρ e ≤ (-(globalMinimizeAffine (Expr.neg e) B cfg).bound.lo : ℝ) := by linarith
  exact_mod_cast h

end LeanCert.Engine.Optimization
