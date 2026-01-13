/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.Optimization.Global
import LeanBound.Numerics.Search.Heuristic

/-!
# Float-Guided Global Optimization

This file provides "oracle-guided" global optimization that uses fast floating-point
heuristics to initialize the rigorous branch-and-bound algorithm with tight bounds.

## Algorithm Overview

The key insight: finding a good upper bound early allows aggressive pruning.

1. **Heuristic Phase**: Use Monte Carlo sampling with hardware floats to find
   a candidate point x_guess that likely minimizes f.

2. **Certification Phase**: Convert x_guess to a tiny rational interval and
   rigorously evaluate f(x_guess) using interval arithmetic to get a certified
   upper bound U.

3. **Pruning Phase**: Initialize branch-and-bound with upper bound U. Any box B
   with lower bound L > U is immediately pruned.

## Performance Impact

For typical optimization problems, this approach can prune 90%+ of the search
space on the first iteration, dramatically reducing total computation.

## Main definitions

* `certifyCandidate` - Convert a float candidate to a certified upper bound
* `globalMinimizeGuided` - Guided minimization using float heuristics
* `globalMaximizeGuided` - Guided maximization using float heuristics

## Design notes

The float results are NEVER trusted directly. They only guide where to look.
All bounds returned are rigorously computed using interval arithmetic.
-/

namespace LeanBound.Numerics.Optimization

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Search

/-! ### Configuration for guided optimization -/

/-- Extended configuration for guided optimization -/
structure GuidedOptConfig extends GlobalOptConfig where
  /-- Number of Monte Carlo samples for heuristic search -/
  heuristicSamples : Nat := 200
  /-- Random seed for reproducibility -/
  seed : Nat := 12345
  /-- Use grid search in addition to Monte Carlo (good for low dimensions) -/
  useGridSearch : Bool := true
  /-- Grid points per dimension (only if useGridSearch = true and dim ≤ 3) -/
  gridPointsPerDim : Nat := 10
  deriving Repr

instance : Inhabited GuidedOptConfig := ⟨{}⟩

/-! ### Float to Rational conversion -/

/-- Convert an integer to a Float -/
private def intToFloat' (z : ℤ) : Float :=
  if z ≥ 0 then z.toNat.toFloat
  else -((-z).toNat.toFloat)

/-- Convert a Float to a rational approximation.
    Returns a rational that is close to the float value.
    Note: This is approximate; the certified interval evaluation handles precision. -/
def floatToRat (f : Float) : ℚ :=
  -- Handle special cases
  if f.isNaN || f.isInf then 0
  else
    -- Scale to integer, round, then convert
    -- Use 10^6 as denominator for reasonable precision
    let scaled := f * 1000000.0
    let rounded := scaled.round.toInt64.toInt
    (rounded : ℚ) / 1000000

/-- Helper: small positive width for interval creation -/
private def smallWidth : ℚ := 1/1000000

private theorem smallWidth_pos : 0 < smallWidth := by native_decide

/-- Convert a float environment to a rational point interval environment.
    Each float coordinate becomes a small interval around the rational approximation.
    Uses a fixed width of 1/1000000 for simplicity. -/
def floatEnvToRatEnv (pt : Nat → Float) (dim : Nat) : IntervalEnv :=
  fun i =>
    if i < dim then
      let r := floatToRat (pt i)
      -- Create a tiny interval around the point
      { lo := r - smallWidth, hi := r + smallWidth, le := by linarith [smallWidth_pos] }
    else
      -- Outside dimension: use point interval at 0
      IntervalRat.singleton 0

/-- Convert a float environment to interval environment within box bounds.
    Clamps coordinates to stay within the box. -/
def floatEnvToRatEnvClamped (pt : Nat → Float) (B : Box) (width : ℚ := 1/1000000) : IntervalEnv :=
  fun i =>
    if h : i < B.length then
      let r := floatToRat (pt i)
      let I := B[i]
      -- Clamp to box bounds
      let lo := max I.lo (r - width)
      let hi := min I.hi (r + width)
      if hle : lo ≤ hi then
        { lo := lo, hi := hi, le := hle }
      else
        -- Fallback if clamping fails: use box midpoint
        let mid := I.midpoint
        IntervalRat.singleton mid
    else
      IntervalRat.singleton 0

/-! ### Candidate certification -/

/-- Certify a float candidate by evaluating it rigorously.
    Returns an interval containing the true function value at (or near) the candidate. -/
def certifyCandidate (e : Expr) (B : Box) (pt : Nat → Float) (cfg : GlobalOptConfig) : IntervalRat :=
  let env := floatEnvToRatEnvClamped pt B
  evalIntervalCore e env { taylorDepth := cfg.taylorDepth }

/-- Certify with division support. -/
def certifyCandidateDiv (e : Expr) (B : Box) (pt : Nat → Float) (cfg : GlobalOptConfig) : IntervalRat :=
  let env := floatEnvToRatEnvClamped pt B
  evalIntervalCoreWithDiv e env { taylorDepth := cfg.taylorDepth }

/-! ### Guided optimization -/

/--
Global minimization with Float guidance.

Algorithm:
1. Evaluate the whole box to get initial bounds
2. Use Monte Carlo (and optionally grid search) to find a good candidate
3. Certify the candidate to get a rigorous upper bound
4. Initialize branch-and-bound with this upper bound for early pruning
-/
def globalMinimizeGuided (e : Expr) (B : Box) (cfg : GuidedOptConfig := {}) : GlobalResult :=
  -- Step 1: Initial rigorous bound on the whole box
  let I_root := evalOnBoxCore e B cfg.toGlobalOptConfig

  -- Step 2: Heuristic Search (The Oracle)
  let (mcBest, mcVal) := findBestCandidate e B (samples := cfg.heuristicSamples) (seed := cfg.seed)

  -- Optionally do grid search for low dimensions
  let (heuristicBest, _heuristicVal) :=
    if cfg.useGridSearch && B.length ≤ 3 then
      let (gridBest, gridVal) := gridSearch e B (pointsPerDim := cfg.gridPointsPerDim)
      if gridVal < mcVal then (gridBest, gridVal) else (mcBest, mcVal)
    else
      (mcBest, mcVal)

  -- Step 3: Certify the heuristic guess
  let certifiedInterval := certifyCandidate e B heuristicBest cfg.toGlobalOptConfig

  -- Step 4: Compute initial bounds
  -- Lower bound: from whole box evaluation
  let initialBestLB := I_root.lo
  -- Upper bound: min of whole box and certified guess
  let initialBestUB := min I_root.hi certifiedInterval.hi
  let initialBestBox := B

  -- Step 5: Initialize queue and run standard branch-and-bound
  let initialQueue : List (ℚ × Box) := [(I_root.lo, B)]

  minimizeLoopCore e cfg.toGlobalOptConfig initialQueue initialBestLB initialBestUB initialBestBox cfg.maxIterations

/--
Global minimization with Float guidance and division support.
-/
def globalMinimizeGuidedDiv (e : Expr) (B : Box) (cfg : GuidedOptConfig := {}) : GlobalResult :=
  let I_root := evalOnBoxCoreDiv e B cfg.toGlobalOptConfig

  let (mcBest, mcVal) := findBestCandidate e B (samples := cfg.heuristicSamples) (seed := cfg.seed)

  let (heuristicBest, _) :=
    if cfg.useGridSearch && B.length ≤ 3 then
      let (gridBest, gridVal) := gridSearch e B (pointsPerDim := cfg.gridPointsPerDim)
      if gridVal < mcVal then (gridBest, gridVal) else (mcBest, mcVal)
    else
      (mcBest, mcVal)

  let certifiedInterval := certifyCandidateDiv e B heuristicBest cfg.toGlobalOptConfig

  let initialBestLB := I_root.lo
  let initialBestUB := min I_root.hi certifiedInterval.hi
  let initialBestBox := B
  let initialQueue : List (ℚ × Box) := [(I_root.lo, B)]

  minimizeLoopCoreDiv e cfg.toGlobalOptConfig initialQueue initialBestLB initialBestUB initialBestBox cfg.maxIterations

/--
Global maximization with Float guidance.
-/
def globalMaximizeGuided (e : Expr) (B : Box) (cfg : GuidedOptConfig := {}) : GlobalResult :=
  let result := globalMinimizeGuided (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/--
Global maximization with Float guidance and division support.
-/
def globalMaximizeGuidedDiv (e : Expr) (B : Box) (cfg : GuidedOptConfig := {}) : GlobalResult :=
  let result := globalMinimizeGuidedDiv (Expr.neg e) B cfg
  { bound := { lo := -result.bound.hi
               hi := -result.bound.lo
               bestBox := result.bound.bestBox
               iterations := result.bound.iterations }
    remainingBoxes := result.remainingBoxes.map fun (lb, box) => (-lb, box) }

/-! ### Convenience API -/

/-- Quick guided minimization with sensible defaults -/
def minimize (e : Expr) (B : Box) (maxIters : Nat := 1000) (tolerance : ℚ := 1/1000) : GlobalResult :=
  globalMinimizeGuided e B { maxIterations := maxIters, tolerance := tolerance }

/-- Quick guided maximization with sensible defaults -/
def maximize (e : Expr) (B : Box) (maxIters : Nat := 1000) (tolerance : ℚ := 1/1000) : GlobalResult :=
  globalMaximizeGuided e B { maxIterations := maxIters, tolerance := tolerance }

/-! ### Result inspection -/

/-- Get the certified minimum interval from a result.
    Note: Returns `none` if `lo > hi` (should not happen for valid results). -/
def GlobalResult.minInterval (r : GlobalResult) : Option IntervalRat :=
  if hle : r.bound.lo ≤ r.bound.hi then
    some { lo := r.bound.lo, hi := r.bound.hi, le := hle }
  else
    none

/-- Check if the optimization has converged (gap is small) -/
def GlobalResult.hasConverged (r : GlobalResult) (tol : ℚ := 1/1000) : Bool :=
  r.bound.hi - r.bound.lo ≤ tol

/-- Get the optimality gap -/
def GlobalResult.gap (r : GlobalResult) : ℚ :=
  r.bound.hi - r.bound.lo

end LeanBound.Numerics.Optimization
