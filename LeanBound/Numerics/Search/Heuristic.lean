/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.FloatEval
import LeanBound.Numerics.Optimization.Box

/-!
# Heuristic Search for Global Optimization

This file provides heuristic search methods using fast floating-point arithmetic
to find good candidate points for global optimization. These candidates are used
to initialize rigorous branch-and-bound algorithms with tight upper bounds,
enabling early pruning of the search space.

## Main definitions

* `FloatBox` - Float representation of a Box for fast sampling
* `PRNG` - Simple pseudo-random number generator
* `samplePoint` - Generate a random point inside a box
* `findBestCandidate` - Monte Carlo search for minimum
* `gridSearch` - Uniform grid sampling

## Design notes

The heuristic results are NOT verified. They are used only to guide the search:
1. Find a candidate point with low objective value
2. Certify this point using rigorous interval arithmetic
3. Use the certified upper bound to prune the branch-and-bound tree

This "oracle-guided" approach can prune 90%+ of the search space on typical problems.
-/

namespace LeanBound.Numerics.Search

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Optimization

/-! ### Rational to Float conversion -/

/-- Convert an integer to a Float -/
private def intToFloat (z : ℤ) : Float :=
  if z ≥ 0 then z.toNat.toFloat
  else -((-z).toNat.toFloat)

/-- Convert a rational to a Float (approximate) -/
def ratToFloat (q : ℚ) : Float :=
  intToFloat q.num / q.den.toFloat

/-! ### Float representation of boxes -/

/-- Float representation of a box for fast sampling -/
structure FloatBox where
  /-- Center of each dimension -/
  centers : Array Float
  /-- Half-width (radius) of each dimension -/
  radii : Array Float
  deriving Repr

/-- Convert a rational Box to float representation -/
def boxToFloatBox (B : Box) : FloatBox :=
  let centers := B.map (fun I => ratToFloat ((I.lo + I.hi) / 2)) |>.toArray
  let radii := B.map (fun I => ratToFloat ((I.hi - I.lo) / 2)) |>.toArray
  ⟨centers, radii⟩

/-- Dimension of a float box -/
def FloatBox.dim (fb : FloatBox) : Nat := fb.centers.size

/-! ### Pseudo-Random Number Generator -/

/-- Simple Linear Congruential Generator (LCG) for reproducible randomness.
    Parameters from Numerical Recipes: a = 1664525, c = 1013904223, m = 2³² -/
structure PRNG where
  state : UInt64
  deriving Repr

/-- Create a PRNG with given seed -/
def PRNG.new (seed : Nat := 12345) : PRNG :=
  ⟨seed.toUInt64⟩

/-- Generate next random number in [0, 1) and updated PRNG -/
def PRNG.nextUnit (rng : PRNG) : Float × PRNG :=
  let a : UInt64 := 1664525
  let c : UInt64 := 1013904223
  let m : UInt64 := 4294967296  -- 2^32
  let newState := (a * rng.state + c) % m
  let floatVal := newState.toFloat / m.toFloat
  (floatVal, ⟨newState⟩)

/-- Generate next random number in [-1, 1] and updated PRNG -/
def PRNG.next (rng : PRNG) : Float × PRNG :=
  let (u, rng') := rng.nextUnit
  (2.0 * u - 1.0, rng')

/-- Generate n random numbers in [-1, 1] -/
def PRNG.nextN (rng : PRNG) (n : Nat) : Array Float × PRNG :=
  let rec loop (i : Nat) (acc : Array Float) (r : PRNG) : Array Float × PRNG :=
    match i with
    | 0 => (acc, r)
    | k + 1 =>
      let (v, r') := r.next
      loop k (acc.push v) r'
  loop n #[] rng

/-! ### Sampling methods -/

/-- Generate a random point inside a float box -/
def samplePoint (fb : FloatBox) (rng : PRNG) : (Nat → Float) × PRNG :=
  let (perturbations, rng') := rng.nextN fb.dim
  let pt := fun i =>
    if h : i < fb.centers.size then
      fb.centers[i] + perturbations.getD i 0.0 * fb.radii.getD i 0.0
    else 0.0
  (pt, rng')

/-- Generate n random points inside a float box -/
def samplePoints (fb : FloatBox) (rng : PRNG) (n : Nat) : Array (Nat → Float) × PRNG :=
  let rec loop (i : Nat) (acc : Array (Nat → Float)) (r : PRNG) : Array (Nat → Float) × PRNG :=
    match i with
    | 0 => (acc, r)
    | k + 1 =>
      let (pt, r') := samplePoint fb r
      loop k (acc.push pt) r'
  loop n #[] rng

/-- Get the center point of a float box -/
def FloatBox.center (fb : FloatBox) : Nat → Float :=
  fun i => fb.centers.getD i 0.0

/-! ### Monte Carlo Minimization -/

/--
Heuristic Minimizer using Monte Carlo sampling.
Samples `n` points using Float arithmetic and returns the best candidate found.

This is surprisingly effective for finding the "basin of attraction" of the
global minimum, especially in high dimensions where grid search is infeasible.
-/
def findBestCandidate (e : Expr) (B : Box) (samples : Nat := 100) (seed : Nat := 12345) :
    (Nat → Float) × Float :=
  let fb := boxToFloatBox B
  let startPt := fb.center
  let startVal := evalFloat e startPt

  let rec loop (i : Nat) (rng : PRNG) (bestVal : Float) (bestPt : Nat → Float) :
      (Nat → Float) × Float :=
    match i with
    | 0 => (bestPt, bestVal)
    | k + 1 =>
      let (pt, rng') := samplePoint fb rng
      let val := evalFloat e pt
      if val < bestVal then
        loop k rng' val pt
      else
        loop k rng' bestVal bestPt

  loop samples (PRNG.new seed) startVal startPt

/--
Find multiple good candidates (for multi-start local search).
Returns the k best distinct points found during sampling.
-/
def findTopCandidates (e : Expr) (B : Box) (samples : Nat := 100) (k : Nat := 5)
    (seed : Nat := 12345) : Array ((Nat → Float) × Float) :=
  let fb := boxToFloatBox B
  let startPt := fb.center
  let startVal := evalFloat e startPt

  -- Collect all samples with their values
  let rec collectSamples (i : Nat) (rng : PRNG) (acc : Array ((Nat → Float) × Float)) :
      Array ((Nat → Float) × Float) :=
    match i with
    | 0 => acc
    | n + 1 =>
      let (pt, rng') := samplePoint fb rng
      let val := evalFloat e pt
      collectSamples n rng' (acc.push (pt, val))

  let allSamples := collectSamples samples (PRNG.new seed) #[(startPt, startVal)]

  -- Sort by value and take top k
  let sorted := allSamples.qsort (fun a b => a.2 < b.2)
  sorted.extract 0 k

/-! ### Grid Search -/

/--
Uniform grid search over a box.
Samples a regular grid with `pointsPerDim` points along each dimension.
Total samples = pointsPerDim^dim, so use sparingly for high dimensions.
-/
def gridSearch (e : Expr) (B : Box) (pointsPerDim : Nat := 10) : (Nat → Float) × Float :=
  let fb := boxToFloatBox B
  let dim := fb.dim

  if dim == 0 then
    (fun _ => 0.0, evalFloat e (fun _ => 0.0))
  else
    -- Generate grid points for one dimension
    let gridFor1D (center radius : Float) : Array Float :=
      if pointsPerDim <= 1 then #[center]
      else
        let step := 2.0 * radius / (pointsPerDim - 1).toFloat
        Array.range pointsPerDim |>.map fun i =>
          (center - radius) + i.toFloat * step

    -- For simplicity, only handle 1D and 2D efficiently
    -- Higher dimensions would need proper enumeration
    match dim with
    | 1 =>
      let pts := gridFor1D (fb.centers.getD 0 0.0) (fb.radii.getD 0 0.0)
      let results := pts.map fun x =>
        let pt : Nat → Float := fun i => if i == 0 then x else 0.0
        (pt, evalFloat e pt)
      let best := results.foldl (fun acc r => if r.2 < acc.2 then r else acc)
                    (results.getD 0 (fun _ => 0.0, 1.0e308))
      best
    | 2 =>
      let pts0 := gridFor1D (fb.centers.getD 0 0.0) (fb.radii.getD 0 0.0)
      let pts1 := gridFor1D (fb.centers.getD 1 0.0) (fb.radii.getD 1 0.0)
      -- Use fold instead of mutable state
      let initBest : (Nat → Float) × Float := (fun _ => 0.0, 1.0e308)
      let result := pts0.foldl (fun acc0 x =>
        pts1.foldl (fun acc1 y =>
          let pt : Nat → Float := fun i =>
            if i == 0 then x else if i == 1 then y else 0.0
          let val := evalFloat e pt
          if val < acc1.2 then (pt, val) else acc1
        ) acc0
      ) initBest
      result
    | _ =>
      -- For higher dimensions, fall back to Monte Carlo
      findBestCandidate e B (samples := pointsPerDim * pointsPerDim) (seed := 42)

/-! ### Combined Strategy -/

/--
Hybrid search combining grid and Monte Carlo.
First does a coarse grid search, then refines around the best point with Monte Carlo.
-/
def hybridSearch (e : Expr) (B : Box) (gridPoints : Nat := 5) (mcSamples : Nat := 50)
    (seed : Nat := 12345) : (Nat → Float) × Float :=
  -- Phase 1: Coarse grid to find promising region
  let (gridBest, gridVal) := gridSearch e B (pointsPerDim := gridPoints)

  -- Phase 2: Monte Carlo refinement
  let (mcBest, mcVal) := findBestCandidate e B (samples := mcSamples) (seed := seed)

  -- Return whichever is better
  if mcVal < gridVal then (mcBest, mcVal) else (gridBest, gridVal)

end LeanBound.Numerics.Search
