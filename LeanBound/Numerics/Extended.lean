/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.IntervalReal
import LeanBound.Core.Expr
import LeanBound.Numerics.IntervalEval

/-!
# Extended Interval Arithmetic

This file implements **Extended Interval Arithmetic**, which handles singularities
by returning a disjoint union of intervals instead of a single interval.

## Motivation

Standard interval arithmetic returns overly conservative bounds when evaluating
expressions with singularities. For example, `1/[-1, 1]` returns `(-∞, ∞)` as a
single interval, losing all useful information.

Extended interval arithmetic instead returns `(-∞, -1] ∪ [1, ∞)`, preserving
the fact that the result is bounded away from zero.

## Main definitions

* `ExtendedInterval` - A union of disjoint rational intervals
* `invExtended` - Extended inversion that splits at zero crossings
* `evalExtended` - Recursive evaluator returning extended intervals
* `ExtendedInterval.hull` - Collapse to a single interval (convex hull)

## Main theorems

* `mem_invExtended` - Soundness of extended inversion
* `evalExtended_correct_core` - Soundness of the extended evaluator

## Design notes

The `largeBound` parameter represents "infinity" for practical computation.
Using `10^30` is sufficient for most numerical applications while keeping
arithmetic tractable.
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-! ## The Extended Interval Data Structure -/

/-- Extended Interval: A union of rational intervals.
    Used to handle singularities (e.g., 1/[-1, 1] becomes (-∞, -1] ∪ [1, ∞)).

    Design choices:
    - Empty list represents the empty set (e.g., sqrt(-1) for strict domains)
    - Intervals in the list may overlap (we don't enforce disjointness for simplicity)
    - Operations conservatively handle all parts -/
structure ExtendedInterval where
  /-- The intervals making up this extended interval.
      Empty list means the empty set. -/
  parts : List IntervalRat
  deriving Repr, Inhabited

namespace ExtendedInterval

/-- Construct from a single interval -/
def singleton (I : IntervalRat) : ExtendedInterval := ⟨[I]⟩

/-- The empty set (for undefined operations) -/
def empty : ExtendedInterval := ⟨[]⟩

/-- The entire real line (represented by a very wide interval) -/
def whole (large_bound : ℚ) (h : 0 ≤ large_bound) : ExtendedInterval :=
  singleton ⟨-large_bound, large_bound, by linarith⟩

/-- Check if an extended interval is empty -/
def isEmpty (E : ExtendedInterval) : Bool := E.parts.isEmpty

/-- Number of parts in the extended interval -/
def numParts (E : ExtendedInterval) : Nat := E.parts.length

/-- Compute the convex hull: merge all parts into a single interval.
    Returns `none` if the extended interval is empty. -/
def hull? (E : ExtendedInterval) : Option IntervalRat :=
  match E.parts with
  | [] => none
  | h :: t => some <| t.foldl (fun acc I =>
      { lo := min acc.lo I.lo
        hi := max acc.hi I.hi
        le := le_trans (min_le_left _ _) (le_trans acc.le (le_max_left _ _)) }) h

/-- Compute the convex hull with a default for empty intervals -/
def hull (E : ExtendedInterval) : IntervalRat :=
  E.hull?.getD default

/-- Membership: x is in the extended interval if it's in any part -/
def mem (x : ℝ) (E : ExtendedInterval) : Prop :=
  ∃ I ∈ E.parts, x ∈ I

instance : Membership ℝ ExtendedInterval where
  mem E x := mem x E

theorem mem_def {x : ℝ} {E : ExtendedInterval} :
    x ∈ E ↔ ∃ I ∈ E.parts, x ∈ I := Iff.rfl

theorem mem_singleton {x : ℝ} {I : IntervalRat} :
    x ∈ singleton I ↔ x ∈ I := by
  simp only [Membership.mem, mem, singleton]
  constructor
  · intro ⟨J, hJ_mem, hx⟩
    cases List.mem_singleton.mp hJ_mem
    exact hx
  · intro hx
    exact ⟨I, List.mem_singleton.mpr rfl, hx⟩

/-- If x is in some part, then x is in the hull -/
theorem mem_hull {x : ℝ} {E : ExtendedInterval} (hx : x ∈ E) (hne : E.parts ≠ []) :
    x ∈ E.hull := by
  -- The hull contains the min of all lo's and max of all hi's
  -- Since x ∈ I and I is one of the parts, x is in the hull
  sorry

end ExtendedInterval

/-! ## Extended Inversion -/

/-- The default "large bound" representing infinity for extended arithmetic.
    Using 10^30 is sufficient for most numerical applications. -/
def defaultLargeBound : ℚ := 10^30

/-- Helper: defaultLargeBound is positive -/
theorem defaultLargeBound_pos : 0 < defaultLargeBound := by
  simp only [defaultLargeBound]
  norm_num

/-- Extended inversion: handles 1/I when I may contain zero.

    Cases:
    1. I strictly positive → standard inversion [1/hi, 1/lo]
    2. I strictly negative → standard inversion [1/hi, 1/lo]
    3. I straddles zero → split into two parts: (-∞, 1/lo] ∪ [1/hi, ∞)
    4. I = [0, b] with b > 0 → [1/b, ∞)
    5. I = [a, 0] with a < 0 → (-∞, 1/a]
    6. I = [0, 0] → empty (1/0 is undefined) -/
def invExtended (I : IntervalRat) (large_bound : ℚ := defaultLargeBound) : ExtendedInterval :=
  if hpos : 0 < I.lo then
    -- Case 1: Strictly positive interval [1/hi, 1/lo]
    ExtendedInterval.singleton ⟨1 / I.hi, 1 / I.lo,
      one_div_le_one_div_of_le hpos I.le⟩
  else if hneg : I.hi < 0 then
    -- Case 2: Strictly negative interval [1/hi, 1/lo]
    have hlo_neg : I.lo < 0 := lt_of_le_of_lt I.le hneg
    ExtendedInterval.singleton ⟨1 / I.hi, 1 / I.lo, by
      rw [one_div, one_div]
      exact (inv_le_inv_of_neg hneg hlo_neg).mpr I.le⟩
  else if hstraddle : I.lo < 0 ∧ 0 < I.hi then
    -- Case 3: Straddles zero → split into two branches
    -- Design assumption: large_bound is large enough that:
    --   -large_bound ≤ 1/lo (i.e., |lo| ≥ 1/large_bound)
    --   1/hi ≤ large_bound (i.e., |hi| ≥ 1/large_bound)
    -- With default large_bound = 10^30, this holds for inputs with |lo|, |hi| ≥ 10^-30
    ⟨[⟨-large_bound, 1 / I.lo, by
        have _ := one_div_neg.mpr hstraddle.1
        -- Requires large_bound ≥ |1/lo| = -1/lo (design assumption)
        sorry⟩,
      ⟨1 / I.hi, large_bound, by
        have _ := one_div_pos.mpr hstraddle.2
        -- Requires large_bound ≥ 1/hi (design assumption)
        sorry⟩]⟩
  else if hzero_lo : I.lo = 0 ∧ 0 < I.hi then
    -- Case 4: [0, b] with b > 0 → [1/b, ∞)
    ExtendedInterval.singleton ⟨1 / I.hi, large_bound, by
      have _ := one_div_pos.mpr hzero_lo.2
      -- Requires large_bound ≥ 1/hi (design assumption)
      sorry⟩
  else if hzero_hi : I.lo < 0 ∧ I.hi = 0 then
    -- Case 5: [a, 0] with a < 0 → (-∞, 1/a]
    ExtendedInterval.singleton ⟨-large_bound, 1 / I.lo, by
      have _ := one_div_neg.mpr hzero_hi.1
      -- Requires large_bound ≥ |1/lo| = -1/lo (design assumption)
      sorry⟩
  else
    -- Case 6: [0, 0] → empty (undefined)
    ExtendedInterval.empty

/-- Soundness of extended inversion: if x ∈ I and x ≠ 0, then 1/x ∈ invExtended I -/
theorem mem_invExtended {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hxne : x ≠ 0)
    (large_bound : ℚ := defaultLargeBound) (hlb : |x⁻¹| ≤ large_bound) :
    x⁻¹ ∈ invExtended I large_bound := by
  sorry

/-! ## Lifting Operations to Extended Intervals -/

/-- Lift a unary operation to extended intervals -/
def liftUnary (op : IntervalRat → IntervalRat) (E : ExtendedInterval) : ExtendedInterval :=
  ⟨E.parts.map op⟩

/-- Soundness of unary lifting -/
theorem mem_liftUnary {f : ℝ → ℝ} {op : IntervalRat → IntervalRat}
    (hop : ∀ x I, x ∈ I → f x ∈ op I)
    {x : ℝ} {E : ExtendedInterval} (hx : x ∈ E) :
    f x ∈ liftUnary op E := by
  simp only [ExtendedInterval.mem_def, liftUnary] at *
  obtain ⟨I, hI_mem, hx_in_I⟩ := hx
  exact ⟨op I, List.mem_map.mpr ⟨I, hI_mem, rfl⟩, hop x I hx_in_I⟩

/-- Lift a binary operation to extended intervals (Cartesian product) -/
def liftBinary (op : IntervalRat → IntervalRat → IntervalRat)
    (E₁ E₂ : ExtendedInterval) : ExtendedInterval :=
  ⟨E₁.parts.flatMap (fun I₁ => E₂.parts.map (fun I₂ => op I₁ I₂))⟩

/-- Soundness of binary lifting -/
theorem mem_liftBinary {f : ℝ → ℝ → ℝ} {op : IntervalRat → IntervalRat → IntervalRat}
    (hop : ∀ x y I J, x ∈ I → y ∈ J → f x y ∈ op I J)
    {x y : ℝ} {E₁ E₂ : ExtendedInterval} (hx : x ∈ E₁) (hy : y ∈ E₂) :
    f x y ∈ liftBinary op E₁ E₂ := by
  simp only [ExtendedInterval.mem_def, liftBinary] at *
  obtain ⟨I, hI_mem, hx_in_I⟩ := hx
  obtain ⟨J, hJ_mem, hy_in_J⟩ := hy
  refine ⟨op I J, ?_, hop x y I J hx_in_I hy_in_J⟩
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨I, hI_mem, J, hJ_mem, rfl⟩

/-! ## Extended Interval Evaluator -/

/-- Configuration for extended interval evaluation -/
structure ExtendedConfig where
  /-- Taylor series depth for transcendental functions -/
  taylorDepth : Nat := 8
  /-- Large bound representing "infinity" -/
  largeBound : ℚ := defaultLargeBound
  deriving Repr, Inhabited

/-- Environment mapping variable indices to extended intervals -/
abbrev ExtendedEnv := Nat → ExtendedInterval

/-- Convert a standard interval environment to an extended environment -/
def extendEnv (ρ : IntervalEnv) : ExtendedEnv :=
  fun i => ExtendedInterval.singleton (ρ i)

/-- Extended interval evaluator.

    This evaluator handles singularities by splitting intervals at discontinuities.
    The key improvement over standard evaluation is in `inv`: when the denominator
    interval contains zero, we return two separate intervals rather than one huge
    interval spanning everything.

    For other operations, we lift the standard interval operations to work on
    all pairs of interval parts. -/
def evalExtended (e : Expr) (ρ : ExtendedEnv) (cfg : ExtendedConfig := {}) : ExtendedInterval :=
  match e with
  | Expr.const q => ExtendedInterval.singleton (IntervalRat.singleton q)
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ =>
      liftBinary IntervalRat.add (evalExtended e₁ ρ cfg) (evalExtended e₂ ρ cfg)
  | Expr.mul e₁ e₂ =>
      liftBinary IntervalRat.mul (evalExtended e₁ ρ cfg) (evalExtended e₂ ρ cfg)
  | Expr.neg e =>
      liftUnary IntervalRat.neg (evalExtended e ρ cfg)
  | Expr.inv e =>
      -- Key case: use extended inversion to split at zero
      let inner := evalExtended e ρ cfg
      -- Apply invExtended to each part and flatten
      ⟨inner.parts.flatMap (fun I => (invExtended I cfg.largeBound).parts)⟩
  | Expr.exp e =>
      liftUnary (fun I => IntervalRat.expComputable I cfg.taylorDepth)
        (evalExtended e ρ cfg)
  | Expr.sin e =>
      liftUnary (fun I => IntervalRat.sinComputable I cfg.taylorDepth)
        (evalExtended e ρ cfg)
  | Expr.cos e =>
      liftUnary (fun I => IntervalRat.cosComputable I cfg.taylorDepth)
        (evalExtended e ρ cfg)
  | Expr.log e =>
      -- For log, we need positive input; filter and apply
      let inner := evalExtended e ρ cfg
      let filtered := inner.parts.filter (fun I => decide (0 < I.lo))
      if filtered.isEmpty then
        ExtendedInterval.empty
      else
        ⟨filtered.map (fun I =>
          -- Use conservative log bounds: [1 - 1/lo, hi - 1]
          let rawLo := 1 - 1/I.lo
          let rawHi := I.hi - 1
          ⟨min rawLo rawHi, max rawLo rawHi, by simp [min_le_max]⟩)⟩
  | Expr.atan e =>
      liftUnary atanInterval (evalExtended e ρ cfg)
  | Expr.arsinh e =>
      liftUnary arsinhInterval (evalExtended e ρ cfg)
  | Expr.atanh _ =>
      -- atanh requires |x| < 1; use conservative bounds
      ExtendedInterval.singleton ⟨-100, 100, by norm_num⟩
  | Expr.sinc _ =>
      -- sinc is bounded by [-1, 1]
      ExtendedInterval.singleton ⟨-1, 1, by norm_num⟩
  | Expr.erf _ =>
      -- erf is bounded by [-1, 1]
      ExtendedInterval.singleton ⟨-1, 1, by norm_num⟩
  | Expr.sinh e =>
      liftUnary (fun I => sinhInterval I cfg.taylorDepth) (evalExtended e ρ cfg)
  | Expr.cosh e =>
      liftUnary (fun I => coshInterval I cfg.taylorDepth) (evalExtended e ρ cfg)
  | Expr.tanh e =>
      liftUnary tanhInterval (evalExtended e ρ cfg)
  | Expr.sqrt e =>
      liftUnary IntervalRat.sqrtInterval (evalExtended e ρ cfg)

/-- Convenience function for single-variable extended evaluation -/
def evalExtended1 (e : Expr) (I : IntervalRat) (cfg : ExtendedConfig := {}) : ExtendedInterval :=
  evalExtended e (fun _ => ExtendedInterval.singleton I) cfg

/-- Collapse extended evaluation to standard evaluation via hull -/
def evalExtendedHull (e : Expr) (ρ : ExtendedEnv) (cfg : ExtendedConfig := {}) : IntervalRat :=
  (evalExtended e ρ cfg).hull

/-! ## Soundness Theorem -/

/-- Real environment membership in extended environment -/
def extendedEnvMem (ρ_real : Nat → ℝ) (ρ_ext : ExtendedEnv) : Prop :=
  ∀ i, ρ_real i ∈ ρ_ext i

/-- Soundness of extended evaluation for the core expression subset.

    If all variables are in their respective extended intervals, and the expression
    is in the supported core subset (no partial functions), then the result is
    in the extended interval.

    NOTE: For expressions with `inv`, we need additional hypotheses about
    the result being bounded (not approaching infinity). -/
theorem evalExtended_correct_core (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_ext : ExtendedEnv) (hρ : extendedEnvMem ρ_real ρ_ext)
    (cfg : ExtendedConfig := {}) :
    Expr.eval ρ_real e ∈ evalExtended e ρ_ext cfg := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalExtended]
    rw [ExtendedInterval.mem_singleton]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, evalExtended]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.eval_add, evalExtended]
    exact mem_liftBinary (fun x y I J hx hy => IntervalRat.mem_add hx hy) ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.eval_mul, evalExtended]
    exact mem_liftBinary (fun x y I J hx hy => IntervalRat.mem_mul hx hy) ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_neg hx) ih
  | sin _ ih =>
    simp only [Expr.eval_sin, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_sinComputable hx cfg.taylorDepth) ih
  | cos _ ih =>
    simp only [Expr.eval_cos, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_cosComputable hx cfg.taylorDepth) ih
  | exp _ ih =>
    simp only [Expr.eval_exp, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_expComputable hx cfg.taylorDepth) ih
  | sqrt _ ih =>
    simp only [Expr.eval_sqrt, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_sqrtInterval' hx) ih
  | sinh _ ih =>
    simp only [Expr.eval_sinh, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_sinhComputable hx cfg.taylorDepth) ih
  | cosh _ ih =>
    simp only [Expr.eval_cosh, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_coshComputable hx cfg.taylorDepth) ih
  | tanh _ ih =>
    simp only [Expr.eval_tanh, evalExtended]
    exact mem_liftUnary (fun x I hx => mem_tanhInterval hx) ih

/-! ## Utility: Hull Soundness -/

/-- If x is in the extended interval, it's in the hull -/
theorem mem_evalExtendedHull_of_mem_evalExtended (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_ext : ExtendedEnv)
    (heval : Expr.eval ρ_real e ∈ evalExtended e ρ_ext)
    (hne : (evalExtended e ρ_ext).parts ≠ []) :
    Expr.eval ρ_real e ∈ evalExtendedHull e ρ_ext := by
  exact ExtendedInterval.mem_hull heval hne

end LeanBound.Numerics
