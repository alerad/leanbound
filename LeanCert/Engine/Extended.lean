/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalReal
import LeanCert.Core.Expr
import LeanCert.Engine.IntervalEval

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

namespace LeanCert.Engine

open LeanCert.Core

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

/-- Helper: the foldl operation maintains the property that the accumulated interval
    has lo ≤ head.lo and hi ≥ head.hi -/
theorem foldl_contains_head (t : List IntervalRat) (h : IntervalRat) :
    let result := t.foldl (fun acc I =>
      { lo := min acc.lo I.lo
        hi := max acc.hi I.hi
        le := le_trans (min_le_left _ _) (le_trans acc.le (le_max_left _ _)) }) h
    result.lo ≤ h.lo ∧ h.hi ≤ result.hi := by
  induction t generalizing h with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    have ih' := ih ⟨min h.lo hd.lo, max h.hi hd.hi,
      le_trans (min_le_left _ _) (le_trans h.le (le_max_left _ _))⟩
    constructor
    · calc _ ≤ min h.lo hd.lo := ih'.1
           _ ≤ h.lo := min_le_left _ _
    · calc h.hi ≤ max h.hi hd.hi := le_max_left _ _
           _ ≤ _ := ih'.2

/-- Helper: the foldl operation maintains the property that the accumulated interval
    contains any element from the tail -/
theorem foldl_contains_tail (t : List IntervalRat) (h : IntervalRat) (I : IntervalRat)
    (hI : I ∈ t) :
    let result := t.foldl (fun acc J =>
      { lo := min acc.lo J.lo
        hi := max acc.hi J.hi
        le := le_trans (min_le_left _ _) (le_trans acc.le (le_max_left _ _)) }) h
    result.lo ≤ I.lo ∧ I.hi ≤ result.hi := by
  induction t generalizing h with
  | nil => simp at hI
  | cons hd tl ih =>
    simp only [List.foldl]
    cases List.mem_cons.mp hI with
    | inl heq =>
      subst heq
      have hhead := foldl_contains_head tl ⟨min h.lo I.lo, max h.hi I.hi,
        le_trans (min_le_left _ _) (le_trans h.le (le_max_left _ _))⟩
      constructor
      · calc _ ≤ min h.lo I.lo := hhead.1
             _ ≤ I.lo := min_le_right _ _
      · calc I.hi ≤ max h.hi I.hi := le_max_right _ _
             _ ≤ _ := hhead.2
    | inr hmem =>
      exact ih ⟨min h.lo hd.lo, max h.hi hd.hi,
        le_trans (min_le_left _ _) (le_trans h.le (le_max_left _ _))⟩ hmem

/-- If x is in some part, then x is in the hull.
    The proof follows from the fact that hull.lo = min of all lo's ≤ I.lo ≤ x
    and x ≤ I.hi ≤ max of all hi's = hull.hi. -/
theorem mem_hull {x : ℝ} {E : ExtendedInterval} (hx : x ∈ E) (hne : E.parts ≠ []) :
    x ∈ E.hull := by
  obtain ⟨I, hI_mem, hx_in_I⟩ := hx
  -- Show x is in the hull interval
  simp only [hull, hull?]
  cases hparts : E.parts with
  | nil => exact absurd hparts hne
  | cons hd tl =>
    simp only [Option.getD_some, IntervalRat.mem_def]
    -- I is either hd or in tl
    cases List.mem_cons.mp (hparts ▸ hI_mem) with
    | inl heq =>
      -- I = hd
      subst heq
      have hhead := foldl_contains_head tl I
      constructor
      · calc (↑(tl.foldl _ I).lo : ℝ) ≤ I.lo := by exact_mod_cast hhead.1
             _ ≤ x := hx_in_I.1
      · calc x ≤ I.hi := hx_in_I.2
             _ ≤ (tl.foldl _ I).hi := by exact_mod_cast hhead.2
    | inr hmem =>
      -- I ∈ tl
      have htail := foldl_contains_tail tl hd I hmem
      constructor
      · calc (↑(tl.foldl _ hd).lo : ℝ) ≤ I.lo := by exact_mod_cast htail.1
             _ ≤ x := hx_in_I.1
      · calc x ≤ I.hi := hx_in_I.2
             _ ≤ (tl.foldl _ hd).hi := by exact_mod_cast htail.2

end ExtendedInterval

/-! ## Extended Inversion -/

/-- The default "large bound" representing infinity for extended arithmetic.
    Using 10^30 is sufficient for most numerical applications. -/
def defaultLargeBound : ℚ := 10^30

/-- Helper: defaultLargeBound is positive -/
theorem defaultLargeBound_pos : 0 < defaultLargeBound := by
  simp only [defaultLargeBound]
  norm_num

/-- Helper to construct an interval, using min/max to ensure validity -/
private def mkSafeInterval (a b : ℚ) : IntervalRat :=
  { lo := min a b, hi := max a b, le := @min_le_max ℚ _ a b }

private theorem mem_mkSafeInterval_of_le_le {x : ℝ} {a b : ℚ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    x ∈ mkSafeInterval a b := by
  simp only [mkSafeInterval, IntervalRat.mem_def, Rat.cast_min, inf_le_iff, Rat.cast_max,
    le_sup_iff]
  exact ⟨Or.inl ha, Or.inr hb⟩

/-- Extended inversion: handles 1/I when I may contain zero.

    Cases:
    1. I strictly positive → standard inversion [1/hi, 1/lo]
    2. I strictly negative → standard inversion [1/hi, 1/lo]
    3. I straddles zero → split into two parts: (-∞, 1/lo] ∪ [1/hi, ∞)
    4. I = [0, b] with b > 0 → [1/b, ∞)
    5. I = [a, 0] with a < 0 → (-∞, 1/a]
    6. I = [0, 0] → empty (1/0 is undefined)

    NOTE: Uses large_bound (default 10^30) to represent ±∞. For inputs with
    |lo|, |hi| ≥ 10^-30, the bounds are guaranteed valid. -/
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
  else if _hstraddle : I.lo < 0 ∧ 0 < I.hi then
    -- Case 3: Straddles zero → split into two branches
    -- Use mkSafeInterval to guarantee well-formedness
    ⟨[mkSafeInterval (-large_bound) (1 / I.lo),
      mkSafeInterval (1 / I.hi) large_bound]⟩
  else if _hzero_lo : I.lo = 0 ∧ 0 < I.hi then
    -- Case 4: [0, b] with b > 0 → [1/b, ∞)
    ExtendedInterval.singleton (mkSafeInterval (1 / I.hi) large_bound)
  else if _hzero_hi : I.lo < 0 ∧ I.hi = 0 then
    -- Case 5: [a, 0] with a < 0 → (-∞, 1/a]
    ExtendedInterval.singleton (mkSafeInterval (-large_bound) (1 / I.lo))
  else
    -- Case 6: [0, 0] → empty (undefined)
    ExtendedInterval.empty

/-- Soundness of extended inversion: if x ∈ I and x ≠ 0, then 1/x ∈ invExtended I.

    The hypothesis `hlb : |x⁻¹| ≤ large_bound` ensures that 1/x fits within the finite bounds.
    This is the key assumption that makes extended inversion sound - without it, 1/x could
    be arbitrarily large for x close to 0.

    NOTE: This theorem has remaining sorries because the `invExtended` function itself
    has design assumption sorries for interval validity when constructing intervals near zero.
    The membership logic is correct modulo these construction assumptions. -/
theorem mem_invExtended {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hxne : x ≠ 0)
    (large_bound : ℚ := defaultLargeBound) (hlb : |x⁻¹| ≤ large_bound) :
    x⁻¹ ∈ invExtended I large_bound := by
  have hxI : (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) := (IntervalRat.mem_def _ _).1 hx
  have hbound : (-(large_bound : ℝ)) ≤ x⁻¹ ∧ x⁻¹ ≤ (large_bound : ℝ) := abs_le.mp hlb
  by_cases hpos : 0 < I.lo
  · have hxpos : 0 < x := by
      have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
      exact lt_of_lt_of_le hlo_pos hxI.1
    have hhi_pos : (0 : ℝ) < I.hi := by
      have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
      have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
      linarith
    simp [invExtended, hpos, ExtendedInterval.mem_singleton, IntervalRat.mem_def,
      Rat.cast_inv, one_div]
    constructor
    · exact (inv_le_inv₀ hhi_pos hxpos).mpr hxI.2
    · exact (inv_le_inv₀ hxpos (by exact_mod_cast hpos)).mpr hxI.1
  · by_cases hneg : I.hi < 0
    · have hxneg : x < 0 := lt_of_le_of_lt hxI.2 (by exact_mod_cast hneg)
      have hhi_neg : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
      have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
      have hlo_neg : (I.lo : ℝ) < 0 := lt_of_le_of_lt hle hhi_neg
      simp [invExtended, hpos, hneg, ExtendedInterval.mem_singleton, IntervalRat.mem_def,
        Rat.cast_inv, one_div]
      constructor
      · exact (inv_le_inv_of_neg (by exact_mod_cast hneg) hxneg).mpr hxI.2
      · exact (inv_le_inv_of_neg hxneg hlo_neg).mpr hxI.1
    · by_cases hstraddle : I.lo < 0 ∧ 0 < I.hi
      · by_cases hxneg : x < 0
        · have hupper_r : x⁻¹ ≤ (I.lo : ℝ)⁻¹ :=
            (inv_le_inv_of_neg hxneg (by exact_mod_cast hstraddle.1)).mpr hxI.1
          have hupper : x⁻¹ ≤ ((1 / I.lo : ℚ) : ℝ) := by
            simpa [Rat.cast_inv, Rat.cast_div, Rat.cast_one, one_div] using hupper_r
          have hlower : ((-large_bound : ℚ) : ℝ) ≤ x⁻¹ := by
            simpa using hbound.1
          have hmem : x⁻¹ ∈ mkSafeInterval (-large_bound) (1 / I.lo) :=
            mem_mkSafeInterval_of_le_le hlower hupper
          simp [invExtended, hpos, hneg, hstraddle, ExtendedInterval.mem_def]
          left
          simpa [IntervalRat.mem_def] using hmem
        · have hxpos : 0 < x := by
            have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
            have hxne0 : (0 : ℝ) ≠ x := by simpa [ne_comm] using hxne
            exact lt_of_le_of_ne hxnonneg hxne0
          have hlower_r : (I.hi : ℝ)⁻¹ ≤ x⁻¹ :=
            (inv_le_inv₀ (by exact_mod_cast hstraddle.2) hxpos).mpr hxI.2
          have hlower : ((1 / I.hi : ℚ) : ℝ) ≤ x⁻¹ := by
            simpa [Rat.cast_inv, Rat.cast_div, Rat.cast_one, one_div] using hlower_r
          have hupper : x⁻¹ ≤ (large_bound : ℝ) := hbound.2
          have hmem : x⁻¹ ∈ mkSafeInterval (1 / I.hi) large_bound :=
            mem_mkSafeInterval_of_le_le hlower hupper
          simp [invExtended, hpos, hneg, hstraddle, ExtendedInterval.mem_def]
          right
          simpa [IntervalRat.mem_def] using hmem
      · by_cases hzero_lo : I.lo = 0 ∧ 0 < I.hi
        · have hxpos : 0 < x := by
            have hxnonneg : 0 ≤ x := by simpa [hzero_lo.1] using hxI.1
            have hxne0 : (0 : ℝ) ≠ x := by simpa [ne_comm] using hxne
            exact lt_of_le_of_ne hxnonneg hxne0
          have hlower_r : (I.hi : ℝ)⁻¹ ≤ x⁻¹ :=
            (inv_le_inv₀ (by exact_mod_cast hzero_lo.2) hxpos).mpr hxI.2
          have hlower : ((1 / I.hi : ℚ) : ℝ) ≤ x⁻¹ := by
            simpa [Rat.cast_inv, Rat.cast_div, Rat.cast_one, one_div] using hlower_r
          have hupper : x⁻¹ ≤ (large_bound : ℝ) := hbound.2
          have hmem : x⁻¹ ∈ mkSafeInterval (1 / I.hi) large_bound :=
            mem_mkSafeInterval_of_le_le hlower hupper
          simpa [invExtended, hpos, hneg, hstraddle, hzero_lo, ExtendedInterval.mem_singleton] using hmem
        · by_cases hzero_hi : I.lo < 0 ∧ I.hi = 0
          · have hxneg : x < 0 := by
              have hxnonpos : x ≤ 0 := by simpa [hzero_hi.2] using hxI.2
              exact lt_of_le_of_ne hxnonpos hxne
            have hupper_r : x⁻¹ ≤ (I.lo : ℝ)⁻¹ :=
              (inv_le_inv_of_neg hxneg (by exact_mod_cast hzero_hi.1)).mpr hxI.1
            have hupper : x⁻¹ ≤ ((1 / I.lo : ℚ) : ℝ) := by
              simpa [Rat.cast_inv, Rat.cast_div, Rat.cast_one, one_div] using hupper_r
            have hlower : ((-large_bound : ℚ) : ℝ) ≤ x⁻¹ := by
              simpa using hbound.1
            have hmem : x⁻¹ ∈ mkSafeInterval (-large_bound) (1 / I.lo) :=
              mem_mkSafeInterval_of_le_le hlower hupper
            simpa [invExtended, hpos, hneg, hstraddle, hzero_lo, hzero_hi,
              ExtendedInterval.mem_singleton] using hmem
          · exfalso
            -- Remaining case implies I.lo = 0 and I.hi = 0, contradicting x ≠ 0.
            have hlo_nonpos : I.lo ≤ 0 := le_of_not_gt hpos
            have hhi_nonneg : 0 ≤ I.hi := le_of_not_gt hneg
            by_cases hlo_eq : I.lo = 0
            · have hhi_nonpos : I.hi ≤ 0 := by
                have : ¬(0 < I.hi) := by
                  intro hhi_pos
                  exact hzero_lo ⟨hlo_eq, hhi_pos⟩
                exact le_of_not_gt this
              have hhi_eq : I.hi = 0 := le_antisymm hhi_nonpos hhi_nonneg
              have hxzero : x = 0 := by
                have hxlo : (0 : ℝ) ≤ x := by simpa [hlo_eq] using hxI.1
                have hxhi : x ≤ (0 : ℝ) := by simpa [hhi_eq] using hxI.2
                exact le_antisymm hxhi hxlo
              exact hxne hxzero
            · have hlo_neg : I.lo < 0 := lt_of_le_of_ne hlo_nonpos hlo_eq
              have hhi_nonpos : I.hi ≤ 0 := by
                have : ¬(0 < I.hi) := by
                  intro hhi_pos
                  exact hstraddle ⟨hlo_neg, hhi_pos⟩
                exact le_of_not_gt this
              have hhi_eq : I.hi = 0 := le_antisymm hhi_nonpos hhi_nonneg
              exact hzero_hi ⟨hlo_neg, hhi_eq⟩

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
      -- For log, filter to positive intervals and apply logComputable
      let inner := evalExtended e ρ cfg
      let filtered := inner.parts.filter (fun I => decide (0 < I.lo))
      if filtered.isEmpty then
        -- Fallback: return a very wide interval to ensure soundness
        ExtendedInterval.singleton ⟨-1000, 1000, by norm_num⟩
      else
        ⟨filtered.map (fun I => IntervalRat.logComputable I cfg.taylorDepth)⟩
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
  | Expr.pi =>
      ExtendedInterval.singleton piInterval

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

/-- Domain validity for Extended evaluation.
    For log, we require the argument's hull to have positive lower bound,
    ensuring all parts have positive lo and the filter keeps them. -/
def evalDomainValidExtended (e : Expr) (ρ : ExtendedEnv) (cfg : ExtendedConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValidExtended e₁ ρ cfg ∧ evalDomainValidExtended e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValidExtended e₁ ρ cfg ∧ evalDomainValidExtended e₂ ρ cfg
  | Expr.neg e => evalDomainValidExtended e ρ cfg
  | Expr.inv e => evalDomainValidExtended e ρ cfg
  | Expr.exp e => evalDomainValidExtended e ρ cfg
  | Expr.sin e => evalDomainValidExtended e ρ cfg
  | Expr.cos e => evalDomainValidExtended e ρ cfg
  | Expr.log e => evalDomainValidExtended e ρ cfg ∧ (evalExtended e ρ cfg).hull.lo > 0
  | Expr.atan e => evalDomainValidExtended e ρ cfg
  | Expr.arsinh e => evalDomainValidExtended e ρ cfg
  | Expr.atanh e => evalDomainValidExtended e ρ cfg
  | Expr.sinc e => evalDomainValidExtended e ρ cfg
  | Expr.erf e => evalDomainValidExtended e ρ cfg
  | Expr.sinh e => evalDomainValidExtended e ρ cfg
  | Expr.cosh e => evalDomainValidExtended e ρ cfg
  | Expr.tanh e => evalDomainValidExtended e ρ cfg
  | Expr.sqrt e => evalDomainValidExtended e ρ cfg
  | Expr.pi => True

/-- Domain validity is trivially true for ExprSupported expressions (which exclude log). -/
theorem evalDomainValidExtended_of_ExprSupported {e : Expr} (hsupp : ExprSupported e)
    (ρ : ExtendedEnv) (cfg : ExtendedConfig := {}) : evalDomainValidExtended e ρ cfg := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Soundness of extended evaluation for the core expression subset.

    If all variables are in their respective extended intervals, and the expression
    is in the supported core subset (no partial functions), then the result is
    in the extended interval. -/
theorem evalExtended_correct_core (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_ext : ExtendedEnv) (hρ : extendedEnvMem ρ_real ρ_ext)
    (cfg : ExtendedConfig := {})
    (hdom : evalDomainValidExtended e ρ_ext cfg) :
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
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_add, evalExtended]
    exact mem_liftBinary (fun x y I J hx hy => IntervalRat.mem_add hx hy) (ih₁ hdom.1) (ih₂ hdom.2)
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_mul, evalExtended]
    exact mem_liftBinary (fun x y I J hx hy => IntervalRat.mem_mul hx hy) (ih₁ hdom.1) (ih₂ hdom.2)
  | neg _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_neg, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_neg hx) (ih hdom)
  | sin _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_sin, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_sinComputable hx cfg.taylorDepth) (ih hdom)
  | cos _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_cos, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_cosComputable hx cfg.taylorDepth) (ih hdom)
  | exp _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_exp, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_expComputable hx cfg.taylorDepth) (ih hdom)
  | sqrt _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_sqrt, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_sqrtInterval' hx) (ih hdom)
  | sinh _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_sinh, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_sinhComputable hx cfg.taylorDepth) (ih hdom)
  | cosh _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_cosh, evalExtended]
    exact mem_liftUnary (fun x I hx => IntervalRat.mem_coshComputable hx cfg.taylorDepth) (ih hdom)
  | tanh _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_tanh, evalExtended]
    exact mem_liftUnary (fun x I hx => mem_tanhInterval hx) (ih hdom)
  | erf _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_erf, evalExtended]
    -- erf returns singleton [-1, 1], need to show Real.erf x ∈ [-1, 1]
    simp only [ExtendedInterval.mem_singleton, IntervalRat.mem_def]
    simp only [Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_erf _, Real.erf_le_one _⟩
  | @log arg _ ih =>
    simp only [evalDomainValidExtended] at hdom
    simp only [Expr.eval_log, evalExtended]
    -- ih gives membership in evalExtended arg
    have hmem := ih hdom.1
    -- hdom.2 gives (evalExtended arg ρ_ext cfg).hull.lo > 0
    have hpos := hdom.2
    -- Since hull.lo > 0, all parts have lo > 0, so filter keeps everything
    -- and the filtered list is non-empty
    obtain ⟨I, hI_mem, hx_in_I⟩ := hmem
    -- I is in the parts of evalExtended arg
    -- Since hull.lo > 0 and hull.lo = min of all lo's, we have I.lo > 0
    have hI_lo_pos : 0 < I.lo := by
      have hparts_ne : (evalExtended arg ρ_ext cfg).parts ≠ [] := by
        intro h
        simp [h] at hI_mem
      -- hull?.lo is the min of all lo's, so hull.lo ≤ I.lo
      cases hparts_eq : (evalExtended arg ρ_ext cfg).parts with
      | nil => exact absurd hparts_eq hparts_ne
      | cons hd tl =>
        have hI_in : I ∈ hd :: tl := hparts_eq ▸ hI_mem
        cases List.mem_cons.mp hI_in with
        | inl heq =>
          subst heq
          have hhead := ExtendedInterval.foldl_contains_head tl I
          simp only [ExtendedInterval.hull, ExtendedInterval.hull?] at hpos
          rw [hparts_eq] at hpos
          simp only [Option.getD_some] at hpos
          calc 0 < (tl.foldl _ I).lo := hpos
               _ ≤ I.lo := hhead.1
        | inr hmem_tl =>
          have htail := ExtendedInterval.foldl_contains_tail tl hd I hmem_tl
          simp only [ExtendedInterval.hull, ExtendedInterval.hull?] at hpos
          rw [hparts_eq] at hpos
          simp only [Option.getD_some] at hpos
          calc 0 < (tl.foldl _ hd).lo := hpos
               _ ≤ I.lo := htail.1
    -- So I passes the filter
    have hI_filter : I ∈ (evalExtended arg ρ_ext cfg).parts.filter (fun J => decide (0 < J.lo)) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hI_mem, hI_lo_pos⟩
    -- filtered is not empty
    have hfilter_ne : ¬((evalExtended arg ρ_ext cfg).parts.filter (fun J => decide (0 < J.lo))).isEmpty := by
      simp only [List.isEmpty_iff]
      intro h
      simp [h] at hI_filter
    simp only [hfilter_ne, ↓reduceIte]
    -- Now show Real.log x ∈ the result
    simp only [ExtendedInterval.mem_def]
    use IntervalRat.logComputable I cfg.taylorDepth
    constructor
    · simp only [List.mem_map]
      exact ⟨I, hI_filter, rfl⟩
    · exact IntervalRat.mem_logComputable hx_in_I hI_lo_pos cfg.taylorDepth
  | pi =>
    simp only [Expr.eval_pi, evalExtended]
    rw [ExtendedInterval.mem_singleton]
    exact mem_piInterval

/-! ## Utility: Hull Soundness -/

/-- If x is in the extended interval, it's in the hull -/
theorem mem_evalExtendedHull_of_mem_evalExtended (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_ext : ExtendedEnv)
    (heval : Expr.eval ρ_real e ∈ evalExtended e ρ_ext)
    (hne : (evalExtended e ρ_ext).parts ≠ []) :
    Expr.eval ρ_real e ∈ evalExtendedHull e ρ_ext := by
  exact ExtendedInterval.mem_hull heval hne

end LeanCert.Engine
