/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert
import LeanCert.Engine.TaylorModel.Log1p

/-!
# Export Theorems for Tao's PNT Formalization

This file provides the key theorems needed for Tao's Prime Number Theorem project,
specifically for GitHub issues PNT#758 and PNT#759.

## Main Results

* `symmetric_combination_removable_singularity` - The key mathematical insight
* `symmetric_combination_bounded` - Boundedness result for integration
* `li2_definition` - Definition of li(2) via symmetric form

## References

* Tao's Zulip discussion (January 2026) on li(2) computation
* PNT#758: Prove li(x) = Li(x) + li(2)
* PNT#759: Verify li(2) ≈ 1.0451
-/

open LeanCert.Engine.TaylorModel

/-! ### Key Mathematical Results for PNT -/

/-- The symmetric combination g(t) = 1/log(1+t) + 1/log(1-t) has a removable
    singularity at t=0 with limit 1. This is THE key result enabling li(2) computation. -/
theorem symmetric_combination_removable_singularity :
    Filter.Tendsto (fun t => 1/Real.log (1 + t) + 1/Real.log (1 - t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  symmetricLogCombination_tendsto_one

/-- The symmetric combination is bounded by 2 on (0, 1/2].
    This ensures the li(2) integral is absolutely convergent. -/
theorem symmetric_combination_bounded (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1/2) :
    |1/Real.log (1 + t) + 1/Real.log (1 - t)| ≤ 2 :=
  symmetricLogCombination_bounded t ht_pos ht_lt

/-- Alternative algebraic form that eliminates the apparent singularity. -/
theorem symmetric_combination_alt_form (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    1/Real.log (1 + t) + 1/Real.log (1 - t) =
    Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) :=
  symmetricLogCombination_alt t ht_pos ht_lt

/-! ### Definition of li(2)

The logarithmic integral li(2) = ∫₀² dt/log(t) has a singularity at t=1.
Using the symmetric form, we define:

  li(2) = ∫₀¹ (1/log(1+u) + 1/log(1-u)) du

This is absolutely convergent because:
1. The singularity at u=0 is removable (limit = 1)
2. The integrand is bounded (|g| ≤ 2)
-/

/-- Definition of li(2) as the integral of the symmetric combination.
    This sidesteps the principal value issues entirely. -/
noncomputable def li2 : ℝ := ∫ t in (0:ℝ)..1, symmetricLogCombination t

/-! ### Bounds for PNT#759

The Ramanujan-Soldner constant μ ≈ 1.451369... is the unique positive zero of li(x).
The value li(2) ≈ 1.04516378... is what we verify here.
-/

/-- Crude upper bound on li(2). -/
theorem li2_le_two : li2 ≤ 2 := by
  sorry -- Follows from |symmetric_combination| ≤ 2

/-- li(2) is positive. -/
theorem li2_pos : 0 < li2 := by
  sorry -- Follows from symmetric_combination → 1 as t → 0

/-! ### Summary for PNT Integration

**What is proven (no sorry):**
- `symmetric_combination_removable_singularity`: g(t) → 1 as t → 0⁺
- `symmetric_combination_bounded`: |g(t)| ≤ 2 for t ∈ (0, 1/2]
- `symmetric_combination_alt_form`: g = log(1-t²)/(log(1+t)·log(1-t))

**With sorry (needs numerical integration):**
- `li2_le_two`: li(2) ≤ 2
- `li2_pos`: li(2) > 0
- Tight bounds: li(2) ∈ [1.04, 1.06] (in Li2Verified.lean)

**Mathematical significance:**
The removable singularity theorem is the key insight. It transforms the
principal value integral into an absolutely convergent one, enabling:
1. Numerical computation with certified error bounds
2. The identity li(x) = Li(x) + li(2) for x ≥ 2
-/
