/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Network
import LeanCert.ML.IntervalVector
import LeanCert.Engine.IntervalEval
import LeanCert.Core.IntervalRat.Taylor

/-!
# Transformer Components

This module provides verified interval arithmetic implementations of key
Transformer components:

1. **GELU** - Gaussian Error Linear Unit activation
2. **LayerNorm** - Layer Normalization

## Design Notes

### GELU
The GELU activation function is approximated as:
  GELU(x) ≈ 0.5 * x * (1 + tanh(√(2/π) * (x + 0.044715 * x³)))

We implement this by composing verified interval operations.

### LayerNorm
LayerNorm computes: (x - μ) / √(σ² + ε) * γ + β

**Warning**: Standard interval arithmetic loses correlation information,
causing significant overestimation in LayerNorm. For example, if x ∈ [0.9, 1.1],
then mean(x) ∈ [0.9, 1.1], and x - mean becomes [-0.2, 0.2] instead of [0, 0].

Affine Arithmetic (tracking symbolic dependencies) would resolve this.
The current implementation is *sound* but may produce loose bounds.

## References

* Hendrycks & Gimpel, "Gaussian Error Linear Units (GELUs)", 2016
* Ba et al., "Layer Normalization", 2016
-/

namespace LeanCert.ML.Transformer

open LeanCert.Core
open LeanCert.Engine
open LeanCert.ML.IntervalVector

/-! ### Real Definitions (The Specification) -/

/--
GELU Approximation (standard in BERT/GPT-2):
  0.5 * x * (1 + tanh(√(2/π) * (x + 0.044715 * x³)))
-/
noncomputable def Real.gelu (x : ℝ) : ℝ :=
  let c1 : ℝ := Real.sqrt (2 / Real.pi)
  let c2 : ℝ := 0.044715
  0.5 * x * (1 + Real.tanh (c1 * (x + c2 * x * x * x)))

/-- Layer Normalization (Real specification) -/
noncomputable def layerNormReal (x : List ℝ) (gamma beta : List ℚ) (epsilon : ℚ) : List ℝ :=
  let n := x.length
  let mean := x.sum / n
  let variance := (x.map (fun xi => (xi - mean) * (xi - mean))).sum / n
  let denom := Real.sqrt (variance + epsilon)

  -- (x - mean) / denom * gamma + beta
  List.zipWith3
    (fun xi (g : ℚ) (b : ℚ) => ((xi - mean) / denom) * (g : ℝ) + (b : ℝ))
    x gamma beta

/-! ### Interval GELU -/

/-- Constants for GELU approximation as rationals -/
-- √(2/π) ≈ 0.7978845608028654
-- We use a lower bound so that the interval [c1_lo, c1_lo + 2e-6] contains √(2/π)
private def gelu_c1_lo : ℚ := 797884 / 1000000  -- Lower bound for √(2/π)
private def gelu_c2 : ℚ := 44715 / 1000000   -- 0.044715

/--
Verified GELU Interval using IntervalRat arithmetic.

We construct the computation using verified interval operations:
1. Compute x³
2. Compute inner = x + c2 * x³
3. Compute arg = c1 * inner
4. Compute tanh(arg) using conservative [-1, 1] bound
5. Compute 0.5 * x * (1 + tanh(arg))

For tight bounds on tanh, we could use Taylor Models, but the global
bound [-1, 1] is sufficient for most Transformer verification.
-/
def geluIntervalRat (I : IntervalRat) : IntervalRat :=
  -- x³
  let x3 := IntervalRat.pow I 3

  -- inner = x + c2 * x³
  let c2_x3 := IntervalRat.scale gelu_c2 x3
  let inner := IntervalRat.add I c2_x3

  -- arg = c1 * inner (using interval containing √(2/π))
  -- √(2/π) ∈ [0.797884, 0.797885] (provable from 3.141592 < π < 3.141593)
  let c1_interval : IntervalRat := ⟨gelu_c1_lo, gelu_c1_lo + 1/1000000, by norm_num⟩
  let arg := IntervalRat.mul c1_interval inner

  -- tanh(arg) ∈ [-1, 1] always
  let tanh_arg := tanhInterval arg

  -- 1 + tanh(arg)
  let one_plus_tanh := IntervalRat.add (IntervalRat.singleton 1) tanh_arg

  -- 0.5 * x
  let half_x := IntervalRat.scale (1/2) I

  -- Result: 0.5 * x * (1 + tanh(arg))
  IntervalRat.mul half_x one_plus_tanh

/-- GELU on IntervalDyadic with precision control -/
def geluInterval (I : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  let rat_result := geluIntervalRat I.toIntervalRat
  IntervalDyadic.ofIntervalRat rat_result prec

/-- Vector version of GELU -/
def geluVector (v : IntervalVector) (prec : Int := -53) : IntervalVector :=
  v.map (fun I => geluInterval I prec)

/-! ### GELU Correctness -/

/-- The constant √(2/π) is bounded by our rational interval.
    Uses the 6-decimal precision bounds: 3.141592 < π < 3.141593.
    Proof outline: From 3.141592 < π < 3.141593, we get
    0.636618... < 2/π < 0.636620... and thus
    0.797884 < √(2/π) < 0.797885 -/
theorem sqrt_two_div_pi_mem_interval :
    Real.sqrt (2 / Real.pi) ∈
      (⟨gelu_c1_lo, gelu_c1_lo + 1/1000000, by norm_num⟩ : IntervalRat) := by
  rw [IntervalRat.mem_def]
  simp only [gelu_c1_lo]
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · -- Lower bound: ↑(797884/1000000) ≤ √(2/π)
    -- Strategy: Use Real.le_sqrt to convert to squared bound, then use π bounds
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    -- Goal: (797884/1000000)^2 ≤ 2/π
    -- Since π < 3.141593, we have 2/3.141593 < 2/π
    -- So it suffices to show (797884/1000000)^2 < 2/3.141593
    have h_div_bound : (2 : ℝ) / 3.141593 < 2 / Real.pi :=
      div_lt_div_of_pos_left (by norm_num) hpi_pos hpi_hi
    have h_sq_bound : ((797884 / 1000000 : ℚ) : ℝ) ^ 2 < (2 : ℝ) / 3.141593 := by norm_num
    linarith
  · -- Upper bound: √(2/π) ≤ ↑(797885/1000000)
    have hsum : ((797884 / 1000000 : ℚ) + 1 / 1000000) = (797885 / 1000000 : ℚ) := by norm_num
    rw [hsum, Real.sqrt_le_left (by norm_num)]
    -- Goal: 2/π ≤ (797885/1000000)^2
    -- Since 3.141592 < π, we have 2/π < 2/3.141592
    -- So it suffices to show 2/3.141592 < (797885/1000000)^2
    have h_div_bound : (2 : ℝ) / Real.pi < 2 / 3.141592 :=
      div_lt_div_of_pos_left (by norm_num) (by linarith) hpi_lo
    have h_sq_bound : (2 : ℝ) / 3.141592 < ((797885 / 1000000 : ℚ) : ℝ) ^ 2 := by norm_num
    linarith

/-- GELU is bounded by the interval computation.
    The proof follows from composition of verified operations:
    1. x³ ∈ pow I 3 (by mem_pow)
    2. c2*x³ ∈ scale gelu_c2 (pow I 3) (by mem_scale)
    3. x + c2*x³ ∈ add I (scale gelu_c2 (pow I 3)) (by mem_add)
    4. √(2/π) ∈ c1_interval (by sqrt_two_div_pi_mem_interval)
    5. √(2/π) * inner ∈ mul c1_interval inner (by mem_mul)
    6. tanh(arg) ∈ tanhInterval arg (by mem_tanhInterval)
    7. 1 + tanh ∈ add (singleton 1) tanh_interval (by mem_add)
    8. 0.5*x ∈ scale (1/2) I (by mem_scale)
    9. Final: 0.5*x*(1+tanh(...)) ∈ mul half_x one_plus_tanh (by mem_mul) -/
theorem mem_geluIntervalRat {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) :
    Real.gelu x ∈ geluIntervalRat I := by
  simp only [Real.gelu, geluIntervalRat, gelu_c1_lo, gelu_c2]
  -- Key equalities for the constants
  have hc2_eq : (0.044715 : ℝ) = ((44715 / 1000000 : ℚ) : ℝ) := by norm_num
  have h_half_eq : (0.5 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  have h_xxx : x * x * x = x ^ 3 := by ring
  have h_one : (1 : ℝ) = ((1 : ℚ) : ℝ) := by norm_num
  -- Step 1: x³ ∈ pow I 3
  have h_x3 : x ^ 3 ∈ IntervalRat.pow I 3 := IntervalRat.mem_pow hx 3
  -- Step 2: c2 * x³ ∈ scale c2 (pow I 3)
  have h_c2_x3 : (44715 / 1000000 : ℚ) * x ^ 3 ∈ IntervalRat.scale (44715/1000000) (IntervalRat.pow I 3) :=
    IntervalRat.mem_scale (44715/1000000) h_x3
  -- Step 3: x + c2*x³ ∈ add I (scale c2 (pow I 3))
  have h_inner : x + (44715 / 1000000 : ℚ) * x ^ 3 ∈
      IntervalRat.add I (IntervalRat.scale (44715/1000000) (IntervalRat.pow I 3)) :=
    IntervalRat.mem_add hx h_c2_x3
  -- Step 4: √(2/π) ∈ c1_interval
  have h_c1_mem : Real.sqrt (2 / Real.pi) ∈
      (⟨797884 / 1000000, 797884 / 1000000 + 1/1000000, by norm_num⟩ : IntervalRat) :=
    sqrt_two_div_pi_mem_interval
  -- Step 5: √(2/π) * inner ∈ mul c1_interval inner
  have h_arg : Real.sqrt (2 / Real.pi) * (x + (44715 / 1000000 : ℚ) * x ^ 3) ∈
      IntervalRat.mul ⟨797884/1000000, 797884/1000000 + 1/1000000, by norm_num⟩
        (IntervalRat.add I (IntervalRat.scale (44715/1000000) (IntervalRat.pow I 3))) :=
    IntervalRat.mem_mul h_c1_mem h_inner
  -- Step 6: tanh(arg) ∈ tanhInterval arg
  have h_tanh : Real.tanh (Real.sqrt (2 / Real.pi) * (x + (44715 / 1000000 : ℚ) * x ^ 3)) ∈
      tanhInterval (IntervalRat.mul ⟨797884/1000000, 797884/1000000 + 1/1000000, by norm_num⟩
        (IntervalRat.add I (IntervalRat.scale (44715/1000000) (IntervalRat.pow I 3)))) :=
    mem_tanhInterval h_arg
  -- Step 7: 1 + tanh ∈ add (singleton 1) tanh_interval
  have h_one_mem : (1 : ℝ) ∈ IntervalRat.singleton 1 := by
    rw [h_one]; exact IntervalRat.mem_singleton 1
  have h_one_plus_tanh : (1 : ℝ) + Real.tanh (Real.sqrt (2 / Real.pi) * (x + (44715 / 1000000 : ℚ) * x ^ 3)) ∈
      IntervalRat.add (IntervalRat.singleton 1)
        (tanhInterval (IntervalRat.mul ⟨797884/1000000, 797884/1000000 + 1/1000000, by norm_num⟩
          (IntervalRat.add I (IntervalRat.scale (44715/1000000) (IntervalRat.pow I 3))))) :=
    IntervalRat.mem_add h_one_mem h_tanh
  -- Step 8: 0.5*x ∈ scale (1/2) I
  have h_half_x : (1 / 2 : ℚ) * x ∈ IntervalRat.scale (1/2) I :=
    IntervalRat.mem_scale (1/2) hx
  -- Step 9: Final: 0.5*x*(1+tanh) ∈ mul half_x one_plus_tanh
  have h_final : (1 / 2 : ℚ) * x *
      ((1 : ℝ) + Real.tanh (Real.sqrt (2 / Real.pi) * (x + (44715 / 1000000 : ℚ) * x ^ 3))) ∈
      IntervalRat.mul (IntervalRat.scale (1/2) I)
        (IntervalRat.add (IntervalRat.singleton 1)
          (tanhInterval (IntervalRat.mul ⟨797884/1000000, 797884/1000000 + 1/1000000, by norm_num⟩
            (IntervalRat.add I (IntervalRat.scale (44715/1000000) (IntervalRat.pow I 3)))))) :=
    IntervalRat.mem_mul h_half_x h_one_plus_tanh
  -- Now convert to the goal using equalities
  -- Goal has: 0.5 * x * (1 + tanh(√(2/π) * (x + 0.044715 * x * x * x)))
  -- h_final has: (1/2) * x * (1 + tanh(√(2/π) * (x + (44715/1000000) * x^3)))
  -- Need to show they're equal
  have h_xxx_assoc : ((44715 / 1000000 : ℚ) : ℝ) * x * x * x = ((44715 / 1000000 : ℚ) : ℝ) * x ^ 3 := by ring
  have h_goal_eq : (0.5 : ℝ) * x * (1 + Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x * x * x)))
      = (1 / 2 : ℚ) * x * ((1 : ℝ) + Real.tanh (Real.sqrt (2 / Real.pi) * (x + (44715 / 1000000 : ℚ) * x ^ 3))) := by
    rw [h_half_eq, hc2_eq, h_xxx_assoc]
  rw [h_goal_eq]
  exact h_final

theorem mem_geluInterval {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ I) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    Real.gelu x ∈ geluInterval I prec := by
  -- Follows from mem_geluIntervalRat and mem_ofIntervalRat
  simp only [geluInterval]
  have hmem_rat : x ∈ I.toIntervalRat := IntervalDyadic.mem_toIntervalRat.mpr hx
  have hgelu_in_rat := mem_geluIntervalRat hmem_rat
  exact IntervalDyadic.mem_ofIntervalRat hgelu_in_rat prec hprec

/-! ### Interval Layer Normalization -/

/-- Layer Normalization parameters -/
structure LayerNormParams where
  /-- Scale parameter γ -/
  gamma : List ℚ
  /-- Shift parameter β -/
  beta : List ℚ
  /-- Numerical stability constant ε > 0 -/
  epsilon : ℚ
  /-- ε must be positive -/
  epsilon_pos : 0 < epsilon
  deriving Repr

namespace LayerNormParams

/-- Sum of interval vector elements -/
def sumIntervals (v : IntervalVector) : IntervalDyadic :=
  match v with
  | [] => IntervalDyadic.singleton (Core.Dyadic.ofInt 0)
  | h :: t => t.foldl IntervalDyadic.add h

/-- Zero interval -/
private def zeroInterval : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt 0)

/--
Standard Interval LayerNorm.

**Warning**: This implementation does NOT track correlations between
variables. The interval for `x - mean` can be significantly wider than
the true range because `mean` depends on `x`.

This is mathematically SOUND (over-approximates) but may be LOOSE.
Affine Arithmetic would improve tightness.

Steps:
1. Compute mean: μ = Σx / n
2. Compute variance: σ² = Σ(x - μ)² / n
3. Compute denominator: 1 / √(σ² + ε)
4. Normalize and scale: ((x - μ) * inv_denom) * γ + β
-/
def forwardInterval (params : LayerNormParams) (x : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  let n := x.length
  if hn : n = 0 then []
  else
    let n_rat : ℚ := n
    let inv_n := IntervalDyadic.ofIntervalRat (IntervalRat.singleton (1/n_rat)) prec

    -- 1. Compute Mean: μ = Σx / n
    let sum := sumIntervals x
    let mean := IntervalDyadic.mulRounded sum inv_n prec

    -- 2. Compute Variance: σ² = Σ(x - μ)² / n
    -- Note: x and mean are correlated, so (x - mean) is overestimated
    let diffs := x.map (fun xi => IntervalDyadic.sub xi mean)
    let sq_diffs := diffs.map (fun d => IntervalDyadic.mulRounded d d prec)
    let sum_sq := sumIntervals sq_diffs
    let var := IntervalDyadic.mulRounded sum_sq inv_n prec

    -- 3. Compute Denominator: 1 / sqrt(σ² + ε)
    -- Add epsilon for numerical stability
    let eps_interval := IntervalDyadic.ofIntervalRat
      (IntervalRat.singleton params.epsilon) prec
    let var_eps := IntervalDyadic.add var eps_interval

    -- Sqrt (conservative: assumes non-negative input)
    let std_dev := IntervalDyadic.sqrt var_eps prec

    -- Invert: Since var + eps ≥ eps > 0, the interval is positive
    -- We need to check this and handle division
    let inv_std_dev :=
      let I := std_dev.toIntervalRat
      if h : 0 < I.lo then
        let hnonzero : ¬IntervalRat.containsZero I := fun hcz => not_lt.mpr hcz.1 h
        let Ipos : IntervalRat.IntervalRatNonzero := ⟨I, hnonzero⟩
        IntervalDyadic.ofIntervalRat (IntervalRat.invNonzero Ipos) prec
      else
        -- Fallback: conservative bound derived from epsilon
        IntervalDyadic.ofIntervalRat ⟨0, 1 / params.epsilon + 1, by
          have hpos : (0 : ℚ) < 1 / params.epsilon := by
            exact one_div_pos.mpr params.epsilon_pos
          linarith⟩ prec

    -- 4. Normalize and Scale: ((x - μ) * inv_std) * γ + β
    let normalized := diffs.map (fun d => IntervalDyadic.mulRounded d inv_std_dev prec)

    -- Apply Gamma and Beta element-wise
    let result := List.zipWith3 (fun norm g b =>
      let g_interval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton g) prec
      let b_interval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec
      let scaled := IntervalDyadic.mulRounded norm g_interval prec
      IntervalDyadic.add scaled b_interval
    ) normalized params.gamma params.beta

    result

end LayerNormParams

/-! ### LayerNorm Helper Lemmas -/

/-- Membership lemma for mulRounded -/
theorem mem_mulRounded {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : Int) :
    x * y ∈ IntervalDyadic.mulRounded I J prec := by
  unfold IntervalDyadic.mulRounded
  exact IntervalDyadic.roundOut_contains (IntervalDyadic.mem_mul hx hy) prec

/-- Membership lemma for addRounded -/
theorem mem_addRounded {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : Int) :
    x + y ∈ IntervalDyadic.addRounded I J prec := by
  unfold IntervalDyadic.addRounded
  exact IntervalDyadic.roundOut_contains (IntervalDyadic.mem_add hx hy) prec

/-- Helper for foldl membership -/
private theorem mem_foldl_add {x : ℝ} {acc : IntervalDyadic} {xs : List ℝ} {Is : IntervalVector}
    (hx_acc : x ∈ acc)
    (hlen : xs.length = Is.length)
    (hmem : ∀ i, i < xs.length → xs[i]! ∈ Is[i]!) :
    x + xs.sum ∈ Is.foldl IntervalDyadic.add acc := by
  induction Is generalizing xs acc x with
  | nil =>
    cases xs with
    | nil => simp only [List.sum_nil, add_zero, List.foldl_nil]; exact hx_acc
    | cons => simp at hlen
  | cons I Is' ih =>
    cases xs with
    | nil => simp at hlen
    | cons x' xs' =>
      simp only [List.sum_cons, List.foldl_cons]
      have hlen' : xs'.length = Is'.length := by simp at hlen; exact hlen
      have hx'_mem : x' ∈ I := by
        have := hmem 0 (by simp)
        simp only [List.getElem!_cons_zero] at this
        exact this
      have hmem' : ∀ i, i < xs'.length → xs'[i]! ∈ Is'[i]! := by
        intro i hi
        have := hmem (i + 1) (by simp; omega)
        simp only [List.getElem!_cons_succ] at this
        exact this
      have heq : x + (x' + xs'.sum) = (x + x') + xs'.sum := by ring
      rw [heq]
      have hadd_mem : x + x' ∈ IntervalDyadic.add acc I := IntervalDyadic.mem_add hx_acc hx'_mem
      exact ih hadd_mem hlen' hmem'

/-- Membership lemma for sumIntervals -/
theorem mem_sumIntervals {xs : List ℝ} {Is : IntervalVector}
    (hlen : xs.length = Is.length)
    (hmem : ∀ i, i < xs.length → xs[i]! ∈ Is[i]!) :
    xs.sum ∈ LayerNormParams.sumIntervals Is := by
  cases xs with
  | nil =>
    cases Is with
    | nil =>
      simp only [List.sum_nil, LayerNormParams.sumIntervals]
      have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt 0)
      simp only [Core.Dyadic.toRat_ofInt, Int.cast_zero, Rat.cast_zero] at h
      exact h
    | cons => simp at hlen
  | cons x xs' =>
    cases Is with
    | nil => simp at hlen
    | cons I Is' =>
      simp only [List.sum_cons, LayerNormParams.sumIntervals]
      have hx_mem : x ∈ I := by
        have := hmem 0 (by simp)
        simp only [List.getElem!_cons_zero] at this
        exact this
      have hlen' : xs'.length = Is'.length := by simp at hlen; exact hlen
      have hmem' : ∀ i, i < xs'.length → xs'[i]! ∈ Is'[i]! := by
        intro i hi
        have := hmem (i + 1) (by simp; omega)
        simp only [List.getElem!_cons_succ] at this
        exact this
      exact mem_foldl_add hx_mem hlen' hmem'

/-- Helper: map preserves membership for interval operations.
    Proof: (xs.map f)[i] = f(xs[i]) and (Is.map g)[i] = g(Is[i]),
    so f(xs[i]) ∈ g(Is[i]) follows from hf applied to hmem. -/
theorem mem_map_intervals {f : ℝ → ℝ} {g : IntervalDyadic → IntervalDyadic}
    {xs : List ℝ} {Is : IntervalVector}
    (hlen : xs.length = Is.length)
    (hmem : ∀ i, i < xs.length → xs[i]! ∈ Is[i]!)
    (hf : ∀ x I, x ∈ I → f x ∈ g I) :
    ∀ i, i < xs.length → (xs.map f)[i]! ∈ (Is.map g)[i]! := by
  induction xs generalizing Is with
  | nil =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | cons x xs' ih =>
    match Is with
    | [] => intro i hi; simp at hlen
    | I :: Is' =>
      intro i hi
      cases i with
      | zero =>
        simp only [List.map, List.getElem!_cons_zero]
        apply hf
        have := hmem 0 (by simp)
        simp only [List.getElem!_cons_zero] at this
        exact this
      | succ j =>
        simp only [List.map, List.getElem!_cons_succ]
        have hlen' : xs'.length = Is'.length := by simp at hlen; exact hlen
        have hmem' : ∀ i, i < xs'.length → xs'[i]! ∈ Is'[i]! := fun i hi' => by
          have := hmem (i + 1) (by simp; omega)
          simp only [List.getElem!_cons_succ] at this
          exact this
        have hj : j < xs'.length := by simp at hi; exact hi
        exact @ih Is' hlen' hmem' j hj

/-- zipWith3 length lemma -/
theorem length_zipWith3_min {α β γ δ : Type*} (f : α → β → γ → δ) (as : List α) (bs : List β) (cs : List γ) :
    (List.zipWith3 f as bs cs).length = min (min as.length bs.length) cs.length := by
  induction as generalizing bs cs with
  | nil => simp [List.zipWith3]
  | cons a as' ih =>
    cases bs with
    | nil => simp [List.zipWith3]
    | cons b bs' =>
      cases cs with
      | nil => simp [List.zipWith3]
      | cons c cs' =>
        simp only [List.zipWith3, List.length_cons]
        rw [ih]
        omega

private theorem zipWith3_map_left {α β γ δ ε : Type*} (f : δ → β → γ → ε) (g : α → δ)
    (as : List α) (bs : List β) (cs : List γ) :
    List.zipWith3 f (as.map g) bs cs = List.zipWith3 (fun a b c => f (g a) b c) as bs cs := by
  induction as generalizing bs cs with
  | nil => simp [List.zipWith3]
  | cons a as' ih =>
    cases bs <;> cases cs <;> simp [List.zipWith3, ih]

/-- zipWith3 membership: if corresponding elements satisfy the relation,
    then zipWith3 outputs satisfy the relation. -/
theorem mem_zipWith3 {f : ℝ → ℚ → ℚ → ℝ} {g : IntervalDyadic → ℚ → ℚ → IntervalDyadic}
    {xs : List ℝ} {Is : IntervalVector} {as bs : List ℚ}
    (hlen_xs_Is : xs.length = Is.length)
    (hmem : ∀ i, i < xs.length → xs[i]! ∈ Is[i]!)
    (hf : ∀ x I a b, x ∈ I → f x a b ∈ g I a b) :
    ∀ i, i < (List.zipWith3 f xs as bs).length →
      (List.zipWith3 f xs as bs)[i]! ∈ (List.zipWith3 g Is as bs)[i]! := by
  induction xs generalizing Is as bs with
  | nil =>
    intro i hi
    simp [List.zipWith3] at hi
  | cons x xs' ih =>
    match Is, as, bs with
    | [], _, _ => intro i hi; simp at hlen_xs_Is
    | I :: Is', [], _ =>
      intro i hi
      simp [List.zipWith3] at hi
    | I :: Is', _ :: _, [] =>
      intro i hi
      simp [List.zipWith3] at hi
    | I :: Is', a :: as', b :: bs' =>
      intro i hi
      cases i with
      | zero =>
        simp only [List.zipWith3, List.getElem!_cons_zero]
        apply hf
        have := hmem 0 (by simp)
        simp only [List.getElem!_cons_zero] at this
        exact this
      | succ j =>
        simp only [List.zipWith3, List.getElem!_cons_succ]
        have hlen' : xs'.length = Is'.length := by simp at hlen_xs_Is; exact hlen_xs_Is
        have hmem' : ∀ i, i < xs'.length → xs'[i]! ∈ Is'[i]! := fun i hi' => by
          have := hmem (i + 1) (by simp; omega)
          simp only [List.getElem!_cons_succ] at this
          exact this
        have hj : j < (List.zipWith3 f xs' as' bs').length := by
          simp [List.zipWith3] at hi ⊢
          omega
        exact @ih Is' as' bs' hlen' hmem' j hj

/-- Membership for singleton rational interval -/
theorem mem_ofIntervalRat_singleton (q : ℚ) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    (q : ℝ) ∈ IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) prec :=
  IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton q) prec hprec

/-- The final scale+shift operation: x * γ + β -/
theorem mem_scale_shift {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (g b : ℚ)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x * g + b ∈ IntervalDyadic.add
      (IntervalDyadic.mulRounded I (IntervalDyadic.ofIntervalRat (IntervalRat.singleton g) prec) prec)
      (IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec) := by
  apply IntervalDyadic.mem_add
  · exact mem_mulRounded hx (mem_ofIntervalRat_singleton g prec hprec) prec
  · exact mem_ofIntervalRat_singleton b prec hprec

/-- Membership for subtraction with a fixed second argument -/
theorem mem_sub_const {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (mean : IntervalDyadic) (m : ℝ)
    (hm : m ∈ mean) : x - m ∈ IntervalDyadic.sub I mean :=
  IntervalDyadic.mem_sub hx hm

/-- Squaring preserves membership (via mulRounded) -/
theorem mem_square {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (prec : Int) :
    x * x ∈ IntervalDyadic.mulRounded I I prec :=
  mem_mulRounded hx hx prec

/-! ### LayerNorm Correctness -/

set_option maxHeartbeats 2000000 in
/-- LayerNorm interval is sound (contains true output).
    Note: May be loose due to dependency problem.

    The proof tracks membership through the composition of interval operations:
    1. sum ∈ sumIntervals (by mem_sumIntervals)
    2. mean = sum/n ∈ mean_interval (by mem_mulRounded)
    3. diffs[i] = x[i] - mean ∈ diffs_interval[i] (by mem_sub)
    4. sq_diffs[i] ∈ sq_diffs_interval[i] (by mem_mulRounded)
    5. var ∈ var_interval (by mem_sumIntervals + mem_mulRounded)
    6. var + eps ∈ var_eps_interval (by mem_add)
    7. sqrt(var + eps) ∈ std_dev_interval (by mem_sqrt)
    8. 1/sqrt(...) ∈ inv_std_dev_interval (by mem_invNonzero or fallback)
    9. normalized[i] ∈ normalized_interval[i] (by mem_mulRounded)
    10. result[i] = normalized[i] * gamma[i] + beta[i] ∈ result_interval[i]
        (by mem_mulRounded + mem_add + mem_ofIntervalRat)

    Each step preserves soundness, though intervals may be loose due to
    the dependency problem (correlation between x and mean is lost).

    The proof establishes:
    - All helper lemmas (mem_sumIntervals, mem_mulRounded, mem_map_intervals,
      mem_zipWith3, mem_scale_shift) are fully proven
    - The composition of these lemmas yields soundness

    The remaining complexity is in tracking indices through nested structures
    and handling the dite branch for inv_std_dev. The core mathematical
    argument is complete. -/
theorem mem_layerNorm_forwardInterval {xs : List ℝ} {Is : IntervalVector}
    (params : LayerNormParams)
    (hlen : xs.length = Is.length)
    (hmem : ∀ i, i < xs.length → xs[i]! ∈ Is[i]!)
    (prec : Int)
    (hprec : prec ≤ 0 := by norm_num) :
    let ys := layerNormReal xs params.gamma params.beta params.epsilon
    let Js := params.forwardInterval Is prec
    ys.length ≤ Js.length ∧
    ∀ i, i < ys.length → ys[i]! ∈ Js[i]! := by
  simp only [layerNormReal]
  -- Handle the n = 0 case
  by_cases hn : Is.length = 0
  · -- Empty input: both outputs are empty or trivially satisfy the goal
    dsimp [LayerNormParams.forwardInterval]
    have hxs_empty : xs.length = 0 := by rw [hlen]; exact hn
    have hxs_nil : xs = [] := List.length_eq_zero_iff.mp hxs_empty
    simp [hn, hxs_nil, List.zipWith3]
  · -- Non-empty input case
    dsimp [LayerNormParams.forwardInterval]
    rw [if_neg hn]

    -- Use local let bindings to define values without rewriting hypothesis
    -- Define real intermediate values
    let n := xs.length
    let n_rat : ℚ := (Is.length : ℚ)
    let mean_real := xs.sum / n
    let variance_real := (xs.map (fun xi => (xi - mean_real) * (xi - mean_real))).sum / n
    let denom_real := Real.sqrt (variance_real + params.epsilon)
    let diffs_real := xs.map (fun xi => xi - mean_real)
    let sq_diffs_real := diffs_real.map (fun d => d * d)
    let inv_denom_real := 1 / denom_real
    let normalized_real := diffs_real.map (fun d => d * inv_denom_real)

    -- Define interval intermediate values
    let inv_n := IntervalDyadic.ofIntervalRat (IntervalRat.singleton (1/n_rat)) prec
    let sum_interval := LayerNormParams.sumIntervals Is
    let mean_interval := IntervalDyadic.mulRounded sum_interval inv_n prec
    let diffs_interval := Is.map (fun xi => IntervalDyadic.sub xi mean_interval)
    let sq_diffs_interval := diffs_interval.map (fun d => IntervalDyadic.mulRounded d d prec)
    let sum_sq_interval := LayerNormParams.sumIntervals sq_diffs_interval
    let var_interval := IntervalDyadic.mulRounded sum_sq_interval inv_n prec
    let eps_interval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton params.epsilon) prec
    let var_eps_interval := IntervalDyadic.add var_interval eps_interval
    let std_dev_interval := IntervalDyadic.sqrt var_eps_interval prec
    let I_std := std_dev_interval.toIntervalRat
    let inv_std_dev_interval :=
      if h : 0 < I_std.lo then
        let hnonzero : ¬IntervalRat.containsZero I_std := fun hcz => not_lt.mpr hcz.1 h
        let Ipos : IntervalRat.IntervalRatNonzero := ⟨I_std, hnonzero⟩
        IntervalDyadic.ofIntervalRat (IntervalRat.invNonzero Ipos) prec
      else
        IntervalDyadic.ofIntervalRat ⟨0, 1 / params.epsilon + 1, by
          have hpos : (0 : ℚ) < 1 / params.epsilon := by
            exact one_div_pos.mpr params.epsilon_pos
          linarith⟩ prec
    let normalized_interval := diffs_interval.map (fun d => IntervalDyadic.mulRounded d inv_std_dev_interval prec)

    -- Prove intermediate membership lemmas
    have hsum_mem : xs.sum ∈ sum_interval := mem_sumIntervals hlen hmem

    have h_inv_n_mem : (1 / n : ℝ) ∈ inv_n := by
      have hcast : ((1 / n_rat : ℚ) : ℝ) = (1 / n : ℝ) := by
        simp [n_rat, n, hlen]
      rw [← hcast]
      exact mem_ofIntervalRat_singleton (1/n_rat) prec hprec

    have hmean_mem : mean_real ∈ mean_interval := by
      have heq : mean_real = xs.sum * (1 / n) := by simp only [mean_real]; field_simp
      rw [heq]
      exact mem_mulRounded hsum_mem h_inv_n_mem prec

    -- Prove diffs membership
    have hdiffs_len : diffs_real.length = diffs_interval.length := by
      simp only [diffs_real, diffs_interval, List.length_map, hlen]

    have hdiffs_mem : ∀ i, i < diffs_real.length → diffs_real[i]! ∈ diffs_interval[i]! := by
      intro i hi
      simp only [diffs_real, List.length_map] at hi
      have hi' : i < Is.length := by rw [← hlen]; exact hi
      simp only [diffs_real, diffs_interval]
      have hxi_mem : xs[i]! ∈ Is[i]! := hmem i hi
      -- Need: (xs.map (fun xi => xi - mean_real))[i]! = xs[i]! - mean_real
      -- And: (Is.map (fun xi => xi.sub mean_interval))[i]! = Is[i]!.sub mean_interval
      -- These follow from map indexing, proven via decidable bounds in Mathlib
      have hdiff_eq : (xs.map (fun xi => xi - mean_real))[i]! = xs[i]! - mean_real := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
        simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
      have hint_eq : (Is.map fun xi => IntervalDyadic.sub xi mean_interval)[i]! =
          IntervalDyadic.sub Is[i]! mean_interval := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
        simp only [List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]
      rw [hdiff_eq, hint_eq]
      exact IntervalDyadic.mem_sub hxi_mem hmean_mem

    -- Prove sq_diffs membership
    have hsq_diffs_len : sq_diffs_real.length = sq_diffs_interval.length := by
      simp only [sq_diffs_real, sq_diffs_interval, diffs_real, diffs_interval, List.length_map, hlen]

    have hsq_diffs_mem : ∀ i, i < sq_diffs_real.length → sq_diffs_real[i]! ∈ sq_diffs_interval[i]! := by
      intro i hi
      simp only [sq_diffs_real, List.length_map] at hi
      have hi_diffs : i < diffs_real.length := hi
      have hi_diffs' : i < diffs_interval.length := by rw [← hdiffs_len]; exact hi
      simp only [sq_diffs_real, sq_diffs_interval]
      have hd_mem : diffs_real[i]! ∈ diffs_interval[i]! := hdiffs_mem i hi_diffs
      -- Index extraction
      have hsq_eq : (diffs_real.map (fun d => d * d))[i]! = diffs_real[i]! * diffs_real[i]! := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
        simp only [List.getElem?_eq_getElem hi_diffs, Option.map_some, Option.getD_some]
      have hint_sq_eq : (diffs_interval.map fun d => IntervalDyadic.mulRounded d d prec)[i]! =
          IntervalDyadic.mulRounded diffs_interval[i]! diffs_interval[i]! prec := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
        simp only [List.getElem?_eq_getElem hi_diffs', Option.map_some, Option.getD_some]
      rw [hsq_eq, hint_sq_eq]
      exact mem_mulRounded hd_mem hd_mem prec

    have hsum_sq_mem : sq_diffs_real.sum ∈ sum_sq_interval :=
      mem_sumIntervals hsq_diffs_len hsq_diffs_mem

    have hvar_mem : variance_real ∈ var_interval := by
      have heq : variance_real = sq_diffs_real.sum * (1 / n) := by
        simp only [variance_real, sq_diffs_real, diffs_real, n]
        -- variance_real = (xs.map (fun xi => (xi - mean_real) * (xi - mean_real))).sum / xs.length
        -- sq_diffs_real.sum = (diffs_real.map (fun d => d * d)).sum
        --                   = ((xs.map (fun xi => xi - mean_real)).map (fun d => d * d)).sum
        --                   = (xs.map (fun xi => (xi - mean_real) * (xi - mean_real))).sum
        have hcomp : (xs.map (fun xi => (xi - mean_real) * (xi - mean_real))) =
            (xs.map (fun xi => xi - mean_real)).map (fun d => d * d) := by
          simp [List.map_map, Function.comp]
        rw [hcomp]
        field_simp
      rw [heq]
      exact mem_mulRounded hsum_sq_mem h_inv_n_mem prec

    have heps_mem : (params.epsilon : ℝ) ∈ eps_interval :=
      mem_ofIntervalRat_singleton params.epsilon prec hprec

    have hvar_eps_mem : variance_real + params.epsilon ∈ var_eps_interval :=
      IntervalDyadic.mem_add hvar_mem heps_mem

    have hvar_nonneg : 0 ≤ variance_real := by
      simp only [variance_real, n]
      apply div_nonneg
      · apply List.sum_nonneg
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨xi, _, rfl⟩ := hx
        -- Need to show (xi - mean_real) * (xi - mean_real) ≥ 0
        exact mul_self_nonneg _
      · exact Nat.cast_nonneg xs.length

    -- The variance + epsilon is always positive
    have hvar_eps_pos : 0 < variance_real + params.epsilon := by
      have heps_pos := params.epsilon_pos
      have heps_cast_pos : (0 : ℝ) < (params.epsilon : ℝ) := by exact_mod_cast heps_pos
      linarith

    have hstd_mem : denom_real ∈ std_dev_interval := by
      simp only [denom_real, std_dev_interval]
      exact IntervalDyadic.mem_sqrt' hvar_eps_mem prec

    -- The sqrt of (var + eps) is positive since var + eps > 0
    have hdenom_pos : 0 < denom_real := Real.sqrt_pos.mpr hvar_eps_pos

    -- Prove that the inv_std_dev interval (whichever branch) contains 1/denom_real.
    -- If the interval is provably positive, use invNonzero; otherwise fall back
    -- to a conservative bound derived from epsilon.
    have hinv_std_mem : inv_denom_real ∈ inv_std_dev_interval := by
      by_cases hpos : 0 < I_std.lo
      · -- Positive interval: use invNonzero
        simp only [inv_std_dev_interval, hpos]
        have hnonzero : ¬IntervalRat.containsZero I_std := by
          intro hcz
          exact not_lt.mpr hcz.1 hpos
        let Ipos : IntervalRat.IntervalRatNonzero := ⟨I_std, hnonzero⟩
        have hstd_rat : denom_real ∈ I_std := IntervalDyadic.mem_toIntervalRat.mp hstd_mem
        have hne : denom_real ≠ 0 := ne_of_gt hdenom_pos
        have hinv_rat : inv_denom_real ∈ IntervalRat.invNonzero Ipos := by
          have hinv := IntervalRat.mem_invNonzero (I := Ipos) hstd_rat hne
          simpa [inv_denom_real] using hinv
        exact IntervalDyadic.mem_ofIntervalRat hinv_rat prec hprec
      · -- Fallback: bound by 1/eps + 1
        simp only [inv_std_dev_interval, hpos]
        have hinv_nonneg : 0 ≤ inv_denom_real := by
          have hdenom_nonneg : 0 ≤ denom_real := le_of_lt hdenom_pos
          simpa [inv_denom_real] using (one_div_nonneg.mpr hdenom_nonneg)
        have hsqrt_le : Real.sqrt (params.epsilon : ℝ) ≤ denom_real := by
          have hle : (params.epsilon : ℝ) ≤ variance_real + params.epsilon := by
            linarith [hvar_nonneg]
          simpa [denom_real] using (Real.sqrt_le_sqrt hle)
        have hsqrt_pos : 0 < Real.sqrt (params.epsilon : ℝ) := by
          apply Real.sqrt_pos.mpr
          exact_mod_cast params.epsilon_pos
        have hinv_le : inv_denom_real ≤ 1 / Real.sqrt (params.epsilon : ℝ) := by
          have hle := one_div_le_one_div_of_le hsqrt_pos hsqrt_le
          simpa [inv_denom_real] using hle
        have hsqrt_sq : (Real.sqrt (params.epsilon : ℝ)) ^ 2 = (params.epsilon : ℝ) := by
          have hnonneg : 0 ≤ (params.epsilon : ℝ) := by exact_mod_cast (le_of_lt params.epsilon_pos)
          simpa using (Real.sq_sqrt hnonneg)
        have hinv_sqrt_le : (1 / Real.sqrt (params.epsilon : ℝ) : ℝ) ≤
            (1 / (params.epsilon : ℝ) + 1) := by
          have hineq : (1 / Real.sqrt (params.epsilon : ℝ) : ℝ) ≤
              (1 / (Real.sqrt (params.epsilon : ℝ)) ^ 2 + 1) := by
            set s : ℝ := 1 / Real.sqrt (params.epsilon : ℝ)
            have : s ≤ s ^ 2 + 1 := by nlinarith
            simpa [s] using this
          simpa [hsqrt_sq] using hineq
        have hinv_upper : inv_denom_real ≤ (1 / (params.epsilon : ℝ) + 1) :=
          le_trans hinv_le hinv_sqrt_le
        have hinv_mem : inv_denom_real ∈ (⟨0, 1 / params.epsilon + 1, by
          have hpos' : (0 : ℚ) < 1 / params.epsilon := by
            exact one_div_pos.mpr params.epsilon_pos
          linarith⟩ : IntervalRat) := by
          refine ⟨?_, ?_⟩
          · simpa using hinv_nonneg
          · simpa using hinv_upper
        exact IntervalDyadic.mem_ofIntervalRat hinv_mem prec hprec

    have hnormalized_len : normalized_real.length = normalized_interval.length := by
      simp only [normalized_real, normalized_interval, diffs_real, diffs_interval, List.length_map, hlen]

    have hnormalized_mem : ∀ i, i < normalized_real.length → normalized_real[i]! ∈ normalized_interval[i]! := by
      intro i hi
      simp only [normalized_real, List.length_map] at hi
      have hi_diffs : i < diffs_real.length := hi
      have hi_diffs' : i < diffs_interval.length := by rw [← hdiffs_len]; exact hi
      simp only [normalized_real, normalized_interval]
      have hd_mem : diffs_real[i]! ∈ diffs_interval[i]! := hdiffs_mem i hi_diffs
      -- Index extraction
      have hnorm_eq : (diffs_real.map (fun d => d * inv_denom_real))[i]! = diffs_real[i]! * inv_denom_real := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
        simp only [List.getElem?_eq_getElem hi_diffs, Option.map_some, Option.getD_some]
      have hint_norm_eq : (diffs_interval.map fun d => IntervalDyadic.mulRounded d inv_std_dev_interval prec)[i]! =
          IntervalDyadic.mulRounded diffs_interval[i]! inv_std_dev_interval prec := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
        simp only [List.getElem?_eq_getElem hi_diffs', Option.map_some, Option.getD_some]
      rw [hnorm_eq, hint_norm_eq]
      exact mem_mulRounded hd_mem hinv_std_mem prec

    -- The key: normalized_interval.length = Is.length = xs.length
    have hnorm_int_len : normalized_interval.length = xs.length := by
      simp only [normalized_interval, diffs_interval, List.length_map]
      exact hlen.symm

    -- Final output membership via zipWith3.
    have hresult_mem :
        ∀ i, i < (List.zipWith3 (fun norm (g : ℚ) (b : ℚ) => norm * (g : ℝ) + (b : ℝ))
          normalized_real params.gamma params.beta).length →
          (List.zipWith3 (fun norm (g : ℚ) (b : ℚ) => norm * (g : ℝ) + (b : ℝ))
            normalized_real params.gamma params.beta)[i]! ∈
          (List.zipWith3 (fun norm g b =>
            IntervalDyadic.add
              (IntervalDyadic.mulRounded norm (IntervalDyadic.ofIntervalRat (IntervalRat.singleton g) prec) prec)
              (IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec))
            normalized_interval params.gamma params.beta)[i]! := by
      exact mem_zipWith3 hnormalized_len hnormalized_mem
        (fun x I g b hx => mem_scale_shift hx g b prec hprec)

    have hys_eq :
        List.zipWith3 (fun xi (g : ℚ) (b : ℚ) => ((xi - mean_real) / denom_real) * (g : ℝ) + (b : ℝ))
          xs params.gamma params.beta =
        List.zipWith3 (fun norm (g : ℚ) (b : ℚ) => norm * (g : ℝ) + (b : ℝ))
          normalized_real params.gamma params.beta := by
      have hmap :
          List.zipWith3 (fun norm (g : ℚ) (b : ℚ) => norm * (g : ℝ) + (b : ℝ))
            normalized_real params.gamma params.beta =
          List.zipWith3 (fun xi (g : ℚ) (b : ℚ) =>
            ((xi - mean_real) * inv_denom_real) * (g : ℝ) + (b : ℝ))
            xs params.gamma params.beta := by
        simp [normalized_real, diffs_real, List.map_map, Function.comp, zipWith3_map_left]
      have hdiv :
          List.zipWith3 (fun xi (g : ℚ) (b : ℚ) =>
            ((xi - mean_real) / denom_real) * (g : ℝ) + (b : ℝ))
            xs params.gamma params.beta =
          List.zipWith3 (fun xi (g : ℚ) (b : ℚ) =>
            ((xi - mean_real) * inv_denom_real) * (g : ℝ) + (b : ℝ))
            xs params.gamma params.beta := by
        simp [inv_denom_real, div_eq_mul_inv, mul_assoc]
      exact hdiv.trans hmap.symm

    have hys_eq' :
        List.zipWith3 (fun xi (g : ℚ) (b : ℚ) =>
          ((xi - xs.sum / ↑xs.length) /
              Real.sqrt
                ((xs.map (fun xi => (xi - xs.sum / ↑xs.length) * (xi - xs.sum / ↑xs.length))).sum / ↑xs.length +
                  ↑params.epsilon)) * (g : ℝ) + (b : ℝ))
          xs params.gamma params.beta =
        List.zipWith3 (fun norm (g : ℚ) (b : ℚ) => norm * (g : ℝ) + (b : ℝ))
          normalized_real params.gamma params.beta := by
      simpa [mean_real, variance_real, denom_real, n] using hys_eq

    constructor
    · -- Lengths agree (same min length after normalization)
      simp only [length_zipWith3_min, List.length_map, hlen]
      exact le_rfl
    ·
      intro i hi
      have hi' := hi
      have hlen_eq := congrArg List.length hys_eq'
      rw [hlen_eq] at hi'
      have hmem' := hresult_mem i hi'
      rw [hys_eq']
      exact hmem'

/-! ### Transformer Block Structure -/

/-- A feed-forward network block (MLP) in a Transformer -/
structure FFNBlock where
  /-- First linear layer (hidden expansion) -/
  linear1 : Layer
  /-- Second linear layer (projection back) -/
  linear2 : Layer
  /-- Dimensions match: linear1.outputDim = linear2.inputDim -/
  dims_match : linear1.outputDim = linear2.inputDim
  deriving Repr

namespace FFNBlock

/-- Real-valued forward pass: Linear -> GELU -> Linear -/
noncomputable def forwardReal (blk : FFNBlock) (x : List ℝ) : List ℝ :=
  let hidden := blk.linear1.forwardReal x
  let activated := hidden.map Real.gelu
  blk.linear2.forwardReal activated

/-- Interval forward pass: Linear -> GELU -> Linear -/
def forwardInterval (blk : FFNBlock) (x : IntervalVector) (prec : Int := -53) : IntervalVector :=
  let hidden := blk.linear1.forwardInterval x prec
  let activated := geluVector hidden prec
  blk.linear2.forwardInterval activated prec

end FFNBlock

/-- A Transformer encoder block (simplified, without attention) -/
structure TransformerBlock where
  /-- Pre-FFN layer normalization -/
  ln1 : LayerNormParams
  /-- Feed-forward network -/
  ffn : FFNBlock
  /-- Post-FFN layer normalization -/
  ln2 : LayerNormParams
  deriving Repr

namespace TransformerBlock

/-- Forward pass through a Transformer block (without attention).
    Computes: LN2(x + FFN(LN1(x)))

    Note: This is a simplified version without self-attention.
    For full attention, see ML/Optimized/MatrixNetwork.lean -/
def forwardInterval (blk : TransformerBlock) (x : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  -- Pre-norm
  let x_norm := blk.ln1.forwardInterval x prec

  -- Feed-forward with GELU
  let ff_out := blk.ffn.forwardInterval x_norm prec

  -- Residual connection: x + ff_out
  let residual := IntervalVector.add x ff_out

  -- Post-norm
  blk.ln2.forwardInterval residual prec

end TransformerBlock

/-! ### ReLU Alternative (for comparison) -/

/-- Standard ReLU-based MLP forward (using existing relu) -/
def reluMLPInterval (linear1 linear2 : Layer) (x : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  let hidden := linear1.forwardInterval x prec  -- includes ReLU
  linear2.forwardInterval hidden prec

end LeanCert.ML.Transformer
