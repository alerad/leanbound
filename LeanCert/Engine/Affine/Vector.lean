/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Affine.Transcendental

/-!
# Affine Arithmetic: Vector Operations

This file provides vectorized affine operations for efficient neural network
verification. The key insight is that **shared noise symbols** track correlations
across vector elements.

## The Dependency Problem in Vectors

Consider LayerNorm: `y_i = (x_i - μ) / σ` where `μ = mean(x)`.

With standard interval arithmetic:
- `x_i ∈ [0.9, 1.1]` for all i
- `μ ∈ [0.9, 1.1]`
- `x_i - μ ∈ [-0.2, 0.2]` (WRONG! Should be nearly 0)

With Affine Arithmetic:
- `x_i = 1.0 + 0.1·ε_i` (each element has its own noise)
- `μ = 1.0 + 0.1·(ε_1 + ... + ε_n)/n`
- `x_i - μ = 0.1·ε_i - 0.1·(ε_1 + ... + ε_n)/n` (TIGHT!)

## Main definitions

* `AffineVector` - Vector of affine forms with shared noise symbols
* `AffineVector.mean` - Compute mean preserving correlations
* `AffineVector.sub` - Element-wise subtraction
* `AffineVector.layerNorm` - LayerNorm with proper dependency tracking
-/

namespace LeanCert.Engine.Affine

open LeanCert.Core

/-! ## Affine Vector -/

/-- A vector of affine forms sharing the same noise symbol space.

    All elements should have the same `coeffs.length` (number of noise symbols).
    This ensures correlations are properly tracked. -/
abbrev AffineVector := List AffineForm

namespace AffineVector

/-- Create an affine vector from intervals, assigning each a unique noise symbol.

    If intervals = [I₀, I₁, I₂], creates:
    - x₀ = mid(I₀) + rad(I₀)·ε₀
    - x₁ = mid(I₁) + rad(I₁)·ε₁
    - x₂ = mid(I₂) + rad(I₂)·ε₂
-/
def ofIntervals (Is : List IntervalRat) : AffineVector :=
  let n := Is.length
  Is.zipIdx.map (fun ⟨I, idx⟩ => AffineForm.ofInterval I idx n)

/-- Convert back to interval bounds -/
def toIntervals (v : AffineVector) : List IntervalRat :=
  v.map AffineForm.toInterval

/-! ## Linear Operations -/

/-- Element-wise addition -/
def add (v w : AffineVector) : AffineVector :=
  List.zipWith AffineForm.add v w

/-- Element-wise subtraction -/
def sub (v w : AffineVector) : AffineVector :=
  List.zipWith AffineForm.sub v w

/-- Element-wise negation -/
def neg (v : AffineVector) : AffineVector :=
  v.map AffineForm.neg

/-- Scalar multiplication -/
def scale (q : ℚ) (v : AffineVector) : AffineVector :=
  v.map (AffineForm.scale q)

/-! ## Aggregation Operations -/

/-- Sum of all elements (preserves correlations!) -/
def sum (v : AffineVector) : AffineForm :=
  v.foldl AffineForm.add AffineForm.zero

/-- Mean of all elements -/
def mean (v : AffineVector) : AffineForm :=
  if v.isEmpty then AffineForm.zero
  else AffineForm.scale (1 / v.length) (sum v)

/-- Dot product of two vectors -/
def dot (v w : AffineVector) : AffineForm :=
  sum (List.zipWith AffineForm.mul v w)

/-! ## LayerNorm Components -/

/-- Compute (x - μ) for each element, where μ = mean(x).

    This is where Affine Arithmetic shines: the subtraction properly
    cancels the correlated parts, giving tight bounds. -/
def centered (v : AffineVector) : AffineVector :=
  let μ := mean v
  v.map (fun xi => AffineForm.sub xi μ)

/-- Compute variance: mean((x - μ)²) -/
def variance (v : AffineVector) : AffineForm :=
  let diffs := centered v
  let sq_diffs := diffs.map AffineForm.sq
  mean sq_diffs

/-- Layer Normalization: (x - μ) / √(σ² + ε) * γ + β

    Parameters:
    - v: input vector (affine)
    - gamma: scale parameters
    - beta: shift parameters
    - eps: numerical stability constant
-/
def layerNorm (v : AffineVector) (gamma beta : List ℚ) (eps : ℚ) : AffineVector :=
  -- 1. Center: x - μ
  let centered_v := centered v

  -- 2. Variance: mean((x - μ)²)
  let var := variance v

  -- 3. Add epsilon and sqrt
  let var_eps := AffineForm.add var (AffineForm.const eps)
  let std := AffineForm.sqrt var_eps

  -- 4. Invert: 1/√(σ² + ε)
  let inv_std := AffineForm.inv std

  -- 5. Normalize and scale
  List.zipWith3 (fun xi g b =>
    let normalized := AffineForm.mul xi inv_std
    let scaled := AffineForm.scale g normalized
    AffineForm.add scaled (AffineForm.const b)
  ) centered_v gamma beta

/-! ## Softmax Components -/

/-- Compute exp(x_i - max(x)) for numerical stability -/
def shiftedExp (v : AffineVector) : AffineVector :=
  let max_c0 := v.foldl (fun m af => max m af.c0) (-10^30)
  let shift := AffineForm.const max_c0
  v.map (fun xi =>
    let shifted := AffineForm.sub xi shift
    AffineForm.exp shifted)

/-- Softmax using algebraic cancellation.

    softmax(x)_i = exp(x_i) / Σ exp(x_j)
                 = 1 / Σ exp(x_j - x_i)

    By computing differences first, we track correlations better.
-/
def softmax (v : AffineVector) : AffineVector :=
  v.map (fun xi =>
    -- Compute x_j - x_i for all j
    let diffs := v.map (fun xj => AffineForm.sub xj xi)
    -- Compute exp(x_j - x_i)
    let exps := diffs.map (fun d => AffineForm.exp d)
    -- Sum
    let sum_exp := sum exps
    -- Invert: 1 / sum
    AffineForm.inv sum_exp)

/-! ## Attention Components -/

/-- Scaled dot-product attention scores for a single query.

    Computes softmax(q · K^T / √d_k) where K is a list of key vectors.
-/
def attentionWeights (q : AffineVector) (K : List AffineVector)
    (inv_sqrt_dk : ℚ) : AffineVector :=
  -- 1. Compute q · k_i for each key
  let scores := K.map (fun ki =>
    let raw_score := dot q ki
    AffineForm.scale inv_sqrt_dk raw_score)

  -- 2. Apply softmax
  softmax scores

/-- Apply attention weights to values -/
def applyAttention (weights : AffineVector) (V : List AffineVector) : AffineVector :=
  if V.isEmpty then []
  else
    let d_v := V.head!.length
    -- Initialize with zeros
    let zero := List.replicate d_v AffineForm.zero
    -- Weighted sum
    let weighted := List.zipWith (fun w v_row =>
      v_row.map (AffineForm.scale w.c0)  -- Simplified: use center value
    ) weights V
    weighted.foldl add zero

/-! ## GELU -/

/-- GELU activation: x · Φ(x) ≈ 0.5 · x · (1 + tanh(√(2/π) · (x + 0.044715 · x³)))

    Using affine arithmetic preserves correlations in x · tanh(f(x)).
-/
def gelu (v : AffineVector) : AffineVector :=
  let c1 : ℚ := 797885 / 1000000  -- ≈ √(2/π)
  let c2 : ℚ := 44715 / 1000000   -- 0.044715
  v.map (fun x =>
    -- x³
    let x2 := AffineForm.sq x
    let x3 := AffineForm.mul x2 x
    -- x + c2 · x³
    let inner := AffineForm.add x (AffineForm.scale c2 x3)
    -- c1 · inner
    let arg := AffineForm.scale c1 inner
    -- tanh(arg)
    let tanh_arg := AffineForm.tanh arg
    -- 1 + tanh(arg)
    let one_plus := AffineForm.add (AffineForm.const 1) tanh_arg
    -- 0.5 · x · (1 + tanh(arg))
    let half_x := AffineForm.scale (1/2) x
    AffineForm.mul half_x one_plus)

/-! ## Soundness -/

/-- Membership for affine vectors -/
def mem (v_real : List ℝ) (v : AffineVector) (eps : AffineForm.NoiseAssignment) : Prop :=
  v_real.length = v.length ∧
  ∀ i (hi_v : i < v.length) (hi_r : i < v_real.length),
    AffineForm.mem_affine v[i] eps v_real[i]

/-- Zero affine form represents 0 -/
private theorem mem_zero (eps : AffineForm.NoiseAssignment) :
    AffineForm.mem_affine AffineForm.zero eps 0 := by
  use 0
  constructor
  · simp [AffineForm.zero, AffineForm.const]
  · simp [AffineForm.evalLinear, AffineForm.linearSum, AffineForm.zero, AffineForm.const]

/-- Helper: linearSum of scaled coefficients equals scaled linearSum -/
private theorem linearSum_map_scale (q : ℚ) (coeffs : List ℚ) (eps : AffineForm.NoiseAssignment) :
    AffineForm.linearSum (coeffs.map (q * ·)) eps = (q : ℝ) * AffineForm.linearSum coeffs eps := by
  simp only [AffineForm.linearSum]
  induction coeffs generalizing eps with
  | nil => simp [List.zipWith]
  | cons c cs ih =>
    cases eps with
    | nil => simp [List.zipWith]
    | cons e es =>
      simp only [List.map_cons, List.zipWith, List.sum_cons]
      rw [ih es]
      push_cast
      ring

/-- Scale is sound -/
private theorem mem_scale (q : ℚ) {a : AffineForm} {eps : AffineForm.NoiseAssignment} {x : ℝ}
    (ha : AffineForm.mem_affine a eps x) :
    AffineForm.mem_affine (AffineForm.scale q a) eps ((q : ℝ) * x) := by
  obtain ⟨err, herr, heq⟩ := ha
  use (q : ℝ) * err
  constructor
  · -- |(q : ℝ) * err| ≤ |q| * a.r
    calc |(q : ℝ) * err| = |(q : ℝ)| * |err| := abs_mul _ _
      _ ≤ |(q : ℝ)| * (a.r : ℝ) := by nlinarith [abs_nonneg (q : ℝ)]
      _ = ((|q| * a.r : ℚ) : ℝ) := by push_cast; rw [← Rat.cast_abs]
  · -- (q : ℝ) * x = evalLinear (scale q a) eps + (q : ℝ) * err
    simp only [AffineForm.evalLinear, AffineForm.scale, linearSum_map_scale]
    rw [heq]
    simp only [AffineForm.evalLinear]
    push_cast
    ring

/-- Helper: foldl add preserves membership -/
private theorem mem_foldl_add {acc : AffineForm} {acc_r : ℝ}
    {v : AffineVector} {v_real : List ℝ}
    (eps : AffineForm.NoiseAssignment)
    (hacc : AffineForm.mem_affine acc eps acc_r)
    (hlen : v_real.length = v.length)
    (hmem : ∀ i (hi_v : i < v.length) (hi_r : i < v_real.length),
            AffineForm.mem_affine v[i] eps v_real[i]) :
    AffineForm.mem_affine (v.foldl AffineForm.add acc) eps (acc_r + v_real.sum) := by
  induction v generalizing acc acc_r v_real with
  | nil =>
    cases v_real with
    | nil =>
      simp only [List.foldl_nil, List.sum_nil, add_zero]
      exact hacc
    | cons h t => simp at hlen
  | cons h t ih =>
    cases v_real with
    | nil => simp at hlen
    | cons h_r t_r =>
      simp only [List.foldl_cons, List.sum_cons]
      simp only [List.length_cons, add_left_inj] at hlen
      -- Apply IH with acc' = add acc h, acc_r' = acc_r + h_r
      have hmem_h : AffineForm.mem_affine h eps h_r := by
        have := hmem 0 (by simp) (by simp)
        simp at this
        exact this
      have hacc' := AffineForm.mem_add hacc hmem_h
      have hmem' : ∀ i (hi_v : i < t.length) (hi_r : i < t_r.length),
                   AffineForm.mem_affine t[i] eps t_r[i] := by
        intro i hi_v hi_r
        have := hmem (i + 1) (by simp; omega) (by simp; omega)
        simp at this
        exact this
      have ih_result := ih hacc' hlen hmem'
      -- Need: (acc_r + h_r) + t_r.sum = acc_r + (h_r + t_r.sum)
      convert ih_result using 1
      ring

/-- Sum is sound -/
theorem mem_sum {v_real : List ℝ} {v : AffineVector} {eps : AffineForm.NoiseAssignment}
    (_hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps) :
    AffineForm.mem_affine (sum v) eps v_real.sum := by
  simp only [sum]
  have := mem_foldl_add eps (mem_zero eps) hmem.1 hmem.2
  simp at this
  exact this

/-- Mean is sound -/
theorem mem_mean {v_real : List ℝ} {v : AffineVector} {eps : AffineForm.NoiseAssignment}
    (hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps)
    (hne : ¬v.isEmpty) :
    AffineForm.mem_affine (mean v) eps (v_real.sum / v_real.length) := by
  simp only [mean, hne, Bool.false_eq_true, ↓reduceIte, one_div]
  -- mean v = scale (1/v.length) (sum v)
  -- By mem_sum, sum v represents v_real.sum
  have hsum := mem_sum hvalid hmem
  -- By mem_scale, scale (1/v.length) (sum v) represents (1/v.length) * v_real.sum
  have hscale := mem_scale (1 / v.length) hsum
  -- (1/v.length) * v_real.sum = v_real.sum / v_real.length (when lengths equal)
  have hlen := hmem.1
  have hne' : v.length ≠ 0 := by
    intro h
    have : v.isEmpty := List.isEmpty_iff.mpr (List.length_eq_zero_iff.mp h)
    exact hne this
  have hne_real : (v.length : ℝ) ≠ 0 := by exact_mod_cast hne'
  convert hscale using 1
  . simp
  rw [hlen]
  push_cast
  field_simp [hne_real]

/-- Centered is sound: x - mean(x) -/
theorem mem_centered {v_real : List ℝ} {v : AffineVector} {eps : AffineForm.NoiseAssignment}
    (hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps) :
    let μ := v_real.sum / v_real.length
    let centered_real := v_real.map (· - μ)
    mem centered_real (centered v) eps := by
  simp only [mem, centered]
  constructor
  · -- Length: centered_real.length = (centered v).length
    simp only [List.length_map]
    exact hmem.1
  · -- Element-wise: for all i, (centered v)[i] represents centered_real[i]
    intro i hi_v hi_r
    simp only [List.length_map] at hi_v hi_r
    simp only [List.getElem_map]
    -- Need: mem_affine (sub v[i] (mean v)) eps (v_real[i] - μ)
    have hmem_i : AffineForm.mem_affine v[i] eps v_real[i] := hmem.2 i hi_v hi_r
    -- Handle empty vs non-empty case
    have hne : ¬v.isEmpty := by
      intro h
      have hv_nil := List.isEmpty_iff.mp h
      simp only [hv_nil, List.length_nil] at hi_v
      exact Nat.not_lt_zero i hi_v
    have hmem_mean : AffineForm.mem_affine (mean v) eps (v_real.sum / v_real.length) :=
      mem_mean hvalid hmem hne
    exact AffineForm.mem_sub hmem_i hmem_mean

/-- Squared centered values are sound -/
private theorem mem_sq_centered {v_real : List ℝ} {v : AffineVector}
    {eps : AffineForm.NoiseAssignment}
    (hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps) :
    let μ := v_real.sum / v_real.length
    let sq_diffs_real := v_real.map (fun x => (x - μ) * (x - μ))
    mem sq_diffs_real ((centered v).map AffineForm.sq) eps := by
  simp only [mem]
  constructor
  · -- Length: sq_diffs_real.length = ((centered v).map sq).length
    simp only [List.length_map, centered]
    exact hmem.1
  · -- Element-wise
    intro i hi_v hi_r
    simp only [List.length_map] at hi_v hi_r
    simp only [List.getElem_map]
    -- Get membership for centered value
    have hcentered := mem_centered hvalid hmem
    -- hi_v : i < (centered v).length
    -- hi_r : i < v_real.length
    have hi_c : i < (centered v).length := hi_v
    have hi_cr : i < (v_real.map (· - v_real.sum / v_real.length)).length := by simp; exact hi_r
    have hmem_ci : AffineForm.mem_affine (centered v)[i] eps ((v_real.map (· - v_real.sum / v_real.length))[i]) :=
      hcentered.2 i hi_c hi_cr
    simp only [List.getElem_map] at hmem_ci
    -- Apply mem_sq
    exact AffineForm.mem_sq hvalid hmem_ci

/-- Variance is sound -/
theorem mem_variance {v_real : List ℝ} {v : AffineVector} {eps : AffineForm.NoiseAssignment}
    (hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps)
    (hne : ¬v.isEmpty) :
    let μ := v_real.sum / v_real.length
    let var_real := (v_real.map (fun x => (x - μ) * (x - μ))).sum / v_real.length
    AffineForm.mem_affine (variance v) eps var_real := by
  simp only [variance]
  -- variance v = mean (centered v).map sq
  -- var_real = mean of squared differences

  -- Get membership for squared centered values
  have hsq_mem := mem_sq_centered hvalid hmem

  -- Show that (centered v).map sq is non-empty
  have hne_sq : ¬((centered v).map AffineForm.sq).isEmpty := by
    simp only [List.isEmpty_iff, List.map_eq_nil_iff, centered] at hne ⊢
    exact hne

  -- Apply mem_mean
  have hmean := mem_mean hvalid hsq_mem hne_sq
  -- hmean : (sq_diffs_real.sum / sq_diffs_real.length)
  -- goal: (v_real.map ...).sum / v_real.length
  -- The types match exactly, just need to align v_real.length with v.length
  have hlen : v_real.length = v.length := hmem.1
  -- Rewrite v.length -> v_real.length in hmean
  simp only [List.length_map] at hmean
  exact hmean

/-- Helper theorem for layerNorm output element -/
private theorem mem_layerNorm_elem {xi_c : AffineForm} {inv_std : AffineForm}
    {xi_real inv_std_real : ℝ} {g b : ℚ}
    {eps : AffineForm.NoiseAssignment}
    (hvalid : AffineForm.validNoise eps)
    (hxi : AffineForm.mem_affine xi_c eps xi_real)
    (hinv : AffineForm.mem_affine inv_std eps inv_std_real) :
    let output := AffineForm.add (AffineForm.scale g (AffineForm.mul xi_c inv_std)) (AffineForm.const b)
    AffineForm.mem_affine output eps (xi_real * inv_std_real * g + b) := by
  -- mul is sound
  have hmul := AffineForm.mem_mul hvalid hxi hinv
  -- scale is sound
  have hscale := AffineForm.mem_scale g hmul
  -- add const is sound
  have hadd := AffineForm.mem_add hscale (AffineForm.mem_const b eps)
  -- Simplify to match goal
  simp only at hadd ⊢
  convert hadd using 1
  ring

/-- Helper: length of zipWith3 -/
private theorem length_zipWith3_aux {α β γ δ : Type*} (f : α → β → γ → δ)
    (as : List α) (bs : List β) (cs : List γ) :
    (List.zipWith3 f as bs cs).length = min (min as.length bs.length) cs.length := by
  induction as generalizing bs cs with
  | nil => simp [List.zipWith3]
  | cons a as ih =>
    cases bs with
    | nil => simp [List.zipWith3]
    | cons b bs =>
      cases cs with
      | nil => simp [List.zipWith3]
      | cons c cs =>
        simp only [List.zipWith3, List.length_cons, ih]
        omega

/-- Helper: access element of zipWith3 -/
private theorem getElem_zipWith3_aux {α β γ δ : Type*} (f : α → β → γ → δ)
    (as : List α) (bs : List β) (cs : List γ) (i : Nat)
    (hi_a : i < as.length) (hi_b : i < bs.length) (hi_c : i < cs.length) :
    (List.zipWith3 f as bs cs)[i]'(by rw [length_zipWith3_aux]; omega) =
      f (as[i]'hi_a) (bs[i]'hi_b) (cs[i]'hi_c) := by
  induction as generalizing bs cs i with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hi_a
  | cons a as ih =>
    cases bs with
    | nil => simp only [List.length_nil, Nat.not_lt_zero] at hi_b
    | cons b bs =>
      cases cs with
      | nil => simp only [List.length_nil, Nat.not_lt_zero] at hi_c
      | cons c cs =>
        cases i with
        | zero => simp only [List.zipWith3, List.getElem_cons_zero]
        | succ j =>
          simp only [List.zipWith3, List.getElem_cons_succ]
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi_a hi_b hi_c
          exact ih bs cs j hi_a hi_b hi_c

/-- Helper: do-notation coercion list has same length for rationals to reals.
    (do let a ← xs; pure (a : ℝ)) = xs.map (↑·) for lists, so length is preserved.
    Technical proof about list monad desugaring. -/
private theorem length_do_pure_rat_real (xs : List ℚ) :
    (do let a ← xs; pure (a : ℝ)).length = xs.length := by
  -- do let a ← xs; pure (↑a) desugars to xs.flatMap (fun a => pure ↑a)
  -- which equals xs.flatMap (fun a => [↑a]) for the List monad
  -- This has the same length as xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- Goal: ((x :: xs).flatMap (fun a => [↑a])).length = (x :: xs).length
    simp only [List.length_cons]
    exact congrArg Nat.succ ih

/-- Helper: element access in coerced list equals coerced element. -/
private theorem getElem_do_pure_rat_real (xs : List ℚ) (i : Nat) (hi : i < xs.length)
    (hi' : i < (do let a ← xs; pure (a : ℝ)).length) :
    (do let a ← xs; pure (a : ℝ))[i]'hi' = (xs[i]'hi : ℝ) := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      -- LHS: (do let a ← x :: xs; pure ↑a)[0] = ↑x :: (do let a ← xs; pure ↑a)[0] = ↑x
      -- RHS: (x :: xs)[0] = x
      rfl
    | succ j =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      have hi'_j : j < (do let a ← xs; pure (a : ℝ)).length := by
        simp only [length_do_pure_rat_real]; exact hi
      -- LHS: (do let a ← x :: xs; pure ↑a)[j+1] = (↑x :: (do let a ← xs; pure ↑a))[j+1]
      --    = (do let a ← xs; pure ↑a)[j]
      -- RHS: (x :: xs)[j+1] = xs[j]
      simp only [List.getElem_cons_succ]
      exact ih j hi hi'_j

/-- Helper: getElem result is independent of the proof of bounds. -/
private theorem getElem_proof_irrel {α : Type*} (xs : List α) (i : Nat)
    (h1 h2 : i < xs.length) : xs[i]'h1 = xs[i]'h2 := by
  have h1' : xs[i]? = some (xs[i]'h1) := List.getElem?_eq_getElem h1
  have h2' : xs[i]? = some (xs[i]'h2) := List.getElem?_eq_getElem h2
  exact Option.some.inj (h1'.symm.trans h2')

/-- LayerNorm is sound for the complete operation.

    Note: This theorem requires additional hypotheses that would typically
    be verified at the call site:
    - The variance + epsilon must be positive (guaranteed by epsilon > 0)
    - Length constraints for gamma and beta
    - The affine form for var + eps must have positive lower bound for inv

    The proof composition uses:
    1. mem_centered for centering
    2. mem_variance for variance
    3. mem_add for adding epsilon
    4. mem_sqrt for standard deviation
    5. mem_inv for reciprocal
    6. mem_layerNorm_elem for each output element
-/
theorem mem_layerNorm {v_real : List ℝ} {v : AffineVector}
    {eps : AffineForm.NoiseAssignment}
    (gamma beta : List ℚ)
    (epsilon : ℚ)
    (heps_pos : 0 < epsilon)
    (hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps)
    (hne : ¬v.isEmpty)
    -- Additional hypotheses needed for sqrt and inv
    (hlen_eps : eps.length = (variance v |>.add (AffineForm.const epsilon)).coeffs.length)
    (hlen_sqrt : eps.length = ((variance v).add (AffineForm.const epsilon) |> AffineForm.sqrt).coeffs.length)
    (hsqrt_pos : 0 < ((variance v).add (AffineForm.const epsilon) |> AffineForm.sqrt).toInterval.lo) :
    let μ := v_real.sum / v_real.length
    let variance_real := (v_real.map (fun x => (x - μ) * (x - μ))).sum / v_real.length
    let std_real := Real.sqrt (variance_real + epsilon)
    let inv_std_real := 1 / std_real
    let output_real :=
      List.zipWith3 (fun xi (g : ℚ) (b : ℚ) => (xi - μ) * inv_std_real * (g : ℝ) + b)
        v_real gamma beta
    mem output_real (layerNorm v gamma beta epsilon) eps := by
  simp only [layerNorm]

  -- Step 1: Centered values
  have hcentered := mem_centered hvalid hmem

  -- Step 2: Variance
  have hvar := mem_variance hvalid hmem hne

  -- Step 3: Variance + epsilon
  have hvar_eps := AffineForm.mem_add hvar (AffineForm.mem_const epsilon eps)

  -- Step 4: Standard deviation (sqrt)
  -- variance_real ≥ 0 (mean of squares) and epsilon > 0, so variance_real + epsilon > 0
  have hvar_nonneg : 0 ≤ (v_real.map (fun x => (x - v_real.sum / ↑v_real.length) *
                          (x - v_real.sum / ↑v_real.length))).sum / ↑v_real.length := by
    apply div_nonneg
    · apply List.sum_nonneg
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      nlinarith
    · exact Nat.cast_nonneg _

  have hpos : 0 ≤ (v_real.map (fun x => (x - (v_real.sum / ↑v_real.length)) * (x - (v_real.sum / ↑v_real.length)))).sum /
               ↑v_real.length + (epsilon : ℝ) := by
    have heps_pos' : (0 : ℝ) < epsilon := Rat.cast_pos.mpr heps_pos
    linarith

  have hstd := AffineForm.mem_sqrt hvalid hlen_eps hvar_eps hpos

  -- Step 5: Inverse (1/std)
  -- Need to show std > 0 and interval is positive
  have hstd_pos : 0 < Real.sqrt ((v_real.map (fun x => (x - v_real.sum / ↑v_real.length) *
                   (x - v_real.sum / ↑v_real.length))).sum / ↑v_real.length + ↑epsilon) := by
    apply Real.sqrt_pos_of_pos
    have heps_pos' : (0 : ℝ) < epsilon := Rat.cast_pos.mpr heps_pos
    linarith

  have hinv := AffineForm.mem_inv hvalid hlen_sqrt hstd hstd_pos hsqrt_pos

  -- Step 6: Combine for each element using zipWith3

  -- Define abbreviations
  let centered_v := centered v
  let inv_std := AffineForm.inv (AffineForm.sqrt ((variance v).add (AffineForm.const epsilon)))

  -- Helper: the length equality
  have hlen_v : v_real.length = v.length := hmem.1

  simp only [mem, centered]

  constructor
  · -- Length equality for zipWith3
    -- The coercion ℚ → ℝ for list elements preserves length
    simp only [length_zipWith3_aux, List.length_map, hlen_v]
  · -- Element-wise membership
    intro i hi_affine hi_real

    -- Normalize length bounds to min-forms for arithmetic reasoning.
    have hi_affine_min : i < min (min v.length gamma.length) beta.length := by
      simpa [length_zipWith3_aux, List.length_map] using hi_affine
    have hi_real_min : i < min (min v_real.length gamma.length) beta.length := by
      simpa [length_zipWith3_aux] using hi_real

    -- Derive index bounds for component lists
    have hi_v : i < v.length := by
      have h1 : i < min v.length gamma.length :=
        lt_of_lt_of_le hi_affine_min (Nat.min_le_left _ _)
      exact lt_of_lt_of_le h1 (Nat.min_le_left _ _)
    have hi_vreal : i < v_real.length := by
      have h1 : i < min v_real.length gamma.length :=
        lt_of_lt_of_le hi_real_min (Nat.min_le_left _ _)
      exact lt_of_lt_of_le h1 (Nat.min_le_left _ _)
    have hi_gamma : i < gamma.length := by
      have h1 : i < min v.length gamma.length :=
        lt_of_lt_of_le hi_affine_min (Nat.min_le_left _ _)
      exact lt_of_lt_of_le h1 (Nat.min_le_right _ _)
    have hi_beta : i < beta.length := by
      exact lt_of_lt_of_le hi_affine_min (Nat.min_le_right _ _)
    have hi_centered : i < (v.map (fun xi => xi.sub v.mean)).length := by
      simpa [List.length_map] using hi_v

    -- Get membership for centered value at index i
    have hi_centered' : i < (v_real.map (· - v_real.sum / ↑v_real.length)).length := by
      simpa [List.length_map] using hi_vreal
    have hcentered_i := hcentered.2 i hi_centered hi_centered'
    simp only [List.getElem_map] at hcentered_i

    -- Apply mem_layerNorm_elem with the centered value and inverse standard deviation
    have helem := mem_layerNorm_elem (g := gamma[i]) (b := beta[i]) hvalid hcentered_i hinv

    have affine_eq := getElem_zipWith3_aux (fun xi g b =>
        AffineForm.add (AffineForm.scale g (AffineForm.mul xi inv_std)) (AffineForm.const b))
        (v.map (fun xi => xi.sub v.mean)) gamma beta i hi_centered hi_gamma hi_beta

    -- The proof follows from:
    -- 1. Affine output[i] = add (scale gamma[i] (mul centered[i] inv_std)) (const beta[i])
    -- 2. Real output[i] = (v_real[i] - μ) * inv_std_real * gamma[i] + beta[i]
    -- 3. mem_layerNorm_elem shows the affine form represents the real value

    -- Simplify the affine side using affine_eq
    simp only [List.getElem_map] at affine_eq

    -- Get the real zipWith3 element
    have real_eq := getElem_zipWith3_aux (fun xi (g : ℚ) (b : ℚ) =>
        (xi - v_real.sum / ↑v_real.length) *
          (1 / Real.sqrt ((v_real.map (fun x => (x - v_real.sum / ↑v_real.length) *
             (x - v_real.sum / ↑v_real.length))).sum / ↑v_real.length + ↑epsilon)) * (g : ℝ) + b)
        v_real gamma beta i hi_vreal hi_gamma hi_beta

    -- Now we can convert the proof
    -- LHS: (List.zipWith3 ...)[i]'hi_affine
    -- RHS: (List.zipWith3 ...)[i]'hi_real
    -- Both simplify to match helem

    -- Switch list element proofs to the ones from the goal.
    have affine_eq' :
        (List.zipWith3 (fun xi g b =>
          AffineForm.add (AffineForm.scale g (AffineForm.mul xi inv_std)) (AffineForm.const b))
          (v.map (fun xi => xi.sub v.mean)) gamma beta)[i]'hi_affine =
          AffineForm.add (AffineForm.scale gamma[i] (AffineForm.mul (v[i].sub v.mean) inv_std))
            (AffineForm.const beta[i]) := by
      have hproof :
          (List.zipWith3 (fun xi g b =>
            AffineForm.add (AffineForm.scale g (AffineForm.mul xi inv_std)) (AffineForm.const b))
            (v.map (fun xi => xi.sub v.mean)) gamma beta)[i]'hi_affine =
          (List.zipWith3 (fun xi g b =>
            AffineForm.add (AffineForm.scale g (AffineForm.mul xi inv_std)) (AffineForm.const b))
            (v.map (fun xi => xi.sub v.mean)) gamma beta)[i]'(by rw [length_zipWith3_aux]; omega) :=
        getElem_proof_irrel _ _ hi_affine (by rw [length_zipWith3_aux]; omega)
      simpa [hproof] using affine_eq

    have real_eq' :
        (List.zipWith3 (fun xi (g : ℚ) (b : ℚ) =>
          (xi - v_real.sum / ↑v_real.length) *
            (1 / Real.sqrt ((v_real.map (fun x => (x - v_real.sum / ↑v_real.length) *
               (x - v_real.sum / ↑v_real.length))).sum / ↑v_real.length + ↑epsilon)) * (g : ℝ) + b)
          v_real gamma beta)[i]'hi_real =
          (v_real[i] - v_real.sum / ↑v_real.length) *
            (1 / Real.sqrt ((v_real.map (fun x => (x - v_real.sum / ↑v_real.length) *
               (x - v_real.sum / ↑v_real.length))).sum / ↑v_real.length + ↑epsilon)) *
              (gamma[i] : ℝ) + (beta[i] : ℝ) := by
      have hproof :
          (List.zipWith3 (fun xi (g : ℚ) (b : ℚ) =>
            (xi - v_real.sum / ↑v_real.length) *
              (1 / Real.sqrt ((v_real.map (fun x => (x - v_real.sum / ↑v_real.length) *
                 (x - v_real.sum / ↑v_real.length))).sum / ↑v_real.length + ↑epsilon)) * (g : ℝ) + b)
            v_real gamma beta)[i]'hi_real =
          (List.zipWith3 (fun xi (g : ℚ) (b : ℚ) =>
            (xi - v_real.sum / ↑v_real.length) *
              (1 / Real.sqrt ((v_real.map (fun x => (x - v_real.sum / ↑v_real.length) *
                 (x - v_real.sum / ↑v_real.length))).sum / ↑v_real.length + ↑epsilon)) * (g : ℝ) + b)
            v_real gamma beta)[i]'(by rw [length_zipWith3_aux]; omega) :=
        getElem_proof_irrel _ _ hi_real (by rw [length_zipWith3_aux]; omega)
      simpa [hproof] using real_eq

    rw [affine_eq', real_eq']
    simpa [centered, variance, inv_std, List.getElem_map] using helem

end AffineVector

end LeanCert.Engine.Affine
