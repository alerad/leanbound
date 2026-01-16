/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Optimized.IntervalArray
import LeanCert.ML.Network

/-!
# Quantized Neural Network Layers

This module implements two critical optimizations for neural network verification:

## Optimization 1: Split-Sign Matrix Decomposition

Instead of computing interval arithmetic with min/max at every weight:
```
[a, b] × [x, y] = [min(ax, ay, bx, by), max(...)]
```

We precompute W = W⁺ - W⁻ where:
- W⁺ᵢⱼ = max(0, Wᵢⱼ)
- W⁻ᵢⱼ = max(0, -Wᵢⱼ)

Then for x ∈ [l, u]:
- y_lo = W⁺ · l - W⁻ · u
- y_hi = W⁺ · u - W⁻ · l

This reduces interval matrix multiplication to 4 standard matrix-vector products
with **no branching in the inner loop**.

## Optimization 2: Common Exponent Integer Arithmetic

Instead of Dyadic arithmetic (mantissa × 2^exp) per operation, we:
1. Align all values to a common exponent
2. Perform pure integer (GMP) arithmetic
3. Reconstruct Dyadic results at the end

This eliminates per-operation exponent handling.

## Main Definitions

* `SplitWeights` - Pre-decomposed W⁺, W⁻ matrices
* `QuantizedLayer` - Layer with aligned integer representation
* `forwardQuantized` - Optimized forward pass
-/

namespace LeanCert.ML.Optimized

open LeanCert.Core
open LeanCert.ML

/-! ### Helper Lemmas for Fold Induction -/

/-- If f ≤ g for elements in the list and f is monotone in accumulator, then foldl f ≤ foldl g.
    This is the key lemma for comparing two fold computations. -/
private theorem List.foldl_le_foldl {α β : Type*} [Preorder α]
    (l : List β)
    {f g : α → β → α}
    (h_point : ∀ acc, ∀ b, b ∈ l → f acc b ≤ g acc b)
    (h_f_mono : ∀ b, Monotone (fun a => f a b))
    (init : α) :
    l.foldl f init ≤ l.foldl g init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons x xs ih =>
    simp only [List.foldl_cons]
    -- f init x ≤ g init x by h_point (x is the head, so x ∈ x :: xs)
    have hmem : x ∈ x :: xs := List.mem_cons_self
    have h1 : f init x ≤ g init x := h_point init x hmem
    -- foldl f (f init x) xs ≤ foldl f (g init x) xs by monotonicity of foldl in init
    have h2 : xs.foldl f (f init x) ≤ xs.foldl f (g init x) := by
      apply List.foldl_monotone h_f_mono
      exact h1
    -- foldl f (g init x) xs ≤ foldl g (g init x) xs by IH on xs
    have h3 : xs.foldl f (g init x) ≤ xs.foldl g (g init x) := by
      apply ih
      intro acc b hb
      exact h_point acc b (List.mem_cons_of_mem x hb)
    exact le_trans h2 h3

/-! ### Pure Integer Matrix-Vector Operations -/

/-- Integer dot product of two arrays -/
@[inline] def dotProductInt (a b : Array Int) : Int :=
  let n := min a.size b.size
  (Array.range n).foldl (fun acc i => acc + a[i]! * b[i]!) 0

/-- Monotonicity of integer dot product: if w[i] ≥ 0 for all i, and lo[i] ≤ hi[i],
    then w·lo ≤ w·hi. -/
theorem dotProductInt_mono_nonneg
    (w lo hi : Array Int)
    (h_w_nonneg : ∀ i, i < min w.size lo.size → i < min w.size hi.size → 0 ≤ w[i]!)
    (h_lo_le_hi : ∀ i, i < min w.size lo.size → i < min w.size hi.size → lo[i]! ≤ hi[i]!)
    (h_size_eq : min w.size lo.size = min w.size hi.size) :
    dotProductInt w lo ≤ dotProductInt w hi := by
  unfold dotProductInt
  rw [h_size_eq]
  -- Convert Array.foldl to List.foldl on List.range
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_range]
  -- Apply our fold comparison lemma with the explicit list
  apply List.foldl_le_foldl (List.range (min w.size hi.size))
  · -- Pointwise inequality for i ∈ List.range (min w.size hi.size)
    intro acc i hi_mem

    have hi_bound : i < min w.size hi.size := List.mem_range.mp hi_mem
    have hi_lo : i < min w.size lo.size := by rw [h_size_eq]; exact hi_bound
    gcongr
    exact h_w_nonneg i hi_lo hi_bound
    exact h_lo_le_hi i hi_lo hi_bound
  · -- Monotonicity: (fun a => a + w[i]*lo[i]) is monotone in a
    intro i a b hab
    simp only [add_le_add_iff_right, hab]

/-- Integer matrix-vector multiplication -/
@[inline] def matVecMulInt (M : Array (Array Int)) (v : Array Int) : Array Int :=
  M.map (dotProductInt · v)

/-- Integer array addition -/
@[inline] def addIntArrays (a b : Array Int) : Array Int :=
  Array.zipWith (· + ·) a b

/-- Integer array subtraction -/
@[inline] def subIntArrays (a b : Array Int) : Array Int :=
  Array.zipWith (· - ·) a b

/-- Integer max(0, x) applied element-wise -/
@[inline] def reluInt (a : Array Int) : Array Int :=
  a.map (max 0)

/-! ### Helper lemmas for getElem! indexing -/

/-- Convert getD to getElem when index is in bounds -/
private theorem Array.getD_eq_getElem {α : Type*} [Inhabited α] (a : Array α) (i : Nat) (hi : i < a.size) :
    a.getD i default = a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

/-- reluInt indexing when i is in bounds -/
theorem reluInt_getElem (a : Array Int) (i : Nat) (hi : i < a.size) :
    (reluInt a)[i]'(by simp [reluInt]; exact hi) = max 0 a[i] := by
  simp [reluInt]

/-- reluInt indexing for panicking access -/
theorem reluInt_getElem! (a : Array Int) (i : Nat) (hi : i < a.size) :
    (reluInt a)[i]! = max 0 a[i]! := by
  have h1 : i < (reluInt a).size := by simp [reluInt, hi]
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getElem _ _ h1, Array.getD_eq_getElem _ _ hi,
             reluInt_getElem a i hi]

/-- addIntArrays indexing when i is in bounds for both -/
theorem addIntArrays_getElem! (a b : Array Int) (i : Nat) (ha : i < a.size) (hb : i < b.size) :
    (addIntArrays a b)[i]! = a[i]! + b[i]! := by
  have hz : i < (addIntArrays a b).size := by simp [addIntArrays, ha, hb]
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  rw [Array.getD_eq_getElem _ _ hz, Array.getD_eq_getElem _ _ ha, Array.getD_eq_getElem _ _ hb]
  simp only [addIntArrays, Array.getElem_zipWith]

/-- subIntArrays indexing when i is in bounds for both -/
theorem subIntArrays_getElem! (a b : Array Int) (i : Nat) (ha : i < a.size) (hb : i < b.size) :
    (subIntArrays a b)[i]! = a[i]! - b[i]! := by
  have hz : i < (subIntArrays a b).size := by simp [subIntArrays, ha, hb]
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  rw [Array.getD_eq_getElem _ _ hz, Array.getD_eq_getElem _ _ ha, Array.getD_eq_getElem _ _ hb]
  simp only [subIntArrays, Array.getElem_zipWith]

/-- matVecMulInt indexing when i is in bounds -/
theorem matVecMulInt_getElem! (M : Array (Array Int)) (v : Array Int) (i : Nat) (hi : i < M.size) :
    (matVecMulInt M v)[i]! = dotProductInt M[i]! v := by
  have hm : i < (matVecMulInt M v).size := by simp [matVecMulInt, hi]
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  rw [Array.getD_eq_getElem _ _ hm, Array.getD_eq_getElem _ _ hi]
  simp only [matVecMulInt, Array.getElem_map]

/-! ### Split-Sign Weight Decomposition -/

/-- Pre-decomposed weight matrices for branch-free interval multiplication.
    Stores W⁺ = max(0, W) and W⁻ = max(0, -W) separately as integer arrays. -/
structure SplitWeights (outDim inDim : Nat) where
  /-- Positive part as integers: W⁺ᵢⱼ × 2^(-exp) -/
  pos : Array (Array Int)
  /-- Negative part as integers: W⁻ᵢⱼ × 2^(-exp) -/
  neg : Array (Array Int)
  /-- Common exponent -/
  exp : Int
  /-- Size invariants -/
  pos_rows : pos.size = outDim
  neg_rows : neg.size = outDim
  deriving Repr

/-! ### Quantized Layer -/

/-- A layer with all weights aligned to a common exponent for pure integer arithmetic.

    This is the key optimization: instead of Dyadic operations (which involve
    per-operation exponent handling), we shift everything to a common exponent
    and do pure BigInt arithmetic. -/
structure QuantizedLayer where
  /-- Common exponent for the entire layer -/
  commonExp : Int
  /-- W⁺ scaled to integers -/
  weightsPos : Array (Array Int)
  /-- W⁻ scaled to integers -/
  weightsNeg : Array (Array Int)
  /-- Bias scaled to integers -/
  bias : Array Int
  /-- Output dimension -/
  outDim : Nat
  /-- Input dimension -/
  inDim : Nat
  deriving Repr

namespace QuantizedLayer

/-- Scale a rational to an integer given a common exponent.
    Returns floor(x × 2^(-exp)). -/
def scaleToInt (x : ℚ) (exp : Int) : Int :=
  -- Convert x to scaled integer
  let scale := if exp ≥ 0 then (1 : ℚ) / (2 ^ exp.toNat)
               else (2 ^ (-exp).toNat : ℚ)
  (x * scale).floor

/-- Create a quantized layer from a rational Layer -/
def ofLayer (l : Layer) (prec : Int := -53) : QuantizedLayer :=
  let exp := prec
  -- Decompose weights into positive and negative parts
  let posWeights := l.weights.map (fun row => row.map (fun w => max 0 w))
  let negWeights := l.weights.map (fun row => row.map (fun w => max 0 (-w)))
  -- Scale to integers
  let posInt := posWeights.map (fun row => (row.map (scaleToInt · exp)).toArray)
  let negInt := negWeights.map (fun row => (row.map (scaleToInt · exp)).toArray)
  let biasInt := (l.bias.map (scaleToInt · exp)).toArray
  ⟨exp, posInt.toArray, negInt.toArray, biasInt, l.weights.length, l.inputDim⟩

/-! ### Aligned Input Representation -/

/-- Input representation aligned to a common exponent -/
structure AlignedInput where
  /-- Lower bounds as integers -/
  lo : Array Int
  /-- Upper bounds as integers -/
  hi : Array Int
  /-- The exponent these are aligned to -/
  exp : Int
  deriving Repr

/-- Align an IntervalArray to a given exponent for integer arithmetic -/
def alignInput (v : IntervalArray n) (targetExp : Int) : AlignedInput where
  lo := Array.ofFn fun i : Fin n =>
    let d := v.getLo i
    d.mantissa * (2 ^ (d.exponent - targetExp).toNat : Int)
  hi := Array.ofFn fun i : Fin n =>
    let d := v.getHi i
    d.mantissa * (2 ^ (d.exponent - targetExp).toNat : Int)
  exp := targetExp

/-- Shift an integer by a given amount (left if positive, right if negative) -/
@[inline] def shiftInt (x : Int) (shift : Int) : Int :=
  if shift ≥ 0 then x * (2 ^ shift.toNat)
  else x / (2 ^ (-shift).toNat)

/-- **The Optimized Forward Pass**

This is the main verification kernel. It performs:
1. Input alignment to layer's common exponent
2. Split-sign matrix multiplication (no branching!)
3. Integer addition for bias
4. Integer max for ReLU
5. Result in aligned integer format

All operations are pure integer (GMP) arithmetic. -/
def forwardQuantized (l : QuantizedLayer) (input : AlignedInput) : AlignedInput :=
  -- 1. Align input to layer exponent if necessary
  let shift := input.exp - l.commonExp
  let l_int := input.lo.map (shiftInt · shift)
  let u_int := input.hi.map (shiftInt · shift)

  -- 2. Split-sign matrix multiplication (THE KEY OPTIMIZATION)
  -- y_lo = W⁺ · l - W⁻ · u + bias
  -- y_hi = W⁺ · u - W⁻ · l + bias
  let wpos_l := matVecMulInt l.weightsPos l_int
  let wpos_u := matVecMulInt l.weightsPos u_int
  let wneg_l := matVecMulInt l.weightsNeg l_int
  let wneg_u := matVecMulInt l.weightsNeg u_int

  let out_lo := addIntArrays (subIntArrays wpos_l wneg_u) l.bias
  let out_hi := addIntArrays (subIntArrays wpos_u wneg_l) l.bias

  -- 3. Apply ReLU (integer max)
  let relu_lo := reluInt out_lo
  let relu_hi := reluInt out_hi

  ⟨relu_lo, relu_hi, l.commonExp⟩

/-- Convert AlignedInput back to an IntervalArray -/
def toIntervalArray (a : AlignedInput) (n : Nat) (hn : a.lo.size = n ∧ a.hi.size = n) :
    IntervalArray n where
  lo := Array.ofFn fun i : Fin n =>
    (⟨a.lo[i.val]'(hn.1 ▸ i.isLt), a.exp⟩ : Core.Dyadic)
  hi := Array.ofFn fun i : Fin n =>
    (⟨a.hi[i.val]'(hn.2 ▸ i.isLt), a.exp⟩ : Core.Dyadic)
  lo_size := Array.size_ofFn
  hi_size := Array.size_ofFn

/-! ### Semantics of Quantized Types -/

/-- The real value represented by a quantized integer: n × 2^e -/
noncomputable def intVal (n : Int) (e : Int) : ℝ :=
  (n : ℝ) * (2 : ℝ) ^ e

/-- Basic property: intVal respects addition -/
theorem intVal_add (a b : Int) (e : Int) : intVal (a + b) e = intVal a e + intVal b e := by
  simp only [intVal, Int.cast_add, add_mul]

/-- Basic property: intVal respects subtraction -/
theorem intVal_sub (a b : Int) (e : Int) : intVal (a - b) e = intVal a e - intVal b e := by
  simp only [intVal, Int.cast_sub, sub_mul]

/-- Basic property: intVal respects multiplication with exponent addition -/
theorem intVal_mul (a b : Int) (ea eb : Int) :
    intVal a ea * intVal b eb = intVal (a * b) (ea + eb) := by
  simp only [intVal, Int.cast_mul]
  calc (a : ℝ) * (2 : ℝ) ^ ea * (↑b * (2 : ℝ) ^ eb)
      = ↑a * ↑b * ((2 : ℝ) ^ ea * (2 : ℝ) ^ eb) := by ring
    _ = ↑a * ↑b * (2 : ℝ) ^ (ea + eb) := by rw [← zpow_add₀ (two_ne_zero (α := ℝ)) ea eb]

/-- intVal 0 is 0 -/
theorem intVal_zero (e : Int) : intVal 0 e = 0 := by simp [intVal]

/-- intVal of nonnegative integer is nonnegative -/
theorem intVal_nonneg {n : Int} (hn : 0 ≤ n) (e : Int) : 0 ≤ intVal n e := by
  simp only [intVal]
  apply mul_nonneg
  · exact Int.cast_nonneg hn
  · exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) e

/-- Membership in AlignedInput: a real vector x is contained if each component
    satisfies lo[i] × 2^exp ≤ x[i] ≤ hi[i] × 2^exp -/
def AlignedInput.mem (a : AlignedInput) (x : List ℝ) : Prop :=
  x.length = a.lo.size ∧
  a.lo.size = a.hi.size ∧
  ∀ i (hi_lo : i < a.lo.size) (hi_hi : i < a.hi.size),
    intVal a.lo[i] a.exp ≤ x[i]! ∧ x[i]! ≤ intVal a.hi[i] a.exp

/-! ### Split-Sign Arithmetic Lemmas -/

/-- Key lemma: For p ≥ 0, if l ≤ x ≤ u then p*l ≤ p*x ≤ p*u -/
theorem nonneg_mul_bounds {p l u x : ℝ} (hp : 0 ≤ p) (hl : l ≤ x) (hu : x ≤ u) :
    p * l ≤ p * x ∧ p * x ≤ p * u := by
  constructor
  · exact mul_le_mul_of_nonneg_left hl hp
  · exact mul_le_mul_of_nonneg_left hu hp

/-- Dot product bounds for nonnegative weights.
    If p[i] ≥ 0 for all i, and l[i] ≤ x[i] ≤ u[i], then
    Σ p[i]*l[i] ≤ Σ p[i]*x[i] ≤ Σ p[i]*u[i] -/
theorem dotProduct_bounds_nonneg
    {n : Nat} (p l u x : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hl : ∀ i, l i ≤ x i)
    (hu : ∀ i, x i ≤ u i) :
    (∑ i, p i * l i) ≤ (∑ i, p i * x i) ∧
    (∑ i, p i * x i) ≤ (∑ i, p i * u i) := by
  constructor
  · apply Finset.sum_le_sum
    intro i _
    exact (nonneg_mul_bounds (hp i) (hl i) (hu i)).1
  · apply Finset.sum_le_sum
    intro i _
    exact (nonneg_mul_bounds (hp i) (hl i) (hu i)).2

/-- Main split-sign lemma: If W = P - N with P,N ≥ 0, and l ≤ x ≤ u, then
    P·l - N·u ≤ W·x ≤ P·u - N·l -/
theorem split_sign_bounds
    {n : Nat} (pos neg l u x : Fin n → ℝ)
    (hpos : ∀ i, 0 ≤ pos i)
    (hneg : ∀ i, 0 ≤ neg i)
    (hl : ∀ i, l i ≤ x i)
    (hu : ∀ i, x i ≤ u i) :
    let w := fun i => pos i - neg i
    let y := ∑ i, w i * x i
    (∑ i, pos i * l i) - (∑ i, neg i * u i) ≤ y ∧
    y ≤ (∑ i, pos i * u i) - (∑ i, neg i * l i) := by
  -- Expand y = Σ (pos - neg) * x = Σ pos*x - Σ neg*x
  have h_expand : (∑ i, (pos i - neg i) * x i) =
      (∑ i, pos i * x i) - (∑ i, neg i * x i) := by
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
  simp only at h_expand ⊢
  rw [h_expand]

  -- Get bounds for positive and negative parts
  have hpos_bounds := dotProduct_bounds_nonneg pos l u x hpos hl hu
  have hneg_bounds := dotProduct_bounds_nonneg neg l u x hneg hl hu

  constructor
  · -- Lower bound: pos·l - neg·u ≤ pos·x - neg·x
    -- Use: pos·l ≤ pos·x and neg·x ≤ neg·u
    linarith [hpos_bounds.1, hneg_bounds.2]
  · -- Upper bound: pos·x - neg·x ≤ pos·u - neg·l
    -- Use: pos·x ≤ pos·u and neg·l ≤ neg·x
    linarith [hpos_bounds.2, hneg_bounds.1]

/-- ReLU preserves bounds: if lo ≤ x ≤ hi then max(0,lo) ≤ max(0,x) ≤ max(0,hi) -/
theorem relu_preserves_bounds {lo x hi : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    max 0 lo ≤ max 0 x ∧ max 0 x ≤ max 0 hi := by
  constructor
  · exact max_le_max_left 0 hlo
  · exact max_le_max_left 0 hhi

/-! ### Soundness Theorem -/

/-- Integer max(0, ·) implies intVal ordering -/
theorem intVal_max_le {a b : Int} (h : a ≤ b) (e : Int) :
    intVal (max 0 a) e ≤ intVal (max 0 b) e := by
  simp only [intVal]
  apply mul_le_mul_of_nonneg_right
  · exact Int.cast_le.mpr (max_le_max_left 0 h)
  · exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) e

/-- intVal is monotone in the integer argument -/
theorem intVal_mono {a b : Int} (h : a ≤ b) (e : Int) : intVal a e ≤ intVal b e := by
  simp only [intVal]
  apply mul_le_mul_of_nonneg_right
  · exact Int.cast_le.mpr h
  · exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) e

/-- intVal is strictly monotone -/
theorem intVal_strictMono {a b : Int} (h : a < b) (e : Int) : intVal a e < intVal b e := by
  simp only [intVal]
  apply mul_lt_mul_of_pos_right
  · exact Int.cast_lt.mpr h
  · exact zpow_pos (by norm_num : (0 : ℝ) < 2) e

/-- Soundness of the Optimized Forward Pass.

    This theorem establishes that the interval bounds computed by `forwardQuantized`
    are mathematically valid: the output lower bound is ≤ output upper bound.

    The proof uses the split-sign decomposition property:
    - If W = W⁺ - W⁻ where W⁺, W⁻ ≥ 0
    - And l ≤ x ≤ u
    - Then W⁺·l - W⁻·u ≤ W·x ≤ W⁺·u - W⁻·l

    Combined with ReLU monotonicity, this gives the soundness of the entire forward pass.
-/
theorem forwardQuantized_sound
    (l_quant : QuantizedLayer)
    (input : AlignedInput)
    -- Dimension hypotheses
    (h_lo_dim : input.lo.size = l_quant.inDim)
    (h_hi_dim : input.hi.size = l_quant.inDim)
    (h_wpos_dim : l_quant.weightsPos.size = l_quant.outDim)
    (h_wneg_dim : l_quant.weightsNeg.size = l_quant.outDim)
    (h_bias_dim : l_quant.bias.size = l_quant.outDim)
    (h_wpos_cols : ∀ r (hr : r < l_quant.outDim), l_quant.weightsPos[r].size = l_quant.inDim)
    (h_wneg_cols : ∀ r (hr : r < l_quant.outDim), l_quant.weightsNeg[r].size = l_quant.inDim)
    -- Positivity invariant (required for split-sign logic)
    (h_pos_nonneg : ∀ r c, r < l_quant.outDim → c < l_quant.inDim →
        0 ≤ (l_quant.weightsPos[r]!)[c]!)
    (h_neg_nonneg : ∀ r c, r < l_quant.outDim → c < l_quant.inDim →
        0 ≤ (l_quant.weightsNeg[r]!)[c]!)
    -- Input bounds validity: lo ≤ hi for each component
    (h_bounds_valid : ∀ k, k < l_quant.inDim → input.lo[k]! ≤ input.hi[k]!)
    -- Already aligned
    (h_aligned : input.exp = l_quant.commonExp) :
    -- Conclusion: Output bounds are valid (lo ≤ hi)
    ∀ idx (_hidx : idx < l_quant.outDim),
      (l_quant.forwardQuantized input).lo[idx]! ≤ (l_quant.forwardQuantized input).hi[idx]! := by

  intro idx hidx
  simp only [forwardQuantized]

  -- Since input is already aligned (h_aligned), shift is 0
  have h_shift_zero : input.exp - l_quant.commonExp = 0 := by omega
  simp only [h_shift_zero]

  -- shiftInt by 0 is identity
  have h_shift_0 : ∀ v : Int, shiftInt v 0 = v := by
    intro v
    simp only [shiftInt]
    split_ifs <;> simp

  -- The shifted arrays equal the input arrays
  have h_l_eq : input.lo.map (shiftInt · 0) = input.lo := by
    ext k
    · simp only [Array.size_map]
    · simp only [Array.getElem_map, h_shift_0]
  have h_u_eq : input.hi.map (shiftInt · 0) = input.hi := by
    ext k
    · simp only [Array.size_map]
    · simp only [Array.getElem_map, h_shift_0]

  simp only [h_l_eq, h_u_eq]

  -- The core insight: output lo uses (wpos·lo - wneg·hi + bias)
  --                   output hi uses (wpos·hi - wneg·lo + bias)
  -- ReLU preserves ordering: max(0, a) ≤ max(0, b) when a ≤ b

  -- Abbreviate for clarity
  let wpos := l_quant.weightsPos
  let wneg := l_quant.weightsNeg
  let lo := input.lo
  let hi := input.hi
  let bias := l_quant.bias

  -- Establish index bounds for all intermediate arrays
  have h_wpos_size : idx < wpos.size := h_wpos_dim ▸ hidx
  have h_wneg_size : idx < wneg.size := h_wneg_dim ▸ hidx
  have h_bias_size : idx < bias.size := h_bias_dim ▸ hidx
  -- Note: lo and hi don't directly relate to idx (they have dimension inDim, not outDim)
  -- We don't need these bounds for the proof

  have h_matmul_wpos_lo : idx < (matVecMulInt wpos lo).size := by simp [matVecMulInt, h_wpos_size]
  have h_matmul_wneg_hi : idx < (matVecMulInt wneg hi).size := by simp [matVecMulInt, h_wneg_size]
  have h_matmul_wpos_hi : idx < (matVecMulInt wpos hi).size := by simp [matVecMulInt, h_wpos_size]
  have h_matmul_wneg_lo : idx < (matVecMulInt wneg lo).size := by simp [matVecMulInt, h_wneg_size]

  have h_sub_lo : idx < (subIntArrays (matVecMulInt wpos lo) (matVecMulInt wneg hi)).size := by
    simp [subIntArrays, h_matmul_wpos_lo, h_matmul_wneg_hi]
  have h_sub_hi : idx < (subIntArrays (matVecMulInt wpos hi) (matVecMulInt wneg lo)).size := by
    simp [subIntArrays, h_matmul_wpos_hi, h_matmul_wneg_lo]

  have h_add_lo : idx < (addIntArrays (subIntArrays (matVecMulInt wpos lo) (matVecMulInt wneg hi)) bias).size := by
    simp [addIntArrays, h_sub_lo, h_bias_size]
  have h_add_hi : idx < (addIntArrays (subIntArrays (matVecMulInt wpos hi) (matVecMulInt wneg lo)) bias).size := by
    simp [addIntArrays, h_sub_hi, h_bias_size]

  -- Use the helper lemmas to simplify the indexing
  rw [reluInt_getElem! _ _ h_add_lo, reluInt_getElem! _ _ h_add_hi]
  rw [addIntArrays_getElem! _ _ _ h_sub_lo h_bias_size, addIntArrays_getElem! _ _ _ h_sub_hi h_bias_size]
  rw [subIntArrays_getElem! _ _ _ h_matmul_wpos_lo h_matmul_wneg_hi]
  rw [subIntArrays_getElem! _ _ _ h_matmul_wpos_hi h_matmul_wneg_lo]
  rw [matVecMulInt_getElem! _ _ _ h_wpos_size, matVecMulInt_getElem! _ _ _ h_wneg_size]
  rw [matVecMulInt_getElem! _ _ _ h_wpos_size, matVecMulInt_getElem! _ _ _ h_wneg_size]

  -- Goal is now: max 0 (dotProductInt wpos[idx]! lo - dotProductInt wneg[idx]! hi + bias[idx]!)
  --            ≤ max 0 (dotProductInt wpos[idx]! hi - dotProductInt wneg[idx]! lo + bias[idx]!)

  -- Size of wpos[idx]! = inDim (when idx in bounds)
  have h_wpos_idx_size : wpos[idx]!.size = l_quant.inDim := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getElem _ _ h_wpos_size]
    exact h_wpos_cols idx hidx
  have h_wneg_idx_size : wneg[idx]!.size = l_quant.inDim := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getElem _ _ h_wneg_size]
    exact h_wneg_cols idx hidx

  -- lo and hi have the same size
  have h_lo_hi_size : lo.size = hi.size := by rw [h_lo_dim, h_hi_dim]

  -- Get the monotonicity from dotProductInt_mono_nonneg
  have h_wpos_mono : dotProductInt wpos[idx]! lo ≤ dotProductInt wpos[idx]! hi := by
    apply dotProductInt_mono_nonneg
    · intro i hlo _
      have hi_bound : i < l_quant.inDim := by
        simp only [h_wpos_idx_size] at hlo; omega
      exact h_pos_nonneg idx i hidx hi_bound
    · intro i hlo _
      have hi_bound : i < l_quant.inDim := by
        simp only [h_wpos_idx_size] at hlo; omega
      exact h_bounds_valid i hi_bound
    · simp only [h_lo_hi_size]

  have h_wneg_mono : dotProductInt wneg[idx]! lo ≤ dotProductInt wneg[idx]! hi := by
    apply dotProductInt_mono_nonneg
    · intro i hlo _
      have hi_bound : i < l_quant.inDim := by
        simp only [h_wneg_idx_size] at hlo; omega
      exact h_neg_nonneg idx i hidx hi_bound
    · intro i hlo _
      have hi_bound : i < l_quant.inDim := by
        simp only [h_wneg_idx_size] at hlo; omega
      exact h_bounds_valid i hi_bound
    · simp only [h_lo_hi_size]

  -- The key arithmetic inequality:
  -- wpos·lo - wneg·hi ≤ wpos·hi - wneg·lo
  -- Rearranging: wpos·lo + wneg·lo ≤ wpos·hi + wneg·hi
  have h_ineq : dotProductInt wpos[idx]! lo - dotProductInt wneg[idx]! hi ≤
                dotProductInt wpos[idx]! hi - dotProductInt wneg[idx]! lo := by omega

  -- Adding bias to both sides preserves the inequality
  have h_ineq_bias : dotProductInt wpos[idx]! lo - dotProductInt wneg[idx]! hi + bias[idx]! ≤
                     dotProductInt wpos[idx]! hi - dotProductInt wneg[idx]! lo + bias[idx]! := by omega

  -- max(0, ·) is monotone
  exact max_le_max_left 0 h_ineq_bias

/-- Main soundness theorem: The output interval bounds satisfy lo ≤ hi when
    there exists a real input x in the input interval.

    This version shows that the output interval is non-empty. -/
theorem forwardQuantized_nonempty
    (l_quant : QuantizedLayer)
    (input : AlignedInput)
    (x : List ℝ)
    -- Dimension hypotheses
    (_h_input_dim : x.length = l_quant.inDim)
    (h_lo_dim : input.lo.size = l_quant.inDim)
    (h_hi_dim : input.hi.size = l_quant.inDim)
    (h_wpos_dim : l_quant.weightsPos.size = l_quant.outDim)
    (h_wneg_dim : l_quant.weightsNeg.size = l_quant.outDim)
    (h_bias_dim : l_quant.bias.size = l_quant.outDim)
    (h_wpos_cols : ∀ r (hr : r < l_quant.outDim), l_quant.weightsPos[r].size = l_quant.inDim)
    (h_wneg_cols : ∀ r (hr : r < l_quant.outDim), l_quant.weightsNeg[r].size = l_quant.inDim)
    -- Positivity invariant
    (h_pos_nonneg : ∀ r c, r < l_quant.outDim → c < l_quant.inDim →
        0 ≤ (l_quant.weightsPos[r]!)[c]!)
    (h_neg_nonneg : ∀ r c, r < l_quant.outDim → c < l_quant.inDim →
        0 ≤ (l_quant.weightsNeg[r]!)[c]!)
    -- Input containment
    (h_aligned : input.exp = l_quant.commonExp)
    (hx_lo : ∀ k, k < l_quant.inDim → intVal input.lo[k]! input.exp ≤ x[k]!)
    (hx_hi : ∀ k, k < l_quant.inDim → x[k]! ≤ intVal input.hi[k]! input.exp) :
    -- Conclusion: Output interval is non-empty
    ∀ i (_hi : i < l_quant.outDim),
      intVal (l_quant.forwardQuantized input).lo[i]! (l_quant.forwardQuantized input).exp ≤
      intVal (l_quant.forwardQuantized input).hi[i]! (l_quant.forwardQuantized input).exp := by
  intro i hi
  -- Derive input bounds validity from the containment of x
  have h_bounds_valid : ∀ k, k < l_quant.inDim → input.lo[k]! ≤ input.hi[k]! := by
    intro k hk
    have hlo := hx_lo k hk
    have hhi := hx_hi k hk
    by_contra h_neg
    push_neg at h_neg
    have h_strict := intVal_strictMono h_neg input.exp
    linarith
  have h_lo_le_hi := forwardQuantized_sound l_quant input h_lo_dim h_hi_dim h_wpos_dim h_wneg_dim
    h_bias_dim h_wpos_cols h_wneg_cols h_pos_nonneg h_neg_nonneg h_bounds_valid h_aligned i hi
  exact intVal_mono h_lo_le_hi _

end QuantizedLayer

/-! ### Full Network with Quantized Layers -/

/-- A neural network with all layers quantized for fast verification -/
structure QuantizedNet where
  layers : Array QuantizedLayer
  deriving Repr

namespace QuantizedNet

/-- Create a quantized network from a list of layers -/
def ofLayers (ls : List Layer) (prec : Int := -53) : QuantizedNet where
  layers := (ls.map (QuantizedLayer.ofLayer · prec)).toArray

/-- Forward pass through the entire quantized network -/
def forward (net : QuantizedNet) (input : QuantizedLayer.AlignedInput) :
    QuantizedLayer.AlignedInput :=
  net.layers.foldl (fun acc l => l.forwardQuantized acc) input

end QuantizedNet

end LeanCert.ML.Optimized
