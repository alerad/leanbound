/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.ML.Optimized.IntervalArray
import LeanBound.ML.Network

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

namespace LeanBound.ML.Optimized

open LeanBound.Core
open LeanBound.ML

/-! ### Pure Integer Matrix-Vector Operations -/

/-- Integer dot product of two arrays -/
@[inline] def dotProductInt (a b : Array Int) : Int :=
  let n := min a.size b.size
  (Array.range n).foldl (fun acc i => acc + a[i]! * b[i]!) 0

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
    (⟨a.lo[i.val]'(hn.1 ▸ i.isLt), a.exp⟩ : Dyadic)
  hi := Array.ofFn fun i : Fin n =>
    (⟨a.hi[i.val]'(hn.2 ▸ i.isLt), a.exp⟩ : Dyadic)
  lo_size := Array.size_ofFn
  hi_size := Array.size_ofFn

/-! ### Soundness (Placeholder) -/

/-- The optimized forward pass over-approximates the real forward pass.

    This is the critical soundness theorem: for any real input x in the
    interval array, the real output Layer.forwardReal(x) is contained
    in the interval produced by forwardQuantized.

    TODO: Full proof requires careful tracking of rounding errors. -/
theorem forwardQuantized_sound (l_real : Layer) (l_quant : QuantizedLayer)
    (hquant : l_quant = ofLayer l_real)
    (input : IntervalArray l_real.inputDim)
    (x : Fin l_real.inputDim → ℝ)
    (hx : x ∈ input) :
    True := by  -- Placeholder for the full proof
  trivial

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

end LeanBound.ML.Optimized
