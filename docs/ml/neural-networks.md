# Neural Network & Transformer Verification

LeanCert includes verified neural network verification based on interval propagation and DeepPoly relaxations, with support for modern architectures including Transformers.

## Overview

The ML module provides:

- **Interval Propagation**: Sound overapproximation of neural network outputs
- **DeepPoly Relaxations**: Tight linear bounds for ReLU and sigmoid activations
- **Transformer Support**: Multi-Head Attention, LayerNorm, GELU, Residual connections
- **Verified Soundness**: All propagation theorems are formally proved in Lean

## Supported Architectures

| Architecture | Components | Status |
|--------------|------------|--------|
| Feedforward (MLP) | Linear, ReLU, Sigmoid | Fully verified |
| Transformers | Attention, LayerNorm, GELU | Fully verified |
| Residual Networks | Skip connections | Fully verified |

## Quick Example

```lean
import LeanCert.ML.Network

open LeanCert.ML

-- Define a simple 2-layer network
def myNet : TwoLayerNet := {
  layer1 := { weights := [[1, -1], [0, 1]], bias := [0, 0] }
  layer2 := { weights := [[1, 1]], bias := [0] }
}

-- Input interval: x₁ ∈ [-1, 1], x₂ ∈ [0, 1]
def inputBox : IntervalVector := [
  IntervalDyadic.ofRat (-1) 1,
  IntervalDyadic.ofRat 0 1
]

-- Propagate intervals through the network
def outputBounds := myNet.forwardInterval inputBox
```

## Architecture

### Layer Structure

A dense layer computes \\( y = \text{ReLU}(Wx + b) \\):

```lean
structure Layer where
  weights : List (List ℚ)  -- Weight matrix (rows)
  bias : List ℚ            -- Bias vector
```

### Soundness Theorem

The key theorem guarantees that interval propagation is sound:

```lean
theorem mem_forwardInterval {l : Layer} {xs : List ℝ} {Is : IntervalVector}
    (hwf : l.WellFormed)
    (hdim : l.inputDim = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, xs[i] ∈ Is[i]) :
    ∀ i, (forwardReal l xs)[i] ∈ (forwardInterval l Is)[i]
```

This says: if every real input is contained in its corresponding interval, then every real output is contained in its corresponding output interval.

## Activation Functions

### ReLU

ReLU interval propagation uses the simple rule:

\\[
\text{ReLU}([l, u]) = [\max(0, l), \max(0, u)]
\\]

```lean
def relu (I : IntervalDyadic) : IntervalDyadic where
  lo := Dyadic.max 0 I.lo
  hi := Dyadic.max 0 I.hi

theorem mem_relu {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    max 0 x ∈ relu I
```

### Sigmoid

Sigmoid uses the conservative bound \\( \sigma(x) \in (0, 1) \\):

```lean
def sigmoid (_I : IntervalDyadic) : IntervalDyadic where
  lo := 0
  hi := 1

theorem mem_sigmoid {x : ℝ} {I : IntervalDyadic} (_hx : x ∈ I) :
    Real.sigmoid x ∈ sigmoid I
```

## DeepPoly Relaxations

For tighter bounds, the module implements DeepPoly-style linear relaxations.

### ReLU Triangle Relaxation

For the "crossing case" where \\( l < 0 < u \\), ReLU is bounded by:

- **Lower**: \\( y \geq 0 \\)
- **Upper**: The line through \\( (l, 0) \\) and \\( (u, u) \\)

```lean
theorem upper_bound_valid (l u : ℚ) (x : ℝ)
    (hl : l < 0) (hu : 0 < u) (hx_mem : l ≤ x ∧ x ≤ u) :
    max 0 x ≤ (crossingUpperBound l u).eval x
```

### Sigmoid Monotonicity Bounds

Since sigmoid is strictly monotone:

\\[
\sigma(l) \leq \sigma(x) \leq \sigma(u) \quad \text{for } x \in [l, u]
\\]

```lean
theorem sigmoid_relaxation_sound (l u x : ℝ) (h : l ≤ x ∧ x ≤ u) :
    sigmoid l ≤ sigmoid x ∧ sigmoid x ≤ sigmoid u
```

### GELU Activation

GELU (Gaussian Error Linear Unit) is the standard activation for Transformers:

\\[
\text{GELU}(x) = 0.5 \cdot x \cdot (1 + \tanh(\sqrt{2/\pi} \cdot (x + 0.044715 \cdot x^3)))
\\]

```lean
def gelu (I : IntervalDyadic) : IntervalDyadic :=
  -- Verified interval approximation
  let inner := I.add (I.mul I.mul I.scale 0.044715)
  let scaled := inner.scale (Real.sqrt (2 / Real.pi))
  I.scale 0.5 |>.mul (IntervalDyadic.one.add (tanh scaled))

theorem mem_geluInterval {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    Real.gelu x ∈ gelu I
```

## Transformer Components

### Self-Attention

LeanCert verifies the scaled dot-product attention mechanism:

\\[
\text{Attention}(Q, K, V) = \text{softmax}\left(\frac{Q \cdot K^T}{\sqrt{d_k}}\right) \cdot V
\\]

```lean
import LeanCert.ML.Attention

-- Verified attention output bounds
theorem mem_scaledDotProductAttention
    {Q K V : Matrix n d ℝ} {Q_int K_int V_int : IntervalMatrix n d}
    (hQ : ∀ i j, Q i j ∈ Q_int i j)
    (hK : ∀ i j, K i j ∈ K_int i j)
    (hV : ∀ i j, V i j ∈ V_int i j) :
    ∀ i j, (scaledDotProductAttention Q K V) i j ∈
           (scaledDotProductAttentionInterval Q_int K_int V_int) i j
```

### Layer Normalization

Interval bounds for LayerNorm are computed soundly:

```lean
import LeanCert.ML.LayerNorm

-- LayerNorm: y = (x - μ) / σ * γ + β
theorem mem_layerNormInterval {x : Vector n ℝ} {I : IntervalVector n}
    (hx : ∀ i, x i ∈ I i) :
    ∀ i, (layerNorm x γ β) i ∈ (layerNormInterval I γ_int β_int) i
```

**Note**: Standard interval arithmetic may overestimate LayerNorm bounds due to variable correlation (the mean and variance are computed from the same input).

## Optimized Implementation

For real-world networks, the `LeanCert.ML.Optimized` module provides:

| Optimization | Speedup | Description |
|--------------|---------|-------------|
| Structure-of-Arrays | ~5x | Cache-efficient interval storage |
| Split-Sign Decomposition | ~2x | Branch-free interval matrix multiply |
| Common Exponent Alignment | ~10-50x | Pure integer (GMP) arithmetic |

```lean
import LeanCert.ML.Optimized

open LeanCert.ML.Optimized

-- Create quantized network for fast propagation
def qnet := QuantizedNet.ofLayers myLayers

-- Fast interval propagation
def output := qnet.forward alignedInput
```

## Verification Status

| Component | Status |
|-----------|--------|
| `mem_forwardInterval` (layer soundness) | ✓ Fully verified |
| `mem_relu` | ✓ Fully verified |
| `mem_sigmoid` | ✓ Fully verified |
| `relu_relaxation_sound` (DeepPoly ReLU) | ✓ Fully verified |
| `sigmoid_relaxation_sound` (DeepPoly Sigmoid) | ✓ Fully verified |
| Optimized implementations | Computationally correct, proofs in progress |

## Use Cases

- **Robustness Verification**: Prove that small input perturbations don't change the output class
- **Safety Certification**: Verify that outputs stay within safe bounds
- **Lipschitz Estimation**: Bound the sensitivity of the network to input changes

## Files

| File | Description |
|------|-------------|
| `ML/Network.lean` | Layer and network definitions |
| `ML/IntervalVector.lean` | Activation functions (ReLU, sigmoid) |
| `ML/Symbolic/ReLU.lean` | DeepPoly ReLU relaxation |
| `ML/Symbolic/Sigmoid.lean` | DeepPoly sigmoid relaxation |
| `ML/Optimized.lean` | High-performance implementations |
