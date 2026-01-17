/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.IntervalVector

/-!
# Verified Neural Network Propagation

This file defines neural network layers and provides verified interval propagation,
enabling robustness verification for neural networks.

## Main definitions

* `Layer` - A dense layer with weights and bias
* `forwardInterval` - Interval propagation through a layer
* `forwardReal` - Real-valued forward pass

## Main theorems

* `mem_layerForwardInterval` - Soundness of single layer propagation

## Design Notes

We keep the network definition simple by using lists. Dimension compatibility
is checked at runtime and encoded in theorem hypotheses. This avoids complex
dependent types while still providing verified soundness.
-/

namespace LeanCert.ML

open LeanCert.Core
open IntervalVector

/-- A dense layer: y = ReLU(W·x + b)
    weights is a list of rows, each row has inputDim elements
    bias has outputDim elements (= number of rows in weights) -/
structure Layer where
  /-- Weight matrix (outputDim × inputDim), stored as list of rows -/
  weights : List (List ℚ)
  /-- Bias vector (outputDim elements) -/
  bias : List ℚ
  deriving Repr

namespace Layer

/-- Input dimension (number of columns in weight matrix) -/
def inputDim (l : Layer) : Nat :=
  match l.weights with
  | [] => 0
  | row :: _ => row.length

/-- Output dimension (number of rows in weight matrix) -/
def outputDim (l : Layer) : Nat := l.weights.length

/-- A layer is well-formed if all rows have the same length and bias matches output -/
def WellFormed (l : Layer) : Prop :=
  (∀ row ∈ l.weights, row.length = l.inputDim) ∧
  l.bias.length = l.outputDim

/-- Forward pass through a layer (real values): y = ReLU(W·x + b) -/
def forwardReal (l : Layer) (x : List ℝ) : List ℝ :=
  let linear := realMatVecMul l.weights x
  let withBias := realAddBias linear l.bias
  withBias.map (fun y => max 0 y)

/-- Forward pass through a layer (interval arithmetic) -/
def forwardInterval (l : Layer) (x : IntervalVector) (prec : Int := -53) : IntervalVector :=
  let linear := matVecMul l.weights x prec
  let withBias := addBias linear l.bias prec
  reluVector withBias

/-- Length of real forward pass output -/
theorem forwardReal_length (l : Layer) (x : List ℝ) :
    (forwardReal l x).length = min l.outputDim l.bias.length := by
  simp [forwardReal, realMatVecMul, realAddBias, outputDim, List.length_map, List.length_zipWith]

/-- Length of interval forward pass output -/
theorem forwardInterval_length (l : Layer) (x : IntervalVector) (prec : Int) :
    (forwardInterval l x prec).length = min l.outputDim l.bias.length := by
  simp only [forwardInterval, matVecMul, addBias, reluVector, List.length_map, List.length_zipWith]
  rfl

/-- Soundness of layer forward pass.
    If x ∈ I (component-wise), then forwardReal(x) ∈ forwardInterval(I). -/
theorem mem_forwardInterval {l : Layer} {xs : List ℝ} {Is : IntervalVector}
    (hwf : l.WellFormed)
    (hdim : l.inputDim = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    ∀ i, (hi : i < min l.outputDim l.bias.length) →
      (forwardReal l xs)[i]'(by rw [forwardReal_length]; exact hi) ∈
      (forwardInterval l Is prec)[i]'(by rw [forwardInterval_length]; exact hi) := by
  intro i hi
  simp only [forwardReal, forwardInterval, reluVector]
  -- Weight matrix has compatible dimensions
  have hWcols : ∀ row ∈ l.weights, row.length = Is.length := by
    intro row hrow
    have h := hwf.1 row hrow
    omega
  -- Matrix-vector multiplication soundness
  have hlinear := mem_matVecMul hWcols hxlen hmem prec hprec
  -- Lengths
  have hlinear_len : (realMatVecMul l.weights xs).length = l.outputDim := by
    simp [realMatVecMul, outputDim]
  have hlinearI_len : (matVecMul l.weights Is prec).length = l.outputDim := by
    simp [matVecMul, outputDim]
  -- Bias addition soundness
  have hlen_eq : (realMatVecMul l.weights xs).length = (matVecMul l.weights Is prec).length := by
    simp [realMatVecMul, matVecMul]
  have hblen_eq : l.bias.length = (matVecMul l.weights Is prec).length := by
    simp [matVecMul]; exact hwf.2
  have hbias := mem_addBias hlen_eq hblen_eq (fun j hj => by
    have hj' : j < l.weights.length := by simp [matVecMul] at hj; exact hj
    exact hlinear j hj') prec hprec
  -- Apply ReLU
  simp only [List.getElem_map]
  have hi_out : i < l.outputDim := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hi_int : i < (matVecMul l.weights Is prec).length := by simp [matVecMul]; exact hi_out
  exact mem_relu (hbias i hi_int)

end Layer

/-- A two-layer network for simple examples -/
structure TwoLayerNet where
  layer1 : Layer
  layer2 : Layer

namespace TwoLayerNet

/-- Forward pass through two layers -/
def forwardReal (net : TwoLayerNet) (x : List ℝ) : List ℝ :=
  Layer.forwardReal net.layer2 (Layer.forwardReal net.layer1 x)

/-- Interval forward pass through two layers -/
def forwardInterval (net : TwoLayerNet) (x : IntervalVector) (prec : Int := -53) : IntervalVector :=
  Layer.forwardInterval net.layer2 (Layer.forwardInterval net.layer1 x prec) prec

/-- Network is well-formed if layers are well-formed and dimensions match -/
def WellFormed (net : TwoLayerNet) : Prop :=
  net.layer1.WellFormed ∧
  net.layer2.WellFormed ∧
  net.layer2.inputDim = min net.layer1.outputDim net.layer1.bias.length

/-- Soundness theorem for two-layer network -/
theorem mem_forwardInterval {net : TwoLayerNet} {xs : List ℝ} {Is : IntervalVector}
    (hwf : net.WellFormed)
    (hdim : net.layer1.inputDim = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    ∀ i, (hi : i < min net.layer2.outputDim net.layer2.bias.length) →
      (forwardReal net xs)[i]'(by
        simp only [forwardReal, Layer.forwardReal_length]; omega) ∈
      (forwardInterval net Is prec)[i]'(by
        simp only [forwardInterval, Layer.forwardInterval_length]; omega) := by
  intro i hi
  simp only [forwardReal, forwardInterval]
  -- First layer soundness
  have hmem1 := Layer.mem_forwardInterval hwf.1 hdim hxlen hmem prec hprec
  -- Second layer input length
  have hlen1_real : (Layer.forwardReal net.layer1 xs).length =
      min net.layer1.outputDim net.layer1.bias.length := Layer.forwardReal_length _ _
  have hlen1_int : (Layer.forwardInterval net.layer1 Is prec).length =
      min net.layer1.outputDim net.layer1.bias.length := Layer.forwardInterval_length _ _ _
  -- Second layer soundness
  have hdim2 : net.layer2.inputDim = (Layer.forwardInterval net.layer1 Is prec).length := by
    rw [hlen1_int]; exact hwf.2.2
  have hmem1' : ∀ j, (hj : j < (Layer.forwardInterval net.layer1 Is prec).length) →
      (Layer.forwardReal net.layer1 xs)[j]'(by
        simp only [Layer.forwardReal_length, Layer.forwardInterval_length] at hlen1_real hj ⊢; omega) ∈
      (Layer.forwardInterval net.layer1 Is prec)[j]'hj := by
    intro j hj
    have hj' : j < min net.layer1.outputDim net.layer1.bias.length := by
      simp only [Layer.forwardInterval_length] at hj; exact hj
    exact hmem1 j hj'
  have hlen_eq : (Layer.forwardReal net.layer1 xs).length =
      (Layer.forwardInterval net.layer1 Is prec).length := by
    simp only [Layer.forwardReal_length, Layer.forwardInterval_length]
  exact Layer.mem_forwardInterval hwf.2.1 hdim2 hlen_eq hmem1' prec hprec i hi

end TwoLayerNet

end LeanCert.ML
