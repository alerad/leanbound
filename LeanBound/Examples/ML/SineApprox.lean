/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors (auto-generated)
-/
import LeanBound.ML.Network

set_option linter.unnecessarySeqFocus false

/-!
# Neural Network: sineNet

This file demonstrates **end-to-end verified ML**:

1. A neural network was trained in PyTorch to approximate sin(x)
2. Weights were exported as exact rational numbers
3. We formally verify output bounds using interval arithmetic

## Key Point: Formal Verification vs Testing

Unlike testing (which checks finitely many points), formal verification proves
properties for ALL inputs in a region. This is a mathematical proof covering
infinitely many inputs - not sampling.


## Architecture

- **Input**: 1 dimensions
- **Hidden**: 16 neurons with ReLU activation
- **Output**: 1 dimensions

## Training Results

- Max approximation error: 0.031652

## Verification

This file provides formal verification that the network output
is bounded for all inputs in the specified domain.
-/

namespace LeanBound.Examples.ML.SineApprox

open LeanBound.Core
open LeanBound.ML
open IntervalVector

/-- Layer 1: 1 → 16 -/
def sineNetLayer1Weights : List (List ℚ) := [
  [((9061 : ℚ) / 9710)],
  [((1552 : ℚ) / 993)],
  [(((-607) : ℚ) / 2591)],
  [((8191 : ℚ) / 7266)],
  [(((-1007) : ℚ) / 4596)],
  [((375 : ℚ) / 8438)],
  [(((-4463) : ℚ) / 9167)],
  [((2893 : ℚ) / 5974)],
  [((6716 : ℚ) / 6591)],
  [(((-4313) : ℚ) / 5879)],
  [((11894 : ℚ) / 9737)],
  [((309 : ℚ) / 1651)],
  [((9132 : ℚ) / 9523)],
  [((1115 : ℚ) / 8233)],
  [((5841 : ℚ) / 9256)],
  [(((-1029) : ℚ) / 7288)]
]

def sineNetLayer1Bias : List ℚ := [((461 : ℚ) / 1126), (((-581) : ℚ) / 414), (((-4132) : ℚ) / 8851), ((1 : ℚ) / 9810), (((-663) : ℚ) / 1439), (((-17) : ℚ) / 70), (((-277) : ℚ) / 682), ((4488 : ℚ) / 6317), (((-16621) : ℚ) / 7287), (((-4499) : ℚ) / 9759), (((-17785) : ℚ) / 9287), (((-5765) : ℚ) / 9588), ((2 : ℚ) / 9667), (((-7375) : ℚ) / 7467), ((2463 : ℚ) / 4460), (((-3115) : ℚ) / 3667)]

def sineNetLayer1 : Layer where
  weights := sineNetLayer1Weights
  bias := sineNetLayer1Bias

/-- Layer 2: 16 → 1 -/
def sineNetLayer2Weights : List (List ℚ) := [
  [((2351 : ℚ) / 9922), (((-373) : ℚ) / 1050), (((-577) : ℚ) / 7108), ((942 : ℚ) / 3269), ((305 : ℚ) / 7828), ((356 : ℚ) / 6801), ((139 : ℚ) / 5086), (((-605) : ℚ) / 9156), (((-5140) : ℚ) / 9361), (((-657) : ℚ) / 9691), (((-149) : ℚ) / 280), ((227 : ℚ) / 1017), ((2774 : ℚ) / 9337), (((-1022) : ℚ) / 9351), ((697 : ℚ) / 5217), ((45 : ℚ) / 1006)]
]

def sineNetLayer2Bias : List ℚ := [(((-57) : ℚ) / 565)]

def sineNetLayer2 : Layer where
  weights := sineNetLayer2Weights
  bias := sineNetLayer2Bias

/-- The sineNet network -/
def sineNet : TwoLayerNet where
  layer1 := sineNetLayer1
  layer2 := sineNetLayer2

/-! ## Well-formedness Proofs -/

theorem sineNetLayer1_wf : sineNetLayer1.WellFormed := by
  constructor
  · intro row hrow
    simp only [sineNetLayer1, sineNetLayer1Weights, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem sineNetLayer2_wf : sineNetLayer2.WellFormed := by
  constructor
  · intro row hrow
    simp only [sineNetLayer2, sineNetLayer2Weights, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem sineNet_wf : sineNet.WellFormed := by
  constructor
  · exact sineNetLayer1_wf
  constructor
  · exact sineNetLayer2_wf
  · simp [sineNet, sineNetLayer1, sineNetLayer2, sineNetLayer1Weights, sineNetLayer2Weights,
         Layer.inputDim, Layer.outputDim, sineNetLayer1Bias]

/-! ## Input Domain and Output Bounds -/

/-- Helper to create dyadic interval -/
def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := -53) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec

/-- Input domain -/
def sineNetInputDomain : IntervalVector := [mkInterval 0 ((355 : ℚ) / 113)]

/-- Computed output bounds for the entire input domain -/
def sineNetOutputBounds : IntervalVector :=
  TwoLayerNet.forwardInterval sineNet sineNetInputDomain (-53)

#eval sineNetOutputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))


/-! ## Main Verification Theorem -/

/-- Membership in mkInterval -/
theorem mem_mkInterval {x : ℝ} {lo hi : ℚ} (hle : lo ≤ hi)
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x ∈ mkInterval lo hi hle prec := by
  unfold mkInterval
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  simp only [IntervalRat.mem_def]
  exact hx

/-- **Main Theorem**: For any x in [0, π], the network output is bounded.

This is a formal verification certificate proving that the trained neural
network's output lies within computed bounds for ALL inputs in the domain.

Unlike testing (which checks finitely many points), this is a mathematical
proof covering infinitely many inputs. -/
theorem output_bounded {x : ℝ} (hx : 0 ≤ x ∧ x ≤ (355 : ℝ) / 113) :
    ∀ i, (hi : i < min sineNet.layer2.outputDim sineNet.layer2.bias.length) →
      (TwoLayerNet.forwardReal sineNet [x])[i]'(by
        simp [TwoLayerNet.forwardReal, Layer.forwardReal_length]; omega) ∈
      sineNetOutputBounds[i]'(by
        simp [sineNetOutputBounds, TwoLayerNet.forwardInterval, Layer.forwardInterval_length]; omega) := by
  have hwf := sineNet_wf
  have hdim : sineNet.layer1.inputDim = sineNetInputDomain.length := by
    simp [sineNet, sineNetLayer1, sineNetLayer1Weights, Layer.inputDim, sineNetInputDomain]
  have hxlen : [x].length = sineNetInputDomain.length := by simp [sineNetInputDomain]
  have hmem : ∀ i, (hi : i < sineNetInputDomain.length) →
      [x][i]'(by omega) ∈ sineNetInputDomain[i]'hi := by
    intro i hi
    simp only [sineNetInputDomain, List.length_cons, List.length_nil] at hi
    match i with
    | 0 =>
      simp only [sineNetInputDomain, List.getElem_cons_zero]
      apply mem_mkInterval (by norm_num) _ (-53)
      constructor
      · simp only [Rat.cast_zero]; exact hx.1
      · simp only [Rat.cast_div, Rat.cast_ofNat]; exact hx.2
    | n + 1 => omega
  intro i hi
  have h := TwoLayerNet.mem_forwardInterval hwf hdim hxlen hmem (-53) (by norm_num) i hi
  simp only [sineNetOutputBounds]
  exact h

/-!
## What This Proves

The theorem `output_bounded` establishes:

> **For every real number x with 0 ≤ x ≤ π:**
> The neural network output is contained in the computed interval bounds.

This is verified by Lean's proof checker - a mathematical certainty, not empirical testing.

### Applications

- **Safety certification**: Prove controller outputs stay in safe range
- **Adversarial robustness**: Bound how much outputs can change
- **Regulatory compliance**: Provide formal guarantees for ML systems
-/

end LeanBound.Examples.ML.SineApprox