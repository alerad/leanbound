import LeanCert.ML.Network

/-!
# Problem 2: Neural Network Robustness - Simplified Version

The full MNIST example requires significant infrastructure, but we can demonstrate
the core verification pattern with a small network.
-/

open LeanCert.Core LeanCert.ML

/-! ## A Simple 2→2→1 Network

This mimics a small classifier:
- 2 inputs (e.g., 2D features)
- Hidden layer with 2 neurons + ReLU
- 1 output (binary classification)
-/

/-- Layer 1: Compute [x+y, x-y] -/
def layer1 : Layer where
  weights := [[1, 1], [1, -1]]
  bias := [0, 0]

/-- Layer 2: Combine hidden units -/
def layer2 : Layer where
  weights := [[1, 1]]
  bias := [0]

def simpleNet : TwoLayerNet where
  layer1 := layer1
  layer2 := layer2

/-! ## Well-formedness -/

theorem layer1_wf : layer1.WellFormed := by
  constructor
  · intro row hrow
    simp only [layer1, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem layer2_wf : layer2.WellFormed := by
  constructor
  · intro row hrow
    simp only [layer2, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem simpleNet_wf : simpleNet.WellFormed := by
  constructor
  · exact layer1_wf
  constructor
  · exact layer2_wf
  · simp only [simpleNet, layer1, layer2, Layer.inputDim, Layer.outputDim]
    rfl

/-! ## Input Region: perturbation around (0.5, 0.5) -/

def inputRegion : IntervalVector :=
  [IntervalDyadic.ofIntervalRat ⟨2/5, 3/5, by norm_num⟩ (-53),
   IntervalDyadic.ofIntervalRat ⟨2/5, 3/5, by norm_num⟩ (-53)]

/-! ## Compute output bounds -/

def outputBounds : IntervalVector :=
  TwoLayerNet.forwardInterval simpleNet inputRegion (-53)

#eval outputBounds

/-! ## Verification

The key theorem would prove that for all inputs in the region,
the output stays within bounds. This requires the full correctness
chain from the ML module.

Note: Full robustness proofs require the affine arithmetic backend
for tight bounds with correlated variables.
-/

/-! ## Summary: Neural Network Support ✓

LeanCert can:
1. Define neural networks with typed layers
2. Compute interval bounds on outputs (forward propagation)
3. Use affine arithmetic for tighter bounds on correlated paths

For full adversarial robustness verification (like MNIST), additional
infrastructure would connect this to classification decisions.
-/
