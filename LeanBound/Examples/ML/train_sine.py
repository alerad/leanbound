#!/usr/bin/env python3
"""
Train a neural network to approximate sin(x) on [0, π] using PyTorch.
Export to Lean for formal verification using the LeanBound SDK.

Usage:
    python train_sine.py

This demonstrates the LeanBound ML verification workflow:
1. Train a neural network in PyTorch
2. Export to Lean with exact rational weights
3. Generate formal verification scaffolding
"""

import sys
sys.path.insert(0, "/Users/yales/workspace/leanbound/python")

import torch
import torch.nn as nn
import numpy as np

import leanbound as lb


class SineNet(nn.Module):
    """Simple ReLU network: 1 → 16 → 1"""
    def __init__(self):
        super().__init__()
        self.layer1 = nn.Linear(1, 16)
        self.layer2 = nn.Linear(16, 1)
        self.relu = nn.ReLU()

    def forward(self, x):
        x = self.relu(self.layer1(x))
        x = self.layer2(x)
        return x


def train_model():
    print("=" * 60)
    print("Training Sine Approximator with PyTorch")
    print("=" * 60)

    # Set seed for reproducibility
    torch.manual_seed(42)
    np.random.seed(42)

    # Create model
    model = SineNet()

    # Training data: sin(x) on [0, π]
    n_samples = 1000
    X = torch.linspace(0, np.pi, n_samples).reshape(-1, 1)
    y = torch.sin(X)

    print(f"\nArchitecture: 1 → 16 → 1 (ReLU)")
    print(f"Training samples: {n_samples}")

    # Training setup
    criterion = nn.MSELoss()
    optimizer = torch.optim.Adam(model.parameters(), lr=0.01)
    scheduler = torch.optim.lr_scheduler.StepLR(optimizer, step_size=2000, gamma=0.5)

    # Train
    print("\nTraining...")
    epochs = 10000
    for epoch in range(epochs):
        optimizer.zero_grad()
        pred = model(X)
        loss = criterion(pred, y)
        loss.backward()
        optimizer.step()
        scheduler.step()

        if epoch % 1000 == 0:
            print(f"  Epoch {epoch:5d}, Loss: {loss.item():.6f}, LR: {scheduler.get_last_lr()[0]:.6f}")

    print(f"  Epoch {epochs:5d}, Loss: {loss.item():.6f}")

    return model


def evaluate_model(model):
    print("\n" + "=" * 60)
    print("Evaluation")
    print("=" * 60)

    model.eval()
    with torch.no_grad():
        X_test = torch.linspace(0, np.pi, 100).reshape(-1, 1)
        y_test = torch.sin(X_test)
        pred = model(X_test)

        errors = torch.abs(pred - y_test)
        max_error = errors.max().item()
        mean_error = errors.mean().item()

        print(f"Max approximation error: {max_error:.6f}")
        print(f"Mean approximation error: {mean_error:.6f}")

        # Check specific points
        for x_val, name in [(0, "0"), (np.pi/2, "π/2"), (np.pi, "π")]:
            x_t = torch.tensor([[x_val]], dtype=torch.float32)
            pred_val = model(x_t).item()
            true_val = np.sin(x_val)
            print(f"  Network({name}) = {pred_val:.4f}, sin({name}) = {true_val:.4f}, error = {abs(pred_val - true_val):.4f}")

    return max_error


def export_to_lean(model, max_error):
    """Export model to Lean using the LeanBound SDK."""
    print("\n" + "=" * 60)
    print("Exporting to Lean via LeanBound SDK")
    print("=" * 60)

    # Convert PyTorch model to LeanBound network
    net = lb.nn.from_pytorch(
        model,
        input_names=["x"],
        max_denom=10000,
        description="""This file demonstrates **end-to-end verified ML**:

1. A neural network was trained in PyTorch to approximate sin(x)
2. Weights were exported as exact rational numbers
3. We formally verify output bounds using interval arithmetic

## Key Point: Formal Verification vs Testing

Unlike testing (which checks finitely many points), formal verification proves
properties for ALL inputs in a region. This is a mathematical proof covering
infinitely many inputs - not sampling.
""",
    )

    # Generate Lean code
    lean_code = net.export_lean(
        name="sineNet",
        namespace="LeanBound.Examples.ML.SineApprox",
        input_domain={"x": (0, 355/113)},  # [0, π]
        precision=-53,
        include_proofs=True,
        training_error=max_error,
    )

    # Add custom sections that the basic export doesn't include
    lean_code = _add_custom_sections(lean_code, net)

    return lean_code


def _add_custom_sections(lean_code: str, net) -> str:
    """Add custom verification theorem and documentation."""
    # Find the end namespace line and insert before it
    end_marker = "end LeanBound.Examples.ML.SineApprox"

    custom_code = '''
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

'''

    lean_code = lean_code.replace(end_marker, custom_code + end_marker)
    return lean_code


def main():
    # Train model
    model = train_model()

    # Evaluate
    max_error = evaluate_model(model)

    # Export to Lean using SDK
    lean_code = export_to_lean(model, max_error)
    output_path = "/Users/yales/workspace/leanbound/LeanBound/Examples/ML/SineApprox.lean"

    with open(output_path, "w") as f:
        f.write(lean_code)

    print(f"\nGenerated: {output_path}")

    # Print weight stats
    print("\n" + "=" * 60)
    print("Weight Statistics")
    print("=" * 60)
    for name, param in model.named_parameters():
        print(f"  {name}: shape={list(param.shape)}, range=[{param.min().item():.4f}, {param.max().item():.4f}]")

    print("\n" + "=" * 60)
    print("Next Steps")
    print("=" * 60)
    print("1. Build with: lake build LeanBound.Examples.ML.SineApprox")
    print("2. The theorem `output_bounded` proves bounds for ALL inputs in [0, π]")


if __name__ == "__main__":
    main()
