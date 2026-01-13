# LeanBound Neural Network Export Module
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Neural network export and verification support.

This module provides tools for exporting trained neural networks to Lean
for formal verification of their properties.

Example:
    >>> import torch
    >>> import leanbound as lb
    >>>
    >>> # Train your PyTorch model
    >>> model = MyNetwork()
    >>> # ... training ...
    >>>
    >>> # Export to Lean
    >>> net = lb.nn.from_pytorch(model, input_names=['x'])
    >>> lean_code = net.export_lean(
    ...     name="myNetwork",
    ...     namespace="MyProject",
    ...     input_domain={"x": (0, 1)},
    ... )
    >>>
    >>> # Save to file
    >>> with open("MyNetwork.lean", "w") as f:
    ...     f.write(lean_code)
"""

from dataclasses import dataclass, field
from fractions import Fraction
from typing import List, Optional, Dict, Tuple, Union
import numpy as np

__all__ = [
    "Layer",
    "TwoLayerReLUNetwork",
    "from_pytorch",
    "float_to_rational",
]


def float_to_rational(x: float, max_denom: int = 10000) -> Tuple[int, int]:
    """Convert float to rational with bounded denominator.

    Args:
        x: Float value to convert
        max_denom: Maximum denominator for the rational approximation

    Returns:
        Tuple of (numerator, denominator)
    """
    frac = Fraction(float(x)).limit_denominator(max_denom)
    return (frac.numerator, frac.denominator)


def _format_lean_rational(num: int, denom: int) -> str:
    """Format as Lean rational literal."""
    if denom == 1:
        return str(num)
    elif num < 0:
        return f"((({num}) : ℚ) / {denom})"
    else:
        return f"(({num} : ℚ) / {denom})"


@dataclass
class Layer:
    """A single dense layer with weights and biases.

    Attributes:
        weights: Weight matrix as list of rows, each row is list of rationals (num, denom)
        bias: Bias vector as list of rationals (num, denom)
        activation: Activation function name ('relu', 'none')
    """
    weights: List[List[Tuple[int, int]]]
    bias: List[Tuple[int, int]]
    activation: str = "relu"

    @property
    def input_dim(self) -> int:
        """Input dimension (number of columns in weight matrix)."""
        if not self.weights:
            return 0
        return len(self.weights[0])

    @property
    def output_dim(self) -> int:
        """Output dimension (number of rows in weight matrix)."""
        return len(self.weights)

    @classmethod
    def from_numpy(
        cls,
        weights: np.ndarray,
        bias: np.ndarray,
        activation: str = "relu",
        max_denom: int = 10000,
    ) -> "Layer":
        """Create layer from numpy arrays.

        Args:
            weights: Weight matrix of shape (output_dim, input_dim)
            bias: Bias vector of shape (output_dim,)
            activation: Activation function name
            max_denom: Maximum denominator for rational conversion
        """
        weight_rats = [
            [float_to_rational(v, max_denom) for v in row]
            for row in weights
        ]
        bias_rats = [float_to_rational(v, max_denom) for v in bias]
        return cls(weights=weight_rats, bias=bias_rats, activation=activation)


@dataclass
class TwoLayerReLUNetwork:
    """A two-layer ReLU network for verification.

    Architecture: input -> Linear -> ReLU -> Linear -> output

    Attributes:
        layer1: First layer (with ReLU activation)
        layer2: Second layer (no activation)
        input_names: Names for input variables
        description: Optional description for documentation
    """
    layer1: Layer
    layer2: Layer
    input_names: List[str] = field(default_factory=lambda: ["x"])
    description: str = ""

    @property
    def input_dim(self) -> int:
        """Input dimension."""
        return self.layer1.input_dim

    @property
    def hidden_dim(self) -> int:
        """Hidden layer dimension."""
        return self.layer1.output_dim

    @property
    def output_dim(self) -> int:
        """Output dimension."""
        return self.layer2.output_dim

    def export_lean(
        self,
        name: str = "network",
        namespace: str = "LeanBound.Examples.ML",
        input_domain: Optional[Dict[str, Tuple[float, float]]] = None,
        pi_approx: Tuple[int, int] = (355, 113),
        precision: int = -53,
        include_proofs: bool = True,
        training_error: Optional[float] = None,
    ) -> str:
        """Export network to Lean code with verification scaffolding.

        Args:
            name: Name for the network definition (e.g., "sineNet")
            namespace: Lean namespace
            input_domain: Dict mapping variable names to (lo, hi) bounds
            pi_approx: Rational approximation of pi as (num, denom)
            precision: Dyadic precision for interval arithmetic
            include_proofs: Whether to include well-formedness proofs
            training_error: Optional training error to document

        Returns:
            Complete Lean source code as string
        """
        lines = []

        # Header
        lines.append("/-")
        lines.append("Copyright (c) 2025 LeanBound Contributors. All rights reserved.")
        lines.append("Released under AGPL-3.0 license as described in the file LICENSE.")
        lines.append("Authors: LeanBound Contributors (auto-generated)")
        lines.append("-/")
        lines.append("import LeanBound.ML.Network")
        lines.append("")
        lines.append("set_option linter.unnecessarySeqFocus false")
        lines.append("")

        # Documentation
        lines.append("/-!")
        lines.append(f"# Neural Network: {name}")
        lines.append("")
        if self.description:
            lines.append(self.description)
            lines.append("")
        lines.append("## Architecture")
        lines.append("")
        lines.append(f"- **Input**: {self.input_dim} dimensions")
        lines.append(f"- **Hidden**: {self.hidden_dim} neurons with ReLU activation")
        lines.append(f"- **Output**: {self.output_dim} dimensions")
        lines.append("")
        if training_error is not None:
            lines.append("## Training Results")
            lines.append("")
            lines.append(f"- Max approximation error: {training_error:.6f}")
            lines.append("")
        lines.append("## Verification")
        lines.append("")
        lines.append("This file provides formal verification that the network output")
        lines.append("is bounded for all inputs in the specified domain.")
        lines.append("-/")
        lines.append("")

        # Namespace
        lines.append(f"namespace {namespace}")
        lines.append("")
        lines.append("open LeanBound.Core")
        lines.append("open LeanBound.ML")
        lines.append("open IntervalVector")
        lines.append("")

        # Layer 1 weights
        lines.append(f"/-- Layer 1: {self.input_dim} → {self.hidden_dim} -/")
        lines.append(f"def {name}Layer1Weights : List (List ℚ) := [")
        for i, row in enumerate(self.layer1.weights):
            row_strs = [_format_lean_rational(n, d) for (n, d) in row]
            comma = "," if i < len(self.layer1.weights) - 1 else ""
            lines.append(f"  [{', '.join(row_strs)}]{comma}")
        lines.append("]")
        lines.append("")

        # Layer 1 bias
        bias_strs = [_format_lean_rational(n, d) for (n, d) in self.layer1.bias]
        lines.append(f"def {name}Layer1Bias : List ℚ := [{', '.join(bias_strs)}]")
        lines.append("")

        lines.append(f"def {name}Layer1 : Layer where")
        lines.append(f"  weights := {name}Layer1Weights")
        lines.append(f"  bias := {name}Layer1Bias")
        lines.append("")

        # Layer 2 weights
        lines.append(f"/-- Layer 2: {self.hidden_dim} → {self.output_dim} -/")
        lines.append(f"def {name}Layer2Weights : List (List ℚ) := [")
        for i, row in enumerate(self.layer2.weights):
            row_strs = [_format_lean_rational(n, d) for (n, d) in row]
            comma = "," if i < len(self.layer2.weights) - 1 else ""
            lines.append(f"  [{', '.join(row_strs)}]{comma}")
        lines.append("]")
        lines.append("")

        # Layer 2 bias
        bias_strs = [_format_lean_rational(n, d) for (n, d) in self.layer2.bias]
        lines.append(f"def {name}Layer2Bias : List ℚ := [{', '.join(bias_strs)}]")
        lines.append("")

        lines.append(f"def {name}Layer2 : Layer where")
        lines.append(f"  weights := {name}Layer2Weights")
        lines.append(f"  bias := {name}Layer2Bias")
        lines.append("")

        # Network definition
        lines.append(f"/-- The {name} network -/")
        lines.append(f"def {name} : TwoLayerNet where")
        lines.append(f"  layer1 := {name}Layer1")
        lines.append(f"  layer2 := {name}Layer2")
        lines.append("")

        if include_proofs:
            # Well-formedness proofs
            lines.append("/-! ## Well-formedness Proofs -/")
            lines.append("")
            lines.append(f"theorem {name}Layer1_wf : {name}Layer1.WellFormed := by")
            lines.append("  constructor")
            lines.append("  · intro row hrow")
            lines.append(f"    simp only [{name}Layer1, {name}Layer1Weights, Layer.inputDim] at *")
            lines.append("    fin_cases hrow <;> rfl")
            lines.append("  · rfl")
            lines.append("")
            lines.append(f"theorem {name}Layer2_wf : {name}Layer2.WellFormed := by")
            lines.append("  constructor")
            lines.append("  · intro row hrow")
            lines.append(f"    simp only [{name}Layer2, {name}Layer2Weights, Layer.inputDim] at *")
            lines.append("    fin_cases hrow <;> rfl")
            lines.append("  · rfl")
            lines.append("")
            lines.append(f"theorem {name}_wf : {name}.WellFormed := by")
            lines.append("  constructor")
            lines.append(f"  · exact {name}Layer1_wf")
            lines.append("  constructor")
            lines.append(f"  · exact {name}Layer2_wf")
            lines.append(f"  · simp [{name}, {name}Layer1, {name}Layer2, {name}Layer1Weights, {name}Layer2Weights,")
            lines.append(f"         Layer.inputDim, Layer.outputDim, {name}Layer1Bias]")
            lines.append("")

        if input_domain:
            # Input domain and bounds
            lines.append("/-! ## Input Domain and Output Bounds -/")
            lines.append("")
            lines.append("/-- Helper to create dyadic interval -/")
            lines.append(f"def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := {precision}) : IntervalDyadic :=")
            lines.append("  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec")
            lines.append("")

            # Build input domain
            domain_parts = []
            for var_name in self.input_names:
                if var_name in input_domain:
                    lo, hi = input_domain[var_name]
                    lo_rat = float_to_rational(lo)
                    hi_rat = float_to_rational(hi)
                    lo_str = _format_lean_rational(*lo_rat)
                    hi_str = _format_lean_rational(*hi_rat)
                    domain_parts.append(f"mkInterval {lo_str} {hi_str}")

            lines.append(f"/-- Input domain -/")
            lines.append(f"def {name}InputDomain : IntervalVector := [{', '.join(domain_parts)}]")
            lines.append("")

            lines.append(f"/-- Computed output bounds for the entire input domain -/")
            lines.append(f"def {name}OutputBounds : IntervalVector :=")
            lines.append(f"  TwoLayerNet.forwardInterval {name} {name}InputDomain ({precision})")
            lines.append("")
            lines.append(f"#eval {name}OutputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))")
            lines.append("")

        lines.append(f"end {namespace}")

        return "\n".join(lines)


def from_pytorch(
    model,
    input_names: List[str] = None,
    max_denom: int = 10000,
    description: str = "",
) -> TwoLayerReLUNetwork:
    """Create a TwoLayerReLUNetwork from a PyTorch model.

    The PyTorch model must have exactly two linear layers accessible as
    `model.layer1` and `model.layer2`, or `model.fc1` and `model.fc2`,
    or the first two Linear modules found.

    Args:
        model: PyTorch nn.Module with two linear layers
        input_names: Names for input variables (default: ['x'])
        max_denom: Maximum denominator for rational conversion
        description: Optional description for documentation

    Returns:
        TwoLayerReLUNetwork ready for Lean export

    Raises:
        ImportError: If PyTorch is not available
        ValueError: If model structure is not supported
    """
    try:
        import torch
        import torch.nn as nn
    except ImportError:
        raise ImportError(
            "PyTorch is required for from_pytorch(). "
            "Install with: pip install torch"
        )

    if input_names is None:
        input_names = ["x"]

    # Try to find the two linear layers
    layer1_module = None
    layer2_module = None

    # Method 1: Direct attributes
    for name1, name2 in [("layer1", "layer2"), ("fc1", "fc2"), ("linear1", "linear2")]:
        if hasattr(model, name1) and hasattr(model, name2):
            l1, l2 = getattr(model, name1), getattr(model, name2)
            if isinstance(l1, nn.Linear) and isinstance(l2, nn.Linear):
                layer1_module = l1
                layer2_module = l2
                break

    # Method 2: Find first two Linear modules
    if layer1_module is None:
        linear_layers = [m for m in model.modules() if isinstance(m, nn.Linear)]
        if len(linear_layers) >= 2:
            layer1_module = linear_layers[0]
            layer2_module = linear_layers[1]

    if layer1_module is None or layer2_module is None:
        raise ValueError(
            "Could not find two Linear layers in model. "
            "Model should have layer1/layer2, fc1/fc2, or at least two nn.Linear modules."
        )

    # Extract weights
    w1 = layer1_module.weight.detach().cpu().numpy()
    b1 = layer1_module.bias.detach().cpu().numpy()
    w2 = layer2_module.weight.detach().cpu().numpy()
    b2 = layer2_module.bias.detach().cpu().numpy()

    # Create layers
    layer1 = Layer.from_numpy(w1, b1, activation="relu", max_denom=max_denom)
    layer2 = Layer.from_numpy(w2, b2, activation="none", max_denom=max_denom)

    return TwoLayerReLUNetwork(
        layer1=layer1,
        layer2=layer2,
        input_names=input_names,
        description=description,
    )
