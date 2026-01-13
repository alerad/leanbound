"""Tests for neural network export module."""

import pytest
import numpy as np
from fractions import Fraction

from leanbound.nn import (
    Layer,
    TwoLayerReLUNetwork,
    float_to_rational,
)


class TestFloatToRational:
    def test_integer(self):
        assert float_to_rational(5.0) == (5, 1)
        assert float_to_rational(-3.0) == (-3, 1)

    def test_simple_fraction(self):
        assert float_to_rational(0.5) == (1, 2)
        assert float_to_rational(0.25) == (1, 4)

    def test_bounded_denominator(self):
        # pi should be approximated
        num, denom = float_to_rational(3.14159265, max_denom=1000)
        approx = num / denom
        assert abs(approx - 3.14159265) < 0.001


class TestLayer:
    def test_from_numpy(self):
        weights = np.array([[1.0, 2.0], [3.0, 4.0]])
        bias = np.array([0.5, -0.5])

        layer = Layer.from_numpy(weights, bias, activation="relu")

        assert layer.input_dim == 2
        assert layer.output_dim == 2
        assert layer.activation == "relu"
        assert len(layer.weights) == 2
        assert len(layer.bias) == 2

    def test_dimensions(self):
        weights = [[(1, 1), (2, 1), (3, 1)], [(4, 1), (5, 1), (6, 1)]]
        bias = [(0, 1), (1, 1)]
        layer = Layer(weights=weights, bias=bias)

        assert layer.input_dim == 3
        assert layer.output_dim == 2


class TestTwoLayerReLUNetwork:
    @pytest.fixture
    def simple_network(self):
        # 2 -> 3 -> 1 network
        layer1 = Layer(
            weights=[[(1, 1), (0, 1)], [(0, 1), (1, 1)], [(1, 2), (1, 2)]],
            bias=[(0, 1), (0, 1), (0, 1)],
            activation="relu",
        )
        layer2 = Layer(
            weights=[[(1, 1), (1, 1), (1, 1)]],
            bias=[(0, 1)],
            activation="none",
        )
        return TwoLayerReLUNetwork(
            layer1=layer1,
            layer2=layer2,
            input_names=["x", "y"],
        )

    def test_dimensions(self, simple_network):
        assert simple_network.input_dim == 2
        assert simple_network.hidden_dim == 3
        assert simple_network.output_dim == 1

    def test_export_lean_basic(self, simple_network):
        code = simple_network.export_lean(
            name="testNet",
            namespace="Test.ML",
            include_proofs=False,
        )

        assert "namespace Test.ML" in code
        assert "def testNet : TwoLayerNet" in code
        assert "testNetLayer1Weights" in code
        assert "testNetLayer2Weights" in code

    def test_export_lean_with_proofs(self, simple_network):
        code = simple_network.export_lean(
            name="testNet",
            namespace="Test.ML",
            include_proofs=True,
        )

        assert "theorem testNetLayer1_wf" in code
        assert "theorem testNetLayer2_wf" in code
        assert "theorem testNet_wf" in code

    def test_export_lean_with_domain(self, simple_network):
        code = simple_network.export_lean(
            name="testNet",
            namespace="Test.ML",
            input_domain={"x": (0, 1), "y": (-1, 1)},
        )

        assert "testNetInputDomain" in code
        assert "testNetOutputBounds" in code
        assert "mkInterval" in code


class TestFromPytorch:
    @pytest.fixture
    def skip_if_no_torch(self):
        pytest.importorskip("torch")

    def test_from_pytorch_simple(self, skip_if_no_torch):
        import torch
        import torch.nn as nn
        from leanbound.nn import from_pytorch

        class SimpleNet(nn.Module):
            def __init__(self):
                super().__init__()
                self.layer1 = nn.Linear(2, 4)
                self.layer2 = nn.Linear(4, 1)

            def forward(self, x):
                return self.layer2(torch.relu(self.layer1(x)))

        model = SimpleNet()
        net = from_pytorch(model, input_names=["a", "b"])

        assert net.input_dim == 2
        assert net.hidden_dim == 4
        assert net.output_dim == 1
        assert net.input_names == ["a", "b"]

    def test_from_pytorch_fc_naming(self, skip_if_no_torch):
        import torch
        import torch.nn as nn
        from leanbound.nn import from_pytorch

        class FCNet(nn.Module):
            def __init__(self):
                super().__init__()
                self.fc1 = nn.Linear(3, 5)
                self.fc2 = nn.Linear(5, 2)

            def forward(self, x):
                return self.fc2(torch.relu(self.fc1(x)))

        model = FCNet()
        net = from_pytorch(model)

        assert net.input_dim == 3
        assert net.hidden_dim == 5
        assert net.output_dim == 2
