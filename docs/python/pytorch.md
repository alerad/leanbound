# PyTorch Export

Export trained PyTorch models to Lean for formal verification.

## Overview

LeanCert can verify properties of neural networks, but first you need to convert your PyTorch model to Lean's representation. The `leancert.nn` module handles this conversion.

## Quick Example

```python
import torch
import torch.nn as nn
import leancert as lc

# Your trained PyTorch model
class MyNetwork(nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(2, 4)
        self.fc2 = nn.Linear(4, 1)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        return self.fc2(x)

model = MyNetwork()
model.load_state_dict(torch.load("model.pt"))

# Convert to LeanCert
net = lf.nn.from_pytorch(model, input_names=['x1', 'x2'])

# Export to Lean code
lean_code = net.export_lean(
    name="myNetwork",
    namespace="MyProject.Networks",
)

print(lean_code)
```

## Output

The exported Lean code looks like:

```lean
import LeanCert.ML.Network

namespace MyProject.Networks

def myNetwork : List Layer := [
  { weights := [[1/2, -3/4], [1/8, 5/16], ...],
    bias := [1/32, -1/64, ...] },
  { weights := [[7/8, -1/2, 3/4, 1/4]],
    bias := [0] }
]

end MyProject.Networks
```

## API Reference

### `from_pytorch`

```python
lf.nn.from_pytorch(
    model: nn.Module,
    input_names: List[str],
    max_denominator: int = 1000
) -> Network
```

**Parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `model` | `nn.Module` | Trained PyTorch model |
| `input_names` | `List[str]` | Names for input variables |
| `max_denominator` | `int` | Max denominator for rational approximation |

**Supported layers:**
- `nn.Linear`
- `nn.ReLU`
- `nn.Sigmoid` (converted to interval bounds)

### `export_lean`

```python
net.export_lean(
    name: str,
    namespace: str = "LeanCert.Examples",
    include_imports: bool = True
) -> str
```

**Parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `name` | `str` | Lean definition name |
| `namespace` | `str` | Lean namespace |
| `include_imports` | `bool` | Include import statements |

### `Layer.from_numpy`

For direct NumPy array import:

```python
import numpy as np

weights = np.array([[1.0, -0.5], [0.25, 0.75]])
bias = np.array([0.1, -0.2])

layer = lf.nn.Layer.from_numpy(weights, bias, max_denominator=100)
```

## Rational Approximation

Neural network weights are floats, but Lean verification uses exact rationals. LeanCert approximates each weight as a fraction:

```python
# float 0.333... becomes 1/3
# float 0.142857... becomes 1/7
```

The `max_denominator` parameter controls precision:

| `max_denominator` | Precision | Verification Speed |
|-------------------|-----------|-------------------|
| 100 | Low | Fast |
| 1000 | Medium | Medium |
| 10000 | High | Slow |

**Tip:** Start with `max_denominator=100` for quick verification, increase if bounds are too loose.

## Verification Workflow

```python
# 1. Export model
net = lf.nn.from_pytorch(model, ['x'])
lean_code = net.export_lean(name="classifier")

# 2. Save to file
with open("MyNetwork.lean", "w") as f:
    f.write(lean_code)

# 3. In Lean, verify properties
```

```lean
-- MyNetwork.lean (generated)
import LeanCert.ML.Network

def classifier : List Layer := [...]

-- Verify robustness
theorem classifier_robust :
    ∀ x ∈ inputDomain, ∀ δ ∈ perturbation,
    classifier.forward (x + δ) = classifier.forward x := by
  -- Use interval propagation
  native_decide
```

## Supported Architectures

| Architecture | Support |
|--------------|---------|
| Feedforward (MLP) | Full |
| Convolutional | Flatten first |
| RNN/LSTM | Not supported |
| Transformer | Manual conversion |

For transformers, use the `LeanCert.ML.Transformer` module directly in Lean.

## Example: MNIST Classifier

```python
import torch
import torch.nn as nn
import leancert as lc

class MNISTNet(nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(784, 128)
        self.fc2 = nn.Linear(128, 10)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        return self.fc2(x)

# Load trained model
model = MNISTNet()
model.load_state_dict(torch.load("mnist.pt"))

# Export with reasonable precision
net = lf.nn.from_pytorch(
    model,
    input_names=[f'pixel_{i}' for i in range(784)],
    max_denominator=1000
)

# Generate Lean code
lean_code = net.export_lean(
    name="mnistClassifier",
    namespace="MNIST"
)

# Save
with open("MNISTClassifier.lean", "w") as f:
    f.write(lean_code)
```

## Limitations

1. **Float precision**: Rational approximation introduces small errors. Verify that `max_denominator` is sufficient for your use case.

2. **Large models**: Models with millions of parameters generate large Lean files. Consider verifying critical subnetworks.

3. **Activations**: Only ReLU and Sigmoid are directly supported. Other activations need manual interval implementations.
