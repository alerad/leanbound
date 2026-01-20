# Lipschitz Bounds

LeanCert can compute verified Lipschitz constants for expressions, enabling rigorous continuity proofs and error bounds.

## Overview

A function `f` is **Lipschitz continuous** with constant `L` if:

$$|f(x) - f(y)| \leq L \cdot |x - y|$$

for all `x, y` in the domain. LeanCert computes `L` by bounding the derivative:

$$L = \sup_{x \in I} |f'(x)|$$

This is justified by the **Mean Value Theorem**: for differentiable `f`, there exists `c` between `x` and `y` such that `f(x) - f(y) = f'(c)(x - y)`.

## Computing Lipschitz Bounds

```python
import leancert as lc

x = lc.var('x')
with lc.Solver() as solver:
    result = solver.compute_lipschitz_bound(
        lc.sin(x),
        {'x': (0, 3.14159)}
    )

    print(result.lipschitz_bound)   # 1.0 (since |cos(x)| ≤ 1)
    print(result.gradient_bounds)   # {'x': Interval(-1, 1)}
```

## LipschitzResult

The `LipschitzResult` dataclass contains:

| Field | Type | Description |
|-------|------|-------------|
| `lipschitz_bound` | `Fraction` | Verified Lipschitz constant L |
| `gradient_bounds` | `dict[str, Interval]` | Derivative bounds per variable |
| `certificate` | `Certificate` | Lean-verifiable proof data |

### Methods

#### `delta_for_epsilon(epsilon: float) -> float`

Compute the δ that guarantees ε-δ continuity:

```python
result = solver.compute_lipschitz_bound(expr, domain)

# For any ε, this δ guarantees |f(x) - f(a)| < ε when |x - a| < δ
delta = result.delta_for_epsilon(0.001)  # δ = ε/L
```

#### `to_lean_tactic() -> str`

Generate Lean proof code:

```python
print(result.to_lean_tactic())
# Output:
# -- Lipschitz bound for sin(x) on [0, π]
# -- L = 1, derived from |∂f/∂x| ≤ 1
# apply lipschitz_continuous_of_bound
# · exact 1
# · interval_deriv_bound
```

## Multivariate Functions

For multivariate functions, the Lipschitz constant is derived from the gradient norm:

$$L = \sup_{x \in I} \|\nabla f(x)\|_\infty = \max_i \sup_{x \in I} |\partial f / \partial x_i|$$

```python
x, y = lc.var('x'), lc.var('y')
expr = x**2 + y**2

result = solver.compute_lipschitz_bound(
    expr,
    {'x': (-1, 1), 'y': (-1, 1)}
)

print(result.gradient_bounds)
# {'x': Interval(-2, 2), 'y': Interval(-2, 2)}
print(result.lipschitz_bound)  # 2.0 (max of |2x|, |2y| over domain)
```

## Applications

### 1. Continuity Proofs (ε-δ)

The primary use case is proving continuity:

```python
from leancert.quantifier import QuantifierSynthesizer

synth = QuantifierSynthesizer(solver)
result = synth.epsilon_delta(
    lc.exp(x),
    var='x',
    point=0.0,
    domain=(-1, 1)
)
# Uses Lipschitz bound L=e to derive δ=ε/e
```

### 2. Error Propagation

Bound how input errors affect outputs:

```python
result = solver.compute_lipschitz_bound(expr, domain)
L = float(result.lipschitz_bound)

input_error = 1e-6
output_error_bound = L * input_error
```

### 3. Numerical Stability Analysis

Verify that small perturbations produce small changes:

```python
# Check if neural network output is stable
result = solver.compute_lipschitz_bound(nn_expr, input_bounds)
if result.lipschitz_bound < 10:
    print("Network is reasonably stable")
```

## How It Works

1. **Symbolic Differentiation**: The expression AST is differentiated symbolically
2. **Interval Evaluation**: Derivative bounds are computed via interval arithmetic
3. **Lipschitz Extraction**: `L = max(|lo|, |hi|)` for each gradient component
4. **Certificate Generation**: The Lean kernel verifies the derivative bounds

The Lean bridge exposes this via the `deriv_interval` method:

```python
# Low-level access (usually use compute_lipschitz_bound instead)
result = client.deriv_interval(expr_json, box_json, taylor_depth=10)
# Returns: {'gradients': [...], 'lipschitz_bound': '3/2'}
```

## Configuration

```python
config = lc.Config(
    taylor_depth=20,  # Higher depth = tighter derivative bounds
)
result = solver.compute_lipschitz_bound(expr, domain, config=config)
```

## See Also

- [Quantifier Synthesis](quantifier.md) - Uses Lipschitz bounds for ε-δ proofs
- [Golden Theorems](../architecture/golden-theorems.md) - Theoretical foundations
