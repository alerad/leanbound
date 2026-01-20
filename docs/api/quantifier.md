# Quantifier Synthesis

The `quantifier` module provides verified witness synthesis for quantified mathematical statements. All witnesses are validated through the Lean kernel, ensuring soundness.

## Overview

Quantifier synthesis automates the construction of witnesses for common proof patterns:

```python
import leancert as lc
from leancert.quantifier import QuantifierSynthesizer

x = lc.var('x')
with lc.Solver() as solver:
    synth = QuantifierSynthesizer(solver)

    # Prove ∀ x ∈ [0, 6], 1 + sin(x) ≥ 0
    result = synth.forall_sign(1 + lc.sin(x), {'x': (0, 6)}, sign='non_negative')
    print(result.success)  # True
```

## Supported Patterns

| Pattern | Goal Form | Method | Verification |
|---------|-----------|--------|--------------|
| `FORALL_SIGN` | `∀ x ∈ I, f(x) ≥ 0` | `forall_sign()` | Interval arithmetic |
| `EXISTS_ROOT` | `∃ x ∈ I, f(x) = 0` | `exists_root()` | Root finding |
| `EXISTS_FORALL_BOUND` | `∃ M, ∀ x ∈ I, \|f(x)\| ≤ M` | `exists_forall_bound()` | Global optimization |
| `MINIMUM_WITNESS` | `∃ m, ∀ x ∈ I, f(x) ≥ m` | `minimum_witness()` | Global optimization |
| `MAXIMUM_WITNESS` | `∃ M, ∀ x ∈ I, f(x) ≤ M` | `maximum_witness()` | Global optimization |
| `EPSILON_DELTA` | `∀ ε>0, ∃ δ>0, \|x-a\|<δ → \|f(x)-L\|<ε` | `epsilon_delta()` | Lipschitz bounds |

## Pattern Details

### FORALL_SIGN - Universal Sign Conditions

Proves that a function maintains a sign condition over an entire interval.

```python
# Prove ∀ x ∈ [0, 6], 1 + sin(x) ≥ 0
result = synth.forall_sign(
    1 + lc.sin(x),
    {'x': (0, 6)},
    sign='non_negative'  # or 'positive', 'negative', 'non_positive'
)

print(result.success)     # True
print(result.lean_proof)  # Lean proof code
```

**How it works**: Uses interval arithmetic to compute rigorous bounds over the domain. The Lean kernel verifies that the interval satisfies the sign condition.

**Note**: For tight bounds (like `sin(x) ≥ 0` on `[0, π]`), interval arithmetic may be too conservative. Use adaptive verification for such cases.

### EXISTS_ROOT - Existential Root Witnesses

Proves existence of a root by finding a concrete witness.

```python
# Prove ∃ x ∈ [1, 2], x² - 2 = 0 (i.e., √2 exists)
result = synth.exists_root(
    x**2 - 2,
    {'x': (1, 2)}
)

print(result.success)     # True
print(result.witnesses)   # [Witness(value={'x': 1.414...}, ...)]
```

**How it works**: Uses bisection or Newton's method to locate a root, then verifies via interval evaluation that a sign change occurs.

### MINIMUM_WITNESS - Global Minimum

Synthesizes a verified lower bound witness.

```python
# Prove ∃ m, ∀ x ∈ [0, 2π], cos(x) ≥ m
result = synth.minimum_witness(
    lc.cos(x),
    {'x': (0, 6.28318)}
)

print(result.success)              # True
print(result.witnesses[0].value)   # {'x': 3.14159} (point where min achieved)
print(result.witnesses[0].rigorous_bounds)  # Interval[-1, 0]
```

**How it works**: Calls `solver.synthesize_min_witness()` which uses verified branch-and-bound optimization. The witness includes both the minimum value and the point where it's achieved.

### MAXIMUM_WITNESS - Global Maximum

Synthesizes a verified upper bound witness.

```python
# Prove ∃ M, ∀ x ∈ [0, 1], exp(x) ≤ M
result = synth.maximum_witness(
    lc.exp(x),
    {'x': (0, 1)}
)

print(result.success)              # True
print(result.witnesses[0].value)   # {'x': 1.0}
print(result.witnesses[0].rigorous_bounds)  # Interval containing e
```

### EXISTS_FORALL_BOUND - Absolute Bound Witness

Proves existence of an absolute bound over the domain.

```python
# Prove ∃ M, ∀ x ∈ [-1, 1], |sin(x)| ≤ M
result = synth.exists_forall_bound(
    lc.sin(x),
    {'x': (-1, 1)},
    abs_bound=True
)

print(result.success)     # True
print(result.witnesses)   # Contains the bound M
```

### EPSILON_DELTA - Continuity Proofs

Proves continuity at a point via the ε-δ definition using Lipschitz bounds.

```python
# Prove sin is continuous at x=0 with limit 0:
# ∀ ε > 0, ∃ δ > 0, |x - 0| < δ → |sin(x) - 0| < ε
result = synth.epsilon_delta(
    lc.sin(x),
    variable='x',
    point=0.0,
    limit=0.0,  # sin(0) = 0
    neighborhood_radius=1.0
)

print(result.success)     # True
print(result.message)     # 'VERIFIED: Lipschitz L=1.000000, δ=ε/L for 3 ε values'
print(result.witnesses)   # [Witness(value=0.1, variable='δ(ε=0.1)', ...), ...]
```

**How it works**: Computes a verified Lipschitz constant `L` via derivative bounds (see [Lipschitz Bounds](lipschitz.md)). Then `δ = ε/L` satisfies the continuity condition by the Mean Value Theorem.

## Result Structure

All methods return a `QuantifierResult`:

```python
@dataclass
class QuantifierResult:
    pattern: QuantifierPattern    # Which pattern was used
    success: bool                 # Whether synthesis succeeded
    witnesses: list[Witness]      # Synthesized witnesses
    lean_proof: Optional[str]     # Generated Lean proof code
    message: str                  # Human-readable status
    certificate: Optional[Certificate]  # Verification certificate
```

Each `Witness` contains:

```python
@dataclass
class Witness:
    value: Union[float, dict[str, float]]  # Witness value or point
    variable: str                           # Variable name
    witness_type: str                       # 'point', 'bound', etc.
    rigorous_bounds: Optional[Interval]     # Verified interval bounds
    certificate: Optional[Certificate]      # Lean-verifiable proof data
```

## Proof Generation

All synthesis methods generate Lean-compatible proof code:

```python
result = synth.minimum_witness(x**2 - 2*x + 1, {'x': (0, 2)})

print(result.lean_proof)
# Output:
# -- Auto-synthesized minimum witness
# -- Witness value: 0.0000000000
# -- Achieved at: x = 1.000000
# ...
```

## Error Handling

When synthesis fails, check the result:

```python
result = synth.forall_sign(lc.sin(x), {'x': (0, 4)}, sign='positive')

if not result.success:
    print(result.message)  # Explains why it failed
```

## See Also

- [Lipschitz Bounds](lipschitz.md) - How ε-δ proofs derive δ from Lipschitz constants
- [Adaptive Verification](adaptive.md) - Domain splitting for complex expressions
- [Solver API](solver.md) - Low-level witness synthesis methods
