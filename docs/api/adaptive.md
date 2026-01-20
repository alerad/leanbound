# Adaptive Verification

The `adaptive` module provides domain splitting strategies and proof assembly for verifying complex expressions that fail on the full domain.

## Overview

When interval arithmetic over a large domain produces bounds that are too loose, **adaptive verification** splits the domain into smaller regions, verifies each independently, and assembles a combined proof.

```python
import leancert as lc
from leancert.adaptive import AdaptiveVerifier

x = lc.var('x')
with lc.Solver() as solver:
    verifier = AdaptiveVerifier(solver)

    # May need splitting to prove tight bound
    result = verifier.verify_bound(
        lc.sin(x) * lc.cos(x),
        {'x': (0, 6.28)},
        upper=0.5
    )

    print(result.verified)          # True
    print(result.num_subdivisions)  # 4
    print(result.proof_tree)        # Hierarchical proof structure
```

## When to Use Adaptive Verification

Use adaptive verification when:

1. **Tight bounds fail** - The expression's true range is close to the bound you're proving
2. **Large domains** - Interval arithmetic accumulates overestimation over wide intervals
3. **Oscillating functions** - Functions like `sin`, `cos` need subdivision to capture behavior
4. **Near-boundary behavior** - Values approach the bound only in small regions

## Splitting Strategies

### Bisection (Default)

Recursively splits the domain in half along each dimension:

```python
result = verifier.verify_bound(
    expr, domain, upper=bound,
    strategy='bisection',
    max_depth=10
)
```

### Algebraic Splitting

Splits at algebraically significant points (roots, critical points):

```python
result = verifier.verify_bound(
    expr, domain, upper=bound,
    strategy='algebraic'
)
# Automatically finds roots of derivatives to split at extrema
```

### Adaptive Heuristics

Automatically chooses split points based on where verification fails:

```python
result = verifier.verify_bound(
    expr, domain, upper=bound,
    strategy='adaptive'
)
# Concentrates subdivisions where the bound is nearly violated
```

## Proof Assembly

After verifying all subdomains, the proofs are assembled into a single certificate:

```python
result = verifier.verify_bound(expr, domain, upper=bound)

# Access the proof tree
for node in result.proof_tree.leaves():
    print(f"Subdomain {node.domain}: verified with bound {node.bound}")

# Generate combined Lean proof
print(result.to_lean_tactic())
# Output:
# apply bound_of_union
# · -- Subdomain [0, π]
#   interval_bound
# · -- Subdomain [π, 2π]
#   interval_bound
```

## Configuration

```python
from leancert.adaptive import AdaptiveConfig

config = AdaptiveConfig(
    max_depth=15,           # Maximum subdivision depth
    min_width=1e-10,        # Stop subdividing below this width
    parallel=True,          # Verify subdomains in parallel
    early_stop=True,        # Stop when counterexample found
    taylor_depth=12,        # Interval arithmetic precision
)

result = verifier.verify_bound(expr, domain, upper=bound, config=config)
```

## Multivariate Domains

For multivariate functions, splitting occurs along all dimensions:

```python
x, y = lc.var('x'), lc.var('y')
expr = x**2 + y**2 - x*y

result = verifier.verify_bound(
    expr,
    {'x': (-1, 1), 'y': (-1, 1)},
    upper=3.0
)

print(result.num_subdivisions)  # May split into 4x4 = 16 regions
```

## Expansion Heuristics

When verification fails near domain boundaries, **expansion heuristics** slightly widen the domain to check if the bound is genuinely violated or just needs more precision:

```python
result = verifier.verify_bound(
    expr, domain, upper=bound,
    expansion_factor=1.01  # Expand by 1% for boundary checks
)

if result.boundary_sensitive:
    print("Bound nearly violated at boundary")
    print(result.critical_points)
```

## Integration with Quantifier Synthesis

Adaptive verification is used internally by quantifier synthesis:

```python
from leancert.quantifier import QuantifierSynthesizer

synth = QuantifierSynthesizer(solver)

# forall_bound uses adaptive verification automatically
result = synth.forall_bound(expr, domain, upper=bound)
```

## Performance Tips

1. **Start with low `max_depth`** - Increase only if verification fails
2. **Use `algebraic` strategy** for functions with known structure
3. **Enable `parallel=True`** for large domains
4. **Check `result.num_subdivisions`** - High counts suggest the bound is too tight

## Result Structure

| Field | Type | Description |
|-------|------|-------------|
| `verified` | `bool` | Whether the bound was proven |
| `num_subdivisions` | `int` | Total subdomains verified |
| `max_depth_reached` | `int` | Deepest subdivision level |
| `proof_tree` | `ProofTree` | Hierarchical proof structure |
| `counterexample` | `dict` | Point violating bound (if failed) |
| `timing_ms` | `float` | Total verification time |

## See Also

- [Quantifier Synthesis](quantifier.md) - High-level synthesis using adaptive verification
- [Solver API](solver.md) - Low-level verification methods
- [Troubleshooting](../troubleshooting.md) - Common verification failures
