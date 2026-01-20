# Solver API

The `Solver` class is the main entry point for the Python SDK. It manages communication with the Lean kernel and handles the verification lifecycle.

## Solver Class

::: leancert.solver.Solver
    options:
      members:
        - __init__
        - find_bounds
        - find_roots
        - find_unique_root
        - verify_bound
        - integrate
        - synthesize_min_witness
        - synthesize_max_witness
        - synthesize_root_witness
        - compute_lipschitz_bound
        - diagnose_bound_failure
      show_root_heading: true
      show_source: false

## Convenience Functions

These standalone functions use a default solver instance for quick scripting.

::: leancert.solver.find_bounds

::: leancert.solver.find_roots

::: leancert.solver.find_unique_root

::: leancert.solver.verify_bound

::: leancert.solver.integrate

## Witness Synthesis

LeanCert can automatically synthesize witnesses for existential proof goals. This allows Lean to delegate witness construction to Python, which finds witnesses via optimization or root-finding and returns certificate-checked results.

### Supported Goal Forms

| Goal Form | Method | Description |
|-----------|--------|-------------|
| `∃ m, ∀ x ∈ I, f(x) ≥ m` | `synthesize_min_witness` | Find global minimum witness |
| `∃ M, ∀ x ∈ I, f(x) ≤ M` | `synthesize_max_witness` | Find global maximum witness |
| `∃ x ∈ I, f(x) = 0` | `synthesize_root_witness` | Find root existence witness |

### Example: Minimum Witness

```python
import leancert as lc

x = lc.var('x')
with lc.Solver() as solver:
    # Synthesize witness for ∃ m, ∀ x ∈ [0,1], x² ≥ m
    result = solver.synthesize_min_witness(x**2, {'x': (0, 1)})

    print(result.witness_value)   # ~0 (the minimum)
    print(result.witness_point)   # WitnessPoint(x=0.0, f=0.0)
    print(result.to_lean_tactic())  # Lean proof code
```

### Example: Root Witness

```python
import leancert as lc

x = lc.var('x')
with lc.Solver() as solver:
    # Synthesize witness for ∃ x ∈ [0.5, 1.5], x² - 1 = 0
    result = solver.synthesize_root_witness(x**2 - 1, {'x': (0.5, 1.5)})

    print(result.witness_point)   # WitnessPoint(x≈1.0, f≈0.0)
    print(result.proof_method)    # 'newton_contraction' or 'sign_change'
```

### Proof Strategy Racing

For unknown expressions, race multiple backends in parallel:

```python
config = lc.Config(race_strategies=True, timeout_ms=5000)
result = solver.synthesize_min_witness(expr, domain, config=config)
print(result.strategy_used)  # 'dyadic', 'affine', or 'rational'
```

### Incremental Refinement

Find the tightest provable bound:

```python
config = lc.Config(incremental_refinement=True)
result = solver.synthesize_max_witness(lc.exp(x), {'x': (0, 1)}, config=config)
print(result.refinement_history)  # [{bound: 2.8, status: 'verified'}, ...]
```

## Lipschitz Bounds

LeanCert can compute verified Lipschitz constants for expressions by bounding derivatives via interval arithmetic.

```python
import leancert as lc

x = lc.var('x')
with lc.Solver() as solver:
    result = solver.compute_lipschitz_bound(
        lc.sin(x),
        {'x': (0, 3.14159)}
    )

    print(result.lipschitz_bound)   # Fraction(1, 1) = 1.0
    print(result.gradient_bounds)   # {'x': Interval(-1, 1)}

    # Use for ε-δ continuity: δ = ε/L
    delta = result.delta_for_epsilon(0.01)  # 0.01
```

See [Lipschitz Bounds](lipschitz.md) for detailed documentation.

## Failure Diagnosis (CEGPR)

The `diagnose_bound_failure` method supports Counterexample-Guided Proof Refinement by analyzing why a bound verification would fail:

```python
x = lc.var('x')
with lc.Solver() as solver:
    # Try to prove exp(x) ≤ 2.5 on [0,1] - this fails!
    diagnosis = solver.diagnose_bound_failure(
        lc.exp(x), {'x': (0, 1)}, upper=2.5
    )

    if diagnosis:
        print(diagnosis.failure_type)    # 'bound_too_tight'
        print(diagnosis.margin)          # -0.218... (negative = violated)
        print(diagnosis.worst_point)     # {'x': 0.999...}
        print(diagnosis.suggested_bound) # 2.746... (would succeed)
```
