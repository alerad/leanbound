# LeanCert

**Verified numerical computation and bound certification for Lean 4.**

LeanCert automates proofs of inequalities, global extrema, root existence, and integration bounds using rigorous interval arithmetic and Taylor models. Unlike standard numerical libraries that provide approximations, LeanCert produces **formal proofs**.

## Key Features

- **Rigorous Interval Arithmetic**: Computable bounds with formal correctness proofs
- **Kernel-Only Verification**: `certify_kernel` tactic uses `decide` for proofs trusted only by the Lean kernel
- **Global Optimization**: Branch-and-bound with verified lower/upper bounds
- **Root Finding**: Existence proofs (bisection) and uniqueness proofs (Newton contraction)
- **Integration**: Verified Riemann sum bounds
- **Neural Network Verification**: Interval propagation with DeepPoly relaxations
- **Transformer Verification**: Multi-Head Attention, LayerNorm, GELU soundness proofs
- **Counter-Example Search**: `interval_refute` finds where conjectured bounds fail
- **Quantifier Synthesis**: Verified witnesses for `∀`, `∃`, min/max, and ε-δ continuity
- **Lipschitz Bounds**: Derivative-based continuity certificates via Mean Value Theorem
- **Adaptive Verification**: Domain splitting and proof assembly for complex expressions
- **Python SDK**: High-level API with symbolic simplification and false-positive filtering

## Quick Example

### Python

```python
import leancert as lc

x = lc.var('x')
expr = x**2 + lc.sin(x)

# Find rigorous bounds on [0, 1]
result = lc.find_bounds(expr, {'x': (0, 1)})
print(f"Bounds: [{result.min_bound}, {result.max_bound}]")

# Prove root existence
roots = lc.find_roots(x**2 - 2, {'x': (1, 2)})
```

### Lean

```lean
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.Discovery

open LeanCert.Core

-- Prove bounds using natural Set.Icc syntax
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by certify_bound 15
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by certify_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by certify_bound

-- Prove root existence (√2) via sign change
def I12 : IntervalRat := ⟨1, 2, by norm_num⟩
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

## Architecture

LeanCert operates on a **certificate-driven architecture**:

1. **Reification**: Mathematical expressions are converted to an AST (`LeanCert.Core.Expr`)
2. **Computation**: Algorithms run on the AST using interval arithmetic
3. **Certification**: Golden theorems lift boolean results to semantic proofs about real numbers

This separation allows efficient computation while maintaining full formal verification.

**Two Backends**: LeanCert includes both rational (`evalIntervalCore`) and dyadic (`evalIntervalDyadic`) interval arithmetic. The dyadic backend is essential for deep expressions like neural networks, where rational denominators would explode exponentially.

## Installation

### Lean

Add to your `lakefile.toml`:

```toml
[[require]]
name = "leancert"
git = "https://github.com/alerad/leancert"
rev = "main"
```

### Python

```bash
cd python
pip install -e .
```

## Documentation

| Guide | Description |
|-------|-------------|
| [Quickstart](quickstart.md) | Get started with Python SDK and Lean tactics |
| [Discovery Mode](discovery.md) | Interactive exploration: `#find_min`, `#bounds`, witnesses |
| [Tactics Reference](tactics.md) | Complete reference for all tactics |
| [Choosing Tactics](choosing-tactics.md) | Decision flowchart for picking the right tactic |
| [Troubleshooting](troubleshooting.md) | Common errors and how to fix them |
| [End-to-End Example](end-to-end-example.md) | Full workflow from exploration to proof |

### API Reference

| Document | Description |
|----------|-------------|
| [Solver API](api/solver.md) | Core verification methods |
| [Quantifier Synthesis](api/quantifier.md) | Verified `∀`/`∃` witnesses |
| [Lipschitz Bounds](api/lipschitz.md) | Derivative-based continuity |
| [Adaptive Verification](api/adaptive.md) | Domain splitting strategies |

### Architecture

| Document | Description |
|----------|-------------|
| [Golden Theorems](architecture/golden-theorems.md) | How computation connects to proofs |
| [Verification Status](architecture/verification-status.md) | What's proven, what's WIP |

## What's Verified?

The core interval arithmetic, Taylor series bounds, global optimization, root finding, and integration are **fully proved** with no `sorry`. See [Verification Status](architecture/verification-status.md) for details.
