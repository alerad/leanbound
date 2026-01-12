# LeanBound

Verified numerical computation and bound certification for Lean 4.

LeanBound automates proofs of inequalities, global extrema, root existence, and integration bounds using rigorous interval arithmetic and Taylor models. Unlike standard numerical libraries that provide approximations, LeanBound produces formal proofs.

## Overview

LeanBound operates on a certificate-driven architecture:

1. **Reification**: Mathematical expressions are converted to an AST (`LeanBound.Core.Expr`)
2. **Computation**: Algorithms run on the AST using rational interval arithmetic
3. **Certification**: Golden theorems lift boolean results to semantic proofs about real numbers

This separation allows efficient computation while maintaining full formal verification.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "leanbound"
git = "https://github.com/alerad/leanbound"
rev = "main"
```

Then run `lake update`.

## Usage

### Tactics

```lean
import LeanBound.Tactic.IntervalAuto
import LeanBound.Tactic.Discovery

open LeanBound.Core

-- Prove bounds on transcendentals using natural Set.Icc syntax
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by interval_bound 15
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by interval_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by interval_bound

-- Or with explicit IntervalRat for more control
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

example : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by interval_bound 15

-- Prove root existence (√2) via sign change
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

### Direct API

```lean
import LeanBound.Numerics.Certificate

open LeanBound.Core LeanBound.Numerics LeanBound.Numerics.Certificate

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def exprExp : Expr := Expr.exp (Expr.var 0)
def exprExp_core : ExprSupportedCore exprExp :=
  ExprSupportedCore.exp (ExprSupportedCore.var 0)

-- Using the certificate API directly
theorem exp_bounded : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ (3 : ℚ) :=
  verify_upper_bound exprExp exprExp_core I01 3 { taylorDepth := 10 } (by native_decide)
```

### Discovery Commands

Interactive commands for exploration (use in editor, not in proofs):

```lean
import LeanBound.Discovery

-- Find global minimum
#minimize (fun x => x^2 + Real.sin x) on [-2, 2]

-- Explore function behavior
#explore (Expr.cos (Expr.var 0)) on [0, 4]
```

For use in proofs, use the corresponding tactics: `interval_minimize`, `interval_maximize`.

### Examples

See `LeanBound/Examples/Showcase.lean` for classic inequalities proved with the library, including bounds on `exp`, `sin`, `cos`, and composed expressions.

## Architecture

### Expression AST

`LeanBound.Core.Expr` supports:
- Arithmetic: `const`, `var`, `add`, `mul`, `neg`, `inv`
- Transcendentals: `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `atan`, `arsinh`, `atanh`
- Special functions: `sinc`, `erf`

Note: While the AST supports all these operations, automated verification is tiered. Not all functions are supported by all tactics or correctness theorems.

### Computability Tiers

- **`ExprSupportedCore`**: Fully computable subset (`const`, `var`, `add`, `mul`, `neg`, `sin`, `cos`, `exp` via Taylor models). Enables `native_decide` proofs.
- **`ExprSupported`**: Non-computable counterpart to `ExprSupportedCore` that uses `Real.exp` directly for theoretical proofs.
- **`ExprSupportedWithInv`**: Most general predicate, including partial functions (`inv`, `log`, `atan`, `arsinh`, `atanh`, `sinc`, `erf`). Verification requires `evalInterval?` which may fail if domain constraints are not met.

### Golden Theorems

These bridge computation and proof. If the checker returns `true`, the theorem holds.

| Goal | Theorem | Checker |
|------|---------|---------|
| Upper bound | `verify_upper_bound` | `checkUpperBound` |
| Lower bound | `verify_lower_bound` | `checkLowerBound` |
| Root existence | `verify_sign_change` | `checkSignChange` |
| Root uniqueness | `verify_unique_root_core` | `checkNewtonContracts` |
| Integration | `verify_integral_bound` | `checkIntegralBoundsCore` |
| Global minimum | `verify_global_lower_bound` | `checkGlobalLowerBound` |

### Numerics Engine

- `evalIntervalCore`: Interval evaluation with Taylor models
- `globalMinimizeCore`: Branch-and-bound optimization
- `bisectRoot`: Root isolation via sign changes
- `newtonStepTM`: Interval Newton for uniqueness proofs
- `integrateInterval`: Riemann sum bounds

## Python SDK

LeanBound includes a Python SDK for integration with external tools.

### Installation

```bash
cd python
pip install -e .
```

### Usage

```python
import leanbound as lf

# Define expressions with named variables
x = lf.var('x')
expr = x**2 + lf.sin(x)

# Find bounds on an interval
result = lf.find_bounds(expr, {'x': (0, 1)})
print(result.min_bound, result.max_bound)

# Find roots
roots = lf.find_roots(x**2 - 2, {'x': (1, 2)})

# Verify a bound
verified = lf.verify_bound(expr, {'x': (0, 1)}, upper=2)
```

### Features

- **Named symbolic variables**: No De Bruijn indices; use `var('x')` directly
- **Automatic domain inference**: Box constraints derived from expression structure
- **Symbolic simplification**: Mitigates the dependency problem in interval arithmetic (e.g., `x - x` simplifies to `0` before evaluation, avoiding spurious width)
- **Adaptive verification**: `verify_bound(method='adaptive')` uses global optimization and counterexample concretization to filter false positives
- **Certificate generation**: Results include `certificate.to_lean_tactic()` for generating formal Lean proofs from Python

### Limitations

- **sqrt/log bounds**: The bridge uses computable algebraic bounds for `log` (`1-1/x ≤ log(x) ≤ x-1`), which are correct but ~2x wider than optimal. For tight bounds on expressions containing `sqrt` or `log`, use Lean's `evalInterval?` directly or the Taylor model API.

## Lean Bridge

`LeanBound.Bridge` provides a JSON-RPC interface over stdin/stdout:

```json
{"method": "eval_interval", "params": {"expr": "x^2", "box": [[0, 1]]}}
{"method": "global_min", "params": {"expr": "x^2 + sin(x)", "box": [[-2, 2]]}}
```

This enables workflows where Python handles search strategy while Lean provides verified computation.

## Verification Status

### Fully Verified

The following have complete proofs with no `sorry`:

- Interval arithmetic (FTIA) for `+`, `-`, `*`, `/`, `^`
- Transcendental bounds: `exp`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `atan`, `arsinh`, `log`
- Taylor series remainder bounds for `exp`, `sin`, `cos`, `log` (Lagrange form)
- Forward-mode AD for core functions (exp, sin, cos, etc.)
- Global optimization (`globalMinimize_lo_correct`, `globalMaximize_hi_correct`)
- Root finding: bisection (existence) and Newton (uniqueness)
- Integration bounds (`integrateInterval_correct`)

### Work in Progress (v1.1)

The Dyadic arithmetic backend is under development for improved kernel performance:

| Component | Status |
|-----------|--------|
| `Core/Dyadic.lean` | Shift/comparison lemmas need proofs |
| `Core/IntervalDyadic.lean` | Interval operation correctness |
| `Numerics/IntervalEvalDyadic.lean` | Evaluator correctness |

To find all `sorry` occurrences:

```bash
grep -rn "sorry" --include="*.lean" LeanBound/ | grep -v "no sorry"
```

## Contributing

Priority areas:

1. Completing Dyadic v1.1 proofs (shift lemmas, interval correctness)
2. Additional functions (`asin`, `acos`, real powers)
3. Subdivision strategies for optimization
4. Documentation and examples

Open an issue before starting major work.

## License

**Dual Licensed:**

- **AGPL-3.0** — Free for open source projects and non-commercial use
- **Commercial License** — Required for proprietary/closed-source use

If your organization uses LeanBound in production without releasing your code under AGPL, contact [your email] for commercial licensing.

See [LICENSE](LICENSE) for the full AGPL-3.0 text.
