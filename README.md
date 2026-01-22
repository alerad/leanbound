# LeanCert

**Numerical computation produces suggestions. LeanCert produces theorems.**

LeanCert transforms numerical insights into formal certificates—proof terms verified by the Lean kernel. Write `by certify_bound` and get a real theorem: `∀ x ∈ I, f(x) ≤ c`, not just a floating-point approximation.

## Why LeanCert?

- **Certification is the product.** Tactics produce theorems, not numbers. The output isn't `-0.232`; it's `∃ m, ∀ x, f(x) ≥ m` with a rigorous rational bound.
- **Golden Theorem architecture.** Every algorithm is designed around a theorem connecting a fast boolean check (`checkUpperBound(...) = true`) to a deep mathematical property (`∀ x ∈ I, f(x) ≤ c`). This makes every result auditable.
- **Trust hierarchy.** Choose your trade-off:
  - *Kernel-only* (`decide`): Proofs verified by reduction alone—no trust in the compiler
  - *Compiler-trusted* (`native_decide`): Orders of magnitude faster for complex arithmetic
  - *External oracle* (Python SDK): Fast exploration, with Lean independently verifying results
- **Focus on the goal, not the guts.** Write `by certify_bound` without understanding Taylor remainder bounds or dyadic rounding modes.

Discovery commands like `#find_min` help *explore*; tactics like `certify_bound` *prove*.

## Architecture

LeanCert operates on a certificate-driven architecture:

1. **Reification**: Mathematical expressions are converted to an AST (`LeanCert.Core.Expr`)
2. **Computation**: The Engine runs algorithms using rational/dyadic interval arithmetic
3. **Certification**: Golden Theorems lift boolean results to semantic proofs about real numbers

This separation allows efficient computation while maintaining full formal verification.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "leancert"
git = "https://github.com/alerad/leancert"
rev = "main"
```

Then run `lake update`.

### Checking Mathlib Compatibility

LeanCert requires a specific Mathlib version (`v4.27.0-rc1`). If you have other dependencies or an existing project, check compatibility:

```bash
lake exe check-compat
```

This will warn you if your Mathlib version doesn't match and provide instructions to fix it.

## Usage

### Tactics

```lean
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.Discovery

open LeanCert.Core

-- Prove bounds on transcendentals using natural Set.Icc syntax
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by certify_bound 15
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by certify_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by certify_bound

-- Or with explicit IntervalRat for more control
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

example : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by certify_bound 15

-- Prove root existence (√2) via sign change
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

### Direct API

```lean
import LeanCert.Validity

open LeanCert.Core LeanCert.Engine LeanCert.Validity

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
import LeanCert.Discovery.Commands

-- Find global minimum
#find_min (fun x => x^2 + Real.sin x) on [-2, 2]

-- Explore function behavior
#explore (Expr.cos (Expr.var 0)) on [0, 4]
```

For use in proofs, use the corresponding tactics: `interval_minimize`, `interval_maximize`.

### Examples

See `LeanCert/Examples/Showcase.lean` for classic inequalities proved with the library, including bounds on `exp`, `sin`, `cos`, and composed expressions.

## Architecture

### Expression AST

`LeanCert.Core.Expr` supports:
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

### Engine

- `evalIntervalCore`: Interval evaluation with Taylor models
- `globalMinimizeCore`: Branch-and-bound optimization
- `bisectRoot`: Root isolation via sign changes
- `newtonStepTM`: Interval Newton for uniqueness proofs
- `integrateInterval`: Riemann sum bounds

## Python SDK

LeanCert includes a Python SDK for integration with external tools.

### Installation

```bash
cd python
pip install -e .
```

### Usage

```python
import leancert as lc

# Define expressions with named variables
x = lc.var('x')
expr = x**2 + lc.sin(x)

# Find bounds on an interval
result = lc.find_bounds(expr, {'x': (0, 1)})
print(result.min_bound, result.max_bound)

# Find roots
roots = lc.find_roots(x**2 - 2, {'x': (1, 2)})

# Verify a bound
verified = lc.verify_bound(expr, {'x': (0, 1)}, upper=2)
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

`LeanCert.Bridge` provides a JSON-RPC interface over stdin/stdout:

```json
{"method": "eval_interval", "params": {"expr": "x^2", "box": [[0, 1]]}}
{"method": "global_min", "params": {"expr": "x^2 + sin(x)", "box": [[-2, 2]]}}
```

This enables workflows where Python handles search strategy while Lean provides verified computation.

## Neural Network Verification

LeanCert includes verified interval propagation for neural networks, enabling robustness verification.

### Features

- **Dense Layers**: Verified forward propagation with ReLU activation
- **DeepPoly Relaxations**: Tight linear bounds for ReLU (triangle relaxation) and sigmoid
- **Optimized Backend**: Structure-of-arrays layout, split-sign decomposition, integer arithmetic

### Quick Example

```lean
import LeanCert.ML.Network

open LeanCert.ML

-- Define a 2-layer network
def net : TwoLayerNet := {
  layer1 := { weights := [[1, -1], [0, 1]], bias := [0, 0] }
  layer2 := { weights := [[1, 1]], bias := [0] }
}

-- Propagate input intervals through the network
def outputBounds := net.forwardInterval inputIntervals
```

### Soundness Theorem

```lean
theorem mem_forwardInterval :
    (∀ i, xs[i] ∈ Is[i]) → (∀ i, (forwardReal net xs)[i] ∈ (forwardInterval net Is)[i])
```

If every real input is in its interval, every real output is in its output interval.

### Files

| File | Description |
|------|-------------|
| `ML/Network.lean` | Layer and network definitions |
| `ML/IntervalVector.lean` | ReLU, sigmoid activations |
| `ML/Symbolic/ReLU.lean` | DeepPoly ReLU relaxation |
| `ML/Symbolic/Sigmoid.lean` | DeepPoly sigmoid relaxation |
| `ML/Optimized.lean` | High-performance implementations |

## Verification Status

### Fully Verified

The following have complete proofs with no `sorry`:

- Interval arithmetic (FTIA) for `+`, `-`, `*`, `/`, `^`
- Transcendental bounds: `exp`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `atan`, `arsinh`, `log`, `sqrt`
- Taylor series remainder bounds for `exp`, `sin`, `cos`, `log` (Lagrange form)
- Forward-mode AD for core functions (exp, sin, cos, etc.)
- Affine arithmetic engine (`evalIntervalAffine_correct`)
- Global optimization (`globalMinimize_lo_correct`, `globalMaximize_hi_correct`)
- Root finding: bisection (existence) and Newton (uniqueness)
- Integration bounds (`integrateInterval_correct`)

### Dyadic Backend (v1.1)

LeanCert includes two interval arithmetic backends:

| Backend | Best For | Trade-off |
|---------|----------|-----------|
| **Rational** (`evalIntervalCore`) | Simple expressions, exact precision | Denominators grow exponentially |
| **Dyadic** (`evalIntervalDyadic`) | Deep expressions, neural networks | Fixed precision, slightly wider bounds |

**When to use Dyadic:**
- Neural network verification (1000s of operations)
- Optimization loops (100s of iterations)
- Deeply nested expressions (e.g., `sin(sin(sin(...)))`)
- Taylor series with many terms

**Performance comparison** (nested exp expressions):

| Expression | Rational Denominator | Dyadic Mantissa |
|------------|---------------------|-----------------|
| `exp(exp(x))` | ~200 digits | 17 digits |
| `exp(exp(exp(x)))` | ~2000 digits | 18 digits |
| `exp(exp(exp(exp(x))))` | timeout | 42 digits |

**Usage:**

```lean
import LeanCert.Engine.IntervalEvalDyadic

open LeanCert.Core LeanCert.Engine

-- Standard precision (53 bits, like IEEE double)
def result := evalIntervalDyadic expr env {}

-- Fast mode (30 bits, ~3x faster)
def fast := evalIntervalDyadic expr env DyadicConfig.fast

-- High precision (100 bits, tighter bounds)
def precise := evalIntervalDyadic expr env DyadicConfig.highPrecision
```

See `LeanCert/Test/BenchmarkBackends.lean` for comprehensive benchmarks.

### Work in Progress

To find all `sorry` occurrences:

```bash
grep -rn "sorry" --include="*.lean" LeanCert/ | grep -v "no sorry"
```

## What LeanCert is Not

- **Not just another numerical library.** NumPy and SciPy produce floating-point approximations. LeanCert produces theorems.
- **Not a black-box solver.** Results are auditable proof terms. The `decide` pathway produces proofs reducible by the kernel alone.
- **Not limited to interval arithmetic.** While interval methods are the core engine today, the framework certifies results from any numerical method that can produce evidence for a Golden Theorem.

## Contributing

Priority areas:

1. Additional functions (`asin`, `acos`, real powers)
2. Subdivision strategies for optimization
3. Tighter Taylor model bounds for transcendentals
4. Documentation and examples

Open an issue before starting major work.

## License

**FSL-1.1-Apache-2.0** (Functional Source License)

- **Free** for personal use, research, education, and internal business operations
- **Commercial license required** for offering verification to third parties
- **Converts to Apache 2.0** on January 17, 2028

See [LICENSE](LICENSE) for full terms and [COMMERCIAL.md](COMMERCIAL.md) for pricing.
