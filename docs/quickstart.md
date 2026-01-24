# Quickstart

This guide walks through the main use cases for LeanCert.

## Installation

```bash
pip install leancert
```

That's it - no Lean installation required. The package includes a pre-compiled verification engine.

## Python SDK

### Finding Bounds

```python
import leancert as lc

x = lc.var('x')
expr = x**2 + lc.sin(x)

# Find min/max on an interval
result = lc.find_bounds(expr, {'x': (0, 1)})

print(f"Minimum: {result.min_bound}")
print(f"Maximum: {result.max_bound}")
```

### Verifying a Bound

```python
# Verify that x^2 + sin(x) ≤ 2 on [0, 1]
# Uses adaptive method with false positive filtering by default
verified = lc.verify_bound(expr, {'x': (0, 1)}, upper=2)

if verified:
    print("Bound verified!")

# For a certificate that can be exported to Lean, use find_bounds:
result = lc.find_bounds(expr, {'x': (0, 1)})
if result.max_bound.hi <= 2:
    print(result.certificate.to_lean_tactic())
```

### Finding Roots

```python
# Find where x^2 - 2 = 0 on [1, 2]
roots = lc.find_roots(x**2 - 2, {'x': (1, 2)})

for root in roots.intervals:
    print(f"Root in [{root.lo}, {root.hi}]")
```

### Symbolic Simplification

LeanCert automatically simplifies expressions to avoid interval explosion:

```python
# Without simplification: (x*100 + 5) - (x*100) would have wide bounds
# With simplification: reduces to 5
expr = (x * 100 + 5) - (x * 100)
simplified = lc.simplify(expr)  # Returns const(5)
```

## Lean Tactics

### Point Inequalities (`interval_decide`)

To prove inequalities involving specific numbers (including transcendentals like π or e), use `interval_decide`:

```lean
import LeanCert.Tactic.IntervalAuto

-- Proves π < 3.15
example : Real.pi < 3.15 := by interval_decide

-- Proves e < 3
example : Real.exp 1 < 3 := by interval_decide

-- For complex expressions with constants
example : Real.sin 1 + Real.cos 1 < 1.5 := by interval_decide
```

### Proving Bounds (`certify_bound`)

```lean
import LeanCert.Tactic.IntervalAuto

open LeanCert.Core

-- Use natural Set.Icc syntax with integer bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by certify_bound 15
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by certify_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by certify_bound

-- Lower bounds work too
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x * x := by certify_bound

-- Or use explicit IntervalRat for more control
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
example : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by certify_bound 15
```

### Kernel-Verified Bounds (`certify_kernel`)

For higher trust, use `certify_kernel`. Unlike `certify_bound` which trusts the Lean compiler (`native_decide`), `certify_kernel` uses the dyadic backend and reduces proofs entirely within the Lean kernel (`decide`) when possible.

```lean
import LeanCert.Tactic.DyadicAuto

-- Same syntax as certify_bound, but uses dyadic backend
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x + Real.sin x ≤ 2 := by
  certify_kernel

-- Increase precision (bits) for tight bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  certify_kernel 100

-- Convenience variants
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  certify_kernel_precise  -- 100 bits precision

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ 2 := by
  certify_kernel_quick    -- 30 bits, faster
```

| Tactic | Backend | Verification | Trust Level |
|--------|---------|--------------|-------------|
| `certify_bound` | Rational | `native_decide` | Compiler + Runtime |
| `certify_kernel` | Dyadic | `decide` (when possible) | Kernel only |

### Finding Counter-Examples (`interval_refute`)

If a bound doesn't hold, use `interval_refute` to find a counter-example:

```lean
import LeanCert.Tactic.Refute

-- A false theorem - interval_refute finds where it fails
example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3 := by
  interval_refute
  -- Output: Counter-example found at x ≈ ±2, where x² = 4 > 3
```

### Proving Root Existence

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

-- Prove √2 exists via sign change
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

### Multivariate Bounds

```lean
import LeanCert.Tactic.IntervalAuto

-- Prove bounds over multiple variables
example : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    x + y ≤ (2 : ℚ) := by
  multivariate_bound

example : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ z ∈ Set.Icc (0:ℝ) 1,
    x + y + z ≤ (3 : ℚ) := by
  multivariate_bound
```

### Proving Absence of Roots

```lean
import LeanCert.Tactic.IntervalAuto

open LeanCert.Core

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

-- Prove f(x) ≠ 0 by showing function stays positive/negative
example : ∀ x ∈ I01, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const 1)) ≠ (0 : ℝ) := by
  root_bound
```

### Discovery Commands

For interactive exploration in the editor:

```lean
import LeanCert.Discovery.Commands

-- Find the global minimum
#find_min (fun x => x^2 + Real.sin x) on [-2, 2]

-- Explore function behavior
#explore (Expr.cos (Expr.var 0)) on [0, 4]
```

### Discovering Bounds (Existential)

```lean
import LeanCert.Tactic.Discovery

-- Automatically find and prove a minimum exists
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, x^2 ≥ m := by
  interval_minimize

-- Find maximum
example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, x^2 ≤ M := by
  interval_maximize

-- Multivariate optimization
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    x*x + y*y ≥ m := by
  interval_minimize_mv
```

## High-Performance Dyadic Backend

For deep expressions (neural networks, optimization loops, nested transcendentals), use the dyadic backend to avoid rational denominator explosion:

```lean
import LeanCert.Engine.IntervalEvalDyadic

open LeanCert.Core LeanCert.Engine

-- Convert interval to dyadic
def I : IntervalDyadic := IntervalDyadic.ofIntervalRat ⟨0, 1, by norm_num⟩ (-53)

-- Evaluate with standard precision (53 bits)
def result := evalIntervalDyadic expr (fun _ => I) {}

-- Use fast mode for very deep expressions
def fast := evalIntervalDyadic expr (fun _ => I) DyadicConfig.fast

-- Use high precision for tight bounds
def precise := evalIntervalDyadic expr (fun _ => I) DyadicConfig.highPrecision
```

The dyadic backend keeps mantissa size bounded regardless of expression depth, while rational denominators grow exponentially.

## Direct API

For more control, use the certificate API directly:

```lean
import LeanCert.Validity

open LeanCert.Core LeanCert.Engine LeanCert.Validity

def exprXSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

def exprXSq_core : ExprSupportedCore exprXSq :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

-- Use native_decide to verify computationally
theorem xsq_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) :=
  verify_upper_bound exprXSq exprXSq_core I01 1 {} (by native_decide)
```
