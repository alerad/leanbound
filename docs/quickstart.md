# Quickstart

This guide walks through the main use cases for LeanBound.

## Python SDK

### Finding Bounds

```python
import leanbound as lf

x = lf.var('x')
expr = x**2 + lf.sin(x)

# Find min/max on an interval
result = lf.find_bounds(expr, {'x': (0, 1)})

print(f"Minimum: {result.min_bound}")
print(f"Maximum: {result.max_bound}")
```

### Verifying a Bound

```python
# Verify that x^2 + sin(x) ≤ 2 on [0, 1]
verified = lf.verify_bound(expr, {'x': (0, 1)}, upper=2)

if verified.success:
    print("Bound verified!")
    # Get the Lean tactic to prove this formally
    print(verified.certificate.to_lean_tactic())
```

### Finding Roots

```python
# Find where x^2 - 2 = 0 on [1, 2]
roots = lf.find_roots(x**2 - 2, {'x': (1, 2)})

for root in roots.intervals:
    print(f"Root in [{root.lo}, {root.hi}]")
```

### Symbolic Simplification

LeanBound automatically simplifies expressions to avoid interval explosion:

```python
# Without simplification: (x*100 + 5) - (x*100) would have wide bounds
# With simplification: reduces to 5
expr = (x * 100 + 5) - (x * 100)
simplified = lf.simplify(expr)  # Returns const(5)
```

## Lean Tactics

### Proving Bounds

```lean
import LeanBound.Tactic.IntervalAuto

open LeanBound.Core

-- Use natural Set.Icc syntax with integer bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by interval_bound 15
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by interval_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by interval_bound

-- Lower bounds work too
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x * x := by interval_bound

-- Or use explicit IntervalRat for more control
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
example : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by interval_bound 15
```

### Proving Root Existence

```lean
import LeanBound.Tactic.Discovery

open LeanBound.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

-- Prove √2 exists via sign change
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

### Discovery Commands

For interactive exploration in the editor:

```lean
import LeanBound.Discovery

-- Find the global minimum
#minimize (fun x => x^2 + Real.sin x) on [-2, 2]

-- Explore function behavior
#explore (Expr.cos (Expr.var 0)) on [0, 4]
```

## Direct API

For more control, use the certificate API directly:

```lean
import LeanBound.Numerics.Certificate

open LeanBound.Core LeanBound.Numerics LeanBound.Numerics.Certificate

def exprXSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

def exprXSq_core : ExprSupportedCore exprXSq :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

-- Use native_decide to verify computationally
theorem xsq_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) :=
  verify_upper_bound exprXSq exprXSq_core I01 1 {} (by native_decide)
```
