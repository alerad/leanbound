# Discovery Mode

Discovery mode lets you **explore** functions before proving things about them. Find bounds, locate extrema, and get witness points—all with rigorous interval arithmetic.

## Interactive Commands

Use these in your editor to explore functions. They print results but don't produce proof terms.

### `#find_min` / `#minimize`

Find the global minimum of a function on a domain.

```lean
import LeanCert.Discovery.Commands

-- Single variable
#find_min (fun x => x^2 + Real.sin x) on [-2, 2]

-- With custom precision (Taylor depth)
#find_min (fun x => Real.exp x - x) on [0, 2] precision 20

-- Multivariate (product of intervals)
#find_min (fun x y => x^2 + y^2 - x*y) on [-1, 1] × [-1, 1]
```

Output:
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#find_min Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Minimum bound: -0.210796
  Upper bound:   -0.209012
  Width:         0.001784
  Iterations:    847
  Verified:      ✓ (rigorous interval arithmetic)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### `#find_max` / `#maximize`

Find the global maximum.

```lean
#find_max (fun x => Real.sin x * Real.exp (-x)) on [0, 3]
```

### `#bounds`

Find both minimum and maximum in one call.

```lean
#bounds (fun x => x^3 - x) on [-2, 2]
```

Output:
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#bounds Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  f(x) ∈ [-1.154, 1.154]

  Minimum: -1.154 (± 0.002)
  Maximum: 1.154 (± 0.002)

  Total iterations: 1247
  Verified: ✓
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### `#eval_interval`

Quick interval evaluation without optimization (just propagate intervals through the expression).

```lean
#eval_interval (fun x => Real.exp (Real.sin x)) on [0, 1]
```

## Tactics for Proofs

These tactics produce actual proof terms.

### `interval_minimize`

Prove that a minimum exists by finding it.

```lean
-- Prove: ∃ m, ∀ x ∈ [0,1], x² + sin(x) ≥ m
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, x^2 + Real.sin x ≥ m := by
  interval_minimize
```

### `interval_maximize`

Prove that a maximum exists by finding it.

```lean
-- Prove: ∃ M, ∀ x ∈ [0,1], sin(x) ≤ M
example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, Real.sin x ≤ M := by
  interval_maximize
```

### `interval_roots`

Prove root existence via sign change (intermediate value theorem).

```lean
-- Prove √2 exists
def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

example : ∃ x ∈ I12, x^2 = 2 := by
  interval_roots
```

## Programmatic API

For more control, use the API directly.

### With Witnesses

Get not just the bound, but also an approximate location of the extremum:

```lean
import LeanCert.Engine.Optimization.BoundVerify

open LeanCert.Core LeanCert.Engine.Optimization

def e := Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.sin (Expr.var 0))
def I : IntervalRat := ⟨-2, 2, by norm_num⟩

#eval
  let result := findMin1WithWitness e I {}
  s!"min ≈ {result.computedBound}, argmin ≈ {result.witness.coords}, ε = {result.epsilon}"
```

Output:
```
min ≈ -0.210, argmin ≈ [-0.4502], ε = 0.001
```

### Available Functions

| Function | Description |
|----------|-------------|
| `findMinWithWitness` | Find minimum with witness point |
| `findMaxWithWitness` | Find maximum with witness point |
| `verifyUpperBoundWithWitness` | Verify f(x) ≤ bound, get argmax |
| `verifyLowerBoundWithWitness` | Verify f(x) ≥ bound, get argmin |

Single-variable versions: `findMin1WithWitness`, `findMax1WithWitness`, etc.

### Result Structure

```lean
structure BoundVerifyResult where
  verified : Bool           -- Did verification succeed?
  computedBound : ℚ         -- The computed bound
  witness : WitnessPoint    -- Approximate argmin/argmax
  epsilon : ℚ               -- Width of best box (precision)
  iterations : Nat          -- Iterations used

structure WitnessPoint where
  coords : List ℚ           -- Coordinates of witness point
  boxWidth : ℚ              -- Width of containing box
```

## Configuration

Control precision and iteration limits:

```lean
let cfg : BoundVerifyConfig := {
  taylorDepth := 15,        -- Taylor series terms (default: 10)
  tolerance := 1/10000,     -- Stop when box width < tolerance
  maxIterations := 2000,    -- Iteration limit (default: 1000)
  useMonotonicity := true   -- Use gradient info to prune (default: true)
}

let result := findMinWithWitness e box cfg
```

## Workflow: Explore → Prove

A typical workflow:

```lean
-- 1. Explore: What's the minimum of x² + sin(x) on [-2, 2]?
#find_min (fun x => x^2 + Real.sin x) on [-2, 2]
-- Output: min ≈ -0.210

-- 2. Prove: Now that we know it's around -0.21, prove a bound
example : ∀ x ∈ Set.Icc (-2:ℝ) 2, x^2 + Real.sin x ≥ -1/4 := by
  certify_bound

-- 3. Or prove the existential directly
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (-2:ℝ) 2, x^2 + Real.sin x ≥ m := by
  interval_minimize
```

## Python SDK

The Python SDK also supports discovery with witnesses:

```python
import leancert as lc

x = lc.var('x')
expr = x**2 + lc.sin(x)

# Find minimum with witness
result = lc.minimize(expr, {'x': (-2, 2)})
print(f"min ≈ {result.bound}")
print(f"argmin ≈ {result.witness}")
print(f"precision: ε = {result.epsilon}")

# Verify a bound
check = lc.verify_lower_bound(expr, {'x': (-2, 2)}, bound=-0.25)
print(f"Verified: {check.verified}")
```
