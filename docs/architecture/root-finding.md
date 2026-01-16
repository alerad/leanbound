# Root Finding Algorithms

LeanCert provides verified root finding with proofs of existence and uniqueness.

## Overview

| Algorithm | Proves | Method | Tactic |
|-----------|--------|--------|--------|
| Bisection | Existence | Sign change + IVT | `interval_roots` |
| Newton Contraction | Uniqueness | Fixed-point theorem | `interval_unique_root` |

## Bisection (Existence)

### How It Works

1. Evaluate f at interval endpoints
2. If signs differ, IVT guarantees a root exists
3. Recursively bisect to narrow the interval

```
f(a) < 0                    f(b) > 0
  ●━━━━━━━━━━━━━━━━━━━━━━━━━●
  a          root          b
             somewhere
             in here
```

### The Theorem

```lean
theorem verify_sign_change (e : Expr) (hsupp : ExprSupportedCore e)
    (hcont : ContinuousOn (Expr.eval e) (Set.Icc I.lo I.hi))
    (I : IntervalRat) (cfg : EvalConfig)
    (h_cert : checkSignChange e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0
```

**Key insight**: The checker `checkSignChange` is computable (runs via `native_decide`), while the conclusion is a semantic statement about real numbers.

### Usage

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

-- Prove √2 exists (root of x² - 2)
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

### Algorithm Details

```
bisectRoot(f, [a, b], depth):
  if depth = 0:
    return [a, b] if sign_change(f, a, b) else ∅

  mid = (a + b) / 2
  roots = []

  if sign_change(f, a, mid):
    roots += bisectRoot(f, [a, mid], depth - 1)

  if sign_change(f, mid, b):
    roots += bisectRoot(f, [mid, b], depth - 1)

  return roots
```

### Limitations

- Only finds roots where sign changes (misses tangent roots like x² at 0)
- Requires continuity (cannot handle discontinuous functions)
- Multiple roots in interval returns multiple candidate intervals

---

## Newton Contraction (Uniqueness)

### How It Works

The Newton operator is:

\\[
N(x) = x - \frac{f(x)}{f'(x)}
\\]

If we can show:
1. N maps interval I into itself: N(I) ⊆ I
2. N is a contraction: |N'(x)| < 1 for all x ∈ I

Then Banach fixed-point theorem guarantees exactly one root in I.

### The Theorem

```lean
theorem newton_contraction_unique_root (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_maps_into : newtonInterval e I cfg ⊆ I)
    (h_contracts : ∀ x ∈ I, |newtonDerivative e x cfg| < 1) :
    ∃! x ∈ I, Expr.eval (fun _ => x) e = 0
```

### Usage

```lean
import LeanCert.Tactic.Discovery

-- Prove x² - 2 has exactly one root in [1, 2]
example : ∃! x ∈ I12, Expr.eval (fun _ => x) expr_x2_minus_2 = 0 := by
  interval_unique_root
```

### Contraction Verification

To verify contraction, we bound |N'(x)|:

\\[
N'(x) = 1 - \frac{f'(x)^2 - f(x) \cdot f''(x)}{f'(x)^2} = \frac{f(x) \cdot f''(x)}{f'(x)^2}
\\]

Using interval arithmetic:
1. Compute interval bounds on f(I), f'(I), f''(I)
2. Check if |f(I) · f''(I)| / |f'(I)|² < 1

### Algorithm Details

```
checkNewtonContracts(f, I):
  # Compute function and derivatives on interval
  f_I   = evalInterval(f, I)
  f'_I  = evalInterval(derivative(f), I)
  f''_I = evalInterval(derivative(derivative(f)), I)

  # Check f' doesn't contain 0 (otherwise N undefined)
  if 0 ∈ f'_I:
    return false

  # Compute Newton image
  N_I = I - f_I / f'_I

  # Check maps into
  if not (N_I ⊆ I):
    return false

  # Check contraction (|N'| < 1)
  N'_bound = |f_I * f''_I| / (f'_I)²
  return N'_bound.hi < 1
```

### Refinement

Once uniqueness is established, Newton iteration refines the root location:

```lean
def newtonRefine (e : Expr) (I : IntervalRat) (n : ℕ) : IntervalRat :=
  match n with
  | 0 => I
  | n + 1 => newtonRefine e (newtonStep e I) n
```

Each iteration roughly doubles the number of correct digits.

---

## Comparison

| Aspect | Bisection | Newton |
|--------|-----------|--------|
| Proves | Existence | Uniqueness |
| Requires | Sign change | f' ≠ 0, contraction |
| Convergence | Linear | Quadratic |
| Multiple roots | Finds all (with sign change) | Finds one |
| Tangent roots | Misses | Can verify if f' ≠ 0 nearby |

## Combined Workflow

For full root verification:

```lean
-- 1. First prove existence
have h_exists : ∃ x ∈ I, f x = 0 := by interval_roots

-- 2. Then prove uniqueness (if needed)
have h_unique : ∃! x ∈ I, f x = 0 := by interval_unique_root

-- 3. Optionally refine location
-- The unique root is in a very narrow interval
```

## Mean Value Theorem Bounds

The `MVTBounds` module provides additional tools:

```lean
-- If f' is bounded on [a,b], then f(b) - f(a) is bounded
theorem mvt_bound (f : ℝ → ℝ) (a b : ℝ) (M : ℝ)
    (h_diff : DifferentiableOn ℝ f (Set.Icc a b))
    (h_bound : ∀ x ∈ Set.Icc a b, |f' x| ≤ M) :
    |f b - f a| ≤ M * |b - a|
```

This is used internally for:
- Bounding how much f can change between sample points
- Verifying monotonicity
- Lipschitz constant estimation

## Files

| File | Description |
|------|-------------|
| `Engine/RootFinding/Basic.lean` | Core predicates (`signChange`, `excludesZero`) |
| `Engine/RootFinding/Bisection.lean` | Bisection algorithm |
| `Engine/RootFinding/Contraction.lean` | Newton contraction verification |
| `Engine/RootFinding/MVTBounds.lean` | Mean value theorem utilities |
| `Tactic/Discovery.lean` | `interval_roots`, `interval_unique_root` tactics |
