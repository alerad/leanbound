# Lean Tactics Reference

Complete reference for all LeanCert tactics.

## Bound Proving

### `certify_bound`

Proves universal bounds over intervals using rational interval arithmetic.

```lean
import LeanCert.Tactic.IntervalAuto

-- Basic usage
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by certify_bound

-- With Taylor depth (higher = tighter bounds, slower)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by certify_bound 15

-- Lower bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by certify_bound

-- Strict inequalities
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x < 3 := by certify_bound
```

Note: `interval_bound` is an alias for backward compatibility.

**Parameters:**

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `depth` | `ℕ` | 10 | Taylor series depth for transcendentals |

**Supported functions:** `+`, `-`, `*`, `sin`, `cos`, `exp`, `sqrt`, `sinh`, `cosh`, `tanh`

---

### `certify_kernel`

Proves bounds using dyadic arithmetic. Attempts kernel-only verification (`decide`) first, falls back to `native_decide`.

```lean
import LeanCert.Tactic.DyadicAuto

-- Default precision (53 bits)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ 2 := by certify_kernel

-- Custom precision (bits)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by certify_kernel 100

-- Convenience variants
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by certify_kernel_precise  -- 100 bits
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ 2 := by certify_kernel_quick           -- 30 bits
```

Note: `fast_bound` is an alias for backward compatibility.

**Trust levels:**

| Verification | Trusted Components |
|--------------|-------------------|
| `decide` (kernel) | Lean kernel only |
| `native_decide` (fallback) | Lean kernel + compiler |

**Diagnostics:** Enable `set_option trace.certify_kernel true` to see why kernel verification fails.

---

### `interval_decide`

Proves point inequalities involving specific numbers (transcendentals like π, e).

```lean
import LeanCert.Tactic.IntervalAuto

example : Real.pi < 3.15 := by interval_decide
example : Real.exp 1 < 3 := by interval_decide
example : Real.sin 1 + Real.cos 1 < 1.5 := by interval_decide
example : Real.sqrt 2 < 1.42 := by interval_decide
```

Use this for concrete values. For universally quantified bounds, use `certify_bound`.

---

## Counter-Example Search

### `interval_refute`

Searches for counter-examples to disprove false bounds.

```lean
import LeanCert.Tactic.Refute

-- This bound is false (x² can reach 4 on [-2, 2])
example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3 := by
  interval_refute
  -- Output: Counter-example found at x ≈ ±2, where x² = 4 > 3
```

**Output types:**

| Result | Meaning |
|--------|---------|
| `Verified` | Rigorous proof that bound fails at this point |
| `Candidate` | Likely counter-example (may be precision artifact) |

**Configuration:**

```lean
-- With custom settings
example : ... := by
  interval_refute (config := { maxIterations := 100, tolerance := 1e-6 })
```

---

## Discovery Tactics

### `interval_minimize` / `interval_maximize`

Proves existence of global minimum/maximum via branch-and-bound optimization.

```lean
import LeanCert.Tactic.Discovery

-- Find and prove a lower bound exists
example : ∃ m, ∀ x ∈ Set.Icc (0 : ℝ) 2, x * x - x ≥ m := by
  interval_minimize

-- With Taylor depth
example : ∃ m, ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≥ m := by
  interval_minimize 15
```

---

### `interval_roots`

Proves root existence via sign change detection (Intermediate Value Theorem).

```lean
import LeanCert.Tactic.Discovery

open LeanCert.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

-- Prove √2 exists
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

**How it works:**
1. Evaluates expression at interval endpoints
2. Detects sign change (f(lo) < 0 < f(hi) or vice versa)
3. Applies IVT to prove existence

---

### `interval_unique_root`

Proves root uniqueness via Newton contraction mapping.

```lean
import LeanCert.Tactic.Discovery

-- Prove there's exactly one root of x² - 2 in [1, 2]
example : ∃! x ∈ I12, Expr.eval (fun _ => x) expr_x2_minus_2 = 0 := by
  interval_unique_root
```

**How it works:**
1. Computes Newton operator N(x) = x - f(x)/f'(x)
2. Verifies N maps interval into itself
3. Verifies |N'(x)| < 1 (contraction)
4. Banach fixed-point theorem gives uniqueness

---

### `interval_integrate`

Proves bounds on definite integrals via verified Riemann sums.

```lean
import LeanCert.Tactic.Discovery

-- Prove integral bounds
example : ∫ x in (0:ℝ)..1, x^2 ≤ 0.34 := by
  interval_integrate
```

**How it works:**
1. Partitions interval into subintervals
2. Computes interval bounds on each partition
3. Sums (width × bound) for rigorous over/under-approximation

---

## Interactive Commands

### `#explore`

Interactive function analysis in the editor. Shows range, extrema, and roots.

```lean
import LeanCert.Tactic.Discovery

-- Explore sin(x) on [0, 4]
#explore (Expr.sin (Expr.var 0)) on [0, 4]
```

**Output includes:**
- Domain and computed range
- Global minimum and maximum with locations
- Sign changes (potential roots)
- Monotonicity information

---

## Comparison Table

| Tactic | Purpose | Trust | Speed |
|--------|---------|-------|-------|
| `certify_bound` | Prove bounds | `native_decide` | Medium |
| `certify_kernel` | Prove bounds | `decide` / fallback | Fast |
| `interval_decide` | Point inequalities | `native_decide` | Fast |
| `interval_refute` | Find counter-examples | Verified | Slow |
| `interval_roots` | Prove root exists | `native_decide` | Medium |
| `interval_unique_root` | Prove root unique | `native_decide` | Slow |
| `interval_minimize` | Prove min exists | `native_decide` | Slow |
| `interval_integrate` | Prove integral bounds | `native_decide` | Medium |

---

## Common Patterns

### Proving a function is bounded

```lean
-- Upper and lower bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.sin x ∧ Real.sin x ≤ 1 := by
  constructor <;> certify_bound
```

### Proving a root exists and is unique

```lean
-- First existence, then uniqueness
example : ∃ x ∈ I, f x = 0 := by interval_roots
example : ∃! x ∈ I, f x = 0 := by interval_unique_root
```

### Debugging failed proofs

```lean
set_option trace.certify_bound true    -- See computation details
set_option trace.certify_kernel true   -- See kernel verification status

-- If bound too tight, try:
-- 1. Increase Taylor depth: certify_bound 20
-- 2. Use certify_kernel_precise for more bits
-- 3. Use interval_refute to check if bound is actually false
```
