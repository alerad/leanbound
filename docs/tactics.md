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

**Native syntax (recommended):**

```lean
import LeanCert.Tactic.Discovery

-- Prove √2 exists in [1, 2]
example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x^2 - 2 = 0 := by
  interval_roots

-- Also supports f(x) = c form
example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x^2 = 2 := by
  interval_roots

-- Transcendental roots
example : ∃ x ∈ Set.Icc (1 : ℝ) 2, Real.cos x = 0 := by
  interval_roots
```

**Expr AST syntax (also supported):**

```lean
open LeanCert.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

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

**Native syntax (recommended):**

```lean
import LeanCert.Tactic.Discovery

-- Prove there's exactly one root of x² - 2 in [1, 2]
example : ∃! x ∈ Set.Icc (1 : ℝ) 2, x^2 - 2 = 0 := by
  interval_unique_root
```

**Expr AST syntax (also supported):**

```lean
open LeanCert.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩
def expr_x2_minus_2 : Expr := Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))

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
| `interval_maximize` | Prove max exists | `native_decide` | Slow |
| `interval_integrate` | Prove integral bounds | `native_decide` | Medium |
| `discover` | Auto-route min/max | `native_decide` | Slow |
| `interval_minimize_mv` | Multivariate min | `native_decide` | Slow |
| `interval_maximize_mv` | Multivariate max | `native_decide` | Slow |
| `multivariate_bound` | N-dim bounds | `native_decide` | Medium |
| `root_bound` | Prove f(x) ≠ 0 | `native_decide` | Medium |
| `interval_bound_subdiv` | Tight bounds via subdivision | `native_decide` | Slow |
| `interval_argmax` | Find maximizer point | `native_decide` | Slow |
| `interval_argmin` | Find minimizer point | `native_decide` | Slow |

---

## Additional Tactics

### `discover`

Meta-tactic that analyzes the goal and automatically routes to `interval_minimize` or `interval_maximize`.

```lean
import LeanCert.Tactic.Discovery

-- Automatically detects ≥ m and calls interval_minimize
example : ∃ m : ℚ, ∀ x ∈ I, f(x) ≥ m := by discover

-- Automatically detects ≤ M and calls interval_maximize
example : ∃ M : ℚ, ∀ x ∈ I, f(x) ≤ M := by discover
```

---

### `interval_minimize_mv` / `interval_maximize_mv`

Multivariate versions of minimize/maximize for N-dimensional domains.

```lean
import LeanCert.Tactic.Discovery

-- Find minimum over 2D domain
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    x*x + y*y ≥ m := by
  interval_minimize_mv

-- Find maximum over 2D domain
example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    x + y ≤ M := by
  interval_maximize_mv
```

Uses more samples (300) and iterations (2000) than univariate versions.

---

### `multivariate_bound`

Proves bounds over multi-variable domains directly.

```lean
import LeanCert.Tactic.IntervalAuto

-- Prove x + y ≤ 2 on [0,1] × [0,1]
example : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    x + y ≤ (2 : ℚ) := by
  multivariate_bound
```

---

### `root_bound`

Proves absence of roots by showing a function is strictly positive or negative.

**Native syntax (recommended):**

```lean
import LeanCert.Tactic.IntervalAuto

-- x² + 1 ≠ 0 on [0, 1] (always positive)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x + 1 ≠ 0 := by
  root_bound

-- exp(x) ≠ 0 on [0, 1]
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≠ 0 := by
  root_bound 15
```

**Expr AST syntax (also supported):**

```lean
open LeanCert.Core

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

example : ∀ x ∈ I01, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const 1)) ≠ (0 : ℝ) := by
  root_bound
```

---

### `interval_bound_subdiv`

Proves bounds using progressive subdivision when direct interval evaluation is too loose.

```lean
import LeanCert.Tactic.IntervalAuto

-- Tighter bound requiring subdivision
example : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x ≤ (272/100 : ℚ) := by
  interval_bound_subdiv 15 3  -- Taylor depth 15, subdivision depth 3
```

**Parameters:**

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `depth` | `ℕ` | 10 | Taylor series depth |
| `subdivDepth` | `ℕ` | 2 | Number of subdivision levels |

---

### `interval_argmax` / `interval_argmin`

Find the point where a function achieves its maximum/minimum.

**`interval_argmax` - Native syntax (recommended):**

```lean
import LeanCert.Tactic.Discovery

-- Find the maximizer of x² on [-1,1] (argmax at endpoints x = ±1)
example : ∃ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    y * y ≤ x * x := by
  interval_argmax

-- Linear function: max of 2x+1 on [0,1] (argmax at x=1)
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    2 * y + 1 ≤ 2 * x + 1 := by
  interval_argmax
```

**`interval_argmin` - Native syntax (recommended):**

```lean
-- Find the minimizer of x on [0,1] (argmin at x=0)
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x ≤ y := by
  interval_argmin
```

**Expr AST syntax (also supported):**

```lean
open LeanCert.Core

def I_neg1_1 : IntervalRat := ⟨-1, 1, by norm_num⟩
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

-- Argmax with Expr AST
example : ∃ x ∈ I_neg1_1, ∀ y ∈ I_neg1_1,
    Expr.eval (fun _ => y) (Expr.mul (Expr.var 0) (Expr.var 0)) ≤
    Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) := by
  interval_argmax

-- Argmin with Expr AST
example : ∃ x ∈ I01, ∀ y ∈ I01,
    Expr.eval (fun _ => x) (Expr.var 0) ≤
    Expr.eval (fun _ => y) (Expr.var 0) := by
  interval_argmin
```

**How it works:**
1. Runs branch-and-bound optimization to find candidate optimizer `xOpt`
2. Evaluates `f(xOpt)` to get a concrete bound `c`
3. For argmax: Proves `∀ y ∈ I, f(y) ≤ c` and `c ≤ f(xOpt)`, then applies transitivity
4. For argmin: Proves `∀ y ∈ I, c ≤ f(y)` and `f(xOpt) ≤ c`, then applies transitivity

**Limitations:**
- Works best when the argmax/argmin is at a rational point (e.g., interval endpoints)
- For transcendental functions, may require higher Taylor depth
- For interior optima at irrational points, consider using `interval_maximize`/`interval_minimize` instead

---

### Low-Level Manual Tactics

For fine-grained control, use these macros from `LeanCert.Tactic.Interval`:

```lean
import LeanCert.Tactic.Interval

open LeanCert.Core LeanCert.Engine

def xSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)
def xSq_supp : ExprSupportedCore xSq :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)

-- Manual bounds with explicit AST and support proof
example : ∀ x ∈ I01, Expr.eval (fun _ => x) xSq ≤ (1 : ℚ) := by
  interval_le xSq, xSq_supp, I01, 1

example : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) xSq := by
  interval_ge xSq, xSq_supp, I01, 0
```

| Macro | Purpose |
|-------|---------|
| `interval_le` | `∀ x ∈ I, f(x) ≤ c` |
| `interval_ge` | `∀ x ∈ I, c ≤ f(x)` |
| `interval_lt` | `∀ x ∈ I, f(x) < c` |
| `interval_gt` | `∀ x ∈ I, c < f(x)` |
| `interval_le_pt` | Pointwise `f(x) ≤ c` given `x ∈ I` |
| `interval_ge_pt` | Pointwise `c ≤ f(x)` given `x ∈ I` |

**Extended (noncomputable) versions** for expressions with `exp`:
`interval_ext_le`, `interval_ext_ge`, `interval_ext_lt`, `interval_ext_gt`

These reduce the goal to a rational inequality that must be proved manually.

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
