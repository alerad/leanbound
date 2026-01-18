# Golden Theorems

LeanCert operates on a **certificate-driven architecture**. The Python side discovers facts, and the Lean side verifies them using **Golden Theorems**.

## Concept

A Golden Theorem bridges the gap between a computable boolean check (which `native_decide` can run) and a semantic proposition about real numbers.

For example, to prove \\( f(x) \le c \\) for all \\( x \in I \\), we use:

\\[
\text{checkUpperBound}(e, I, c) = \text{true} \implies \forall x \in I,\ \text{eval}(x, e) \le c
\\]

The key insight is that the checker runs in the Lean kernel using computable rational arithmetic, while the conclusion is a statement about real numbers.

## Core Theorems

Golden Theorems are defined across multiple files:
- `Validity/Bounds.lean` - Rational arithmetic (default)
- `Validity/DyadicBounds.lean` - Dyadic arithmetic (fast)
- `Validity/AffineBounds.lean` - Affine arithmetic (tight bounds)
- `Validity/Monotonicity.lean` - Monotonicity via automatic differentiation

### Bound Verification

| Goal | Theorem | Checker |
|------|---------|---------|
| Upper bound \\( f(x) \le c \\) | `verify_upper_bound` | `checkUpperBound` |
| Lower bound \\( c \le f(x) \\) | `verify_lower_bound` | `checkLowerBound` |
| Strict upper \\( f(x) < c \\) | `verify_strict_upper_bound` | `checkStrictUpperBound` |
| Strict lower \\( c < f(x) \\) | `verify_strict_lower_bound` | `checkStrictLowerBound` |

```lean
theorem verify_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c
```

### Root Finding

| Goal | Theorem | Checker |
|------|---------|---------|
| Root existence | `verify_sign_change` | `checkSignChange` |
| Root uniqueness | `verify_unique_root_core` | `checkNewtonContracts` |
| No roots | `verify_no_root` | `checkNoRoot` |

```lean
theorem verify_sign_change (e : Expr) (hsupp : ExprSupportedCore e)
    (hcont : ContinuousOn (Expr.evalAlong e ρ 0) (Set.Icc I.lo I.hi))
    (I : IntervalRat) (cfg : EvalConfig)
    (h_cert : checkSignChange e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0
```

### Global Optimization

| Goal | Theorem | Checker |
|------|---------|---------|
| Global lower bound | `verify_global_lower_bound` | `checkGlobalLowerBound` |
| Global upper bound | `verify_global_upper_bound` | `checkGlobalUpperBound` |

```lean
theorem verify_global_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (box : Box) (c : ℚ) (cfg : GlobalOptConfig)
    (h_cert : (globalMinimizeCore e box cfg).lo ≥ c) :
    ∀ x ∈ box, Expr.eval x e ≥ c
```

### Integration

```lean
theorem verify_integral_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (n : ℕ) (lo hi : ℚ)
    (h_cert : checkIntegralBoundsCore e I n = some (lo, hi)) :
    lo ≤ ∫ x in I.lo..I.hi, Expr.eval (fun _ => x) e ∧
    ∫ x in I.lo..I.hi, Expr.eval (fun _ => x) e ≤ hi
```

### Monotonicity

Prove monotonicity properties using automatic differentiation with interval arithmetic.

| Goal | Theorem | Checker |
|------|---------|---------|
| Strictly increasing | `verify_strictly_increasing` | `checkStrictlyIncreasing` |
| Strictly decreasing | `verify_strictly_decreasing` | `checkStrictlyDecreasing` |
| Monotone (weak) | `verify_monotone` | `checkStrictlyIncreasing` |
| Antitone (weak) | `verify_antitone` | `checkStrictlyDecreasing` |

```lean
theorem verify_strictly_increasing (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    StrictMonoOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)
```

The approach uses automatic differentiation to compute interval bounds on derivatives:
1. Compute `dI := derivIntervalCore e I cfg` (interval containing all derivatives)
2. If `dI.lo > 0`, then f'(x) > 0 for all x ∈ I, so f is strictly increasing
3. If `dI.hi < 0`, then f'(x) < 0 for all x ∈ I, so f is strictly decreasing

The mathematical foundation is the Mean Value Theorem: if f' has consistent sign, then f is monotonic.

**Example:**
```lean
-- Prove exp is strictly increasing on [0, 1]
theorem exp_strictly_increasing :
    StrictMonoOn (fun x => Real.exp x) (Set.Icc 0 1) := by
  have h := verify_strictly_increasing (Expr.exp (Expr.var 0))
    (ExprSupported.exp (ExprSupported.var 0))
    ⟨0, 1, by norm_num⟩ {} (by native_decide)
  simp only [Expr.eval_exp, Expr.eval_var] at h
  convert h using 2 <;> simp
```

## Expression Support Tiers

Not all expressions support all theorems.

### ExprSupportedCore

Fully computable subset enabling `native_decide`:

- `const`, `var`, `add`, `mul`, `neg`
- `sin`, `cos`, `exp`, `sqrt` (via Taylor series)

### ExprSupportedWithInv

Extended support including partial functions:

- Everything in `ExprSupportedCore`
- `inv`, `log`, `atan`, `arsinh`, `atanh`, `sinc`, `erf`

These require `evalInterval?` which may return `none` if domain constraints are violated.

## Arithmetic Backends

LeanCert provides three arithmetic backends, each with different tradeoffs:

| Backend | File | Speed | Precision | Best For |
|---------|------|-------|-----------|----------|
| **Rational** | `Validity/Bounds.lean` | Slow | Exact | Small expressions, reproducibility |
| **Dyadic** | `Validity/DyadicBounds.lean` | Fast | Fixed-precision | Deep expressions, neural networks |
| **Affine** | `Validity/AffineBounds.lean` | Medium | Correlation-aware | Dependency-heavy expressions |

### Rational Backend (Default)

The standard backend using arbitrary-precision rationals. Guarantees exact intermediate results but can suffer from denominator explosion on deep expressions.

### Dyadic Backend

Uses fixed-precision dyadic numbers (m · 2^e) to avoid denominator explosion:

```lean
theorem verify_upper_bound_dyadic (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalDyadic) (c : Dyadic) (cfg : DyadicConfig)
    (h_cert : checkUpperBoundDyadic e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c
```

Key parameters:
- `prec : Int` - Precision (negative = more precision, must be ≤ 0)
- `depth : Nat` - Taylor series depth for transcendentals

Essential for neural network verification and optimization loops where expression depth can be in the hundreds.

### Affine Backend

Solves the "dependency problem" in interval arithmetic by tracking linear correlations:

```lean
theorem verify_upper_bound_affine1 (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (h_cert : checkUpperBoundAffine1 e I c cfg = true)
    (hvalid : domainValidAt e (fun _ => I)) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c
```

Affine arithmetic represents values as `x̂ = c₀ + Σᵢ cᵢ·εᵢ + [-r, r]` where εᵢ ∈ [-1, 1] are noise symbols. This means:

- Standard IA: `x - x` on `[-1, 1]` → `[-2, 2]` (pessimistic)
- Affine AA: `x - x` on `[-1, 1]` → `[0, 0]` (exact)

Use affine when the same variable appears multiple times in an expression.

## Backend Theorems Summary

| Goal | Rational | Dyadic | Affine |
|------|----------|--------|--------|
| Upper bound | `verify_upper_bound` | `verify_upper_bound_dyadic` | `verify_upper_bound_affine1` |
| Lower bound | `verify_lower_bound` | `verify_lower_bound_dyadic` | `verify_lower_bound_affine1` |

Each backend also provides `'` variants for `ExprSupported` expressions where domain validity is automatic:
- `verify_upper_bound_dyadic'`
- `verify_lower_bound_affine1'`
- etc.

## Kernel Verification

For higher trust, the dyadic backend supports verification via `decide` instead of `native_decide`:

| Theorem | Verification | Trust Level |
|---------|--------------|-------------|
| `verify_upper_bound_dyadic` | `decide` | Kernel only |
| `verify_lower_bound_dyadic` | `decide` | Kernel only |

This removes the compiler from the trusted computing base—only the Lean kernel must be trusted.

**Note**: Kernel verification requires the goal to be in `Core.Expr.eval` form with rational interval bounds.

## The Certificate Workflow

1. **Python discovers**: Find bounds, roots, or optima
2. **Python generates certificate**: Parameters that make the checker return `true`
3. **Lean verifies**: Run the checker via `native_decide`
4. **Golden theorem applies**: Boolean `true` lifts to semantic proof

```
Python                           Lean
──────                           ────
find_bounds(x²+sin(x), [0,1])
    │
    ▼
{expr: "...", interval: [0,1],   ──▶  checkUpperBound(...) = true
 upper_bound: 2, config: {...}}        │
                                       ▼
                                  verify_upper_bound(...)
                                       │
                                       ▼
                                  ∀ x ∈ [0,1], x² + sin(x) ≤ 2
```
