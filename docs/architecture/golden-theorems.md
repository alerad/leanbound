# Golden Theorems

LeanBound operates on a **certificate-driven architecture**. The Python side discovers facts, and the Lean side verifies them using **Golden Theorems**.

## Concept

A Golden Theorem bridges the gap between a computable boolean check (which `native_decide` can run) and a semantic proposition about real numbers.

For example, to prove \\( f(x) \le c \\) for all \\( x \in I \\), we use:

\\[
\text{checkUpperBound}(e, I, c) = \text{true} \implies \forall x \in I,\ \text{eval}(x, e) \le c
\\]

The key insight is that the checker runs in the Lean kernel using computable rational arithmetic, while the conclusion is a statement about real numbers.

## Core Theorems

All Golden Theorems are defined in `Numerics/Certificate.lean`.

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

## Dyadic Backend

For deep expressions, the dyadic evaluator provides the same correctness guarantees:

```lean
theorem evalIntervalDyadic_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig) :
    Expr.eval ρ_real e ∈ evalIntervalDyadic e ρ_dyad cfg
```

The dyadic backend avoids denominator explosion by using fixed-precision arithmetic, making it essential for neural network verification and optimization loops.

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
