# Verification Status

LeanCert aims for full formal verification. This page documents what is **fully proved** versus what contains `sorry` (unfinished proofs).

## Fully Verified

The following components have complete proofs with no `sorry`:

### Interval Arithmetic (FTIA)

The Fundamental Theorem of Interval Arithmetic is proved for all basic operations:

- Addition, subtraction: \\( x \in I_1, y \in I_2 \implies x + y \in I_1 + I_2 \\)
- Multiplication: \\( x \in I_1, y \in I_2 \implies x \cdot y \in I_1 \cdot I_2 \\)
- Division: \\( x \in I_1, y \in I_2, 0 \notin I_2 \implies x / y \in I_1 / I_2 \\)
- Power: \\( x \in I \implies x^n \in I^n \\)

### Transcendental Functions

Rigorous bounds via Taylor series with verified remainder terms:

| Function | Theorem | Location |
|----------|---------|----------|
| \\( e^x \\) | `mem_expInterval` | `Core/IntervalReal.lean` |
| \\( \sin x \\) | `mem_sinInterval` | `Core/IntervalReal.lean` |
| \\( \cos x \\) | `mem_cosInterval` | `Core/IntervalReal.lean` |
| \\( \log x \\) | `mem_logInterval` | `Core/IntervalReal.lean` |
| \\( \sinh x \\) | `mem_sinhInterval` | `Core/IntervalReal.lean` |
| \\( \cosh x \\) | `mem_coshInterval` | `Core/IntervalReal.lean` |
| \\( \tanh x \\) | `mem_tanhInterval` | `Core/IntervalReal.lean` |
| \\( \arctan x \\) | `mem_atanInterval` | `Core/IntervalReal.lean` |
| \\( \text{arsinh} x \\) | `mem_arsinhInterval` | `Core/IntervalReal.lean` |
| \\( \text{atanh} x \\) | `mem_atanhInterval` | `Engine/IntervalEval.lean` |

### Extended Interval Arithmetic

Standard interval arithmetic fails when dividing by an interval containing zero. LeanCert's **Extended Arithmetic** returns a union of intervals, preserving soundness even across singularities.

- **Theorem**: `evalExtended_correct_core`
- **Behavior**: 1 / [-1, 1] → (-∞, -1] ∪ [1, ∞)
- **Status**: Verified for core expressions

This enables robust handling of expressions like 1/x near x = 0.

### Taylor Series

The core Taylor remainder bounds are fully proved:

```lean
theorem taylor_remainder_bound (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) ...
```

This is the foundation for all transcendental function bounds.

### Automatic Differentiation

Forward-mode AD with verified value and derivative bounds:

- `evalDual_val_correct`: Value component is correct
- `evalDual_der_correct`: Derivative component is correct

### Global Optimization

Branch-and-bound with formal guarantees:

- `globalMinimize_lo_correct`: Lower bound is valid
- `globalMaximize_hi_correct`: Upper bound is valid

### Root Finding

- **Bisection**: `verify_sign_change` proves existence via IVT
- **Newton**: `verify_unique_root_core` proves uniqueness via contraction

### Integration

- `integrateInterval_correct`: Riemann sum bounds contain the true integral

### Dyadic Backend

The high-performance dyadic interval evaluator is fully verified:

- `evalIntervalDyadic_correct`: Dyadic evaluation produces sound intervals
- `IntervalDyadic.mem_add`, `mem_mul`, `mem_neg`: FTIA for dyadic operations
- `IntervalDyadic.roundOut_contains`: Outward rounding preserves containment

The dyadic backend avoids rational denominator explosion by using fixed-precision arithmetic:

| Expression | Rational Denominator | Dyadic Mantissa |
|------------|---------------------|-----------------|
| `exp(exp(x))` | ~200 digits | 17 digits |
| `exp(exp(exp(x)))` | ~2000 digits | 18 digits |

See `LeanCert/Test/BenchmarkBackends.lean` for performance comparisons.

### Neural Network Verification

The ML module provides verified interval propagation for neural networks:

- `mem_forwardInterval`: Soundness of dense layer propagation
- `mem_relu`, `mem_sigmoid`: Activation function soundness
- `relu_relaxation_sound`: DeepPoly ReLU triangle relaxation
- `sigmoid_relaxation_sound`: DeepPoly sigmoid monotonicity bounds

**Transformer Components:**

- `mem_scaledDotProductAttention`: Soundness of Q×K^T + Softmax + V
- `mem_layerNormInterval`: Soundness of Layer Normalization
- `mem_geluInterval`: Soundness of GELU activation
- `forwardQuantized_sound`: Soundness of integer-quantized split-sign inference

See `LeanCert/ML/` for the full implementation.

### Kernel Verification (Dyadic)

Bridge theorems for kernel-level verification via `decide`:

- `verify_upper_bound_dyadic`: Connects Dyadic boolean check to Real semantic bounds
- `verify_lower_bound_dyadic`: Lower bound variant
- `evalIntervalDyadic_correct`: Dyadic evaluation is sound w.r.t Real operations

These enable the `certify_kernel` tactic to produce proofs verified purely by the Lean kernel, removing the compiler from the trusted computing base.

## Incomplete (Contains `sorry`)

These features work computationally but have gaps in formal proofs:

| Component | Issue | Impact |
|-----------|-------|--------|
| `atanh` Taylor | `atanh_series_remainder_bound` incomplete | Medium - affects precision |
| `log` Taylor model | `tmLog_correct` incomplete | Low - basic interval verified |
| `sinc` derivative | Missing `Differentiable ℝ Real.sinc` | Low - exotic function |
| `erf` derivative | Missing `Differentiable ℝ Real.erf` | Low - exotic function |

## Finding Sorries

To audit the codebase yourself:

```bash
grep -r "sorry" --include="*.lean" LeanCert/ | grep -v "no sorry"
```

Current count: 6 declarations using `sorry`, all in edge cases for exotic functions (Taylor remainders for atanh/log, differentiability of sinc/erf).

## What This Means

**For typical use cases** (polynomials, `sin`, `cos`, `exp`, `log`, optimization, root finding):

> The verification is complete. Proofs generated by LeanCert are accepted by the Lean kernel with no axioms beyond standard Mathlib foundations.

**For `atanh`**:

> The basic interval theorem `mem_atanhInterval` is fully verified (requires domain hypotheses). The Taylor model path `atanh_series_remainder_bound` has a gap.

**For `sinc`, `erf`**:

> These work computationally, but formal proofs have gaps (missing differentiability proofs in Mathlib). Use with awareness that the Lean proofs contain `sorry`.
