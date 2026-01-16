# Result Types

LeanCert returns rich result objects containing both numerical data and verification certificates.

## BoundsResult

Returned by `find_bounds()`.

::: leancert.result.BoundsResult
    options:
      show_root_heading: true

## RootsResult

Returned by `find_roots()`.

::: leancert.result.RootsResult
    options:
      show_root_heading: true

## RootInterval

Represents an isolating interval for a root.

::: leancert.result.RootInterval
    options:
      show_root_heading: true

## UniqueRootResult

Returned by `find_unique_root()`.

::: leancert.result.UniqueRootResult
    options:
      show_root_heading: true

## IntegralResult

Returned by `integrate()`.

::: leancert.result.IntegralResult
    options:
      show_root_heading: true

## Certificate

Contains the verification certificate that can be exported to Lean.

::: leancert.result.Certificate
    options:
      show_root_heading: true
      members:
        - to_lean_tactic
        - save
        - load

## VerifyResult

Returned by `verify_bound()`.

::: leancert.result.VerifyResult
    options:
      show_root_heading: true

## Discovery Results (Lean)

The Lean side provides structured result types for discovery operations.

### VerifiedGlobalMin

Contains the lower bound, the box where it was found, and the formal proof.

```lean
structure VerifiedGlobalMin where
  lowerBound : ℚ
  achievingBox : Box
  proof : ∀ x ∈ domain, f x ≥ lowerBound
```

### VerifiedRoot

Contains an isolating interval for a root and the proof of existence (via sign change/IVT).

```lean
structure VerifiedRoot where
  interval : IntervalRat
  proof : ∃ x ∈ interval, f x = 0
```

### VerifiedEquivalence

Contains the certificate that two neural networks produce outputs within a specific tolerance ε.

```lean
structure VerifiedEquivalence where
  tolerance : ℚ
  proof : ∀ x ∈ domain, |teacher x - student x| ≤ tolerance
```
