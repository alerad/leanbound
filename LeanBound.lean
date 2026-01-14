/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/

-- Core modules
import LeanBound.Core.Expr
import LeanBound.Core.Interval
import LeanBound.Core.IntervalReal
import LeanBound.Core.IntervalRealEndpoints
import LeanBound.Core.Taylor
import LeanBound.Core.DerivativeIntervals
-- v1.1: Dyadic arithmetic (high-performance alternative to Rat)
import LeanBound.Core.Dyadic
import LeanBound.Core.IntervalDyadic

-- Numerics modules
import LeanBound.Numerics.IntervalEval
import LeanBound.Numerics.IntervalEvalReal
import LeanBound.Numerics.AD
import LeanBound.Numerics.Integrate
import LeanBound.Numerics.Optimize
import LeanBound.Numerics.RootFinding.Main
import LeanBound.Numerics.TaylorModel
import LeanBound.Numerics.IntervalEvalRefined
import LeanBound.Numerics.Certificate
-- v1.1: Dyadic evaluator (prevents denominator explosion)
import LeanBound.Numerics.IntervalEvalDyadic

-- Global Optimization
import LeanBound.Numerics.Optimization.Box
import LeanBound.Numerics.Optimization.Gradient
import LeanBound.Numerics.Optimization.Global
import LeanBound.Numerics.Optimization.Guided

-- Affine Arithmetic
import LeanBound.Numerics.Affine.Basic
import LeanBound.Numerics.Affine.Nonlinear
import LeanBound.Numerics.Affine.Transcendental
import LeanBound.Numerics.Affine.Vector

-- Extended Numerics
import LeanBound.Numerics.Extended

-- Search + Certify APIs
import LeanBound.Numerics.SearchAPI

-- Tactics
import LeanBound.Tactic.Interval
import LeanBound.Tactic.Discovery
-- v1.1: fast_bound tactic (uses Dyadic backend)
import LeanBound.Tactic.DyadicAuto
-- Counter-example hunting
import LeanBound.Tactic.Refute

-- Discovery Mode
import LeanBound.Discovery

-- Machine Learning
import LeanBound.ML.Network
import LeanBound.ML.IntervalVector
import LeanBound.ML.Distillation
import LeanBound.ML.Symbolic.ReLU
import LeanBound.ML.Symbolic.Sigmoid
import LeanBound.ML.Transformer
import LeanBound.ML.Softmax
import LeanBound.ML.Attention
import LeanBound.ML.Optimized.MatrixNetwork

-- ML Examples
import LeanBound.Examples.ML.Distillation

-- Examples
import LeanBound.Examples.Basic
import LeanBound.Examples.Calculus
import LeanBound.Examples.Numerics
import LeanBound.Examples.Tactics
import LeanBound.Examples.Certificate
import LeanBound.Examples.GlobalOptimization

/-! ## Public API

The `LeanBound` namespace re-exports the most commonly used definitions
so users can write `open LeanBound` and have immediate access to the core API.
-/

namespace LeanBound

-- Re-export core expression types
export LeanBound.Core (Expr)

-- Re-export interval types
export LeanBound.Core (IntervalRat)

-- v1.1: Re-export Dyadic types (high-performance arithmetic)
export LeanBound.Core (Dyadic IntervalDyadic)

-- Re-export evaluation and interval operations
export LeanBound.Numerics (
  ExprSupported
  ExprSupportedCore
  EvalConfig
  evalInterval
  evalInterval1
  evalInterval_correct
  evalInterval1_correct
  evalIntervalCore
  evalIntervalCore1
  evalIntervalCore_correct
  evalIntervalCore1_correct
  -- Refined evaluation (uses Taylor models for tighter bounds)
  evalIntervalRefined
  evalIntervalRefined1
  evalIntervalRefined_correct
  evalIntervalRefined1_correct
  DualInterval
  evalDual
  derivInterval
  -- Refined AD evaluation
  evalDualRefined
  evalDualRefined1
  evalDualRefined_val_correct
  -- v1.1: Dyadic evaluation (prevents denominator explosion)
  DyadicConfig
  evalIntervalDyadic
  evalIntervalDyadic_correct
  checkUpperBoundDyadic
  checkLowerBoundDyadic
  checkBoundsDyadic
)

-- Re-export certificate verification
export LeanBound.Numerics.Certificate (
  checkUpperBound
  checkLowerBound
  checkStrictUpperBound
  checkStrictLowerBound
  checkBounds
  verify_upper_bound
  verify_lower_bound
  verify_strict_upper_bound
  verify_strict_lower_bound
  verify_bounds
)

-- Re-export root finding
export LeanBound.Numerics (
  RootStatus
  bisectRoot
  BisectionResult
)

-- Re-export integration
export LeanBound.Numerics (
  integrateInterval
)

-- Re-export optimization
export LeanBound.Numerics (
  minimizeInterval
  maximizeInterval
  OptResult
)

-- Re-export global optimization
export LeanBound.Numerics.Optimization (
  Box
  GlobalOptConfig
  GlobalBound
  GlobalResult
  globalMinimizeCore
  globalMaximizeCore
)

-- Re-export Discovery Mode
export LeanBound.Discovery (
  DiscoveryConfig
  VerifiedGlobalMin
  VerifiedGlobalMax
  VerifiedRoot
  VerifiedIntegral
  VerifiedUpperBound
  VerifiedLowerBound
  findGlobalMin
  findGlobalMax
  verifyUpperBound
  verifyLowerBound
  searchRoots
)

-- Re-export ML/Distillation API
export LeanBound.ML.Distillation (
  SequentialNet
  checkEquivalence
  verify_equivalence
)

-- Re-export Search + Certify APIs
export LeanBound.Numerics.SearchAPI (
  -- Root Finding API
  RootSearchConfig
  RootExistenceProof
  UniqueRootProof
  RootIsolation
  UniqueRootResult
  findRoots
  findUniqueRoot
  -- Optimization API
  OptSearchConfig
  GlobalMinResult
  GlobalMaxResult
  GlobalMin1DResult
  GlobalMax1DResult
  findGlobalMin1D
  findGlobalMax1D
  -- Integration API
  IntegSearchConfig
  IntegralResult
  findIntegral
  findIntegralWithTolerance
  -- Convenience functions
  hasRootIn
  isPositiveOn
  isNegativeOn
  getLowerBound
  getUpperBound
)

/-! ### Convenience abbreviations -/

/-- Evaluate a single-variable expression at a real point.
    Shorthand for `Expr.eval (fun _ => x) e`. -/
noncomputable abbrev eval₀ (e : LeanBound.Core.Expr) (x : ℝ) : ℝ := LeanBound.Core.Expr.eval (fun _ => x) e

/-- Evaluate a single-variable expression at a rational point.
    Useful for `#eval` demonstrations. -/
def eval₀_rat (e : LeanBound.Core.Expr) (x : ℚ) : ℚ :=
  match e with
  | .const q => q
  | .var _ => x
  | .add e₁ e₂ => eval₀_rat e₁ x + eval₀_rat e₂ x
  | .mul e₁ e₂ => eval₀_rat e₁ x * eval₀_rat e₂ x
  | .neg e => -eval₀_rat e x
  | .inv e => (eval₀_rat e x)⁻¹
  | .exp _ => 0  -- Not computable over ℚ
  | .sin _ => 0  -- Not computable over ℚ
  | .cos _ => 0  -- Not computable over ℚ
  | .log _ => 0  -- Not computable over ℚ
  | .atan _ => 0  -- Not computable over ℚ
  | .arsinh _ => 0  -- Not computable over ℚ
  | .atanh _ => 0  -- Not computable over ℚ
  | .sinc _ => 0  -- Not computable over ℚ
  | .erf _ => 0  -- Not computable over ℚ
  | .sinh _ => 0  -- Not computable over ℚ
  | .cosh _ => 0  -- Not computable over ℚ
  | .tanh _ => 0  -- Not computable over ℚ
  | .sqrt _ => 0  -- Not computable over ℚ
  | .pi => 157 / 50  -- Rational approximation of π ≈ 3.14

/-- The unit interval [0, 1] -/
def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The interval [-1, 1] -/
def symInterval : IntervalRat := ⟨-1, 1, by norm_num⟩

end LeanBound
