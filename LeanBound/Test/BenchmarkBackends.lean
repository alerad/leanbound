/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Expr
import LeanBound.Core.IntervalReal
import LeanBound.Core.IntervalDyadic
import LeanBound.Numerics.IntervalEval
import LeanBound.Numerics.IntervalEvalDyadic

/-!
# Performance Benchmark: Dyadic vs Rational Backend

This file benchmarks the performance difference between rational (IntervalRat)
and dyadic (IntervalDyadic) interval arithmetic backends.

## Benchmark Categories

1. **Polynomial expressions** - Test denominator explosion in rational arithmetic
2. **Deep multiplications** - Stress test for GCD normalization overhead
3. **Transcendental functions** - sin, cos, exp with Taylor series
4. **Nested transcendentals** - sin(sin(sin(x))), etc.
5. **Mixed expressions** - Polynomials + transcendentals

## Expected Results

The dyadic backend should be 10-100x faster for deep expressions due to:
- No GCD normalization (uses bit-shifts instead)
- Bounded precision prevents mantissa explosion
- O(1) rounding instead of O(n) GCD for n-digit numbers

## Usage

Run with: `lake exe leanbound-bench` or evaluate in Lean REPL.
-/

namespace LeanBound.Benchmark

open LeanBound.Core
open LeanBound.Numerics

/-! ### Test Expression Generators -/

/-- Create a polynomial: x^n -/
def mkPowerExpr (n : Nat) : Expr :=
  match n with
  | 0 => Expr.const 1
  | n + 1 => Expr.mul (Expr.var 0) (mkPowerExpr n)

/-- Create a polynomial: 1 + x + x² + ... + x^n -/
def mkPolynomialExpr (n : Nat) : Expr :=
  match n with
  | 0 => Expr.const 1
  | m + 1 => Expr.add (mkPolynomialExpr m) (mkPowerExpr (m + 1))

/-- Create deep multiplication: ((x * x) * x) * ... -/
def mkDeepMulExpr (n : Nat) : Expr :=
  match n with
  | 0 => Expr.var 0
  | m + 1 => Expr.mul (mkDeepMulExpr m) (Expr.var 0)

/-- Create nested sin: sin(sin(...sin(x)...)) -/
def mkNestedSin (n : Nat) : Expr :=
  match n with
  | 0 => Expr.var 0
  | m + 1 => Expr.sin (mkNestedSin m)

/-- Create nested exp: exp(exp(...exp(x)...)) - careful with bounds! -/
def mkNestedExp (n : Nat) : Expr :=
  match n with
  | 0 => Expr.var 0
  | m + 1 => Expr.exp (mkNestedExp m)

/-- Create expression: sin(x) * cos(x) + exp(-x²) -/
def mkMixedExpr : Expr :=
  let sinx := Expr.sin (Expr.var 0)
  let cosx := Expr.cos (Expr.var 0)
  let x2 := Expr.mul (Expr.var 0) (Expr.var 0)
  let negx2 := Expr.neg x2
  let expnegx2 := Expr.exp negx2
  Expr.add (Expr.mul sinx cosx) expnegx2

/-- Create Horner-form polynomial: a₀ + x(a₁ + x(a₂ + ...)) -/
def mkHornerPoly (coeffs : List ℚ) : Expr :=
  match coeffs with
  | [] => Expr.const 0
  | [a] => Expr.const a
  | a :: rest => Expr.add (Expr.const a) (Expr.mul (Expr.var 0) (mkHornerPoly rest))

/-- Create expression with many adds and muls: (x+1)^n expanded -/
def mkExpandedBinomial (n : Nat) : Expr :=
  match n with
  | 0 => Expr.const 1
  | m + 1 =>
    let xp1 := Expr.add (Expr.var 0) (Expr.const 1)
    Expr.mul xp1 (mkExpandedBinomial m)

/-! ### Benchmark Intervals -/

/-- Standard test interval [-1, 1] -/
def testIntervalRat : IntervalRat := ⟨-1, 1, by norm_num⟩

/-- Small interval [0.1, 0.2] for exp tests -/
def smallIntervalRat : IntervalRat := ⟨1/10, 1/5, by norm_num⟩

/-- Dyadic version of test interval -/
def testIntervalDyadic : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat testIntervalRat (-53)

/-- Dyadic version of small interval -/
def smallIntervalDyadic : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat smallIntervalRat (-53)

/-! ### Benchmark Runner Functions -/

/-- Evaluate using rational backend -/
def evalRational (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  evalIntervalCore e (fun _ => I) cfg

/-- Evaluate using dyadic backend -/
def evalDyadic (e : Expr) (I : IntervalDyadic) (cfg : DyadicConfig := {}) : IntervalDyadic :=
  evalIntervalDyadic e (fun _ => I) cfg

/-! ### Concrete Benchmark Expressions -/

-- Polynomial benchmarks
def polyExpr5 : Expr := mkPolynomialExpr 5
def polyExpr10 : Expr := mkPolynomialExpr 10
def polyExpr15 : Expr := mkPolynomialExpr 15
def polyExpr20 : Expr := mkPolynomialExpr 20

-- Deep multiplication benchmarks
def deepMul10 : Expr := mkDeepMulExpr 10
def deepMul20 : Expr := mkDeepMulExpr 20
def deepMul30 : Expr := mkDeepMulExpr 30
def deepMul50 : Expr := mkDeepMulExpr 50

-- Nested sin benchmarks
def nestedSin3 : Expr := mkNestedSin 3
def nestedSin5 : Expr := mkNestedSin 5
def nestedSin7 : Expr := mkNestedSin 7

-- Nested exp benchmarks (use small interval)
def nestedExp2 : Expr := mkNestedExp 2
def nestedExp3 : Expr := mkNestedExp 3

-- Horner polynomial benchmarks
def horner10 : Expr := mkHornerPoly [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def horner20 : Expr := mkHornerPoly (List.range 20 |>.map (fun n => (n + 1 : ℚ)))

-- Binomial expansion benchmarks
def binomial5 : Expr := mkExpandedBinomial 5
def binomial10 : Expr := mkExpandedBinomial 10
def binomial15 : Expr := mkExpandedBinomial 15

/-! ### Run Benchmarks -/

/-- Benchmark result structure -/
structure BenchResult where
  name : String
  ratLo : ℚ
  ratHi : ℚ
  dyadLo : ℚ
  dyadHi : ℚ
  deriving Repr

/-- Run a single benchmark comparing both backends -/
def runBenchmark (name : String) (e : Expr) (Irat : IntervalRat) (Idyad : IntervalDyadic)
    (ratCfg : EvalConfig := {}) (dyadCfg : DyadicConfig := {}) : BenchResult :=
  let ratResult := evalRational e Irat ratCfg
  let dyadResult := evalDyadic e Idyad dyadCfg
  { name := name
    ratLo := ratResult.lo
    ratHi := ratResult.hi
    dyadLo := dyadResult.lo.toRat
    dyadHi := dyadResult.hi.toRat }

/-! ### Benchmark Execution -/

-- Polynomial benchmarks
#eval runBenchmark "poly5" polyExpr5 testIntervalRat testIntervalDyadic
#eval runBenchmark "poly10" polyExpr10 testIntervalRat testIntervalDyadic
#eval runBenchmark "poly15" polyExpr15 testIntervalRat testIntervalDyadic
-- #eval runBenchmark "poly20" polyExpr20 testIntervalRat testIntervalDyadic  -- May be slow for rational

-- Deep multiplication benchmarks
#eval runBenchmark "deepMul10" deepMul10 testIntervalRat testIntervalDyadic
#eval runBenchmark "deepMul20" deepMul20 testIntervalRat testIntervalDyadic
#eval runBenchmark "deepMul30" deepMul30 testIntervalRat testIntervalDyadic
-- #eval runBenchmark "deepMul50" deepMul50 testIntervalRat testIntervalDyadic  -- May timeout for rational

-- Nested sin benchmarks
#eval runBenchmark "nestedSin3" nestedSin3 testIntervalRat testIntervalDyadic
#eval runBenchmark "nestedSin5" nestedSin5 testIntervalRat testIntervalDyadic
-- #eval runBenchmark "nestedSin7" nestedSin7 testIntervalRat testIntervalDyadic  -- Slow for rational

-- Nested exp benchmarks (small interval to prevent overflow)
#eval runBenchmark "nestedExp2" nestedExp2 smallIntervalRat smallIntervalDyadic
#eval runBenchmark "nestedExp3" nestedExp3 smallIntervalRat smallIntervalDyadic

-- Horner polynomial benchmarks
#eval runBenchmark "horner10" horner10 testIntervalRat testIntervalDyadic
#eval runBenchmark "horner20" horner20 testIntervalRat testIntervalDyadic

-- Binomial expansion benchmarks
#eval runBenchmark "binomial5" binomial5 testIntervalRat testIntervalDyadic
#eval runBenchmark "binomial10" binomial10 testIntervalRat testIntervalDyadic
-- #eval runBenchmark "binomial15" binomial15 testIntervalRat testIntervalDyadic  -- May be slow

-- Mixed expression benchmark
#eval runBenchmark "mixed" mkMixedExpr testIntervalRat testIntervalDyadic

/-! ### Dyadic-Only Benchmarks (for expressions too slow with rational) -/

/-- Run dyadic-only benchmark -/
def runDyadicOnly (name : String) (e : Expr) (I : IntervalDyadic)
    (cfg : DyadicConfig := {}) : String :=
  let result := evalDyadic e I cfg
  s!"{name}: [{result.lo.toRat}, {result.hi.toRat}]"

-- These would timeout with rational backend
#eval runDyadicOnly "poly20_dyadic" polyExpr20 testIntervalDyadic
#eval runDyadicOnly "deepMul50_dyadic" deepMul50 testIntervalDyadic
#eval runDyadicOnly "deepMul100_dyadic" (mkDeepMulExpr 100) testIntervalDyadic
#eval runDyadicOnly "nestedSin10_dyadic" (mkNestedSin 10) testIntervalDyadic
#eval runDyadicOnly "binomial20_dyadic" (mkExpandedBinomial 20) testIntervalDyadic

/-! ### Precision Comparison -/

/-- Compare precision at different dyadic settings -/
def comparePrecision (e : Expr) (I : IntervalDyadic) : String :=
  let fast := evalDyadic e I DyadicConfig.fast
  let standard := evalDyadic e I {}
  let highPrec := evalDyadic e I DyadicConfig.highPrecision
  let fastWidth := fast.hi.toRat - fast.lo.toRat
  let stdWidth := standard.hi.toRat - standard.lo.toRat
  let highWidth := highPrec.hi.toRat - highPrec.lo.toRat
  s!"fast: {fastWidth}, std: {stdWidth}, high: {highWidth}"

#eval comparePrecision nestedSin5 testIntervalDyadic
#eval comparePrecision horner10 testIntervalDyadic
#eval comparePrecision mkMixedExpr testIntervalDyadic

/-! ### Verification: Results are sound -/

-- The dyadic results should contain the rational results (they're both sound)
-- Dyadic may have slightly wider intervals due to rounding

example : (evalDyadic polyExpr5 testIntervalDyadic).lo.toRat ≤
          (evalRational polyExpr5 testIntervalRat).lo := by native_decide

example : (evalRational polyExpr5 testIntervalRat).hi ≤
          (evalDyadic polyExpr5 testIntervalDyadic).hi.toRat := by native_decide

end LeanBound.Benchmark
