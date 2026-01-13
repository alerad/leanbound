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
# Timing Benchmark: Dyadic vs Rational Backend

This file provides timing measurements to compare the performance of
rational vs dyadic backends on various expressions.

## Usage

Run: `lake env lean --run LeanBound/Test/TimingBenchmark.lean`

Or build and run: `lake build TimingBenchmark && .lake/build/bin/TimingBenchmark`
-/

namespace LeanBound.Benchmark.Timing

open LeanBound.Core
open LeanBound.Numerics

/-! ### Expression Generators -/

def mkPowerExpr (n : Nat) : Expr :=
  match n with
  | 0 => Expr.const 1
  | n + 1 => Expr.mul (Expr.var 0) (mkPowerExpr n)

def mkPolynomialExpr (n : Nat) : Expr :=
  match n with
  | 0 => Expr.const 1
  | m + 1 => Expr.add (mkPolynomialExpr m) (mkPowerExpr (m + 1))

def mkDeepMulExpr (n : Nat) : Expr :=
  match n with
  | 0 => Expr.var 0
  | m + 1 => Expr.mul (mkDeepMulExpr m) (Expr.var 0)

def mkNestedSin (n : Nat) : Expr :=
  match n with
  | 0 => Expr.var 0
  | m + 1 => Expr.sin (mkNestedSin m)

def mkExpandedBinomial (n : Nat) : Expr :=
  match n with
  | 0 => Expr.const 1
  | m + 1 =>
    let xp1 := Expr.add (Expr.var 0) (Expr.const 1)
    Expr.mul xp1 (mkExpandedBinomial m)

def mkHornerPoly (coeffs : List ℚ) : Expr :=
  match coeffs with
  | [] => Expr.const 0
  | [a] => Expr.const a
  | a :: rest => Expr.add (Expr.const a) (Expr.mul (Expr.var 0) (mkHornerPoly rest))

/-! ### Test Intervals -/

def testIntervalRat : IntervalRat := ⟨-1, 1, by norm_num⟩
def smallIntervalRat : IntervalRat := ⟨1/10, 1/5, by norm_num⟩
def testIntervalDyadic : IntervalDyadic := IntervalDyadic.ofIntervalRat testIntervalRat (-53)
def smallIntervalDyadic : IntervalDyadic := IntervalDyadic.ofIntervalRat smallIntervalRat (-53)

/-! ### Evaluation Functions -/

def evalRational (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  evalIntervalCore e (fun _ => I) cfg

def evalDyadic (e : Expr) (I : IntervalDyadic) (cfg : DyadicConfig := {}) : IntervalDyadic :=
  evalIntervalDyadic e (fun _ => I) cfg

/-! ### Timing Infrastructure -/

/-- Run an IO action n times and collect timing -/
def timeAction (n : Nat) (action : IO Unit) : IO Nat := do
  let startTime ← IO.monoNanosNow
  for _ in [:n] do
    action
  let endTime ← IO.monoNanosNow
  return (endTime - startTime) / n

/-- Format nanoseconds as milliseconds with 2 decimal places -/
def formatNanos (ns : Nat) : String :=
  let ms := ns / 1000000
  let frac := (ns % 1000000) / 10000
  s!"{ms}.{String.mk (if frac < 10 then ['0', Char.ofNat (48 + frac)] else (frac.repr.toList.take 2))}"

/-- Benchmark a single expression with both backends -/
def benchmarkExpr (name : String) (e : Expr) (Irat : IntervalRat) (Idyad : IntervalDyadic)
    (iterations : Nat := 100) : IO Unit := do
  -- Force evaluation to avoid lazy evaluation effects
  let ratAction : IO Unit := do
    let result := evalRational e Irat
    if result.lo > result.hi then panic! "impossible" else pure ()

  let dyadAction : IO Unit := do
    let result := evalDyadic e Idyad
    if result.lo.toRat > result.hi.toRat then panic! "impossible" else pure ()

  let ratTime ← timeAction iterations ratAction
  let dyadTime ← timeAction iterations dyadAction

  let speedup := if dyadTime > 0 then (ratTime.toFloat / dyadTime.toFloat) else 0.0

  IO.println s!"  {name}: Rational={formatNanos ratTime}ms, Dyadic={formatNanos dyadTime}ms, Speedup={speedup.toString.take 5}x"

/-- Benchmark dyadic only (for expressions too slow with rational) -/
def benchmarkDyadicOnly (name : String) (e : Expr) (I : IntervalDyadic)
    (iterations : Nat := 100) : IO Unit := do
  let action : IO Unit := do
    let result := evalDyadic e I
    if result.lo.toRat > result.hi.toRat then panic! "impossible" else pure ()

  let time ← timeAction iterations action
  IO.println s!"  {name}: Dyadic={formatNanos time}ms (Rational too slow)"

/-! ### Main Benchmark Suite -/

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════╗"
  IO.println "║       Dyadic vs Rational Backend Performance Benchmark           ║"
  IO.println "╚══════════════════════════════════════════════════════════════════╝"
  IO.println ""

  IO.println "┌─────────────────────────────────────────────────────────────────┐"
  IO.println "│ 1. POLYNOMIAL EXPRESSIONS (1 + x + x² + ... + xⁿ)               │"
  IO.println "└─────────────────────────────────────────────────────────────────┘"
  benchmarkExpr "poly5" (mkPolynomialExpr 5) testIntervalRat testIntervalDyadic
  benchmarkExpr "poly10" (mkPolynomialExpr 10) testIntervalRat testIntervalDyadic
  benchmarkExpr "poly15" (mkPolynomialExpr 15) testIntervalRat testIntervalDyadic
  benchmarkDyadicOnly "poly20" (mkPolynomialExpr 20) testIntervalDyadic
  benchmarkDyadicOnly "poly30" (mkPolynomialExpr 30) testIntervalDyadic
  IO.println ""

  IO.println "┌─────────────────────────────────────────────────────────────────┐"
  IO.println "│ 2. DEEP MULTIPLICATION (x * x * x * ... * x)                    │"
  IO.println "└─────────────────────────────────────────────────────────────────┘"
  benchmarkExpr "deepMul10" (mkDeepMulExpr 10) testIntervalRat testIntervalDyadic
  benchmarkExpr "deepMul20" (mkDeepMulExpr 20) testIntervalRat testIntervalDyadic
  benchmarkExpr "deepMul30" (mkDeepMulExpr 30) testIntervalRat testIntervalDyadic
  benchmarkDyadicOnly "deepMul50" (mkDeepMulExpr 50) testIntervalDyadic
  benchmarkDyadicOnly "deepMul100" (mkDeepMulExpr 100) testIntervalDyadic
  IO.println ""

  IO.println "┌─────────────────────────────────────────────────────────────────┐"
  IO.println "│ 3. NESTED TRANSCENDENTALS (sin(sin(...sin(x)...)))              │"
  IO.println "└─────────────────────────────────────────────────────────────────┘"
  benchmarkExpr "nestedSin3" (mkNestedSin 3) testIntervalRat testIntervalDyadic 50
  benchmarkExpr "nestedSin5" (mkNestedSin 5) testIntervalRat testIntervalDyadic 20
  benchmarkDyadicOnly "nestedSin7" (mkNestedSin 7) testIntervalDyadic 20
  benchmarkDyadicOnly "nestedSin10" (mkNestedSin 10) testIntervalDyadic 10
  IO.println ""

  IO.println "┌─────────────────────────────────────────────────────────────────┐"
  IO.println "│ 4. BINOMIAL EXPANSION ((x+1)ⁿ expanded)                         │"
  IO.println "└─────────────────────────────────────────────────────────────────┘"
  benchmarkExpr "binomial5" (mkExpandedBinomial 5) testIntervalRat testIntervalDyadic
  benchmarkExpr "binomial10" (mkExpandedBinomial 10) testIntervalRat testIntervalDyadic
  benchmarkDyadicOnly "binomial15" (mkExpandedBinomial 15) testIntervalDyadic
  benchmarkDyadicOnly "binomial20" (mkExpandedBinomial 20) testIntervalDyadic
  IO.println ""

  IO.println "┌─────────────────────────────────────────────────────────────────┐"
  IO.println "│ 5. HORNER POLYNOMIALS (a₀ + x(a₁ + x(a₂ + ...)))                │"
  IO.println "└─────────────────────────────────────────────────────────────────┘"
  benchmarkExpr "horner10" (mkHornerPoly (List.range 10 |>.map (fun n => (n + 1 : ℚ)))) testIntervalRat testIntervalDyadic
  benchmarkExpr "horner20" (mkHornerPoly (List.range 20 |>.map (fun n => (n + 1 : ℚ)))) testIntervalRat testIntervalDyadic
  benchmarkDyadicOnly "horner30" (mkHornerPoly (List.range 30 |>.map (fun n => (n + 1 : ℚ)))) testIntervalDyadic
  IO.println ""

  IO.println "┌─────────────────────────────────────────────────────────────────┐"
  IO.println "│ 6. PRECISION COMPARISON (different DyadicConfig settings)       │"
  IO.println "└─────────────────────────────────────────────────────────────────┘"
  let testExpr := mkNestedSin 5

  let fastResult := evalIntervalDyadic testExpr (fun _ => testIntervalDyadic) DyadicConfig.fast
  let stdResult := evalIntervalDyadic testExpr (fun _ => testIntervalDyadic) {}
  let highResult := evalIntervalDyadic testExpr (fun _ => testIntervalDyadic) DyadicConfig.highPrecision

  IO.println s!"  nestedSin5 interval widths:"
  IO.println s!"    fast (-30 bits):  {(fastResult.hi.toRat - fastResult.lo.toRat)}"
  IO.println s!"    std  (-53 bits):  {(stdResult.hi.toRat - stdResult.lo.toRat)}"
  IO.println s!"    high (-100 bits): {(highResult.hi.toRat - highResult.lo.toRat)}"
  IO.println ""

  IO.println "╔══════════════════════════════════════════════════════════════════╗"
  IO.println "║                        SUMMARY                                   ║"
  IO.println "╠══════════════════════════════════════════════════════════════════╣"
  IO.println "║ The dyadic backend avoids denominator explosion in rational      ║"
  IO.println "║ arithmetic by using fixed-precision bit-shift operations.        ║"
  IO.println "║                                                                  ║"
  IO.println "║ Key advantages:                                                  ║"
  IO.println "║ • No GCD normalization overhead                                  ║"
  IO.println "║ • Bounded precision prevents number explosion                    ║"
  IO.println "║ • Consistent O(1) rounding instead of O(n) GCD for n-digit nums  ║"
  IO.println "║                                                                  ║"
  IO.println "║ Trade-off: Slightly looser bounds (but always sound!)            ║"
  IO.println "╚══════════════════════════════════════════════════════════════════╝"

end LeanBound.Benchmark.Timing

-- Entry point for standalone execution
def main : IO Unit := LeanBound.Benchmark.Timing.main
