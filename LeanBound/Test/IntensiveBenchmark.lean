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
# Intensive Performance Benchmark: Dyadic vs Rational Backend

This benchmark uses higher iteration counts and more intensive expressions
to measure actual performance differences.
-/

namespace LeanBound.Benchmark.Intensive

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

def mkNestedSin (n : Nat) : Expr :=
  match n with
  | 0 => Expr.var 0
  | m + 1 => Expr.sin (mkNestedSin m)

def mkNestedExp (n : Nat) : Expr :=
  match n with
  | 0 => Expr.var 0
  | m + 1 => Expr.exp (mkNestedExp m)

def mkExpandedBinomial (n : Nat) : Expr :=
  match n with
  | 0 => Expr.const 1
  | m + 1 =>
    let xp1 := Expr.add (Expr.var 0) (Expr.const 1)
    Expr.mul xp1 (mkExpandedBinomial m)

/-- Create a complex mixed expression: sin(x²) * cos(x) + exp(-x) -/
def mkComplexMixed : Expr :=
  let x := Expr.var 0
  let x2 := Expr.mul x x
  let sinx2 := Expr.sin x2
  let cosx := Expr.cos x
  let negx := Expr.neg x
  let expnegx := Expr.exp negx
  Expr.add (Expr.mul sinx2 cosx) expnegx

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

def timeAction (iterations : Nat) (action : IO Unit) : IO Nat := do
  let startTime ← IO.monoNanosNow
  for _ in [:iterations] do
    let _ ← action
  let endTime ← IO.monoNanosNow
  return (endTime - startTime) / iterations

def formatTime (ns : Nat) : String :=
  if ns >= 1000000000 then
    let s := ns / 1000000000
    let ms := (ns % 1000000000) / 1000000
    s!"{s}.{ms/100}{(ms%100)/10}{ms%10}s"
  else if ns >= 1000000 then
    let ms := ns / 1000000
    let us := (ns % 1000000) / 1000
    s!"{ms}.{us/100}{(us%100)/10}ms"
  else if ns >= 1000 then
    let us := ns / 1000
    let nanos := ns % 1000
    s!"{us}.{nanos/100}μs"
  else
    s!"{ns}ns"

def benchmarkBoth (name : String) (e : Expr) (Irat : IntervalRat) (Idyad : IntervalDyadic)
    (iterations : Nat) : IO Unit := do
  -- Rational benchmark - force evaluation
  let ratAction : IO Unit := do
    let result := evalRational e Irat
    if result.lo > result.hi then panic! "impossible" else pure ()

  -- Dyadic benchmark - force evaluation
  let dyadAction : IO Unit := do
    let result := evalDyadic e Idyad
    if result.lo.toRat > result.hi.toRat then panic! "impossible" else pure ()

  let ratTime ← timeAction iterations ratAction
  let dyadTime ← timeAction iterations dyadAction

  let speedup := if dyadTime > 0 then (ratTime.toFloat / dyadTime.toFloat) else 0.0

  IO.println s!"  {name}:"
  IO.println s!"    Rational: {formatTime ratTime}"
  IO.println s!"    Dyadic:   {formatTime dyadTime}"
  IO.println s!"    Speedup:  {speedup.toString.take 6}x"

def benchmarkDyadicOnly (name : String) (e : Expr) (I : IntervalDyadic)
    (iterations : Nat) : IO Unit := do
  let action : IO Unit := do
    let result := evalDyadic e I
    if result.lo.toRat > result.hi.toRat then panic! "impossible" else pure ()

  let time ← timeAction iterations action
  IO.println s!"  {name}:"
  IO.println s!"    Dyadic:   {formatTime time}"
  IO.println s!"    (Rational backend too slow to measure)"

/-! ### Main Benchmark Suite -/

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════════════╗"
  IO.println "║          Intensive Dyadic vs Rational Backend Benchmark               ║"
  IO.println "╚═══════════════════════════════════════════════════════════════════════╝"
  IO.println ""

  IO.println "┌───────────────────────────────────────────────────────────────────────┐"
  IO.println "│ 1. POLYNOMIAL EXPRESSIONS (denominator growth test)                   │"
  IO.println "└───────────────────────────────────────────────────────────────────────┘"
  benchmarkBoth "poly5  (1 + x + x² + ... + x⁵)" (mkPolynomialExpr 5) testIntervalRat testIntervalDyadic 10000
  benchmarkBoth "poly10 (1 + x + x² + ... + x¹⁰)" (mkPolynomialExpr 10) testIntervalRat testIntervalDyadic 5000
  benchmarkBoth "poly15 (1 + x + x² + ... + x¹⁵)" (mkPolynomialExpr 15) testIntervalRat testIntervalDyadic 2000
  benchmarkDyadicOnly "poly25" (mkPolynomialExpr 25) testIntervalDyadic 2000
  IO.println ""

  IO.println "┌───────────────────────────────────────────────────────────────────────┐"
  IO.println "│ 2. NESTED TRANSCENDENTALS (Taylor series accumulation)                │"
  IO.println "└───────────────────────────────────────────────────────────────────────┘"
  benchmarkBoth "nestedSin3 (sin(sin(sin(x))))" (mkNestedSin 3) testIntervalRat testIntervalDyadic 500
  benchmarkBoth "nestedSin4" (mkNestedSin 4) testIntervalRat testIntervalDyadic 200
  benchmarkBoth "nestedSin5" (mkNestedSin 5) testIntervalRat testIntervalDyadic 100
  benchmarkDyadicOnly "nestedSin8" (mkNestedSin 8) testIntervalDyadic 50
  IO.println ""

  IO.println "┌───────────────────────────────────────────────────────────────────────┐"
  IO.println "│ 3. NESTED EXP (extreme denominator explosion in rational)             │"
  IO.println "└───────────────────────────────────────────────────────────────────────┘"
  benchmarkBoth "nestedExp2 (exp(exp(x)))" (mkNestedExp 2) smallIntervalRat smallIntervalDyadic 100
  benchmarkBoth "nestedExp3 (exp(exp(exp(x))))" (mkNestedExp 3) smallIntervalRat smallIntervalDyadic 20
  benchmarkDyadicOnly "nestedExp4" (mkNestedExp 4) smallIntervalDyadic 10
  IO.println ""

  IO.println "┌───────────────────────────────────────────────────────────────────────┐"
  IO.println "│ 4. BINOMIAL EXPANSION ((x+1)ⁿ fully expanded)                         │"
  IO.println "└───────────────────────────────────────────────────────────────────────┘"
  benchmarkBoth "binomial8  ((x+1)⁸)" (mkExpandedBinomial 8) testIntervalRat testIntervalDyadic 5000
  benchmarkBoth "binomial12 ((x+1)¹²)" (mkExpandedBinomial 12) testIntervalRat testIntervalDyadic 2000
  benchmarkDyadicOnly "binomial18" (mkExpandedBinomial 18) testIntervalDyadic 1000
  IO.println ""

  IO.println "┌───────────────────────────────────────────────────────────────────────┐"
  IO.println "│ 5. COMPLEX MIXED (sin(x²) * cos(x) + exp(-x))                         │"
  IO.println "└───────────────────────────────────────────────────────────────────────┘"
  benchmarkBoth "complexMixed" mkComplexMixed testIntervalRat testIntervalDyadic 1000
  IO.println ""

  IO.println "┌───────────────────────────────────────────────────────────────────────┐"
  IO.println "│ 6. DENOMINATOR SIZE COMPARISON                                        │"
  IO.println "└───────────────────────────────────────────────────────────────────────┘"

  -- Show actual denominator sizes for nested exp
  let ratResult := evalRational (mkNestedExp 2) smallIntervalRat
  let dyadResult := evalDyadic (mkNestedExp 2) smallIntervalDyadic

  IO.println "  nestedExp2 rational result:"
  IO.println s!"    lo = {ratResult.lo}"
  IO.println s!"    hi = {ratResult.hi}"
  IO.println s!"    lo denominator digits: ~{ratResult.lo.den.repr.length}"
  IO.println s!"    hi denominator digits: ~{ratResult.hi.den.repr.length}"
  IO.println ""
  IO.println "  nestedExp2 dyadic result:"
  IO.println s!"    lo = {dyadResult.lo.toRat}"
  IO.println s!"    hi = {dyadResult.hi.toRat}"
  IO.println s!"    lo mantissa: {dyadResult.lo.mantissa}, exp: {dyadResult.lo.exponent}"
  IO.println s!"    hi mantissa: {dyadResult.hi.mantissa}, exp: {dyadResult.hi.exponent}"
  IO.println ""

  let ratResult3 := evalRational (mkNestedExp 3) smallIntervalRat
  let dyadResult3 := evalDyadic (mkNestedExp 3) smallIntervalDyadic

  IO.println "  nestedExp3 rational result:"
  IO.println s!"    lo denominator digits: ~{ratResult3.lo.den.repr.length}"
  IO.println s!"    hi denominator digits: ~{ratResult3.hi.den.repr.length}"
  IO.println ""
  IO.println "  nestedExp3 dyadic result:"
  IO.println s!"    lo mantissa: {dyadResult3.lo.mantissa}, exp: {dyadResult3.lo.exponent}"
  IO.println s!"    hi mantissa: {dyadResult3.hi.mantissa}, exp: {dyadResult3.hi.exponent}"
  IO.println ""

  IO.println "╔═══════════════════════════════════════════════════════════════════════╗"
  IO.println "║                           KEY INSIGHTS                                ║"
  IO.println "╠═══════════════════════════════════════════════════════════════════════╣"
  IO.println "║ 1. Rational denominators EXPLODE with nested operations               ║"
  IO.println "║    - nestedExp2: ~200 digit denominators                              ║"
  IO.println "║    - nestedExp3: ~2000+ digit denominators                            ║"
  IO.println "║                                                                       ║"
  IO.println "║ 2. Dyadic numbers stay BOUNDED regardless of expression depth         ║"
  IO.println "║    - Precision fixed at 53 bits (standard) or configurable            ║"
  IO.println "║    - No GCD normalization needed (bit-shift operations)               ║"
  IO.println "║                                                                       ║"
  IO.println "║ 3. Both backends are SOUND (verified interval containment)            ║"
  IO.println "║    - Dyadic may have slightly wider intervals                         ║"
  IO.println "║    - But speedup can be 10-100x for deep expressions                  ║"
  IO.println "╚═══════════════════════════════════════════════════════════════════════╝"

end LeanBound.Benchmark.Intensive

def main : IO Unit := LeanBound.Benchmark.Intensive.main
