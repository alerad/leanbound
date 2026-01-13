/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Expr

/-!
# Fast Float Evaluator

This file provides a fast, unverified floating-point evaluator for expressions.
It is used only for heuristics to guide the verified search (e.g., finding good
initial upper bounds for branch-and-bound optimization).

## Main definitions

* `evalFloat` - Evaluate an expression using hardware floats
* `FloatEnv` - Environment mapping variable indices to Float values

## Design notes

This evaluator uses Lean's native `Float` type, which maps to hardware IEEE 754
double precision. The results are NOT verified and should only be used as hints
for the rigorous interval arithmetic algorithms.

Functions not directly available in Lean's Float stdlib are approximated:
- `tanh(x)` via `(exp(2x) - 1) / (exp(2x) + 1)`
- `sinh(x)` via `(exp(x) - exp(-x)) / 2`
- `cosh(x)` via `(exp(x) + exp(-x)) / 2`
- `arsinh(x)` via `log(x + sqrt(x² + 1))`
- `atanh(x)` via `log((1+x)/(1-x)) / 2`
- `sinc(x)` via `sin(x)/x` with special case at 0
- `erf(x)` via polynomial approximation
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-- Evaluation environment for Floats -/
abbrev FloatEnv := Nat → Float

/-- Polynomial approximation of erf(x) for |x| ≤ 1.
    Uses Horner's method for the approximation:
    erf(x) ≈ 2x/√π * (1 - x²/3 + x⁴/10 - x⁶/42 + ...)
    For |x| > 1, uses tanh-based approximation which saturates to ±1. -/
private def floatErf (x : Float) : Float :=
  if x.abs ≤ 1.0 then
    -- Taylor series approximation for small x
    let x2 := x * x
    let coeff := 1.0 - x2 * (1.0/3.0 - x2 * (1.0/10.0 - x2 * (1.0/42.0 - x2 * (1.0/216.0))))
    x * coeff * 1.1283791670955126  -- 2/√π
  else
    -- For larger x, use tanh approximation: erf(x) ≈ tanh(1.2x)
    let y := 1.2 * x
    let e2y := Float.exp (2.0 * y)
    (e2y - 1.0) / (e2y + 1.0)

/-- Convert an integer to a Float -/
private def intToFloat (z : ℤ) : Float :=
  if z ≥ 0 then z.toNat.toFloat
  else -((-z).toNat.toFloat)

/-- Convert a rational to a Float (approximate) -/
private def ratToFloat (q : ℚ) : Float :=
  intToFloat q.num / q.den.toFloat

/--
Fast, unverified floating point evaluator.
Used only for heuristics to guide the verified search.
-/
def evalFloat (e : Expr) (ρ : FloatEnv) : Float :=
  match e with
  | Expr.const q => ratToFloat q
  | Expr.var i => ρ i
  | Expr.add a b => evalFloat a ρ + evalFloat b ρ
  | Expr.mul a b => evalFloat a ρ * evalFloat b ρ
  | Expr.neg a => -(evalFloat a ρ)
  | Expr.inv a => 1.0 / (evalFloat a ρ)
  | Expr.exp a => Float.exp (evalFloat a ρ)
  | Expr.log a => Float.log (evalFloat a ρ)
  | Expr.sin a => Float.sin (evalFloat a ρ)
  | Expr.cos a => Float.cos (evalFloat a ρ)
  | Expr.sqrt a => Float.sqrt (evalFloat a ρ)
  | Expr.atan a => Float.atan (evalFloat a ρ)
  | Expr.sinh a =>
      let x := evalFloat a ρ
      (Float.exp x - Float.exp (-x)) / 2.0
  | Expr.cosh a =>
      let x := evalFloat a ρ
      (Float.exp x + Float.exp (-x)) / 2.0
  | Expr.tanh a =>
      let x := evalFloat a ρ
      let e2x := Float.exp (2.0 * x)
      (e2x - 1.0) / (e2x + 1.0)
  | Expr.arsinh a =>
      let x := evalFloat a ρ
      Float.log (x + Float.sqrt (x * x + 1.0))
  | Expr.atanh a =>
      let x := evalFloat a ρ
      Float.log ((1.0 + x) / (1.0 - x)) / 2.0
  | Expr.sinc a =>
      let x := evalFloat a ρ
      if x.abs < 1e-10 then 1.0
      else Float.sin x / x
  | Expr.erf a => floatErf (evalFloat a ρ)

/-- Evaluate with a list-based environment (for compatibility with Box) -/
def evalFloatList (e : Expr) (vars : List Float) : Float :=
  evalFloat e (fun i => vars.getD i 0.0)

/-- Evaluate with an array-based environment (faster for repeated access) -/
def evalFloatArray (e : Expr) (vars : Array Float) : Float :=
  evalFloat e (fun i => vars.getD i 0.0)

end LeanBound.Numerics
