/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import Lean
import LeanBound.Meta.ToExpr
import LeanBound.Meta.ProveSupported
import LeanBound.Core.Expr
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Automatic Continuity Proof Generation

This module provides metaprogramming infrastructure to automatically generate
`ContinuousOn` proof terms for reified LeanBound expressions.

Given a reified AST `e : LeanBound.Core.Expr`, we construct a proof that
`ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc lo hi)`.

## Main definitions

* `LeanBound.Meta.mkContinuousOnProof` - Generate `ContinuousOn` proofs for ExprSupportedCore expressions
* `exprSupportedCore_continuousOn` - Base theorem: all ExprSupportedCore expressions are continuous

## Design

The key insight is that all operations in `ExprSupportedCore` are continuous:
- Constants: `continuousOn_const`
- Variables (identity): `continuousOn_id`
- Add, Mul, Neg: preserved by composition
- Sin, Cos, Exp: continuous everywhere

**Note**: `log` and `inv` are NOT in `ExprSupportedCore`, so we don't need to handle
their continuity restrictions (they're only continuous on positive/nonzero domains).
-/

open Lean Meta Elab Term Command
open LeanBound.Core

-- Use explicit alias to avoid ambiguity with Lean.Expr
abbrev LExpr := LeanBound.Core.Expr

namespace LeanBound.Meta

/-! ## Base Continuity Theorem

This theorem proves that all `ExprSupportedCore` expressions evaluate to continuous functions.
We prove this by induction on the structure of `ExprSupportedCore`.
-/

/-- All ExprSupportedCore expressions are continuous on any set.

This is the foundational theorem that allows automatic continuity proof generation.
Since ExprSupportedCore only includes operations that are continuous everywhere
(const, var, add, mul, neg, sin, cos, exp), the result follows by structural induction. -/
theorem exprSupportedCore_continuousOn (e : LExpr) (hsupp : LeanBound.Numerics.ExprSupportedCore e)
    {s : Set ℝ} :
    ContinuousOn (fun x => LeanBound.Core.Expr.eval (fun _ => x) e) s := by
  induction hsupp with
  | const c =>
    simp only [LeanBound.Core.Expr.eval]
    exact continuousOn_const
  | var n =>
    -- eval (fun _ => x) (var n) = (fun _ => x) n = x
    simp only [LeanBound.Core.Expr.eval]
    exact continuous_id.continuousOn
  | add _ _ ih1 ih2 =>
    simp only [LeanBound.Core.Expr.eval]
    exact ih1.add ih2
  | mul _ _ ih1 ih2 =>
    simp only [LeanBound.Core.Expr.eval]
    exact ih1.mul ih2
  | neg _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact ih.neg
  | sin _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_sin.comp_continuousOn ih
  | cos _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_cos.comp_continuousOn ih
  | exp _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_exp.comp_continuousOn ih
  | sqrt _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    -- sqrt is continuous on [0, ∞) and returns 0 for negative inputs
    -- For ContinuousOn on any set, we use Real.continuous_sqrt
    exact Real.continuous_sqrt.comp_continuousOn ih
  | sinh _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_sinh.comp_continuousOn ih
  | cosh _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_cosh.comp_continuousOn ih
  | tanh _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    -- tanh = sinh / cosh, and cosh > 0 everywhere
    have hcont : Continuous Real.tanh := by
      have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
        ext x; exact Real.tanh_eq_sinh_div_cosh x
      rw [h]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))
    exact hcont.comp_continuousOn ih

/-- Specialized version for Icc intervals (common case for interval_roots) -/
theorem exprSupportedCore_continuousOn_Icc (e : LExpr) (hsupp : LeanBound.Numerics.ExprSupportedCore e)
    (lo hi : ℝ) :
    ContinuousOn (fun x => LeanBound.Core.Expr.eval (fun _ => x) e) (Set.Icc lo hi) :=
  exprSupportedCore_continuousOn e hsupp

/-- Version taking IntervalRat for convenience -/
theorem exprSupportedCore_continuousOn_interval (e : LExpr) (hsupp : LeanBound.Numerics.ExprSupportedCore e)
    (I : LeanBound.Core.IntervalRat) :
    ContinuousOn (fun x => LeanBound.Core.Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi) :=
  exprSupportedCore_continuousOn e hsupp

/-! ## Metaprogramming: Continuity Proof Generation

Generate proof terms of `ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc lo hi)`
by applying `exprSupportedCore_continuousOn_Icc` with an automatically generated
`ExprSupportedCore` proof.
-/

/-- Generate a ContinuousOn proof for an expression on an interval.

    Given:
    - `e_ast` : the AST expression (Lean.Expr representing LeanBound.Core.Expr)
    - `interval` : the interval expression (Lean.Expr representing IntervalRat)

    Returns a proof of:
    `ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)`

    This works by:
    1. Generating an ExprSupportedCore proof for the AST
    2. Applying exprSupportedCore_continuousOn_interval
-/
def mkContinuousOnProof (e_ast : Lean.Expr) (interval : Lean.Expr) : MetaM Lean.Expr := do
  -- Generate the ExprSupportedCore proof
  let supportProof ← mkSupportedCoreProof e_ast
  -- Apply the continuity theorem
  mkAppM ``exprSupportedCore_continuousOn_interval #[e_ast, supportProof, interval]

/-- Alternative: generate ContinuousOn proof with explicit lo/hi bounds -/
def mkContinuousOnProofIcc (e_ast : Lean.Expr) (lo hi : Lean.Expr) : MetaM Lean.Expr := do
  let supportProof ← mkSupportedCoreProof e_ast
  mkAppM ``exprSupportedCore_continuousOn_Icc #[e_ast, supportProof, lo, hi]

/-! ## Testing Infrastructure -/

/-- Debug command to test continuity proof generation -/
elab "#check_continuous " t:term " on " lo:term ", " hi:term : command => do
  let (ast, _contProof, contType) ← liftTermElabM do
    -- Elaborate the term
    let t ← elabTerm t none
    let t ← instantiateMVars t
    -- Reify to AST
    let ast ← reify t
    -- Elaborate bounds
    let loExpr ← elabTerm lo (some (mkConst ``Real))
    let hiExpr ← elabTerm hi (some (mkConst ``Real))
    -- Generate continuity proof
    let contProof ← mkContinuousOnProofIcc ast loExpr hiExpr
    let contType ← inferType contProof
    return (ast, contProof, contType)
  logInfo m!"AST: {ast}"
  logInfo m!"Continuity proof type: {contType}"

end LeanBound.Meta
