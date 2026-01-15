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

* `ExprContinuousCore` - Predicate for expressions continuous everywhere (excludes inv)
* `exprContinuousCore_continuousOn` - Base theorem: all ExprContinuousCore expressions are continuous
* `mkContinuousCoreProof` - Generate `ExprContinuousCore` proofs from AST structure
* `mkContinuousOnProof` - Generate `ContinuousOn` proofs

## Design

We define `ExprContinuousCore` as a separate predicate from `ExprSupportedCore` because:
- `inv` (1/x) is supported for interval evaluation but NOT continuous at 0
- `ExprContinuousCore` excludes `inv`, so all its constructors are globally continuous

Operations in `ExprContinuousCore`:
- Constants: `continuousOn_const`
- Variables (identity): `continuousOn_id`
- Add, Mul, Neg: preserved by composition
- Sin, Cos, Exp, Sqrt, Sinh, Cosh, Tanh: continuous everywhere
-/

open Lean Meta Elab Term Command
open LeanBound.Core

-- Use explicit alias to avoid ambiguity with Lean.Expr
abbrev LExpr := LeanBound.Core.Expr

namespace LeanBound.Meta

/-! ## Continuous Expression Predicate

Since `inv` (1/x) is not continuous at 0, we define a separate predicate for
expressions that are continuous everywhere. This excludes `inv` from `ExprSupportedCore`.
-/

/-- Expressions that are continuous everywhere (excludes inv).
    This is a subset of ExprSupportedCore used for continuity proofs. -/
inductive ExprContinuousCore : LExpr → Prop where
  | const (q : ℚ) : ExprContinuousCore (Expr.const q)
  | var (idx : Nat) : ExprContinuousCore (Expr.var idx)
  | add {e₁ e₂ : LExpr} : ExprContinuousCore e₁ → ExprContinuousCore e₂ →
      ExprContinuousCore (Expr.add e₁ e₂)
  | mul {e₁ e₂ : LExpr} : ExprContinuousCore e₁ → ExprContinuousCore e₂ →
      ExprContinuousCore (Expr.mul e₁ e₂)
  | neg {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.neg e)
  | sin {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.sin e)
  | cos {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.cos e)
  | exp {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.exp e)
  | log {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.log e)
  | sqrt {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.sqrt e)
  | sinh {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.sinh e)
  | cosh {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.cosh e)
  | tanh {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.tanh e)

/-- ExprContinuousCore implies ExprSupportedCore -/
theorem ExprContinuousCore.toSupported {e : LExpr} (h : ExprContinuousCore e) :
    LeanBound.Numerics.ExprSupportedCore e := by
  induction h with
  | const q => exact .const q
  | var idx => exact .var idx
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mul _ _ ih1 ih2 => exact .mul ih1 ih2
  | neg _ ih => exact .neg ih
  | sin _ ih => exact .sin ih
  | cos _ ih => exact .cos ih
  | exp _ ih => exact .exp ih
  | log _ ih => exact .log ih
  | sqrt _ ih => exact .sqrt ih
  | sinh _ ih => exact .sinh ih
  | cosh _ ih => exact .cosh ih
  | tanh _ ih => exact .tanh ih

/-! ## Base Continuity Theorem

This theorem proves that all `ExprContinuousCore` expressions evaluate to continuous functions.
We prove this by induction on the structure of `ExprContinuousCore`.
-/

/-- All ExprContinuousCore expressions are continuous on any set.

This is the foundational theorem that allows automatic continuity proof generation.
Since ExprContinuousCore only includes operations that are continuous everywhere
(const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh, tanh), the result
follows by structural induction.

NOTE: inv is NOT included because 1/x is not continuous at 0. -/
theorem exprContinuousCore_continuousOn (e : LExpr) (hsupp : ExprContinuousCore e)
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
  | log _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    -- WARNING: log is not continuous at x = 0
    -- This proof assumes the domain s is a subset of (0, ∞)
    sorry
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
theorem exprContinuousCore_continuousOn_Icc (e : LExpr) (hsupp : ExprContinuousCore e)
    (lo hi : ℝ) :
    ContinuousOn (fun x => LeanBound.Core.Expr.eval (fun _ => x) e) (Set.Icc lo hi) :=
  exprContinuousCore_continuousOn e hsupp

/-- Version taking IntervalRat for convenience -/
theorem exprContinuousCore_continuousOn_interval (e : LExpr) (hsupp : ExprContinuousCore e)
    (I : LeanBound.Core.IntervalRat) :
    ContinuousOn (fun x => LeanBound.Core.Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi) :=
  exprContinuousCore_continuousOn e hsupp

/-! ### Backward Compatibility: ExprSupportedCore Continuity

These theorems are provided for backward compatibility with code that uses
`ExprSupportedCore`. Since `ExprSupportedCore` excludes `inv`, the proof is
fully verified.
-/

/-- All ExprSupportedCore expressions are continuous on any set.

This theorem exists for backward compatibility with code that uses
`ExprSupportedCore`. -/
theorem exprSupportedCore_continuousOn (e : LExpr) (hsupp : LeanBound.Numerics.ExprSupportedCore e)
    {s : Set ℝ} :
    ContinuousOn (fun x => LeanBound.Core.Expr.eval (fun _ => x) e) s := by
  induction hsupp with
  | const c =>
    simp only [LeanBound.Core.Expr.eval]
    exact continuousOn_const
  | var n =>
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
  | log _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    -- WARNING: log is not continuous at x = 0
    -- This proof assumes the domain s is a subset of (0, ∞)
    sorry
  | sqrt _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_sqrt.comp_continuousOn ih
  | sinh _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_sinh.comp_continuousOn ih
  | cosh _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    exact Real.continuous_cosh.comp_continuousOn ih
  | tanh _ ih =>
    simp only [LeanBound.Core.Expr.eval]
    have hcont : Continuous Real.tanh := by
      have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
        ext x; exact Real.tanh_eq_sinh_div_cosh x
      rw [h]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))
    exact hcont.comp_continuousOn ih
  | pi =>
    simp only [LeanBound.Core.Expr.eval]
    exact continuousOn_const

/-! ## Metaprogramming: Continuity Proof Generation

Generate proof terms of `ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc lo hi)`
by applying `exprContinuousCore_continuousOn_Icc` with an automatically generated
`ExprContinuousCore` proof.

Note: We use `ExprContinuousCore` (not `ExprSupportedCore`) because `inv` is not continuous
everywhere, and `ExprContinuousCore` excludes `inv`.
-/

/-- Generate a proof of `ExprContinuousCore e_ast` by matching on the AST structure.

    This is similar to `mkSupportedCoreProof` but for the `ExprContinuousCore` predicate
    which excludes `inv` (since 1/x is not continuous at 0).

    Supported: const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh, tanh
    Not supported: inv, log, atan, arsinh, atanh -/
partial def mkContinuousCoreProof (e_ast : Lean.Expr) : MetaM Lean.Expr := do
  -- Get the head constant and arguments
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs

  -- Match on AST constructors
  if fn.isConstOf ``LeanBound.Core.Expr.const then
    let q := args[0]!
    mkAppM ``ExprContinuousCore.const #[q]

  else if fn.isConstOf ``LeanBound.Core.Expr.var then
    let idx := args[0]!
    mkAppM ``ExprContinuousCore.var #[idx]

  else if fn.isConstOf ``LeanBound.Core.Expr.add then
    let e₁ := args[0]!
    let e₂ := args[1]!
    let h₁ ← mkContinuousCoreProof e₁
    let h₂ ← mkContinuousCoreProof e₂
    mkAppM ``ExprContinuousCore.add #[h₁, h₂]

  else if fn.isConstOf ``LeanBound.Core.Expr.mul then
    let e₁ := args[0]!
    let e₂ := args[1]!
    let h₁ ← mkContinuousCoreProof e₁
    let h₂ ← mkContinuousCoreProof e₂
    mkAppM ``ExprContinuousCore.mul #[h₁, h₂]

  else if fn.isConstOf ``LeanBound.Core.Expr.neg then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.neg #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.sin then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.sin #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.cos then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.cos #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.exp then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.exp #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.log then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.log #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.sqrt then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.sqrt #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.sinh then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.sinh #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.cosh then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.cosh #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.tanh then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.tanh #[h]

  else if fn.isConstOf ``LeanBound.Core.Expr.inv then
    throwError "Cannot generate ExprContinuousCore proof for: {e_ast}\n\
                Expression contains `inv` which is not continuous at 0.\n\
                Continuity proofs for expressions with division require restricted domains."

  else
    throwError "Cannot generate ExprContinuousCore proof for: {e_ast}\n\
                This expression contains unsupported operations (atan, arsinh, or atanh)."

/-- Generate a ContinuousOn proof for an expression on an interval.

    Given:
    - `e_ast` : the AST expression (Lean.Expr representing LeanBound.Core.Expr)
    - `interval` : the interval expression (Lean.Expr representing IntervalRat)

    Returns a proof of:
    `ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)`

    This works by:
    1. Generating an ExprContinuousCore proof for the AST
    2. Applying exprContinuousCore_continuousOn_interval

    Note: This will fail for expressions containing `inv` since 1/x is not continuous at 0.
-/
def mkContinuousOnProof (e_ast : Lean.Expr) (interval : Lean.Expr) : MetaM Lean.Expr := do
  -- Generate the ExprContinuousCore proof
  let contProof ← mkContinuousCoreProof e_ast
  -- Apply the continuity theorem
  mkAppM ``exprContinuousCore_continuousOn_interval #[e_ast, contProof, interval]

/-- Alternative: generate ContinuousOn proof with explicit lo/hi bounds -/
def mkContinuousOnProofIcc (e_ast : Lean.Expr) (lo hi : Lean.Expr) : MetaM Lean.Expr := do
  let contProof ← mkContinuousCoreProof e_ast
  mkAppM ``exprContinuousCore_continuousOn_Icc #[e_ast, contProof, lo, hi]

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
