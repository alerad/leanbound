/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr

/-!
# Expression Support Predicates

This file defines predicates indicating which expressions are supported by
different interval evaluation strategies.

## Main definitions

* `ExprSupportedCore` - Predicate for expressions in the computable subset
  (const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh, cosh, tanh, erf, pi)

* `ExprSupported` - Predicate for the noncomputable AD subset
  (const, var, add, mul, neg, sin, cos, exp)

* `ExprSupportedWithInv` - Syntactic support predicate for expressions with inv and log

## Design notes

The predicates are ordered by generality:
- `ExprSupported` ⊆ `ExprSupportedCore` (via `ExprSupported.toCore`)
- `ExprSupported` ⊆ `ExprSupportedWithInv` (via `ExprSupported.toWithInv`)

The core subset is kept computable so that tactics can use `native_decide`
for interval bound checking. The extended subset uses `Real.exp` with
floor/ceil bounds, which requires noncomputability.
-/

namespace LeanCert.Core

open LeanCert.Core

/-! ### Core supported expression subset (computable) -/

/-- Predicate indicating an expression is in the computable core subset.
    Supports: const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh, cosh, tanh, erf, pi

    Note: log requires positive domain for correctness. The correctness theorem
    `evalIntervalCore_correct` has an additional hypothesis `evalDomainValid`
    that ensures log arguments evaluate to positive intervals. -/
inductive ExprSupportedCore : Expr → Prop where
  | const (q : ℚ) : ExprSupportedCore (Expr.const q)
  | var (idx : Nat) : ExprSupportedCore (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.neg e)
  | sin {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sin e)
  | cos {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cos e)
  | exp {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.exp e)
  | log {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.log e)
  | sqrt {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sqrt e)
  | sinh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sinh e)
  | cosh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cosh e)
  | tanh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.tanh e)
  | erf {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.erf e)
  | pi : ExprSupportedCore Expr.pi

/-! ### Extended supported expression subset (with exp) -/

/-- Predicate indicating an expression is in the fully-verified subset for AD.
    Supports: const, var, add, mul, neg, sin, cos, exp
    Does NOT support:
    - sqrt (not differentiable at 0 - use ExprSupportedCore for interval evaluation only)
    - inv (requires nonzero interval checks)
    - log (requires positive interval checks)
    - atan/arsinh/atanh (derivative proofs incomplete - use ExprSupportedWithInv + evalInterval?) -/
inductive ExprSupported : Expr → Prop where
  | const (q : ℚ) : ExprSupported (Expr.const q)
  | var (idx : Nat) : ExprSupported (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupported e₁ → ExprSupported e₂ → ExprSupported (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupported e₁ → ExprSupported e₂ → ExprSupported (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupported e → ExprSupported (Expr.neg e)
  | sin {e : Expr} : ExprSupported e → ExprSupported (Expr.sin e)
  | cos {e : Expr} : ExprSupported e → ExprSupported (Expr.cos e)
  | exp {e : Expr} : ExprSupported e → ExprSupported (Expr.exp e)

/-- ExprSupported expressions are also in ExprSupportedCore -/
theorem ExprSupported.toCore {e : Expr} (h : ExprSupported e) : ExprSupportedCore e := by
  induction h with
  | const q => exact ExprSupportedCore.const q
  | var idx => exact ExprSupportedCore.var idx
  | add _ _ ih₁ ih₂ => exact ExprSupportedCore.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact ExprSupportedCore.mul ih₁ ih₂
  | neg _ ih => exact ExprSupportedCore.neg ih
  | sin _ ih => exact ExprSupportedCore.sin ih
  | cos _ ih => exact ExprSupportedCore.cos ih
  | exp _ ih => exact ExprSupportedCore.exp ih

/-! ### Syntactic support predicate with inv and log -/

/-- Syntactic support predicate for expressions with inv and log (no semantic conditions).
    This is the most general support predicate, allowing all expression constructors.
    Semantic correctness is handled by evalInterval? returning None when conditions fail. -/
inductive ExprSupportedWithInv : Expr → Prop where
  | const (q : ℚ) : ExprSupportedWithInv (Expr.const q)
  | var (idx : Nat) : ExprSupportedWithInv (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupportedWithInv e₁ → ExprSupportedWithInv e₂ →
      ExprSupportedWithInv (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupportedWithInv e₁ → ExprSupportedWithInv e₂ →
      ExprSupportedWithInv (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.neg e)
  | inv {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.inv e)
  | exp {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.exp e)
  | sin {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.sin e)
  | cos {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.cos e)
  | log {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.log e)
  | atan {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.atan e)
  | arsinh {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.arsinh e)
  | atanh {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.atanh e)
  | sinc {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.sinc e)
  | erf {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.erf e)
  | sqrt {e : Expr} : ExprSupportedWithInv e → ExprSupportedWithInv (Expr.sqrt e)
  | pi : ExprSupportedWithInv Expr.pi

/-- ExprSupported implies ExprSupportedWithInv -/
theorem ExprSupported.toWithInv {e : Expr} (h : ExprSupported e) : ExprSupportedWithInv e := by
  induction h with
  | const q => exact ExprSupportedWithInv.const q
  | var idx => exact ExprSupportedWithInv.var idx
  | add _ _ ih₁ ih₂ => exact ExprSupportedWithInv.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact ExprSupportedWithInv.mul ih₁ ih₂
  | neg _ ih => exact ExprSupportedWithInv.neg ih
  | sin _ ih => exact ExprSupportedWithInv.sin ih
  | cos _ ih => exact ExprSupportedWithInv.cos ih
  | exp _ ih => exact ExprSupportedWithInv.exp ih

end LeanCert.Core
