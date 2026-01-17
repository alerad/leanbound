/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalDyadic

/-!
# Interval Vector Arithmetic

This file provides vector and matrix operations for Dyadic intervals,
enabling verified linear algebra computations.

## Main definitions

* `IntervalVector` - A list of Dyadic intervals representing bounded vectors
* `scalarMulInterval` - Multiply an interval by a rational scalar
* `dotProduct` - Dot product of rational weights with interval vector
* `matVecMul` - Matrix-vector multiplication
* `addBias` - Add a rational bias vector
* `add` - Pointwise addition of interval vectors

## Main theorems

* `mem_scalarMulInterval` - Soundness of scalar multiplication
* `mem_dotProduct` - Soundness of dot product (FTIA for linear combinations)
* `mem_matVecMul` - Soundness of matrix-vector multiplication
* `mem_addBias` - Soundness of bias addition
* `mem_add_component` - Soundness of vector addition
-/

namespace LeanCert.Engine

open LeanCert.Core
-- open Core
-- open Core.Dyadic

/-- A vector of intervals representing bounded real vectors -/
abbrev IntervalVector := List IntervalDyadic

namespace IntervalVector

/-! ### Scalar Operations -/

/-- Multiply an interval by a rational scalar.
    Uses the existing interval multiplication by converting the scalar to a singleton. -/
def scalarMulInterval (w : ℚ) (I : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  let wInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton w) prec
  IntervalDyadic.mul wInterval I

/-- Soundness of scalar-interval multiplication -/
theorem mem_scalarMulInterval {w : ℚ} {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ I) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    (w : ℝ) * x ∈ scalarMulInterval w I prec := by
  unfold scalarMulInterval
  apply IntervalDyadic.mem_mul
  · exact IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton w) prec hprec
  · exact hx

/-! ### Dot Product -/

/-- Dot product of rational weights with an interval vector.
    Returns an interval containing all possible dot products. -/
def dotProduct (weights : List ℚ) (inputs : IntervalVector) (prec : Int := -53) : IntervalDyadic :=
  match weights, inputs with
  | [], [] => IntervalDyadic.singleton (Core.Dyadic.ofInt 0)
  | w :: ws, I :: Is =>
      IntervalDyadic.add (scalarMulInterval w I prec) (dotProduct ws Is prec)
  | _, _ => IntervalDyadic.singleton (Core.Dyadic.ofInt 0)  -- dimension mismatch fallback

/-- Helper: real dot product of two lists -/
def realDotProduct (weights : List ℚ) (values : List ℝ) : ℝ :=
  match weights, values with
  | [], [] => 0
  | w :: ws, x :: xs => (w : ℝ) * x + realDotProduct ws xs
  | _, _ => 0

/-- Zero is in the zero singleton -/
theorem mem_zero_singleton : (0 : ℝ) ∈ IntervalDyadic.singleton (Core.Dyadic.ofInt 0) := by
  have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt 0)
  simp only [Core.Dyadic.toRat_ofInt, Int.cast_zero, Rat.cast_zero] at h
  exact h

/-- Soundness of dot product for matching-length lists -/
theorem mem_dotProduct_aux (weights : List ℚ) (xs : List ℝ) (Is : IntervalVector)
    (hlen : weights.length = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0) :
    realDotProduct weights xs ∈ dotProduct weights Is prec := by
  induction weights generalizing xs Is with
  | nil =>
    match xs, Is with
    | [], [] =>
      simp only [realDotProduct, dotProduct]
      exact mem_zero_singleton
    | _ :: _, [] => simp at hxlen
    | [], _ :: _ => simp at hlen
    | _ :: _, _ :: _ => simp at hlen
  | cons w ws ih =>
    match xs, Is with
    | [], [] => simp at hlen
    | [], _ :: _ => simp at hxlen
    | _ :: _, [] => simp at hlen
    | x :: xs', I :: Is' =>
      simp only [realDotProduct, dotProduct]
      apply IntervalDyadic.mem_add
      · apply mem_scalarMulInterval _ _ hprec
        exact hmem 0 (by simp)
      · have hlen' : ws.length = Is'.length := by simp at hlen; exact hlen
        have hxlen' : xs'.length = Is'.length := by simp at hxlen; exact hxlen
        have hmem' : ∀ i, (hi : i < Is'.length) → xs'[i] ∈ Is'[i] := by
          intro i hi
          have h := hmem (i + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at h
          exact h
        exact ih xs' Is' hlen' hxlen' hmem'

/-- Soundness of dot product: if each x_i ∈ I_i, then ∑ w_i * x_i ∈ dotProduct -/
theorem mem_dotProduct {weights : List ℚ} {xs : List ℝ} {Is : IntervalVector}
    (hlen : weights.length = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    realDotProduct weights xs ∈ dotProduct weights Is prec :=
  mem_dotProduct_aux weights xs Is hlen hxlen hmem prec hprec

/-! ### Vector Addition -/

/-- Pointwise addition of two interval vectors -/
def add (Is Js : IntervalVector) : IntervalVector :=
  List.zipWith IntervalDyadic.add Is Js

/-- Soundness of vector addition (component-wise) -/
theorem mem_add_component {x y : ℝ} {I J : IntervalDyadic}
    (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ IntervalDyadic.add I J :=
  IntervalDyadic.mem_add hx hy

/-- Zero interval (singleton at 0) -/
def zero : IntervalDyadic := IntervalDyadic.singleton (Core.Dyadic.ofInt 0)

/-- Membership in zero interval -/
theorem mem_zero : (0 : ℝ) ∈ zero := mem_zero_singleton

/-! ### Matrix-Vector Operations -/

/-- Matrix-vector multiplication: W · x where W is a matrix of rational weights
    and x is an interval vector. Each row of W is dotted with x. -/
def matVecMul (W : List (List ℚ)) (x : IntervalVector) (prec : Int := -53) : IntervalVector :=
  W.map (fun row => dotProduct row x prec)

/-- Real matrix-vector multiplication -/
def realMatVecMul (W : List (List ℚ)) (x : List ℝ) : List ℝ :=
  W.map (fun row => realDotProduct row x)

/-- Soundness of matrix-vector multiplication -/
theorem mem_matVecMul {W : List (List ℚ)} {xs : List ℝ} {Is : IntervalVector}
    (hWcols : ∀ row ∈ W, row.length = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    ∀ i, (hi : i < W.length) →
      (realMatVecMul W xs)[i]'(by simp [realMatVecMul]; exact hi) ∈
      (matVecMul W Is prec)[i]'(by simp [matVecMul]; exact hi) := by
  intro i hi
  simp only [realMatVecMul, matVecMul, List.getElem_map]
  exact mem_dotProduct (hWcols (W[i]) (List.getElem_mem hi)) hxlen hmem prec hprec

/-- Add a rational bias vector to an interval vector -/
def addBias (Is : IntervalVector) (bias : List ℚ) (prec : Int := -53) : IntervalVector :=
  List.zipWith (fun I b =>
    IntervalDyadic.add I (IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec)
  ) Is bias

/-- Real vector plus bias -/
def realAddBias (xs : List ℝ) (bias : List ℚ) : List ℝ :=
  List.zipWith (fun x (b : ℚ) => x + (b : ℝ)) xs bias

/-- Soundness of bias addition -/
theorem mem_addBias {xs : List ℝ} {Is : IntervalVector} {bias : List ℚ}
    (hlen : xs.length = Is.length)
    (hblen : bias.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    ∀ i, (hi : i < Is.length) →
      (realAddBias xs bias)[i]'(by simp [realAddBias, List.length_zipWith]; omega) ∈
      (addBias Is bias prec)[i]'(by simp [addBias, List.length_zipWith]; omega) := by
  intro i hi
  have hib : i < bias.length := by omega
  have hxi : i < xs.length := by omega
  simp only [realAddBias, addBias, List.getElem_zipWith]
  apply IntervalDyadic.mem_add
  · exact hmem i hi
  · exact IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton (bias[i])) prec hprec

end IntervalVector

end LeanCert.Engine
