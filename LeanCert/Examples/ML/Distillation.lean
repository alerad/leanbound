/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Distillation

/-!
# Model Distillation Verification Example

This file demonstrates **verified model distillation** using LeanCert's
interval arithmetic infrastructure.

## The Scenario

In AI deployment, we often need to:
1. Train a large "Teacher" model for accuracy
2. Compress it into a smaller "Student" model for efficiency
3. **Verify** that the Student behaves similarly to the Teacher

LeanCert can formally prove that |Teacher(x) - Student(x)| ≤ ε for ALL inputs
in a domain - not just sampled points, but a mathematical guarantee.

## Example Networks

We define two simple 2→2→1 networks and verify their outputs differ by at most
ε = 3 on the input domain [0, 1]².

## Main Results

* `distillationCheck_passes` - The computable check returns true
* `distillation_certificate` - Formal proof of bounded difference
-/

namespace LeanCert.Examples.ML.Distillation

open LeanCert.Core
open LeanCert.ML
open LeanCert.ML.Distillation
open LeanCert.Engine.IntervalVector

/-! ### Network Definitions -/

/-- Layer 1: 2 inputs → 2 outputs -/
def layer1 : Layer where
  weights := [[1, 1], [1, 0]]
  bias := [0, 0]

/-- Layer 2: 2 inputs → 1 output -/
def layer2 : Layer where
  weights := [[1, 1]]
  bias := [0]

/-- The Teacher network -/
def teacherNet : SequentialNet where
  layers := [layer1, layer2]

/-- The Student network -/
def studentNet : SequentialNet where
  layers := [layer1, layer2]

/-! ### Well-formedness Proofs -/

theorem layer1_wf : layer1.WellFormed := by
  constructor
  · intro row hrow; simp only [layer1, Layer.inputDim] at hrow ⊢; fin_cases hrow <;> rfl
  · rfl

theorem layer2_wf : layer2.WellFormed := by
  constructor
  · intro row hrow; simp only [layer2, Layer.inputDim] at hrow ⊢; fin_cases hrow; rfl
  · rfl

theorem teacherNet_wf : teacherNet.WellFormed 2 := by
  simp only [SequentialNet.WellFormed, teacherNet, SequentialNet.LayersWellFormed]
  exact ⟨layer1_wf, rfl, layer2_wf, rfl, trivial⟩

theorem studentNet_wf : studentNet.WellFormed 2 := by
  simp only [SequentialNet.WellFormed, studentNet, SequentialNet.LayersWellFormed]
  exact ⟨layer1_wf, rfl, layer2_wf, rfl, trivial⟩

/-! ### Input Domain -/

/-- Create an interval from rational bounds -/
def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := -53) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec

/-- Input domain: [0, 1]² -/
def inputDomain : IntervalVector :=
  [mkInterval 0 1, mkInterval 0 1]

/-! ### Equivalence Check -/

/-- Tolerance for distillation verification -/
def epsilon : ℚ := 3

/-- The computable certificate -/
def distillationCheck : Bool :=
  checkEquivalence teacherNet studentNet inputDomain epsilon (-53)

/-- The check passes! This is verified by computation. -/
theorem distillationCheck_passes : distillationCheck = true := by native_decide

/-! ### Helper Lemmas -/

/-- Membership in mkInterval -/
theorem mem_mkInterval {x : ℝ} {lo hi : ℚ} (hle : lo ≤ hi)
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x ∈ mkInterval lo hi hle prec := by
  unfold mkInterval
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  simp only [IntervalRat.mem_def]
  exact hx

/-! ### The Distillation Certificate -/

/-- For ANY inputs (x, y) in [0, 1]², Teacher and Student outputs differ by at most ε = 3. -/
theorem distillation_certificate (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    (SequentialNet.forwardInterval teacherNet inputDomain (-53)).length =
    (SequentialNet.forwardInterval studentNet inputDomain (-53)).length ∧
    ∀ i (hi_t : i < (SequentialNet.forwardInterval teacherNet inputDomain (-53)).length)
        (hi_s : i < (SequentialNet.forwardInterval studentNet inputDomain (-53)).length),
      |(SequentialNet.forwardReal teacherNet [x, y])[i]'(by
          simp only [SequentialNet.forwardReal]
          simp only [SequentialNet.forwardInterval] at hi_t hi_s
          have h := SequentialNet.forwardLength_aux teacherNet.layers [x, y] inputDomain
              (by rfl) teacherNet_wf (-53)
          have hlen : (List.foldl (fun acc l => l.forwardInterval acc (-53)) inputDomain teacherNet.layers).length = 1 := by native_decide
          omega) -
       (SequentialNet.forwardReal studentNet [x, y])[i]'(by
          simp only [SequentialNet.forwardReal]
          simp only [SequentialNet.forwardInterval] at hi_t hi_s
          have h := SequentialNet.forwardLength_aux studentNet.layers [x, y] inputDomain
              (by rfl) studentNet_wf (-53)
          have hlen : (List.foldl (fun acc l => l.forwardInterval acc (-53)) inputDomain studentNet.layers).length = 1 := by native_decide
          omega)| ≤ (epsilon : ℝ) := by
  -- Build domain membership
  have hdom : [x, y].length = inputDomain.length := rfl
  have hmem : ∀ i (hi : i < inputDomain.length), [x, y][i]'(hdom ▸ hi) ∈ inputDomain[i]'hi := by
    intro i hi
    match i with
    | 0 =>
      simp only [inputDomain, List.getElem_cons_zero]
      exact mem_mkInterval (by norm_num) ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩ (-53)
    | 1 =>
      simp only [inputDomain, List.getElem_cons_succ, List.getElem_cons_zero]
      exact mem_mkInterval (by norm_num) ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩ (-53)
    | n + 2 =>
      simp only [inputDomain, List.length_cons, List.length_nil] at hi
      omega
  -- Apply the golden theorem
  exact verify_equivalence teacherNet studentNet inputDomain epsilon (-53)
    [x, y] (by norm_num) teacherNet_wf studentNet_wf hdom hmem distillationCheck_passes

/-! ### Interpretation

The theorem `distillation_certificate` proves that for ANY (x, y) ∈ [0, 1]²:
  |Teacher(x,y) - Student(x,y)| ≤ 3

This bound arises from interval arithmetic conservatism: the analysis computes
bounds on Teacher and Student outputs independently, then subtracts them.

## Applications

- **Deployment Safety**: Verify compressed models before deployment
- **Regulatory Compliance**: Provide machine-checked certificates
- **CI/CD Integration**: Automatically verify model equivalence in pipelines
-/

end LeanCert.Examples.ML.Distillation
