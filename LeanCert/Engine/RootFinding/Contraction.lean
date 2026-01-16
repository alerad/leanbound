/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.RootFinding.MVTBounds
import LeanCert.Engine.RootFinding.Bisection
import Mathlib.Topology.Order.IntermediateValue

/-!
# Root Finding: Newton Contraction Existence Theorem

This file contains the main theorem proving that Newton contraction implies
root existence, along with the uniqueness theorem.

## Main theorems

* `newton_contraction_has_root` - If Newton step contracts, a root exists
* `newton_contraction_unique_root` - If Newton step contracts, exactly one root exists
* `newtonIntervalGo_preserves_root` - Newton iteration preserves roots

## Verification Status

All theorems in this file are **fully proved** with no `sorry` statements.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Newton contraction existence theorem -/

/-- If Newton iteration detects contraction (N ⊂ I strictly), existence of root.
    Combined with newton_preserves_root, this gives uniqueness.

    The key insight is that contraction of the Newton operator implies that
    f must change sign within the interval (otherwise the operator wouldn't contract).
    This uses the structure of Newton's method, not just general contraction. -/
theorem newton_contraction_has_root (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I N : IntervalRat)
    (hN : newtonStepTM e I 0 1 = some N ∨ newtonStepSimple e I 0 = some N)
    (hContract : N.lo > I.lo ∧ N.hi < I.hi)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)) :
    ∃ x ∈ N, Expr.eval (fun _ => x) e = 0 := by
  -- N is non-empty since N.lo ≤ N.hi
  have hN_nonempty : N.lo ≤ N.hi := N.le

  -- N is contained in I
  have hN_in_I : ∀ x, x ∈ N → x ∈ I := by
    intro x hx
    simp only [IntervalRat.mem_def] at hx ⊢
    constructor
    · have h1 : (I.lo : ℝ) < N.lo := by exact_mod_cast hContract.1
      linarith [hx.1]
    · have h2 : (N.hi : ℝ) < I.hi := by exact_mod_cast hContract.2
      linarith [hx.2]

  -- N ⊆ I as sets
  have hN_sub_I : Set.Icc (N.lo : ℝ) N.hi ⊆ Set.Icc (I.lo : ℝ) I.hi := by
    intro z ⟨hzlo, hzhi⟩
    constructor
    · have h1 : (I.lo : ℝ) < N.lo := by exact_mod_cast hContract.1
      linarith
    · have h2 : (N.hi : ℝ) < I.hi := by exact_mod_cast hContract.2
      linarith

  have hCont_N : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc N.lo N.hi) :=
    hCont.mono hN_sub_I

  -- Extract that dI doesn't contain zero
  have hdI_nonzero : ¬(derivInterval e (fun _ => I) 0).containsZero := by
    rcases hN with hTM | hSimple
    · simp only [newtonStepTM] at hTM
      cases htm : TaylorModel.fromExpr? e I 1 with
      | none => simp only [htm, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hTM
      | some tm =>
        simp only [htm] at hTM
        by_cases h : (derivInterval e (fun _ => I) 0).containsZero
        · simp only [h, ↓reduceDIte, Option.bind_eq_bind, Option.bind_fun_none,
          reduceCtorEq] at hTM
        · exact h
    · simp only [newtonStepSimple] at hSimple
      by_cases h : (derivInterval e (fun _ => I) 0).containsZero
      · simp only [h, ↓reduceDIte, reduceCtorEq] at hSimple
      · exact h

  simp only [IntervalRat.containsZero, not_and_or, not_le] at hdI_nonzero

  -- Define convenient aliases
  set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf_def
  set dI := derivInterval e (fun _ => I) 0 with hdI_def

  -- Contraction implies I is non-singleton
  have hI_nonsingleton : I.lo < I.hi := by
    have h1 : (I.lo : ℝ) < N.lo := by exact_mod_cast hContract.1
    have h2 : (N.hi : ℝ) < I.hi := by exact_mod_cast hContract.2
    have h3 : (N.lo : ℝ) ≤ N.hi := by exact_mod_cast hN_nonempty
    linarith

  rcases hdI_nonzero with hdI_pos | hdI_neg
  · -- Case: dI.lo > 0 (derivative positive, f strictly increasing)
    have hf_incr := strictMonoOn_of_deriv_pos_interval e hsupp hvar0 I hdI_pos

    by_cases hlo : f I.lo ≥ 0
    · by_cases hhi : f I.hi ≤ 0
      · -- f(I.lo) ≥ 0 and f(I.hi) ≤ 0 with f increasing → both equal 0
        have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
        have hIlo_in_I : (I.lo : ℝ) ∈ I := by
          simp only [IntervalRat.mem_def]
          exact ⟨le_refl _, by exact_mod_cast I.le⟩
        have hIhi_in_I : (I.hi : ℝ) ∈ I := by
          simp only [IntervalRat.mem_def]
          exact ⟨by exact_mod_cast I.le, le_refl _⟩
        have hroot_lo : f I.lo = 0 := by
          by_cases heq : (I.lo : ℝ) = I.hi
          · have heq_f : f I.lo = f I.hi := by simp only [heq]
            linarith [heq_f]
          · have hlt : (I.lo : ℝ) < I.hi := lt_of_le_of_ne hle heq
            have hmono := hf_incr hIlo_in_I hIhi_in_I hlt
            linarith
        use I.lo
        constructor
        · have hpres := newton_preserves_root e hsupp hvar0 I N hN (I.lo : ℝ) hIlo_in_I hroot_lo
          exact hpres
        · exact hroot_lo
      · -- f(I.lo) ≥ 0 and f(I.hi) > 0
        push_neg at hhi
        by_cases hlo_eq : f I.lo = 0
        · use I.lo
          constructor
          · have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            exact newton_preserves_root e hsupp hvar0 I N hN (I.lo : ℝ) hIlo_in_I hlo_eq
          · exact hlo_eq
        · have hlo_pos : 0 < f I.lo := lt_of_le_of_ne hlo (Ne.symm hlo_eq)
          exfalso
          have hquot_real := newton_positive_increasing_contradicts_contraction e hsupp hvar0 I
            hI_nonsingleton hdI_pos hCont hlo_pos
          have hquot : (evalInterval1 e (IntervalRat.singleton I.midpoint)).hi /
              (derivInterval e (fun _ => I) 0).lo ≥ (I.hi - I.lo) / 2 := by
            have h : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).hi : ℝ) /
                ((derivInterval e (fun _ => I) 0).lo : ℝ) ≥
                (((I.hi - I.lo) / 2 : ℚ) : ℝ) := hquot_real
            have hdI_lo_pos_rat : (0 : ℚ) < (derivInterval e (fun _ => I) 0).lo := hdI_pos
            rw [ge_iff_le]
            have hdiv_cast : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).hi : ℝ) /
                ((derivInterval e (fun _ => I) 0).lo : ℝ) =
                (((evalInterval1 e (IntervalRat.singleton I.midpoint)).hi /
                (derivInterval e (fun _ => I) 0).lo : ℚ) : ℝ) := by
              push_cast; ring
            rw [hdiv_cast] at h
            exact_mod_cast h
          rcases hN with hTM | hSimple
          · -- TM case: use TM structure and generic contradiction
            obtain ⟨tm, hdI_nonzero, htm, hc_eq, hN_lo, hN_hi⟩ := newtonStepTM_structure e I N hTM
            have hfc_correct := newtonStepTM_fc_correct e I tm htm
            have hMVT := mvt_fc_lower_bound_pos_increasing e hsupp hvar0 I hdI_pos hCont hlo_pos
            exact generic_contraction_absurd_hi I I.midpoint (TaylorModel.valueAtCenterInterval tm)
              (derivInterval e (fun _ => I) 0) N rfl hdI_nonzero hdI_pos hfc_correct hN_lo hContract.1 hMVT
          · exact newtonStepSimple_contraction_absurd_hi e I N hSimple hContract hdI_pos hquot
    · push_neg at hlo
      by_cases hhi : f I.hi ≤ 0
      · by_cases hhi_eq : f I.hi = 0
        · use I.hi
          constructor
          · have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            exact newton_preserves_root e hsupp hvar0 I N hN (I.hi : ℝ) hIhi_in_I hhi_eq
          · exact hhi_eq
        · have hhi_neg : f I.hi < 0 := lt_of_le_of_ne hhi hhi_eq
          exfalso
          have hquot_real := newton_negative_increasing_contradicts_contraction e hsupp hvar0 I
            hI_nonsingleton hdI_pos hCont hhi_neg
          have hquot : (evalInterval1 e (IntervalRat.singleton I.midpoint)).lo /
              (derivInterval e (fun _ => I) 0).lo ≤ -((I.hi - I.lo) / 2) := by
            have h : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo : ℝ) /
                ((derivInterval e (fun _ => I) 0).lo : ℝ) ≤
                ((-(((I.hi - I.lo) / 2) : ℚ)) : ℝ) := hquot_real
            rw [le_iff_lt_or_eq]
            rw [le_iff_lt_or_eq] at h
            rcases h with hlt | heq
            · left
              have hdiv_cast : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo : ℝ) /
                  ((derivInterval e (fun _ => I) 0).lo : ℝ) =
                  (((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo /
                  (derivInterval e (fun _ => I) 0).lo : ℚ) : ℝ) := by
                push_cast; ring
              rw [hdiv_cast] at hlt
              exact_mod_cast hlt
            · right
              have hdiv_cast : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo : ℝ) /
                  ((derivInterval e (fun _ => I) 0).lo : ℝ) =
                  (((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo /
                  (derivInterval e (fun _ => I) 0).lo : ℚ) : ℝ) := by
                push_cast; ring
              rw [hdiv_cast] at heq
              exact_mod_cast heq
          rcases hN with hTM | hSimple
          · -- TM case: use TM structure and generic contradiction
            obtain ⟨tm, hdI_nonzero, htm, hc_eq, hN_lo, hN_hi⟩ := newtonStepTM_structure e I N hTM
            have hfc_correct := newtonStepTM_fc_correct e I tm htm
            have hMVT := mvt_fc_upper_bound_pos_increasing e hsupp hvar0 I hdI_pos hCont hhi_neg
            exact generic_contraction_absurd_lo I I.midpoint (TaylorModel.valueAtCenterInterval tm)
              (derivInterval e (fun _ => I) 0) N rfl hdI_nonzero hdI_pos hfc_correct hN_hi hContract.2 hMVT
          · exact newtonStepSimple_contraction_absurd_lo e I N hSimple hContract hdI_pos hquot
      · -- f(I.lo) < 0 and f(I.hi) > 0: SIGN CHANGE! Apply IVT.
        push_neg at hhi
        have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
        have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.lo) (f I.hi) := ⟨le_of_lt hlo, le_of_lt hhi⟩
        have hivt := intermediate_value_Icc hle hCont h0_in_range
        obtain ⟨x, hx_mem, hx_root⟩ := hivt
        use x
        constructor
        · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
          exact newton_preserves_root e hsupp hvar0 I N hN x hx_in_I hx_root
        · exact hx_root

  · -- Case: dI.hi < 0 (derivative negative, f strictly decreasing)
    have hf_decr := strictAntiOn_of_deriv_neg_interval e hsupp hvar0 I hdI_neg

    by_cases hlo : f I.lo ≤ 0
    · by_cases hhi : f I.hi ≥ 0
      · have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
        by_cases heq : (I.lo : ℝ) = I.hi
        · have heq_f : f I.lo = f I.hi := by simp only [heq]
          have hroot : f I.lo = 0 := by linarith [hhi, hlo, heq_f]
          use I.lo
          constructor
          · have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            exact newton_preserves_root e hsupp hvar0 I N hN (I.lo : ℝ) hIlo_in_I hroot
          · exact hroot
        · have hlt : (I.lo : ℝ) < I.hi := lt_of_le_of_ne hle heq
          have hIlo_in_I : (I.lo : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨le_refl _, by exact_mod_cast I.le⟩
          have hIhi_in_I : (I.hi : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨by exact_mod_cast I.le, le_refl _⟩
          have hmono := hf_decr hIlo_in_I hIhi_in_I hlt
          linarith
      · push_neg at hhi
        by_cases hlo_eq : f I.lo = 0
        · use I.lo
          constructor
          · have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            exact newton_preserves_root e hsupp hvar0 I N hN (I.lo : ℝ) hIlo_in_I hlo_eq
          · exact hlo_eq
        · exfalso
          have hlo_neg : f I.lo < 0 := lt_of_le_of_ne hlo hlo_eq
          have hquot_real := newton_negative_decreasing_contradicts_contraction e hsupp hvar0 I
            hI_nonsingleton hdI_neg hCont hlo_neg
          -- MVT gives: fc.lo / dI.hi ≥ hw
          have hquot : (evalInterval1 e (IntervalRat.singleton I.midpoint)).lo /
              (derivInterval e (fun _ => I) 0).hi ≥ (I.hi - I.lo) / 2 := by
            have h : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo : ℝ) /
                ((derivInterval e (fun _ => I) 0).hi : ℝ) ≥
                (((I.hi - I.lo) / 2 : ℚ) : ℝ) := hquot_real
            rw [ge_iff_le]
            have hdiv_cast : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo : ℝ) /
                ((derivInterval e (fun _ => I) 0).hi : ℝ) =
                (((evalInterval1 e (IntervalRat.singleton I.midpoint)).lo /
                (derivInterval e (fun _ => I) 0).hi : ℚ) : ℝ) := by
              push_cast; ring
            rw [hdiv_cast] at h
            exact_mod_cast h
          rcases hN with hTM | hSimple
          · -- TM case: use TM structure and generic contradiction
            obtain ⟨tm, hdI_nonzero, htm, hc_eq, hN_lo, hN_hi⟩ := newtonStepTM_structure e I N hTM
            have hfc_correct := newtonStepTM_fc_correct e I tm htm
            have hMVT := mvt_fc_upper_bound_neg_decreasing e hsupp hvar0 I hI_nonsingleton hdI_neg hCont hlo_neg
            exact generic_contraction_absurd_hi_neg I I.midpoint (TaylorModel.valueAtCenterInterval tm)
              (derivInterval e (fun _ => I) 0) N rfl hdI_nonzero hdI_neg hfc_correct hN_lo hContract.1 hMVT
          · -- For dI < 0: Q.hi ≥ fc.lo / dI.hi ≥ hw (from quotient lemma + MVT)
            -- But contraction implies Q.hi < hw, contradiction!
            obtain ⟨hdI_nonzero, hN_lo_eq, _hN_hi_eq⟩ := newtonStepSimple_extract e I N hSimple
            let c := I.midpoint
            let fc := evalInterval1 e (IntervalRat.singleton c)
            let dI := derivInterval e (fun _ => I) 0
            let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
            let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
            let hw : ℚ := (I.hi - I.lo) / 2
            -- From contraction: N.lo > I.lo, but N.lo = max I.lo (c - Q.hi)
            -- This means c - Q.hi > I.lo, so Q.hi < c - I.lo = hw
            have hQ_hi_lt_hw : Q.hi < hw := by
              have hmax_gt : max I.lo (c - Q.hi) > I.lo := by
                rw [← hN_lo_eq]; exact hContract.1
              have hright_gt : c - Q.hi > I.lo := by
                by_contra h
                push_neg at h
                have : max I.lo (c - Q.hi) = I.lo := max_eq_left h
                rw [this] at hmax_gt
                exact lt_irrefl I.lo hmax_gt
              have hc_minus_Ilo : c - I.lo = hw := by
                show I.midpoint - I.lo = (I.hi - I.lo) / 2
                simp only [IntervalRat.midpoint]; ring
              linarith
            -- But quotient_hi_ge_neg says Q.hi ≥ fc.lo / dI.hi (no sign hypothesis needed!)
            have hQ_hi_ge : Q.hi ≥ fc.lo / dI.hi := quotient_hi_ge_neg hdI_neg
            -- And MVT says fc.lo / dI.hi ≥ hw
            have hQ_hi_ge_hw : Q.hi ≥ hw := le_trans hquot hQ_hi_ge
            linarith
    · push_neg at hlo
      by_cases hhi : f I.hi ≥ 0
      · by_cases hhi_eq : f I.hi = 0
        · use I.hi
          constructor
          · have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            exact newton_preserves_root e hsupp hvar0 I N hN (I.hi : ℝ) hIhi_in_I hhi_eq
          · exact hhi_eq
        · exfalso
          have hhi_pos : 0 < f I.hi := lt_of_le_of_ne hhi (Ne.symm hhi_eq)
          have hquot_real := newton_positive_decreasing_contradicts_contraction e hsupp hvar0 I
            hI_nonsingleton hdI_neg hCont hhi_pos
          -- MVT gives: fc.hi / dI.hi ≤ -hw
          have hquot : (evalInterval1 e (IntervalRat.singleton I.midpoint)).hi /
              (derivInterval e (fun _ => I) 0).hi ≤ -((I.hi - I.lo) / 2) := by
            have h : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).hi : ℝ) /
                ((derivInterval e (fun _ => I) 0).hi : ℝ) ≤
                ((-(((I.hi - I.lo) / 2) : ℚ)) : ℝ) := hquot_real
            have hdiv_cast : ((evalInterval1 e (IntervalRat.singleton I.midpoint)).hi : ℝ) /
                ((derivInterval e (fun _ => I) 0).hi : ℝ) =
                (((evalInterval1 e (IntervalRat.singleton I.midpoint)).hi /
                (derivInterval e (fun _ => I) 0).hi : ℚ) : ℝ) := by
              push_cast; ring
            rw [hdiv_cast] at h
            exact_mod_cast h
          rcases hN with hTM | hSimple
          · -- TM case: use TM structure and generic contradiction
            obtain ⟨tm, hdI_nonzero, htm, hc_eq, hN_lo, hN_hi⟩ := newtonStepTM_structure e I N hTM
            have hfc_correct := newtonStepTM_fc_correct e I tm htm
            have hMVT := mvt_fc_lower_bound_neg_decreasing e hsupp hvar0 I hI_nonsingleton hdI_neg hCont hhi_pos
            exact generic_contraction_absurd_lo_neg I I.midpoint (TaylorModel.valueAtCenterInterval tm)
              (derivInterval e (fun _ => I) 0) N rfl hdI_nonzero hdI_neg hfc_correct hN_hi hContract.2 hMVT
          · -- For dI < 0: Q.lo ≤ fc.hi / dI.hi ≤ -hw (from quotient lemma + MVT)
            -- But contraction implies Q.lo > -hw, contradiction!
            obtain ⟨hdI_nonzero, _hN_lo_eq, hN_hi_eq⟩ := newtonStepSimple_extract e I N hSimple
            let c := I.midpoint
            let fc := evalInterval1 e (IntervalRat.singleton c)
            let dI := derivInterval e (fun _ => I) 0
            let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
            let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
            let hw : ℚ := (I.hi - I.lo) / 2
            -- From contraction: N.hi < I.hi, but N.hi = min I.hi (c - Q.lo)
            -- This means c - Q.lo < I.hi, so Q.lo > c - I.hi = -hw
            have hQ_lo_gt_neg_hw : Q.lo > -hw := by
              have hmin_lt : min I.hi (c - Q.lo) < I.hi := by
                rw [← hN_hi_eq]; exact hContract.2
              have hright_lt : c - Q.lo < I.hi := by
                by_contra h
                push_neg at h
                have : min I.hi (c - Q.lo) = I.hi := min_eq_left h
                rw [this] at hmin_lt
                exact lt_irrefl I.hi hmin_lt
              have hc_minus_Ihi : c - I.hi = -hw := by
                show I.midpoint - I.hi = -((I.hi - I.lo) / 2)
                simp only [IntervalRat.midpoint]; ring
              linarith
            -- But quotient_lo_le_neg says Q.lo ≤ fc.hi / dI.hi (no sign hypothesis needed!)
            have hQ_lo_le : Q.lo ≤ fc.hi / dI.hi := quotient_lo_le_neg hdI_neg
            -- And MVT says fc.hi / dI.hi ≤ -hw
            have hQ_lo_le_neg_hw : Q.lo ≤ -hw := le_trans hQ_lo_le hquot
            linarith
      · -- f(I.lo) > 0 and f(I.hi) < 0: SIGN CHANGE for decreasing function!
        push_neg at hhi
        have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
        have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hhi, le_of_lt hlo⟩
        have hivt := intermediate_value_Icc' hle hCont h0_in_range
        obtain ⟨x, hx_mem, hx_root⟩ := hivt
        use x
        constructor
        · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
          exact newton_preserves_root e hsupp hvar0 I N hN x hx_in_I hx_root
        · exact hx_root

/-- If Newton iteration detects contraction, the root is unique in I.
    This is THE key uniqueness theorem for Newton's method. -/
theorem newton_contraction_unique_root (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I N : IntervalRat)
    (hN : newtonStepTM e I 0 1 = some N ∨ newtonStepSimple e I 0 = some N)
    (hContract : N.lo > I.lo ∧ N.hi < I.hi)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  obtain ⟨x₀, hx₀_mem, hx₀_root⟩ := newton_contraction_has_root e hsupp hvar0 I N hN hContract hCont
  have hx₀_in_I : x₀ ∈ I := by
    simp only [IntervalRat.mem_def] at hx₀_mem ⊢
    constructor
    · have h1 : (I.lo : ℝ) < N.lo := by exact_mod_cast hContract.1
      linarith [hx₀_mem.1]
    · have h2 : (N.hi : ℝ) < I.hi := by exact_mod_cast hContract.2
      linarith [hx₀_mem.2]
  use x₀
  constructor
  · exact ⟨hx₀_in_I, hx₀_root⟩
  · intro y ⟨hy_in_I, hy_root⟩
    -- Use newton_step_at_most_one_root
    have hNewtonExists : (∃ M, newtonStepTM e I 0 1 = some M) ∨ (∃ M, newtonStepSimple e I 0 = some M) := by
      rcases hN with h | h
      · left; exact ⟨N, h⟩
      · right; exact ⟨N, h⟩
    exact (newton_step_at_most_one_root e hsupp hvar0 I hNewtonExists hCont x₀ y hx₀_in_I hy_in_I hx₀_root hy_root).symm

/-! ### Newton iteration loop correctness -/

/-- If a root exists in J and Newton iteration doesn't return noRoot, the root is preserved.
    Key lemma for proving noRoot correctness.

    Note: Uses newton_preserves_root which puts x in both J and N -/
theorem newtonIntervalGo_preserves_root (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (J : IntervalRat) (iter : ℕ) (contracted : Bool)
    (x : ℝ) (hxJ : x ∈ J) (hroot : Expr.eval (fun _ => x) e = 0) :
    (newtonIntervalGo e 0 1 J iter contracted).2 ≠ RootStatus.noRoot := by
  induction iter generalizing J contracted with
  | zero =>
    -- Base case: iter = 0
    simp only [newtonIntervalGo]
    split_ifs with hc
    · -- contracted = true: returns uniqueRoot ≠ noRoot
      simp only [ne_eq]
      intro h
      exact RootStatus.noConfusion h
    · -- contracted = false: returns checkRootStatus e J
      intro hcheck
      -- checkRootStatus = noRoot implies excludesZero
      have hexcl := checkRootStatus_noRoot_implies_excludesZero e J hcheck
      -- But excludesZero_correct says no root in J, contradicting hroot
      have hnoroot := excludesZero_correct e hsupp J hexcl x hxJ
      exact hnoroot hroot
  | succ n ih =>
    -- Inductive case: iter = n + 1
    simp only [newtonIntervalGo]
    -- Match on newtonStepTM result
    match htm : newtonStepTM e J 0 1 with
    | none =>
      -- TM step failed, try simple
      simp
      match hsimple : newtonStepSimple e J 0 with
      | none =>
        -- Both steps failed: returns based on contracted
        simp
        split_ifs with hc
        · intro h
          exact h.elim
        · intro hcheck
          have hexcl := checkRootStatus_noRoot_implies_excludesZero e J hcheck
          have hnoroot := excludesZero_correct e hsupp J hexcl x hxJ
          exact hnoroot hroot
      | some N =>
        -- Simple step succeeded with N
        simp
        -- Extract membership bounds before splitting
        have hxN := newton_preserves_root e hsupp hvar0 J N (Or.inr hsimple) x hxJ hroot
        have hxJ_lo : (J.lo : ℝ) ≤ x := by simp only [IntervalRat.mem_def] at hxJ; exact hxJ.1
        have hxJ_hi : x ≤ (J.hi : ℝ) := by simp only [IntervalRat.mem_def] at hxJ; exact hxJ.2
        have hxN_lo : (N.lo : ℝ) ≤ x := by simp only [IntervalRat.mem_def] at hxN; exact hxN.1
        have hxN_hi : x ≤ (N.hi : ℝ) := by simp only [IntervalRat.mem_def] at hxN; exact hxN.2
        -- Need to handle the processStep logic
        split_ifs with hcontract hno_intersect
        · -- Contraction case: recurse with true
          exact ih N true hxN
        · -- No intersection case: returns (J, noRoot)
          -- With strict inequality (N.lo > J.hi ∨ N.hi < J.lo), truly disjoint intervals
          intro _
          rcases hno_intersect with hlo | hhi
          · -- N.lo > J.hi: strict disjoint
            have hcast : (J.hi : ℝ) < N.lo := by exact_mod_cast hlo
            linarith
          · -- N.hi < J.lo: strict disjoint
            have hcast : (N.hi : ℝ) < J.lo := by exact_mod_cast hhi
            linarith
        · -- Normal recursion case
          exact ih N contracted hxN
    | some N =>
      -- TM step succeeded with N
      simp
      -- Extract membership bounds before splitting
      have hxN := newton_preserves_root e hsupp hvar0 J N (Or.inl htm) x hxJ hroot
      have hxJ_lo : (J.lo : ℝ) ≤ x := by simp only [IntervalRat.mem_def] at hxJ; exact hxJ.1
      have hxJ_hi : x ≤ (J.hi : ℝ) := by simp only [IntervalRat.mem_def] at hxJ; exact hxJ.2
      have hxN_lo : (N.lo : ℝ) ≤ x := by simp only [IntervalRat.mem_def] at hxN; exact hxN.1
      have hxN_hi : x ≤ (N.hi : ℝ) := by simp only [IntervalRat.mem_def] at hxN; exact hxN.2
      split_ifs with hcontract hno_intersect
      · -- Contraction case
        exact ih N true hxN
      · -- No intersection case (strict inequality)
        intro _
        rcases hno_intersect with hlo | hhi
        · have hcast : (J.hi : ℝ) < N.lo := by exact_mod_cast hlo
          linarith
        · have hcast : (N.hi : ℝ) < J.lo := by exact_mod_cast hhi
          linarith
      · -- Normal recursion case
        exact ih N contracted hxN

end LeanCert.Engine
