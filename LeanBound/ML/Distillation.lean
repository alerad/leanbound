/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.ML.Network
import LeanBound.ML.IntervalVector

/-!
# Verified Model Distillation / Equivalence Checking

This module implements the logic to verify that two neural networks
(e.g., a massive Teacher and a compressed Student) produce outputs
that are within a specific tolerance `ε` of each other for ALL inputs
in a given domain.

## Main Definitions

* `SequentialNet` - A network with N layers
* `checkEquivalence` - Computable certificate for network equivalence
* `verify_equivalence` - The main theorem proving |T(x) - S(x)| ≤ ε

## The Math

We define the difference graph:
  Diff(x) = Teacher(x) - Student(x)

We compute interval bounds for Diff(InputBox).
If the resulting interval is contained in [-ε, ε], the networks are ε-equivalent.
-/

namespace LeanBound.ML.Distillation

open LeanBound.Core
open LeanBound.ML
open LeanBound.Numerics

/-! ### Interval Subtraction -/

/-- Negate an interval: -I = [-hi, -lo] -/
def IntervalDyadic.neg (I : IntervalDyadic) : IntervalDyadic where
  lo := Dyadic.neg I.hi
  hi := Dyadic.neg I.lo
  le := by
    have h := Dyadic.toRat_neg I.hi
    have h' := Dyadic.toRat_neg I.lo
    rw [h, h']
    linarith [I.le]

/-- Membership in negated interval -/
theorem IntervalDyadic.mem_neg {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    -x ∈ I.neg := by
  simp only [IntervalDyadic.mem_def] at hx ⊢
  constructor
  · -- Lower bound: (I.neg.lo.toRat : ℝ) ≤ -x
    show (↑(Dyadic.neg I.hi).toRat : ℝ) ≤ -x
    rw [Dyadic.toRat_neg, Rat.cast_neg]
    linarith [hx.2]
  · -- Upper bound: -x ≤ (I.neg.hi.toRat : ℝ)
    show -x ≤ ↑(Dyadic.neg I.lo).toRat
    rw [Dyadic.toRat_neg, Rat.cast_neg]
    linarith [hx.1]

/-- Subtract two intervals: I - J = I + (-J) -/
def IntervalDyadic.sub (I J : IntervalDyadic) : IntervalDyadic :=
  IntervalDyadic.add I J.neg

/-- Membership in subtracted interval -/
theorem IntervalDyadic.mem_sub {x y : ℝ} {I J : IntervalDyadic}
    (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ I.sub J := by
  simp only [sub, sub_eq_add_neg]
  exact IntervalDyadic.mem_add hx (IntervalDyadic.mem_neg hy)

/-! ### Sequential Network Infrastructure -/

/-- A standard feedforward network is just a list of layers -/
structure SequentialNet where
  layers : List Layer
  deriving Repr

namespace SequentialNet

/-- Real-valued forward pass -/
def forwardReal (net : SequentialNet) (x : List ℝ) : List ℝ :=
  net.layers.foldl (fun acc l => Layer.forwardReal l acc) x

/-- Interval forward pass -/
def forwardInterval (net : SequentialNet) (x : IntervalVector) (prec : Int) : IntervalVector :=
  net.layers.foldl (fun acc l => Layer.forwardInterval l acc prec) x

/-- A layer chain is well-formed if dimensions align -/
def LayersWellFormed : List Layer → Nat → Prop
  | [], _ => True
  | l :: rest, inputDim =>
      l.WellFormed ∧
      l.inputDim = inputDim ∧
      LayersWellFormed rest (min l.outputDim l.bias.length)

/-- Check if all layers in the sequence are well-formed and dimensions align -/
def WellFormed (net : SequentialNet) (inputDim : Nat) : Prop :=
  LayersWellFormed net.layers inputDim

/-- Helper: Lengths of foldl outputs match -/
theorem forwardLength_aux (layers : List Layer) (xs : List ℝ) (Is : IntervalVector)
    (hdim : xs.length = Is.length)
    (hwf : LayersWellFormed layers xs.length) (prec : Int) :
    (layers.foldl (fun acc l => Layer.forwardReal l acc) xs).length =
    (layers.foldl (fun acc l => Layer.forwardInterval l acc prec) Is).length := by
  induction layers generalizing xs Is with
  | nil => exact hdim
  | cons l rest ih =>
    simp only [List.foldl_cons, LayersWellFormed] at hwf ⊢
    obtain ⟨l_wf, l_dim, rest_wf⟩ := hwf
    have hRealLen := Layer.forwardReal_length l xs
    have hIntLen := Layer.forwardInterval_length l Is prec
    have hNext : (Layer.forwardReal l xs).length = (Layer.forwardInterval l Is prec).length := by
      rw [hRealLen, hIntLen]
    have hwf' : LayersWellFormed rest (Layer.forwardReal l xs).length := by
      rw [hRealLen]; exact rest_wf
    exact ih _ _ hNext hwf'

/-- Soundness of SequentialNet forward pass -/
theorem mem_forwardInterval_aux (layers : List Layer) (xs : List ℝ) (Is : IntervalVector)
    (hdim : xs.length = Is.length)
    (hwf : LayersWellFormed layers xs.length)
    (hmem : ∀ i (hi : i < Is.length), xs[i]'(hdim ▸ hi) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0) :
    let outReal := layers.foldl (fun acc l => Layer.forwardReal l acc) xs
    let outInt := layers.foldl (fun acc l => Layer.forwardInterval l acc prec) Is
    ∀ i (hi : i < outInt.length),
      outReal[i]'((forwardLength_aux layers xs Is hdim hwf prec) ▸ hi) ∈ outInt[i]'hi := by
  induction layers generalizing xs Is with
  | nil =>
    simp only [List.foldl_nil]
    intro i hi; exact hmem i hi
  | cons layer rest ih =>
    simp only [List.foldl_cons]
    -- Unpack WellFormed hypothesis
    simp only [LayersWellFormed] at hwf
    obtain ⟨l_wf, l_dim, rest_wf⟩ := hwf

    -- First layer output
    let nextReal := Layer.forwardReal layer xs
    let nextInt := Layer.forwardInterval layer Is prec

    -- Lengths of next layer outputs
    have hRealLen : nextReal.length = min layer.outputDim layer.bias.length :=
      Layer.forwardReal_length layer xs
    have hIntLen : nextInt.length = min layer.outputDim layer.bias.length :=
      Layer.forwardInterval_length layer Is prec
    have hNextLen : nextReal.length = nextInt.length := by rw [hRealLen, hIntLen]

    -- Layer 1 is sound
    have hL1 : ∀ j (hj : j < min layer.outputDim layer.bias.length),
        nextReal[j]'(hRealLen ▸ hj) ∈ nextInt[j]'(hIntLen ▸ hj) := by
      have hdim' : layer.inputDim = Is.length := by rw [l_dim, hdim]
      exact Layer.mem_forwardInterval l_wf hdim' hdim hmem prec hprec

    -- Translate membership for next layer
    have hmem' : ∀ i (hi : i < nextInt.length),
        nextReal[i]'(hNextLen ▸ hi) ∈ nextInt[i]'hi := by
      intro i hi
      have hi' : i < min layer.outputDim layer.bias.length := by rw [hIntLen] at hi; exact hi
      exact hL1 i hi'

    -- Well-formedness for rest uses output dim
    have hwf' : LayersWellFormed rest nextReal.length := by
      rw [hRealLen]; exact rest_wf

    exact ih nextReal nextInt hNextLen hwf' hmem'

/-- Public soundness theorem -/
theorem mem_forwardInterval {net : SequentialNet} {xs : List ℝ} {Is : IntervalVector}
    (hdim : xs.length = Is.length)
    (hwf : WellFormed net xs.length)
    (hmem : ∀ i (hi : i < Is.length), xs[i]'(hdim ▸ hi) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    let outReal := forwardReal net xs
    let outInt := forwardInterval net Is prec
    outReal.length = outInt.length ∧
    ∀ i (hi : i < outInt.length), outReal[i]'((forwardLength_aux net.layers xs Is hdim hwf prec) ▸ hi) ∈ outInt[i]'hi :=
  ⟨forwardLength_aux net.layers xs Is hdim hwf prec, mem_forwardInterval_aux net.layers xs Is hdim hwf hmem prec hprec⟩

end SequentialNet

/-! ### Interval Vector Subtraction -/

/-- Subtract two interval vectors (pointwise) -/
def subVectors (a b : IntervalVector) : IntervalVector :=
  List.zipWith IntervalDyadic.sub a b

/-- Length of subtracted vectors -/
theorem subVectors_length (a b : IntervalVector) :
    (subVectors a b).length = min a.length b.length := by
  simp [subVectors, List.length_zipWith]

/-- Membership in subtracted vectors -/
theorem mem_subVectors {ra rb : List ℝ} {ia ib : IntervalVector}
    (halen : ra.length = ia.length)
    (hblen : rb.length = ib.length)
    (ha : ∀ i (hi : i < ia.length), ra[i]'(halen ▸ hi) ∈ ia[i]'hi)
    (hb : ∀ i (hi : i < ib.length), rb[i]'(hblen ▸ hi) ∈ ib[i]'hi) :
    ∀ i (hi : i < (subVectors ia ib).length),
      (ra[i]'(by simp [subVectors_length] at hi; rw [halen]; omega) -
       rb[i]'(by simp [subVectors_length] at hi; rw [hblen]; omega)) ∈
      (subVectors ia ib)[i]'hi := by
  intro i hi
  simp only [subVectors_length] at hi
  have hi_ia : i < ia.length := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hi_ib : i < ib.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
  simp only [subVectors, List.getElem_zipWith]
  exact IntervalDyadic.mem_sub (ha i hi_ia) (hb i hi_ib)

/-! ### The Equivalence Checker -/

/-- Check if an interval is contained within [-eps, eps] -/
def intervalBoundedBy (I : IntervalDyadic) (eps : ℚ) : Bool :=
  let r := I.toIntervalRat
  decide ((-eps) ≤ r.lo ∧ r.hi ≤ eps)

/-- Check if an interval vector is contained within [-eps, eps] -/
def isBoundedBy (v : IntervalVector) (eps : ℚ) : Bool :=
  v.all (intervalBoundedBy · eps)

/-- Soundness of intervalBoundedBy -/
theorem intervalBoundedBy_spec {x : ℝ} {I : IntervalDyadic} {eps : ℚ}
    (hx : x ∈ I) (hcheck : intervalBoundedBy I eps = true) :
    |x| ≤ (eps : ℝ) := by
  simp only [intervalBoundedBy, decide_eq_true_eq] at hcheck
  rw [abs_le]
  have hmem := IntervalDyadic.mem_toIntervalRat.mp hx
  simp only [IntervalRat.mem_def] at hmem
  constructor
  · calc -(eps : ℝ) ≤ (I.toIntervalRat.lo : ℝ) := by exact_mod_cast hcheck.1
      _ ≤ x := hmem.1
  · calc x ≤ (I.toIntervalRat.hi : ℝ) := hmem.2
      _ ≤ eps := by exact_mod_cast hcheck.2

/--
  **The Distillation Certifier**

  Returns `true` if the student network is proven to be within `eps`
  of the teacher network for all inputs in the domain.
-/
def checkEquivalence (teacher student : SequentialNet)
    (domain : IntervalVector) (eps : ℚ) (prec : Int := -53) : Bool :=
  let t_out := SequentialNet.forwardInterval teacher domain prec
  let s_out := SequentialNet.forwardInterval student domain prec
  -- We only compare if output dimensions match
  if t_out.length != s_out.length then false
  else
    let diff := subVectors t_out s_out
    isBoundedBy diff eps

/-! ### Correctness Proofs -/

/-- Helper: extract dimension equality from checkEquivalence -/
theorem checkEquivalence_dims {teacher student : SequentialNet}
    {domain : IntervalVector} {eps : ℚ} {prec : Int}
    (h : checkEquivalence teacher student domain eps prec = true) :
    (SequentialNet.forwardInterval teacher domain prec).length =
    (SequentialNet.forwardInterval student domain prec).length := by
  unfold checkEquivalence at h
  by_cases hdim : (SequentialNet.forwardInterval teacher domain prec).length =
                  (SequentialNet.forwardInterval student domain prec).length
  · exact hdim
  · simp only [bne_iff_ne, ne_eq, hdim, not_false_eq_true, ↓reduceIte] at h
    exact absurd h (by decide)

/-- **Golden Theorem: Verified Model Distillation**

    If `checkEquivalence` returns true, then for ALL real inputs `x` in the domain,
    the output difference `|Teacher(x) - Student(x)|` is at most `eps` for every output neuron.
-/
theorem verify_equivalence (teacher student : SequentialNet)
    (domain : IntervalVector) (eps : ℚ) (prec : Int)
    (x : List ℝ)
    (hprec : prec ≤ 0)
    (hwf_t : teacher.WellFormed x.length)
    (hwf_s : student.WellFormed x.length)
    (h_dom_len : x.length = domain.length)
    (h_mem : ∀ i (hi : i < domain.length), x[i]'(h_dom_len ▸ hi) ∈ domain[i]'hi)
    (h_cert : checkEquivalence teacher student domain eps prec = true) :
    let t_out := SequentialNet.forwardReal teacher x
    let s_out := SequentialNet.forwardReal student x
    let t_int := SequentialNet.forwardInterval teacher domain prec
    let s_int := SequentialNet.forwardInterval student domain prec
    -- Dimensions match
    t_int.length = s_int.length ∧
    -- All outputs are within eps
    ∀ i (hi_t : i < t_int.length) (hi_s : i < s_int.length),
      |t_out[i]'((SequentialNet.forwardLength_aux teacher.layers x domain h_dom_len hwf_t prec) ▸ hi_t) -
       s_out[i]'((SequentialNet.forwardLength_aux student.layers x domain h_dom_len hwf_s prec) ▸ hi_s)| ≤ (eps : ℝ) := by
  -- Get dimension equality
  have h_dim := checkEquivalence_dims h_cert

  -- Interval soundness
  have ⟨hT_len, hT_mem⟩ := SequentialNet.mem_forwardInterval h_dom_len hwf_t h_mem prec hprec
  have ⟨hS_len, hS_mem⟩ := SequentialNet.mem_forwardInterval h_dom_len hwf_s h_mem prec hprec

  constructor
  · exact h_dim
  · intro i hi_t hi_s

    -- Get membership in difference
    have hdiff := mem_subVectors hT_len hS_len hT_mem hS_mem

    -- The diff vector
    let diff := subVectors
      (SequentialNet.forwardInterval teacher domain prec)
      (SequentialNet.forwardInterval student domain prec)

    -- Index bound for diff
    have hi_diff : i < diff.length := by
      have hlen := subVectors_length (SequentialNet.forwardInterval teacher domain prec)
                                     (SequentialNet.forwardInterval student domain prec)
      rw [hlen, h_dim, Nat.min_self]
      exact h_dim ▸ hi_t

    -- Get membership for index i
    have hdiff_i := hdiff i hi_diff

    -- Apply the bounded check
    unfold checkEquivalence at h_cert
    by_cases hdim_eq : (SequentialNet.forwardInterval teacher domain prec).length =
                       (SequentialNet.forwardInterval student domain prec).length
    · simp only [bne_iff_ne, ne_eq, hdim_eq, not_true_eq_false, ↓reduceIte,
                 isBoundedBy, List.all_eq_true] at h_cert
      have hbound := h_cert (diff[i]) (List.getElem_mem hi_diff)
      exact intervalBoundedBy_spec hdiff_i hbound
    · simp only [bne_iff_ne, ne_eq, hdim_eq, not_false_eq_true, ↓reduceIte] at h_cert
      exact absurd h_cert (by decide)

end LeanBound.ML.Distillation
