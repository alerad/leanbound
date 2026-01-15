/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.IntervalReal

/-!
# Affine Arithmetic

This file implements Affine Arithmetic (AA), which tracks linear dependencies
between variables to avoid the "dependency problem" in interval arithmetic.

## The Dependency Problem

Standard interval arithmetic treats each occurrence of a variable independently:
- `x - x` with `x ∈ [-1, 1]` gives `[-2, 2]` instead of `[0, 0]`

Affine arithmetic solves this by representing values as:
  `x̂ = c₀ + Σᵢ cᵢ·εᵢ + [-r, r]`

where `εᵢ ∈ [-1, 1]` are noise symbols tracking input correlations.

## Main definitions

* `AffineForm` - Affine representation: central value + linear terms + error
* `AffineForm.add`, `sub`, `neg`, `scale` - Linear operations (exact)
* `AffineForm.mul` - Multiplication (introduces error)
* `AffineForm.toInterval` - Convert back to interval bounds

## Key Properties

* `sub_self_c0` - x - x has central value 0
* `sub_self_radius_zero` - For input forms (r=0), x - x has radius 0

## References

* Stolfi & de Figueiredo, "Self-Validated Numerical Methods and Applications"
-/

namespace LeanBound.Numerics.Affine

open LeanBound.Core

/-! ## Helper Lemmas -/

private theorem list_foldl_abs_nonneg (l : List ℚ) (init : ℚ) (hinit : 0 ≤ init) :
    0 ≤ l.foldl (fun acc c => acc + |c|) init := by
  induction l generalizing init with
  | nil => exact hinit
  | cons h t ih =>
    simp only [List.foldl_cons]
    apply ih
    have := abs_nonneg h
    linarith

/-! ## The Affine Form Data Structure -/

/-- Affine Form: `c₀ + Σᵢ (coeffs[i] * εᵢ) + [-r, r]`

    where `εᵢ ∈ [-1, 1]` are independent noise symbols. -/
structure AffineForm where
  c0 : ℚ
  coeffs : List ℚ
  r : ℚ
  r_nonneg : 0 ≤ r
  deriving Repr

namespace AffineForm

def const (q : ℚ) : AffineForm :=
  { c0 := q, coeffs := [], r := 0, r_nonneg := le_refl 0 }

def zero : AffineForm := const 0

instance : Inhabited AffineForm := ⟨zero⟩

/-! ## Helper Functions -/

def sumAbs (l : List ℚ) : ℚ := l.foldl (fun acc c => acc + |c|) 0

theorem sumAbs_nonneg (l : List ℚ) : 0 ≤ sumAbs l :=
  list_foldl_abs_nonneg l 0 (le_refl 0)

def deviationBound (af : AffineForm) : ℚ := af.r + sumAbs af.coeffs

theorem deviationBound_nonneg (af : AffineForm) : 0 ≤ af.deviationBound := by
  simp only [deviationBound]
  have h1 := af.r_nonneg
  have h2 := sumAbs_nonneg af.coeffs
  linarith

def zipWithPad (f : ℚ → ℚ → ℚ) (l1 l2 : List ℚ) : List ℚ :=
  match l1, l2 with
  | [], [] => []
  | [], h :: t => f 0 h :: zipWithPad f [] t
  | h :: t, [] => f h 0 :: zipWithPad f t []
  | h1 :: t1, h2 :: t2 => f h1 h2 :: zipWithPad f t1 t2

/-! ## Linear Operations (Exact) -/

def add (a b : AffineForm) : AffineForm :=
  { c0 := a.c0 + b.c0
    coeffs := zipWithPad (· + ·) a.coeffs b.coeffs
    r := a.r + b.r
    r_nonneg := add_nonneg a.r_nonneg b.r_nonneg }

def neg (a : AffineForm) : AffineForm :=
  { c0 := -a.c0
    coeffs := a.coeffs.map (·.neg)
    r := a.r
    r_nonneg := a.r_nonneg }

def sub (a b : AffineForm) : AffineForm := add a (neg b)

def scale (q : ℚ) (a : AffineForm) : AffineForm :=
  { c0 := q * a.c0
    coeffs := a.coeffs.map (q * ·)
    r := |q| * a.r
    r_nonneg := mul_nonneg (abs_nonneg q) a.r_nonneg }

/-! ## Non-Linear Operations -/

def mul (a b : AffineForm) : AffineForm :=
  let cx := a.c0
  let cy := b.c0
  let new_coeffs := zipWithPad (fun ca cb => cx * cb + cy * ca) a.coeffs b.coeffs
  let rad_a := deviationBound a
  let rad_b := deviationBound b
  let quad_error := rad_a * rad_b
  let new_r := |cx| * b.r + |cy| * a.r + quad_error
  { c0 := cx * cy
    coeffs := new_coeffs
    r := new_r
    r_nonneg := by
      have h1 : 0 ≤ |cx| * b.r := mul_nonneg (abs_nonneg cx) b.r_nonneg
      have h2 : 0 ≤ |cy| * a.r := mul_nonneg (abs_nonneg cy) a.r_nonneg
      have h3 : 0 ≤ quad_error := mul_nonneg (deviationBound_nonneg a) (deviationBound_nonneg b)
      linarith }

def sq (a : AffineForm) : AffineForm :=
  let cx := a.c0
  let new_coeffs := a.coeffs.map (2 * cx * ·)
  let rad := deviationBound a
  let quad_error := rad * rad
  let new_r := 2 * |cx| * a.r + quad_error
  { c0 := cx * cx
    coeffs := new_coeffs
    r := new_r
    r_nonneg := by
      have h1 : 0 ≤ 2 * |cx| * a.r := by nlinarith [abs_nonneg cx, a.r_nonneg]
      have h2 : 0 ≤ quad_error := mul_nonneg (deviationBound_nonneg a) (deviationBound_nonneg a)
      linarith }

/-! ## Interval Conversion -/

def ofInterval (I : IntervalRat) (idx : Nat) (totalVars : Nat) : AffineForm :=
  let mid := (I.lo + I.hi) / 2
  let rad := (I.hi - I.lo) / 2
  let coeffs := List.range totalVars |>.map (fun i => if i == idx then rad else 0)
  { c0 := mid, coeffs := coeffs, r := 0, r_nonneg := le_refl 0 }

def toInterval (af : AffineForm) : IntervalRat :=
  let width := af.deviationBound
  { lo := af.c0 - width
    hi := af.c0 + width
    le := by linarith [deviationBound_nonneg af] }

/-! ## The Key Property: x - x = 0 -/

/-- The central value of x - x is exactly 0 -/
theorem sub_self_c0 (a : AffineForm) : (sub a a).c0 = 0 := by
  simp only [sub, add, neg]; ring

/-- For an input affine form (r = 0), x - x has zero radius -/
theorem sub_self_radius_zero (a : AffineForm) (h : a.r = 0) : (sub a a).r = 0 := by
  simp only [sub, add, neg]; linarith [a.r_nonneg]

/-- Helper: zipWithPad (· + ·) l (l.map neg) gives all zeros -/
private theorem zipWithPad_add_neg_zero (l : List ℚ) :
    ∀ c ∈ zipWithPad (· + ·) l (l.map (·.neg)), c = 0 := by
  induction l with
  | nil =>
    intro c hc
    simp only [List.map_nil, zipWithPad, List.not_mem_nil] at hc
  | cons h t ih =>
    intro c hc
    simp only [List.map_cons, zipWithPad, List.mem_cons] at hc
    cases hc with
    | inl heq =>
      rw [heq]
      show h + (-h) = 0
      ring
    | inr hmem => exact ih c hmem

/-- Subtraction of the same form gives all-zero coefficients -/
theorem sub_self_coeffs_allzero (a : AffineForm) :
    ∀ c ∈ (sub a a).coeffs, c = 0 := by
  simp only [sub, add, neg]
  exact zipWithPad_add_neg_zero a.coeffs

/-! ## Soundness Infrastructure -/

abbrev NoiseAssignment := List ℝ

def validNoise (eps : NoiseAssignment) : Prop := ∀ e, e ∈ eps → -1 ≤ e ∧ e ≤ 1

/-- The linear functional Σ cᵢ * εᵢ -/
def linearSum (coeffs : List ℚ) (eps : NoiseAssignment) : ℝ :=
  (List.zipWith (fun (c : ℚ) (e : ℝ) => (c : ℝ) * e) coeffs eps).sum

def evalLinear (af : AffineForm) (eps : NoiseAssignment) : ℝ :=
  (af.c0 : ℝ) + linearSum af.coeffs eps

def mem_affine (af : AffineForm) (eps : NoiseAssignment) (v : ℝ) : Prop :=
  ∃ (err : ℝ), |err| ≤ af.r ∧ v = evalLinear af eps + err

/-! ### Helper lemmas for soundness -/

/-- linearSum of zipWithPad addition equals sum of linearSums (when lengths match eps) -/
private theorem linearSum_zipWithPad_add (l1 l2 : List ℚ) (eps : NoiseAssignment) :
    linearSum (zipWithPad (· + ·) l1 l2) eps =
    linearSum l1 eps + linearSum l2 eps := by
  simp only [linearSum]
  induction l1 generalizing l2 eps with
  | nil =>
    induction l2 generalizing eps with
    | nil => simp [zipWithPad]
    | cons h2 t2 ih2 =>
      cases eps with
      | nil => simp [zipWithPad, List.zipWith]
      | cons e es =>
        simp only [zipWithPad, List.zipWith, List.sum_cons, List.zipWith_nil_left]
        rw [ih2 es]
        simp [List.zipWith]
  | cons h1 t1 ih1 =>
    cases l2 with
    | nil =>
      cases eps with
      | nil => simp [zipWithPad, List.zipWith]
      | cons e es =>
        simp only [zipWithPad, List.zipWith, List.sum_cons]
        have := ih1 [] es
        simp only [zipWithPad, List.zipWith, List.sum_nil, add_zero] at this
        rw [this]
        simp [List.zipWith]
    | cons h2 t2 =>
      cases eps with
      | nil => simp [zipWithPad, List.zipWith]
      | cons e es =>
        simp only [zipWithPad, List.zipWith, List.sum_cons]
        rw [ih1 t2 es]
        push_cast
        ring

/-- linearSum of negated coefficients equals negation of linearSum -/
private theorem linearSum_map_neg (l : List ℚ) (eps : NoiseAssignment) :
    linearSum (l.map (·.neg)) eps = -linearSum l eps := by
  simp only [linearSum]
  induction l generalizing eps with
  | nil => simp [List.zipWith]
  | cons h t ih =>
    cases eps with
    | nil => simp [List.zipWith]
    | cons e es =>
      simp only [List.map_cons, List.zipWith, List.sum_cons]
      rw [ih es]
      have : ((h.neg : ℚ) : ℝ) = -((h : ℚ) : ℝ) := by
        show ((-h : ℚ) : ℝ) = -(h : ℝ)
        exact Rat.cast_neg h
      rw [this]
      ring

/-! ## Soundness Proofs -/

/-- Constants are sound: const q represents q -/
theorem mem_const (q : ℚ) (eps : NoiseAssignment) :
    mem_affine (const q) eps (q : ℝ) := by
  use 0
  constructor
  · simp [const]
  · simp [evalLinear, const, linearSum]

/-- Helper: linearSum of scaled coefficients equals scaled linearSum -/
private theorem linearSum_map_mul (q : ℚ) (coeffs : List ℚ) (eps : NoiseAssignment) :
    linearSum (coeffs.map (q * ·)) eps = (q : ℝ) * linearSum coeffs eps := by
  simp only [linearSum]
  induction coeffs generalizing eps with
  | nil => simp [List.zipWith]
  | cons c cs ih =>
    cases eps with
    | nil => simp [List.zipWith]
    | cons e es =>
      simp only [List.map_cons, List.zipWith, List.sum_cons]
      rw [ih es]
      push_cast
      ring

/-- Scalar multiplication is sound -/
theorem mem_scale (q : ℚ) {a : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hmem : mem_affine a eps v) :
    mem_affine (scale q a) eps ((q : ℝ) * v) := by
  obtain ⟨err, herr, hv⟩ := hmem
  use (q : ℝ) * err
  constructor
  · calc |(q : ℝ) * err| = |(q : ℝ)| * |err| := abs_mul _ _
      _ ≤ |(q : ℝ)| * (a.r : ℝ) := by nlinarith [abs_nonneg (q : ℝ)]
      _ = ((|q| * a.r : ℚ) : ℝ) := by push_cast; rw [← Rat.cast_abs]
  · simp only [evalLinear, scale, linearSum_map_mul]
    simp only [evalLinear] at hv
    rw [hv]
    push_cast
    ring

/-- Addition is sound -/
theorem mem_add {a b : AffineForm} {eps : NoiseAssignment} {va vb : ℝ}
    (ha : mem_affine a eps va) (hb : mem_affine b eps vb) :
    mem_affine (add a b) eps (va + vb) := by
  obtain ⟨erra, herra_bound, hva⟩ := ha
  obtain ⟨errb, herrb_bound, hvb⟩ := hb
  use erra + errb
  constructor
  · -- |erra + errb| ≤ |erra| + |errb| ≤ a.r + b.r
    have h1 : |erra| ≤ (a.r : ℝ) := herra_bound
    have h2 : |errb| ≤ (b.r : ℝ) := herrb_bound
    have h3 : ((add a b).r : ℝ) = a.r + b.r := by simp only [add, Rat.cast_add]
    calc |erra + errb| ≤ |erra| + |errb| := abs_add erra errb
      _ ≤ (a.r : ℝ) + (b.r : ℝ) := by linarith
      _ = ((add a b).r : ℝ) := by rw [h3]
  · -- va + vb = evalLinear (add a b) eps + (erra + errb)
    simp only [evalLinear, add, linearSum_zipWithPad_add] at *
    rw [hva, hvb]
    push_cast
    ring

/-- Negation is sound -/
theorem mem_neg {a : AffineForm} {eps : NoiseAssignment} {va : ℝ}
    (ha : mem_affine a eps va) : mem_affine (neg a) eps (-va) := by
  obtain ⟨erra, herra_bound, hva⟩ := ha
  use -erra
  constructor
  · have h : ((neg a).r : ℝ) = (a.r : ℝ) := by simp only [neg]
    simp only [abs_neg, h]; exact herra_bound
  · simp only [evalLinear, neg, linearSum_map_neg, Rat.cast_neg]
    rw [hva]
    simp only [evalLinear]
    ring

/-- Subtraction is sound -/
theorem mem_sub {a b : AffineForm} {eps : NoiseAssignment} {va vb : ℝ}
    (ha : mem_affine a eps va) (hb : mem_affine b eps vb) :
    mem_affine (sub a b) eps (va - vb) := by
  simp only [sub, sub_eq_add_neg]
  exact mem_add ha (mem_neg hb)

/-! ### Bounding the linear sum -/

/-- Helper: foldl with abs is additive -/
private theorem sumAbs_foldl_add (l : List ℚ) (init : ℚ) :
    List.foldl (fun acc c => acc + |c|) init l = init + List.foldl (fun acc c => acc + |c|) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    have h1 := ih (init + |h|)
    have h2 := ih |h|
    calc List.foldl (fun acc c => acc + |c|) (init + |h|) t
        = init + |h| + List.foldl (fun acc c => acc + |c|) 0 t := by rw [h1]
      _ = init + (|h| + List.foldl (fun acc c => acc + |c|) 0 t) := by ring
      _ = init + List.foldl (fun acc c => acc + |c|) |h| t := by rw [← h2]
      _ = init + List.foldl (fun acc c => acc + |c|) (0 + |h|) t := by simp only [zero_add]

/-- Key lemma: |Σ cᵢ * εᵢ| ≤ Σ |cᵢ| when εᵢ ∈ [-1, 1] and lists have same length -/
private theorem linearSum_bounded_by_sumAbs (coeffs : List ℚ) (eps : NoiseAssignment)
    (hvalid : validNoise eps) (hlen : eps.length = coeffs.length) :
    |linearSum coeffs eps| ≤ sumAbs coeffs := by
  simp only [linearSum]
  induction coeffs generalizing eps with
  | nil =>
    simp only [List.zipWith, List.sum_nil, abs_zero]
    have h : sumAbs [] = 0 := by simp [sumAbs]
    simp only [h, Rat.cast_zero, le_refl]
  | cons c cs ih =>
    cases eps with
    | nil => simp at hlen
    | cons e es =>
      simp only [List.length_cons, Nat.succ_eq_add_one, add_left_inj] at hlen
      have hvalid_e : -1 ≤ e ∧ e ≤ 1 := hvalid e (by simp)
      have hvalid_es : validNoise es := fun x hx => hvalid x (List.mem_cons_of_mem e hx)
      simp only [List.zipWith, List.sum_cons]
      have ih_bound := ih es hvalid_es hlen
      have h_abs_e : |e| ≤ 1 := abs_le.mpr hvalid_e
      have h_ce : |(↑c : ℝ) * e| ≤ |(↑c : ℝ)| := by
        calc |(↑c : ℝ) * e| = |(↑c : ℝ)| * |e| := abs_mul _ _
          _ ≤ |(↑c : ℝ)| * 1 := by nlinarith [abs_nonneg (↑c : ℝ)]
          _ = |(↑c : ℝ)| := by ring
      have h_sumAbs_cons : (sumAbs (c :: cs) : ℝ) = (|c| : ℝ) + (sumAbs cs : ℝ) := by
        simp only [sumAbs, List.foldl_cons]
        rw [sumAbs_foldl_add]
        push_cast
        ring
      have h_abs_cast : |(↑c : ℝ)| = ((|c| : ℚ) : ℝ) := (Rat.cast_abs c).symm
      calc |↑c * e + (List.zipWith (fun c e => ↑c * e) cs es).sum|
          ≤ |↑c * e| + |(List.zipWith (fun c e => ↑c * e) cs es).sum| := abs_add _ _
        _ ≤ |(↑c : ℝ)| + (sumAbs cs : ℝ) := by linarith
        _ = ((|c| : ℚ) : ℝ) + (sumAbs cs : ℝ) := by rw [h_abs_cast]
        _ = (sumAbs (c :: cs) : ℝ) := by rw [h_sumAbs_cons, h_abs_cast]

/-! ### Multiplication Soundness Infrastructure -/

/-- The total deviation of v from c0 is bounded by deviationBound -/
private theorem deviation_from_center {af : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps) (hlen : eps.length = af.coeffs.length)
    (hmem : mem_affine af eps v) :
    |v - af.c0| ≤ af.deviationBound := by
  obtain ⟨err, herr, hv⟩ := hmem
  rw [hv]
  simp only [evalLinear]
  -- |c0 + linear + err - c0| = |linear + err|
  have heq : (af.c0 : ℝ) + linearSum af.coeffs eps + err - af.c0 = linearSum af.coeffs eps + err := by ring
  rw [heq]
  -- |linear + err| ≤ |linear| + |err| ≤ sumAbs + r = deviationBound
  have hlin := linearSum_bounded_by_sumAbs af.coeffs eps hvalid hlen
  simp only [deviationBound]
  calc |linearSum af.coeffs eps + err|
      ≤ |linearSum af.coeffs eps| + |err| := abs_add _ _
    _ ≤ (sumAbs af.coeffs : ℝ) + (af.r : ℝ) := by linarith
    _ = ((af.r + sumAbs af.coeffs : ℚ) : ℝ) := by push_cast; ring

/-- Helper: linearSum of zipWithPad with scaled coefficients -/
private theorem linearSum_zipWithPad_scale (cx cy : ℚ) (l1 l2 : List ℚ) (eps : NoiseAssignment) :
    linearSum (zipWithPad (fun ca cb => cx * cb + cy * ca) l1 l2) eps =
    (cx : ℝ) * linearSum l2 eps + (cy : ℝ) * linearSum l1 eps := by
  simp only [linearSum]
  induction l1 generalizing l2 eps with
  | nil =>
    induction l2 generalizing eps with
    | nil => simp [zipWithPad, List.zipWith]
    | cons h2 t2 ih2 =>
      cases eps with
      | nil => simp [zipWithPad, List.zipWith]
      | cons e es =>
        simp only [zipWithPad, List.zipWith, List.sum_cons, List.zipWith_nil_left, List.sum_nil, mul_zero, add_zero]
        rw [ih2 es]
        simp only [List.zipWith_nil_left, List.sum_nil, mul_zero, add_zero]
        push_cast
        ring
  | cons h1 t1 ih1 =>
    cases l2 with
    | nil =>
      cases eps with
      | nil => simp [zipWithPad, List.zipWith]
      | cons e es =>
        simp only [zipWithPad, List.zipWith, List.sum_cons, List.zipWith_nil_left, List.sum_nil, mul_zero, add_zero]
        have := ih1 [] es
        simp only [zipWithPad, List.zipWith, List.sum_nil, mul_zero, add_zero] at this
        rw [this]
        push_cast
        ring
    | cons h2 t2 =>
      cases eps with
      | nil => simp [zipWithPad, List.zipWith]
      | cons e es =>
        simp only [zipWithPad, List.zipWith, List.sum_cons]
        rw [ih1 t2 es]
        push_cast
        ring

/-- Helper: |linearSum coeffs eps| ≤ sumAbs coeffs (no length constraint) -/
private theorem linearSum_bounded_weak (coeffs : List ℚ) (eps : NoiseAssignment) (hvalid : validNoise eps) :
    |linearSum coeffs eps| ≤ sumAbs coeffs := by
  simp only [linearSum]
  induction coeffs generalizing eps with
  | nil => simp [List.zipWith, sumAbs]
  | cons c cs ih =>
    cases eps with
    | nil =>
      simp only [List.zipWith, List.sum_nil, abs_zero, sumAbs, List.foldl_cons, zero_add]
      exact_mod_cast list_foldl_abs_nonneg cs |c| (abs_nonneg c)
    | cons e es =>
      simp only [List.zipWith, List.sum_cons]
      have hvalid_es : validNoise es := fun x hx => hvalid x (List.mem_cons_of_mem e hx)
      have hvalid_e : -1 ≤ e ∧ e ≤ 1 := hvalid e (by simp)
      have h_abs_e : |e| ≤ 1 := abs_le.mpr hvalid_e
      have h_ce : |(↑c : ℝ) * e| ≤ |(↑c : ℝ)| := by
        calc |(↑c : ℝ) * e| = |(↑c : ℝ)| * |e| := abs_mul _ _
          _ ≤ |(↑c : ℝ)| * 1 := by nlinarith [abs_nonneg (↑c : ℝ)]
          _ = |(↑c : ℝ)| := by ring
      have ih_bound := ih es hvalid_es
      have h_sumAbs_cons : (sumAbs (c :: cs) : ℝ) = |(↑c : ℝ)| + (sumAbs cs : ℝ) := by
        simp only [sumAbs, List.foldl_cons]
        rw [sumAbs_foldl_add]
        push_cast
        rw [(Rat.cast_abs c).symm]
        ring
      calc |↑c * e + (List.zipWith (fun c e => ↑c * e) cs es).sum|
          ≤ |↑c * e| + |(List.zipWith (fun c e => ↑c * e) cs es).sum| := abs_add _ _
        _ ≤ |(↑c : ℝ)| + (sumAbs cs : ℝ) := by linarith
        _ = (sumAbs (c :: cs) : ℝ) := by rw [← h_sumAbs_cons]

/-- Multiplication is sound -/
theorem mem_mul {a b : AffineForm} {eps : NoiseAssignment} {va vb : ℝ}
    (hvalid : validNoise eps)
    (ha : mem_affine a eps va) (hb : mem_affine b eps vb) :
    mem_affine (mul a b) eps (va * vb) := by
  -- Unpack membership
  obtain ⟨ea, hea, heqa⟩ := ha
  obtain ⟨eb, heb, heqb⟩ := hb

  -- Define the deviations (linear + error)
  let La := linearSum a.coeffs eps
  let Lb := linearSum b.coeffs eps
  let Da := La + ea  -- total deviation of a from c0
  let Db := Lb + eb  -- total deviation of b from c0

  -- The new error term
  let err_new := (a.c0 : ℝ) * eb + (b.c0 : ℝ) * ea + Da * Db

  use err_new
  constructor

  -- Part 1: Bound |err_new| ≤ new_r
  · simp only [mul]
    have h1 : |(a.c0 : ℝ) * eb| ≤ |(a.c0 : ℝ)| * (b.r : ℝ) := by rw [abs_mul]; gcongr
    have h2 : |(b.c0 : ℝ) * ea| ≤ |(b.c0 : ℝ)| * (a.r : ℝ) := by rw [abs_mul]; gcongr
    have h3 : |Da * Db| = |Da| * |Db| := abs_mul Da Db

    -- Bound |Da| and |Db| by deviationBound
    have hLa_bound : |La| ≤ (sumAbs a.coeffs : ℝ) := linearSum_bounded_weak a.coeffs eps hvalid
    have hLb_bound : |Lb| ≤ (sumAbs b.coeffs : ℝ) := linearSum_bounded_weak b.coeffs eps hvalid

    have hDa_bound : |Da| ≤ (deviationBound a : ℝ) := by
      calc |Da| = |La + ea| := rfl
        _ ≤ |La| + |ea| := abs_add _ _
        _ ≤ (sumAbs a.coeffs : ℝ) + (a.r : ℝ) := by linarith
        _ = (deviationBound a : ℝ) := by simp [deviationBound]; ring

    have hDb_bound : |Db| ≤ (deviationBound b : ℝ) := by
      calc |Db| = |Lb + eb| := rfl
        _ ≤ |Lb| + |eb| := abs_add _ _
        _ ≤ (sumAbs b.coeffs : ℝ) + (b.r : ℝ) := by linarith
        _ = (deviationBound b : ℝ) := by simp [deviationBound]; ring

    -- Combine bounds
    have hDaDb : |Da * Db| ≤ (deviationBound a : ℝ) * (deviationBound b : ℝ) := by
      rw [h3]
      apply mul_le_mul hDa_bound hDb_bound (abs_nonneg _)
      exact_mod_cast deviationBound_nonneg a

    -- Final bound
    have hfinal : |err_new| ≤ |(a.c0 : ℝ)| * (b.r : ℝ) + |(b.c0 : ℝ)| * (a.r : ℝ) +
                            (deviationBound a : ℝ) * (deviationBound b : ℝ) := by
      calc |err_new|
          = |(a.c0 : ℝ) * eb + (b.c0 : ℝ) * ea + Da * Db| := rfl
        _ ≤ |(a.c0 : ℝ) * eb + (b.c0 : ℝ) * ea| + |Da * Db| := abs_add _ _
        _ ≤ |(a.c0 : ℝ) * eb| + |(b.c0 : ℝ) * ea| + |Da * Db| := by linarith [abs_add ((a.c0 : ℝ) * eb) ((b.c0 : ℝ) * ea)]
        _ ≤ |(a.c0 : ℝ)| * (b.r : ℝ) + |(b.c0 : ℝ)| * (a.r : ℝ) + (deviationBound a : ℝ) * (deviationBound b : ℝ) := by linarith
    -- Cast to match the goal
    calc |err_new|
        ≤ |(a.c0 : ℝ)| * (b.r : ℝ) + |(b.c0 : ℝ)| * (a.r : ℝ) + (deviationBound a : ℝ) * (deviationBound b : ℝ) := hfinal
      _ = ((|a.c0| * b.r + |b.c0| * a.r + deviationBound a * deviationBound b : ℚ) : ℝ) := by
          simp only [deviationBound]; push_cast; rw [(Rat.cast_abs a.c0).symm, (Rat.cast_abs b.c0).symm]

  -- Part 2: Show va * vb = evalLinear (mul a b) eps + err_new
  · simp only [evalLinear, mul, linearSum_zipWithPad_scale]
    simp only [evalLinear] at heqa heqb
    rw [heqa, heqb]
    -- Algebra: (ca + La + ea) * (cb + Lb + eb) = ca*cb + (ca*Lb + cb*La) + (ca*eb + cb*ea + (La+ea)*(Lb+eb))
    push_cast
    ring

/-- Squaring is sound: if v is represented by a, then v*v is represented by sq a -/
theorem mem_sq {a : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps)
    (hmem : mem_affine a eps v) :
    mem_affine (sq a) eps (v * v) := by
  -- The sq operation is an optimized version of mul a a
  -- The proof follows the same pattern as mem_mul but with a = b
  obtain ⟨ea, hea, heqa⟩ := hmem

  let La := linearSum a.coeffs eps
  let Da := La + ea

  -- The new error term for sq
  let err_new := 2 * (a.c0 : ℝ) * ea + Da * Da

  use err_new
  constructor

  -- Part 1: Bound |err_new| ≤ new_r
  · simp only [sq]
    have h1 : |2 * (a.c0 : ℝ) * ea| ≤ 2 * |(a.c0 : ℝ)| * (a.r : ℝ) := by
      calc |2 * (a.c0 : ℝ) * ea|
          = |2| * |(a.c0 : ℝ)| * |ea| := by rw [abs_mul, abs_mul]
        _ = 2 * |(a.c0 : ℝ)| * |ea| := by norm_num
        _ ≤ 2 * |(a.c0 : ℝ)| * (a.r : ℝ) := by
            have h := abs_nonneg (a.c0 : ℝ)
            nlinarith [hea]
    have h2 : |Da * Da| = |Da| * |Da| := abs_mul Da Da

    have hLa_bound : |La| ≤ (sumAbs a.coeffs : ℝ) := linearSum_bounded_weak a.coeffs eps hvalid

    have hDa_bound : |Da| ≤ (deviationBound a : ℝ) := by
      calc |Da| = |La + ea| := rfl
        _ ≤ |La| + |ea| := abs_add _ _
        _ ≤ (sumAbs a.coeffs : ℝ) + (a.r : ℝ) := by linarith
        _ = (deviationBound a : ℝ) := by simp [deviationBound]; ring

    have hDaDa : |Da * Da| ≤ (deviationBound a : ℝ) * (deviationBound a : ℝ) := by
      rw [h2]
      apply mul_le_mul hDa_bound hDa_bound (abs_nonneg _)
      exact_mod_cast deviationBound_nonneg a

    have hfinal : |err_new| ≤ 2 * |(a.c0 : ℝ)| * (a.r : ℝ) +
                            (deviationBound a : ℝ) * (deviationBound a : ℝ) := by
      calc |err_new|
          = |2 * (a.c0 : ℝ) * ea + Da * Da| := rfl
        _ ≤ |2 * (a.c0 : ℝ) * ea| + |Da * Da| := abs_add _ _
        _ ≤ 2 * |(a.c0 : ℝ)| * (a.r : ℝ) + (deviationBound a : ℝ) * (deviationBound a : ℝ) := by linarith

    calc |err_new|
        ≤ 2 * |(a.c0 : ℝ)| * (a.r : ℝ) + (deviationBound a : ℝ) * (deviationBound a : ℝ) := hfinal
      _ = ((2 * |a.c0| * a.r + deviationBound a * deviationBound a : ℚ) : ℝ) := by
          simp only [deviationBound]; push_cast; rw [(Rat.cast_abs a.c0).symm]

  -- Part 2: Show v * v = evalLinear (sq a) eps + err_new
  · simp only [evalLinear, sq]
    simp only [evalLinear] at heqa
    rw [heqa]
    -- Algebra: (ca + La + ea)^2 = ca^2 + 2*ca*(La + ea) + (La + ea)^2
    --        = ca^2 + 2*ca*La + 2*ca*ea + (La + ea)^2
    -- linearSum of scaled coefficients = scaled linearSum
    simp only [linearSum_map_mul]
    push_cast
    ring

/-- If v is represented by af, then v ∈ toInterval af -/
theorem mem_toInterval {af : AffineForm} {eps : NoiseAssignment} {v : ℝ}
    (hvalid : validNoise eps)
    (hlen : eps.length = af.coeffs.length)
    (hmem : mem_affine af eps v) :
    v ∈ af.toInterval := by
  obtain ⟨err, herr_bound, hv⟩ := hmem
  simp only [toInterval, IntervalRat.mem_def]
  simp only [evalLinear] at hv
  rw [hv]
  have hlin_bound := linearSum_bounded_by_sumAbs af.coeffs eps hvalid hlen
  have herr_abs : |err| ≤ (af.r : ℝ) := herr_bound
  have hlin_abs : |linearSum af.coeffs eps| ≤ (sumAbs af.coeffs : ℝ) := hlin_bound
  -- Need: c0 - deviationBound ≤ c0 + linear + err ≤ c0 + deviationBound
  -- From |linear| ≤ sumAbs we get -sumAbs ≤ linear ≤ sumAbs
  -- From |err| ≤ r we get -r ≤ err ≤ r
  simp only [deviationBound]
  have h_lin_lo : -(sumAbs af.coeffs : ℝ) ≤ linearSum af.coeffs eps := by
    have := abs_nonneg (linearSum af.coeffs eps)
    linarith [neg_abs_le (linearSum af.coeffs eps)]
  have h_lin_hi : linearSum af.coeffs eps ≤ (sumAbs af.coeffs : ℝ) := by
    linarith [le_abs_self (linearSum af.coeffs eps)]
  have h_err_lo : -(af.r : ℝ) ≤ err := by
    linarith [neg_abs_le err]
  have h_err_hi : err ≤ (af.r : ℝ) := by
    linarith [le_abs_self err]
  constructor
  · -- Lower bound: c0 - (r + sumAbs) ≤ c0 + linear + err
    have hcast : ((af.c0 - (af.r + sumAbs af.coeffs)) : ℚ) = af.c0 - af.r - sumAbs af.coeffs := by ring
    calc (((af.c0 - (af.r + sumAbs af.coeffs)) : ℚ) : ℝ)
        = (af.c0 : ℝ) - (af.r : ℝ) - (sumAbs af.coeffs : ℝ) := by push_cast; ring
      _ ≤ (af.c0 : ℝ) + linearSum af.coeffs eps + err := by linarith
  · -- Upper bound: c0 + linear + err ≤ c0 + (r + sumAbs)
    calc (af.c0 : ℝ) + linearSum af.coeffs eps + err
        ≤ (af.c0 : ℝ) + (af.r : ℝ) + (sumAbs af.coeffs : ℝ) := by linarith
      _ = (((af.c0 + (af.r + sumAbs af.coeffs)) : ℚ) : ℝ) := by push_cast; ring

end AffineForm

end LeanBound.Numerics.Affine
