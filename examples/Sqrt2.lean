import LeanCert

/-!
# Problem 1: The Classic - Prove √2 Exists and is Unique

Domain: Real analysis / Number theory
Why it matters: Foundation of irrational numbers, historical significance
-/

open LeanCert.Core LeanCert.Validity

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

/-! ## Part A: Existence via Sign Change (IVT) -/

-- f(x) = x² - 2 changes sign on [1, 2]: f(1) = -1 < 0, f(2) = 2 > 0
-- Therefore by IVT, ∃ x ∈ [1, 2] with x² = 2

theorem sqrt2_exists : ∃ x ∈ I12,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

-- Native syntax version (using certify approach)
theorem sqrt2_exists_native : ∃ x ∈ Set.Icc (1:ℝ) 2, x * x - 2 = 0 := by
  interval_roots

/-! ## Part B: Uniqueness via Newton Contraction -/

-- f'(x) = 2x ≠ 0 on [1, 2] (since x ≥ 1 > 0)
-- Newton iteration contracts, so the root is unique

theorem sqrt2_unique : ∃! x, x ∈ I12 ∧
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) = 0 := by
  interval_unique_root

-- Native syntax version
theorem sqrt2_unique_native : ∃! x, x ∈ Set.Icc (1:ℝ) 2 ∧ x * x - 2 = 0 := by
  interval_unique_root

/-! ## Part C: Precise Bounds -/

-- We can show √2 ∈ [1.41, 1.42] by showing:
-- 1. f(1.41) = 1.41² - 2 ≈ -0.0119 < 0
-- 2. f(1.42) = 1.42² - 2 ≈ 0.0164 > 0

def I_sqrt2_tight : IntervalRat := ⟨141/100, 142/100, by norm_num⟩

-- Sign change on tighter interval proves √2 ∈ [1.41, 1.42]
theorem sqrt2_in_tight_interval : ∃ x ∈ I_sqrt2_tight,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

-- Even tighter: √2 ∈ [1.414, 1.415]
def I_sqrt2_tighter : IntervalRat := ⟨1414/1000, 1415/1000, by norm_num⟩

theorem sqrt2_in_tighter_interval : ∃ x ∈ I_sqrt2_tighter,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

-- 9 decimal places: √2 ∈ [1.414213562, 1.414213563]
def I_sqrt2_9decimals : IntervalRat := ⟨1414213562/1000000000, 1414213563/1000000000, by norm_num⟩

theorem sqrt2_9_decimals : ∃ x ∈ I_sqrt2_9decimals,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                                     (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

/-! ## Part D: Discovery Commands -/

-- Check bounds interactively
#bounds (fun x => x * x - 2) on [1, 2]

-- Find minimum and maximum
#find_min (fun x => x * x - 2) on [1, 2]
#find_max (fun x => x * x - 2) on [1, 2]

/-! ## Summary: √2 Problem Solved ✓

All three parts work:
- Part A (Existence): interval_roots via IVT
- Part B (Uniqueness): interval_unique_root via Newton contraction
- Part C (Bounds): Arbitrarily tight via smaller intervals
-/
