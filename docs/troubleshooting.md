# Troubleshooting Guide

Common issues and how to fix them.

## Tactic Failures

### "native_decide evaluated that the proposition is false"

```
error: Tactic `native_decide` evaluated that the proposition
  checkUpperBound ... = true
is false
```

**Cause:** The bound you're trying to prove is too tight for the current Taylor depth.

**Solutions:**

1. **Increase Taylor depth:**
   ```lean
   -- Instead of
   example : ∀ x ∈ I, Real.exp x ≤ 2.72 := by certify_bound

   -- Try
   example : ∀ x ∈ I, Real.exp x ≤ 2.72 := by certify_bound 20
   ```

2. **Use a looser bound:**
   ```lean
   -- exp(1) ≈ 2.718, so 2.72 may be too tight
   -- Try 2.75 or 3 instead
   example : ∀ x ∈ I, Real.exp x ≤ 3 := by certify_bound
   ```

3. **Use subdivision for tight bounds:**
   ```lean
   example : ∀ x ∈ I, Real.exp x ≤ 2.72 := by interval_bound_subdiv 15 3
   ```

4. **Check if the bound is actually true:**
   ```lean
   -- Use discovery to see what bounds actually hold
   #bounds (fun x => Real.exp x) on [0, 1]
   ```

---

### "could not unify ... Expr.eval ... with the goal"

```
error: Tactic `apply` failed: could not unify the conclusion of the term
  ∀ x ∈ I, Expr.eval (fun x_1 => x) (...) ≤ ↑c
with the goal
  ∀ x ∈ I, <your expression> ≤ ↑c
```

**Cause:** The tactic reified your expression to an `Expr` AST, but it doesn't match the goal syntactically.

> **Note:** As of v1.2, most cases are now handled automatically. Expressions with numeric coefficients like `2 * x * x + 3 * x + 1` should work out of the box. If you still encounter this error, try the solutions below.

**This may still happen with:**
- Very complex nested coefficient expressions
- Custom definitions that aren't unfolded
- Unusual type coercions

**Solutions:**

1. **First, just try it** - most expressions now work:
   ```lean
   -- These all work now:
   example : ∀ x ∈ I, 2 * x * x + 3 * x + 1 ≤ 6 := by certify_bound  -- ✓
   example : ∀ x ∈ I, x * x - x + 1 ≤ 2 := by certify_bound           -- ✓
   example : ∀ x ∈ I, 2 * Real.sin x + x * x ≤ 3 := by certify_bound  -- ✓
   ```

2. **If it still fails, build the Expr AST explicitly:**
   ```lean
   open LeanCert.Core

   def myExpr : Expr := Expr.add
     (Expr.mul (Expr.const 2) (Expr.mul (Expr.var 0) (Expr.var 0)))
     (Expr.const 1)

   def myExpr_core : ExprSupportedCore myExpr := ...

   example : ∀ x ∈ I, Expr.eval (fun _ => x) myExpr ≤ 5 := by
     interval_le myExpr, myExpr_core, I, 5
   ```

3. **Use the low-level tactics with explicit arguments:**
   ```lean
   example : ∀ x ∈ I01, Expr.eval (fun _ => x) quadExpr ≤ (5 : ℚ) := by
     interval_le quadExpr, quadExpr_core, I01, 5
   ```

---

### "unsolved goals" with multivariate bounds

```
error: unsolved goals
x✝ : ℝ
a✝ : x✝ ∈ I01
⊢ ∀ (y : ℝ), ↑I01.lo ≤ y → y ≤ ↑I01.hi → x✝ + y ≤ 2
```

**Cause:** You used `certify_bound` for a multivariate goal, but it only handles single-variable bounds.

**Solution:** Use `multivariate_bound`:
```lean
-- Instead of
example : ∀ x ∈ I, ∀ y ∈ J, x + y ≤ 2 := by certify_bound  -- Fails

-- Use
example : ∀ x ∈ I, ∀ y ∈ J, x + y ≤ 2 := by multivariate_bound
```

---

### "Cannot parse as integer: 3.14159"

```
error: Cannot parse as integer: 3.14159
```

**Cause:** Discovery commands only accept integer bounds, not floats.

**Solution:** Use rational approximations:
```lean
-- Instead of
#bounds (fun x => Real.sin x) on [0, 3.14159]  -- Fails

-- Use integers
#bounds (fun x => Real.sin x) on [0, 4]

-- Or define a rational interval for tactics
def I_0_pi : IntervalRat := ⟨0, 314159/100000, by norm_num⟩
```

---

## Warning Messages

### "Optimization gap exceeds tolerance"

```
warning: ⚠️ Optimization gap [-0.17, 0] exceeds tolerance 1/1000.
Consider increasing maxIterations or taylorDepth.
```

**Cause:** The branch-and-bound algorithm didn't converge to the requested precision, but the proof still succeeded because the discovered bound is valid.

**When to worry:** Only if you need tighter bounds. The proof is still correct.

**Solutions:**
```lean
-- Increase Taylor depth
example : ∃ m, ∀ x ∈ I, f x ≥ m := by interval_minimize 20

-- Or just accept slightly looser bounds (the proof is still valid)
```

---

## Expression Support

### What works with raw Lean syntax?

**Works well:**
```lean
-- Basic arithmetic
x * x + 1
x * x * x  -- (not x^3)

-- Simple coefficients
x * x + x + 1

-- Transcendentals
Real.sin x
Real.cos x
Real.exp x
Real.sin x + Real.cos x
Real.exp (Real.sin x)
```

**May have issues:**
```lean
-- Numeric coefficients (type inference)
2 * x * x + 3 * x  -- Sometimes fails

-- Power notation
x^3  -- May not reify correctly for some tactics

-- Complex nested coefficients
(2/3) * x * Real.sin x
```

### What requires Expr AST syntax?

**Always use Expr AST for:**
- `interval_roots` (root existence)
- `root_bound` (root absence)
- Low-level tactics (`interval_le`, `interval_ge`, etc.)

**Example:**
```lean
open LeanCert.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

-- Root existence requires Expr AST
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
              (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

---

## Precision and Taylor Depth

### When to increase Taylor depth

| Situation | Recommended Depth |
|-----------|-------------------|
| Polynomials only | 10 (default) |
| Single transcendental (`sin x`, `exp x`) | 10-15 |
| Composed transcendentals (`exp(sin x)`) | 15-20 |
| Tight bounds (within 1% of true value) | 20-30 |
| Very tight bounds | Use `interval_bound_subdiv` |

### When to use `fast_bound` (dyadic)

Use the dyadic backend when:
- Deeply nested expressions: `sin(cos(sin(x)))`
- Many operations: `x₁ + x₂ + ... + x₁₀₀`
- Proofs with rational backend timeout or are slow

```lean
-- Dyadic handles nesting well
example : ∀ x ∈ I, Real.cos (Real.sin (Real.cos x)) ≤ 1 := by fast_bound

-- Equivalent but may be slower/fail with many terms
example : ∀ x ∈ I, Real.cos (Real.sin (Real.cos x)) ≤ 1 := by certify_bound
```

---

## Debugging Tips

### Enable tracing

```lean
set_option trace.certify_bound true in
example : ∀ x ∈ I, f x ≤ c := by certify_bound

set_option trace.certify_kernel true in
example : ∀ x ∈ I, f x ≤ c := by certify_kernel
```

### Use discovery to check bounds

Before writing a theorem, verify the bound holds:
```lean
-- See what bounds actually hold
#bounds (fun x => your_expression) on [lo, hi]

-- Then prove with margin
-- If #bounds says max ≈ 2.72, prove ≤ 3
```

### Use `interval_refute` to check false bounds

```lean
-- Is this bound even true?
example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3 := by
  interval_refute  -- Finds counterexample at x = ±2

-- The bound is false! x² = 4 > 3 at endpoints
```

---

## Common Patterns

### Discovery → Proof workflow

```lean
-- Step 1: Explore
#bounds (fun x => Real.exp x + Real.sin x) on [0, 1]
-- Output: f(x) ∈ [1, 3.56]

-- Step 2: Pick safe bounds (with margin)
-- Discovery says max ≈ 3.56, so prove ≤ 4

-- Step 3: Prove
example : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x + Real.sin x ≤ 4 := by
  certify_bound 15
```

### Let LeanCert find bounds for you

```lean
-- Don't know what bound to use? Let LeanCert discover it:
example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x ≤ M := by
  interval_maximize 15
-- LeanCert finds M and proves it!
```
