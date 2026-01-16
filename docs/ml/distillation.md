# Model Distillation Verification

LeanCert allows you to formally verify that a compressed "Student" model behaves identically (within a tolerance ε) to a large "Teacher" model.

## The Problem

When deploying AI, we often compress large models via distillation, pruning, or quantization. How do we know the compressed model is safe? Testing on a dataset isn't enough—it leaves gaps where untested inputs could produce dangerous outputs.

## The Solution: Formal Equivalence

We verify that:

\\[
\forall x \in \text{Domain}, \quad |\text{Teacher}(x) - \text{Student}(x)| \le \epsilon
\\]

This provides a **guarantee** that holds for all possible inputs, not just test samples.

## Usage

```lean
import LeanCert.ML.Distillation

open LeanCert.ML.Distillation

-- 1. Define input domain (e.g., [0, 1]²)
def domain := [IntervalDyadic.ofRat 0 1, IntervalDyadic.ofRat 0 1]

-- 2. Define tolerance
def epsilon : ℚ := 0.01

-- 3. Verify equivalence
theorem model_equivalence :
    verify_equivalence teacherNet studentNet domain epsilon := by
  native_decide
```

## How it Works

The verifier computes interval bounds for the **difference graph** D(x) = T(x) - S(x). By computing the difference directly, interval arithmetic can cancel out correlated terms (like shared inputs), resulting in much tighter bounds than bounding T(x) and S(x) separately.

### Difference Graph Approach

```
Standard approach (loose):
  |T(x) - S(x)| ≤ |T(x)| + |S(x)| ≤ wide bound

Difference graph approach (tight):
  D(x) = T(x) - S(x)
  |D(x)| ≤ tight bound (cancellation exploited)
```

## Verification Workflow

1. **Define networks**: Specify Teacher and Student as `Layer` lists
2. **Define domain**: Input intervals representing valid inputs
3. **Set tolerance**: Maximum acceptable output difference ε
4. **Run verification**: LeanCert propagates intervals through the difference graph
5. **Get proof**: If successful, produces a formal Lean theorem

## Example: Pruned Classifier

```lean
-- Teacher: Full 3-layer network
def teacher : List Layer := [layer1, layer2, layer3]

-- Student: Pruned version with zeroed weights
def student : List Layer := [layer1_pruned, layer2_pruned, layer3_pruned]

-- Verify pruning didn't change outputs by more than 0.1
theorem pruning_safe :
    ∀ x ∈ inputDomain, |teacher.forward x - student.forward x| ≤ 0.1 :=
  verify_equivalence teacher student inputDomain 0.1
```

## Limitations

- **Scalability**: Very deep networks or wide input domains may require subdivision
- **Tolerance**: The verifier may fail if ε is too tight (increase ε or refine the domain)
- **Architecture**: Both networks must have compatible input/output dimensions

## Files

| File | Description |
|------|-------------|
| `ML/Distillation.lean` | Core verification algorithm |
| `Examples/ML/Distillation.lean` | Example usage |
