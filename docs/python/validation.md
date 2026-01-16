# Bug Validation Framework

LeanCert includes a validation framework to filter false positives from counter-example searches.

## The Problem

Static analysis and interval arithmetic can report "violations" that aren't real bugs:

- **Interval explosion**: Wide bounds due to the dependency problem
- **Precision artifacts**: Floating-point rounding in the checker
- **Intentional behavior**: Code that's designed to handle edge cases

The validation framework helps distinguish real bugs from false alarms.

## Quick Example

```python
import leancert as lc
from leancert.validation import BugValidator

# Expression that might have issues
x = lf.var('x')
expr = 1 / (x - 1)  # Singularity at x = 1

# Find potential violations
result = lf.find_bounds(expr, {'x': (0.5, 1.5)})

# Validate if the "unbounded" result is a real issue
validator = BugValidator()
verdict = validator.validate(
    expr=expr,
    domain={'x': (0.5, 1.5)},
    reported_issue="unbounded output"
)

print(verdict)
# ValidationVerdict(
#   is_real_bug=True,
#   confidence=0.95,
#   reason="Singularity at x=1 within domain"
# )
```

## Components

### `BugValidator`

Main entry point for validation.

```python
from leancert.validation import BugValidator

validator = BugValidator()
verdict = validator.validate(expr, domain, reported_issue)
```

### `IntervalExplosionDetector`

Detects if bounds blew up due to interval arithmetic limitations, not actual unboundedness.

```python
from leancert.validation import IntervalExplosionDetector

detector = IntervalExplosionDetector()

# Check if wide bounds are due to dependency problem
is_explosion = detector.detect(
    expr=x * x - x * x,  # Should be 0, but interval gives [-1, 1] on [-1, 1]
    domain={'x': (-1, 1)}
)
# Returns True - this is interval explosion, not a real issue
```

**Common explosion patterns:**
- `x - x` → should be 0, interval gives wide bounds
- `x * (1/x)` → should be 1, interval gives wide bounds
- Correlated variables in LayerNorm

### `CounterexampleVerifier`

Concretely evaluates the expression at reported counter-example points.

```python
from leancert.validation import CounterexampleVerifier

verifier = CounterexampleVerifier()

# Check if counter-example is real
is_real = verifier.verify(
    expr=x**2,
    point={'x': 2.0},
    claimed_bound=3.0,
    bound_type='upper'
)
# Returns True - x²=4 really does exceed 3
```

### `CommentAnalyzer`

Checks code context for indicators that behavior is intentional.

```python
from leancert.validation import CommentAnalyzer

analyzer = CommentAnalyzer()

code_context = """
# NOTE: This can return infinity for x near 0
# This is expected behavior - caller handles it
def f(x):
    return 1/x
"""

is_intentional = analyzer.is_intentional(code_context)
# Returns True - comment indicates intentional behavior
```

**Detected patterns:**
- `# expected`, `# intentional`, `# by design`
- `# TODO: handle edge case`
- `# FIXME` (indicates known issue)

## ValidationVerdict

Result of validation:

```python
@dataclass
class ValidationVerdict:
    is_real_bug: bool          # True if this is likely a real issue
    confidence: float          # 0.0 to 1.0
    reason: str                # Human-readable explanation
    suggested_fix: str | None  # Optional fix suggestion
```

## Validation Pipeline

The `BugValidator` runs multiple checks:

```
Reported Issue
      │
      ▼
┌─────────────────┐
│ Interval        │──▶ If explosion detected,
│ Explosion Check │    likely false positive
└─────────────────┘
      │
      ▼
┌─────────────────┐
│ Counterexample  │──▶ Concrete evaluation
│ Verification    │    confirms or refutes
└─────────────────┘
      │
      ▼
┌─────────────────┐
│ Comment         │──▶ Check for intentional
│ Analysis        │    behavior markers
└─────────────────┘
      │
      ▼
   Verdict
```

## Configuration

```python
validator = BugValidator(
    concrete_samples=100,      # Points to sample for verification
    explosion_threshold=1e10,  # Bound magnitude indicating explosion
    confidence_threshold=0.8   # Min confidence to report as bug
)
```

## Integration with CI

```python
import leancert as lc
from leancert.validation import BugValidator

def check_module(module_path):
    """Check a module for real bugs, filtering false positives."""
    validator = BugValidator()
    real_bugs = []

    # Run interval analysis
    results = lf.analyze_file(module_path)

    for issue in results.potential_issues:
        verdict = validator.validate(
            expr=issue.expr,
            domain=issue.domain,
            reported_issue=issue.description
        )

        if verdict.is_real_bug and verdict.confidence > 0.8:
            real_bugs.append(issue)

    return real_bugs

# In CI pipeline
bugs = check_module("src/math_utils.py")
if bugs:
    print(f"Found {len(bugs)} real bugs")
    sys.exit(1)
```

## BugReport

Structured bug report for integration:

```python
@dataclass
class BugReport:
    location: str              # File and line
    expr: Expr                 # Expression with issue
    domain: dict               # Input domain
    issue_type: str            # "overflow", "division_by_zero", etc.
    counterexample: dict       # Concrete input triggering issue
    confidence: float

    def to_json(self) -> str: ...
    def to_github_annotation(self) -> str: ...
```

## Example: Filtering False Positives

```python
import leancert as lc
from leancert.validation import BugValidator

x = lf.var('x')

# False positive: interval explosion
expr1 = (x + 1) * (x - 1) - (x*x - 1)  # Algebraically 0
result1 = lf.find_bounds(expr1, {'x': (-10, 10)})
# Interval says [-400, 400] but it's actually always 0

validator = BugValidator()
verdict1 = validator.validate(expr1, {'x': (-10, 10)}, "large bounds")
# verdict1.is_real_bug = False (detected as interval explosion)

# Real bug: division by zero possible
expr2 = 1 / x
result2 = lf.find_bounds(expr2, {'x': (-1, 1)})

verdict2 = validator.validate(expr2, {'x': (-1, 1)}, "unbounded")
# verdict2.is_real_bug = True (x=0 causes real issue)
```
