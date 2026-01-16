# Expressions and Domains

## Building Expressions

LeanCert uses symbolic expressions that are reified to the Lean AST.

### Variables

```python
import leancert as lc

x = lf.var('x')
y = lf.var('y')
```

### Constants

```python
c = lf.const(3.14159)
half = lf.const(1, 2)  # Fraction 1/2
```

### Arithmetic

```python
expr = x**2 + 2*x + 1
expr = (x + y) / (x - y)
```

### Transcendental Functions

```python
lf.sin(x)
lf.cos(x)
lf.exp(x)
lf.log(x)
lf.tan(x)
lf.atan(x)
lf.sinh(x)
lf.cosh(x)
lf.tanh(x)
lf.arsinh(x)
lf.atanh(x)
```

### Special Functions

```python
lf.sinc(x)  # sin(x)/x with sinc(0) = 1
lf.erf(x)   # Error function
```

### Min/Max/Clamp

```python
lf.Min(x, y)
lf.Max(x, y)
lf.clamp(x, lo, hi)  # Equivalent to Min(Max(x, lo), hi)
```

## Domain Specification

### Intervals

```python
from leancert import Interval

I = Interval(0, 1)       # [0, 1]
I = Interval(-1, 1)      # [-1, 1]
I = Interval("1/3", 1)   # [1/3, 1] (exact rational)
```

### Boxes (Multi-dimensional)

```python
from leancert import Box

# Using a dictionary
box = Box({'x': (0, 1), 'y': (-1, 1)})

# Or pass directly to solver functions
result = lf.find_bounds(x + y, {'x': (0, 1), 'y': (0, 1)})
```

## Simplification

LeanCert includes symbolic simplification to mitigate the dependency problem in interval arithmetic.

::: leancert.simplify.simplify

::: leancert.simplify.expand

### Example

```python
x = lf.var('x')

# Without simplification, (x*100 + 5) - (x*100) on [0, 1e10]
# would give bounds like [-1e12, 1e12] due to dependency

# With simplification, it reduces to 5
expr = (x * 100 + 5) - (x * 100)
simplified = lf.simplify(expr)
# simplified is const(5)
```

## Expression Reference

::: leancert.expr.Expr
    options:
      show_root_heading: true
      members:
        - free_vars
        - substitute

::: leancert.expr.var

::: leancert.expr.const
