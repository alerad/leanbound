# LeanBound v2 SDK
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
LeanBound v2 Python SDK - Rigorous Numerical Verification.

This SDK provides a user-friendly interface to the LeanBound verification engine,
allowing you to compute rigorous bounds, find roots, and verify mathematical
properties with machine-checked proofs.

Example:
    >>> import leanbound_v2 as lf
    >>> x = lf.var('x')
    >>> result = lf.find_bounds(x**2, {'x': (0, 1)})
    >>> print(result.min_bound)  # Contains 0
    >>> print(result.max_bound)  # Contains 1

Key Features:
    - Named symbolic variables (no De Bruijn indices)
    - Automatic domain inference
    - Rich result objects with certificates
    - Context manager support for resource management
"""

__version__ = "0.2.0"

# Core expression types and constructors
from .expr import (
    Expr,
    Variable,
    Const,
    var,
    const,
    sin,
    cos,
    exp,
    log,
    sqrt,
    tan,
    atan,
    abs,
    # New functions
    inv,
    sinh,
    cosh,
    tanh,
    arsinh,
    atanh,
    # Special functions
    sinc,
    erf,
    # Min/Max/Clamp
    Min,
    Max,
    clamp,
)

# Domain types
from .domain import (
    Interval,
    Box,
    normalize_domain,
)

# Rational utilities
from .rational import to_fraction

# Configuration
from .config import Config

# Result types
from .result import (
    BoundsResult,
    RootsResult,
    RootInterval,
    IntegralResult,
    Certificate,
    UniqueRootResult,
    VerifyResult,
)

# Solver
from .solver import (
    Solver,
    find_bounds,
    verify_bound,
    find_roots,
    find_unique_root,
    integrate,
)

# Client (for advanced users)
from .client import LeanClient

# Simplification utilities
from .simplify import simplify, expand

# Exceptions
from .exceptions import (
    LeanBoundError,
    CompilationError,
    DomainError,
    VerificationFailed,
    VerificationTimeout,
    BridgeError,
    ExpressionError,
    UnsupportedExpressionError,
    PartialFunctionError,
    SUPPORTED_KINDS,
    PARTIAL_FUNCTIONS,
)

# Neural network export
from . import nn

# Bug validation and false positive filtering
from .validation import (
    ValidationVerdict,
    ValidationResult,
    IntervalExplosionDetector,
    CommentAnalyzer,
    CounterexampleVerifier,
    BugValidator,
    BugReport,
    detect_interval_explosion,
    is_intentional_behavior,
    verify_counterexample_concrete,
)

__all__ = [
    # Version
    "__version__",
    # Expression types
    "Expr",
    "Variable",
    "Const",
    # Expression constructors
    "var",
    "const",
    "sin",
    "cos",
    "exp",
    "log",
    "sqrt",
    "tan",
    "atan",
    "abs",
    # New functions
    "inv",
    "sinh",
    "cosh",
    "tanh",
    "arsinh",
    "atanh",
    # Special functions
    "sinc",
    "erf",
    # Min/Max/Clamp
    "Min",
    "Max",
    "clamp",
    # Domain types
    "Interval",
    "Box",
    "normalize_domain",
    # Rational utilities
    "to_fraction",
    # Configuration
    "Config",
    # Result types
    "BoundsResult",
    "RootsResult",
    "RootInterval",
    "IntegralResult",
    "Certificate",
    "UniqueRootResult",
    "VerifyResult",
    # Solver
    "Solver",
    "find_bounds",
    "verify_bound",
    "find_roots",
    "find_unique_root",
    "integrate",
    # Client
    "LeanClient",
    # Simplification
    "simplify",
    "expand",
    # Exceptions
    "LeanBoundError",
    "CompilationError",
    "DomainError",
    "VerificationFailed",
    "VerificationTimeout",
    "BridgeError",
    "ExpressionError",
    "UnsupportedExpressionError",
    "PartialFunctionError",
    "SUPPORTED_KINDS",
    "PARTIAL_FUNCTIONS",
    # Bug validation
    "ValidationVerdict",
    "ValidationResult",
    "IntervalExplosionDetector",
    "CommentAnalyzer",
    "CounterexampleVerifier",
    "BugValidator",
    "BugReport",
    "detect_interval_explosion",
    "is_intentional_behavior",
    "verify_counterexample_concrete",
    # Neural network export
    "nn",
]
