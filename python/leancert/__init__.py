# LeanCert v2 SDK
# Copyright (c) 2024 LeanCert Contributors. All rights reserved.

"""
LeanCert Python SDK - Rigorous Numerical Verification.

This SDK provides a user-friendly interface to the LeanCert verification engine,
allowing you to compute rigorous bounds, find roots, and verify mathematical
properties with machine-checked proofs.

Example:
    >>> import leancert_v2 as lf
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

__version__ = "0.3.0"

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
from .config import Config, Backend, DyadicConfig, AffineConfig

# Result types
from .result import (
    BoundsResult,
    RootsResult,
    RootInterval,
    IntegralResult,
    Certificate,
    UniqueRootResult,
    VerifyResult,
    LipschitzResult,
)

# Adaptive verification (CEGAR)
from .adaptive import (
    AdaptiveResult,
    AdaptiveConfig,
    SplitStrategy,
    Subdomain,
    SubdomainResult,
    SplitCandidate,
    AlgebraicAnalyzer,
    verify_bound_adaptive,
)

# Quantifier pattern synthesis
from .quantifier import (
    QuantifierPattern,
    QuantifierResult,
    QuantifierSynthesizer,
    Witness,
    synthesize_bound,
    synthesize_minimum,
    synthesize_maximum,
    prove_limit,
    prove_sign,
)

# Solver
from .solver import (
    Solver,
    find_bounds,
    verify_bound,
    find_roots,
    find_unique_root,
    integrate,
    eval_interval,
    forward_interval,
    verify_nn_bounds,
)

# Client (for advanced users)
from .client import LeanClient

# Simplification utilities
from .simplify import simplify, expand

# Exceptions
from .exceptions import (
    LeanCertError,
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
from .nn import (
    # Core network types
    Layer,
    TwoLayerReLUNetwork,
    SequentialNetwork,
    from_pytorch,
    from_pytorch_sequential,
    # Transformer components
    LayerNormParams,
    LinearLayer,
    FFNBlock,
    TransformerBlock,
    TransformerEncoder,
    from_pytorch_transformer,
)

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
    "Backend",
    "DyadicConfig",
    "AffineConfig",
    # Result types
    "BoundsResult",
    "RootsResult",
    "RootInterval",
    "IntegralResult",
    "Certificate",
    "UniqueRootResult",
    "VerifyResult",
    # Adaptive verification (CEGAR)
    "AdaptiveResult",
    "AdaptiveConfig",
    "SplitStrategy",
    "Subdomain",
    "SubdomainResult",
    "verify_bound_adaptive",
    # Solver
    "Solver",
    "find_bounds",
    "verify_bound",
    "find_roots",
    "find_unique_root",
    "integrate",
    "eval_interval",
    "forward_interval",
    "verify_nn_bounds",
    # Client
    "LeanClient",
    # Simplification
    "simplify",
    "expand",
    # Exceptions
    "LeanCertError",
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
    # Core network types
    "Layer",
    "TwoLayerReLUNetwork",
    "SequentialNetwork",
    "from_pytorch",
    "from_pytorch_sequential",
    # Transformer components
    "LayerNormParams",
    "LinearLayer",
    "FFNBlock",
    "TransformerBlock",
    "TransformerEncoder",
    "from_pytorch_transformer",
]
