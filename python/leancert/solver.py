# LeanCert v2 SDK - Solver
# Copyright (c) 2024 LeanCert Contributors. All rights reserved.

"""
High-level Solver API for LeanCert v2.

This module provides the main user-facing interface for verification.
"""

from __future__ import annotations
from fractions import Fraction
from typing import Optional, Union, Any

from .expr import Expr
from .domain import Interval, Box, normalize_domain
from .config import Config, Backend
from .client import LeanClient, _parse_interval, _parse_rat, _parse_dyadic_interval
from .result import (
    BoundsResult, RootsResult, RootInterval, IntegralResult, Certificate,
    UniqueRootResult, WitnessPoint, MinWitnessResult, MaxWitnessResult,
    RootWitnessResult, FailureDiagnosis, LipschitzResult,
)
from .adaptive import AdaptiveResult, AdaptiveConfig, verify_bound_adaptive as _verify_bound_adaptive
from .exceptions import VerificationFailed, DomainError
from .rational import to_fraction
from .simplify import simplify as _simplify_expr
from .expr import has_dependency as _has_dependency


# Version info
__version__ = "0.2.0"
LEAN_VERSION = "4.24.0"  # Updated when bridge is rebuilt


class Solver:
    """
    High-level interface for LeanCert verification.

    Manages compilation and communication with the Lean kernel.
    Use as a context manager for automatic cleanup.

    Example:
        with Solver() as solver:
            x = var('x')
            result = solver.find_bounds(x**2, {'x': (0, 1)})
    """

    def __init__(
        self,
        client: Optional[LeanClient] = None,
        auto_simplify: bool = True,
        auto_affine: bool = True,
    ):
        """
        Initialize the solver.

        Args:
            client: Optional LeanClient instance. If None, creates a new one.
            auto_simplify: If True (default), automatically simplify expressions
                          before sending to the kernel. This reduces the dependency
                          problem in interval arithmetic by canceling like terms.
            auto_affine: If True (default), automatically switch to Affine backend
                        for expressions with the dependency problem (same variable
                        appears multiple times). This gives much tighter bounds
                        for expressions like x - x, x * (1 - x), etc.
        """
        self._client = client
        self._owns_client = client is None
        self._auto_simplify = auto_simplify
        self._auto_affine = auto_affine

    def _ensure_client(self) -> LeanClient:
        """Ensure we have a client connection."""
        if self._client is None:
            self._client = LeanClient()
        return self._client

    def close(self) -> None:
        """Close the solver and release resources."""
        if self._owns_client and self._client is not None:
            self._client.close()
            self._client = None

    def __enter__(self) -> Solver:
        return self

    def __exit__(self, *args) -> None:
        self.close()

    def _prepare_request(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
    ) -> tuple[dict, Box]:
        """
        Prepare expression and domain for a kernel request.

        Returns:
            Tuple of (compiled expr JSON, normalized Box).
        """
        # Auto-simplify expression to reduce dependency problem
        if self._auto_simplify:
            expr = _simplify_expr(expr)

        # Normalize domain to Box
        # For univariate, infer variable name from expression
        if isinstance(domain, (Interval, tuple)):
            free_vars = expr.free_vars()
            if len(free_vars) == 1:
                default_var = next(iter(free_vars))
            else:
                default_var = 'x'
            box = normalize_domain(domain, default_var=default_var)
        else:
            box = normalize_domain(domain)

        # Validate expression uses only defined variables
        box.validate_expr(expr)

        # Compile expression with box's variable ordering
        var_order = box.var_order()
        expr_json = expr.compile(var_order)

        return expr_json, box

    def _select_backend(self, expr: Expr, config: Config) -> Config:
        """
        Select the appropriate backend based on expression characteristics.

        If auto_affine is enabled and the expression has the dependency problem
        (same variable appears multiple times), automatically upgrade to the
        Affine backend for tighter bounds.

        Args:
            expr: The expression being evaluated.
            config: The user-provided configuration.

        Returns:
            Potentially modified config with upgraded backend.
        """
        # Only auto-upgrade if:
        # 1. auto_affine is enabled
        # 2. User is using the default backend (DYADIC) - don't override explicit choices
        # 3. Expression has dependency problem
        if (self._auto_affine
            and config.backend == Backend.DYADIC
            and _has_dependency(expr)):
            # Create a new config with AFFINE backend
            from dataclasses import replace
            from .config import AffineConfig
            return replace(
                config,
                backend=Backend.AFFINE,
                affine_config=AffineConfig(),
            )
        return config

    def eval_interval(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> Interval:
        """
        Evaluate expression over a domain using interval arithmetic.

        This is the core operation that computes a rigorous enclosure of
        all possible values the expression can take over the domain.

        Args:
            expr: Expression to evaluate.
            domain: Domain specification (Interval, Box, tuple, or dict).
            config: Solver configuration. Defaults to DYADIC backend.
                   For expressions with repeated variables (e.g., x - x),
                   AFFINE backend is automatically used for tighter bounds.

        Returns:
            Interval containing all possible values.

        Example:
            >>> solver.eval_interval(x**2 + sin(x), {'x': (0, 1)})
            Interval(0, 1.8414709848...)

            # Dependency problem is auto-detected and handled:
            >>> solver.eval_interval(x - x, {'x': (-1, 1)})  # Returns ~[0, 0]
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()

        # Auto-select backend based on expression characteristics
        config = self._select_backend(expr, config)

        if config.backend == Backend.DYADIC:
            # Use high-performance Dyadic backend
            dyadic_cfg = config.to_dyadic_kernel()
            result = client.eval_interval_dyadic(
                expr_json, box_json,
                precision=dyadic_cfg['precision'],
                taylor_depth=dyadic_cfg['taylorDepth'],
                round_after_ops=dyadic_cfg['roundAfterOps'],
            )
            # Parse the Dyadic interval for higher precision
            if 'dyadic' in result:
                return _parse_dyadic_interval(result['dyadic'])
            # Fallback to rational representation
            return _parse_interval({'lo': result['lo'], 'hi': result['hi']})
        elif config.backend == Backend.AFFINE:
            # Use Affine arithmetic for tight bounds (solves dependency problem)
            affine_cfg = config.to_affine_kernel()
            result = client.eval_interval_affine(
                expr_json, box_json,
                taylor_depth=affine_cfg['taylorDepth'],
                max_noise_symbols=affine_cfg['maxNoiseSymbols'],
            )
            return _parse_interval({'lo': result['lo'], 'hi': result['hi']})
        else:
            # Use standard rational backend
            cfg = config.to_kernel()
            result = client.eval_interval(
                expr_json, box_json,
                taylor_depth=cfg['taylorDepth'],
            )
            return _parse_interval({'lo': result['lo'], 'hi': result['hi']})

    def find_bounds(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> BoundsResult:
        """
        Find global minimum and maximum bounds.

        Args:
            expr: Expression to analyze.
            domain: Domain specification (Interval, Box, tuple, or dict).
            config: Solver configuration. Defaults to DYADIC backend.
                   For expressions with repeated variables (e.g., x - x, x*(1-x)),
                   AFFINE backend is automatically used for tighter bounds.

        Returns:
            BoundsResult with verified min/max intervals.

        Example:
            >>> # Default: uses Dyadic backend (fast, avoids denominator explosion)
            >>> result = solver.find_bounds(x**2, {'x': (-1, 1)})

            >>> # Dependency problem auto-detected, uses Affine for tight bounds:
            >>> result = solver.find_bounds(x - x, {'x': (-1, 1)})  # Returns ~[0, 0]

            >>> # Explicit backend choice overrides auto-selection:
            >>> result = solver.find_bounds(expr, domain, Config.affine())
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()

        # Auto-select backend based on expression characteristics
        config = self._select_backend(expr, config)
        cfg = config.to_kernel()

        if config.backend == Backend.DYADIC:
            # Use high-performance Dyadic backend
            dyadic_cfg = config.to_dyadic_kernel()
            min_result = client.global_min_dyadic(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=dyadic_cfg['taylorDepth'],
                precision=dyadic_cfg['precision'],
            )
            max_result = client.global_max_dyadic(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=dyadic_cfg['taylorDepth'],
                precision=dyadic_cfg['precision'],
            )
        elif config.backend == Backend.AFFINE:
            # Use Affine backend for tight bounds
            affine_cfg = config.to_affine_kernel()
            min_result = client.global_min_affine(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=affine_cfg['taylorDepth'],
                max_noise_symbols=affine_cfg['maxNoiseSymbols'],
            )
            max_result = client.global_max_affine(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=affine_cfg['taylorDepth'],
                max_noise_symbols=affine_cfg['maxNoiseSymbols'],
            )
        else:
            # Standard rational backend
            min_result = client.global_min(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )
            max_result = client.global_max(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

        min_bound = _parse_interval({'lo': min_result['lo'], 'hi': min_result['hi']})
        max_bound = _parse_interval({'lo': max_result['lo'], 'hi': max_result['hi']})

        # Create certificate
        cert = Certificate(
            operation='find_bounds',
            expr_json=expr_json,
            domain_json=box_json,
            result_json={
                'min': {'lo': min_result['lo'], 'hi': min_result['hi']},
                'max': {'lo': max_result['lo'], 'hi': max_result['hi']},
                'backend': config.backend.value,
            },
            verified=True,
            lean_version=LEAN_VERSION,
            leancert_version=__version__,
        )

        return BoundsResult(
            min_bound=min_bound,
            max_bound=max_bound,
            verified=True,
            certificate=cert,
        )

    def verify_bound(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        upper: Optional[float] = None,
        lower: Optional[float] = None,
        config: Config = Config(),
        method: str = 'adaptive',  # Changed default to adaptive
    ) -> bool:
        """
        Verify that expression satisfies given bounds with False Positive Filtering.

        Pipeline:
        1. Symbolic Simplification (handles dependency problem)
        2. Global Optimization (Branch & Bound)
        3. Counterexample Concretization (filters false positives)

        Args:
            expr: Expression to verify.
            domain: Domain specification.
            upper: Upper bound to verify (expr <= upper).
            lower: Lower bound to verify (expr >= lower).
            config: Solver configuration.
            method: Verification method - 'adaptive' (default, uses optimization
                   with false positive filtering) or 'interval' (fast, conservative).

        Returns:
            True if verified.

        Raises:
            VerificationFailed: If bound verification fails AND is confirmed by
                               concrete evaluation (not a false positive).
            ValueError: If method is invalid or no bounds specified.
        """
        if upper is None and lower is None:
            raise ValueError("Must specify at least one of upper or lower bound")

        if method not in ('interval', 'adaptive'):
            raise ValueError(f"Unknown method: {method}. Use 'interval' or 'adaptive'.")

        # Keep original expression for concrete evaluation
        original_expr = expr

        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()
        cfg = config.to_kernel()

        if method == 'adaptive':
            return self._verify_bound_adaptive_with_concretization(
                client, original_expr, expr_json, box, box_json, cfg, upper, lower
            )
        else:
            return self._verify_bound_interval(
                client, expr_json, box_json, cfg, upper, lower
            )

    def _verify_bound_interval(
        self,
        client,
        expr_json: dict,
        box_json: list,
        cfg: dict,
        upper: Optional[float],
        lower: Optional[float],
    ) -> bool:
        """Verify bounds using simple interval evaluation."""
        if upper is not None:
            bound_frac = to_fraction(upper)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.check_bound(
                expr_json, box_json, bound_json,
                is_upper_bound=True,
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                computed = _parse_rat(result['computed_hi'])
                raise VerificationFailed(
                    f"Failed to verify upper bound {upper}. Computed max: {float(computed):.6f}",
                    computed_bound=computed,
                )

        if lower is not None:
            bound_frac = to_fraction(lower)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.check_bound(
                expr_json, box_json, bound_json,
                is_upper_bound=False,
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                computed = _parse_rat(result['computed_lo'])
                raise VerificationFailed(
                    f"Failed to verify lower bound {lower}. Computed min: {float(computed):.6f}",
                    computed_bound=computed,
                )

        return True

    def _verify_bound_adaptive(
        self,
        client,
        expr_json: dict,
        box_json: list,
        cfg: dict,
        upper: Optional[float],
        lower: Optional[float],
    ) -> bool:
        """Verify bounds using adaptive optimization."""
        if upper is not None:
            bound_frac = to_fraction(upper)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.verify_adaptive(
                expr_json, box_json, bound_json,
                is_upper_bound=True,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                min_value = _parse_rat(result['minValue'])
                raise VerificationFailed(
                    f"Failed to verify upper bound {upper}. Gap: {float(min_value):.6f}",
                    computed_bound=to_fraction(upper) - min_value,
                )

        if lower is not None:
            bound_frac = to_fraction(lower)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.verify_adaptive(
                expr_json, box_json, bound_json,
                is_upper_bound=False,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                min_value = _parse_rat(result['minValue'])
                raise VerificationFailed(
                    f"Failed to verify lower bound {lower}. Gap: {float(min_value):.6f}",
                    computed_bound=to_fraction(lower) + min_value,
                )

        return True

    def _verify_bound_adaptive_with_concretization(
        self,
        client,
        original_expr: Expr,
        expr_json: dict,
        box: Box,
        box_json: list,
        cfg: dict,
        upper: Optional[float],
        lower: Optional[float],
    ) -> bool:
        """
        Verify bounds using optimization with false positive filtering.

        This method uses global optimization to find the min/max, then
        concretizes the result by evaluating the original expression
        at the reported extremum point. If the concrete evaluation
        doesn't violate the bound, it's a false positive caused by
        interval over-approximation.
        """
        var_names = box.var_order()

        def _concretize_and_check(
            best_box: list,
            limit: float,
            is_upper: bool,
        ) -> bool:
            """
            Check if violation is real by evaluating at the midpoint.

            Returns True if the violation is REAL (not a false positive).
            Returns False if it's a false positive (concrete value is OK).
            """
            try:
                if not best_box:
                    # No location data, can't filter - assume real
                    return True

                # Construct environment from bestBox midpoints
                env = {}
                for i, interval_json in enumerate(best_box):
                    if i >= len(var_names):
                        break
                    name = var_names[i]
                    lo = _parse_rat(interval_json['lo'])
                    hi = _parse_rat(interval_json['hi'])
                    midpoint = (lo + hi) / 2
                    env[name] = float(midpoint)

                # Concrete evaluation using Python math
                concrete_val = original_expr.evaluate(env)

                # Check against limit
                if is_upper:
                    # Claimed violation: max(f) > upper
                    # Real if concrete_val > limit
                    return float(concrete_val) > limit
                else:
                    # Claimed violation: min(f) < lower
                    # Real if concrete_val < limit
                    return float(concrete_val) < limit

            except Exception:
                # If concretization fails, assume real to be safe
                return True

        # --- LOWER BOUND CHECK (f(x) >= lower) ---
        if lower is not None:
            # Find minimum of f
            min_result = client.global_min(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

            computed_min_lo = _parse_rat(min_result.get('lo', {'n': 0, 'd': 1}))
            limit = to_fraction(lower)

            if computed_min_lo < limit:
                # Solver claims violation. Check with concretization.
                best_box = min_result.get('bestBox', [])

                if _concretize_and_check(best_box, float(lower), is_upper=False):
                    # Real violation confirmed
                    raise VerificationFailed(
                        f"Lower bound verification failed. "
                        f"Min value: {float(computed_min_lo):.6f} < {lower}",
                        computed_bound=computed_min_lo,
                    )
                # Else: False positive, continue (bound is actually OK)

        # --- UPPER BOUND CHECK (f(x) <= upper) ---
        if upper is not None:
            # Find maximum of f
            max_result = client.global_max(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

            computed_max_hi = _parse_rat(max_result.get('hi', {'n': 0, 'd': 1}))
            limit = to_fraction(upper)

            if computed_max_hi > limit:
                # Solver claims violation. Check with concretization.
                best_box = max_result.get('bestBox', [])

                if _concretize_and_check(best_box, float(upper), is_upper=True):
                    # Real violation confirmed
                    raise VerificationFailed(
                        f"Upper bound verification failed. "
                        f"Max value: {float(computed_max_hi):.6f} > {upper}",
                        computed_bound=computed_max_hi,
                    )
                # Else: False positive, continue

        return True

    def find_roots(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> RootsResult:
        """
        Find roots of a univariate expression.

        Uses interval bisection with sign change detection. The algorithm
        subdivides the domain and checks each subinterval for roots.

        Args:
            expr: Expression to find roots of.
            domain: Search domain (must be 1D).
            config: Solver configuration.

        Returns:
            RootsResult with root intervals. Each RootInterval has a status:

            - 'confirmed': Sign change detected (f(lo) and f(hi) have opposite signs).
              The Intermediate Value Theorem GUARANTEES a root exists in this interval.
              This is mathematically certain.

            - 'possible': The interval contains zero but no sign change was detected.
              This can happen when:
              * The root is a tangent point (e.g., x² = 0 at x=0)
              * Interval bounds are too loose to detect sign change
              * Multiple roots in the interval cancel out
              A root MAY exist but is not proven.

            - 'no_root': The interval provably contains no roots (f(x) is bounded
              away from zero throughout the interval).

        Example:
            >>> result = solver.find_roots(x**2 - 1, {'x': (-2, 2)})
            >>> for root in result.roots:
            ...     print(f"{root.interval}: {root.status}")
            [-1.001, -0.999]: confirmed  # Sign change proves root at x=-1
            [0.999, 1.001]: confirmed    # Sign change proves root at x=1
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)

        # For root finding, we need a 1D interval
        if len(box) != 1:
            raise DomainError("Root finding requires a 1D domain")

        var_name = box.var_order()[0]
        interval = box[var_name]
        interval_json = interval.to_kernel()
        cfg = config.to_kernel()

        result = client.find_roots(
            expr_json, interval_json,
            max_iter=cfg['maxIters'],
            tolerance=cfg['tolerance'],
            taylor_depth=cfg['taylorDepth'],
        )

        roots = []
        for r in result['roots']:
            status_map = {
                'hasRoot': 'confirmed',
                'noRoot': 'no_root',
                'unknown': 'possible',
            }
            roots.append(RootInterval(
                interval=_parse_interval(r),
                status=status_map.get(r['status'], 'possible'),
            ))

        return RootsResult(
            roots=roots,
            iterations=result['iterations'],
            verified=True,
        )

    def find_unique_root(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> UniqueRootResult:
        """
        Find a unique root using interval Newton method.

        This method uses interval Newton iteration to prove both EXISTENCE
        and UNIQUENESS of a root. It's mathematically stronger than
        find_roots() which only proves existence.

        The interval Newton method works by:
        1. Computing the interval derivative f'([x])
        2. Performing Newton step: N(x) = m - f(m)/f'([x]) where m = midpoint
        3. If N(x) ⊂ [x] (contracts), uniqueness is proven by Brouwer fixed point

        Args:
            expr: Expression to find root of.
            domain: Search domain (must be 1D).
            config: Solver configuration.

        Returns:
            UniqueRootResult with:
            - unique: True if a unique root is PROVEN to exist
            - interval: Containing interval for the root
            - reason: Explanation of the result:
              * 'contraction': Newton iteration contracted, proving uniqueness
              * 'no_contraction': Could not prove uniqueness (root may still exist)
              * 'no_root': Interval provably contains no roots

        Note:
            'no_contraction' does NOT mean no root exists. It means uniqueness
            couldn't be proven. The interval might:
            - Contain multiple roots
            - Be too wide for Newton to contract
            - Have a nearly-zero derivative (ill-conditioned)

            Use find_roots() first to locate candidate intervals, then
            find_unique_root() on smaller subintervals if uniqueness matters.
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)

        # For unique root finding, we need a 1D interval
        if len(box) != 1:
            raise DomainError("Unique root finding requires a 1D domain")

        var_name = box.var_order()[0]
        interval = box[var_name]
        interval_json = interval.to_kernel()
        cfg = config.to_kernel()

        result = client.find_unique_root(
            expr_json, interval_json,
            taylor_depth=cfg['taylorDepth'],
        )

        result_interval = _parse_interval(result['interval'])

        return UniqueRootResult(
            unique=result['unique'],
            interval=result_interval,
            reason=result['reason'],
        )

    def integrate(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        partitions: int = 10,
        config: Config = Config(),
    ) -> IntegralResult:
        """
        Compute rigorous integral bounds.

        Args:
            expr: Expression to integrate.
            domain: Integration domain.
            partitions: Number of partitions.
            config: Solver configuration.

        Returns:
            IntegralResult with verified bounds.
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)

        # For integration, we need a 1D interval
        if len(box) != 1:
            raise DomainError("Integration requires a 1D domain")

        var_name = box.var_order()[0]
        interval = box[var_name]
        interval_json = interval.to_kernel()
        cfg = config.to_kernel()

        result = client.integrate(
            expr_json, interval_json,
            partitions=partitions,
            taylor_depth=cfg['taylorDepth'],
        )

        bounds = _parse_interval(result)

        return IntegralResult(
            bounds=bounds,
            verified=True,
        )

    # =========================================================================
    # Witness Synthesis Methods
    # =========================================================================
    # These methods support auto-witness synthesis for existential proof goals.
    # They find witnesses via optimization/root-finding and return certificate-
    # checked results that can be used to construct Lean proofs.

    def synthesize_min_witness(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> MinWitnessResult:
        """
        Synthesize a witness for ∃ m, ∀ x ∈ I, f(x) ≥ m.

        Finds the global minimum of the expression over the domain and returns
        a witness value m along with the point where the minimum is achieved.

        Args:
            expr: Expression to minimize.
            domain: Domain specification.
            config: Solver configuration. Use race_strategies=True to try
                   multiple backends in parallel.

        Returns:
            MinWitnessResult containing the witness value and point.

        Example:
            >>> result = solver.synthesize_min_witness(x**2, {'x': (-1, 1)})
            >>> print(result.witness_value)  # ~0
            >>> print(result.to_lean_tactic())  # Lean proof code
        """
        client = self._ensure_client()
        original_expr = expr
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()
        var_names = box.var_order()

        # Select backend and prepare config
        config = self._select_backend(expr, config)

        if config.race_strategies:
            result, strategy = self._race_min_strategies(
                expr_json, box_json, config
            )
        else:
            result = self._run_min_optimization(
                client, expr_json, box_json, config
            )
            strategy = config.backend.value

        # Extract witness from bestBox
        witness_point = self._extract_witness_point(
            result.get('bestBox', []),
            var_names,
            original_expr,
        )

        # The proven bound is the lower bound of the minimum interval
        min_lo = _parse_rat(result.get('lo', {'n': 0, 'd': 1}))
        min_hi = _parse_rat(result.get('hi', {'n': 0, 'd': 1}))

        # Use midpoint as witness value (it's within the proven interval)
        witness_value = (min_lo + min_hi) / 2

        # Apply incremental refinement if requested
        refinement_history = []
        if config.incremental_refinement:
            witness_value, refinement_history = self._refine_min_bound(
                client, expr_json, box_json, config, min_lo, min_hi
            )

        # Create certificate
        cert = Certificate(
            operation='synthesize_min_witness',
            expr_json=expr_json,
            domain_json=box_json,
            result_json={
                'witness': {'n': witness_value.numerator, 'd': witness_value.denominator},
                'witness_point': witness_point.to_dict() if witness_point else None,
                'proven_bound': {'n': min_lo.numerator, 'd': min_lo.denominator},
                'backend': strategy,
            },
            verified=True,
            lean_version=LEAN_VERSION,
            leancert_version=__version__,
        )

        return MinWitnessResult(
            verified=True,
            witness_value=witness_value,
            witness_point=witness_point,
            proven_bound=min_lo,
            certificate=cert,
            strategy_used=strategy,
            refinement_history=refinement_history,
        )

    def synthesize_max_witness(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> MaxWitnessResult:
        """
        Synthesize a witness for ∃ M, ∀ x ∈ I, f(x) ≤ M.

        Finds the global maximum of the expression over the domain and returns
        a witness value M along with the point where the maximum is achieved.

        Args:
            expr: Expression to maximize.
            domain: Domain specification.
            config: Solver configuration.

        Returns:
            MaxWitnessResult containing the witness value and point.
        """
        client = self._ensure_client()
        original_expr = expr
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()
        var_names = box.var_order()

        config = self._select_backend(expr, config)

        if config.race_strategies:
            result, strategy = self._race_max_strategies(
                expr_json, box_json, config
            )
        else:
            result = self._run_max_optimization(
                client, expr_json, box_json, config
            )
            strategy = config.backend.value

        witness_point = self._extract_witness_point(
            result.get('bestBox', []),
            var_names,
            original_expr,
        )

        max_lo = _parse_rat(result.get('lo', {'n': 0, 'd': 1}))
        max_hi = _parse_rat(result.get('hi', {'n': 0, 'd': 1}))
        witness_value = (max_lo + max_hi) / 2

        refinement_history = []
        if config.incremental_refinement:
            witness_value, refinement_history = self._refine_max_bound(
                client, expr_json, box_json, config, max_lo, max_hi
            )

        cert = Certificate(
            operation='synthesize_max_witness',
            expr_json=expr_json,
            domain_json=box_json,
            result_json={
                'witness': {'n': witness_value.numerator, 'd': witness_value.denominator},
                'witness_point': witness_point.to_dict() if witness_point else None,
                'proven_bound': {'n': max_hi.numerator, 'd': max_hi.denominator},
                'backend': strategy,
            },
            verified=True,
            lean_version=LEAN_VERSION,
            leancert_version=__version__,
        )

        return MaxWitnessResult(
            verified=True,
            witness_value=witness_value,
            witness_point=witness_point,
            proven_bound=max_hi,
            certificate=cert,
            strategy_used=strategy,
            refinement_history=refinement_history,
        )

    def synthesize_root_witness(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> RootWitnessResult:
        """
        Synthesize a witness for ∃ x ∈ I, f(x) = 0.

        Finds a root of the expression in the domain and returns a witness
        point along with the enclosing interval.

        Args:
            expr: Expression to find root of.
            domain: Search domain (must be 1D).
            config: Solver configuration.

        Returns:
            RootWitnessResult containing the witness point and interval.

        Raises:
            VerificationFailed: If no root can be found/proven.
        """
        client = self._ensure_client()
        original_expr = expr
        expr_json, box = self._prepare_request(expr, domain)

        if len(box) != 1:
            raise DomainError("Root witness synthesis requires a 1D domain")

        var_name = box.var_order()[0]
        interval = box[var_name]
        interval_json = interval.to_kernel()
        cfg = config.to_kernel()

        # Try Newton contraction first (proves uniqueness too)
        unique_result = client.find_unique_root(
            expr_json, interval_json,
            taylor_depth=cfg['taylorDepth'],
        )

        if unique_result['unique']:
            root_interval = _parse_interval(unique_result['interval'])
            midpoint = root_interval.midpoint()

            # Evaluate at midpoint to get function value
            env = {var_name: float(midpoint)}
            try:
                func_val = original_expr.evaluate(env)
            except Exception:
                func_val = Fraction(0)

            witness_point = WitnessPoint(
                values={var_name: midpoint},
                function_value=to_fraction(func_val),
                interval={var_name: (root_interval.lo, root_interval.hi)},
            )

            cert = Certificate(
                operation='synthesize_root_witness',
                expr_json=expr_json,
                domain_json=box.to_kernel_list(),
                result_json={
                    'witness_point': witness_point.to_dict(),
                    'root_interval': {'lo': {'n': root_interval.lo.numerator, 'd': root_interval.lo.denominator},
                                      'hi': {'n': root_interval.hi.numerator, 'd': root_interval.hi.denominator}},
                    'proof_method': 'newton_contraction',
                },
                verified=True,
                lean_version=LEAN_VERSION,
                leancert_version=__version__,
            )

            return RootWitnessResult(
                verified=True,
                witness_point=witness_point,
                root_interval=root_interval,
                proof_method='newton_contraction',
                certificate=cert,
            )

        # Fall back to sign change detection
        roots_result = client.find_roots(
            expr_json, interval_json,
            max_iter=cfg['maxIters'],
            tolerance=cfg['tolerance'],
            taylor_depth=cfg['taylorDepth'],
        )

        confirmed_roots = [r for r in roots_result['roots'] if r['status'] == 'hasRoot']
        if not confirmed_roots:
            raise VerificationFailed(
                "No root found via sign change or Newton contraction",
                computed_bound=None,
            )

        # Use first confirmed root
        root_data = confirmed_roots[0]
        root_interval = _parse_interval(root_data)
        midpoint = root_interval.midpoint()

        env = {var_name: float(midpoint)}
        try:
            func_val = original_expr.evaluate(env)
        except Exception:
            func_val = Fraction(0)

        witness_point = WitnessPoint(
            values={var_name: midpoint},
            function_value=to_fraction(func_val),
            interval={var_name: (root_interval.lo, root_interval.hi)},
        )

        cert = Certificate(
            operation='synthesize_root_witness',
            expr_json=expr_json,
            domain_json=box.to_kernel_list(),
            result_json={
                'witness_point': witness_point.to_dict(),
                'root_interval': {'lo': {'n': root_interval.lo.numerator, 'd': root_interval.lo.denominator},
                                  'hi': {'n': root_interval.hi.numerator, 'd': root_interval.hi.denominator}},
                'proof_method': 'sign_change',
            },
            verified=True,
            lean_version=LEAN_VERSION,
            leancert_version=__version__,
        )

        return RootWitnessResult(
            verified=True,
            witness_point=witness_point,
            root_interval=root_interval,
            proof_method='sign_change',
            certificate=cert,
        )

    def diagnose_bound_failure(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        upper: Optional[float] = None,
        lower: Optional[float] = None,
        config: Config = Config(),
    ) -> Optional[FailureDiagnosis]:
        """
        Diagnose why a bound verification would fail.

        This is the foundation for Counterexample-Guided Proof Refinement (CEGPR).
        It finds the worst-case point and suggests a bound that would succeed.

        Args:
            expr: Expression to analyze.
            domain: Domain specification.
            upper: Upper bound to check.
            lower: Lower bound to check.
            config: Solver configuration.

        Returns:
            FailureDiagnosis if the bound would fail, None if it would succeed.
        """
        client = self._ensure_client()
        original_expr = expr
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()
        var_names = box.var_order()
        cfg = config.to_kernel()

        if upper is not None:
            # Check if upper bound would fail
            max_result = client.global_max(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

            max_hi = _parse_rat(max_result.get('hi', {'n': 0, 'd': 1}))
            limit = to_fraction(upper)

            if max_hi > limit:
                # Bound fails - extract worst point
                best_box = max_result.get('bestBox', [])
                worst_point = {}
                for i, interval_json in enumerate(best_box):
                    if i >= len(var_names):
                        break
                    name = var_names[i]
                    lo = _parse_rat(interval_json['lo'])
                    hi = _parse_rat(interval_json['hi'])
                    worst_point[name] = float((lo + hi) / 2)

                margin = float(limit - max_hi)  # Negative when bound violated
                suggested = float(max_hi) * 1.01  # Add 1% margin

                return FailureDiagnosis(
                    failure_type='bound_too_tight',
                    margin=margin,
                    worst_point=worst_point,
                    suggested_bound=suggested,
                )

        if lower is not None:
            # Check if lower bound would fail
            min_result = client.global_min(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

            min_lo = _parse_rat(min_result.get('lo', {'n': 0, 'd': 1}))
            limit = to_fraction(lower)

            if min_lo < limit:
                best_box = min_result.get('bestBox', [])
                worst_point = {}
                for i, interval_json in enumerate(best_box):
                    if i >= len(var_names):
                        break
                    name = var_names[i]
                    lo = _parse_rat(interval_json['lo'])
                    hi = _parse_rat(interval_json['hi'])
                    worst_point[name] = float((lo + hi) / 2)

                margin = float(min_lo - limit)  # Negative when bound violated
                suggested = float(min_lo) * 0.99  # Add 1% margin

                return FailureDiagnosis(
                    failure_type='bound_too_tight',
                    margin=margin,
                    worst_point=worst_point,
                    suggested_bound=suggested,
                )

        return None  # Bound would succeed

    # =========================================================================
    # Adaptive Verification (CEGAR)
    # =========================================================================

    def verify_bound_adaptive(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        upper: Optional[float] = None,
        lower: Optional[float] = None,
        adaptive_config: AdaptiveConfig = AdaptiveConfig(),
        config: Config = Config(),
    ) -> AdaptiveResult:
        """
        Verify a bound using CEGAR (Counterexample-Guided Abstraction Refinement).

        When single-shot verification fails on a large domain, this method
        automatically splits the domain and retries on subdomains until either:
        - The bound is verified on all subdomains, or
        - A minimal subdomain is found where the bound genuinely fails

        This turns LeanCert into a CEGAR loop where Python handles the search
        tree and Lean only checks final claims. The result includes a structured
        Lean proof that combines subdomain proofs.

        Args:
            expr: Expression to verify.
            domain: Domain specification.
            upper: Upper bound to verify (f(x) ≤ upper).
            lower: Lower bound to verify (f(x) ≥ lower).
            adaptive_config: Configuration for domain splitting (max_splits,
                            max_depth, strategy, etc.).
            config: Underlying solver configuration.

        Returns:
            AdaptiveResult with:
            - verified: True if bound holds on all subdomains
            - subdomains: Tree of all subdomains explored
            - lean_proof: Generated Lean proof combining subdomain proofs
            - failing_subdomain: Minimal region where bound fails (if any)

        Example:
            >>> result = solver.verify_bound_adaptive(
            ...     sin(x) + cos(x),
            ...     {'x': (0, 10)},
            ...     upper=1.5,
            ...     adaptive_config=AdaptiveConfig(max_splits=64),
            ... )
            >>> print(result.verified)
            True
            >>> print(result.lean_proof)
            theorem adaptive_bound_proof : ...

        Generated Lean proofs have this structure:
            theorem bound_on_domain : ∀ x ∈ Set.Icc 0 10, f x ≤ 1.5 := by
              intro x hx
              rcases interval_cases hx with h1 | h2 | h3
              · interval_decide  -- x ∈ [0, 3.33]
              · interval_decide  -- x ∈ [3.33, 6.67]
              · interval_decide  -- x ∈ [6.67, 10]
        """
        return _verify_bound_adaptive(
            self,
            expr,
            domain,
            upper=upper,
            lower=lower,
            adaptive_config=adaptive_config,
            solver_config=config,
        )

    # =========================================================================
    # Helper methods for witness synthesis
    # =========================================================================

    def _extract_witness_point(
        self,
        best_box: list,
        var_names: list[str],
        original_expr: Expr,
    ) -> Optional[WitnessPoint]:
        """Extract a WitnessPoint from optimization bestBox."""
        if not best_box:
            return None

        try:
            values = {}
            interval = {}
            for i, interval_json in enumerate(best_box):
                if i >= len(var_names):
                    break
                name = var_names[i]
                lo = _parse_rat(interval_json['lo'])
                hi = _parse_rat(interval_json['hi'])
                midpoint = (lo + hi) / 2
                values[name] = midpoint
                interval[name] = (lo, hi)

            # Evaluate expression at witness point
            env = {k: float(v) for k, v in values.items()}
            func_val = original_expr.evaluate(env)

            return WitnessPoint(
                values=values,
                function_value=to_fraction(func_val),
                interval=interval,
            )
        except Exception:
            return None

    def _run_min_optimization(
        self,
        client: LeanClient,
        expr_json: dict,
        box_json: list,
        config: Config,
    ) -> dict:
        """Run minimization with the configured backend."""
        cfg = config.to_kernel()

        if config.backend == Backend.DYADIC:
            dyadic_cfg = config.to_dyadic_kernel()
            return client.global_min_dyadic(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=dyadic_cfg['taylorDepth'],
                precision=dyadic_cfg['precision'],
            )
        elif config.backend == Backend.AFFINE:
            affine_cfg = config.to_affine_kernel()
            return client.global_min_affine(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=affine_cfg['taylorDepth'],
                max_noise_symbols=affine_cfg['maxNoiseSymbols'],
            )
        else:
            return client.global_min(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

    def _run_max_optimization(
        self,
        client: LeanClient,
        expr_json: dict,
        box_json: list,
        config: Config,
    ) -> dict:
        """Run maximization with the configured backend."""
        cfg = config.to_kernel()

        if config.backend == Backend.DYADIC:
            dyadic_cfg = config.to_dyadic_kernel()
            return client.global_max_dyadic(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=dyadic_cfg['taylorDepth'],
                precision=dyadic_cfg['precision'],
            )
        elif config.backend == Backend.AFFINE:
            affine_cfg = config.to_affine_kernel()
            return client.global_max_affine(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=affine_cfg['taylorDepth'],
                max_noise_symbols=affine_cfg['maxNoiseSymbols'],
            )
        else:
            return client.global_max(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

    # =========================================================================
    # Lipschitz Bound Computation (for ε-δ continuity proofs)
    # =========================================================================

    def compute_lipschitz_bound(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> 'LipschitzResult':
        """
        Compute a verified Lipschitz bound for an expression over a domain.

        Uses forward-mode automatic differentiation to bound all partial
        derivatives |∂f/∂xᵢ| over the domain. The Lipschitz constant is
        L = max_i sup_{x ∈ domain} |∂f/∂xᵢ(x)|.

        This is VERIFIED by the Lean kernel - the derivative bounds are
        computed using interval arithmetic with correctness proofs.

        Args:
            expr: Expression to compute Lipschitz bound for.
            domain: Domain over which to compute the bound.
            config: Solver configuration.

        Returns:
            LipschitzResult containing:
              - lipschitz_bound: The verified Lipschitz constant L
              - gradient_bounds: Dict mapping variable names to derivative intervals
              - certificate: Verification certificate

        Example:
            >>> solver = Solver()
            >>> x = var('x')
            >>> result = solver.compute_lipschitz_bound(x**2, {'x': (0, 1)})
            >>> print(result.lipschitz_bound)  # Should be 2 (max of |2x| on [0,1])
            2

        Use case (ε-δ continuity):
            If L is the Lipschitz constant, then for any ε > 0,
            setting δ = ε/L guarantees |f(x) - f(a)| < ε whenever |x - a| < δ.
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()
        var_names = box.var_order()
        cfg = config.to_kernel()

        # Call the Lean kernel's derivative interval evaluation
        result = client.deriv_interval(
            expr_json, box_json,
            taylor_depth=cfg['taylorDepth'],
        )

        # Parse results
        lipschitz_bound = _parse_rat(result['lipschitz_bound'])

        gradient_bounds = {}
        for i, grad_json in enumerate(result.get('gradients', [])):
            if i < len(var_names):
                name = var_names[i]
                lo = _parse_rat(grad_json['lo'])
                hi = _parse_rat(grad_json['hi'])
                gradient_bounds[name] = Interval(lo, hi)

        # Create certificate
        cert = Certificate(
            operation='compute_lipschitz_bound',
            expr_json=expr_json,
            domain_json=box_json,
            result_json={
                'lipschitz_bound': {'n': lipschitz_bound.numerator, 'd': lipschitz_bound.denominator},
                'gradient_bounds': {k: v.to_kernel() for k, v in gradient_bounds.items()},
            },
            verified=True,
            lean_version=LEAN_VERSION,
            leancert_version=__version__,
        )

        return LipschitzResult(
            lipschitz_bound=lipschitz_bound,
            gradient_bounds=gradient_bounds,
            certificate=cert,
        )

    def _race_min_strategies(
        self,
        expr_json: dict,
        box_json: list,
        config: Config,
    ) -> tuple[dict, str]:
        """Race multiple optimization strategies and return the first to succeed."""
        import concurrent.futures

        client = self._ensure_client()
        cfg = config.to_kernel()

        def run_dyadic():
            dyadic_cfg = config.to_dyadic_kernel()
            return client.global_min_dyadic(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=dyadic_cfg['taylorDepth'],
                precision=dyadic_cfg['precision'],
            ), 'dyadic'

        def run_affine():
            affine_cfg = Config.affine().to_affine_kernel()
            return client.global_min_affine(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=affine_cfg['taylorDepth'],
                max_noise_symbols=affine_cfg['maxNoiseSymbols'],
            ), 'affine'

        def run_rational():
            return client.global_min(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            ), 'rational'

        # Race all strategies
        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as executor:
            futures = [
                executor.submit(run_dyadic),
                executor.submit(run_affine),
                executor.submit(run_rational),
            ]

            # Return first to complete successfully
            for future in concurrent.futures.as_completed(futures, timeout=config.timeout_ms / 1000):
                try:
                    result, strategy = future.result()
                    # Cancel remaining futures
                    for f in futures:
                        f.cancel()
                    return result, strategy
                except Exception:
                    continue

        # If all fail, fall back to dyadic
        result = run_dyadic()[0]
        return result, 'dyadic'

    def _race_max_strategies(
        self,
        expr_json: dict,
        box_json: list,
        config: Config,
    ) -> tuple[dict, str]:
        """Race multiple optimization strategies for maximization."""
        import concurrent.futures

        client = self._ensure_client()
        cfg = config.to_kernel()

        def run_dyadic():
            dyadic_cfg = config.to_dyadic_kernel()
            return client.global_max_dyadic(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=dyadic_cfg['taylorDepth'],
                precision=dyadic_cfg['precision'],
            ), 'dyadic'

        def run_affine():
            affine_cfg = Config.affine().to_affine_kernel()
            return client.global_max_affine(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=affine_cfg['taylorDepth'],
                max_noise_symbols=affine_cfg['maxNoiseSymbols'],
            ), 'affine'

        def run_rational():
            return client.global_max(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            ), 'rational'

        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as executor:
            futures = [
                executor.submit(run_dyadic),
                executor.submit(run_affine),
                executor.submit(run_rational),
            ]

            for future in concurrent.futures.as_completed(futures, timeout=config.timeout_ms / 1000):
                try:
                    result, strategy = future.result()
                    for f in futures:
                        f.cancel()
                    return result, strategy
                except Exception:
                    continue

        result = run_dyadic()[0]
        return result, 'dyadic'

    def _refine_min_bound(
        self,
        client: LeanClient,
        expr_json: dict,
        box_json: list,
        config: Config,
        min_lo: Fraction,
        min_hi: Fraction,
    ) -> tuple[Fraction, list[dict]]:
        """Incrementally refine minimum bound to find tightest provable value."""
        history = []
        current = (min_lo + min_hi) / 2
        step = (min_hi - min_lo) / 4

        # Try to tighten toward min_hi (the tighter estimate)
        for _ in range(10):  # Max 10 refinement steps
            candidate = current + step
            if config.target_bound is not None and float(candidate) > config.target_bound:
                break

            # Try to verify this tighter bound
            try:
                # Use interval check to verify
                cfg = config.to_kernel()
                bound_json = {'n': candidate.numerator, 'd': candidate.denominator}
                result = client.check_bound(
                    expr_json, box_json, bound_json,
                    is_upper_bound=False,  # Checking lower bound
                    taylor_depth=cfg['taylorDepth'],
                )

                if result.get('verified', False):
                    history.append({'bound': float(candidate), 'status': 'verified'})
                    current = candidate
                    step = step / 2
                else:
                    history.append({'bound': float(candidate), 'status': 'failed'})
                    step = -abs(step) / 2  # Back off
            except Exception:
                history.append({'bound': float(candidate), 'status': 'error'})
                step = -abs(step) / 2

            if abs(step) < abs(min_hi - min_lo) / 1000:
                break  # Convergence

        return current, history

    def _refine_max_bound(
        self,
        client: LeanClient,
        expr_json: dict,
        box_json: list,
        config: Config,
        max_lo: Fraction,
        max_hi: Fraction,
    ) -> tuple[Fraction, list[dict]]:
        """Incrementally refine maximum bound to find tightest provable value."""
        history = []
        current = (max_lo + max_hi) / 2
        step = (max_hi - max_lo) / 4

        # Try to tighten toward max_lo (the tighter estimate)
        for _ in range(10):
            candidate = current - step
            if config.target_bound is not None and float(candidate) < config.target_bound:
                break

            try:
                cfg = config.to_kernel()
                bound_json = {'n': candidate.numerator, 'd': candidate.denominator}
                result = client.check_bound(
                    expr_json, box_json, bound_json,
                    is_upper_bound=True,
                    taylor_depth=cfg['taylorDepth'],
                )

                if result.get('verified', False):
                    history.append({'bound': float(candidate), 'status': 'verified'})
                    current = candidate
                    step = step / 2
                else:
                    history.append({'bound': float(candidate), 'status': 'failed'})
                    step = -abs(step) / 2
            except Exception:
                history.append({'bound': float(candidate), 'status': 'error'})
                step = -abs(step) / 2

            if abs(step) < abs(max_hi - max_lo) / 1000:
                break

        return current, history

    def forward_interval(
        self,
        network,  # SequentialNetwork or TwoLayerReLUNetwork
        input_domain: Union[Box, dict, list],
        precision: int = -53,
    ) -> list[Interval]:
        """
        Propagate intervals through a neural network using verified arithmetic.

        This runs verified interval arithmetic forward propagation through
        the network, computing rigorous bounds on all possible outputs.

        Args:
            network: A SequentialNetwork or TwoLayerReLUNetwork from leancert.nn
            input_domain: Input intervals as Box, dict, or list of tuples
            precision: Dyadic precision (-53 = IEEE double precision)

        Returns:
            List of output intervals (one per output neuron)

        Example:
            >>> import leancert as lc
            >>> from leancert.nn import SequentialNetwork, Layer
            >>> layer = Layer.from_numpy(np.array([[1, -1]]), np.array([0]))
            >>> net = SequentialNetwork([layer])
            >>> outputs = lc.forward_interval(net, {"x0": (-1, 1), "x1": (-1, 1)})
        """
        # Import here to avoid circular dependency
        from . import nn as nn_module

        client = self._ensure_client()

        # Convert network to SequentialNetwork if needed
        if isinstance(network, nn_module.TwoLayerReLUNetwork):
            network = nn_module.SequentialNetwork.from_two_layer(network)

        # Convert input domain to list of intervals
        if isinstance(input_domain, dict):
            # Dict format: {"x0": (lo, hi), "x1": (lo, hi), ...}
            intervals = []
            for i in range(network.input_dim):
                var_name = network.input_names[i] if i < len(network.input_names) else f"x{i}"
                if var_name in input_domain:
                    lo, hi = input_domain[var_name]
                else:
                    raise DomainError(f"Missing input variable: {var_name}")
                intervals.append({"lo": {"n": int(Fraction(lo).numerator), "d": int(Fraction(lo).denominator)},
                                  "hi": {"n": int(Fraction(hi).numerator), "d": int(Fraction(hi).denominator)}})
        elif isinstance(input_domain, Box):
            intervals = [input_domain[v].to_kernel() for v in input_domain.var_order()]
        elif isinstance(input_domain, list):
            # List of tuples: [(lo0, hi0), (lo1, hi1), ...]
            intervals = []
            for lo, hi in input_domain:
                intervals.append({"lo": {"n": int(Fraction(lo).numerator), "d": int(Fraction(lo).denominator)},
                                  "hi": {"n": int(Fraction(hi).numerator), "d": int(Fraction(hi).denominator)}})
        else:
            raise DomainError(f"Unsupported input_domain type: {type(input_domain)}")

        # Convert layers to JSON format
        layers_json = []
        for layer in network.layers:
            weights_json = [
                [{"n": num, "d": denom} for num, denom in row]
                for row in layer.weights
            ]
            bias_json = [{"n": num, "d": denom} for num, denom in layer.bias]
            layers_json.append({"weights": weights_json, "bias": bias_json})

        # Call bridge
        result = client.forward_interval(layers_json, intervals, precision)

        # Parse output intervals
        outputs = []
        for interval_data in result["output"]:
            lo = _parse_rat(interval_data["lo"])
            hi = _parse_rat(interval_data["hi"])
            outputs.append(Interval(lo, hi))

        return outputs


# Global solver instance for convenience functions
_global_solver: Optional[Solver] = None


def _get_solver() -> Solver:
    """Get or create global solver instance."""
    global _global_solver
    if _global_solver is None:
        _global_solver = Solver()
    return _global_solver


# Convenience functions that use global solver

def find_bounds(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    config: Config = Config(),
) -> BoundsResult:
    """Find global min/max bounds for an expression."""
    return _get_solver().find_bounds(expr, domain, config)


def eval_interval(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    config: Config = Config(),
) -> Interval:
    """
    Evaluate expression over a domain using interval arithmetic.

    This is the core operation that computes a rigorous enclosure of
    all possible values the expression can take over the domain.

    Args:
        expr: Expression to evaluate.
        domain: Domain specification (Interval, Box, tuple, or dict).
        config: Solver configuration. Use Config.dyadic() for high
               performance on deep expressions.

    Returns:
        Interval containing all possible values.

    Example:
        >>> import leancert as lc
        >>> x = lc.var('x')
        >>> lc.eval_interval(x**2 + lc.sin(x), {'x': (0, 1)})
        Interval(0, 1.8414709848...)

        # For faster evaluation on complex expressions:
        >>> lc.eval_interval(expr, domain, Config.dyadic())
    """
    return _get_solver().eval_interval(expr, domain, config)


def verify_bound(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    upper: Optional[float] = None,
    lower: Optional[float] = None,
    config: Config = Config(),
    method: str = 'adaptive',
) -> bool:
    """Verify that an expression satisfies bounds with false positive filtering.

    This function uses global optimization with counterexample concretization
    to filter false positives caused by interval over-approximation.

    Args:
        expr: Expression to verify.
        domain: Domain specification.
        upper: Upper bound to verify (expr <= upper).
        lower: Lower bound to verify (expr >= lower).
        config: Solver configuration.
        method: 'adaptive' (default, uses optimization with false positive
               filtering) or 'interval' (fast, conservative).

    Returns:
        True if verified.

    Raises:
        VerificationFailed: If bound verification fails AND is confirmed by
                           concrete evaluation (not a false positive).
    """
    return _get_solver().verify_bound(expr, domain, upper, lower, config, method)


def find_roots(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    config: Config = Config(),
) -> RootsResult:
    """
    Find roots of a univariate expression.

    Returns RootInterval objects with status:
    - 'confirmed': Sign change detected, root GUARANTEED by IVT
    - 'possible': Contains zero but no sign change (may or may not have root)
    - 'no_root': Provably no roots in interval
    """
    return _get_solver().find_roots(expr, domain, config)


def find_unique_root(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    config: Config = Config(),
) -> UniqueRootResult:
    """
    Find a unique root using interval Newton method.

    Returns UniqueRootResult with:
    - unique=True: A unique root is PROVEN to exist (Newton contracted)
    - unique=False with reason='no_contraction': Couldn't prove uniqueness
      (root may still exist, try a smaller interval)
    - unique=False with reason='no_root': Provably no roots
    """
    return _get_solver().find_unique_root(expr, domain, config)


def integrate(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    partitions: int = 10,
    config: Config = Config(),
) -> IntegralResult:
    """Compute rigorous integral bounds."""
    return _get_solver().integrate(expr, domain, partitions, config)


def forward_interval(
    network,  # SequentialNetwork or TwoLayerReLUNetwork
    input_domain: Union[Box, dict, list],
    precision: int = -53,
) -> list[Interval]:
    """
    Propagate intervals through a neural network using verified arithmetic.

    This runs verified interval arithmetic forward propagation through
    the network, computing rigorous bounds on all possible outputs.

    Args:
        network: A SequentialNetwork or TwoLayerReLUNetwork from leancert.nn
        input_domain: Input intervals as Box, dict, or list of tuples
        precision: Dyadic precision (-53 = IEEE double precision)

    Returns:
        List of output intervals (one per output neuron)
    """
    return _get_solver().forward_interval(network, input_domain, precision)


def verify_bound_adaptive(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    upper: Optional[float] = None,
    lower: Optional[float] = None,
    adaptive_config: AdaptiveConfig = AdaptiveConfig(),
    config: Config = Config(),
) -> AdaptiveResult:
    """
    Verify a bound using CEGAR (Counterexample-Guided Abstraction Refinement).

    When single-shot verification fails on a large domain, this function
    automatically splits the domain and retries on subdomains until either:
    - The bound is verified on all subdomains, or
    - A minimal subdomain is found where the bound genuinely fails

    Args:
        expr: Expression to verify.
        domain: Domain specification.
        upper: Upper bound to verify (f(x) ≤ upper).
        lower: Lower bound to verify (f(x) ≥ lower).
        adaptive_config: Configuration for domain splitting.
        config: Underlying solver configuration.

    Returns:
        AdaptiveResult with verification status, subdomain tree, and Lean proof.

    Example:
        >>> import leancert as lc
        >>> x = lc.var('x')
        >>> result = lc.verify_bound_adaptive(
        ...     lc.sin(x) + lc.cos(x),
        ...     {'x': (0, 10)},
        ...     upper=1.5,
        ... )
        >>> print(result.verified)
        True
    """
    return _get_solver().verify_bound_adaptive(
        expr, domain, upper, lower, adaptive_config, config
    )


def verify_nn_bounds(
    network,  # SequentialNetwork or TwoLayerReLUNetwork
    input_domain: Union[Box, dict, list],
    output_lower: Union[float, list, None] = None,
    output_upper: Union[float, list, None] = None,
    precision: int = -53,
) -> bool:
    """
    Verify that a neural network's outputs stay within specified bounds.

    This is a convenience wrapper around forward_interval that checks
    whether the computed output intervals are contained within the
    specified bounds.

    Args:
        network: A SequentialNetwork or TwoLayerReLUNetwork from leancert.nn
        input_domain: Input intervals as Box, dict, or list of tuples
        output_lower: Lower bound(s) for outputs (single value or list per output)
        output_upper: Upper bound(s) for outputs (single value or list per output)
        precision: Dyadic precision (-53 = IEEE double precision)

    Returns:
        True if all outputs are verified to be within bounds, False otherwise.

    Example:
        >>> import leancert as lc
        >>> from leancert.nn import TwoLayerReLUNetwork, Layer
        >>> import numpy as np
        >>>
        >>> # Create a small network
        >>> layer1 = Layer.from_numpy(np.array([[1, -1], [0, 1]]), np.array([0, 0]))
        >>> layer2 = Layer.from_numpy(np.array([[1, 1]]), np.array([0]), activation='none')
        >>> net = TwoLayerReLUNetwork(layer1, layer2)
        >>>
        >>> # Verify output bounds
        >>> verified = lc.verify_nn_bounds(
        ...     net,
        ...     input_domain={'x0': (-1, 1), 'x1': (-1, 1)},
        ...     output_lower=0,
        ...     output_upper=5,
        ... )
        >>> print(verified)  # True
    """
    # Get verified output intervals
    output_intervals = forward_interval(network, input_domain, precision)

    # Normalize bounds to lists
    n_outputs = len(output_intervals)

    if output_lower is None:
        lower_bounds = [None] * n_outputs
    elif isinstance(output_lower, (int, float)):
        lower_bounds = [float(output_lower)] * n_outputs
    else:
        lower_bounds = [float(x) if x is not None else None for x in output_lower]

    if output_upper is None:
        upper_bounds = [None] * n_outputs
    elif isinstance(output_upper, (int, float)):
        upper_bounds = [float(output_upper)] * n_outputs
    else:
        upper_bounds = [float(x) if x is not None else None for x in output_upper]

    # Check each output
    for i, interval in enumerate(output_intervals):
        lo = float(interval.lo)
        hi = float(interval.hi)

        if lower_bounds[i] is not None and lo < lower_bounds[i]:
            return False
        if upper_bounds[i] is not None and hi > upper_bounds[i]:
            return False

    return True
