# LeanCert v3 SDK - Adaptive Verification (CEGAR)
# Copyright (c) 2024 LeanCert Contributors. All rights reserved.

"""
Counterexample-Guided Abstraction Refinement (CEGAR) for verified bounds.

This module implements adaptive domain splitting to verify bounds that fail
on the full domain. When a proof fails, it automatically:
1. Extracts the worst-case point from the failure diagnosis
2. Splits the domain along the most influential variable
3. Retries verification on each subdomain
4. Assembles a structured Lean proof from subdomain results

Key Features:
- Multiple splitting strategies (bisect, worst_point, gradient_guided)
- Parallel subdomain verification
- Automatic proof assembly for Lean
- Minimal counterexample isolation
- Progress callbacks for long-running verifications
- Auto-gradient computation for smarter splitting
- Tree visualization for debugging
"""

from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional, Union, Callable, Any, TYPE_CHECKING
from enum import Enum
import concurrent.futures
import threading
import time

if TYPE_CHECKING:
    from .solver import Solver
    from .expr import Expr

from .domain import Interval, Box, normalize_domain
from .config import Config
from .result import Certificate, FailureDiagnosis
from .rational import to_fraction


# Type alias for progress callback
# (current_splits, max_splits, current_depth, verified_count, failed_count) -> None
ProgressCallback = Callable[[int, int, int, int, int], None]


class SplitStrategy(Enum):
    """Strategy for splitting domains during CEGAR refinement."""
    BISECT = "bisect"  # Always split at midpoint
    WORST_POINT = "worst_point"  # Split at the worst-case point
    GRADIENT_GUIDED = "gradient_guided"  # Split along variable with largest gradient
    LARGEST_FIRST = "largest_first"  # Split the largest dimension first
    AUTO = "auto"  # Automatically choose best strategy based on context
    ALGEBRAIC = "algebraic"  # Use algebraic structure (critical points, monotonicity)


@dataclass
class Subdomain:
    """
    A subdomain in the CEGAR search tree.

    Attributes:
        box: The domain box for this subdomain
        parent_id: ID of the parent subdomain (None for root)
        split_var: Variable that was split to create this subdomain
        split_side: 'left' or 'right' indicating which half
        depth: Depth in the search tree
        id: Unique identifier for this subdomain
    """
    box: Box
    parent_id: Optional[int] = None
    split_var: Optional[str] = None
    split_side: Optional[str] = None  # 'left' or 'right'
    depth: int = 0
    id: int = 0

    def id_str(self) -> str:
        """Generate a human-readable ID for this subdomain."""
        if self.parent_id is None:
            return "root"
        return f"d{self.depth}_{self.split_var}_{self.split_side}"

    def volume(self) -> float:
        """Compute the volume of this subdomain."""
        vol = 1.0
        for name in self.box.var_order():
            vol *= float(self.box[name].width())
        return vol


@dataclass
class SubdomainResult:
    """
    Result of verifying a bound on a single subdomain.

    Attributes:
        subdomain: The subdomain that was verified
        verified: Whether the bound holds on this subdomain
        diagnosis: Failure diagnosis if verification failed
        proof_fragment: Lean proof fragment for this subdomain
        verification_time_ms: Time taken for verification in milliseconds
        gradient_info: Computed gradient information (if available)
    """
    subdomain: Subdomain
    verified: bool
    diagnosis: Optional[FailureDiagnosis] = None
    proof_fragment: Optional[str] = None
    iterations_used: int = 0
    verification_time_ms: float = 0.0
    gradient_info: Optional[dict[str, float]] = None


@dataclass
class AdaptiveConfig:
    """
    Configuration for adaptive verification.

    Attributes:
        max_splits: Maximum number of domain splits (controls tree size)
        max_depth: Maximum depth of the search tree
        strategy: Splitting strategy to use
        parallel: Whether to verify subdomains in parallel
        max_workers: Maximum number of parallel workers (None = auto)
        min_width: Minimum interval width before stopping splits
        min_volume: Minimum domain volume before stopping splits
        timeout_per_subdomain_ms: Timeout for each subdomain verification
        compute_gradients: Whether to compute gradients for smarter splitting
        progress_callback: Optional callback for progress updates
        progress_interval_ms: Minimum interval between progress callbacks
    """
    max_splits: int = 64
    max_depth: int = 10
    strategy: SplitStrategy = SplitStrategy.WORST_POINT
    parallel: bool = True
    max_workers: Optional[int] = None
    min_width: float = 1e-10
    min_volume: Optional[float] = None  # If set, stop when volume below this
    timeout_per_subdomain_ms: int = 10000
    compute_gradients: bool = False  # Enable auto-gradient computation
    progress_callback: Optional[ProgressCallback] = None
    progress_interval_ms: int = 100  # Minimum ms between callbacks

    @classmethod
    def quick(cls) -> 'AdaptiveConfig':
        """Quick verification with limited splitting."""
        return cls(max_splits=16, max_depth=5, parallel=True)

    @classmethod
    def thorough(cls) -> 'AdaptiveConfig':
        """Thorough verification with more splitting allowed."""
        return cls(max_splits=256, max_depth=15, parallel=True)

    @classmethod
    def exhaustive(cls) -> 'AdaptiveConfig':
        """Exhaustive verification for difficult problems."""
        return cls(max_splits=1024, max_depth=20, parallel=True, min_width=1e-15)

    @classmethod
    def with_progress(cls, callback: ProgressCallback, **kwargs) -> 'AdaptiveConfig':
        """Create config with a progress callback."""
        return cls(progress_callback=callback, **kwargs)


@dataclass
class AdaptiveResult:
    """
    Result of adaptive (CEGAR) bound verification.

    This is returned when using verify_bound_adaptive(). It contains:
    - Whether the bound was verified on all subdomains
    - The tree of subdomains explored
    - A structured Lean proof combining subdomain proofs
    - Minimal counterexample if verification failed

    Attributes:
        verified: True if bound holds on ALL subdomains
        subdomains: List of all subdomains explored
        results: Results for each subdomain
        total_splits: Total number of domain splits performed
        failing_subdomain: Minimal subdomain where bound genuinely fails (if any)
        lean_proof: Generated Lean proof code
        certificate: Verification certificate
        total_time_ms: Total verification time in milliseconds
        unverified_volume: Total volume of unverified regions
    """
    verified: bool
    subdomains: list[Subdomain] = field(default_factory=list)
    results: list[SubdomainResult] = field(default_factory=list)
    total_splits: int = 0
    failing_subdomain: Optional[Subdomain] = None
    lean_proof: Optional[str] = None
    certificate: Optional[Certificate] = None
    total_time_ms: float = 0.0
    unverified_volume: float = 0.0

    @property
    def verified_subdomains(self) -> list[SubdomainResult]:
        """Return only successfully verified subdomains."""
        return [r for r in self.results if r.verified]

    @property
    def failed_subdomains(self) -> list[SubdomainResult]:
        """Return subdomains where verification failed."""
        return [r for r in self.results if not r.verified]

    @property
    def num_verified(self) -> int:
        """Number of subdomains verified."""
        return len(self.verified_subdomains)

    @property
    def num_failed(self) -> int:
        """Number of subdomains that failed."""
        return len(self.failed_subdomains)

    @property
    def verified_volume(self) -> float:
        """Total volume of verified regions."""
        return sum(r.subdomain.volume() for r in self.verified_subdomains)

    def summary(self) -> str:
        """Return a human-readable summary."""
        status = "VERIFIED" if self.verified else "FAILED"
        lines = [
            f"AdaptiveResult: {status}",
            f"  Subdomains explored: {len(self.subdomains)}",
            f"  Verified: {self.num_verified}",
            f"  Failed: {self.num_failed}",
            f"  Total splits: {self.total_splits}",
            f"  Time: {self.total_time_ms:.1f}ms",
        ]
        if self.failing_subdomain:
            lines.append(f"  Minimal failing region: {self.failing_subdomain.box}")
        if self.unverified_volume > 0:
            lines.append(f"  Unverified volume: {self.unverified_volume:.2e}")
        return "\n".join(lines)

    def tree_visualization(self, max_depth: Optional[int] = None) -> str:
        """
        Generate ASCII tree visualization of the subdomain exploration.

        Args:
            max_depth: Maximum depth to display (None = all)

        Returns:
            ASCII tree string
        """
        return SubdomainTreeVisualizer.visualize(
            self.subdomains, self.results, max_depth
        )

    def __repr__(self) -> str:
        status = "VERIFIED" if self.verified else "FAILED"
        return f"AdaptiveResult({status}, {len(self.subdomains)} subdomains, {self.total_splits} splits)"


class SubdomainTreeVisualizer:
    """Generates ASCII tree visualizations of subdomain exploration."""

    @staticmethod
    def visualize(
        subdomains: list[Subdomain],
        results: list[SubdomainResult],
        max_depth: Optional[int] = None,
    ) -> str:
        """Generate ASCII tree visualization."""
        if not subdomains:
            return "(empty tree)"

        # Build result lookup
        result_map = {id(r.subdomain.box): r for r in results}

        # Build tree structure
        children: dict[Optional[int], list[Subdomain]] = {}
        for sd in subdomains:
            if sd.parent_id not in children:
                children[sd.parent_id] = []
            children[sd.parent_id].append(sd)

        lines = []
        SubdomainTreeVisualizer._visualize_node(
            subdomains[0] if subdomains else None,
            children,
            result_map,
            lines,
            "",
            True,
            max_depth,
            0,
        )
        return "\n".join(lines)

    @staticmethod
    def _visualize_node(
        node: Optional[Subdomain],
        children: dict[Optional[int], list[Subdomain]],
        result_map: dict,
        lines: list[str],
        prefix: str,
        is_last: bool,
        max_depth: Optional[int],
        current_depth: int,
    ):
        if node is None:
            return

        if max_depth is not None and current_depth > max_depth:
            lines.append(f"{prefix}{'└── ' if is_last else '├── '}...")
            return

        # Get result for this node
        result = result_map.get(id(node.box))
        status = "✓" if result and result.verified else "✗" if result else "?"

        # Format node info
        if node.parent_id is None:
            node_str = f"[root] {status}"
        else:
            var = node.split_var or "?"
            side = node.split_side or "?"
            node_str = f"[{var}:{side}] {status}"

        # Add volume info for failed nodes
        if result and not result.verified:
            vol = node.volume()
            node_str += f" (vol={vol:.2e})"

        connector = "└── " if is_last else "├── "
        lines.append(f"{prefix}{connector}{node_str}")

        # Process children
        node_children = children.get(node.id, [])
        child_prefix = prefix + ("    " if is_last else "│   ")

        for i, child in enumerate(node_children):
            is_last_child = (i == len(node_children) - 1)
            SubdomainTreeVisualizer._visualize_node(
                child,
                children,
                result_map,
                lines,
                child_prefix,
                is_last_child,
                max_depth,
                current_depth + 1,
            )


class GradientEstimator:
    """
    Estimates gradients for smarter splitting decisions.

    Uses finite differences at the box center to estimate
    which variables have the largest gradient magnitude.
    """

    @staticmethod
    def estimate_gradients(
        solver: 'Solver',
        expr: 'Expr',
        box: Box,
        config: Config,
        delta: float = 1e-6,
    ) -> dict[str, float]:
        """
        Estimate gradient magnitudes at the center of a box.

        Args:
            solver: LeanCert solver
            expr: Expression to analyze
            box: Domain box
            config: Solver configuration
            delta: Step size for finite differences

        Returns:
            Dictionary mapping variable names to gradient magnitudes
        """
        var_names = box.var_order()
        gradients = {}

        # Compute center point
        center = {name: float(box[name].midpoint()) for name in var_names}

        # Evaluate at center
        try:
            center_val = float(expr.evaluate(center))
        except Exception:
            # If evaluation fails, return zeros
            return {name: 0.0 for name in var_names}

        # Finite difference for each variable
        for name in var_names:
            try:
                # Forward difference
                perturbed = center.copy()
                perturbed[name] = center[name] + delta

                perturbed_val = float(expr.evaluate(perturbed))
                gradient = (perturbed_val - center_val) / delta
                gradients[name] = abs(gradient)
            except Exception:
                gradients[name] = 0.0

        return gradients


@dataclass
class SplitCandidate:
    """A candidate split point with its expected improvement score."""
    variable: str
    point: Fraction
    score: float  # Higher = better expected interval tightening
    reason: str  # Why this split was suggested


class AlgebraicAnalyzer:
    """
    Analyzes algebraic structure of expressions to find optimal split points.

    Uses:
    - Monotonicity detection (where derivatives don't change sign)
    - Polynomial critical points (where f'(x) = 0)
    - Zero crossings of derivatives
    - Interval dependency analysis

    This eliminates the dependency problem without user intervention and
    beats affine arithmetic alone in many nonlinear cases.
    """

    @staticmethod
    def analyze_expression(
        expr: 'Expr',
        box: Box,
        num_samples: int = 20,
    ) -> list[SplitCandidate]:
        """
        Analyze an expression to find optimal split points.

        Args:
            expr: Expression to analyze
            box: Domain box
            num_samples: Number of sample points for numerical analysis

        Returns:
            List of SplitCandidate objects sorted by score (best first)
        """
        candidates = []
        var_names = box.var_order()

        for var_name in var_names:
            # Analyze this variable
            var_candidates = AlgebraicAnalyzer._analyze_variable(
                expr, box, var_name, num_samples
            )
            candidates.extend(var_candidates)

        # Sort by score (highest first)
        candidates.sort(key=lambda c: c.score, reverse=True)
        return candidates

    @staticmethod
    def _analyze_variable(
        expr: 'Expr',
        box: Box,
        var_name: str,
        num_samples: int,
    ) -> list[SplitCandidate]:
        """Analyze a single variable for split candidates."""
        candidates = []
        interval = box[var_name]
        lo, hi = float(interval.lo), float(interval.hi)
        width = hi - lo

        if width <= 0:
            return candidates

        # Sample points along this variable
        samples = [lo + (hi - lo) * i / (num_samples - 1) for i in range(num_samples)]

        # Compute function values and estimate derivatives
        values = []
        derivatives = []

        # Create evaluation context with other variables at midpoint
        base_point = {
            name: float(box[name].midpoint())
            for name in box.var_order()
        }

        try:
            for x in samples:
                point = base_point.copy()
                point[var_name] = x
                val = float(expr.evaluate(point))
                values.append(val)

            # Estimate derivatives using central differences
            for i in range(1, len(samples) - 1):
                dx = samples[i + 1] - samples[i - 1]
                if dx > 0:
                    deriv = (values[i + 1] - values[i - 1]) / dx
                    derivatives.append((samples[i], deriv))
        except Exception:
            # If evaluation fails, return empty
            return candidates

        # Find critical points (where derivative ≈ 0)
        critical_points = AlgebraicAnalyzer._find_critical_points(
            derivatives, lo, hi
        )
        for cp in critical_points:
            candidates.append(SplitCandidate(
                variable=var_name,
                point=to_fraction(cp),
                score=1.0,  # High priority - extrema
                reason="critical_point"
            ))

        # Find sign changes in derivative (inflection-like behavior)
        sign_changes = AlgebraicAnalyzer._find_derivative_sign_changes(
            derivatives, lo, hi
        )
        for sc in sign_changes:
            candidates.append(SplitCandidate(
                variable=var_name,
                point=to_fraction(sc),
                score=0.8,  # Medium-high priority
                reason="derivative_sign_change"
            ))

        # Analyze curvature (second derivative) for dependency problem
        high_curvature = AlgebraicAnalyzer._find_high_curvature_regions(
            samples, values, lo, hi
        )
        for hc in high_curvature:
            candidates.append(SplitCandidate(
                variable=var_name,
                point=to_fraction(hc),
                score=0.6,  # Medium priority
                reason="high_curvature"
            ))

        # For products like x*(1-x), find points where both factors change sign
        # or where the dependency is strongest (at 0.5 for this example)
        dependency_points = AlgebraicAnalyzer._find_dependency_points(
            samples, values, lo, hi
        )
        for dp in dependency_points:
            candidates.append(SplitCandidate(
                variable=var_name,
                point=to_fraction(dp),
                score=0.7,  # Medium-high priority
                reason="dependency_reduction"
            ))

        return candidates

    @staticmethod
    def _find_critical_points(
        derivatives: list[tuple[float, float]],
        lo: float,
        hi: float,
        threshold: float = 0.1,
    ) -> list[float]:
        """Find approximate critical points where f'(x) ≈ 0."""
        if not derivatives:
            return []

        # Normalize threshold by derivative range
        deriv_values = [d for _, d in derivatives]
        deriv_range = max(abs(max(deriv_values)), abs(min(deriv_values)))
        if deriv_range == 0:
            return []

        normalized_threshold = threshold * deriv_range
        critical = []

        # Look for sign changes or near-zero derivatives
        for i in range(len(derivatives) - 1):
            x1, d1 = derivatives[i]
            x2, d2 = derivatives[i + 1]

            # Sign change in derivative
            if d1 * d2 < 0:
                # Linear interpolation to find zero crossing
                t = abs(d1) / (abs(d1) + abs(d2))
                cp = x1 + t * (x2 - x1)
                # Ensure it's not too close to boundaries
                margin = (hi - lo) * 0.1
                if lo + margin < cp < hi - margin:
                    critical.append(cp)

            # Near-zero derivative
            elif abs(d1) < normalized_threshold:
                margin = (hi - lo) * 0.1
                if lo + margin < x1 < hi - margin:
                    critical.append(x1)

        return critical

    @staticmethod
    def _find_derivative_sign_changes(
        derivatives: list[tuple[float, float]],
        lo: float,
        hi: float,
    ) -> list[float]:
        """Find points where the derivative changes sign."""
        if len(derivatives) < 2:
            return []

        changes = []
        for i in range(len(derivatives) - 1):
            x1, d1 = derivatives[i]
            x2, d2 = derivatives[i + 1]

            if d1 * d2 < 0:  # Sign change
                # Linear interpolation
                t = abs(d1) / (abs(d1) + abs(d2))
                cp = x1 + t * (x2 - x1)
                margin = (hi - lo) * 0.1
                if lo + margin < cp < hi - margin:
                    changes.append(cp)

        return changes

    @staticmethod
    def _find_high_curvature_regions(
        samples: list[float],
        values: list[float],
        lo: float,
        hi: float,
        top_k: int = 2,
    ) -> list[float]:
        """Find regions of high curvature (large second derivative)."""
        if len(samples) < 3:
            return []

        # Estimate second derivatives using finite differences
        curvatures = []
        for i in range(1, len(samples) - 1):
            dx = samples[i + 1] - samples[i - 1]
            if dx > 0:
                # Second derivative approximation
                d2 = (values[i + 1] - 2 * values[i] + values[i - 1]) / (dx / 2) ** 2
                curvatures.append((samples[i], abs(d2)))

        if not curvatures:
            return []

        # Sort by curvature magnitude
        curvatures.sort(key=lambda x: x[1], reverse=True)

        # Return top-k points that aren't too close to boundaries
        result = []
        margin = (hi - lo) * 0.1
        for x, _ in curvatures[:top_k * 2]:  # Check more in case some are near boundary
            if lo + margin < x < hi - margin:
                result.append(x)
                if len(result) >= top_k:
                    break

        return result

    @staticmethod
    def _find_dependency_points(
        samples: list[float],
        values: list[float],
        lo: float,
        hi: float,
    ) -> list[float]:
        """
        Find points where splitting reduces interval dependency.

        For expressions like x*(1-x), the dependency problem is worst
        at the midpoint. Splitting there reduces the dependency.
        """
        if len(samples) < 3:
            return []

        # Compute "dependency score" as variance reduction potential
        # High variance in the function suggests splitting could help

        mid_idx = len(samples) // 2
        left_values = values[:mid_idx]
        right_values = values[mid_idx:]

        def variance(vs):
            if len(vs) < 2:
                return 0
            mean = sum(vs) / len(vs)
            return sum((v - mean) ** 2 for v in vs) / len(vs)

        total_var = variance(values)
        left_var = variance(left_values)
        right_var = variance(right_values)

        # If splitting reduces total variance significantly, suggest midpoint
        if total_var > 0 and (left_var + right_var) / 2 < total_var * 0.8:
            mid = (lo + hi) / 2
            return [mid]

        return []

    @staticmethod
    def get_best_split(
        expr: 'Expr',
        box: Box,
        num_samples: int = 20,
    ) -> Optional[SplitCandidate]:
        """Get the single best split candidate."""
        candidates = AlgebraicAnalyzer.analyze_expression(expr, box, num_samples)
        return candidates[0] if candidates else None


class DomainSplitter:
    """
    Handles domain splitting strategies for CEGAR.
    """

    @staticmethod
    def split_box(
        box: Box,
        strategy: SplitStrategy,
        diagnosis: Optional[FailureDiagnosis] = None,
        gradient_info: Optional[dict[str, float]] = None,
        expr: Optional['Expr'] = None,
        algebraic_candidate: Optional[SplitCandidate] = None,
    ) -> tuple[Box, Box, str]:
        """
        Split a box into two sub-boxes.

        Args:
            box: The box to split
            strategy: Splitting strategy
            diagnosis: Failure diagnosis (for worst_point strategy)
            gradient_info: Gradient magnitudes per variable (for gradient_guided)
            expr: Expression (for ALGEBRAIC strategy)
            algebraic_candidate: Pre-computed algebraic split candidate

        Returns:
            Tuple of (left_box, right_box, split_variable_name)
        """
        var_names = box.var_order()

        # AUTO strategy: choose based on available info
        if strategy == SplitStrategy.AUTO:
            if algebraic_candidate:
                strategy = SplitStrategy.ALGEBRAIC
            elif gradient_info and any(g > 0 for g in gradient_info.values()):
                strategy = SplitStrategy.GRADIENT_GUIDED
            elif diagnosis and diagnosis.worst_point:
                strategy = SplitStrategy.WORST_POINT
            else:
                strategy = SplitStrategy.LARGEST_FIRST

        # Handle ALGEBRAIC strategy
        if strategy == SplitStrategy.ALGEBRAIC:
            if algebraic_candidate:
                split_var = algebraic_candidate.variable
                split_point = algebraic_candidate.point
                interval = box[split_var]
                # Clamp to interval and avoid degenerate splits
                split_point = max(interval.lo, min(interval.hi, split_point))
                margin = interval.width() / 10
                if split_point <= interval.lo + margin:
                    split_point = interval.lo + interval.width() / 4
                elif split_point >= interval.hi - margin:
                    split_point = interval.hi - interval.width() / 4
            elif expr:
                # Compute algebraic candidate on the fly
                candidate = AlgebraicAnalyzer.get_best_split(expr, box)
                if candidate:
                    split_var = candidate.variable
                    split_point = candidate.point
                    interval = box[split_var]
                    split_point = max(interval.lo, min(interval.hi, split_point))
                    margin = interval.width() / 10
                    if split_point <= interval.lo + margin:
                        split_point = interval.lo + interval.width() / 4
                    elif split_point >= interval.hi - margin:
                        split_point = interval.hi - interval.width() / 4
                else:
                    # Fall back to largest first
                    split_var = max(var_names, key=lambda v: float(box[v].width()))
                    split_point = box[split_var].midpoint()
            else:
                # Fall back to largest first
                split_var = max(var_names, key=lambda v: float(box[v].width()))
                split_point = box[split_var].midpoint()

            # Create boxes for ALGEBRAIC strategy
            interval = box[split_var]
            left_intervals = {}
            right_intervals = {}
            for name in var_names:
                if name == split_var:
                    left_intervals[name] = Interval(interval.lo, split_point)
                    right_intervals[name] = Interval(split_point, interval.hi)
                else:
                    left_intervals[name] = box[name]
                    right_intervals[name] = box[name]
            return Box(left_intervals), Box(right_intervals), split_var

        # Choose variable to split for other strategies
        if strategy == SplitStrategy.BISECT:
            # Split the first variable
            split_var = var_names[0]
        elif strategy == SplitStrategy.WORST_POINT and diagnosis:
            # Split the variable with the worst point closest to boundary
            split_var = DomainSplitter._find_worst_point_var(box, diagnosis)
        elif strategy == SplitStrategy.GRADIENT_GUIDED and gradient_info:
            # Split along variable with largest gradient magnitude
            split_var = max(gradient_info.keys(), key=lambda v: abs(gradient_info.get(v, 0)))
        elif strategy == SplitStrategy.LARGEST_FIRST:
            # Split the dimension with largest width
            split_var = max(var_names, key=lambda v: float(box[v].width()))
        else:
            # Default: split largest dimension
            split_var = max(var_names, key=lambda v: float(box[v].width()))

        # Compute split point
        interval = box[split_var]
        if strategy == SplitStrategy.WORST_POINT and diagnosis and split_var in diagnosis.worst_point:
            # Split at the worst point
            worst = to_fraction(diagnosis.worst_point[split_var])
            # Clamp to interval
            split_point = max(interval.lo, min(interval.hi, worst))
            # Avoid degenerate splits
            if split_point == interval.lo:
                split_point = interval.lo + interval.width() / 4
            elif split_point == interval.hi:
                split_point = interval.hi - interval.width() / 4
        else:
            # Split at midpoint
            split_point = interval.midpoint()

        # Create left and right boxes
        left_intervals = {}
        right_intervals = {}
        for name in var_names:
            if name == split_var:
                left_intervals[name] = Interval(interval.lo, split_point)
                right_intervals[name] = Interval(split_point, interval.hi)
            else:
                left_intervals[name] = box[name]
                right_intervals[name] = box[name]

        return Box(left_intervals), Box(right_intervals), split_var

    @staticmethod
    def _find_worst_point_var(box: Box, diagnosis: FailureDiagnosis) -> str:
        """Find which variable's worst point is most critical."""
        var_names = box.var_order()

        # For each variable, compute how close the worst point is to boundaries
        # Prefer splitting variables where the worst point is far from center
        best_var = var_names[0]
        best_score = 0.0

        for name in var_names:
            if name in diagnosis.worst_point:
                interval = box[name]
                worst = diagnosis.worst_point[name]
                width = float(interval.width())
                if width > 0:
                    mid = float(interval.midpoint())
                    # Score: how far from center (0 = at center, 1 = at boundary)
                    score = abs(worst - mid) / (width / 2) if width > 0 else 0
                    if score > best_score:
                        best_score = score
                        best_var = name

        return best_var

    @staticmethod
    def should_continue_splitting(
        box: Box,
        config: AdaptiveConfig,
        depth: int,
        total_splits: int,
    ) -> bool:
        """Check if we should continue splitting this box."""
        # Check depth limit
        if depth >= config.max_depth:
            return False

        # Check total splits limit
        if total_splits >= config.max_splits:
            return False

        # Check minimum width
        for name in box.var_order():
            if float(box[name].width()) < config.min_width:
                return False

        # Check minimum volume
        if config.min_volume is not None:
            volume = 1.0
            for name in box.var_order():
                volume *= float(box[name].width())
            if volume < config.min_volume:
                return False

        return True


class LeanProofAssembler:
    """
    Assembles Lean proof code from subdomain verification results.
    """

    @staticmethod
    def assemble_bound_proof(
        expr_lean: str,
        bound_type: str,  # 'upper' or 'lower'
        bound_value: float,
        results: list[SubdomainResult],
        full_domain: Box,
    ) -> str:
        """
        Assemble a structured Lean proof from subdomain results.

        Generates proofs like:

        ```lean
        theorem bound_on_domain : ∀ x ∈ Set.Icc 0 10, f x ≤ 1.5 := by
          intro x hx
          rcases interval_cases hx with h1 | h2 | h3
          · -- x ∈ [0, 3.33]
            interval_decide
          · -- x ∈ [3.33, 6.67]
            interval_decide
          · -- x ∈ [6.67, 10]
            interval_decide
        ```
        """
        lines = []
        verified_results = [r for r in results if r.verified]

        if not verified_results:
            lines.append("-- No subdomains were verified")
            return "\n".join(lines)

        # Header
        lines.append("-- CEGAR-generated proof via domain splitting")
        lines.append(f"-- Expression: {expr_lean}")
        lines.append(f"-- Bound type: {bound_type}")
        lines.append(f"-- Bound value: {bound_value}")
        lines.append(f"-- Subdomains verified: {len(verified_results)}")
        lines.append("")

        # Generate domain quantifiers
        var_names = full_domain.var_order()
        is_multivariate = len(var_names) > 1

        if is_multivariate:
            quantifiers = LeanProofAssembler._multivar_quantifiers(full_domain)
            bound_expr = f"{bound_value} ≤ {expr_lean}" if bound_type == 'lower' else f"{expr_lean} ≤ {bound_value}"
            lines.append(f"theorem adaptive_bound_proof :")
            lines.append(f"    {quantifiers}")
            lines.append(f"    {bound_expr} := by")
        else:
            var = var_names[0]
            interval = full_domain[var]
            lo, hi = float(interval.lo), float(interval.hi)
            bound_expr = f"{bound_value} ≤ {expr_lean}" if bound_type == 'lower' else f"{expr_lean} ≤ {bound_value}"
            lines.append(f"theorem adaptive_bound_proof :")
            lines.append(f"    ∀ {var} ∈ Set.Icc {lo} {hi}, {bound_expr} := by")

        # Generate proof body
        lines.append("  intro x hx")

        if len(verified_results) == 1:
            # Single subdomain - direct proof
            lines.append("  interval_decide")
        else:
            # Multiple subdomains - case split
            n = len(verified_results)
            case_labels = " | ".join([f"h{i+1}" for i in range(n)])
            lines.append(f"  rcases interval_cases hx with {case_labels}")

            for i, result in enumerate(verified_results):
                subdomain = result.subdomain
                lines.append(f"  · -- Subdomain {i+1}: {LeanProofAssembler._box_comment(subdomain.box)}")
                lines.append(f"    interval_decide")

        # Add helper lemma for interval union
        lines.append("")
        lines.append("-- Helper: interval_cases splits the domain")
        lines.append("-- theorem interval_cases (hx : x ∈ Set.Icc a c) :")
        lines.append("--   x ∈ Set.Icc a b ∨ x ∈ Set.Icc b c := ...")

        return "\n".join(lines)

    @staticmethod
    def _multivar_quantifiers(box: Box) -> str:
        """Generate nested forall quantifiers for multivariate domain."""
        var_names = box.var_order()
        parts = []
        for name in var_names:
            interval = box[name]
            lo, hi = float(interval.lo), float(interval.hi)
            parts.append(f"∀ {name} ∈ Set.Icc {lo} {hi},")
        return " ".join(parts)

    @staticmethod
    def _box_comment(box: Box) -> str:
        """Generate human-readable comment for a box."""
        var_names = box.var_order()
        parts = []
        for name in var_names:
            interval = box[name]
            lo, hi = float(interval.lo), float(interval.hi)
            parts.append(f"{name} ∈ [{lo:.4f}, {hi:.4f}]")
        return ", ".join(parts)


class CEGARVerifier:
    """
    Counterexample-Guided Abstraction Refinement verifier.

    This class implements the main CEGAR loop:
    1. Try to verify bound on current domain
    2. If verification fails, extract counterexample (worst point)
    3. Split domain based on counterexample
    4. Recursively verify on subdomains
    5. Assemble proof from subdomain results
    """

    def __init__(
        self,
        solver: 'Solver',
        adaptive_config: AdaptiveConfig = AdaptiveConfig(),
        solver_config: Config = Config(),
    ):
        """
        Initialize the CEGAR verifier.

        Args:
            solver: The LeanCert solver to use for verification
            adaptive_config: Configuration for adaptive splitting
            solver_config: Configuration for the underlying solver
        """
        self.solver = solver
        self.adaptive_config = adaptive_config
        self.solver_config = solver_config

        # State tracking
        self._subdomains: list[Subdomain] = []
        self._results: list[SubdomainResult] = []
        self._total_splits = 0
        self._subdomain_id = 0
        self._lock = threading.Lock()
        self._last_progress_time = 0.0
        self._start_time = 0.0

    def verify_upper_bound(
        self,
        expr: 'Expr',
        domain: Union[Interval, Box, tuple, dict],
        bound: float,
    ) -> AdaptiveResult:
        """
        Verify f(x) ≤ bound using CEGAR.

        Args:
            expr: Expression to verify
            domain: Domain to verify over
            bound: Upper bound to verify

        Returns:
            AdaptiveResult with verification status and proof
        """
        return self._verify_bound(expr, domain, upper=bound, lower=None)

    def verify_lower_bound(
        self,
        expr: 'Expr',
        domain: Union[Interval, Box, tuple, dict],
        bound: float,
    ) -> AdaptiveResult:
        """
        Verify f(x) ≥ bound using CEGAR.

        Args:
            expr: Expression to verify
            domain: Domain to verify over
            bound: Lower bound to verify

        Returns:
            AdaptiveResult with verification status and proof
        """
        return self._verify_bound(expr, domain, upper=None, lower=bound)

    def _verify_bound(
        self,
        expr: 'Expr',
        domain: Union[Interval, Box, tuple, dict],
        upper: Optional[float],
        lower: Optional[float],
    ) -> AdaptiveResult:
        """Main CEGAR verification loop."""
        self._start_time = time.time()

        # Reset state
        self._subdomains = []
        self._results = []
        self._total_splits = 0
        self._subdomain_id = 0

        # Normalize domain
        box = normalize_domain(domain)

        # Create root subdomain
        root = Subdomain(box=box, depth=0, id=0)
        self._subdomains.append(root)

        if self.adaptive_config.parallel:
            self._verify_parallel(expr, box, upper, lower)
        else:
            self._verify_sequential(expr, box, upper, lower)

        # Compute final results
        total_time = (time.time() - self._start_time) * 1000
        leaf_results = self._get_leaf_results()
        all_verified = all(r.verified for r in leaf_results)

        # Find minimal failing subdomain and compute unverified volume
        failing_subdomain = None
        unverified_volume = 0.0
        if not all_verified:
            failed = [r for r in leaf_results if not r.verified]
            if failed:
                failing_subdomain = min(
                    [r.subdomain for r in failed],
                    key=lambda s: s.volume()
                )
                unverified_volume = sum(r.subdomain.volume() for r in failed)

        # Assemble Lean proof
        expr_lean = self._expr_to_lean_simple(expr)
        bound_type = 'upper' if upper is not None else 'lower'
        bound_value = upper if upper is not None else lower
        lean_proof = LeanProofAssembler.assemble_bound_proof(
            expr_lean,
            bound_type,
            bound_value,
            [r for r in leaf_results if r.verified],
            box,
        )

        # Create certificate
        cert = Certificate(
            operation='verify_adaptive',
            expr_json=expr.compile(box.var_order()),
            domain_json=box.to_kernel_list(),
            result_json={
                'verified': all_verified,
                'num_subdomains': len(leaf_results),
                'num_splits': self._total_splits,
                'bound_type': bound_type,
                'bound_value': bound_value,
                'total_time_ms': total_time,
            },
            verified=all_verified,
            lean_version="4.24.0",
            leancert_version="0.3.0",
        )

        return AdaptiveResult(
            verified=all_verified,
            subdomains=self._subdomains,
            results=leaf_results,
            total_splits=self._total_splits,
            failing_subdomain=failing_subdomain,
            lean_proof=lean_proof,
            certificate=cert,
            total_time_ms=total_time,
            unverified_volume=unverified_volume,
        )

    def _verify_sequential(
        self,
        expr: 'Expr',
        box: Box,
        upper: Optional[float],
        lower: Optional[float],
    ):
        """Sequential verification loop."""
        queue: list[Subdomain] = [self._subdomains[0]]

        while queue:
            subdomain = queue.pop(0)
            self._process_subdomain(expr, subdomain, upper, lower, queue)

    def _verify_parallel(
        self,
        expr: 'Expr',
        box: Box,
        upper: Optional[float],
        lower: Optional[float],
    ):
        """Parallel verification loop."""
        max_workers = self.adaptive_config.max_workers
        if max_workers is None:
            max_workers = min(8, (self.adaptive_config.max_splits + 1))

        # Start with root
        pending: list[Subdomain] = [self._subdomains[0]]
        futures: dict[concurrent.futures.Future, Subdomain] = {}

        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            while pending or futures:
                # Submit new work
                while pending and len(futures) < max_workers:
                    subdomain = pending.pop(0)
                    future = executor.submit(
                        self._verify_subdomain, expr, subdomain, upper, lower
                    )
                    futures[future] = subdomain

                if not futures:
                    break

                # Wait for any completion
                done, _ = concurrent.futures.wait(
                    futures.keys(),
                    timeout=0.1,
                    return_when=concurrent.futures.FIRST_COMPLETED,
                )

                for future in done:
                    subdomain = futures.pop(future)
                    try:
                        result = future.result()
                    except Exception as e:
                        result = SubdomainResult(
                            subdomain=subdomain,
                            verified=False,
                            diagnosis=None,
                        )

                    with self._lock:
                        self._results.append(result)

                    if result.verified:
                        self._report_progress()
                        continue

                    # Check if we should split
                    with self._lock:
                        should_split = DomainSplitter.should_continue_splitting(
                            subdomain.box,
                            self.adaptive_config,
                            subdomain.depth,
                            self._total_splits,
                        )

                    if not should_split:
                        self._report_progress()
                        continue

                    # Split and add children
                    gradient_info = None
                    algebraic_candidate = None

                    if self.adaptive_config.compute_gradients:
                        gradient_info = GradientEstimator.estimate_gradients(
                            self.solver, expr, subdomain.box, self.solver_config
                        )

                    # Compute algebraic analysis for ALGEBRAIC or AUTO strategies
                    strategy = self.adaptive_config.strategy
                    if strategy in (SplitStrategy.ALGEBRAIC, SplitStrategy.AUTO):
                        algebraic_candidate = AlgebraicAnalyzer.get_best_split(
                            expr, subdomain.box
                        )

                    if strategy == SplitStrategy.AUTO:
                        if algebraic_candidate and algebraic_candidate.score >= 0.5:
                            strategy = SplitStrategy.ALGEBRAIC
                        elif gradient_info and any(g > 0 for g in gradient_info.values()):
                            strategy = SplitStrategy.GRADIENT_GUIDED

                    left_box, right_box, split_var = DomainSplitter.split_box(
                        subdomain.box,
                        strategy,
                        result.diagnosis,
                        gradient_info,
                        expr=expr,
                        algebraic_candidate=algebraic_candidate,
                    )

                    with self._lock:
                        self._total_splits += 1
                        self._results.remove(result)

                        self._subdomain_id += 1
                        left = Subdomain(
                            box=left_box,
                            parent_id=subdomain.id,
                            split_var=split_var,
                            split_side='left',
                            depth=subdomain.depth + 1,
                            id=self._subdomain_id,
                        )

                        self._subdomain_id += 1
                        right = Subdomain(
                            box=right_box,
                            parent_id=subdomain.id,
                            split_var=split_var,
                            split_side='right',
                            depth=subdomain.depth + 1,
                            id=self._subdomain_id,
                        )

                        self._subdomains.extend([left, right])

                    pending.extend([left, right])
                    self._report_progress()

    def _process_subdomain(
        self,
        expr: 'Expr',
        subdomain: Subdomain,
        upper: Optional[float],
        lower: Optional[float],
        queue: list[Subdomain],
    ):
        """Process a single subdomain in sequential mode."""
        result = self._verify_subdomain(expr, subdomain, upper, lower)
        self._results.append(result)

        if result.verified:
            self._report_progress()
            return

        # Check if we should split
        if not DomainSplitter.should_continue_splitting(
            subdomain.box,
            self.adaptive_config,
            subdomain.depth,
            self._total_splits,
        ):
            self._report_progress()
            return

        # Compute gradients if enabled
        gradient_info = None
        algebraic_candidate = None

        if self.adaptive_config.compute_gradients:
            gradient_info = GradientEstimator.estimate_gradients(
                self.solver, expr, subdomain.box, self.solver_config
            )

        # Compute algebraic analysis for ALGEBRAIC or AUTO strategies
        strategy = self.adaptive_config.strategy
        if strategy in (SplitStrategy.ALGEBRAIC, SplitStrategy.AUTO):
            algebraic_candidate = AlgebraicAnalyzer.get_best_split(
                expr, subdomain.box
            )

        if strategy == SplitStrategy.AUTO:
            if algebraic_candidate and algebraic_candidate.score >= 0.5:
                strategy = SplitStrategy.ALGEBRAIC
            elif gradient_info and any(g > 0 for g in gradient_info.values()):
                strategy = SplitStrategy.GRADIENT_GUIDED

        left_box, right_box, split_var = DomainSplitter.split_box(
            subdomain.box,
            strategy,
            result.diagnosis,
            gradient_info,
            expr=expr,
            algebraic_candidate=algebraic_candidate,
        )

        self._total_splits += 1
        self._results.remove(result)

        # Create child subdomains
        self._subdomain_id += 1
        left = Subdomain(
            box=left_box,
            parent_id=subdomain.id,
            split_var=split_var,
            split_side='left',
            depth=subdomain.depth + 1,
            id=self._subdomain_id,
        )

        self._subdomain_id += 1
        right = Subdomain(
            box=right_box,
            parent_id=subdomain.id,
            split_var=split_var,
            split_side='right',
            depth=subdomain.depth + 1,
            id=self._subdomain_id,
        )

        self._subdomains.extend([left, right])
        queue.extend([left, right])
        self._report_progress()

    def _verify_subdomain(
        self,
        expr: 'Expr',
        subdomain: Subdomain,
        upper: Optional[float],
        lower: Optional[float],
    ) -> SubdomainResult:
        """Verify bound on a single subdomain."""
        start = time.time()
        gradient_info = None

        try:
            # Compute gradients if enabled (for future splits)
            if self.adaptive_config.compute_gradients:
                gradient_info = GradientEstimator.estimate_gradients(
                    self.solver, expr, subdomain.box, self.solver_config
                )

            # Try verification
            self.solver.verify_bound(
                expr,
                subdomain.box,
                upper=upper,
                lower=lower,
                config=self.solver_config,
            )

            elapsed = (time.time() - start) * 1000
            return SubdomainResult(
                subdomain=subdomain,
                verified=True,
                proof_fragment="interval_decide",
                verification_time_ms=elapsed,
                gradient_info=gradient_info,
            )

        except Exception as e:
            # Verification failed - get diagnosis
            diagnosis = self.solver.diagnose_bound_failure(
                expr,
                subdomain.box,
                upper=upper,
                lower=lower,
                config=self.solver_config,
            )

            elapsed = (time.time() - start) * 1000
            return SubdomainResult(
                subdomain=subdomain,
                verified=False,
                diagnosis=diagnosis,
                verification_time_ms=elapsed,
                gradient_info=gradient_info,
            )

    def _report_progress(self):
        """Report progress via callback if configured."""
        if self.adaptive_config.progress_callback is None:
            return

        now = time.time() * 1000
        if now - self._last_progress_time < self.adaptive_config.progress_interval_ms:
            return

        self._last_progress_time = now

        verified_count = sum(1 for r in self._results if r.verified)
        failed_count = sum(1 for r in self._results if not r.verified)
        max_depth = max((s.depth for s in self._subdomains), default=0)

        try:
            self.adaptive_config.progress_callback(
                self._total_splits,
                self.adaptive_config.max_splits,
                max_depth,
                verified_count,
                failed_count,
            )
        except Exception:
            pass  # Don't let callback errors break verification

    def _get_leaf_results(self) -> list[SubdomainResult]:
        """Get results for leaf subdomains only."""
        # A subdomain is a leaf if no other subdomain has it as parent
        parent_ids = {s.parent_id for s in self._subdomains if s.parent_id is not None}
        leaf_subdomain_ids = {s.id for s in self._subdomains if s.id not in parent_ids}

        # Filter results to only leaf subdomains
        return [r for r in self._results if r.subdomain.id in leaf_subdomain_ids]

    def _expr_to_lean_simple(self, expr: 'Expr') -> str:
        """Simple expression to Lean string (for comments)."""
        return str(expr)


def verify_bound_adaptive(
    solver: 'Solver',
    expr: 'Expr',
    domain: Union[Interval, Box, tuple, dict],
    upper: Optional[float] = None,
    lower: Optional[float] = None,
    adaptive_config: AdaptiveConfig = AdaptiveConfig(),
    solver_config: Config = Config(),
) -> AdaptiveResult:
    """
    Verify a bound using CEGAR (Counterexample-Guided Abstraction Refinement).

    When single-shot verification fails on a large domain, this function
    automatically splits the domain and retries on subdomains until either:
    - The bound is verified on all subdomains, or
    - A minimal subdomain is found where the bound genuinely fails

    Args:
        solver: LeanCert solver instance
        expr: Expression to verify
        domain: Domain to verify over
        upper: Upper bound to verify (f(x) ≤ upper)
        lower: Lower bound to verify (f(x) ≥ lower)
        adaptive_config: CEGAR configuration
        solver_config: Underlying solver configuration

    Returns:
        AdaptiveResult with verification status, subdomain tree, and Lean proof

    Example:
        >>> result = verify_bound_adaptive(
        ...     solver,
        ...     sin(x) + cos(x),
        ...     {'x': (0, 10)},
        ...     upper=1.5,
        ... )
        >>> print(result.verified)
        True
        >>> print(result.lean_proof)
        theorem adaptive_bound_proof : ...
        >>> print(result.tree_visualization())
        └── [root] ✓
            ├── [x:left] ✓
            └── [x:right] ✓
    """
    if upper is None and lower is None:
        raise ValueError("Must specify at least one of upper or lower bound")

    verifier = CEGARVerifier(solver, adaptive_config, solver_config)

    if upper is not None:
        return verifier.verify_upper_bound(expr, domain, upper)
    else:
        return verifier.verify_lower_bound(expr, domain, lower)
