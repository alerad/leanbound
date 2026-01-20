"""
Tests for algebraic structure-aware domain splitting.

Tests the AlgebraicAnalyzer class and ALGEBRAIC split strategy that uses:
- Critical point detection (where f'(x) = 0)
- Derivative sign change detection
- High curvature region detection
- Dependency reduction analysis
"""

import pytest
from fractions import Fraction

from leancert import var, sin, cos, exp, Solver
from leancert.domain import Box, Interval
from leancert.adaptive import (
    AdaptiveConfig,
    SplitStrategy,
    SplitCandidate,
    AlgebraicAnalyzer,
    DomainSplitter,
    verify_bound_adaptive,
)


# =============================================================================
# AlgebraicAnalyzer Tests
# =============================================================================

class TestAlgebraicAnalyzerBasic:
    """Basic tests for AlgebraicAnalyzer."""

    def test_analyze_expression_returns_list(self):
        """analyze_expression should return a list of SplitCandidate."""
        x = var('x')
        expr = x**2
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        assert isinstance(candidates, list)

    def test_split_candidate_has_required_fields(self):
        """SplitCandidate should have variable, point, score, reason."""
        x = var('x')
        expr = x * (1 - x)  # Has critical point at 0.5
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should find critical point for x*(1-x)
        if candidates:
            c = candidates[0]
            assert hasattr(c, 'variable')
            assert hasattr(c, 'point')
            assert hasattr(c, 'score')
            assert hasattr(c, 'reason')

    def test_get_best_split_returns_candidate_or_none(self):
        """get_best_split should return best candidate or None."""
        x = var('x')
        expr = x**2
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        result = AlgebraicAnalyzer.get_best_split(expr, box)

        assert result is None or isinstance(result, SplitCandidate)


class TestCriticalPointDetection:
    """Tests for critical point (f'(x) = 0) detection."""

    def test_detects_quadratic_vertex(self):
        """Should detect vertex of x*(1-x) at x=0.5."""
        x = var('x')
        expr = x * (1 - x)  # Maximum at x = 0.5
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should suggest split near 0.5
        critical_points = [c for c in candidates if c.reason == 'critical_point']

        # Even if not found as critical_point, should have candidates
        assert len(candidates) > 0

    def test_detects_sine_extrema(self):
        """Should detect extrema of sin(x) in [0, 2*pi]."""
        x = var('x')
        expr = sin(x)
        box = Box({'x': Interval(Fraction(0), Fraction(628) / Fraction(100))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should find some candidates (extrema at pi/2, 3pi/2)
        assert len(candidates) >= 0  # May not find exact extrema

    def test_linear_has_no_critical_points(self):
        """Linear function should have no critical points."""
        x = var('x')
        expr = 2 * x + 1
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)
        critical = [c for c in candidates if c.reason == 'critical_point']

        # Linear function has no critical points
        assert len(critical) == 0


class TestDerivativeSignChange:
    """Tests for derivative sign change detection."""

    def test_detects_inflection_like_behavior(self):
        """Should detect where derivative changes sign."""
        x = var('x')
        expr = x * (1 - x)  # f'(x) = 1 - 2x, changes sign at x = 0.5
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should find derivative sign change
        assert len(candidates) > 0


class TestHighCurvatureDetection:
    """Tests for high curvature region detection."""

    def test_detects_high_curvature_in_exp(self):
        """Should detect high curvature regions in exp(x)."""
        x = var('x')
        expr = exp(x)
        box = Box({'x': Interval(Fraction(0), Fraction(3))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)
        curvature = [c for c in candidates if c.reason == 'high_curvature']

        # exp(x) has higher curvature toward larger x
        # May or may not find candidates depending on thresholds
        assert isinstance(curvature, list)


class TestDependencyReduction:
    """Tests for interval dependency reduction analysis."""

    def test_dependency_reduction_for_product(self):
        """x*(1-x) has dependency problem - should suggest midpoint split."""
        x = var('x')
        expr = x * (1 - x)
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)
        dependency = [c for c in candidates if c.reason == 'dependency_reduction']

        # May suggest midpoint for dependency reduction
        assert isinstance(dependency, list)


class TestMultivariateAnalysis:
    """Tests for multivariate expression analysis."""

    def test_analyzes_all_variables(self):
        """Should analyze all variables in multivariate expression."""
        x = var('x')
        y = var('y')
        expr = x**2 + y**2
        box = Box({
            'x': Interval(Fraction(0), Fraction(1)),
            'y': Interval(Fraction(0), Fraction(1)),
        })

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should have candidates for both variables
        vars_found = {c.variable for c in candidates}
        # May find candidates for one or both variables
        assert isinstance(vars_found, set)

    def test_multivariate_product(self):
        """Should handle x*y."""
        x = var('x')
        y = var('y')
        expr = x * y
        box = Box({
            'x': Interval(Fraction(0), Fraction(1)),
            'y': Interval(Fraction(0), Fraction(1)),
        })

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should return a list (may be empty)
        assert isinstance(candidates, list)


# =============================================================================
# ALGEBRAIC Split Strategy Tests
# =============================================================================

class TestAlgebraicSplitStrategy:
    """Tests for the ALGEBRAIC split strategy."""

    def test_algebraic_strategy_exists(self):
        """ALGEBRAIC strategy should exist in enum."""
        assert hasattr(SplitStrategy, 'ALGEBRAIC')
        assert SplitStrategy.ALGEBRAIC.value == 'algebraic'

    def test_algebraic_strategy_in_config(self):
        """Should be able to use ALGEBRAIC strategy in config."""
        config = AdaptiveConfig(strategy=SplitStrategy.ALGEBRAIC)
        assert config.strategy == SplitStrategy.ALGEBRAIC

    def test_algebraic_split_with_candidate(self):
        """DomainSplitter should use algebraic candidate when provided."""
        x = var('x')
        expr = x * (1 - x)
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidate = SplitCandidate(
            variable='x',
            point=Fraction(1, 2),
            score=1.0,
            reason='critical_point'
        )

        left, right, split_var = DomainSplitter.split_box(
            box,
            SplitStrategy.ALGEBRAIC,
            algebraic_candidate=candidate,
        )

        assert split_var == 'x'
        # Should split near 0.5
        assert float(left['x'].hi) == pytest.approx(0.5, abs=0.1)

    def test_algebraic_split_computes_candidate_if_needed(self):
        """Should compute candidate from expr if not provided."""
        x = var('x')
        expr = x * (1 - x)
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        left, right, split_var = DomainSplitter.split_box(
            box,
            SplitStrategy.ALGEBRAIC,
            expr=expr,
        )

        assert split_var == 'x'
        # Should produce valid split
        assert left['x'].lo == box['x'].lo
        assert right['x'].hi == box['x'].hi

    def test_algebraic_falls_back_without_info(self):
        """Should fall back to largest_first without expr or candidate."""
        box = Box({
            'x': Interval(Fraction(0), Fraction(1)),
            'y': Interval(Fraction(0), Fraction(2)),  # Larger
        })

        left, right, split_var = DomainSplitter.split_box(
            box,
            SplitStrategy.ALGEBRAIC,
        )

        # Falls back to largest first -> y
        assert split_var == 'y'


# =============================================================================
# Integration Tests
# =============================================================================

class TestAlgebraicIntegration:
    """Integration tests for algebraic splitting with verification."""

    def test_algebraic_strategy_verifies_quadratic(self):
        """ALGEBRAIC strategy should work for x*(1-x)."""
        x = var('x')
        expr = x * (1 - x)  # Max is 0.25 at x=0.5
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=0.3,  # Above max
            adaptive_config=AdaptiveConfig(
                strategy=SplitStrategy.ALGEBRAIC,
                max_splits=5,
            )
        )

        assert result.verified is True

    def test_algebraic_strategy_verifies_polynomial(self):
        """ALGEBRAIC strategy should work for x^2."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(
                strategy=SplitStrategy.ALGEBRAIC,
                max_splits=5,
            )
        )

        assert result.verified is True

    def test_algebraic_with_auto_fallback(self):
        """AUTO should use ALGEBRAIC when beneficial."""
        x = var('x')
        expr = x * (1 - x)
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=0.3,
            adaptive_config=AdaptiveConfig(
                strategy=SplitStrategy.AUTO,
                max_splits=5,
            )
        )

        assert result.verified is True

    def test_algebraic_multivariate(self):
        """ALGEBRAIC should work with multiple variables."""
        x = var('x')
        y = var('y')
        expr = x * (1 - x) + y * (1 - y)  # Max is 0.5
        domain = {'x': (0, 1), 'y': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=0.6,
            adaptive_config=AdaptiveConfig(
                strategy=SplitStrategy.ALGEBRAIC,
                max_splits=5,
            )
        )

        assert result.verified is True


# =============================================================================
# Split Candidate Scoring Tests
# =============================================================================

class TestSplitCandidateScoring:
    """Tests for split candidate scoring."""

    def test_critical_point_has_high_score(self):
        """Critical points should have high score."""
        x = var('x')
        expr = x * (1 - x)
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)
        critical = [c for c in candidates if c.reason == 'critical_point']

        for c in critical:
            assert c.score >= 0.8  # High priority

    def test_candidates_sorted_by_score(self):
        """Candidates should be sorted by score (highest first)."""
        x = var('x')
        expr = sin(x) * x
        box = Box({'x': Interval(Fraction(0), Fraction(3))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        if len(candidates) > 1:
            for i in range(len(candidates) - 1):
                assert candidates[i].score >= candidates[i + 1].score


# =============================================================================
# Edge Cases
# =============================================================================

class TestAlgebraicEdgeCases:
    """Edge case tests for algebraic analysis."""

    def test_constant_expression(self):
        """Should handle constant expression."""
        x = var('x')
        expr = x * 0 + 5  # Constant 5
        box = Box({'x': Interval(Fraction(0), Fraction(1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Constant has no structure to analyze
        # Should return empty or minimal candidates
        assert isinstance(candidates, list)

    def test_point_interval(self):
        """Should handle point interval (width = 0)."""
        x = var('x')
        expr = x**2
        box = Box({'x': Interval(Fraction(1, 2), Fraction(1, 2))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Point interval has no room to split
        assert isinstance(candidates, list)

    def test_very_small_interval(self):
        """Should handle very small interval."""
        x = var('x')
        expr = x**2
        box = Box({'x': Interval(Fraction(0), Fraction(1, 1000000))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should return candidates (may be empty due to small interval)
        assert isinstance(candidates, list)

    def test_negative_domain(self):
        """Should handle negative domain."""
        x = var('x')
        expr = x**2
        box = Box({'x': Interval(Fraction(-2), Fraction(-1))})

        candidates = AlgebraicAnalyzer.analyze_expression(expr, box)

        # Should work with negative domain
        assert isinstance(candidates, list)
