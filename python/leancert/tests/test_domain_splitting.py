# LeanCert v3 SDK - Domain Splitting Tests
# Copyright (c) 2024 LeanCert Contributors. All rights reserved.

"""
Comprehensive tests for domain splitting strategies in CEGAR verification.

Test Categories:
1. Bisect Strategy - Midpoint splitting
2. Worst Point Strategy - Counterexample-guided splitting
3. Gradient Guided Strategy - Split along steepest variable
4. Largest First Strategy - Split widest dimension
5. Splitting Termination - Tests for should_continue_splitting
6. Edge Cases - Degenerate boxes, boundary conditions
7. Multivariate Splitting - High-dimensional domain splits
"""

import pytest
from fractions import Fraction

from leancert.domain import Interval, Box
from leancert.adaptive import (
    SplitStrategy,
    AdaptiveConfig,
    Subdomain,
    DomainSplitter,
)
from leancert.result import FailureDiagnosis


# =============================================================================
# Test Fixtures
# =============================================================================

@pytest.fixture
def unit_box_1d():
    """1D unit box [0, 1]."""
    return Box({'x': (0, 1)})


@pytest.fixture
def unit_box_2d():
    """2D unit box [0, 1] x [0, 1]."""
    return Box({'x': (0, 1), 'y': (0, 1)})


@pytest.fixture
def unit_box_3d():
    """3D unit box [0, 1]^3."""
    return Box({'x': (0, 1), 'y': (0, 1), 'z': (0, 1)})


@pytest.fixture
def asymmetric_box():
    """Asymmetric box with different widths."""
    return Box({'x': (0, 10), 'y': (-1, 1), 'z': (0, 100)})


# =============================================================================
# 1. Bisect Strategy Tests
# =============================================================================

class TestBisectStrategy:
    """Tests for BISECT splitting strategy."""

    def test_bisect_splits_at_midpoint(self, unit_box_1d):
        """BISECT should split at exact midpoint."""
        left, right, var = DomainSplitter.split_box(
            unit_box_1d, SplitStrategy.BISECT
        )

        assert var == 'x'
        assert left['x'].lo == Fraction(0)
        assert left['x'].hi == Fraction(1, 2)
        assert right['x'].lo == Fraction(1, 2)
        assert right['x'].hi == Fraction(1)

    def test_bisect_splits_first_variable(self, unit_box_2d):
        """BISECT should split the first variable."""
        left, right, var = DomainSplitter.split_box(
            unit_box_2d, SplitStrategy.BISECT
        )

        assert var == 'x'
        # y should be unchanged
        assert left['y'].lo == Fraction(0)
        assert left['y'].hi == Fraction(1)

    def test_bisect_preserves_exact_rationals(self):
        """BISECT should preserve exact rational arithmetic."""
        box = Box({'x': (Fraction(1, 3), Fraction(2, 3))})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        expected_mid = Fraction(1, 2)  # (1/3 + 2/3) / 2 = 1/2
        assert left['x'].hi == expected_mid
        assert right['x'].lo == expected_mid

    def test_bisect_negative_interval(self):
        """BISECT should work with negative intervals."""
        box = Box({'x': (-10, -2)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        assert var == 'x'
        assert left['x'].hi == Fraction(-6)  # (-10 + -2) / 2 = -6
        assert right['x'].lo == Fraction(-6)


# =============================================================================
# 2. Worst Point Strategy Tests
# =============================================================================

class TestWorstPointStrategy:
    """Tests for WORST_POINT splitting strategy."""

    def test_worst_point_splits_near_diagnosis(self, unit_box_1d):
        """WORST_POINT should split near the diagnosed worst point."""
        diagnosis = FailureDiagnosis(
            failure_type='bound_too_tight',
            margin=-0.1,
            worst_point={'x': 0.75},
            suggested_bound=1.1,
        )

        left, right, var = DomainSplitter.split_box(
            unit_box_1d, SplitStrategy.WORST_POINT, diagnosis
        )

        assert var == 'x'
        # Should split near 0.75
        split_point = float(left['x'].hi)
        assert 0.7 <= split_point <= 0.8

    def test_worst_point_clamps_to_interval(self):
        """WORST_POINT should clamp split point to interval bounds."""
        box = Box({'x': (0, 1)})
        diagnosis = FailureDiagnosis(
            failure_type='bound_too_tight',
            margin=-0.1,
            worst_point={'x': 1.5},  # Outside interval!
            suggested_bound=1.1,
        )

        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.WORST_POINT, diagnosis
        )

        # Split point should be clamped, not at 1.5
        split_point = float(left['x'].hi)
        assert 0 < split_point < 1

    def test_worst_point_avoids_degenerate_split(self):
        """WORST_POINT should avoid splitting at exact boundary."""
        box = Box({'x': (0, 1)})
        diagnosis = FailureDiagnosis(
            failure_type='bound_too_tight',
            margin=-0.1,
            worst_point={'x': 0.0},  # At boundary
            suggested_bound=1.1,
        )

        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.WORST_POINT, diagnosis
        )

        # Left box should not be degenerate
        assert float(left['x'].width()) > 0

    def test_worst_point_multivariate_selects_critical_var(self):
        """WORST_POINT should select variable with most critical worst point."""
        box = Box({'x': (0, 10), 'y': (0, 10)})
        diagnosis = FailureDiagnosis(
            failure_type='bound_too_tight',
            margin=-0.1,
            worst_point={'x': 5.0, 'y': 9.5},  # y is near boundary (more critical)
            suggested_bound=1.1,
        )

        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.WORST_POINT, diagnosis
        )

        # Should split y since 9.5 is farther from center (5) than x's 5.0
        assert var == 'y'

    def test_worst_point_falls_back_without_diagnosis(self, unit_box_1d):
        """WORST_POINT without diagnosis should fall back to largest dimension."""
        left, right, var = DomainSplitter.split_box(
            unit_box_1d, SplitStrategy.WORST_POINT, diagnosis=None
        )

        # Should still work, using default behavior
        assert var == 'x'


# =============================================================================
# 3. Gradient Guided Strategy Tests
# =============================================================================

class TestGradientGuidedStrategy:
    """Tests for GRADIENT_GUIDED splitting strategy."""

    def test_gradient_guided_splits_steepest(self):
        """GRADIENT_GUIDED should split along variable with largest gradient."""
        box = Box({'x': (0, 1), 'y': (0, 1), 'z': (0, 1)})
        gradient_info = {'x': 0.5, 'y': 2.0, 'z': 0.1}

        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.GRADIENT_GUIDED, gradient_info=gradient_info
        )

        assert var == 'y'  # y has largest gradient magnitude

    def test_gradient_guided_handles_negative_gradients(self):
        """GRADIENT_GUIDED should use absolute value of gradient."""
        box = Box({'x': (0, 1), 'y': (0, 1)})
        gradient_info = {'x': 0.5, 'y': -3.0}  # y has larger magnitude

        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.GRADIENT_GUIDED, gradient_info=gradient_info
        )

        assert var == 'y'

    def test_gradient_guided_falls_back_without_info(self, unit_box_2d):
        """GRADIENT_GUIDED without info should fall back to largest dimension."""
        left, right, var = DomainSplitter.split_box(
            unit_box_2d, SplitStrategy.GRADIENT_GUIDED, gradient_info=None
        )

        # Both have same width, should pick first
        assert var in ['x', 'y']


# =============================================================================
# 4. Largest First Strategy Tests
# =============================================================================

class TestLargestFirstStrategy:
    """Tests for LARGEST_FIRST splitting strategy."""

    def test_largest_first_splits_widest(self, asymmetric_box):
        """LARGEST_FIRST should split the widest dimension."""
        left, right, var = DomainSplitter.split_box(
            asymmetric_box, SplitStrategy.LARGEST_FIRST
        )

        assert var == 'z'  # z has width 100

    def test_largest_first_breaks_ties_by_order(self):
        """LARGEST_FIRST should break ties by variable order."""
        box = Box({'x': (0, 1), 'y': (0, 1)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.LARGEST_FIRST
        )

        # Both have same width, should pick first (x)
        assert var == 'x'

    def test_largest_first_handles_point_intervals(self):
        """LARGEST_FIRST should handle boxes with some point intervals."""
        box = Box({'x': (5, 5), 'y': (0, 1)})  # x is a point
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.LARGEST_FIRST
        )

        assert var == 'y'  # y is the only splittable dimension


# =============================================================================
# 5. Splitting Termination Tests
# =============================================================================

class TestSplittingTermination:
    """Tests for should_continue_splitting logic."""

    def test_stops_at_max_depth(self):
        """Should stop when depth reaches max_depth."""
        box = Box({'x': (0, 1)})
        config = AdaptiveConfig(max_depth=5)

        # At depth 5, should not continue
        result = DomainSplitter.should_continue_splitting(
            box, config, depth=5, total_splits=0
        )
        assert result is False

        # At depth 4, should continue
        result = DomainSplitter.should_continue_splitting(
            box, config, depth=4, total_splits=0
        )
        assert result is True

    def test_stops_at_max_splits(self):
        """Should stop when total_splits reaches max_splits."""
        box = Box({'x': (0, 1)})
        config = AdaptiveConfig(max_splits=10)

        # At 10 splits, should not continue
        result = DomainSplitter.should_continue_splitting(
            box, config, depth=1, total_splits=10
        )
        assert result is False

        # At 9 splits, should continue
        result = DomainSplitter.should_continue_splitting(
            box, config, depth=1, total_splits=9
        )
        assert result is True

    def test_stops_at_min_width(self):
        """Should stop when interval width is below min_width."""
        box = Box({'x': (0, 1e-12)})
        config = AdaptiveConfig(min_width=1e-10)

        result = DomainSplitter.should_continue_splitting(
            box, config, depth=1, total_splits=0
        )
        assert result is False

    def test_continues_with_sufficient_width(self):
        """Should continue when interval width is above min_width."""
        box = Box({'x': (0, 1e-5)})
        config = AdaptiveConfig(min_width=1e-10)

        result = DomainSplitter.should_continue_splitting(
            box, config, depth=1, total_splits=0
        )
        assert result is True

    def test_multivariate_min_width_checks_all(self):
        """Should stop if ANY dimension is below min_width."""
        box = Box({'x': (0, 1), 'y': (0, 1e-12)})
        config = AdaptiveConfig(min_width=1e-10)

        result = DomainSplitter.should_continue_splitting(
            box, config, depth=1, total_splits=0
        )
        assert result is False


# =============================================================================
# 6. Edge Cases Tests
# =============================================================================

class TestEdgeCases:
    """Tests for edge cases in domain splitting."""

    def test_split_point_interval(self):
        """Splitting a point interval should still work (degenerate case)."""
        box = Box({'x': (5, 5), 'y': (0, 1)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.LARGEST_FIRST
        )

        # Should split y (x has zero width)
        assert var == 'y'

    def test_split_very_small_interval(self):
        """Splitting a very small interval should work."""
        # Use Fraction to avoid floating point precision issues
        box = Box({'x': (Fraction(0), Fraction(1, 10**10))})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        assert var == 'x'
        assert left['x'].hi <= right['x'].hi
        # Midpoint should be half the original width
        assert left['x'].hi == Fraction(1, 2 * 10**10)

    def test_split_large_interval(self):
        """Splitting a very large interval should work."""
        box = Box({'x': (-1e10, 1e10)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        assert var == 'x'
        assert float(left['x'].hi) == pytest.approx(0.0, abs=1e-5)

    def test_split_rational_boundaries(self):
        """Splitting intervals with rational boundaries should be exact."""
        box = Box({'x': (Fraction(1, 7), Fraction(3, 7))})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        # Midpoint of [1/7, 3/7] is 2/7
        assert left['x'].hi == Fraction(2, 7)
        assert right['x'].lo == Fraction(2, 7)


# =============================================================================
# 7. Multivariate Splitting Tests
# =============================================================================

class TestMultivariateSplitting:
    """Tests for splitting high-dimensional domains."""

    def test_split_3d_preserves_two_dims(self, unit_box_3d):
        """Splitting 3D box should preserve two dimensions."""
        left, right, var = DomainSplitter.split_box(
            unit_box_3d, SplitStrategy.BISECT
        )

        other_vars = [v for v in ['x', 'y', 'z'] if v != var]
        for v in other_vars:
            assert left[v].lo == unit_box_3d[v].lo
            assert left[v].hi == unit_box_3d[v].hi
            assert right[v].lo == unit_box_3d[v].lo
            assert right[v].hi == unit_box_3d[v].hi

    def test_split_many_dimensions(self):
        """Splitting high-dimensional box should work."""
        box = Box({f'x{i}': (0, 1) for i in range(10)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        assert var == 'x0'  # First variable
        # All other dimensions unchanged
        for i in range(1, 10):
            assert left[f'x{i}'] == box[f'x{i}']

    def test_largest_first_in_high_dim(self):
        """LARGEST_FIRST should find largest dimension in high-dim box."""
        intervals = {f'x{i}': (0, i + 1) for i in range(10)}
        box = Box(intervals)

        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.LARGEST_FIRST
        )

        assert var == 'x9'  # x9 has width 10 (largest)


# =============================================================================
# 8. Subdomain Structure Tests
# =============================================================================

class TestSubdomainConstruction:
    """Tests for Subdomain data structure construction during splitting."""

    def test_subdomain_preserves_box(self):
        """Subdomain should correctly store the box."""
        box = Box({'x': (0, 1), 'y': (-1, 1)})
        subdomain = Subdomain(box=box, depth=0)

        assert subdomain.box == box
        assert subdomain.depth == 0
        assert subdomain.parent_id is None

    def test_child_subdomain_structure(self):
        """Child subdomain should have correct structure."""
        parent_box = Box({'x': (0, 1)})
        child_box = Box({'x': (0, 0.5)})

        parent = Subdomain(box=parent_box, depth=0)
        child = Subdomain(
            box=child_box,
            parent_id=0,
            split_var='x',
            split_side='left',
            depth=1,
        )

        assert child.parent_id == 0
        assert child.split_var == 'x'
        assert child.split_side == 'left'
        assert child.depth == 1


# =============================================================================
# 9. Strategy Enum Tests
# =============================================================================

class TestSplitStrategyEnum:
    """Tests for SplitStrategy enum."""

    def test_all_strategies_have_values(self):
        """All strategies should have string values."""
        assert SplitStrategy.BISECT.value == "bisect"
        assert SplitStrategy.WORST_POINT.value == "worst_point"
        assert SplitStrategy.GRADIENT_GUIDED.value == "gradient_guided"
        assert SplitStrategy.LARGEST_FIRST.value == "largest_first"

    def test_strategy_comparison(self):
        """Strategies should be comparable."""
        assert SplitStrategy.BISECT == SplitStrategy.BISECT
        assert SplitStrategy.BISECT != SplitStrategy.WORST_POINT


# =============================================================================
# 10. Integration Tests
# =============================================================================

class TestSplittingIntegration:
    """Integration tests for domain splitting."""

    def test_repeated_splitting_refines_domain(self):
        """Repeated splitting should refine the domain."""
        box = Box({'x': (0, 1)})

        for _ in range(5):
            left, right, var = DomainSplitter.split_box(
                box, SplitStrategy.BISECT
            )
            # Continue with left half
            box = left

        # After 5 bisections, width should be 1/32
        expected_width = Fraction(1, 32)
        assert box['x'].width() == expected_width

    def test_splitting_covers_original_domain(self):
        """Left and right subdomains should cover the original domain."""
        box = Box({'x': (-5, 5), 'y': (0, 10)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        # Check coverage
        assert left[var].lo == box[var].lo
        assert right[var].hi == box[var].hi
        assert left[var].hi == right[var].lo  # No gap

    def test_splitting_produces_disjoint_interiors(self):
        """Split subdomains should have disjoint interiors."""
        box = Box({'x': (0, 1)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        # Interiors don't overlap (boundaries may touch)
        left_interior = (float(left[var].lo), float(left[var].hi))
        right_interior = (float(right[var].lo), float(right[var].hi))

        # No overlap in interiors
        assert left_interior[1] <= right_interior[0]
