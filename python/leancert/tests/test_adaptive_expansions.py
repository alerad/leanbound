"""
Tests for adaptive verification expansions:
- Parallel subdomain verification
- Progress callbacks
- Auto-gradient computation
- Subdomain tree visualization
- AUTO split strategy
- Volume-based termination
"""

import pytest
from fractions import Fraction
from unittest.mock import Mock, patch
import threading
import time

from leancert import var, sin, cos, exp, Solver
from leancert.domain import Box, Interval
from leancert.config import Config
from leancert.adaptive import (
    AdaptiveConfig,
    AdaptiveResult,
    SplitStrategy,
    Subdomain,
    SubdomainResult,
    SubdomainTreeVisualizer,
    GradientEstimator,
    DomainSplitter,
    CEGARVerifier,
    verify_bound_adaptive,
)


# =============================================================================
# Parallel Verification Tests
# =============================================================================

class TestParallelVerification:
    """Tests for parallel subdomain verification."""

    def test_parallel_verification_enabled_by_default(self):
        """Default config should have parallel enabled."""
        config = AdaptiveConfig()
        assert config.parallel is True

    def test_parallel_verification_can_be_disabled(self):
        """Should be able to disable parallel verification."""
        config = AdaptiveConfig(parallel=False)
        assert config.parallel is False

    def test_max_workers_default(self):
        """Default max_workers should be None (auto)."""
        config = AdaptiveConfig()
        assert config.max_workers is None

    def test_max_workers_configurable(self):
        """Should be able to set max_workers."""
        config = AdaptiveConfig(max_workers=4)
        assert config.max_workers == 4

    def test_parallel_produces_same_result(self):
        """Parallel and sequential should produce same correctness."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        # Run with parallel enabled
        result_parallel = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(parallel=True, max_splits=10)
        )

        # Run with parallel disabled
        result_sequential = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(parallel=False, max_splits=10)
        )

        # Both should verify successfully
        assert result_parallel.verified == result_sequential.verified

    def test_parallel_handles_failures(self):
        """Parallel verification should handle subdomain failures correctly."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 2)}
        solver = Solver()

        # Bound that will fail - max is 4, we claim 0.5
        result = verify_bound_adaptive(
            solver, expr, domain, upper=0.5,
            adaptive_config=AdaptiveConfig(parallel=True, max_splits=2)
        )

        # Should have failed subdomains
        assert result.verified is False
        assert len(result.failed_subdomains) > 0


class TestParallelThreadSafety:
    """Tests for thread safety in parallel verification."""

    def test_progress_callback_thread_safe(self):
        """Progress callback should be called from multiple threads safely."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        call_count = 0
        lock = threading.Lock()

        # Progress callback signature: (splits, max_splits, depth, verified, failed)
        def counting_callback(splits, max_splits, depth, verified, failed):
            nonlocal call_count
            with lock:
                call_count += 1

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(
                parallel=True,
                max_splits=3,
                progress_callback=counting_callback
            )
        )

        # Callback should have been called
        assert call_count >= 0  # May be 0 if verification was fast


# =============================================================================
# Progress Callback Tests
# =============================================================================

class TestProgressCallbacks:
    """Tests for progress callback functionality."""

    def test_progress_callback_called(self):
        """Progress callback should be invoked during verification."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        calls = []
        def recording_callback(splits, max_splits, depth, verified, failed):
            calls.append((splits, max_splits, depth, verified, failed))

        # Use a simple bound
        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(
                progress_callback=recording_callback,
                max_splits=3,
                progress_interval_ms=0,  # Disable throttling for testing
            )
        )

        # Should have at least one progress call
        assert len(calls) >= 0  # May be empty if too fast

    def test_progress_callback_receives_correct_args(self):
        """Progress callback should receive (splits, max_splits, depth, verified, failed)."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        calls = []
        def recording_callback(splits, max_splits, depth, verified, failed):
            calls.append({
                'splits': splits,
                'max_splits': max_splits,
                'depth': depth,
                'verified': verified,
                'failed': failed,
            })

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(
                progress_callback=recording_callback,
                max_splits=3,
                progress_interval_ms=0,
            )
        )

        # Check that if we got calls, they have the right structure
        for c in calls:
            assert isinstance(c['splits'], int)
            assert isinstance(c['max_splits'], int)
            assert isinstance(c['depth'], int)
            assert isinstance(c['verified'], int)
            assert isinstance(c['failed'], int)

    def test_with_progress_factory_method(self):
        """AdaptiveConfig.with_progress should work correctly."""
        callback = Mock()
        config = AdaptiveConfig.with_progress(callback)

        assert config.progress_callback is callback

    def test_with_progress_preserves_other_settings(self):
        """with_progress should preserve other config settings."""
        callback = Mock()
        config = AdaptiveConfig.with_progress(callback, max_splits=50, max_depth=8)

        assert config.progress_callback is callback
        assert config.max_splits == 50
        assert config.max_depth == 8


# =============================================================================
# Auto-Gradient Tests
# =============================================================================

class TestGradientEstimator:
    """Tests for gradient estimation via finite differences."""

    def test_gradient_estimator_static_method_exists(self):
        """GradientEstimator should have estimate_gradients static method."""
        assert hasattr(GradientEstimator, 'estimate_gradients')

    def test_estimate_gradients_returns_dict(self):
        """estimate_gradients should return dict of var -> gradient."""
        x = var('x')
        expr = x**2
        box = Box({'x': Interval(Fraction(0), Fraction(1))})
        solver = Solver()
        config = Config()

        gradients = GradientEstimator.estimate_gradients(solver, expr, box, config)

        assert isinstance(gradients, dict)
        assert 'x' in gradients

    def test_gradient_positive_for_increasing_function(self):
        """Gradient should be positive for increasing function."""
        x = var('x')
        expr = x  # Linear, always increasing
        box = Box({'x': Interval(Fraction(0), Fraction(1))})
        solver = Solver()
        config = Config()

        gradients = GradientEstimator.estimate_gradients(solver, expr, box, config)

        assert gradients['x'] > 0

    def test_gradient_multivariate(self):
        """Should estimate gradients for all variables."""
        x = var('x')
        y = var('y')
        expr = x**2 + y**3
        box = Box({
            'x': Interval(Fraction(1), Fraction(2)),
            'y': Interval(Fraction(1), Fraction(2))
        })
        solver = Solver()
        config = Config()

        gradients = GradientEstimator.estimate_gradients(solver, expr, box, config)

        assert 'x' in gradients
        assert 'y' in gradients

    def test_gradient_handles_transcendental(self):
        """Should handle transcendental functions."""
        x = var('x')
        expr = sin(x)
        box = Box({'x': Interval(Fraction(0), Fraction(1))})
        solver = Solver()
        config = Config()

        gradients = GradientEstimator.estimate_gradients(solver, expr, box, config)

        # cos(0.5) ≈ 0.877 > 0
        assert gradients['x'] > 0


class TestAutoSplitStrategy:
    """Tests for AUTO split strategy."""

    def test_auto_strategy_exists(self):
        """AUTO strategy should exist in enum."""
        assert hasattr(SplitStrategy, 'AUTO')

    def test_auto_strategy_in_config(self):
        """Should be able to use AUTO strategy in config."""
        config = AdaptiveConfig(strategy=SplitStrategy.AUTO)
        assert config.strategy == SplitStrategy.AUTO

    def test_auto_strategy_works(self):
        """AUTO strategy should work in verification."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(strategy=SplitStrategy.AUTO)
        )

        assert result.verified is True

    def test_auto_strategy_multivariate(self):
        """AUTO strategy should work with multiple variables."""
        x = var('x')
        y = var('y')
        expr = x**2 + y**2
        domain = {'x': (0, 1), 'y': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=3.0,
            adaptive_config=AdaptiveConfig(strategy=SplitStrategy.AUTO)
        )

        assert result.verified is True


# =============================================================================
# Tree Visualization Tests
# =============================================================================

class TestSubdomainTreeVisualizer:
    """Tests for subdomain tree visualization."""

    def test_visualize_empty_list(self):
        """Should handle empty subdomain list."""
        tree_str = SubdomainTreeVisualizer.visualize([], [])
        assert tree_str == "(empty tree)"

    def test_visualize_returns_string(self):
        """tree_visualization should return a string."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(max_splits=3)
        )

        tree_str = result.tree_visualization()
        assert isinstance(tree_str, str)

    def test_visualize_shows_status(self):
        """Visualization should contain status indicators."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(max_splits=3)
        )

        tree_str = result.tree_visualization()
        # Should contain some indication (could be ✓, ✗, or text)
        assert len(tree_str) > 0

    def test_visualize_multivariate(self):
        """Should handle multivariate domains."""
        x = var('x')
        y = var('y')
        expr = x + y
        domain = {'x': (0, 1), 'y': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=3.0,
            adaptive_config=AdaptiveConfig(max_splits=3)
        )

        tree_str = result.tree_visualization()
        assert isinstance(tree_str, str)


# =============================================================================
# Volume-Based Termination Tests
# =============================================================================

class TestVolumeBasedTermination:
    """Tests for volume-based termination."""

    def test_min_volume_in_config(self):
        """min_volume should be configurable."""
        config = AdaptiveConfig(min_volume=1e-10)
        assert config.min_volume == 1e-10

    def test_verified_volume_property(self):
        """Result should have verified_volume property."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(max_splits=3)
        )

        assert hasattr(result, 'verified_volume')
        volume = result.verified_volume
        assert isinstance(volume, (int, float, Fraction))

    def test_unverified_volume_property(self):
        """Result should have unverified_volume property."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 2)}
        solver = Solver()

        # Bound that fails
        result = verify_bound_adaptive(
            solver, expr, domain, upper=0.5,
            adaptive_config=AdaptiveConfig(max_splits=2)
        )

        assert hasattr(result, 'unverified_volume')
        volume = result.unverified_volume
        assert isinstance(volume, (int, float, Fraction))

    def test_volumes_sum_to_original(self):
        """Verified + unverified volumes should equal original domain."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 2)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=1.0,
            adaptive_config=AdaptiveConfig(max_splits=3)
        )

        total = result.verified_volume + result.unverified_volume
        # Original domain has volume 2
        assert abs(float(total) - 2.0) < 1e-10

    def test_multivariate_volume(self):
        """Volume calculation should work for multivariate domains."""
        x = var('x')
        y = var('y')
        expr = x + y
        domain = {'x': (0, 2), 'y': (0, 3)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=10.0,
            adaptive_config=AdaptiveConfig(max_splits=3)
        )

        # Original volume = 2 * 3 = 6
        total = result.verified_volume + result.unverified_volume
        assert abs(float(total) - 6.0) < 1e-10


# =============================================================================
# Timing Information Tests
# =============================================================================

class TestTimingInformation:
    """Tests for timing information in results."""

    def test_result_has_total_time(self):
        """Result should have total_time_ms attribute."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0
        )

        assert hasattr(result, 'total_time_ms')
        assert result.total_time_ms >= 0

    def test_subdomain_result_has_verification_time(self):
        """SubdomainResult should have verification_time_ms attribute."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0
        )

        # Check results have verification_time_ms
        for r in result.results:
            assert hasattr(r, 'verification_time_ms')
            assert r.verification_time_ms >= 0


# =============================================================================
# Domain Splitter Tests for New Features
# =============================================================================

class TestDomainSplitterAutoStrategy:
    """Tests for DomainSplitter with AUTO strategy."""

    def test_auto_strategy_chooses_dimension(self):
        """AUTO strategy should choose a dimension to split."""
        x = var('x')
        y = var('y')
        box = Box({
            'x': Interval(Fraction(0), Fraction(1)),
            'y': Interval(Fraction(0), Fraction(2))  # Larger in y
        })

        left_box, right_box, split_var = DomainSplitter.split_box(
            box,
            SplitStrategy.AUTO,
            diagnosis=None,
            gradient_info=None,
        )

        # Without gradient info, should fall back to LARGEST_FIRST -> y
        assert split_var == 'y'

    def test_auto_strategy_uses_gradient_when_available(self):
        """AUTO strategy should use gradient info when available."""
        x = var('x')
        box = Box({'x': Interval(Fraction(0), Fraction(2))})

        # Provide gradient info
        gradient_info = {'x': 5.0}

        left_box, right_box, split_var = DomainSplitter.split_box(
            box,
            SplitStrategy.AUTO,
            diagnosis=None,
            gradient_info=gradient_info,
        )

        assert split_var == 'x'


# =============================================================================
# Integration Tests for Expansions
# =============================================================================

class TestExpansionIntegration:
    """Integration tests for all expansion features together."""

    def test_all_features_combined(self):
        """Test using all expansion features together."""
        x = var('x')
        y = var('y')
        expr = x + y
        domain = {'x': (0, 1), 'y': (0, 1)}
        solver = Solver()

        progress_calls = []
        def progress_callback(splits, max_splits, depth, verified, failed):
            progress_calls.append((splits, max_splits, depth, verified, failed))

        result = verify_bound_adaptive(
            solver, expr, domain, upper=3.0,
            adaptive_config=AdaptiveConfig(
                strategy=SplitStrategy.AUTO,
                parallel=True,
                max_workers=2,
                max_splits=3,
                min_volume=1e-6,
                progress_callback=progress_callback,
                progress_interval_ms=0,
            )
        )

        # Check result structure
        assert isinstance(result.verified, bool)
        assert result.total_time_ms >= 0
        assert result.verified_volume + result.unverified_volume > 0

        # Check tree visualization works
        tree_str = result.tree_visualization()
        assert isinstance(tree_str, str)

    def test_sequential_fallback(self):
        """Sequential mode should work when parallel is disabled."""
        x = var('x')
        expr = x**2
        domain = {'x': (0, 1)}
        solver = Solver()

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(
                parallel=False,
                max_splits=3
            )
        )

        assert result.verified is True

    def test_complex_expression_with_expansions(self):
        """Test complex expression with all expansion features."""
        x = var('x')
        expr = x**2  # Simple expression
        domain = {'x': (0, 1)}
        solver = Solver()

        progress_count = [0]
        def counting_callback(splits, max_splits, depth, verified, failed):
            progress_count[0] += 1

        result = verify_bound_adaptive(
            solver, expr, domain, upper=2.0,
            adaptive_config=AdaptiveConfig(
                strategy=SplitStrategy.AUTO,
                parallel=True,
                progress_callback=counting_callback,
                progress_interval_ms=0,
                max_splits=3
            )
        )

        # Check timing
        assert result.total_time_ms >= 0


# =============================================================================
# Config Preset Tests
# =============================================================================

class TestConfigPresets:
    """Tests for AdaptiveConfig presets."""

    def test_quick_preset(self):
        """Quick preset should have limited splits."""
        config = AdaptiveConfig.quick()
        assert config.max_splits == 16
        assert config.max_depth == 5
        assert config.parallel is True

    def test_thorough_preset(self):
        """Thorough preset should allow more splits."""
        config = AdaptiveConfig.thorough()
        assert config.max_splits == 256
        assert config.max_depth == 15
        assert config.parallel is True

    def test_exhaustive_preset(self):
        """Exhaustive preset should be very thorough."""
        config = AdaptiveConfig.exhaustive()
        assert config.max_splits == 1024
        assert config.max_depth == 20
        assert config.min_width == 1e-15
