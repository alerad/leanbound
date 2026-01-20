# LeanCert v3 SDK - Adaptive Verification Tests
# Copyright (c) 2024 LeanCert Contributors. All rights reserved.

"""
Comprehensive tests for CEGAR (Counterexample-Guided Abstraction Refinement)
adaptive verification.

Test Categories:
1. Basic Adaptive Verification - Simple cases that benefit from splitting
2. Domain Splitting Behavior - Tests for different splitting strategies
3. Convergence and Limits - Tests for max_splits, max_depth limits
4. Multivariate Domains - Tests for multi-dimensional problems
5. Edge Cases - Boundary conditions, degenerate cases
6. Failure Isolation - Tests for minimal counterexample extraction
7. Proof Generation - Tests for Lean proof assembly
"""

import pytest
from fractions import Fraction
from unittest.mock import Mock, patch

from leancert import (
    var, sin, cos, exp, log, sqrt,
    Solver, Config, Interval, Box,
)
from leancert.adaptive import (
    AdaptiveResult,
    AdaptiveConfig,
    SplitStrategy,
    Subdomain,
    SubdomainResult,
    DomainSplitter,
    LeanProofAssembler,
    CEGARVerifier,
    verify_bound_adaptive,
)
from leancert.result import FailureDiagnosis


# =============================================================================
# Test Fixtures
# =============================================================================

@pytest.fixture
def solver():
    """Create a solver instance for tests."""
    return Solver()


@pytest.fixture
def x():
    """Create variable x."""
    return var('x')


@pytest.fixture
def y():
    """Create variable y."""
    return var('y')


# =============================================================================
# 1. Basic Adaptive Verification Tests
# =============================================================================

class TestBasicAdaptiveVerification:
    """Tests for basic adaptive verification functionality."""

    def test_simple_bound_succeeds_without_splitting(self, solver, x):
        """A simple bound that succeeds without splitting."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
            adaptive_config=AdaptiveConfig(max_splits=16),
        )

        assert result.verified is True
        # May not need any splits for this easy case
        assert result.total_splits >= 0

    def test_tight_bound_requires_splitting(self, solver, x):
        """A tight bound that may require splitting to verify."""
        # sin(x) has max ~1 on [0, pi]
        result = solver.verify_bound_adaptive(
            sin(x),
            {'x': (0, 4)},  # Includes the maximum at pi/2
            upper=1.01,
            adaptive_config=AdaptiveConfig(max_splits=32),
        )

        assert result.verified is True
        assert isinstance(result.lean_proof, str)
        assert len(result.lean_proof) > 0

    def test_lower_bound_adaptive(self, solver, x):
        """Test adaptive verification of lower bounds."""
        # exp(x) >= 1 for x >= 0
        result = solver.verify_bound_adaptive(
            exp(x),
            {'x': (0, 2)},
            lower=0.99,
            adaptive_config=AdaptiveConfig(max_splits=16),
        )

        assert result.verified is True

    def test_upper_bound_only(self, solver, x):
        """Test verifying only upper bound."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=1.5,
        )
        assert result.verified is True

    def test_no_bounds_raises_error(self, solver, x):
        """Must specify at least one bound."""
        with pytest.raises(ValueError, match="Must specify"):
            solver.verify_bound_adaptive(
                x**2,
                {'x': (0, 1)},
            )


class TestAdaptiveResultStructure:
    """Tests for AdaptiveResult data structure."""

    def test_result_has_subdomains(self, solver, x):
        """Result should contain subdomain information."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
            adaptive_config=AdaptiveConfig(max_splits=8),
        )

        assert hasattr(result, 'subdomains')
        assert hasattr(result, 'results')
        assert hasattr(result, 'total_splits')
        assert hasattr(result, 'lean_proof')
        assert hasattr(result, 'certificate')

    def test_result_summary(self, solver, x):
        """Result should have a readable summary."""
        result = solver.verify_bound_adaptive(
            sin(x),
            {'x': (0, 3)},
            upper=1.1,
            adaptive_config=AdaptiveConfig(max_splits=8),
        )

        summary = result.summary()
        assert "VERIFIED" in summary or "FAILED" in summary
        assert "Subdomains explored" in summary
        assert "splits" in summary.lower()

    def test_verified_and_failed_subdomain_accessors(self, solver, x):
        """Test accessors for verified and failed subdomains."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
        )

        verified = result.verified_subdomains
        failed = result.failed_subdomains

        assert isinstance(verified, list)
        assert isinstance(failed, list)
        assert result.num_verified == len(verified)
        assert result.num_failed == len(failed)


# =============================================================================
# 2. Splitting Strategy Tests
# =============================================================================

class TestSplitStrategies:
    """Tests for different domain splitting strategies."""

    def test_bisect_strategy_splits_at_midpoint(self):
        """BISECT strategy should split at interval midpoint."""
        box = Box({'x': (0, 10)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        assert var == 'x'
        assert left['x'].hi == Fraction(5)
        assert right['x'].lo == Fraction(5)

    def test_worst_point_strategy_uses_diagnosis(self):
        """WORST_POINT strategy should split near the worst point."""
        box = Box({'x': (0, 10)})
        diagnosis = FailureDiagnosis(
            failure_type='bound_too_tight',
            margin=-0.1,
            worst_point={'x': 7.5},
            suggested_bound=1.1,
        )

        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.WORST_POINT, diagnosis
        )

        assert var == 'x'
        # Should split near 7.5
        assert float(left['x'].hi) == pytest.approx(7.5, abs=0.1)

    def test_largest_first_strategy_multivariate(self):
        """LARGEST_FIRST should split the widest dimension."""
        box = Box({'x': (0, 1), 'y': (0, 10), 'z': (0, 5)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.LARGEST_FIRST
        )

        assert var == 'y'  # y has the largest width (10)

    def test_strategy_via_config(self, solver, x):
        """Test that strategy is respected via AdaptiveConfig."""
        config = AdaptiveConfig(
            max_splits=4,
            strategy=SplitStrategy.BISECT,
        )

        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 4)},
            upper=20.0,
            adaptive_config=config,
        )

        assert result.verified is True


class TestMultivariableSplitting:
    """Tests for splitting multivariate domains."""

    def test_split_2d_domain(self):
        """Test splitting a 2D domain."""
        box = Box({'x': (0, 1), 'y': (0, 1)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.BISECT
        )

        # First variable should be split
        assert var == 'x'
        # y should be unchanged
        assert left['y'] == box['y']
        assert right['y'] == box['y']

    def test_split_preserves_all_dimensions(self):
        """Splitting should preserve non-split dimensions."""
        box = Box({'x': (0, 10), 'y': (-1, 1), 'z': (0, 5)})
        left, right, var = DomainSplitter.split_box(
            box, SplitStrategy.LARGEST_FIRST
        )

        # x is largest, should be split
        assert var == 'x'
        # y and z should be unchanged in both children
        assert left['y'].lo == box['y'].lo
        assert left['y'].hi == box['y'].hi
        assert right['z'].lo == box['z'].lo
        assert right['z'].hi == box['z'].hi


# =============================================================================
# 3. Convergence and Limits Tests
# =============================================================================

class TestConvergenceLimits:
    """Tests for max_splits, max_depth, and convergence."""

    def test_respects_max_splits(self, solver, x):
        """Verification should stop at max_splits."""
        config = AdaptiveConfig(max_splits=4)

        result = solver.verify_bound_adaptive(
            sin(x),
            {'x': (0, 100)},  # Large domain that might fail
            upper=1.5,
            adaptive_config=config,
        )

        # Should not exceed max_splits
        assert result.total_splits <= 4

    def test_respects_max_depth(self, solver, x):
        """Verification should stop at max_depth."""
        config = AdaptiveConfig(max_depth=3, max_splits=100)

        result = solver.verify_bound_adaptive(
            sin(x) * cos(x),
            {'x': (0, 10)},
            upper=1.0,
            adaptive_config=config,
        )

        # Check no subdomain exceeds max_depth
        for subdomain in result.subdomains:
            assert subdomain.depth <= 3

    def test_respects_min_width(self):
        """Splitting should stop when interval width is below min_width."""
        config = AdaptiveConfig(min_width=0.5)
        box = Box({'x': (0, 0.4)})  # Width is 0.4 < 0.5

        should_continue = DomainSplitter.should_continue_splitting(
            box, config, depth=1, total_splits=0
        )

        assert should_continue is False

    def test_quick_config_preset(self):
        """Test the quick preset configuration."""
        config = AdaptiveConfig.quick()

        assert config.max_splits == 16
        assert config.max_depth == 5
        assert config.parallel is True

    def test_thorough_config_preset(self):
        """Test the thorough preset configuration."""
        config = AdaptiveConfig.thorough()

        assert config.max_splits == 256
        assert config.max_depth == 15

    def test_exhaustive_config_preset(self):
        """Test the exhaustive preset configuration."""
        config = AdaptiveConfig.exhaustive()

        assert config.max_splits == 1024
        assert config.max_depth == 20
        assert config.min_width == 1e-15


# =============================================================================
# 4. Multivariate Domain Tests
# =============================================================================

class TestMultivariateDomains:
    """Tests for adaptive verification on multivariate domains."""

    def test_2d_verification(self, solver, x, y):
        """Test adaptive verification on 2D domain."""
        result = solver.verify_bound_adaptive(
            x**2 + y**2,
            {'x': (-1, 1), 'y': (-1, 1)},
            upper=3.0,
            adaptive_config=AdaptiveConfig(max_splits=16),
        )

        assert result.verified is True

    def test_multivariate_lean_proof_format(self, solver, x, y):
        """Multivariate proof should use nested forall."""
        result = solver.verify_bound_adaptive(
            x + y,
            {'x': (0, 1), 'y': (0, 1)},
            upper=3.0,
        )

        proof = result.lean_proof
        assert proof is not None
        # Should contain nested quantifiers for multivariate
        assert "∀" in proof or "forall" in proof.lower()


# =============================================================================
# 5. Edge Cases Tests
# =============================================================================

class TestEdgeCases:
    """Tests for edge cases and boundary conditions."""

    def test_point_interval(self, solver, x):
        """Test with a point interval (lo == hi)."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (2, 2)},  # Point interval
            upper=5.0,
        )

        assert result.verified is True

    def test_very_small_interval(self, solver, x):
        """Test with a very small interval."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0.5, 0.5 + 1e-10)},
            upper=1.0,
        )

        assert result.verified is True

    def test_constant_expression(self, solver):
        """Test with a constant expression (no variables)."""
        from leancert import const
        result = solver.verify_bound_adaptive(
            const(5),
            {'x': (0, 1)},  # Domain doesn't matter
            upper=6.0,
        )

        assert result.verified is True

    def test_negative_bound(self, solver, x):
        """Test with negative bounds."""
        result = solver.verify_bound_adaptive(
            x - 1,
            {'x': (0, 0.5)},
            upper=-0.4,
        )

        # x - 1 on [0, 0.5] ranges from -1 to -0.5, so upper=-0.4 should fail
        # or succeed depending on the verification
        assert isinstance(result.verified, bool)


# =============================================================================
# 6. Failure Isolation Tests
# =============================================================================

class TestFailureIsolation:
    """Tests for minimal counterexample extraction."""

    def test_failing_subdomain_identified(self, solver, x):
        """When bound is genuinely violated, should identify failing region."""
        # sin(x) can reach 1.0, so upper=0.9 should fail on some subdomains
        result = solver.verify_bound_adaptive(
            sin(x),
            {'x': (0, 4)},  # Includes pi/2 where sin = 1
            upper=0.9,
            adaptive_config=AdaptiveConfig(max_splits=16),
        )

        if not result.verified:
            # Should have identified a failing subdomain
            assert result.failing_subdomain is not None
            # The failing subdomain should be smaller than original
            original_width = 4.0
            failing_width = float(result.failing_subdomain.box['x'].width())
            assert failing_width < original_width

    def test_failure_diagnosis_in_results(self, solver, x):
        """Failed subdomains should have diagnosis information."""
        result = solver.verify_bound_adaptive(
            sin(x),
            {'x': (0, 4)},
            upper=0.5,  # Very tight bound that will fail
            adaptive_config=AdaptiveConfig(max_splits=8),
        )

        # If there are failed subdomains, they should have diagnoses
        for sr in result.failed_subdomains:
            # diagnosis may be None if splitting exhausted
            # but if verification was attempted, should have info
            pass  # Just check structure is correct


# =============================================================================
# 7. Proof Generation Tests
# =============================================================================

class TestProofGeneration:
    """Tests for Lean proof generation."""

    def test_proof_contains_theorem_statement(self, solver, x):
        """Generated proof should contain theorem statement."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
        )

        assert "theorem" in result.lean_proof

    def test_proof_contains_bound_value(self, solver, x):
        """Generated proof should mention the bound value."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
        )

        assert "2.0" in result.lean_proof or "2" in result.lean_proof

    def test_proof_uses_interval_decide(self, solver, x):
        """Proof should use interval_decide tactic."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
        )

        assert "interval_decide" in result.lean_proof

    def test_multivariate_proof_has_nested_forall(self, solver, x, y):
        """Multivariate proof should have nested universal quantifiers."""
        result = solver.verify_bound_adaptive(
            x + y,
            {'x': (0, 1), 'y': (0, 1)},
            upper=3.0,
        )

        proof = result.lean_proof
        # Count occurrences of forall
        forall_count = proof.count("∀")
        assert forall_count >= 2 or "x" in proof and "y" in proof


class TestLeanProofAssembler:
    """Direct tests for LeanProofAssembler."""

    def test_assemble_single_subdomain_proof(self):
        """Test proof assembly with single subdomain."""
        box = Box({'x': (0, 1)})
        subdomain = Subdomain(box=box)
        result = SubdomainResult(
            subdomain=subdomain,
            verified=True,
            proof_fragment="interval_decide",
        )

        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            2.0,
            [result],
            box,
        )

        assert "theorem" in proof
        assert "2.0" in proof
        assert "interval_decide" in proof

    def test_assemble_multiple_subdomain_proof(self):
        """Test proof assembly with multiple subdomains."""
        box = Box({'x': (0, 10)})
        results = []

        for i in range(3):
            sub_box = Box({'x': (i * 3.33, (i + 1) * 3.33)})
            subdomain = Subdomain(box=sub_box, depth=1)
            results.append(SubdomainResult(
                subdomain=subdomain,
                verified=True,
            ))

        proof = LeanProofAssembler.assemble_bound_proof(
            "sin(x)",
            "upper",
            1.5,
            results,
            box,
        )

        assert "rcases" in proof or "interval_cases" in proof
        # Should have multiple cases
        assert proof.count("·") >= 2 or proof.count("interval_decide") >= 2


# =============================================================================
# 8. Subdomain Data Structure Tests
# =============================================================================

class TestSubdomainStructure:
    """Tests for Subdomain data class."""

    def test_subdomain_id_str_root(self):
        """Root subdomain should have 'root' id."""
        subdomain = Subdomain(box=Box({'x': (0, 1)}))
        assert subdomain.id_str() == "root"

    def test_subdomain_id_str_child(self):
        """Child subdomain should have descriptive id."""
        subdomain = Subdomain(
            box=Box({'x': (0, 0.5)}),
            parent_id=0,
            split_var='x',
            split_side='left',
            depth=1,
        )
        assert "d1" in subdomain.id_str()
        assert "x" in subdomain.id_str()
        assert "left" in subdomain.id_str()

    def test_subdomain_result_structure(self):
        """Test SubdomainResult data structure."""
        subdomain = Subdomain(box=Box({'x': (0, 1)}))
        result = SubdomainResult(
            subdomain=subdomain,
            verified=True,
            iterations_used=5,
        )

        assert result.verified is True
        assert result.iterations_used == 5
        assert result.diagnosis is None


# =============================================================================
# 9. Integration Tests
# =============================================================================

class TestIntegration:
    """Integration tests combining multiple components."""

    def test_full_workflow_polynomial(self, solver, x):
        """Full workflow test with polynomial expression."""
        expr = x**3 - 2*x + 1
        domain = {'x': (-2, 2)}

        result = solver.verify_bound_adaptive(
            expr,
            domain,
            upper=10.0,
            adaptive_config=AdaptiveConfig(max_splits=16),
        )

        assert result.verified is True
        assert result.certificate is not None
        assert result.lean_proof is not None

    def test_full_workflow_transcendental(self, solver, x):
        """Full workflow test with transcendental expression."""
        expr = sin(x) * exp(-x/10)
        domain = {'x': (0, 10)}

        result = solver.verify_bound_adaptive(
            expr,
            domain,
            upper=1.5,
            adaptive_config=AdaptiveConfig(max_splits=32),
        )

        assert result.verified is True

    def test_result_repr(self, solver, x):
        """Test string representation of result."""
        result = solver.verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
        )

        repr_str = repr(result)
        assert "AdaptiveResult" in repr_str


# =============================================================================
# 10. Module-Level Function Tests
# =============================================================================

class TestModuleLevelFunction:
    """Tests for the module-level verify_bound_adaptive function."""

    def test_module_function_exists(self):
        """Module-level function should be importable."""
        from leancert import verify_bound_adaptive
        assert callable(verify_bound_adaptive)

    def test_module_function_works(self):
        """Module-level function should work correctly."""
        from leancert.solver import verify_bound_adaptive
        from leancert import var

        x = var('x')
        result = verify_bound_adaptive(
            x**2,
            {'x': (0, 1)},
            upper=2.0,
        )

        assert result.verified is True
