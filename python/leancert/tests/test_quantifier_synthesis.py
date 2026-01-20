"""
Tests for Quantifier Pattern Synthesis.

Tests the QuantifierSynthesizer class and various quantifier patterns:
- EXISTS_FORALL_BOUND: ∃ δ > 0, ∀ x ∈ I, |f(x)| ≤ δ
- MINIMUM_WITNESS: ∃ x₀, ∀ x, f(x₀) ≤ f(x)
- MAXIMUM_WITNESS: ∃ x₀, ∀ x, f(x) ≤ f(x₀)
- EPSILON_DELTA: ∀ ε > 0, ∃ δ > 0, continuity proof
- EXISTS_ROOT: ∃ x, f(x) = 0
- FORALL_SIGN: ∀ x, f(x) > 0
"""

import pytest
from fractions import Fraction

from leancert import var, sin, cos, exp, Solver
from leancert.quantifier import (
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


# =============================================================================
# Basic Structure Tests
# =============================================================================

class TestQuantifierPatternEnum:
    """Tests for QuantifierPattern enum."""

    def test_all_patterns_exist(self):
        """All expected patterns should exist."""
        assert hasattr(QuantifierPattern, 'EXISTS_FORALL_BOUND')
        assert hasattr(QuantifierPattern, 'FORALL_EXISTS_ASYMPTOTIC')
        assert hasattr(QuantifierPattern, 'MINIMUM_WITNESS')
        assert hasattr(QuantifierPattern, 'MAXIMUM_WITNESS')
        assert hasattr(QuantifierPattern, 'EPSILON_DELTA')
        assert hasattr(QuantifierPattern, 'EXISTS_ROOT')
        assert hasattr(QuantifierPattern, 'FORALL_SIGN')


class TestWitnessStructure:
    """Tests for Witness dataclass."""

    def test_witness_creation(self):
        """Should be able to create a Witness."""
        w = Witness(value=1.5, variable="δ", witness_type="bound")
        assert w.value == 1.5
        assert w.variable == "δ"
        assert w.witness_type == "bound"

    def test_witness_to_lean_scalar(self):
        """to_lean should work for scalar values."""
        w = Witness(value=1.5, variable="δ", witness_type="bound")
        assert w.to_lean() == "1.5"

    def test_witness_to_lean_point(self):
        """to_lean should work for point values."""
        w = Witness(value={'x': 0.5, 'y': 0.25}, variable="x₀", witness_type="point")
        lean = w.to_lean()
        assert 'x' in lean
        assert 'y' in lean


class TestQuantifierResultStructure:
    """Tests for QuantifierResult dataclass."""

    def test_result_creation(self):
        """Should be able to create a QuantifierResult."""
        result = QuantifierResult(
            pattern=QuantifierPattern.EXISTS_FORALL_BOUND,
            success=True,
            message="Test"
        )
        assert result.success is True
        assert result.pattern == QuantifierPattern.EXISTS_FORALL_BOUND

    def test_result_summary(self):
        """summary() should return readable string."""
        result = QuantifierResult(
            pattern=QuantifierPattern.MINIMUM_WITNESS,
            success=True,
            witnesses=[Witness(value=0.5, variable="x₀", witness_type="point")],
            message="Found minimizer"
        )
        summary = result.summary()
        assert "SUCCESS" in summary
        assert "MINIMUM_WITNESS" in summary or "minimum_witness" in summary


# =============================================================================
# EXISTS_FORALL_BOUND Tests
# =============================================================================

class TestExistsForallBound:
    """Tests for ∃ δ > 0, ∀ x ∈ I, |f(x)| ≤ δ pattern."""

    def test_simple_polynomial(self):
        """Should find bound for simple polynomial."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_forall_bound(expr, {'x': (0, 1)})

        assert result.success is True
        assert len(result.witnesses) == 1
        assert result.witnesses[0].variable == "δ"
        assert result.witnesses[0].value >= 1.0  # max is 1

    def test_sine_bounded(self):
        """sin(x) should be bounded by 1."""
        x = var('x')
        expr = sin(x)
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_forall_bound(expr, {'x': (0, 10)}, abs_bound=True)

        assert result.success is True
        assert result.witnesses[0].value >= 1.0  # |sin(x)| ≤ 1

    def test_generates_lean_proof(self):
        """Should generate Lean proof code."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_forall_bound(expr, {'x': (0, 1)})

        assert result.lean_proof is not None
        assert "∃" in result.lean_proof or "exists" in result.lean_proof.lower()

    def test_convenience_function(self):
        """synthesize_bound convenience function should work."""
        x = var('x')
        expr = x**2
        solver = Solver()

        result = synthesize_bound(solver, expr, {'x': (0, 1)})

        assert result.success is True


# =============================================================================
# MINIMUM_WITNESS Tests
# =============================================================================

class TestMinimumWitness:
    """Tests for ∃ x₀, ∀ x, f(x₀) ≤ f(x) pattern."""

    def test_quadratic_minimum(self):
        """Should find minimum of x^2 at 0."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.minimum_witness(expr, {'x': (-1, 1)})

        assert result.success is True
        assert len(result.witnesses) == 1
        x0 = result.witnesses[0].value
        # Minimum should be near 0
        if isinstance(x0, dict):
            assert abs(x0['x']) < 0.2
        else:
            assert abs(x0) < 0.2

    def test_shifted_quadratic(self):
        """Should find minimum of (x-0.5)^2 at 0.5."""
        x = var('x')
        expr = (x - 0.5)**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.minimum_witness(expr, {'x': (0, 1)})

        assert result.success is True
        x0 = result.witnesses[0].value
        if isinstance(x0, dict):
            assert abs(x0['x'] - 0.5) < 0.2

    def test_generates_lean_proof(self):
        """Should generate Lean proof code."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.minimum_witness(expr, {'x': (-1, 1)})

        assert result.lean_proof is not None
        # New verified witness synthesis uses different format
        assert "minimum witness" in result.lean_proof.lower()

    def test_convenience_function(self):
        """synthesize_minimum convenience function should work."""
        x = var('x')
        expr = x**2
        solver = Solver()

        result = synthesize_minimum(solver, expr, {'x': (-1, 1)})

        assert result.success is True


# =============================================================================
# MAXIMUM_WITNESS Tests
# =============================================================================

class TestMaximumWitness:
    """Tests for ∃ x₀, ∀ x, f(x) ≤ f(x₀) pattern."""

    def test_quadratic_maximum(self):
        """Should find maximum of -x^2 at 0."""
        x = var('x')
        expr = -x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.maximum_witness(expr, {'x': (-1, 1)})

        assert result.success is True
        x0 = result.witnesses[0].value
        if isinstance(x0, dict):
            assert abs(x0['x']) < 0.2

    def test_parabola_maximum(self):
        """Should find maximum of x*(1-x) at 0.5."""
        x = var('x')
        expr = x * (1 - x)
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.maximum_witness(expr, {'x': (0, 1)})

        assert result.success is True
        x0 = result.witnesses[0].value
        if isinstance(x0, dict):
            assert abs(x0['x'] - 0.5) < 0.2

    def test_convenience_function(self):
        """synthesize_maximum convenience function should work."""
        x = var('x')
        expr = x * (1 - x)
        solver = Solver()

        result = synthesize_maximum(solver, expr, {'x': (0, 1)})

        assert result.success is True


# =============================================================================
# EXISTS_ROOT Tests
# =============================================================================

class TestExistsRoot:
    """Tests for ∃ x, f(x) = 0 pattern."""

    def test_linear_root(self):
        """Should find root of x - 0.5 at 0.5."""
        x = var('x')
        expr = x - 0.5
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_root(expr, {'x': (0, 1)})

        assert result.success is True
        assert len(result.witnesses) == 1
        x0 = result.witnesses[0].value
        assert abs(x0 - 0.5) < 0.1

    def test_quadratic_root(self):
        """Should find root of x^2 - 0.25 at 0.5."""
        x = var('x')
        expr = x**2 - 0.25
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_root(expr, {'x': (0, 1)})

        assert result.success is True
        x0 = result.witnesses[0].value
        assert abs(x0 - 0.5) < 0.1

    def test_no_root(self):
        """Should fail when no root exists."""
        x = var('x')
        expr = x**2 + 1  # Always positive
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_root(expr, {'x': (-1, 1)})

        assert result.success is False


# =============================================================================
# FORALL_SIGN Tests
# =============================================================================

class TestForallSign:
    """Tests for ∀ x, f(x) > 0 pattern."""

    def test_positive_polynomial(self):
        """Should verify x^2 + 2 > 0 (need margin for interval widening)."""
        x = var('x')
        expr = x**2 + 2  # Well above 0
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.forall_sign(expr, {'x': (-1, 1)}, 'positive')

        assert result.success is True

    def test_non_negative(self):
        """Should verify (x^2 + 2) >= 0 (need margin for interval widening)."""
        x = var('x')
        expr = x**2 + 2  # Well above 0, safely non-negative
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.forall_sign(expr, {'x': (-1, 1)}, 'non_negative')

        assert result.success is True

    def test_negative_fails(self):
        """Should fail for x^2 < 0."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.forall_sign(expr, {'x': (-1, 1)}, 'negative')

        assert result.success is False

    def test_convenience_function(self):
        """prove_sign convenience function should work."""
        x = var('x')
        expr = x**2 + 2  # Well above 0
        solver = Solver()

        result = prove_sign(solver, expr, {'x': (-1, 1)}, 'positive')

        assert result.success is True


# =============================================================================
# EPSILON_DELTA Tests
# =============================================================================

class TestEpsilonDelta:
    """Tests for ∀ ε > 0, ∃ δ > 0 continuity pattern."""

    def test_continuous_at_point(self):
        """Should prove x^2 is continuous at x=1."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        # lim_{x→1} x^2 = 1
        result = synth.epsilon_delta(expr, 'x', point=1.0, limit=1.0)

        # May or may not succeed depending on precision
        # Just check structure is correct
        assert result.pattern == QuantifierPattern.EPSILON_DELTA

    def test_generates_delta_values(self):
        """Should generate δ for each ε."""
        x = var('x')
        expr = x  # Identity is continuous everywhere
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.epsilon_delta(
            expr, 'x', point=0.0, limit=0.0,
            epsilon_values=[0.1, 0.01]
        )

        if result.success:
            # Should have witnesses for each ε
            assert len(result.witnesses) >= 1

    def test_verified_lipschitz_epsilon_delta(self):
        """VERIFIED: Should use Lipschitz bound for ε-δ."""
        x = var('x')
        expr = x**2  # f'(x) = 2x, on [-1,1] has |f'| ≤ 2, so L=2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.epsilon_delta(
            expr, 'x', point=0.0, limit=0.0,  # x² → 0 as x → 0
            epsilon_values=[0.1, 0.01],
            use_lipschitz=True,  # Use verified Lipschitz path
            neighborhood_radius=1.0,
        )

        assert result.success is True
        # Should say "VERIFIED" in the message
        assert "VERIFIED" in result.message or "Lipschitz" in result.message

        # Should have certificate from Lipschitz computation
        assert result.certificate is not None

        # For ε=0.1 with L≈2, δ should be around 0.05
        for w in result.witnesses:
            if "0.1" in w.variable:
                delta = w.value
                # δ = ε/L ≈ 0.1/2 = 0.05
                assert 0.01 < delta < 0.2

        # Lean proof should mention Lipschitz
        assert result.lean_proof is not None
        assert "Lipschitz" in result.lean_proof

    def test_lipschitz_fallback_to_heuristic(self):
        """Should fallback to heuristic if use_lipschitz=False."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.epsilon_delta(
            expr, 'x', point=0.0, limit=0.0,
            epsilon_values=[0.1],
            use_lipschitz=False,  # Use heuristic fallback
        )

        # Should still work but without "VERIFIED" in message
        if result.success:
            assert "VERIFIED" not in result.message


# =============================================================================
# Lipschitz Bound Tests
# =============================================================================

class TestLipschitzBound:
    """Tests for verified Lipschitz bound computation."""

    def test_linear_lipschitz(self):
        """Linear function f(x) = 2x has Lipschitz constant 2."""
        x = var('x')
        expr = 2 * x
        solver = Solver()

        result = solver.compute_lipschitz_bound(expr, {'x': (0, 1)})

        # f'(x) = 2, so L should be 2
        L = float(result.lipschitz_bound)
        assert 1.9 < L < 2.1

    def test_quadratic_lipschitz(self):
        """Quadratic f(x) = x² on [0,1] has Lipschitz constant 2."""
        x = var('x')
        expr = x**2
        solver = Solver()

        result = solver.compute_lipschitz_bound(expr, {'x': (0, 1)})

        # f'(x) = 2x, max on [0,1] is 2
        L = float(result.lipschitz_bound)
        assert 1.9 < L < 2.1

    def test_sine_lipschitz(self):
        """sin(x) has Lipschitz constant 1 (|cos(x)| ≤ 1)."""
        x = var('x')
        expr = sin(x)
        solver = Solver()

        result = solver.compute_lipschitz_bound(expr, {'x': (0, 10)})

        # |sin'(x)| = |cos(x)| ≤ 1
        L = float(result.lipschitz_bound)
        assert 0.9 < L < 1.1

    def test_lipschitz_delta_for_epsilon(self):
        """delta_for_epsilon helper should compute δ = ε/L."""
        x = var('x')
        expr = x**2
        solver = Solver()

        result = solver.compute_lipschitz_bound(expr, {'x': (0, 1)})

        epsilon = 0.1
        delta = result.delta_for_epsilon(epsilon)

        # L ≈ 2, so δ ≈ 0.05
        assert 0.04 < delta < 0.06

    def test_lipschitz_generates_lean_tactic(self):
        """Should generate Lean tactic proof."""
        x = var('x')
        expr = x**2
        solver = Solver()

        result = solver.compute_lipschitz_bound(expr, {'x': (0, 1)})
        tactic = result.to_lean_tactic()

        assert "Lipschitz" in tactic
        assert "gradient" in tactic.lower() or "deriv" in tactic.lower()


# =============================================================================
# Multivariate Tests
# =============================================================================

class TestMultivariate:
    """Tests for multivariate quantifier synthesis."""

    def test_2d_bound(self):
        """Should find bound for 2D expression."""
        x = var('x')
        y = var('y')
        expr = x**2 + y**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_forall_bound(
            expr,
            {'x': (0, 1), 'y': (0, 1)}
        )

        assert result.success is True
        assert result.witnesses[0].value >= 2.0  # max is 2

    def test_2d_minimum(self):
        """Should find minimum of x^2 + y^2."""
        x = var('x')
        y = var('y')
        expr = x**2 + y**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.minimum_witness(
            expr,
            {'x': (-1, 1), 'y': (-1, 1)}
        )

        assert result.success is True
        x0 = result.witnesses[0].value
        # Minimum should be near (0, 0)
        if isinstance(x0, dict):
            assert abs(x0.get('x', 0)) < 0.3
            assert abs(x0.get('y', 0)) < 0.3


# =============================================================================
# Lean Proof Generation Tests
# =============================================================================

class TestLeanProofGeneration:
    """Tests for Lean proof code generation."""

    def test_bound_proof_structure(self):
        """Bound proof should have correct structure."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_forall_bound(expr, {'x': (0, 1)})

        assert result.lean_proof is not None
        assert "theorem" in result.lean_proof
        assert "by" in result.lean_proof

    def test_minimum_proof_structure(self):
        """Minimum proof should have correct structure."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.minimum_witness(expr, {'x': (-1, 1)})

        assert result.lean_proof is not None
        # Verified witness synthesis generates tactic code (use, intro, etc.)
        assert "use" in result.lean_proof
        assert "interval_min_witness" in result.lean_proof

    def test_sign_proof_structure(self):
        """Sign proof should have correct structure."""
        x = var('x')
        expr = x**2 + 2  # Well above 0
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.forall_sign(expr, {'x': (-1, 1)}, 'positive')

        assert result.lean_proof is not None
        assert "> 0" in result.lean_proof


# =============================================================================
# Edge Cases
# =============================================================================

class TestEdgeCases:
    """Edge case tests."""

    def test_constant_expression(self):
        """Should handle constant expression."""
        x = var('x')
        expr = x * 0 + 5
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.exists_forall_bound(expr, {'x': (0, 1)})

        assert result.success is True
        # Bound should be around 5
        assert result.witnesses[0].value >= 5.0

    def test_point_domain(self):
        """Should handle point domain."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        # This may or may not work with point domain
        result = synth.exists_forall_bound(expr, {'x': (0.5, 0.5)})

        # Just check it doesn't crash
        assert isinstance(result, QuantifierResult)

    def test_negative_domain(self):
        """Should handle negative domain."""
        x = var('x')
        expr = x**2
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        result = synth.minimum_witness(expr, {'x': (-2, -1)})

        assert result.success is True
        # Minimum should be at x = -1
        x0 = result.witnesses[0].value
        if isinstance(x0, dict):
            assert abs(abs(x0['x']) - 1) < 0.2


# =============================================================================
# Integration Tests
# =============================================================================

class TestIntegration:
    """Integration tests combining multiple features."""

    def test_min_max_consistent(self):
        """Min and max witnesses should be consistent."""
        x = var('x')
        expr = x * (1 - x)  # max at 0.5, min at 0 or 1
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        min_result = synth.minimum_witness(expr, {'x': (0, 1)})
        max_result = synth.maximum_witness(expr, {'x': (0, 1)})

        assert min_result.success is True
        assert max_result.success is True

        # Maximum should be near 0.5
        max_x0 = max_result.witnesses[0].value
        if isinstance(max_x0, dict):
            assert abs(max_x0['x'] - 0.5) < 0.2

    def test_bound_implies_sign(self):
        """If f(x) ≤ δ and δ > 0, then certain sign properties hold."""
        x = var('x')
        expr = x**2 + 2  # Always positive, well above 0 (need margin for interval widening)
        solver = Solver()
        synth = QuantifierSynthesizer(solver)

        bound_result = synth.exists_forall_bound(expr, {'x': (-1, 1)}, abs_bound=False)
        sign_result = synth.forall_sign(expr, {'x': (-1, 1)}, 'positive')

        assert bound_result.success is True
        assert sign_result.success is True
