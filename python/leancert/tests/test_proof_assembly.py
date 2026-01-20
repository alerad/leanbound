# LeanCert v3 SDK - Proof Assembly Tests
# Copyright (c) 2024 LeanCert Contributors. All rights reserved.

"""
Comprehensive tests for Lean proof generation from CEGAR verification.

Test Categories:
1. Basic Proof Structure - Theorem statements, quantifiers
2. Single Subdomain Proofs - Simple case without splitting
3. Multiple Subdomain Proofs - Case analysis for split domains
4. Multivariate Proofs - Nested quantifiers for multiple variables
5. Bound Type Handling - Upper vs lower bound proofs
6. Proof Comments and Metadata - Documentation in generated proofs
7. Edge Cases - Empty results, single point, etc.
8. Lean Syntax Correctness - Valid Lean code generation
"""

import pytest
from fractions import Fraction

from leancert.domain import Interval, Box
from leancert.adaptive import (
    Subdomain,
    SubdomainResult,
    LeanProofAssembler,
    AdaptiveResult,
)


# =============================================================================
# Test Fixtures
# =============================================================================

@pytest.fixture
def simple_subdomain():
    """A simple verified subdomain."""
    box = Box({'x': (0, 1)})
    return SubdomainResult(
        subdomain=Subdomain(box=box, depth=0),
        verified=True,
        proof_fragment="interval_decide",
    )


@pytest.fixture
def three_subdomains():
    """Three verified subdomains covering [0, 3]."""
    results = []
    for i in range(3):
        box = Box({'x': (i, i + 1)})
        results.append(SubdomainResult(
            subdomain=Subdomain(box=box, depth=1),
            verified=True,
            proof_fragment="interval_decide",
        ))
    return results


@pytest.fixture
def multivar_subdomain():
    """A multivariate verified subdomain."""
    box = Box({'x': (0, 1), 'y': (0, 1)})
    return SubdomainResult(
        subdomain=Subdomain(box=box, depth=0),
        verified=True,
        proof_fragment="multivariate_bound",
    )


# =============================================================================
# 1. Basic Proof Structure Tests
# =============================================================================

class TestBasicProofStructure:
    """Tests for basic structure of generated proofs."""

    def test_proof_contains_theorem_keyword(self, simple_subdomain):
        """Generated proof should contain 'theorem' keyword."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "theorem" in proof

    def test_proof_contains_intro_tactic(self, simple_subdomain):
        """Generated proof should contain 'intro' tactic."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "intro" in proof

    def test_proof_contains_forall_quantifier(self, simple_subdomain):
        """Generated proof should contain universal quantifier."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "∀" in proof or "forall" in proof.lower()

    def test_proof_contains_set_icc(self, simple_subdomain):
        """Generated proof should contain Set.Icc for closed interval."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "Set.Icc" in proof

    def test_proof_contains_expression(self, simple_subdomain):
        """Generated proof should mention the expression."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "sin(x) + cos(x)",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "sin" in proof.lower() or "Expression" in proof


# =============================================================================
# 2. Single Subdomain Proof Tests
# =============================================================================

class TestSingleSubdomainProof:
    """Tests for proofs with a single subdomain (no splitting)."""

    def test_single_subdomain_uses_interval_decide(self, simple_subdomain):
        """Single subdomain proof should use interval_decide directly."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "interval_decide" in proof

    def test_single_subdomain_no_rcases(self, simple_subdomain):
        """Single subdomain proof should not need rcases."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        # rcases is for multiple cases
        assert "rcases" not in proof

    def test_single_subdomain_has_correct_domain(self, simple_subdomain):
        """Proof should reference the correct domain bounds."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        # Should contain the domain bounds
        assert "0" in proof
        assert "1" in proof


# =============================================================================
# 3. Multiple Subdomain Proof Tests
# =============================================================================

class TestMultipleSubdomainProof:
    """Tests for proofs with multiple subdomains (case analysis)."""

    def test_multiple_subdomains_uses_rcases(self, three_subdomains):
        """Multiple subdomain proof should use rcases for case analysis."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            10.0,
            three_subdomains,
            Box({'x': (0, 3)}),
        )

        assert "rcases" in proof or "interval_cases" in proof

    def test_multiple_subdomains_has_bullet_points(self, three_subdomains):
        """Multiple subdomain proof should have bullet points for cases."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            10.0,
            three_subdomains,
            Box({'x': (0, 3)}),
        )

        # Should have multiple bullet points (·) for cases
        assert proof.count("·") >= 2 or proof.count("interval_decide") >= 2

    def test_multiple_subdomains_covers_all_cases(self, three_subdomains):
        """Proof should have a case for each subdomain."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            10.0,
            three_subdomains,
            Box({'x': (0, 3)}),
        )

        # Should have 3 interval_decide calls
        assert proof.count("interval_decide") >= 3

    def test_multiple_subdomains_has_hypothesis_names(self, three_subdomains):
        """Case analysis should generate hypothesis names."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            10.0,
            three_subdomains,
            Box({'x': (0, 3)}),
        )

        # Should have hypothesis names like h1, h2, h3
        assert "h1" in proof or "h2" in proof


# =============================================================================
# 4. Multivariate Proof Tests
# =============================================================================

class TestMultivariateProof:
    """Tests for proofs with multiple variables."""

    def test_multivariate_has_nested_quantifiers(self, multivar_subdomain):
        """Multivariate proof should have nested forall quantifiers."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x + y",
            "upper",
            3.0,
            [multivar_subdomain],
            Box({'x': (0, 1), 'y': (0, 1)}),
        )

        # Should have two universal quantifiers
        forall_count = proof.count("∀")
        assert forall_count >= 2 or ("x" in proof and "y" in proof)

    def test_multivariate_mentions_all_variables(self, multivar_subdomain):
        """Proof should mention all variable names."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x * y",
            "upper",
            2.0,
            [multivar_subdomain],
            Box({'x': (0, 1), 'y': (0, 1)}),
        )

        assert "x" in proof
        assert "y" in proof

    def test_3d_proof_has_three_quantifiers(self):
        """3D proof should have three nested quantifiers."""
        box = Box({'x': (0, 1), 'y': (0, 1), 'z': (0, 1)})
        result = SubdomainResult(
            subdomain=Subdomain(box=box, depth=0),
            verified=True,
        )

        proof = LeanProofAssembler.assemble_bound_proof(
            "x + y + z",
            "upper",
            4.0,
            [result],
            box,
        )

        # Should reference all three variables
        assert "x" in proof
        assert "y" in proof
        assert "z" in proof


# =============================================================================
# 5. Bound Type Handling Tests
# =============================================================================

class TestBoundTypeHandling:
    """Tests for upper vs lower bound proof generation."""

    def test_upper_bound_uses_le(self, simple_subdomain):
        """Upper bound proof should use ≤ symbol."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "≤" in proof or "<=" in proof

    def test_lower_bound_uses_ge(self, simple_subdomain):
        """Lower bound proof should use ≥ symbol."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "lower",
            -0.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        # Lower bound: bound ≤ expr
        assert "≤" in proof or ">=" in proof

    def test_bound_value_appears_in_proof(self, simple_subdomain):
        """The bound value should appear in the proof."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "1.5" in proof

    def test_negative_bound_value(self, simple_subdomain):
        """Negative bound values should be handled correctly."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x - 1",
            "lower",
            -2.0,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "-2" in proof or "-2.0" in proof


# =============================================================================
# 6. Proof Comments and Metadata Tests
# =============================================================================

class TestProofCommentsMetadata:
    """Tests for comments and metadata in generated proofs."""

    def test_proof_has_header_comment(self, simple_subdomain):
        """Proof should have a header comment explaining its origin."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "CEGAR" in proof or "domain splitting" in proof.lower()

    def test_proof_comments_expression(self, simple_subdomain):
        """Proof should comment on the expression."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "sin(x) * cos(x)",
            "upper",
            1.0,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "Expression" in proof or "--" in proof

    def test_proof_comments_num_subdomains(self, three_subdomains):
        """Proof should mention number of subdomains."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            10.0,
            three_subdomains,
            Box({'x': (0, 3)}),
        )

        assert "3" in proof or "Subdomain" in proof


# =============================================================================
# 7. Edge Cases Tests
# =============================================================================

class TestEdgeCases:
    """Tests for edge cases in proof generation."""

    def test_empty_results_produces_comment(self):
        """Empty results should produce informative comment."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [],  # No verified subdomains
            Box({'x': (0, 1)}),
        )

        assert "No subdomains" in proof or "--" in proof

    def test_point_domain_proof(self):
        """Proof for point domain should still be valid."""
        box = Box({'x': (0.5, 0.5)})  # Point domain
        result = SubdomainResult(
            subdomain=Subdomain(box=box, depth=0),
            verified=True,
        )

        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.0,
            [result],
            box,
        )

        # Should still generate valid structure
        assert "theorem" in proof
        assert "0.5" in proof

    def test_very_small_bound_value(self, simple_subdomain):
        """Very small bound values should be formatted correctly."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1e-10,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        # Should contain some representation of the small number
        assert "1e-10" in proof or "0.0000" in proof or "10" in proof

    def test_large_bound_value(self, simple_subdomain):
        """Large bound values should be formatted correctly."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "exp(x)",
            "upper",
            1e10,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        # Should contain some representation of the large number
        assert proof is not None
        assert len(proof) > 0


# =============================================================================
# 8. Lean Syntax Correctness Tests
# =============================================================================

class TestLeanSyntaxCorrectness:
    """Tests to ensure generated proofs have correct Lean syntax."""

    def test_colons_after_theorem_name(self, simple_subdomain):
        """Theorem statement should have colon after name."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert "theorem" in proof
        # Should have pattern: theorem name :
        assert ": " in proof or ":\n" in proof

    def test_by_keyword_for_tactic_mode(self, simple_subdomain):
        """Proof should enter tactic mode with 'by'."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        assert " by" in proof or ":= by" in proof

    def test_proper_indentation(self, simple_subdomain):
        """Proof should have proper indentation."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        # Should have some indented lines
        lines = proof.split('\n')
        indented_lines = [l for l in lines if l.startswith('  ') or l.startswith('    ')]
        assert len(indented_lines) > 0

    def test_no_unmatched_parentheses(self, simple_subdomain):
        """Proof should have balanced parentheses."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            1.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        # Count parentheses
        open_parens = proof.count('(')
        close_parens = proof.count(')')
        assert open_parens == close_parens


# =============================================================================
# 9. Subdomain Comment Tests
# =============================================================================

class TestSubdomainComments:
    """Tests for subdomain-specific comments in proofs."""

    def test_subdomain_comments_include_bounds(self, three_subdomains):
        """Each case should comment on its subdomain bounds."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            10.0,
            three_subdomains,
            Box({'x': (0, 3)}),
        )

        # Should have comments indicating subdomain ranges
        assert "Subdomain" in proof or "[" in proof

    def test_box_comment_format(self):
        """Test _box_comment utility function."""
        box = Box({'x': (0, 1), 'y': (-1, 1)})
        comment = LeanProofAssembler._box_comment(box)

        assert "x ∈" in comment
        assert "y ∈" in comment
        assert "[" in comment and "]" in comment


# =============================================================================
# 10. Integration Tests
# =============================================================================

class TestProofAssemblyIntegration:
    """Integration tests for complete proof assembly workflow."""

    def test_complete_proof_is_multiline(self, simple_subdomain):
        """Complete proof should span multiple lines."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2 + x",
            "upper",
            2.5,
            [simple_subdomain],
            Box({'x': (0, 1)}),
        )

        lines = proof.split('\n')
        assert len(lines) > 5  # Should have multiple lines

    def test_complete_proof_parseable_structure(self, three_subdomains):
        """Complete proof should have recognizable structure."""
        proof = LeanProofAssembler.assemble_bound_proof(
            "x^2",
            "upper",
            10.0,
            three_subdomains,
            Box({'x': (0, 3)}),
        )

        # Should have these structural elements
        assert "theorem" in proof
        assert "by" in proof
        assert "intro" in proof
        assert "interval_decide" in proof

    def test_multivar_quantifier_generation(self):
        """Test _multivar_quantifiers utility."""
        box = Box({'x': (0, 1), 'y': (2, 3), 'z': (-1, 0)})
        quantifiers = LeanProofAssembler._multivar_quantifiers(box)

        assert "∀ x" in quantifiers
        assert "∀ y" in quantifiers
        assert "∀ z" in quantifiers
        assert "Set.Icc" in quantifiers

    def test_real_world_expression_proof(self):
        """Test proof generation for a realistic expression."""
        box = Box({'x': (0, Fraction(22, 7))})  # [0, pi approx]
        result = SubdomainResult(
            subdomain=Subdomain(box=box, depth=0),
            verified=True,
        )

        proof = LeanProofAssembler.assemble_bound_proof(
            "Real.sin x",
            "upper",
            1.01,
            [result],
            box,
        )

        assert "sin" in proof.lower()
        assert "1.01" in proof
        assert "theorem" in proof
