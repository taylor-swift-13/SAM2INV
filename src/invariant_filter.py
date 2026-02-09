#!/usr/bin/env python3
"""
Frama-C Loop Invariant Filter

Filters generated loop invariants based on the system prompt rules.
Rejects forbidden patterns and validates allowed constructs.
"""

import re
import ast
from typing import List, Tuple, Optional, Set
from dataclasses import dataclass
from enum import Enum


class ViolationType(Enum):
    FORBIDDEN_PREDICATE = "Custom predicate"
    FORBIDDEN_INDUCTIVE = "Inductive definition"
    FORBIDDEN_LOGIC_FUNCTION = "Logic function"
    FORBIDDEN_AXIOMATIC = "Axiomatic block"
    FORBIDDEN_LEMMA = "Lemma"
    UNDEFINED_IDENTIFIER = "Undefined identifier"
    WRONG_QUANTIFIER_TYPE = "Wrong quantifier type (use 'integer', not 'int')"
    MISSING_QUANTIFIER_BOUNDS = "Missing quantifier bounds"


@dataclass
class ValidationResult:
    is_valid: bool
    invariant: str
    violations: List[Tuple[ViolationType, str]]


class LoopInvariantFilter:
    """Filters and validates ACSL loop invariants against forbidden patterns."""

    FORBIDDEN_PATTERNS = [
        (r'\bpredicate\s+', ViolationType.FORBIDDEN_PREDICATE, "Custom predicate definition"),
        (r'\binductive\s+', ViolationType.FORBIDDEN_INDUCTIVE, "Inductive definition"),
        (r'\blogic\s+', ViolationType.FORBIDDEN_LOGIC_FUNCTION, "Logic function"),
        (r'\baxiomatic\s+', ViolationType.FORBIDDEN_AXIOMATIC, "Axiomatic block"),
        (r'\blemma\s+', ViolationType.FORBIDDEN_LEMMA, "Lemma"),
    ]

    FORBIDDEN_KEYWORDS = [
        (r'\\forall\s+', "Quantifier \\forall is forbidden in loop invariants"),
        (r'\\exists\s+', "Quantifier \\exists is forbidden in loop invariants"),
        (r'\\product\s+', "Mathematical operator \\product is not an ACSL built-in"),
        (r'\\sum\s+', "Mathematical operator \\sum is not an ACSL built-in"),
        (r'\\min\s+', "Mathematical operator \\min is not an ACSL built-in"),
        (r'\\max\s+', "Mathematical operator \\max is not an ACSL built-in"),
        (r'(?:\d+|\w+|\))\s*!(?!=)', "Logical operator '!' can only be applied to boolean values, not numeric expressions. If you meant factorial, ACSL does not support factorial operator"),
    ]

    ALLOWED_QUANTIFIER_TYPES = {'integer', 'real', 'boolean'}
    FORBIDDEN_QUANTIFIER_TYPES = {'int', 'long', 'short', 'char', 'float', 'double'}

    def __init__(self, known_variables: Optional[Set[str]] = None):
        self.known_variables = known_variables if known_variables is not None else set()

    def validate_invariant(self, invariant: str) -> ValidationResult:
        """Validate a single loop invariant."""
        violations = []

        stripped = invariant.strip()

        for pattern, vtype, description in self.FORBIDDEN_PATTERNS:
            if re.search(pattern, stripped, re.IGNORECASE):
                violations.append((vtype, description))

        for pattern, description in self.FORBIDDEN_KEYWORDS:
            if re.search(pattern, stripped):
                violations.append((ViolationType.UNDEFINED_IDENTIFIER, description))

        if not stripped.startswith(('loop invariant', 'loop assigns', 'loop variant')):
            stripped = f"loop invariant {stripped}"

        return ValidationResult(
            is_valid=len(violations) == 0,
            invariant=invariant,
            violations=violations
        )

    def validate_loop_annotation(self, annotation: str) -> List[ValidationResult]:
        """Validate all loop invariants in an annotation block."""
        results = []
        lines = annotation.split('\n')

        for line in lines:
            stripped = line.strip()
            if 'loop invariant' in stripped:
                invariant = re.sub(r'^\s*loop invariant\s+', '', stripped).rstrip(';')
                result = self.validate_invariant(invariant)
                result.invariant = stripped
                results.append(result)
            elif 'loop assigns' in stripped or 'loop variant' in stripped:
                results.append(ValidationResult(
                    is_valid=True,
                    invariant=stripped,
                    violations=[]
                ))

        return results

    def filter_invariants(self, invariants: List[str]) -> Tuple[List[str], List[Tuple[str, List[Tuple[ViolationType, str]]]]]:
        """Filter a list of invariants, returning valid ones and rejected ones with reasons."""
        valid = []
        rejected = []

        for invariant in invariants:
            result = self.validate_invariant(invariant)
            if result.is_valid:
                valid.append(invariant)
            else:
                rejected.append((invariant, result.violations))

        return valid, rejected


def check_invariant_syntax(invariant: str) -> Optional[str]:
    """Check for common ACSL syntax errors."""
    issues = []

    if '\\product' in invariant or '\\sum' in invariant or '\\min' in invariant or '\\max' in invariant:
        issues.append("Mathematical operators like \\product, \\sum, \\min, \\max are not ACSL built-ins")

    if re.search(r'\b[a-zA-Z_]\w*\s*\([^)]*\)\s*[=!]', invariant):
        issues.append("Possible custom function/predicate call detected")

    if '\\let' in invariant:
        issues.append("\\let binding is not supported in loop invariants")

    if ':=' in invariant:
        issues.append(":=(assignment) not allowed in logic expressions")

    if issues:
        return "; ".join(issues)
    return None


def validate_and_filter(invariants: List[str], verbose: bool = True) -> List[str]:
    """Main entry point for filtering invariants."""
    filter_obj = LoopInvariantFilter()
    valid, rejected = filter_obj.filter_invariants(invariants)

    if verbose and rejected:
        print("\n=== Filtered Invariants ===")
        for inv, violations in rejected:
            print(f"\nREJECTED: {inv}")
            for vtype, desc in violations:
                print(f"  - [{vtype.value}] {desc}")

    return valid


if __name__ == "__main__":
    import sys

    test_invariants = [
        "w == \\product integer t; 0 <= t < i ==> a[t]",
        "\\forall integer k; 0 <= k < i ==> a[k] >= 0",
        "\\exists integer k; a[k] == x",
        "\\forall int k; 0 <= k < i ==> a[k] == 0",
        "sorted(a, i)",
        "sum(a, i) == expected",
        "inductive(relation, x, y)",
        "w == \\product integer t",
    ]

    print("Testing invariant filter...")
    print("=" * 60)

    valid = validate_and_filter(test_invariants)

    print("\n\n=== Valid Invariants ===")
    for v in valid:
        print(f"  ✓ {v}")

    print("\n" + "=" * 60)
    print(f"Total: {len(test_invariants)} | Valid: {len(valid)} | Rejected: {len(test_invariants) - len(valid)}")
