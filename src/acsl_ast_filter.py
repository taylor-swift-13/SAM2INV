#!/usr/bin/env python3
"""
ACSL Loop Invariant Syntax Tree Filter

Uses Python AST to parse and validate ACSL loop invariants against
the Frama-C/WP allowed constructs.
"""

import re
import ast
import yaml
from typing import List, Tuple, Optional, Any, Set
from dataclasses import dataclass, field
from enum import Enum


class ViolationType(Enum):
    FORBIDDEN_CONSTRUCT = "Forbidden construct"
    UNDEFINED_SYMBOL = "Undefined symbol"
    TYPE_ERROR = "Type error"
    SYNTAX_ERROR = "Syntax error"
    UNSUPPORTED_FEATURE = "Unsupported feature"


@dataclass
class Violation:
    type: ViolationType
    message: str
    position: Tuple[int, int] = (0, 0)


@dataclass
class ValidationResult:
    is_valid: bool
    violations: List[Violation] = field(default_factory=list)
    ast_nodes: List[Any] = field(default_factory=list)


class ACSLConfig:
    def __init__(self, config_path: Optional[str] = None):
        self.enable_ast_filter: bool = True
        self.enable_regex_filter: bool = True
        self.allowed_operators: dict = {}
        self.allowed_types: List[str] = []
        self.forbidden_keywords: List[str] = []
        self.forbidden_math_ops: List[str] = []
        self.forbidden_quantifiers: List[str] = []
        self.known_variables: Set[str] = set()
        self.allowed_functions: Set[str] = set()
        self._load_config(config_path)

    def _load_config(self, config_path: Optional[str]):
        path = config_path if config_path else "/home/yangfp/SE2INV/src/config.yaml"

        try:
            with open(path, 'r') as f:
                config = yaml.safe_load(f)

            self.enable_ast_filter = config.get('enable_ast_filter', True)
            self.enable_regex_filter = config.get('enable_regex_filter', True)
            self.allowed_operators = config.get('allowed', {}).get('operators', {})
            self.allowed_types = config.get('allowed', {}).get('types', [])
            self.forbidden_keywords = config.get('forbidden', {}).get('keywords', [])
            self.forbidden_math_ops = config.get('forbidden', {}).get('math_operators', [])
            self.forbidden_quantifiers = config.get('forbidden', {}).get('quantifiers', [])
            self.known_variables = set(config.get('known_variables', []))
            self.allowed_functions = set(config.get('allowed_functions', []))
        except FileNotFoundError:
            pass


class LoopInvariantFilter:
    def __init__(self, config: Optional[ACSLConfig] = None):
        self.config = config if config else ACSLConfig()
        self.violations: List[Violation] = []
        self.allowed_types: List[str] = self.config.allowed_types

    def validate_invariant(self, invariant: str) -> ValidationResult:
        result = ValidationResult(is_valid=True)
        stripped = invariant.strip()

        if self.config.enable_regex_filter:
            self._check_regex_patterns(stripped, result)

        if self.config.enable_ast_filter:
            self._check_ast_compliance(stripped, result)

        return result

    def _check_regex_patterns(self, expr: str, result: ValidationResult):
        forbidden = [
            ('predicate', 'Custom predicate definition'),
            ('inductive', 'Inductive definition'),
            ('logic', 'Logic function definition'),
            ('axiomatic', 'Axiomatic block'),
            ('lemma', 'Lemma'),
            (':=', 'Assignment operator'),
        ]

        for pattern, description in forbidden:
            if pattern == ':=':
                if pattern in expr:
                    result.violations.append(Violation(
                        ViolationType.FORBIDDEN_CONSTRUCT,
                        f"{description}: {pattern}"
                    ))
                    result.is_valid = False
            elif re.search(r'\b' + pattern + r'\b', expr, re.IGNORECASE):
                result.violations.append(Violation(
                    ViolationType.FORBIDDEN_CONSTRUCT,
                    f"{description}: {pattern}"
                ))
                result.is_valid = False

        if '\\let' in expr:
            result.violations.append(Violation(
                ViolationType.FORBIDDEN_CONSTRUCT,
                "Let binding '\\let' is forbidden"
            ))
            result.is_valid = False

        for op in self.config.forbidden_quantifiers:
            if op in expr:
                result.violations.append(Violation(
                    ViolationType.FORBIDDEN_CONSTRUCT,
                    f"Quantifier '{op}' is forbidden"
                ))
                result.is_valid = False

        for op in self.config.forbidden_math_ops:
            if op in expr:
                result.violations.append(Violation(
                    ViolationType.FORBIDDEN_CONSTRUCT,
                    f"Math operator '{op}' is forbidden"
                ))
                result.is_valid = False
        
        # Check for ellipsis (...) which is not valid ACSL syntax
        if '...' in expr:
            result.violations.append(Violation(
                ViolationType.SYNTAX_ERROR,
                "Ellipsis '...' is not valid ACSL syntax. Use explicit expressions or summation/product notation instead."
            ))
            result.is_valid = False

    def _check_ast_compliance(self, expr: str, result: ValidationResult):
        self._check_undefined_functions(expr, result)
        self._check_quantifier_types(expr, result)

    def _check_undefined_functions(self, expr: str, result: ValidationResult):
        func_pattern = r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\('
        matches = re.findall(func_pattern, expr)

        for func in matches:
            if func not in self.config.allowed_functions and func not in self.config.known_variables:
                result.violations.append(Violation(
                    ViolationType.UNDEFINED_SYMBOL,
                    f"Function '{func}' is not defined or not in allowed list"
                ))
                result.is_valid = False

    def _check_quantifier_types(self, expr: str, result: ValidationResult):
        quantifier_match = re.match(r'\\forall\s+(\w+)\s+(\w+)\s*;', expr)
        if quantifier_match:
            qtype = quantifier_match.group(1)
            if qtype.lower() not in self.allowed_types:
                result.violations.append(Violation(
                    ViolationType.TYPE_ERROR,
                    f"Quantifier type '{qtype}' should be 'integer', 'real', or 'boolean'"
                ))
                result.is_valid = False

    def validate_loop_annotation(self, annotation: str) -> List[ValidationResult]:
        results = []
        lines = annotation.split('\n')

        for line in lines:
            stripped = line.strip()
            if 'loop invariant' in stripped:
                invariant = re.sub(r'^\s*loop invariant\s+', '', stripped).rstrip(';')
                result = self.validate_invariant(invariant)
                results.append(result)
            elif 'loop assigns' in stripped:
                results.append(ValidationResult(is_valid=True))
            elif 'loop variant' in stripped:
                results.append(ValidationResult(is_valid=True))

        return results

    def filter_invariants(self, invariants: List[str]) -> Tuple[List[str], List[Tuple[str, List[Violation]]]]:
        valid = []
        rejected = []

        for invariant in invariants:
            result = self.validate_invariant(invariant)
            if result.is_valid:
                valid.append(invariant)
            else:
                rejected.append((invariant, result.violations))

        return valid, rejected


def validate_and_filter(invariants: List[str], config_path: Optional[str] = None, verbose: bool = True) -> List[str]:
    config = ACSLConfig(config_path)
    filter_obj = LoopInvariantFilter(config)
    valid, rejected = filter_obj.filter_invariants(invariants)

    if verbose:
        print("\n" + "=" * 60)
        print("FILTER CONFIG")
        print("=" * 60)
        print(f"AST Filter: {'enabled' if config.enable_ast_filter else 'disabled'}")
        print(f"Regex Filter: {'enabled' if config.enable_regex_filter else 'disabled'}")

        if rejected:
            print("\n" + "=" * 60)
            print("FILTERED INVARIANTS (Violations)")
            print("=" * 60)
            for inv, violations in rejected:
                print(f"\n✗ {inv}")
                for v in violations:
                    print(f"  [{v.type.value}] {v.message}")

        if valid:
            print("\n" + "=" * 60)
            print("VALID INVARIANTS")
            print("=" * 60)
            for v in valid:
                print(f"  ✓ {v}")

        print("\n" + "=" * 60)
        print(f"Summary: {len(valid)} valid, {len(rejected)} rejected out of {len(invariants)}")
        print("=" * 60)

    return valid


if __name__ == "__main__":
    test_cases = [
        "0 <= i <= n",
        "s == i * (i + 1) / 2",
        "\\forall integer k; 0 <= k < i ==> a[k] == 0",
        "\\exists integer k; a[k] == x",
        "w == \\product integer t",
        "sorted(a, i)",
        "sum(a, i) == expected",
        "inductive(relation, x, y)",
        "\\let x = 5; x + 1",
        "a := b + c",
        "\\forall int k; k >= 0",
        "p == n!",
        "\\product integer t; 0 <= t < i ==> a[t]",
        "\\max(a, b) > 0",
        "\\separated(a, b)",
    ]

    print("ACSL Loop Invariant Filter (Configurable)")
    print("=" * 60)

    valid = validate_and_filter(test_cases, verbose=True)
