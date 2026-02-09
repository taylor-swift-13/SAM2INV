from z3 import *
import numpy as np
import itertools
import re
from typing import List, Dict, Tuple, Any, Optional
import random
import time

class UniMultiPolyFit:
    """
    [Refactor V12 - Enhanced for NLA problems]
    Symbolic regression engine to find relationships V1 = P(V2s) using Z3.
    Pure integer polynomial fitting with progressive degree search.

    Improvements over V11:
    - Larger default coefficient range (-100, 100)
    - Progressive degree search (1 -> 2 -> 3 -> 4)
    - Data point deduplication
    - Better timeout handling
    - More candidate solutions
    """

    def __init__(self, coefficient_range: Tuple[int, int] = (-100, 100)):
        """
        Initialize the polynomial fitter.

        Args:
            coefficient_range: Range of coefficients to search. Default expanded to (-100, 100)
                             to handle cases like y == 3*n*n + 3*n + 1
        """
        self.coeff_range = coefficient_range

    # --- 1. Data Parsing ---
    def _parse_assignments(self, assignments: List[str], all_variables: List[str]) -> List[Dict[str, int]]:
        """Parse assignment strings into data points with deduplication."""
        data_points = []
        seen_points = set()  # For deduplication
        var_set = set(all_variables)

        for i, assign_str in enumerate(assignments):
            point = {}
            parts = assign_str.split('&&')

            for part in parts:
                # Match "var == val", allow '*' in variable names (e.g., "3*z"), support "@pre" suffix
                match = re.match(r'\s*([a-zA-Z0-9_*]+(?:@[a-zA-Z]+)?)\s*==\s*(-?\d+)\s*', part.strip())

                if not match:
                    continue

                var_name, val_str = match.groups()

                if var_name not in var_set:
                    continue

                point[var_name] = int(val_str)

            if not var_set.issubset(set(point.keys())):
                continue

            # Create a hashable key for deduplication
            point_key = tuple(sorted(point.items()))
            if point_key in seen_points:
                continue
            seen_points.add(point_key)

            data_points.append(point)

        return data_points

    # --- 2. Basis Function Generation ---
    def _generate_polynomial_terms(self, variables: List[str], max_total_degree: int) -> List[Tuple]:
        """Generates polynomial terms where sum(powers) <= max_total_degree."""
        num_vars = len(variables)
        per_var_range = range(max_total_degree + 1)
        all_products = itertools.product(per_var_range, repeat=num_vars)

        monomial_powers_list = [
            powers for powers in all_products if sum(powers) <= max_total_degree
        ]
        return monomial_powers_list

    def _generate_bitwise_terms(self, variables: List[str]) -> List[Tuple]:
        """Generates commutative bitwise basis functions."""
        terms = []
        for v1, v2 in itertools.combinations(variables, 2):
            terms.append(('and', v1, v2))
            terms.append(('or', v1, v2))
            terms.append(('xor', v1, v2))
        return terms

    # --- 3. Formula String Formatting ---
    def _format_term(self, key: Tuple, val: int, indep_vars: List[str]) -> Tuple[str, bool]:
        term_str = ""
        is_constant_term = False

        if all(isinstance(i, int) for i in key):
            powers = key
            var_parts = []
            is_constant_term = True
            for var_name, power in zip(indep_vars, powers):
                if power > 0:
                    is_constant_term = False
                if power == 1:
                    var_parts.append(var_name)
                elif power > 1:
                    # Convert power to multiplication (x^3 -> x*x*x)
                    var_parts.append("*".join([var_name] * power))

            if not is_constant_term:
                term_str = "*".join(var_parts)
            else:
                term_str = "1"
        else:
            op = key[0]
            if op in ('and', 'or', 'xor'):
                op_symbol = {'and': '&', 'or': '|', 'xor': '^'}[op]
                term_str = f"({key[1]} {op_symbol} {key[2]})"

        abs_val = abs(val)

        if all(i == 0 for i in key) and all(isinstance(i, int) for i in key):
            # Constant term
            return f"{abs_val}", True

        if abs_val == 1:
            return term_str, False

        # Simplify output format, e.g., 1*x*y should just output x*y
        if term_str == "1":
             return f"{abs_val}", True

        return f"{abs_val}*{term_str}", False

    def _coefficients_to_formula(self, coeffs: Dict[Tuple, int], dep_var: str, indep_vars: List[str]) -> str:
        terms_with_info = []
        is_only_constant = True

        for key, val in coeffs.items():
            if val == 0:
                continue

            term_str, is_const = self._format_term(key, val, indep_vars)

            if not is_const:
                is_only_constant = False

            if is_const:
                sort_key = 100000
            else:
                sort_key = len(term_str)

            terms_with_info.append({
                'sign': " + " if val > 0 else " - ",
                'term_str': term_str,
                'is_constant': is_const,
                'sort_key': sort_key
            })

        sorted_terms = sorted(terms_with_info, key=lambda x: (
            x['sort_key']
        ))

        if not sorted_terms:
            return f"{dep_var} == 0", True

        final_terms = []
        first_term = True
        for info in sorted_terms:
            if first_term:
                sign = "" if info['sign'] == " + " else "-"
                final_terms.append(f"{sign}{info['term_str']}")
                first_term = False
            else:
                final_terms.append(f"{info['sign']}{info['term_str']}")

        return f"{dep_var} == " + " ".join(final_terms), is_only_constant

    # --- 4. Z3 Solver ---
    def _solve_for_relation(self, data_points: List[Dict[str, int]], dep_var: str, indep_vars: List[str],
                          all_term_keys: List[Tuple], max_solutions: int, timeout_seconds: float = 5.0,
                          coeff_range: Tuple[int, int] = None) -> List[Dict[Tuple, int]]:
        """
        Solve for polynomial coefficients using Z3.

        Args:
            coeff_range: Override coefficient range for this solve attempt
        """
        if coeff_range is None:
            coeff_range = self.coeff_range

        s = Solver()
        s.set("timeout", int(timeout_seconds * 1000))
        coefficients = {}

        for key in all_term_keys:
            name = f'a_{key}'
            coeff_var = Int(name)
            coefficients[key] = coeff_var
            s.add(coeff_var >= coeff_range[0], coeff_var <= coeff_range[1])

        for point in data_points:
            v1_value = point[dep_var]
            poly_sum = 0
            for key, coeff_var in coefficients.items():
                term_val = 0
                if all(isinstance(i, int) for i in key):
                    term_val = 1
                    for var_name, power in zip(indep_vars, key):
                        term_val *= (point[var_name] ** power)
                else:
                    op, v1_name, v2_name = key[0], key[1], key[2]
                    v1, v2 = point.get(v1_name, 0), point.get(v2_name, 0)
                    op_map = {'and': lambda x, y: x & y, 'or': lambda x, y: x | y, 'xor': lambda x, y: x ^ y}
                    term_val = op_map[op](v1, v2)
                poly_sum += coeff_var * term_val
            s.add(v1_value == poly_sum)

        found_solutions_coeffs = []
        start_time = time.time()
        no_result_timeout = 2.0  # Increased from 1.0
        last_result_time = start_time

        while len(found_solutions_coeffs) < max_solutions:
            elapsed_time = time.time() - start_time
            if elapsed_time >= timeout_seconds:
                break

            if time.time() - last_result_time > no_result_timeout:
                break

            check_result = s.check()
            if check_result == sat:
                m = s.model()
                result_coeffs = {}
                blocking_clause = []

                for key, var in coefficients.items():
                    val_model = m[var]
                    val_long = val_model.as_long() if val_model is not None else 0
                    result_coeffs[key] = val_long
                    blocking_clause.append(var != val_long)

                found_solutions_coeffs.append(result_coeffs)
                last_result_time = time.time()
                s.add(Or(blocking_clause))
            elif check_result == unknown:
                break
            else:
                break

        return found_solutions_coeffs

    def _estimate_required_degree(self, data_points: List[Dict[str, int]], dep_var: str, indep_vars: List[str]) -> int:
        """
        Estimate the polynomial degree needed based on data characteristics.

        Heuristics:
        - If dependent variable grows much faster than independent variables, likely higher degree
        - Check for cubic/quadratic patterns
        """
        if len(data_points) < 3:
            return 2

        # Sort data points by first independent variable
        if not indep_vars:
            return 2

        first_var = indep_vars[0]
        sorted_points = sorted(data_points, key=lambda p: p.get(first_var, 0))

        # Compute first and second differences
        dep_values = [p[dep_var] for p in sorted_points]

        if len(dep_values) < 3:
            return 2

        # First differences
        first_diff = [dep_values[i+1] - dep_values[i] for i in range(len(dep_values)-1)]

        # Second differences
        if len(first_diff) >= 2:
            second_diff = [first_diff[i+1] - first_diff[i] for i in range(len(first_diff)-1)]

            # If second differences are constant (non-zero), it's quadratic
            if len(set(second_diff)) == 1 and second_diff[0] != 0:
                return 2

            # Third differences
            if len(second_diff) >= 2:
                third_diff = [second_diff[i+1] - second_diff[i] for i in range(len(second_diff)-1)]

                # If third differences are constant (non-zero), it's cubic
                if len(set(third_diff)) == 1 and third_diff[0] != 0:
                    return 3

        # Check magnitude ratio
        max_dep = max(abs(v) for v in dep_values) if dep_values else 1
        max_indep = max(
            max(abs(p.get(v, 0)) for p in sorted_points)
            for v in indep_vars
        ) if indep_vars and sorted_points else 1

        if max_indep > 0:
            ratio = max_dep / (max_indep ** 2)
            if ratio > 10:  # Likely cubic or higher
                return 3

        return 2

    # --- 5. Main Public Method ---
    def find_relation(self, assignments_lists: List[List[str]], dependent_var: str, independent_vars: List[str],
                    max_total_poly_degree: int, max_solutions: int = 5, use_bitwise: bool = False,
                    timeout_seconds: float = 5.0, progressive_search: bool = True) -> List[Dict[str, Any]]:
        """
        Find relationships between variables using polynomial fitting.

        Enhanced V12 features:
        - Progressive degree search: automatically tries higher degrees if lower fails
        - Better coefficient range handling
        - Data deduplication

        Args:
            assignments_lists: Lists of assignment strings
            dependent_var: Variable to predict
            independent_vars: Variables to use as predictors
            max_total_poly_degree: Maximum polynomial degree to try
            max_solutions: Maximum number of solutions to find
            use_bitwise: Whether to include bitwise operations
            timeout_seconds: Timeout per degree attempt
            progressive_search: If True, try degrees 1, 2, 3, ... up to max_total_poly_degree

        Returns:
            List of solution dictionaries with 'formula', 'length', etc.
        """
        all_vars = [dependent_var] + independent_vars
        merged_assignments = [item for sublist in assignments_lists for item in sublist]
        data_points = self._parse_assignments(merged_assignments, all_vars)

        if not data_points:
            return []

        # Deduplicated data points
        unique_data_points = data_points

        # Estimate required degree from data
        estimated_degree = self._estimate_required_degree(unique_data_points, dependent_var, independent_vars)

        # Progressive search: try from low to high degree
        if progressive_search:
            # Start from estimated degree or 1, go up to max or 4
            start_degree = min(1, estimated_degree)
            end_degree = max(max_total_poly_degree, min(estimated_degree + 1, 4))
            degrees_to_try = list(range(start_degree, end_degree + 1))
        else:
            degrees_to_try = [max_total_poly_degree]

        all_found_solutions = []

        for degree in degrees_to_try:
            polynomial_terms = self._generate_polynomial_terms(independent_vars, degree)
            base_bitwise_terms = self._generate_bitwise_terms(independent_vars) if use_bitwise else []
            all_term_keys = list(set(polynomial_terms + base_bitwise_terms))

            # Try with different coefficient ranges
            coeff_ranges = [
                self.coeff_range,  # Default (-100, 100)
            ]

            # If default range is small, also try larger ranges
            if self.coeff_range[1] - self.coeff_range[0] < 200:
                coeff_ranges.append((-100, 100))
            if self.coeff_range[1] - self.coeff_range[0] < 1000:
                coeff_ranges.append((-500, 500))

            for coeff_range in coeff_ranges:
                # Adjust timeout based on degree (higher degree needs more time)
                adjusted_timeout = timeout_seconds * (1 + 0.5 * (degree - 1))

                list_of_coeffs = self._solve_for_relation(
                    unique_data_points, dependent_var, independent_vars,
                    all_term_keys, max_solutions, adjusted_timeout, coeff_range
                )

                if list_of_coeffs:
                    for coeffs in list_of_coeffs:
                        formula, is_only_constant = self._coefficients_to_formula(coeffs, dependent_var, independent_vars)
                        length = sum(1 for v in coeffs.values() if v != 0)

                        # Filter trivial solutions (pure constant expressions)
                        if is_only_constant and length == 1:
                            continue

                        # Avoid duplicate formulas
                        if any(s['formula'] == formula for s in all_found_solutions):
                            continue

                        all_found_solutions.append({
                            'dependent_var': dependent_var,
                            'formula': formula,
                            'length': length,
                            'is_only_constant': is_only_constant,
                            'degree': degree
                        })

            # If we found solutions at this degree, we can stop
            # (lower degree solutions are preferred)
            if all_found_solutions and not progressive_search:
                break

        # Sort by length (prefer simpler solutions)
        sorted_solutions = sorted(all_found_solutions, key=lambda s: (s['length'], s.get('degree', 0)))

        # Limit to max_solutions
        return sorted_solutions[:max_solutions * 2]  # Return more candidates for selection

    def find_relation_with_validation(self, assignments_lists: List[List[str]], dependent_var: str,
                                       independent_vars: List[str], max_total_poly_degree: int,
                                       validation_assignments: List[str] = None,
                                       max_solutions: int = 5, use_bitwise: bool = False,
                                       timeout_seconds: float = 5.0) -> List[Dict[str, Any]]:
        """
        Find relations and validate against additional data points.

        This helps filter out overfitted solutions that don't generalize.
        """
        solutions = self.find_relation(
            assignments_lists, dependent_var, independent_vars,
            max_total_poly_degree, max_solutions * 2, use_bitwise, timeout_seconds
        )

        if not validation_assignments:
            return solutions[:max_solutions]

        # Parse validation data
        all_vars = [dependent_var] + independent_vars
        validation_points = self._parse_assignments(validation_assignments, all_vars)

        if not validation_points:
            return solutions[:max_solutions]

        # Validate each solution
        validated_solutions = []
        for sol in solutions:
            formula = sol['formula']
            # Extract expression from "var == expr"
            match = re.match(r'(\w+)\s*==\s*(.+)', formula)
            if not match:
                continue

            var_name, expr = match.groups()

            # Validate against all validation points
            is_valid = True
            for point in validation_points:
                try:
                    # Substitute values and evaluate
                    eval_expr = expr
                    for v in independent_vars:
                        eval_expr = re.sub(r'\b' + re.escape(v) + r'\b', str(point.get(v, 0)), eval_expr)

                    # Handle multiplication notation
                    eval_expr = eval_expr.replace('*', ' * ')
                    computed = eval(eval_expr)
                    expected = point[dependent_var]

                    if computed != expected:
                        is_valid = False
                        break
                except:
                    is_valid = False
                    break

            if is_valid:
                validated_solutions.append(sol)

        return validated_solutions[:max_solutions] if validated_solutions else solutions[:max_solutions]


# --- External Test Logic ---

def generate_and_test_formula(target_formula_blackbox: str, dependent_var: str, independent_vars: List[str],
                             num_samples: int = 15, max_degree: int = 3, max_solutions: int = 5):
    """
    Generate random data and attempt to fit, without k-value iteration.
    """
    print(f"\n=========================================================")
    print(f" 🚀 Symbolic Regression (Progressive Degree Search, Max Degree={max_degree})")
    print(f"🎯 Target: {dependent_var} = {target_formula_blackbox}")
    print(f"=========================================================")

    # 1. Generate data
    assignments_list = []
    input_range = (1, 10)

    for _ in range(num_samples):
        inputs = {var: random.randint(*input_range) for var in independent_vars}
        try:
            # Ensure result is integer
            val_float = eval(target_formula_blackbox, {}, inputs)
            val_int = int(round(val_float))
        except:
            continue

        parts = [f"{dependent_var}=={val_int}"]
        for key, val in inputs.items():
            parts.append(f"{key}=={val}")
        assignments_list.append(" && ".join(parts))

    if not assignments_list:
        print("❌ No valid data generated")
        return []

    # 2. Call solver with enhanced settings
    fitter = UniMultiPolyFit(coefficient_range=(-100, 100))
    solutions = fitter.find_relation(
        assignments_lists=[assignments_list],
        dependent_var=dependent_var,
        independent_vars=independent_vars,
        max_total_poly_degree=max_degree,
        max_solutions=max_solutions,
        use_bitwise=False,
        progressive_search=True
    )

    # 3. Output
    if not solutions:
        print("❌ No formula found.")
        return []

    print(f"\n✅ Found {len(solutions)} solutions (sorted by complexity):")
    results = []
    for i, sol in enumerate(solutions):
        degree = sol.get('degree', '?')
        line = f"{i+1}. Length={sol['length']}, Degree={degree} -> {sol['formula']}"
        print(line)
        results.append(line)

    return results


if __name__ == '__main__':
    # Test case 1: Quadratic polynomial
    print("\n" + "="*60)
    print("TEST 1: Quadratic (x = y^2 + 2y - 5)")
    print("="*60)
    generate_and_test_formula(
        target_formula_blackbox='y * y + 2 * y - 5',
        dependent_var='x',
        independent_vars=['y'],
        max_degree=3,
        max_solutions=5
    )

    # Test case 2: Cubic polynomial (like NLA_lipus/1.c: x = n^3)
    print("\n" + "="*60)
    print("TEST 2: Cubic (x = n^3)")
    print("="*60)
    generate_and_test_formula(
        target_formula_blackbox='n * n * n',
        dependent_var='x',
        independent_vars=['n'],
        max_degree=4,
        max_solutions=5
    )

    # Test case 3: y = 3*n^2 + 3*n + 1 (from NLA_lipus/1.c)
    print("\n" + "="*60)
    print("TEST 3: y = 3*n^2 + 3*n + 1")
    print("="*60)
    generate_and_test_formula(
        target_formula_blackbox='3 * n * n + 3 * n + 1',
        dependent_var='y',
        independent_vars=['n'],
        max_degree=3,
        max_solutions=5
    )

    # Test case 4: x = y*y (from NLA_lipus/21.c)
    print("\n" + "="*60)
    print("TEST 4: x = y^2")
    print("="*60)
    generate_and_test_formula(
        target_formula_blackbox='y * y',
        dependent_var='x',
        independent_vars=['y'],
        max_degree=2,
        max_solutions=5
    )
