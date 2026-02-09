import re
from typing import Dict, List, Tuple, Any, Optional
from config import LLMConfig


def llmfind_relation(assignments_lists: List[List[str]], dependent_var: str, independent_vars: List[str],
                   max_total_poly_degree: int, max_solutions: int = 5, use_bitwise: bool = False,
                   timeout_seconds: float = 5.0, progressive_search: bool = True,
                   llm_config: Optional[LLMConfig] = None) -> List[Dict[str, Any]]:
    """
    Find relationships between variables using LLM (same interface as pfit.find_relation).

    This function provides a fallback when polynomial fitting fails. It uses the LLM
    to analyze execution traces and discover mathematical relationships between variables.

    Args:
        assignments_lists: Lists of assignment strings (execution traces)
        dependent_var: Variable to predict (output variable)
        independent_vars: Variables to use as predictors (input variables)
        max_total_poly_degree: Maximum polynomial degree (not used by LLM, but kept for interface consistency)
        max_solutions: Maximum number of solutions to return
        use_bitwise: Whether to include bitwise operations (not used by LLM, but kept for interface consistency)
        timeout_seconds: Timeout for LLM API call (not strictly enforced, but provides guidance)
        progressive_search: Whether to try different approaches (not used by LLM, but kept for interface consistency)
        llm_config: LLM configuration (optional, defaults to LLMConfig())

    Returns:
        List of solution dictionaries with the same format as pfit.find_relation:
        - dependent_var: The dependent variable
        - formula: The discovered formula (e.g., "x == y + 2*z")
        - length: Complexity score (number of operations in the formula)
        - is_only_constant: Whether the formula is a constant
        - degree: Estimated degree (1 for linear, 2 for quadratic, etc.)
    """
    if llm_config is None:
        llm_config = LLMConfig()

    # Flatten the assignments lists
    all_assignments = [item for sublist in assignments_lists for item in sublist]

    # Create a prompt for the LLM
    prompt = _build_llmfit_prompt(all_assignments, dependent_var, independent_vars, max_total_poly_degree)

    # Call LLM via llm.py
    from llm import Chatbot
    chatbot = Chatbot(llm_config)
    response = chatbot.chat(prompt)

    # Parse the LLM response into the expected format
    solutions = _parse_llmfit_response(response, dependent_var, independent_vars)

    # Sort by length and limit to max_solutions
    sorted_solutions = sorted(solutions, key=lambda s: s['length'])
    return sorted_solutions[:max_solutions]


def _build_llmfit_prompt(assignments: List[str], dependent_var: str,
                          independent_vars: List[str], max_degree: int) -> str:
    """Build a prompt for the LLM to find relationships."""
    # Format assignments as a table
    assignment_lines = []
    for i, assign in enumerate(assignments[:20], 1):  # Limit to first 20 to avoid context overflow
        assignment_lines.append(f"  {i}. {assign}")
    if len(assignments) > 20:
        assignment_lines.append(f"  ... ({len(assignments) - 20} more traces)")

    assignments_str = "\n".join(assignment_lines)

    # Build the prompt
    prompt = f"""### Task: Find Mathematical Relationship ###

Analyze the execution traces below and find the relationship between variables.

### Variables ###
- Dependent variable (output): {dependent_var}
- Independent variables (inputs): {', '.join(independent_vars)}

### Execution Traces ###
{assignments_str}

### Your Task ###

Find a formula that relates {dependent_var} to {independent_vars}.
The formula should be in the format: {dependent_var} == <expression>

**Guidelines:**
1. Look for patterns in the data (try multiple formula types)
2. The formula should hold for ALL of the traces provided
3. Provide multiple candidate formulas if different patterns exist
4. Try diverse formula types, not just polynomials

**Supported Formula Types:**
- **Polynomials:** x + 2*y - 1, x*x + y*y, x*x*x + 2*x*y + y
- **Rational functions:** x / y, (x + y) / (x - y), x / (y + 1)
- **Modulo operations:** x % y, (x + y) % 5, x % (y + 1)
- **Bitwise operations:** x & y, x | y, x ^ y, x << y, x >> y
- **Conditional expressions:** x < y ? x : y, x >= 0 ? x : -x
- **Max/Min/abs:** x > y ? x : y (max), x < y ? x : y (min), x < 0 ? -x : x (abs)
- **Floor/Ceiling:** x / y (integer division), x % y (remainder)
- **Mixed expressions:** x*x + y*y + x*y, (x + 1)*(y + 1) - 1

**Expected Output Format:**
{dependent_var} == <formula_1>
{dependent_var} == <formula_2>
{dependent_var} == <formula_3>

**IMPORTANT:** Output ONLY the formula lines, nothing else! Do NOT include explanations or examples.

### Examples ###

**Example 1 (Linear):**
Traces: z==3 && x==1 && y==1, z==4 && x==2 && y==1, z==5 && x==1 && y==2
{dependent_var} == x + 2*y

**Example 2 (Quadratic):**
Traces: z==1 && x==0, z==4 && x==1, z==9 && x==2, z==16 && x==3
{dependent_var} == x*x

**Example 3 (Modulo):**
Traces: z==1 && x==5 && y==2, z==2 && x==7 && y==2, z==0 && x==6 && y==2
{dependent_var} == x % y

**Example 4 (Integer Division):**
Traces: z==2 && x==5 && y==2, z==3 && x==7 && y==2, z==3 && x==6 && y==2
{dependent_var} == x / y

**Example 5 (Bitwise AND):**
Traces: z==0 && x==5 && y==2, z==2 && x==7 && y==2, z==2 && x==6 && y==2
{dependent_var} == x & y

**Example 6 (Conditional/Max):**
Traces: z==5 && x==3 && y==5, z==5 && x==5 && y==3, z==7 && x==7 && y==5
{dependent_var} == (x > y ? x : y)

**Example 7 (Absolute Value):**
Traces: z==3 && x==3, z==3 && x==-3, z==5 && x==5, z==5 && x==-5
{dependent_var} == (x < 0 ? -x : x)

**Example 8 (Mixed):**
Traces: z==7 && x==1 && y==2, z==13 && x==2 && y==3, z==21 && x==3 && y==4
{dependent_var} == x*x + x*y + y*y

**Now analyze the provided traces and output the formula(s):**
"""

    return prompt


def _parse_llmfit_response(response: str, dependent_var: str,
                           independent_vars: List[str]) -> List[Dict[str, Any]]:
    """Parse the LLM response into the expected format."""
    solutions = []

    # Split response by lines to process each line separately
    lines = response.split('\n')

    # Pattern to match formulas like "z == x + 2*y" or "z == x*x"
    pattern = rf'^\s*{re.escape(dependent_var)}\s*==\s*(.+?)\s*$'

    for line in lines:
        match = re.match(pattern, line)
        if match:
            expression = match.group(1).strip()

            # Filter out examples or non-formula content
            if 'Traces:' in line or 'Output:' in line:
                continue

            formula = f"{dependent_var} == {expression}"

            # Calculate length (simple heuristic: count operators)
            length = _calculate_formula_length(expression)

            # Determine if it's a constant
            is_only_constant = _is_constant_formula(expression)

            # Estimate degree
            degree = _estimate_formula_degree(expression)

            solutions.append({
                'dependent_var': dependent_var,
                'formula': formula,
                'length': length,
                'is_only_constant': is_only_constant,
                'degree': degree
            })

    # If no formulas found, return empty list
    if not solutions:
        return []

    return solutions


def _calculate_formula_length(expression: str) -> int:
    """Calculate the complexity score of a formula."""
    # Base complexity score
    length = 1

    # Count operators (higher weight for complex operators)
    operators = {
        '+': 1,
        '-': 1,
        '*': 2,
        '/': 2,
        '%': 2,
        '&': 2,
        '|': 2,
        '^': 2,
        '<<': 2,
        '>>': 2,
        '?': 3,  # Conditional operator
        ':': 1,
        '<': 1,
        '>': 1,
        '<=': 1,
        '>=': 1,
        '==': 1,
        '!=': 1,
    }

    for op, weight in operators.items():
        length += expression.count(op) * weight

    return length


def _is_constant_formula(expression: str) -> bool:
    """Check if the formula is a constant."""
    try:
        # Try to parse as an integer
        int(expression.strip())
        return True
    except ValueError:
        return False


def _estimate_formula_degree(expression: str) -> int:
    """Estimate the degree of a polynomial formula.

    For non-polynomial expressions (modulo, conditional, bitwise, etc.),
    returns a default degree of 1.
    """
    # Check for conditional expressions (ternary operator)
    if '?' in expression:
        return 1  # Conditional expressions are treated as linear for simplicity

    # Check for bitwise or modulo operations (non-polynomial)
    if any(op in expression for op in ['%', '&', '|', '^', '<<', '>>']):
        return 1  # Non-polynomial, default to linear

    # Check for division (rational function)
    if '/' in expression:
        return 1  # Rational function, default to linear

    # Check for polynomial powers (x^2, x*x, x*x*x, etc.)
    power_patterns = [
        (r'\w+\s*\*\*\s*2', 2),      # x**2
        (r'\w+\s*\*\*\s*3', 3),      # x**3
        (r'\w+\s*\*\*\s*\d+', 4),     # x**n (higher degree)
        (r'\w+\s*\*\s*\w+', 2),       # x*x (implicit multiplication)
        (r'\w+\s*\*\s*\w+\s*\*\s*\w+', 3),  # x*x*x
    ]

    degree = 1  # Default to linear

    for pattern, deg in power_patterns:
        match = re.search(pattern, expression)
        if match:
            # For x**n, extract n
            if '\*\*' in pattern and r'\d+' in pattern:
                n_match = re.search(r'\*\*\s*(\d+)', expression)
                if n_match:
                    degree = max(degree, int(n_match.group(1)))
            else:
                degree = max(degree, deg)

    return degree


class LLMInvariantFitter:
    """LLM-based invariant fitter for discovering loop invariants from execution traces."""

    def __init__(self, llm_config: Optional[LLMConfig] = None, logger=None):
        """
        Initialize the LLM invariant fitter.

        Args:
            llm_config: LLM configuration (optional, defaults to LLMConfig())
            logger: Logger instance (optional)
        """
        self.llm_config = llm_config if llm_config else LLMConfig()
        self.logger = logger

    def _log(self, message: str, level: str = 'info'):
        """Log a message if logger is available."""
        if self.logger:
            getattr(self.logger, level, self.logger.info)(message)

    def discover_invariants(self, assignments_list: List[str], variables: List[str],
                           loop_bound: Optional[int] = None, max_invariants: int = 15) -> List[str]:
        """
        Discover loop invariants from execution traces using LLM.

        Args:
            assignments_list: List of assignment strings (execution traces)
            variables: List of variable names to analyze
            loop_bound: Optional loop bound information
            max_invariants: Maximum number of invariants to return

        Returns:
            List of discovered invariant strings (e.g., ["x >= 0", "y == x + 1"])
        """
        if not assignments_list or not variables:
            return []

        self._log(f"Discovering invariants for variables: {variables}")
        self._log(f"Using {len(assignments_list)} execution traces")

        invariants = []

        # Try to find relationships for each variable
        for var in variables:
            other_vars = [v for v in variables if v != var]
            if not other_vars:
                continue

            try:
                # Use llmfind_relation to find relationships
                solutions = llmfind_relation(
                    assignments_lists=[assignments_list],
                    dependent_var=var,
                    independent_vars=other_vars,
                    max_total_poly_degree=2,
                    max_solutions=3,
                    llm_config=self.llm_config
                )

                for sol in solutions:
                    formula = sol.get('formula', '')
                    if formula and not sol.get('is_only_constant', False):
                        invariants.append(formula)

            except Exception as e:
                self._log(f"Error finding relation for {var}: {e}", level='warning')

        # Remove duplicates while preserving order
        seen = set()
        unique_invariants = []
        for inv in invariants:
            if inv not in seen:
                seen.add(inv)
                unique_invariants.append(inv)

        self._log(f"Discovered {len(unique_invariants)} unique invariants")
        return unique_invariants[:max_invariants]


def llmfit_discover_invariants(assignments_list: List[str], variables: List[str],
                               loop_bound: Optional[int] = None, max_invariants: int = 15,
                               llm_config: Optional[LLMConfig] = None) -> List[str]:
    """
    Convenience function to discover invariants without creating a fitter instance.

    Args:
        assignments_list: List of assignment strings (execution traces)
        variables: List of variable names to analyze
        loop_bound: Optional loop bound information
        max_invariants: Maximum number of invariants to return
        llm_config: LLM configuration (optional)

    Returns:
        List of discovered invariant strings
    """
    fitter = LLMInvariantFitter(llm_config=llm_config)
    return fitter.discover_invariants(assignments_list, variables, loop_bound, max_invariants)
