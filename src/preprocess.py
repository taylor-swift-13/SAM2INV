#!/usr/bin/env python3
"""
Preprocessing Module for Loop Invariant Filter

Extracts known variables from loop record to populate FILTER_CONTEXT dynamically.
"""

from typing import List, Set, Dict, Optional


def extract_context_from_record(record: Dict) -> Dict[str, List[str]]:
    """
    Extract filter context from loop record.
    
    Args:
        record: Loop record containing:
            - current_vars: List of current variables in scope
            - function_params: List of function parameters
            - param_pre_vars: Dict mapping params to their Pre values
            
    Returns:
        Dictionary with 'known_variables' and 'param_pre_vars'
    """
    # Extract all known variables
    known_vars = set()
    
    # Add current variables
    if 'current_vars' in record:
        known_vars.update(record['current_vars'])
    
    # Add function parameters
    if 'function_params' in record:
        known_vars.update(record['function_params'])
    
    # Add common variables
    if 'common_vars' in record:
        known_vars.update(record['common_vars'])
    
    # Extract parameters that can use \at(v, Pre)
    param_pre_vars = []
    if 'param_pre_vars' in record:
        param_pre_vars = list(record['param_pre_vars'].keys())
    
    return {
        'known_variables': sorted(list(known_vars)),
        'param_pre_vars': param_pre_vars
    }


def update_filter_context_from_record(record: Dict):
    """
    Update FILTER_CONTEXT in config.py with variables from record.
    
    Args:
        record: Loop record dictionary
    """
    import config
    
    context = extract_context_from_record(record)
    config.FILTER_CONTEXT['known_variables'] = context['known_variables']
    
    return context


if __name__ == "__main__":
    # Test with example record
    test_record = {
        'loop_idx': 0,
        'loop_content': 'for (i = 0; i < n; i++) { s += i + 1; }',
        'begin': {},
        'end': {},
        'common_vars': ['i', 'n', 's'],
        'unchanged_vars': [],
        'non_inductive_vars': [],
        'pre_condition': 'n >= 0',
        'loop_condition': 'i < n',
        'updated_loop_conditions': [],
        'var_maps': {},
        'path_conds': [],
        'current_vars': ['i', 'n', 's'],
        'param_pre_vars': {'n': 'n_pre'},
        'function_params': ['n'],
        'loop_bound': None,
    }
    
    context = extract_context_from_record(test_record)
    
    print("=" * 60)
    print("Context Extraction from Record")
    print("=" * 60)
    print(f"Known Variables: {context['known_variables']}")
    print(f"Param Pre Vars: {context['param_pre_vars']}")
    print("=" * 60)

