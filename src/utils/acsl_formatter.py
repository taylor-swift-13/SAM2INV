"""
ACSL 格式转换工具
用于将内部表示转换为标准 ACSL 格式
"""
import re


def convert_precondition_to_acsl(pre_condition: str) -> str:
    """
    将内部 precondition 格式转换为标准 ACSL 格式。
    
    转换规则：
    1. 移除外层括号
    2. * 替换为 &&
    3. var@pre 替换为 \at(var, Pre)
    
    示例：
    - 输入: "(w == 1) * (z == 1) * (y == y@pre) * (x == x@pre)"
    - 输出: "w == 1 && z == 1 && y == \at(y, Pre) && x == \at(x, Pre)"
    
    Args:
        pre_condition: 内部格式的 precondition 字符串
        
    Returns:
        标准 ACSL 格式的 precondition 字符串
    """
    if not pre_condition or pre_condition.strip() == "":
        return ""
    
    result = pre_condition.strip()
    
    # 1. 移除外层括号 (if the whole string is wrapped in parentheses)
    while result.startswith('(') and result.endswith(')'):
        # Check if parentheses are balanced
        count = 0
        for i, char in enumerate(result):
            if char == '(':
                count += 1
            elif char == ')':
                count -= 1
            if count == 0 and i < len(result) - 1:
                # Found closing paren before end, don't strip
                break
        else:
            # All parentheses balanced, can strip outer pair
            result = result[1:-1].strip()
    
    # 2. 替换 * 为 &&
    # Need to be careful: only replace * that are operators, not in variable names
    # Pattern: * surrounded by spaces or parentheses
    result = re.sub(r'\)\s*\*\s*\(', ' && ', result)
    result = re.sub(r'\*\s*\(', '&& (', result)
    result = re.sub(r'\)\s*\*', ') &&', result)
    result = re.sub(r'^\*\s*', '', result)  # Remove leading *
    result = re.sub(r'\s*\*$', '', result)  # Remove trailing *
    # Replace remaining standalone *
    result = re.sub(r'\s*\*\s*', ' && ', result)
    
    # 3. 替换 var@pre 为 \at(var, Pre)
    # Pattern: word characters followed by @pre
    result = re.sub(r'(\w+)@pre', r'\\at(\1, Pre)', result)
    
    # Clean up extra spaces
    result = re.sub(r'\s+', ' ', result).strip()
    
    return result


def convert_assignment_to_acsl(assignment_str: str) -> str:
    """
    将赋值字符串转换为 ACSL 格式。
    
    示例：
    - 输入: "x == 1 && y == x@pre + 1"
    - 输出: "x == 1 && y == \at(x, Pre) + 1"
    
    Args:
        assignment_str: 赋值字符串
        
    Returns:
        ACSL 格式的赋值字符串
    """
    if not assignment_str:
        return ""
    
    # Replace var@pre with \at(var, Pre)
    result = re.sub(r'(\w+)@pre', r'\\at(\1, Pre)', assignment_str)
    
    return result


def format_loop_invariant(invariant_expr: str) -> str:
    """
    格式化循环不变量为标准 ACSL loop invariant 语句。
    
    Args:
        invariant_expr: 不变量表达式，如 "x >= 0"
        
    Returns:
        完整的 ACSL 语句，如 "loop invariant x >= 0;"
    """
    if not invariant_expr:
        return ""
    
    expr = invariant_expr.strip()
    
    # Remove trailing semicolon if present
    if expr.endswith(';'):
        expr = expr[:-1].strip()
    
    # Remove "loop invariant" prefix if already present
    if expr.lower().startswith('loop invariant'):
        expr = expr[14:].strip()
    
    return f"loop invariant {expr};"


if __name__ == "__main__":
    # Test cases
    test_cases = [
        "(w == 1) * (z == 1) * (y == y@pre) * (x == x@pre)",
        "x > 0 && y@pre == 0",
        "n >= 0",
        "(a == 1) * (b == a@pre + 1)",
        "",
    ]
    
    print("Testing convert_precondition_to_acsl:")
    for tc in test_cases:
        result = convert_precondition_to_acsl(tc)
        print(f"  Input:  {tc}")
        print(f"  Output: {result}")
        print()
