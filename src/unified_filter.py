#!/usr/bin/env python3
r"""
Unified Loop Invariant Filter

检查 LLM 生成的不变量在符号执行提取的变量列表上是否构成合法的语法树。

输入: 
  - invariants: List[str] - LLM 生成的不变量列表
  - record: Dict - 符号执行提取的变量信息
  
输出: 
  - FilterResult - 有效/被拒绝的不变量及原因
"""

import re
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Any, Set, Optional
from enum import Enum


class ViolationType(Enum):
    FORBIDDEN_CONSTRUCT = "Forbidden construct"
    UNDEFINED_SYMBOL = "Undefined symbol"
    VALIDATION_ERROR = "Validation error"


@dataclass
class Violation:
    type: ViolationType
    message: str


@dataclass
class FilterResult:
    valid: List[str] = field(default_factory=list)
    rejected: List[Tuple[str, List[Violation]]] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)


class SyntaxFilter:
    r"""
    基于语法树的过滤器，检查不变量是否合法。
    
    规则（基于 system_prompt.txt）:
    1. 禁止量词: \forall, \exists
    2. 禁止自定义: predicate, inductive, logic, axiomatic, lemma
    3. 禁止数学运算符: \product, \sum, \min, \max
    4. 禁止函数调用（除了 \at(v, Pre)）
    5. 只允许使用 record 中的变量
    6. \at(v, Pre) 只能用于函数参数
    7. 禁止三元运算符: ? :
    """

    def __init__(self, known_variables: Set[str], param_pre_vars: Set[str]):
        self.known_vars = known_variables
        self.param_pre_vars = param_pre_vars
        
        # 禁止的构造
        self._forbidden_quantifiers = {'\\forall', '\\exists'}
        self._forbidden_keywords = {'predicate', 'inductive', 'logic', 'axiomatic', 'lemma'}
        self._forbidden_math_ops = {'\\product', '\\sum', '\\min', '\\max'}

    def filter(self, invariants: List[str]) -> Tuple[List[str], List[Tuple[str, List[Violation]]]]:
        """过滤不变量列表"""
        valid = []
        rejected = []

        for inv in invariants:
            violations = self._check_invariant(inv)
            if not violations:
                valid.append(inv)
            else:
                rejected.append((inv, violations))

        return valid, rejected

    def _check_invariant(self, invariant: str) -> List[Violation]:
        """检查单个不变量"""
        violations = []
        stripped = invariant.strip()

        # -1. 快速拒绝明显无效的不变式（LLM 有时生成 '...' 或其他垃圾 token）
        if not stripped or stripped in ('...', '…', 'true', 'false', 'TRUE', 'FALSE'):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Invalid invariant token: '{stripped}'"
            ))
            return violations

        # 检查是否只包含非标识符字符（如纯标点、纯数字等）
        if not re.search(r'[a-zA-Z_]', stripped):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Invariant contains no variables or identifiers: '{stripped}'"
            ))
            return violations

        # 检查是否包含省略号 '...'（可能嵌在表达式中）
        if '...' in stripped or '…' in stripped:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Invariant contains ellipsis '...': not a valid ACSL expression"
            ))
            return violations

        # 0. 检查括号平衡（必须最先检查，因为不平衡的括号会导致后续检查失败）
        paren_balance = 0
        bracket_balance = 0
        brace_balance = 0
        
        for i, char in enumerate(stripped):
            if char == '(':
                paren_balance += 1
            elif char == ')':
                paren_balance -= 1
                if paren_balance < 0:
                    violations.append(Violation(
                        ViolationType.VALIDATION_ERROR,
                        f"Unmatched closing parenthesis ')' at position {i}. "
                        f"Every ')' must have a matching '(' before it."
                    ))
                    break
            elif char == '[':
                bracket_balance += 1
            elif char == ']':
                bracket_balance -= 1
                if bracket_balance < 0:
                    violations.append(Violation(
                        ViolationType.VALIDATION_ERROR,
                        f"Unmatched closing bracket ']' at position {i}. "
                        f"Every ']' must have a matching '[' before it."
                    ))
                    break
            elif char == '{':
                brace_balance += 1
            elif char == '}':
                brace_balance -= 1
                if brace_balance < 0:
                    violations.append(Violation(
                        ViolationType.VALIDATION_ERROR,
                        f"Unmatched closing brace '}}' at position {i}. "
                        f"Every '}}' must have a matching '{{' before it."
                    ))
                    break
        
        # 检查是否有未闭合的括号
        if paren_balance > 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Missing {paren_balance} closing parenthesis ')'. "
                f"Every '(' must have a matching ')'. "
                f"Invariant: {stripped}"
            ))
        elif paren_balance < 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Extra {-paren_balance} closing parenthesis ')' without matching '('. "
                f"Invariant: {stripped}"
            ))
        
        if bracket_balance > 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Missing {bracket_balance} closing bracket ']'. "
                f"Every '[' must have a matching ']'."
            ))
        elif bracket_balance < 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Extra {-bracket_balance} closing bracket ']' without matching '['."
            ))
        
        if brace_balance > 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Missing {brace_balance} closing brace '}}'. "
                f"Every '{{' must have a matching '}}'."
            ))
        elif brace_balance < 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Extra {-brace_balance} closing brace '}}' without matching '{{'."
            ))
        
        # 如果括号不平衡，直接返回，不进行后续检查
        if violations:
            return violations

        # 1. 检查禁止的量词
        for op in self._forbidden_quantifiers:
            if op in stripped:
                violations.append(Violation(
                    ViolationType.FORBIDDEN_CONSTRUCT,
                    f"Quantifier '{op}' is not allowed"
                ))

        # 2. 检查禁止的关键字
        for keyword in self._forbidden_keywords:
            if re.search(r'\b' + keyword + r'\b', stripped, re.IGNORECASE):
                violations.append(Violation(
                    ViolationType.FORBIDDEN_CONSTRUCT,
                    f"Keyword '{keyword}' is not allowed"
                ))

        # 3. 检查禁止的数学运算符
        for op in self._forbidden_math_ops:
            if op in stripped:
                violations.append(Violation(
                    ViolationType.FORBIDDEN_CONSTRUCT,
                    f"Math operator '{op}' is not allowed"
                ))

        # 3b. 禁止把 ^ 当作幂运算（在 C/ACSL 中 ^ 是按位异或）
        if '^' in stripped:
            violations.append(Violation(
                ViolationType.FORBIDDEN_CONSTRUCT,
                "Operator '^' is not allowed in loop invariants. "
                "Use explicit multiplication (e.g., x * x) instead of exponent notation."
            ))

        # 4. 检查 let 绑定和赋值
        if '\\let' in stripped:
            violations.append(Violation(
                ViolationType.FORBIDDEN_CONSTRUCT,
                "Let binding '\\let' is not allowed"
            ))

        if ':=' in stripped:
            violations.append(Violation(
                ViolationType.FORBIDDEN_CONSTRUCT,
                "Assignment operator ':=' is not allowed"
            ))

        # 5. 检查函数调用（只允许 \at, \valid, \valid_read）
        func_pattern = r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\('
        allowed_funcs = {'at', 'valid', 'valid_read'}
        for match in re.finditer(func_pattern, stripped):
            func_name = match.group(1)
            if func_name not in allowed_funcs:
                violations.append(Violation(
                    ViolationType.UNDEFINED_SYMBOL,
                    f"Function '{func_name}' is not allowed (only \\at(v, Pre) permitted)"
                ))

        # 5b. 检查 \at(v, Pre) 只能用于函数参数，不能用于局部变量
        at_pattern = r'\\at\s*\(\s*(\w+)\s*,\s*Pre\s*\)'
        for at_match in re.finditer(at_pattern, stripped):
            var_in_at = at_match.group(1)
            if var_in_at not in self.param_pre_vars:
                violations.append(Violation(
                    ViolationType.VALIDATION_ERROR,
                    f"\\at({var_in_at}, Pre) only allowed for parameters: {sorted(self.param_pre_vars)}"
                ))

        # 6. 检查未定义的变量
        identifiers = re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', stripped)
        acsl_keywords = {'at', 'Pre', 'valid', 'valid_read', 'loop', 'invariant', 'assigns', 'variant'}
        for identifier in identifiers:
            if identifier not in acsl_keywords and identifier not in self.known_vars:
                violations.append(Violation(
                    ViolationType.UNDEFINED_SYMBOL,
                    f"Variable '{identifier}' not in scope: {sorted(self.known_vars)}"
                ))

        # 7. 检查混合类型运算：布尔值不能参与算术运算
        # 在 ACSL 中，比较运算符（==, !=, <, >, <=, >=）返回布尔值，不能用于 * / + -
        # 例如: "(y - 1) * (r >= y - 1)" 或 "(r >= y - 1) * (y - 1)" 是非法的

        pattern1 = r'[+\-*/%]\s*\([^)]*([<>]=?|==|!=)[^)]*\)'
        pattern2 = r'\([^)]*([<>]=?|==|!=)[^)]*\)[\s]*[+\-*/%]'

        if re.search(pattern1, stripped) or re.search(pattern2, stripped):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Boolean expression cannot be used in arithmetic operation. Use conditional expression '(cond ? val1 : val2)' instead"
            ))

        # 7b. 检查蕴含表达式被嵌入算术项（例如: a - (p ==> q)）
        implies_in_arith_pattern1 = r'[+\-*/%]\s*\([^)]*==>[^)]*\)'
        implies_in_arith_pattern2 = r'\([^)]*==>[^)]*\)\s*[+\-*/%]'
        if re.search(implies_in_arith_pattern1, stripped) or re.search(implies_in_arith_pattern2, stripped):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                "Implication '==>' cannot be used as an arithmetic sub-expression. "
                "Use implication as the top-level predicate (e.g., 'cond ==> expr')."
            ))

        # 8. 检查 ! 运算符只能用于布尔值，不能用于数值
        # 在 ACSL 中，! 是逻辑非运算符，只能用于布尔表达式
        # 例如: "(x-1)!" 或 "5!" 是非法的（会被误认为是阶乘）
        # 需要匹配：数字/变量/表达式后面直接跟!，但排除 != 和 \! 转义
        # 模式：数字后跟空格*再跟!，或变量后跟!，或)后跟!
        factorial_like_pattern = r'(?:\d+|\w+|\))\s*!(?!=)'
        
        for match in re.finditer(factorial_like_pattern, stripped):
            matched_text = match.group(0)
            # 排除已知的 ACSL 关键字和逻辑表达式
            if not any(kw in matched_text for kw in ['\at', '\valid']):
                violations.append(Violation(
                    ViolationType.VALIDATION_ERROR,
                    f"Logical operator '!' can only be applied to boolean values, not numeric expressions. "
                    f"Found: '{matched_text}'. "
                    f"If you meant factorial, ACSL does not support factorial operator; use explicit multiplication or recurrence relations instead."
                ))
                break  # 只报告一次即可

        # 9. 检查无效/非标准的运算符组合
        # 例如: !==> 不是有效的ACSL运算符，应该是 ==>
        invalid_operators = ['!==>', '<=>', ':=', '!==', '===', '<<=', '>>=']
        for op in invalid_operators:
            if op in stripped:
                violations.append(Violation(
                    ViolationType.VALIDATION_ERROR,
                    f"Invalid operator '{op}' found. ACSL logical implication is '==>', not '{op}'. "
                    f"Use '==>' for logical implication, '==' for equality, '!=' for inequality."
                ))
        
        # 10. 检查 == 和 <>/ 的歧义组合（运算符优先级问题）
        # 在 ACSL 中，== 的优先级比 < > <= >= 高
        # 所以 "z == (x - 1) < y" 会被解析为 "(z == (x - 1)) < y"（布尔值与整数比较，类型错误）
        # 正确的写法应该是 "z == ((x - 1) < y)" 或单独使用 "(x - 1) < y"
        # 先去掉 ==> 逻辑蕴含，避免误判
        temp_stripped = stripped.replace('==>', '##IMPLIES##')
        
        # 检查歧义模式：== 后紧跟的比较操作不在明确的括号内
        # 歧义: "z == (x - 1) < y"  (== 后的 < 在最外层)
        # 合法: "z == ((x - 1) < y)" (== 后的 < 在嵌套括号内)
        # 合法: "(x - 1) < y ==> z == 1" (< 在 ==> 左边，不是 == 后面)
        
        # 方法：检查是否有 == 后跟非嵌套括号表达式，然后是 < 或 >
        # 歧义模式：== ... ) < 或 == ... ) > (其中 ) 是最外层括号的结束)
        # 或者：== identifier < 或 == identifier >
        
        # 模式1：== 后跟简单的括号表达式，然后是 < 或 >
        # 例如：z == (x - 1) < y
        ambiguous_pattern = r'==\s*\([^()]*\)\s*[<>]'
        
        # 模式2：== 后跟变量/数字，然后是 < 或 >
        # 例如：z == x < y
        ambiguous_pattern2 = r'==\s+\w+\s*[<>](?!=[<>])'
        
        if re.search(ambiguous_pattern, temp_stripped) or re.search(ambiguous_pattern2, temp_stripped):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Ambiguous operator precedence: '==' has higher precedence than '<' or '>'. "
                f"Expression like 'z == (x - 1) < y' is parsed as '(z == (x - 1)) < y' which is a type error. "
                f"Use explicit parentheses: 'z == ((x - 1) < y)' or separate into two invariants."
            ))

        # 11. 检查不完整的表达式（缺少操作数、尾随运算符等）
        # 例如: "z == 1 * (x - 1" (缺少右括号)
        # 例如: "z == x +" (尾随运算符)
        # 例如: "z == * x" (前导运算符)
        
        # 检查尾随的二元运算符（表达式不应该以运算符结尾）
        trailing_op_pattern = r'[+\-*/%<>=!&|]\s*$'
        if re.search(trailing_op_pattern, stripped):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Incomplete expression: invariant ends with an operator. "
                f"Every binary operator must have both left and right operands. "
                f"Invariant: {stripped}"
            ))
        
        # 检查运算符后缺少操作数的情况
        # 模式: 运算符后面直接跟另一个二元运算符（不包括负号和逻辑非）
        # 例如: "z == * x" 中 == 后面直接跟 *
        # 例如: "z + * x" 中 + 后面直接跟 *
        missing_operand_pattern = r'[+\-*/%<>=!&|]\s+[*/%<>=&|]'
        if re.search(missing_operand_pattern, stripped):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Missing operand between operators. "
                f"Every binary operator must have both left and right operands. "
                f"Invariant: {stripped}"
            ))
        
        # 检查连续的运算符（除了 ==, !=, <=, >=, ==>, &&, ||）
        # 允许的连续运算符组合
        allowed_double_ops = ['==', '!=', '<=', '>=', '&&', '||', '==>', '<<', '>>']
        temp_for_check = stripped
        for allowed_op in allowed_double_ops:
            temp_for_check = temp_for_check.replace(allowed_op, '##')
        
        # 检查是否还有连续的运算符
        consecutive_op_pattern = r'[+\-*/%<>=!&|]{2,}'
        consecutive_matches = re.findall(consecutive_op_pattern, temp_for_check)
        if consecutive_matches:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Invalid consecutive operators found: {consecutive_matches}. "
                f"Check for missing operands or extra operators. "
                f"Invariant: {stripped}"
            ))
        
        # 12. 检查空的或仅包含空白的不变量
        if not stripped or stripped.isspace():
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Empty or whitespace-only invariant is not allowed."
            ))
        
        # 13. 检查不变量是否以非法字符开头或结尾
        # 不变量不应该以运算符开头（除了 ! 和 - 用于逻辑非和负号）
        # 不应该以逗号、分号等结尾（分号会在外部添加）
        if stripped and re.match(r'^[*/%<>=&|,;]', stripped):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Invariant starts with invalid character. "
                f"Invariants should start with a variable, constant, or unary operator (!, -, \\at). "
                f"Invariant: {stripped}"
            ))
        
        # 14. 检查是否包含未转义的特殊字符或控制字符
        # ACSL 不应该包含制表符以外的控制字符
        control_chars = [c for c in stripped if ord(c) < 32 and c not in ['\t', '\n', '\r']]
        if control_chars:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Invariant contains control characters: {[hex(ord(c)) for c in control_chars]}. "
                f"Only printable characters are allowed in ACSL annotations."
            ))
        
        # 15. 检查是否有多余的分号（不变量内部不应该有分号）
        # 分号应该只在最后添加，不应该在表达式中间
        if ';' in stripped:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Semicolon ';' found inside invariant expression. "
                f"Semicolons should only appear at the end of the invariant statement, not within the expression. "
                f"If you have multiple invariants, split them into separate 'loop invariant' statements. "
                f"Invariant: {stripped}"
            ))
        
        # 16. 检查是否有未闭合的字符串字面量（虽然 ACSL 不常用字符串）
        # 检查单引号和双引号是否成对
        single_quote_count = stripped.count("'")
        double_quote_count = stripped.count('"')
        
        if single_quote_count % 2 != 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Unmatched single quote in invariant. "
                f"Every opening quote must have a closing quote. "
                f"Invariant: {stripped}"
            ))
        
        if double_quote_count % 2 != 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Unmatched double quote in invariant. "
                f"Every opening quote must have a closing quote. "
                f"Invariant: {stripped}"
            ))
        
        # 17. 检查是否有 C 注释标记（不变量内部不应该有注释）
        if '/*' in stripped or '*/' in stripped or '//' in stripped:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Comment markers ('/*', '*/', '//') found inside invariant. "
                f"Invariants should not contain comments. "
                f"Invariant: {stripped}"
            ))
        
        # 18. 检查是否有连续的 == 运算符（如 z == (x - 1) == 1）
        # 这种模式是不允许的，因为 == 不能连用
        # 需要排除 ==> (逻辑蕴含) 和已经用 && 或 || 连接的情况
        
        # 策略：先将所有合法的分隔符（&&, ||, ==>）替换为特殊标记
        temp_for_eq_check = stripped
        temp_for_eq_check = temp_for_eq_check.replace('==>', '##IMP##')
        temp_for_eq_check = temp_for_eq_check.replace('&&', '##AND##')
        temp_for_eq_check = temp_for_eq_check.replace('||', '##OR##')
        
        # 现在检查是否有 == ... == 的模式
        # 如果两个 == 之间没有 ##IMP##, ##AND##, ##OR##，就是非法的连续 ==
        consecutive_eq_pattern = r'==(?!#)[^#]*==(?!#)'
        if re.search(consecutive_eq_pattern, temp_for_eq_check):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Consecutive '==' operators detected. "
                f"Expressions like 'z == (x - 1) == 1' are not allowed. "
                f"Use logical AND to combine conditions: 'z == (x - 1) && (x - 1) == 1'. "
                f"Invariant: {stripped}"
            ))
        
        # 19. 检查是否有可疑的比较链（如 x < y < z）
        # 注意：Frama-C 实际上支持 chained comparison 语法（如 1 <= x <= y）
        # 所以这个检查被禁用了，不再报告为错误
        pass
        
        # 20. 检查是否包含三元运算符 ? :
        # 三元运算符在 ACSL 中虽然语法上可能被接受，但在循环不变量中使用会导致验证困难
        # 例如：z == (x > 1 ? 1 * \at(x, Pre) : 1)
        if '?' in stripped:
            violations.append(Violation(
                ViolationType.FORBIDDEN_CONSTRUCT,
                f"Ternary operator '?' is not allowed in loop invariants. "
                f"Conditional expressions make invariants harder to verify. "
                f"Use separate invariants with logical implications instead. "
                f"For example, instead of 'z == (x > 1 ? a : b)', use 'x > 1 ==> z == a' and 'x <= 1 ==> z == b'. "
                f"Invariant: {stripped}"
            ))

        return violations


def validate_code_structure(code: str) -> List[Violation]:
    """
    验证生成的 C 代码结构是否正确。
    检查 ACSL 注释是否正确闭合，以及其他代码级别的问题。
    
    Args:
        code: 完整的 C 代码
        
    Returns:
        List of violations found (empty if code is valid)
    """
    violations = []
    
    # 1. 检查 ACSL 注释是否正确闭合
    # 统计 /*@ 和 */ 的数量
    acsl_open_count = len(re.findall(r'/\*@', code))
    # 注意：需要匹配 */ 但不包括 /*@ 内部的 */
    # 简单方法：统计所有 */ 的数量
    comment_close_count = len(re.findall(r'\*/', code))
    
    # 检查是否有未闭合的 ACSL 注释
    if acsl_open_count > comment_close_count:
        violations.append(Violation(
            ViolationType.VALIDATION_ERROR,
            f"Unclosed ACSL comment: found {acsl_open_count} '/*@' but only {comment_close_count} '*/'. "
            f"Every ACSL comment must be properly closed with '*/'."
        ))
    
    # 2. 检查 ACSL 注释块的结构
    # 查找所有 ACSL 注释块
    acsl_blocks = re.findall(r'/\*@.*?\*/', code, re.DOTALL)
    
    for i, block in enumerate(acsl_blocks):
        # 检查块内是否有嵌套的 /*
        inner_open = block[3:-2].count('/*')  # 排除开头的 /*@ 和结尾的 */
        if inner_open > 0:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"ACSL comment block {i+1} contains nested '/*' which is not allowed. "
                f"Block preview: {block[:100]}..."
            ))
        
        # 检查块内是否有 #include 或其他预处理指令（说明注释没有正确闭合）
        if '#include' in block or '#define' in block or '#ifdef' in block:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"ACSL comment block {i+1} contains preprocessor directives, "
                f"which suggests the comment is not properly closed. "
                f"Block preview: {block[:100]}..."
            ))
    
    # 3. 检查是否有孤立的 */ （没有对应的 /*）
    # 这个检查比较复杂，需要逐字符扫描
    comment_depth = 0
    i = 0
    while i < len(code) - 1:
        if code[i:i+2] == '/*':
            comment_depth += 1
            i += 2
        elif code[i:i+2] == '*/':
            comment_depth -= 1
            if comment_depth < 0:
                # 找到行号
                line_num = code[:i].count('\n') + 1
                violations.append(Violation(
                    ViolationType.VALIDATION_ERROR,
                    f"Unmatched '*/' at line {line_num}. "
                    f"Every '*/' must have a matching '/*' or '/*@' before it."
                ))
                break
            i += 2
        else:
            i += 1
    
    if comment_depth > 0:
        violations.append(Violation(
            ViolationType.VALIDATION_ERROR,
            f"Unclosed comment: {comment_depth} '/*' or '/*@' without matching '*/'. "
            f"All comments must be properly closed."
        ))
    
    # 4. 检查 loop invariant 语句的格式
    # 查找所有 loop invariant 语句
    inv_pattern = r'loop\s+invariant\s+([^;]*);'
    invariants_in_code = re.findall(inv_pattern, code, re.DOTALL)
    
    for inv in invariants_in_code:
        inv_stripped = inv.strip()
        
        # 检查是否为空
        if not inv_stripped:
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Empty loop invariant found: 'loop invariant ;'. "
                f"Invariants must have a non-empty expression."
            ))
    
    # 检查是否有同一行中的 "loop invariant a; b;"（保守检测，避免跨行/注释误报）
    for line in code.splitlines():
        if 'loop invariant' not in line:
            continue

        # 去掉行内 // 注释，避免注释文本影响结构判断
        line_no_comment = re.sub(r'//.*$', '', line).strip()
        if not line_no_comment:
            continue

        # 仅关注 loop invariant 起始后的内容
        inv_start = re.search(r'loop\s+invariant\s+', line_no_comment)
        if not inv_start:
            continue
        tail = line_no_comment[inv_start.end():]

        # 一个合法 invariant 行应当只有一个语句终止分号
        semicolon_count = tail.count(';')
        if semicolon_count <= 1:
            continue

        # 允许 "loop invariant a; loop invariant b;" 这种极少见的同一行双声明格式
        extra = tail[tail.find(';') + 1:].strip()
        if re.match(r'^loop\s+(?:invariant|assigns|variant)\b', extra):
            continue

        violations.append(Violation(
            ViolationType.VALIDATION_ERROR,
            f"Multiple invariant expressions found in same statement. "
            f"Each invariant should be a separate 'loop invariant' statement. "
            f"Split into multiple lines."
        ))
        break
    
    # 5. 检查 requires/ensures 子句的格式
    # 查找 requires 子句 - 改进正则以正确提取内容
    requires_pattern = r'/\*@\s*requires\s+([^*]+?)\*/'
    requires_matches = re.findall(requires_pattern, code, re.DOTALL)
    
    for req in requires_matches:
        req_stripped = req.strip()
        # Ignore trailing comments when checking statement terminator.
        # Example: "1; // placeholder" should still be treated as semicolon-terminated.
        req_no_comments = re.sub(r'//.*$', '', req_stripped, flags=re.MULTILINE)
        req_no_comments = re.sub(r'/\*.*?\*/', '', req_no_comments, flags=re.DOTALL).strip()
        
        # 检查是否为空或只有分号
        if not req_no_comments or req_no_comments == ';':
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Empty requires clause found. "
                f"Requires clauses must have a non-empty expression."
            ))
            continue
        
        # 检查是否缺少分号
        if not req_no_comments.endswith(';'):
            violations.append(Violation(
                ViolationType.VALIDATION_ERROR,
                f"Requires clause missing semicolon: '{req_stripped[:50]}...'. "
                f"ACSL requires clauses must end with ';'."
            ))
    
    # 6. 检查代码中是否有明显的语法错误标记
    # 例如 LLM 可能生成的占位符或错误标记
    error_markers = ['TODO', 'FIXME', 'XXX', 'PLACEHOLDER', 'ERROR', '???']
    for marker in error_markers:
        if marker in code:
            # 检查是否在注释中（允许在普通注释中出现）
            # 但不允许在 ACSL 注释或代码中出现
            if f'/*@' in code and marker in code:
                # 简单检查：如果在 ACSL 块中出现
                for block in acsl_blocks:
                    if marker in block:
                        violations.append(Violation(
                            ViolationType.VALIDATION_ERROR,
                            f"Error marker '{marker}' found in ACSL annotation. "
                            f"This suggests incomplete or placeholder code."
                        ))
                        break
    
    return violations


def filter_invariants(invariants: List[str], record: Dict, verbose: bool = True) -> FilterResult:
    """
    过滤 LLM 生成的不变量。
    
    Args:
        invariants: LLM 生成的不变量列表
        record: 符号执行提取的记录，包含:
            - current_vars: 当前作用域的变量
            - function_params: 函数参数
            - param_pre_vars: 可以使用 \at(v, Pre) 的参数
            
    Returns:
        FilterResult 包含有效/被拒绝的不变量
    """
    # 提取变量信息
    known_vars = set()
    if 'current_vars' in record:
        known_vars.update(record['current_vars'])
    if 'function_params' in record:
        known_vars.update(record['function_params'])
    if 'common_vars' in record:
        known_vars.update(record['common_vars'])
    
    # 提取可以使用 \at(v, Pre) 的参数
    param_pre_vars = set()
    if 'param_pre_vars' in record:
        ppv = record['param_pre_vars']
        if isinstance(ppv, dict):
            # If it's a dict, keys are parameter names
            param_pre_vars = set(ppv.keys())
        elif isinstance(ppv, list):
            # If it's a list, extract parameter names
            # Handle both formats: 'x' or '\at(x, Pre)'
            for item in ppv:
                if isinstance(item, str):
                    # Check if it's in \at(param, Pre) format
                    match = re.match(r'\\at\s*\(\s*(\w+)\s*,\s*Pre\s*\)', item)
                    if match:
                        param_pre_vars.add(match.group(1))
                    else:
                        # It's just a parameter name
                        param_pre_vars.add(item)
        else:
            param_pre_vars = set()
    
    # Also check function_params as a fallback
    if not param_pre_vars and 'function_params' in record:
        fp = record['function_params']
        if isinstance(fp, list):
            param_pre_vars = set(fp)
        elif isinstance(fp, set):
            param_pre_vars = fp
    
    if verbose:
        print(f"Known variables: {sorted(known_vars)}")
        print(f"Parameters (can use \\at(v, Pre)): {sorted(param_pre_vars)}")

    # Step 0: 先尝试改写 \at(local_var, Pre) 为 precondition 中的初始值
    # 这样 \at(s, Pre) 在 precondition 中有 s==0 时会被替换为 0
    # 必须在语法过滤之前执行，否则这些不变量会被直接拒绝
    # 兼容两种字段名: 'pre_condition' (loop_sampler 写入) 和 'precondition'
    precondition = record.get('pre_condition', '') or record.get('precondition', '')
    function_params = set()
    if 'function_params' in record:
        fp = record['function_params']
        if isinstance(fp, list):
            function_params = set(fp)
        elif isinstance(fp, set):
            function_params = fp

    if precondition and invariants:
        # 从 record 中获取 begin_map（符号执行提取的初始状态），优先使用它来改写 \at(var, Pre)
        begin_map = record.get('begin', None)
        if isinstance(begin_map, dict):
            # 如果 begin 是字典格式，转换为字符串
            begin_map = ' * '.join([f"({k} == {v})" for k, v in begin_map.items()])
        invariants = _rewrite_at_pre(invariants, precondition, function_params, begin_map)
        if verbose:
            source = "begin_map" if begin_map else "precondition"
            print(f"\nAfter \\at(v, Pre) rewriting (using {source}: {begin_map or precondition}):")
            for inv in invariants:
                print(f"  - {inv}")

    # 创建过滤器并执行语法过滤
    filter_obj = SyntaxFilter(known_vars, param_pre_vars)
    valid, rejected = filter_obj.filter(invariants)

    # 构建结果
    result = FilterResult(
        valid=valid,
        rejected=rejected,
        metadata={
            'total_input': len(invariants),
            'total_valid': len(valid),
            'total_rejected': len(rejected),
        }
    )

    if verbose:
        print("\n" + "=" * 60)
        print("FILTER RESULT")
        print("=" * 60)
        print(f"Input: {result.metadata['total_input']} invariants")
        print(f"Valid: {result.metadata['total_valid']}")
        print(f"Rejected: {result.metadata['total_rejected']}")

        if result.valid:
            print("\n✓ VALID INVARIANTS:")
            for v in result.valid:
                print(f"  - {v}")

        if result.rejected:
            print("\n✗ REJECTED INVARIANTS:")
            for inv, violations in result.rejected:
                print(f"\n  {inv}")
                for v in violations:
                    print(f"    [{v.type.value}] {v.message}")

    return result


def _extract_precondition_values(precondition: str) -> Dict[str, str]:
    """
    从 precondition 中提取变量的初始值。
    支持格式：
    - (x == 1) * (y == 2)  或
    - x == 1 && y == 2

    Returns:
        Dict[variable_name, value_string]
    """
    if not precondition:
        return {}

    result = {}

    # 处理 * 和 && 分隔的条件
    normalized = precondition.replace('*', '&&')

    # 分割条件
    parts = []
    current_part = []
    balance = 0

    for char in normalized:
        if char == '(':
            balance += 1
            current_part.append(char)
        elif char == ')':
            balance -= 1
            current_part.append(char)
        elif char == '&' and balance == 0:
            parts.append(''.join(current_part).strip())
            current_part = []
            # 跳过第二个 &
            while current_part and current_part[-1] == '&':
                current_part.pop()
        else:
            current_part.append(char)

    if current_part:
        parts.append(''.join(current_part).strip())

    # 从每个部分提取变量和值
    for part in parts:
        part = part.strip().strip('()')
        if not part:
            continue

        # 匹配 var == value 格式
        match = re.match(r'(\w+)\s*==\s*(.+)', part)
        if match:
            var_name = match.group(1)
            value_str = match.group(2).strip()
            result[var_name] = value_str

    return result


def _rewrite_at_pre(invariants: List[str], precondition: str, function_params: Set[str], begin_map: Optional[str] = None) -> List[str]:
    """
    改写不变量中错误使用 \\at(..., Pre) 在非参数变量上的问题。

    规则：
    - 如果 \\at(var, Pre) 中的 var 不是函数参数
    - 就从 begin_map 或 precondition 中找到该变量的初始值并替换

    Args:
        invariants: 不变量列表
        precondition: precondition 字符串（requires 子句）
        function_params: 函数参数集合
        begin_map: 符号执行提取的初始状态（如 "(w == 1) * (z == 1)"），优先使用

    Returns:
        改写后的不变量列表
    """
    if not invariants:
        return []

    # 优先从 begin_map 提取变量值，如果不存在则使用 precondition
    if begin_map:
        pre_values = _extract_precondition_values(begin_map)
    else:
        pre_values = _extract_precondition_values(precondition)

    # 查找所有 \\at(var, Pre) 模式
    pattern = r'\\at\((\w+),\s*Pre\)'

    def replacement(match):
        var_name = match.group(1)

        # 如果是函数参数，保留原样
        if var_name in function_params:
            return match.group(0)

        # 如果不是函数参数，但 begin_map/precondition 中有定义，替换为对应的值
        if var_name in pre_values:
            return pre_values[var_name]

        # 对非参数变量，如果没有初值信息，降级为当前变量名，避免 Frama-C
        # 报 "unbound logic variable <var>" 的语法错误。
        return var_name

    # 对每个不变量应用改写
    rewritten_invariants = []
    for inv in invariants:
        rewritten = re.sub(pattern, replacement, inv)
        rewritten_invariants.append(rewritten)

    return rewritten_invariants


def _simplify_arithmetic_expressions(invariants: List[str]) -> List[str]:
    """
    简化不变量中的算术表达式，避免 Frama-C 语法错误。
    
    处理的模式：
    - 1 * (1) -> 1
    - 1 * (expr) -> expr (当 expr 是常量时)
    - (1) -> 1
    - expr * 1 -> expr
    - expr + 0 -> expr
    - 0 + expr -> expr
    
    Args:
        invariants: 不变量列表
        
    Returns:
        简化后的不变量列表
    """
    if not invariants:
        return []
    
    simplified = []
    for inv in invariants:
        result = inv
        
        # 简化 1 * (数字)
        result = re.sub(r'\b1\s*\*\s*\((\d+)\)', r'\1', result)
        
        # 简化 (单个数字)
        result = re.sub(r'\((\d+)\)(?!\s*[+\-*/])', r'\1', result)
        
        # 简化 expr * 1 (但要小心不要破坏其他表达式)
        result = re.sub(r'(\w+)\s*\*\s*1\b(?!\s*\*)', r'\1', result)
        
        # 简化 1 * expr (但要小心不要破坏其他表达式)
        result = re.sub(r'\b1\s*\*\s*(\w+)', r'\1', result)
        
        # 简化 expr + 0
        result = re.sub(r'(\w+)\s*\+\s*0\b', r'\1', result)
        
        # 简化 0 + expr
        result = re.sub(r'\b0\s*\+\s*(\w+)', r'\1', result)
        
        simplified.append(result)
    
    return simplified


if __name__ == "__main__":
    # 测试用例
    test_record = {
        'loop_idx': 0,
        'current_vars': ['i', 'n', 's'],
        'function_params': ['n'],
        'common_vars': ['i', 'n', 's'],
        'param_pre_vars': {'n': 'n_pre'},
        'precondition': 's == 0',
    }
    
    test_invariants = [
        "0 <= i <= n",
        "s == i * (i + 1) / 2",
        "\\at(n, Pre) >= 0",
        "\\forall integer k; 0 <= k < i ==> a[k] == 0",
        "\\exists integer k; a[k] == x",
        "w == \\product integer t",
        "sorted(a, i)",
        "\\at(s, Pre) == 0",  # s 不是参数，但 precondition 中有定义 s == 0，会被改写为 0 == 0
        "unknown_var > 0",     # 未定义变量
    ]

    print("Unified Loop Invariant Filter")
    print("=" * 60)
    
    result = filter_invariants(test_invariants, test_record, verbose=True)
