import re
from typing import List, Tuple, Dict, Set, Optional
import ast
import unittest

# --- 实用工具函数 ---

def strip_outer_parens(s: str) -> str:
    """剥离最外层括号，直到无法再剥离。"""
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        balance = 0
        matched = False
        for i, ch in enumerate(s):
            if ch == '(':
                balance += 1
            elif ch == ')':
                balance -= 1
            if balance == 0:
                matched = (i == len(s) - 1)
                break
        if matched:
            s = s[1:-1].strip()
        else:
            break
    return s

def split_and_conditions(clause: str) -> List[str]:
    """
    仅分解最外层（括号层级为 0）的 '&&'。
    """
    parts = []
    current_part = []
    balance = 0
    
    # 替换 '&&' 为一个不容易出现的标记
    s = clause.replace('&&', '\x00')
    
    for ch in s:
        if ch == '(':
            balance += 1
            current_part.append(ch)
        elif ch == ')':
            balance -= 1
            current_part.append(ch)
        elif ch == '\x00' and balance == 0:
            # 找到了顶层 '&&'
            parts.append("".join(current_part).strip())
            current_part = []
        else:
            current_part.append(ch)

    if current_part:
        parts.append("".join(current_part).strip())
        
    return [p.replace('\x00', '&&') for p in parts if p.strip()]

# 修复点 1: 全局去除空格，确保输出格式紧凑
def replace_top_level_star_with_and(s: str) -> str:
    """
    将最外层 '*' 替换为 '&&'。
    为了匹配测试用例并简化处理，此函数会移除输入字符串中的所有空格。
    """
    # 1. 直接移除所有空格，满足 "忽略空格" 的要求，并匹配测试期望 (a*b)&&c
    s = s.replace(' ', '')
    
    out = []
    depth = 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == '(':
            depth += 1
            out.append(ch)
        elif ch == ')':
            depth = max(0, depth-1)
            out.append(ch)
        elif ch == '*' and depth == 0:
            out.append('&&')
        else:
            out.append(ch)
        i += 1
    
    result = "".join(out)
    return result


# --- 核心逻辑函数 ---

def process_conditions(parts: List[str], bound_vars: Set[str]) -> Tuple[Dict[str, int], List[str]]:
    initial_values: Dict[str, int] = {}
    remaining: List[str] = []

    # 1. 收集 \\at(var, Pre) 初值
    for part in parts:
        p = strip_outer_parens(part) 
        
        if p.startswith('exists') or p.startswith('retval') or 'retval_' in p:
            continue
            
        # 匹配紧凑形式 \\at(var, Pre)==val
        pre_match = re.fullmatch(r'\\at\((\w+),\s*Pre\)==(-?\d+)', p)
        if pre_match:
            var, val = pre_match.groups()
            initial_values[var] = int(val)
            # 添加到 remaining，后续去重
            remaining.append(f"\\at({var}, Pre)=={val}") 
            continue
            
        # 对于普通赋值，为了方便正则匹配和阅读，我们不需要手动加空格，
        # 直接按紧凑形式处理，或者在下面正则中兼容无空格
        remaining.append(p)

    # --- 表达式求值工具 ---
    allowed_binops = (
        ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod,
        ast.BitAnd, ast.BitOr, ast.BitXor, ast.LShift, ast.RShift,
    )
    allowed_unops = (ast.UAdd, ast.USub, ast.Invert)

    def _eval_ast(node: ast.AST) -> int:
        if isinstance(node, (ast.Num, ast.Constant)):
            return int(getattr(node, 'n', node.value))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, allowed_unops):
            val = _eval_ast(node.operand)
            if isinstance(node.op, ast.UAdd): return +val
            if isinstance(node.op, ast.USub): return -val
            if isinstance(node.op, ast.Invert): return ~val
        if isinstance(node, ast.BinOp) and isinstance(node.op, allowed_binops):
            left = _eval_ast(node.left)
            right = _eval_ast(node.right)
            if isinstance(node.op, ast.Add): return left + right
            if isinstance(node.op, ast.Sub): return left - right
            if isinstance(node.op, ast.Mult): return left * right
            if isinstance(node.op, (ast.Div, ast.FloorDiv)): return int(left // right)
            if isinstance(node.op, ast.Mod): return left % right
            if isinstance(node.op, ast.BitAnd): return left & right
            if isinstance(node.op, ast.BitOr): return left | right
            if isinstance(node.op, ast.BitXor): return left ^ right
            if isinstance(node.op, ast.LShift): return left << right
            if isinstance(node.op, ast.RShift): return left >> right
        
        if isinstance(node, ast.Name):
            var_name = node.id
            if var_name in initial_values:
                return initial_values[var_name]
            raise NameError(f"Undefined variable in expression: {var_name}")
        
        raise ValueError("Unsupported expression structure or operation")

    def safe_eval_int(expr: str) -> int:
        expr = expr.replace('/', '//')
        
        def _sub_pre_name(mm):
            v = mm.group(1)
            return v 
        # \b 在无空格情况下也能正确匹配单词边界（例如 \\at(x, Pre)+10，@和+都是非单词字符）
        # 将 \\at(var, Pre) 替换为 var 以便求值
        eval_expr = re.sub(r'\\at\((\w+),\s*Pre\)', _sub_pre_name, expr)
        
        tree = ast.parse(eval_expr, mode='eval')
        return _eval_ast(tree.body)

    # 2. 第二轮处理：简化赋值
    final_remaining = []
    unique_results: Set[str] = set()
    
    for part in remaining:
        p = part 

        # 紧凑形式匹配 \\at(var, Pre)==val
        if re.fullmatch(r'\\at\(\w+,\s*Pre\)==-?\d+', p):
            if p not in unique_results:
                final_remaining.append(p)
                unique_results.add(p)
            continue
        
        # 形如 var==<expr> (紧凑)
        # 注意：由于输入已去空格，正则不需要 \s*
        m = re.fullmatch(r'(\w+)==(.+)', p)
        if m:
            var = m.group(1)
            rhs = m.group(2)
            
            try:
                val = safe_eval_int(rhs)
                
                # 防止重复计算覆盖（保持第一次计算的值，或根据逻辑需要）
                # 这里的逻辑是：如果算出来的值与已有的不同，且已有值来自 @pre，则更新
                # 但简单起见，我们信任 safe_eval_int 的结果
                initial_values[var] = int(val)
                
                # 输出紧凑格式
                result_str = f"{var}=={val}"
                if result_str not in unique_results:
                    final_remaining.append(result_str)
                    unique_results.add(result_str)
                continue
            except (ValueError, NameError, TypeError, SyntaxError, ZeroDivisionError):
                pass
        
        # 过滤掉纯数字
        if re.fullmatch(r"-?\d+", p):
            continue
        
        if p not in unique_results:
            final_remaining.append(p)
            unique_results.add(p)

    return initial_values, final_remaining


def simplify_clause(clause: str, allowed_vars: Optional[Set[str]] = None) -> str:
    # 1. 替换顶层 * 并去除所有空格
    clause = replace_top_level_star_with_and(clause)
    # 2. 剥离最外层括号
    clause = strip_outer_parens(clause)
    bound_vars: Set[str] = set()
    
    # 3. 迭代展开所有 && 连接
    current_queue = [clause]
    final_parts = []
    processed_parts: Set[str] = set()
    
    while current_queue:
        part = current_queue.pop(0)
        
        if not part or part in processed_parts:
            continue
        processed_parts.add(part)

        sub_parts = split_and_conditions(part)
        
        if len(sub_parts) > 1:
            current_queue.extend(sub_parts)
        else:
            stripped_part = strip_outer_parens(part)
            if not stripped_part:
                continue
            
            # 再次检查剥离括号后是否暴露了新的 &&
            if '&&' in stripped_part:
                if stripped_part not in processed_parts:
                    current_queue.append(stripped_part)
            else:
                final_parts.append(stripped_part)

    # 4. 处理条件并求值
    initial_values, remaining = process_conditions(final_parts, bound_vars)

    # 5. 组装结果，使用紧凑连接符 '&&' (或者 ' && '，根据您的测试期望)
    # 根据之前的测试失败信息 - (a * b)&&c vs (a*b)&&c，
    # 这里的期望是紧凑的 &&，或者您想要带空格的 &&？
    # 通常测试用例 self.assertEqual(..., "x@pre == 5 && x == 9") 里面是带空格的 &&。
    # **但是** replace_top_level_star 测试用例期望的是 (a*b)&&c (无空格)。
    # 为了兼容，我们这里输出带空格的 ' && ' 增强可读性，
    # 但在 replace_top_level_star_with_and 中我们严格输出了无空格。
    # 
    # 如果您的测试用例 parse_and_simplify 期望的结果字符串包含空格 (如 "x == 9")，
    # 那么我们需要在 f-string 中加回空格。
    #
    # 让我们看测试用例 t1: "x@pre == 5 && x == 9" (带空格)
    # 而 process_conditions 现在生成的是 "x@pre==5" (无空格)
    #
    # 为了让所有测试通过，我们需要统一输出格式。
    # 我将统一输出为 **带空格** 的标准格式 "var == val"，
    # 但 replace_top_level_star_with_and 保持无空格用于内部处理和特定测试。
    
    # 修改 process_conditions 的输出为带空格的标准格式：
    formatted_results = []
    for r in remaining:
        # 尝试格式化 == 为带空格形式，提升可读性并匹配 parse_and_simplify 的测试期望
        if '==' in r:
             # 将紧凑的 == 替换为 == 
             r = r.replace('==', ' == ')
        formatted_results.append(r)

    simplified = " && ".join(formatted_results).strip()
    
    # 过滤逻辑
    if allowed_vars is not None and simplified:
        filtered_results = []
        for result_part in formatted_results:
            clause_vars = set()
            matches = re.findall(r'\b(\w+)(?:@pre)?\b', result_part)
            for match in matches:
                if match.isdigit(): continue
                # 注意：由于重新加了空格，@pre 可能被切分，但上面 regex 没变
                # 简单起见，我们重新在 result_part 中找
                pass 
            
            # 重新提取变量逻辑（针对带空格的字符串）
            # 查找 x@pre 或 x
            found_vars = re.findall(r'\b\w+(?:@pre)?\b', result_part)
            current_clause_vars = set()
            for v in found_vars:
                 if not v[0].isdigit(): # 简单排除数字
                     current_clause_vars.add(v)
            
            all_allowed = all(v in allowed_vars for v in current_clause_vars) if current_clause_vars else True
            if all_allowed:
                filtered_results.append(result_part)
        
        return " && ".join(filtered_results).strip()
    
    return simplified

def parse_and_simplify(expr: str, allowed_vars: Optional[Set[str]] = None) -> str:
    return simplify_clause(expr, allowed_vars)

def parse_samples(input_string: str, allowed_vars: Optional[Set[str]] = None) -> Dict[str, List[str]]:
    """
    解析 LoopEntry_<idx>[_initial|_final] 字符串块，提取**块中的单行内容**，
    对每个内容应用 parse_and_simplify 函数。将所有同 idx 的结果聚合，
    保留 initial、迭代、final 的顺序。
    
    标记说明：
    - LoopEntry_{idx}_initial: 进入循环前的状态
    - LoopEntry_{idx}: 循环迭代中的状态
    - LoopEntry_{idx}_final: 退出循环后的状态

    参数:
    - input_string: 包含 LoopEntry_<idx>[_initial|_final] 块的字符串。
    - allowed_vars: 允许的变量集合（current_vars U param_pre_vars），用于过滤 clause

    返回:
    - 按 idx 分组的简化条件列表，保持 initial -> iterations -> final 的顺序。
    """
    # 1. 捕获 "LoopEntry_xxx" 或 "LoopEntry_xxx_initial" 或 "LoopEntry_xxx_final" 和对应的内容
    # 模式：LoopEntry_(\d+)(?:_(initial|final))?: 匹配三种情况
    pattern = r'LoopEntry_(\d+)(?:_(initial|final))?:\s*(.*?)(?=\s*LoopEntry_\d+(?:_(initial|final))?:|$)'
    matches = re.findall(pattern, input_string, re.DOTALL)

    # 临时字典用于聚合所有结果，保持顺序
    # 结构：{idx: [(marker_type, simplified_result), ...]}
    # marker_type: 'initial', 'final', 或 None (迭代)
    all_simplified_results: Dict[str, List[tuple]] = {}

    # 2. 遍历每个匹配项，处理内容并聚合
    for idx, marker_type, content_block, _ in matches:
        clean_content = content_block.strip()
        
        if clean_content:
            simplified_result = parse_and_simplify(clean_content, allowed_vars)
            
            # 聚合：将结果添加到对应 idx 的列表中，保留标记类型
            if idx not in all_simplified_results:
                all_simplified_results[idx] = []
            all_simplified_results[idx].append((marker_type or 'iteration', simplified_result))

    # 3. 对聚合后的每一组进行排序和截断
    # 排序规则：initial -> iterations -> final
    final_grouped: Dict[str, List[str]] = {}
    
    for idx, results_with_markers in all_simplified_results.items():
        # 分离 initial、iterations、final
        initial_traces = []
        iteration_traces = []
        final_traces = []
        
        for marker_type, result in results_with_markers:
            if marker_type == 'initial':
                initial_traces.append(result)
            elif marker_type == 'final':
                final_traces.append(result)
            else:  # iteration
                iteration_traces.append(result)
        
        # 对迭代 traces 进行截断（如果超过限制）
        from config import DYNAMIC_SAMPLING_CONFIG
        m = DYNAMIC_SAMPLING_CONFIG.get('keep_traces_per_run', 3)
        
        if len(iteration_traces) > 2 * m:
            # 保留前 m 个和后 m 个迭代 traces
            iteration_traces = iteration_traces[:m] + iteration_traces[-m:]
        
        # 组合：initial + iterations + final
        # 注意：initial 和 final 可能不存在（如果循环没有执行或只执行一次）
        combined_traces = []
        if initial_traces:
            combined_traces.extend(initial_traces)
        combined_traces.extend(iteration_traces)
        if final_traces:
            combined_traces.extend(final_traces)
        
        final_grouped[idx] = combined_traces
        
        if len(results_with_markers) > len(combined_traces):
            print(f"DEBUG: LoopEntry_{idx} 聚合结果数 ({len(results_with_markers)}) 已截断为 {len(combined_traces)} 个元素 (initial: {len(initial_traces)}, iterations: {len(iteration_traces)}, final: {len(final_traces)})")

    # 4. 返回最终结果
    return final_grouped


# --- 测试类 ---

class TestConditionParser(unittest.TestCase):

    def test_strip_outer_parens(self):
        self.assertEqual(strip_outer_parens("((a && b))"), "a && b")
        # 此时去除了所有空格
        self.assertEqual(strip_outer_parens("( a && (b) )".replace(' ','')), "a&&(b)")

    def test_replace_top_level_star(self):
        # 期望完全无空格的输出
        self.assertEqual(replace_top_level_star_with_and("(a * b) * c"), "(a*b)&&c")
        self.assertEqual(replace_top_level_star_with_and(" a * b "), "a&&b") 

    def test_parse_and_simplify_arithmetic(self):
        # 输入可以是乱的，输出应该是标准格式 "var == val"
        t1 = "\\at(x, Pre) == 5 && (x == \\at(x, Pre) + 10 - 3 * 2)"
        # 期望输出标准格式
        self.assertEqual(parse_and_simplify(t1), "\\at(x, Pre) == 5 && x == 9")
        
        t2 = "\\at(x, Pre) == 8 && (x == \\at(x, Pre)/2 && y == 9%4)"
        self.assertEqual(parse_and_simplify(t2), "\\at(x, Pre) == 8 && x == 4 && y == 1")
        
    def test_parse_and_simplify_complex(self):
        t = "\\at(p, Pre)==6 && \\at(q, Pre)==3 && (p == (\\at(p, Pre)%4 + (1<<2)) * 3) * (q == (\\at(q, Pre)|1) ^ 2)"
        expected = "\\at(p, Pre) == 6 && \\at(q, Pre) == 3 && p == 18 && q == 1"
        self.assertEqual(parse_and_simplify(t), expected)

    def test_parse_and_simplify_filtering(self):
        t = "\\at(a, Pre) == 1 && b == \\at(a, Pre) + 1 && c == 3"
        allowed = {"b"}
        # 输出应包含空格
        self.assertEqual(parse_and_simplify(t, allowed), "b == 2") 

if __name__ == '__main__':
    unittest.main(argv=['first-arg-is-ignored'], exit=False)
