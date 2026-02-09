import re
import math
from typing import Dict, Any, Optional, Set, Tuple

class LoopBoundAnalyzer:
    """
    分析一个以字符串形式描述的循环，并推断出循环条件中变量的边界。

    ✅ 修改特性：
    - 计算并包含“第一次不满足 condition 的情况”（first failing value）。
    - 若该值可达，则输出闭区间（inclusive），如：`0 <= i <= 100 (includes first failing value 100)`。
    - 若无法到达，则返回说明信息或维持旧式边界推断。
    """

    # ---------- 基础解析 ----------
    def _parse_entry(self, entry_str: str) -> Dict[str, int]:
        """解析初始条件字符串 -> {'var': val, ...}"""
        initial_state = {}
        pattern = re.compile(r'\(\s*(\w+)\s*==\s*(-?\d+)\s*\)')
        matches = pattern.findall(entry_str)
        for var, val in matches:
            initial_state[var] = int(val)
        return initial_state

    def _parse_condition(self, cond_str: str) -> Optional[Dict[str, Any]]:
        """解析循环条件 -> {'var': 'x', 'op': '<', 'val': 10}"""
        pattern = re.compile(r'\s*(\w+)\s*([<>]=?|==|!=)\s*(-?\d+)\s*')
        match = pattern.match(cond_str.strip())
        if match:
            var, op, val = match.groups()
            return {'var': var, 'op': op, 'val': int(val)}
        return None

    def _parse_iteration(self, iter_str: str) -> Dict[str, str]:
        """解析迭代规则 -> {'var': 'expr', ...}"""
        update_rules = {}
        pattern = re.compile(r'\(\s*(\w+)\s*==?\s*(.*?)\s*\)')
        matches = pattern.findall(iter_str)
        for var, expr in matches:
            update_rules[var] = expr.strip()
        return update_rules

    # ---------- 常量与步长解析 ----------
    def _find_constant_variables(self, rules: Dict[str, str]) -> Set[str]:
        """找出在循环中保持不变的变量"""
        constant_vars = set()
        for var, expr in rules.items():
            if expr == var or expr == f"{var}@last":
                constant_vars.add(var)
        return constant_vars

    def _resolve_step_size(
        self,
        target_var: str,
        update_expr: str,
        initial_state: Dict[str, int],
        constant_vars: Set[str]
    ) -> Optional[int]:
        """根据更新表达式解析目标变量的恒定步长"""
        resolved_expr = update_expr

        # 替换常量变量为初始值
        for const_var in constant_vars:
            if const_var in initial_state:
                const_val = initial_state[const_var]
                resolved_expr = re.sub(
                    r'\b' + re.escape(f"{const_var}@last") + r'\b',
                    str(const_val),
                    resolved_expr
                )
                resolved_expr = re.sub(
                    r'\b' + re.escape(const_var) + r'\b',
                    str(const_val),
                    resolved_expr
                )

        # 去除 target_var@last / target_var 后剩下步长部分
        step_expr = re.sub(r'\b' + re.escape(f"{target_var}@last") + r'\b', '', resolved_expr)
        step_expr = re.sub(r'\b' + re.escape(target_var) + r'\b', '', step_expr).strip()

        # 尝试匹配 ±整数模式
        try:
            match = re.fullmatch(r'\s*([+-]?)\s*(\d+)\s*', step_expr)
            if match:
                sign, val_str = match.groups()
                value = int(val_str)
                return -value if sign == '-' else value
        except (ValueError, TypeError):
            return None
        return None

    # ---------- 条件与首次失效检测 ----------
    def _eval_condition(self, x: int, op: str, c: int) -> bool:
        if op == '<': return x < c
        if op == '<=': return x <= c
        if op == '>': return x > c
        if op == '>=': return x >= c
        if op == '==': return x == c
        if op == '!=': return x != c
        raise ValueError(f"Unsupported operator: {op}")

    def _first_failing_value(self, start: int, step: int, op: str, c: int) -> Optional[Tuple[int,bool]]:
        """
        计算第一次不满足条件的变量值。
        返回 (first_failing_value, reachable_flag)。
        """
        if not self._eval_condition(start, op, c):
            return (start, True)
        if step == 0:
            return (None, False)

        going_up = step > 0
        will_eventually_flip = False
        if op in ('<', '<='):
            will_eventually_flip = going_up
        elif op in ('>', '>='):
            will_eventually_flip = not going_up
        elif op in ('==', '!='):
            will_eventually_flip = True

        if not will_eventually_flip:
            return (None, False)

        s, d = start, step
        def ceil_div(a, b): return math.ceil(a / b)

        n = None
        if op == '<':
            if d > 0:
                n = max(0, ceil_div(c - s, d))
            else:
                return (None, False)
        elif op == '<=':
            if d > 0:
                n = ( (c - s) // d ) + 1
                n = max(0, n)
            else:
                return (None, False)
        elif op == '>':
            if d < 0:
                t = -d
                n = max(0, ceil_div(s - c, t))
            else:
                return (None, False)
        elif op == '>=':
            if d < 0:
                t = -d
                n = ( (s - c) // t ) + 1
                n = max(0, n)
            else:
                return (None, False)
        elif op == '==':
            if d == 0: return (None, False)
            n = 1
        elif op == '!=':
            if d == 0: return (None, False)
            if (c - s) % d == 0:
                n = (c - s) // d
                if n < 0: return (None, False)
            else:
                return (None, False)

        first_fail_val = s + n * d
        return (first_fail_val, True)

    # ---------- 主分析接口 ----------
    def analyze(self, entry_str: str, cond_str: str, iter_str: str) -> str:
        """主分析函数"""
        try:
            initial_state = self._parse_entry(entry_str)
            cond_info = self._parse_condition(cond_str)
            update_rules = self._parse_iteration(iter_str)
        except Exception as e:
            return f"Error parsing inputs: {e}"

        if not cond_info:
            return "Error: Could not parse loop condition."

        target_var = cond_info['var']

        if target_var not in initial_state:
            return f"Error: Initial value for '{target_var}' not found in LoopEntry."
        if target_var not in update_rules:
            return f"Error: Update rule for '{target_var}' not found in Iteration."

        constant_vars = self._find_constant_variables(update_rules)
        start_val = initial_state[target_var]
        update_expr = update_rules[target_var]
        step = self._resolve_step_size(target_var, update_expr, initial_state, constant_vars)

        if step is None:
            return (f"Error: Could not resolve a constant step for '{target_var}'. "
                    f"Update rule: '{update_expr}'")

        cond_op, cond_val = cond_info['op'], cond_info['val']

        first_fail = self._first_failing_value(start_val, step, cond_op, cond_val)
        if first_fail and first_fail[1]:
            ff_val = first_fail[0]
            lo, hi = min(start_val, ff_val), max(start_val, ff_val)
            return f"{lo} <= {target_var} <= {hi}", f"(includes first failing value {ff_val})"
        else:
            if step > 0:
                if cond_op in ('<', '<='):
                    return f"{start_val} <= {target_var} <= {cond_val}"
                else:
                    return f"{start_val} <= {target_var}", f"(condition may never fail with step {step})"
            elif step < 0:
                if cond_op in ('>', '>='):
                    return f"{cond_val} <= {target_var} <= {start_val}"
                else:
                    return f"{target_var} <= {start_val}", f"(condition may never fail with step {step})"
            else:
                return f"Analysis Result: Variable '{target_var}' is constant at {start_val}."


# ---------- 示例 ----------
if __name__ == "__main__":
    analyzer = LoopBoundAnalyzer()

    print("--- Example 1: Indirect Constant Step (User's Case) ---")
    entry1 = "(counter == 100)*(const == 5)"
    cond1 = "counter > 0"
    iter1 = "(counter == counter@last - const@last)*(const == const@last)"
    print(analyzer.analyze(entry1, cond1, iter1), "\n")

    print("--- Example 2: Direct Constant Step ---")
    entry2 = "(y == 0)"
    cond2 = "y < 10000"
    iter2 = "(y = y@last + 9)"
    print(analyzer.analyze(entry2, cond2, iter2), "\n")

    print("--- Example 3: Indirect Constant Step (Addition) ---")
    entry3 = "(i == 0)*(step_size == 10)"
    cond3 = "i < 100"
    iter3 = "(i = i + step_size)*(step_size = step_size@last)"
    print(analyzer.analyze(entry3, cond3, iter3), "\n")

    print("--- Example 4: Non-Constant Step (Expected Error) ---")
    entry4 = "(y == 0) * (x == 1)"
    cond4 = "y < 100"
    iter4 = "(y = y + x) * (x = x + 1)"
    print(analyzer.analyze(entry4, cond4, iter4))
