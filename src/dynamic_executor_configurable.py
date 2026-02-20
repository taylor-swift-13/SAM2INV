"""
配置驱动的动态执行器修改方案
通过 config.py 控制采样策略，保留原有随机采样功能
"""

import re
import random
from typing import Dict, List, Optional

# 从配置文件读取采样策略
try:
    from config import (
        SAMPLING_STRATEGY,
        SMART_SAMPLING_CONFIG,
        RANDOM_SAMPLING_CONFIG,
        SAMPLING_DEBUG
    )
except ImportError:
    # 默认配置（如果配置文件不存在）
    SAMPLING_STRATEGY = 'random'
    SMART_SAMPLING_CONFIG = {'enable_negative': True, 'max_samples': 100}
    RANDOM_SAMPLING_CONFIG = {'default_min': -100, 'default_max': 100}
    SAMPLING_DEBUG = False

# 仅在使用智能采样时才导入 SmartSampler
if SAMPLING_STRATEGY == 'smart':
    try:
        from smart_sampler import SmartSampler
    except ImportError:
        print("⚠️  警告: smart_sampler.py 未找到，将使用随机采样")
        SAMPLING_STRATEGY = 'random'


class DynamicExecutorConfigurable:
    """
    配置驱动的动态执行器

    特性：
    1. 通过 config.py 控制采样策略
    2. 完全保留原有随机采样功能
    3. 向后兼容，可随时切换
    4. 无需修改调用代码
    """

    def __init__(self, default_min: int = None, default_max: int = None):
        """
        初始化动态执行器

        Args:
            default_min: 默认最小值（如果为None，从配置读取）
            default_max: 默认最大值（如果为None，从配置读取）
        """
        # 从配置文件读取默认值
        if default_min is None:
            default_min = RANDOM_SAMPLING_CONFIG.get('default_min', -100)
        if default_max is None:
            default_max = RANDOM_SAMPLING_CONFIG.get('default_max', 100)

        self.DEFAULT_MIN = default_min
        self.DEFAULT_MAX = default_max

        # 读取采样策略配置
        self.sampling_strategy = SAMPLING_STRATEGY
        self.sampling_debug = SAMPLING_DEBUG

        # 初始化智能采样器（如果需要）
        if self.sampling_strategy == 'smart':
            try:
                self.smart_sampler = SmartSampler(
                    enable_negative=SMART_SAMPLING_CONFIG.get('enable_negative', True),
                    max_samples=SMART_SAMPLING_CONFIG.get('max_samples', 100)
                )
                if self.sampling_debug:
                    print("✅ 已启用智能采样策略 (从简单值开始)")
            except Exception as e:
                print(f"⚠️  智能采样器初始化失败: {e}，将使用随机采样")
                self.sampling_strategy = 'random'

        if self.sampling_strategy == 'random' and self.sampling_debug:
            print("ℹ️  使用随机采样策略 (原始版本)")
        
        # 用于跟踪每次调用的采样索引，确保多样性
        self._call_counter = 0

    def _get_constraints(self, pre_condition_str: str, post_condition_template: str) -> Dict:
        """
        解析约束条件（保持原有逻辑）
        从 requires 和 template 中提取变量约束
        
        支持两种格式：
        1. \\at(var, Pre) - ACSL 格式
        2. var@pre - 简化格式
        """
        constraints = {}

        # 处理 None 值：如果为 None，转换为空字符串
        if pre_condition_str is None:
            pre_condition_str = ""
        if post_condition_template is None:
            post_condition_template = ""

        combined_str = pre_condition_str + ' ' + post_condition_template

        # 提取所有 \\at(var, Pre) 变量（ACSL 格式）
        pre_vars_acsl = set(re.findall(r'\\at\((\w+),\s*Pre\)', combined_str))
        
        # 提取所有 var@pre 变量（简化格式）
        pre_vars_simple = set(re.findall(r'(\w+)@pre', combined_str))
        
        # 合并两种格式的变量
        pre_vars = pre_vars_acsl | pre_vars_simple

        # 为每个变量设置默认范围
        for var in pre_vars:
            constraints[var] = {'min': self.DEFAULT_MIN, 'max': self.DEFAULT_MAX}

        # 提取所有可能的变量名（包括函数参数和 @pre 变量）
        all_vars = set(re.findall(r'\b(\w+)\b', combined_str))
        # 排除常见的关键字
        keywords = {'int', 'void', 'float', 'double', 'long', 'short', 'const', 'return', 'if', 'else', 'for', 'while', 'do', 'switch', 'case', 'break', 'continue', 'goto', 'sizeof', 'typedef', 'struct', 'union', 'enum', 'extern', 'static', 'auto', 'register', 'signed', 'unsigned', 'char', 'main', 'printf', 'scanf', 'time', 'srand', 'Pre', 'at'}
        all_vars = {v for v in all_vars if v not in keywords}
        
        # 为所有识别到的变量设置默认范围（如果还没有设置）
        for var in all_vars:
            if var not in constraints:
                constraints[var] = {'min': self.DEFAULT_MIN, 'max': self.DEFAULT_MAX}
        
        # 解析具体约束（包括等值约束）
        patterns = [
            (r'(\w+)\s*==\s*(-?\d+)', lambda m: {'min': int(m.group(2)), 'max': int(m.group(2))}),  # 等值约束
            (r'(\w+)\s*>\s*(-?\d+)', lambda m: {'min': int(m.group(2)) + 1}),
            (r'(\w+)\s*>=\s*(-?\d+)', lambda m: {'min': int(m.group(2))}),
            (r'(\w+)\s*<\s*(-?\d+)', lambda m: {'max': int(m.group(2)) - 1}),
            (r'(\w+)\s*<=\s*(-?\d+)', lambda m: {'max': int(m.group(2))}),
        ]

        for pattern, constraint_func in patterns:
            for match in re.finditer(pattern, combined_str):
                var_name = match.group(1)
                # 如果变量不在 constraints 中，先添加它（用于普通函数参数）
                if var_name not in constraints:
                    constraints[var_name] = {'min': self.DEFAULT_MIN, 'max': self.DEFAULT_MAX}
                constraint = constraint_func(match)
                constraints[var_name].update(constraint)

        return constraints

    def substitute_pre_values(self,
                             pre_condition_str: str,
                             post_condition_template: str,
                             m: int = 1) -> List[str]:
        """
        根据前条件生成 m 组值，替换 @pre

        根据配置自动选择采样策略：
        - SAMPLING_STRATEGY='smart': 使用智能采样（从简单值开始）
        - SAMPLING_STRATEGY='random': 使用随机采样（原始版本）

        Args:
            pre_condition_str: 前置条件字符串（如 "x > 0 && y > 0"）
            post_condition_template: 后置条件模板（包含 @pre 变量）
            m: 需要生成的样本数量

        Returns:
            替换后的条件字符串列表
        """
        # 1. 解析约束
        constraints = self._get_constraints(pre_condition_str, post_condition_template)

        if not constraints and not re.search(r'\w+@pre', post_condition_template):
            return [post_condition_template] * m

        # 2. 根据配置选择采样策略
        if self.sampling_strategy == 'smart' and hasattr(self, 'smart_sampler'):
            return self._smart_sampling(constraints, post_condition_template, m)
        else:
            return self._random_sampling(constraints, post_condition_template, m)

    def _smart_sampling(self,
                       constraints: Dict,
                       post_condition_template: str,
                       m: int) -> List[str]:
        """
        智能采样策略：从简单值开始系统遍历
        """
        try:
            if self.sampling_debug:
                print(f"🎯 使用智能采样策略生成 {m} 个样本")

            samples = self.smart_sampler.generate_samples(constraints, num_samples=m)

            results = []
            for sample in samples:
                final_str = post_condition_template
                for name, val in sample.items():
                    # 替换 \\at(name, Pre) 格式
                    final_str = re.sub(rf'\\at\({re.escape(name)},\s*Pre\)', str(val), final_str)
                    # 替换 name@pre 格式
                    final_str = re.sub(rf'\b{re.escape(name)}@pre\b', str(val), final_str)
                results.append(final_str)

            if self.sampling_debug and results:
                print(f"✅ 智能采样完成: 前3个样本")
                for i, r in enumerate(results[:3], 1):
                    print(f"   {i}. {r}")

            return results

        except Exception as e:
            if self.sampling_debug:
                print(f"⚠️  智能采样失败: {e}，切换到随机采样")
            return self._random_sampling(constraints, post_condition_template, m)

    def _random_sampling(self,
                        constraints: Dict,
                        post_condition_template: str,
                        m: int) -> List[str]:
        """
        随机采样策略：完全随机（原始版本）
        """
        if self.sampling_debug:
            print(f"🎲 使用随机采样策略生成 {m} 个样本")

        results, generated_sets = [], set()
        attempts, max_attempts = 0, m * 100

        while len(results) < m and attempts < max_attempts:
            attempts += 1
            pre_values, current_set_tuple = {}, []

            for name, limits in constraints.items():
                val = random.randint(limits['min'], limits['max'])
                pre_values[name] = val
                current_set_tuple.append((name, val))

            current_set_tuple.sort()
            current_set = tuple(current_set_tuple)

            if current_set not in generated_sets:
                generated_sets.add(current_set)
                final_str = post_condition_template
                for name, val in pre_values.items():
                    # 替换 \\at(name, Pre) 格式
                    final_str = re.sub(rf'\\at\({re.escape(name)},\s*Pre\)', str(val), final_str)
                    # 替换 name@pre 格式
                    final_str = re.sub(rf'\b{re.escape(name)}@pre\b', str(val), final_str)
                results.append(final_str)

        if attempts >= max_attempts and len(results) < m:
            print(f"⚠️  警告：仅生成了 {len(results)} 个结果 (目标: {m})")

        if self.sampling_debug and results:
            print(f"✅ 随机采样完成: 前3个样本")
            for i, r in enumerate(results[:3], 1):
                print(f"   {i}. {r}")

        return results

    def generate_random_test_case(self, code: str) -> tuple:
        """
        为给定的 C 代码生成随机测试用例
        包含原始函数和一个 main 函数，使用随机参数调用原始函数
        
        Returns:
            (test_case_code, param_values_dict): 测试用例代码和参数值字典
            param_values_dict: {param_name: value} 格式
        """
        import subprocess
        import tempfile
        import os

        headers = '''#include "stdio.h"
#include "stdlib.h"
#include "time.h"
'''

        try:
            code = code.replace('\r\n', '\n').replace('\r', '\n')
            lines = code.split('\n')
            function_code_lines = []
            function_found = False
            function_signature = None
            main_function_already_exists = False

            for i, line in enumerate(lines):
                if 'int main(' in line or 'void main(' in line or 'main()' in line:
                    main_function_already_exists = True
                    break

                stripped_line = line.strip()
                if stripped_line.startswith('/*@') or stripped_line.startswith('//') or stripped_line.startswith('/*'):
                    continue

                if function_found:
                    function_code_lines.append(line)
                    brace_count = sum(1 for char in ''.join(function_code_lines) if char == '{')
                    close_brace_count = sum(1 for char in ''.join(function_code_lines) if char == '}')
                    if close_brace_count > 0 and brace_count == close_brace_count:
                        break
                elif any(keyword in stripped_line for keyword in ['int ', 'void ', 'float ', 'double ', 'long ']):
                    if ('(' in line and ')' in line) and '{' in line:
                        function_found = True
                        function_signature = stripped_line.split('{')[0].strip()
                        function_code_lines.append(line)

            if not main_function_already_exists and function_code_lines:
                function_code = '\n'.join(function_code_lines)

                func_name_match = re.search(r'\b(\w+)\s*\(', function_signature)
                func_name = func_name_match.group(1) if func_name_match else 'test_function'

                params_match = re.search(r'\(([^)]*)\)', function_signature)
                params_str = params_match.group(1).strip() if params_match else ''

                if params_str:
                    # 提取参数名（只考虑 int 类型）
                    param_names = []
                    for p in params_str.split(','):
                        p = p.strip()
                        # 匹配 int 类型参数: 'int x', 'int* x', 'const int x' 等
                        param_match = re.match(r'(?:const\s+)?int\s*(?:\*+\s*)?(\w+)', p)
                        if param_match:
                            param_names.append(param_match.group(1))
                else:
                    param_names = []

                # 解析 requires 子句以获取参数约束
                requires_clause = None
                # 查找 /*@ requires ... */ 或 //@ requires ...
                requires_pattern = r'(?:/\*@|//@)\s*requires\s+([^@]+?)(?:\*/|$)'
                
                # 先在 function_code 中查找
                requires_match = re.search(requires_pattern, function_code, re.DOTALL)
                if not requires_match:
                    # 如果 function_code 中没有，在整个 code 中查找（可能在函数定义前）
                    requires_match = re.search(requires_pattern, code, re.DOTALL)
                
                if requires_match:
                    requires_clause = requires_match.group(1).strip()
                
                # 从 requires 子句提取约束
                constraints = {}
                if requires_clause:
                    constraints = self._get_constraints(requires_clause, '')
                
                # 生成随机参数值并保存
                param_values = {}
                main_code = '''
int main() {
    srand(time(NULL));
'''

                for param_idx, param in enumerate(param_names):
                    # 检查是否有针对该参数的约束
                    param_constraint = constraints.get(param, {})

                    # 确定参数的最小值和最大值
                    min_val = param_constraint.get('min', self.DEFAULT_MIN)
                    max_val = param_constraint.get('max', self.DEFAULT_MAX)

                    # 如果 requires 子句中有 > 0 或 >= 1 等约束，确保最小值至少为 1
                    if requires_clause:
                        # 检查是否有 param > 0 或 param >= 1 等约束
                        param_gt_pattern = rf'\b{re.escape(param)}\s*>\s*(\d+)'
                        param_ge_pattern = rf'\b{re.escape(param)}\s*>=\s*(\d+)'

                        gt_match = re.search(param_gt_pattern, requires_clause)
                        ge_match = re.search(param_ge_pattern, requires_clause)

                        if gt_match:
                            min_val = max(min_val, int(gt_match.group(1)) + 1)
                        elif ge_match:
                            min_val = max(min_val, int(ge_match.group(1)))

                    # 使用智能采样策略生成参数值（如果可用）
                    if self.sampling_strategy == 'smart' and hasattr(self, 'smart_sampler'):
                        # 使用智能采样器生成当前参数值（不做缓存）
                        param_constraints = {param: {'min': min_val, 'max': max_val}}
                        samples = self.smart_sampler.generate_samples(param_constraints, num_samples=1)
                        if samples:
                            param_value = samples[0][param]
                        else:
                            param_value = random.randint(min_val, max_val)
                    else:
                        # 随机生成（确保满足约束）
                        param_value = random.randint(min_val, max_val)

                    param_values[param] = param_value
                    main_code += f'    int {param} = {param_value};\n'

                main_code += f'    {func_name}({", ".join(param_names) if param_names else ""});\n'
                main_code += '    return 0;\n}\n'

                # 增加调用计数器，确保下次调用时使用不同的样本
                self._call_counter += 1

                full_code = headers + function_code + '\n' + main_code
                return full_code, param_values

            return code, {}

        except Exception as e:
            print(f"Error generating test case: {e}")
            return code, {}

    def execute_c_code(self, c_code_string: str) -> tuple:
        """
        执行 C 代码并返回输出和超时标志
        """
        import subprocess
        import tempfile
        import os
        import time

        compiler_command = 'gcc'
        executable_name = '.out'
        language_extension = '.c'

        source_filename = None
        executable_path = None

        try:
            with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=language_extension) as tmp_file:
                tmp_file.write(c_code_string)
                source_filename = tmp_file.name

            executable_path = os.path.splitext(source_filename)[0] + executable_name

            compile_command = [compiler_command, source_filename, '-o', executable_path]

            subprocess.run(
                compile_command,
                check=True,
                capture_output=True,
                text=True,
                timeout=5
            )

            run_command = [executable_path]

            # Use Popen with output limit to prevent OOM from infinite loops.
            # Infinite loops (e.g., Newton's method oscillation) can produce GBs
            # of printf output in 10s, causing memory exhaustion with capture_output.
            MAX_OUTPUT_BYTES = 2 * 1024 * 1024  # 2 MB limit
            proc = subprocess.Popen(
                run_command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            try:
                stdout_bytes, _ = proc.communicate(timeout=10)
                # Truncate to limit memory usage
                if len(stdout_bytes) > MAX_OUTPUT_BYTES:
                    stdout_bytes = stdout_bytes[:MAX_OUTPUT_BYTES]
                timeout = False
                return stdout_bytes.decode('utf-8', errors='replace').strip(), timeout
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.communicate()  # clean up
                timeout = True
                return "", timeout
        except subprocess.CalledProcessError as e:
            timeout = False
            return (f"Compilation/execution failed\nSTDOUT: {e.stdout}\nSTDERR: {e.stderr.strip()}"), timeout
        except FileNotFoundError:
            timeout = False
            return f"Compiler '{compiler_command}' not found", timeout
        except Exception as e:
            timeout = False
            return f"Unexpected error: {e}", timeout
        finally:
            if source_filename and os.path.exists(source_filename):
                os.remove(source_filename)
            if executable_path and os.path.exists(executable_path):
                os.remove(executable_path)


# ==============================================================================
# 使用示例和测试
# ==============================================================================

def demo_configurable_executor():
    """演示配置驱动的执行器"""
    print("="*70)
    print("  配置驱动的动态执行器演示")
    print("="*70)
    print(f"\n当前配置: SAMPLING_STRATEGY = '{SAMPLING_STRATEGY}'")
    print(f"调试模式: SAMPLING_DEBUG = {SAMPLING_DEBUG}\n")

    # 创建执行器
    executor = DynamicExecutorConfigurable()

    # 测试场景
    pre_condition = "x > 0 && y > 0"
    post_template = "result == x@pre + 2*y@pre"

    print(f"测试场景:")
    print(f"  前置条件: {pre_condition}")
    print(f"  后置模板: {post_template}")
    print(f"  生成数量: 8\n")

    results = executor.substitute_pre_values(pre_condition, post_template, m=8)

    print(f"\n生成的样本:")
    for i, result in enumerate(results, 1):
        print(f"  {i:2d}. {result}")

    print("\n" + "="*70)
    print("提示: 修改 config.py 中的 SAMPLING_STRATEGY 可切换采样策略")
    print("  - 'smart': 智能采样（从简单值开始）")
    print("  - 'random': 随机采样（原始版本）")
    print("="*70)


if __name__ == '__main__':
    demo_configurable_executor()
