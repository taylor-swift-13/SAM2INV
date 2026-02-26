import argparse
import subprocess
import os
import re
import json
import random
import copy
from pathlib import Path
from dynamic_executor_configurable import DynamicExecutorConfigurable
from typing import List, Tuple, Dict, Set, Optional
from config import LLMConfig, SUBDIR
from llm import Chatbot
from bound_analysis import LoopBoundAnalyzer
from loop_analysis import LoopAnalysis
from simple import parse_samples

class LoopSampler:
    def __init__ (self, file_name, input_subdir: Optional[str] = None):
        """
        Initialize LoopSampler object.
        :param file_name: Filename (without extension)
        :param input_subdir: Input subdirectory (e.g., 'linear', 'NLA_lipus'). If None, will auto-detect.
        """
        if file_name.endswith('.c'):
            file_name = file_name[:-2]
        
        self.file_name = file_name
        self.input_subdir_config = input_subdir  # Store configuration
        self.loop_contents = None  # Store loop content
        self.sorted_indices = None  # Store sorted indices
        self.inner_flags = None 
        self.loop_entries = []  # Store extracted loop entries

        self.global_unchanged_vars = []
        self.loop_slices = []

        # Store common variables, unchanged variables, and non-inductive variables of the currenct outer loop
        self.begin_map = {}
        self.end_map = {}
        
        self.common_vars = []
        self.unchanged_vars = []
        self.non_inductive_vars = []

        self.loop_bound_analyzer = LoopBoundAnalyzer()

        self.executor = DynamicExecutorConfigurable()
        self.timeout = False

        # Store stripped ACSL contracts
        self.precondition = None
        self.goal = None

        # Store per-outer-loop records
        self.records = []

        self.llm_config = LLMConfig()
        self.llm = Chatbot(self.llm_config)

        # 使用全局配置的 subdir（如需覆盖可传入 input_subdir）
        resolved_subdir = self.input_subdir_config if self.input_subdir_config else SUBDIR
        safe_subdir = re.sub(r"[^A-Za-z0-9_]+", "_", resolved_subdir)
        goal_prefix = f"{safe_subdir}_{self.file_name}"
        self.goal_file = f"../goal/{goal_prefix}_goal.v"
        self.proof_auto_file = f"../goal/{goal_prefix}_proof_auto.v"
        self.proof_manual_file = f"../goal/{goal_prefix}_proof_manual.v"
        
        self.input_file = f"../src/input/{resolved_subdir}/{self.file_name}.c"
        self.output_file = f"../src/output/{resolved_subdir}/{self.file_name}.c"

        self.unfold_file = f"../src/unfold/{resolved_subdir}/{self.file_name}.c"
        self.outer_file = f"../src/outer/{resolved_subdir}/{self.file_name}.c"
        self.sample_file = f"../src/sample/{resolved_subdir}/{self.file_name}.c"

        # self.iter_file = f"../../src/output/{input_subdir}/{self.file_name}"
        
        # JSON file should be in loop/{subdir}/ directory
        Path(f'loop/{resolved_subdir}').mkdir(parents=True, exist_ok=True)
        self.json_file = f'loop/{resolved_subdir}/{self.file_name}.json'
        self.code = open(self.input_file, "r").read()
        self.sample_files = []

        self.sample_contents = []

        self.loop_bound = None
        
        # Extract function parameters from original input file
        self.function_params = self._extract_function_parameters(self.input_file)
    
    def _detect_input_subdir(self) -> str:
        """
        Detect which subdirectory the input file is in (linear, NLA_lipus, etc.)
        
        Returns:
            Subdirectory name (default: 'linear')
        """
        import os
        script_dir = os.path.dirname(os.path.abspath(__file__))
        
        # 简化为使用全局配置的 subdir
        return SUBDIR

    def _extract_function_parameters(self, input_file_path: str) -> List[str]:
        """
        Extract function parameter names from original C input file.
        Only considers int type parameters.
        
        Args:
            input_file_path: Path to the original input C file
            
        Returns:
            List of function parameter names (only int type)
        """
        # Read the original input file
        try:
            with open(input_file_path, 'r', encoding='utf-8') as f:
                code = f.read()
        except Exception as e:
            print(f"Error reading input file {input_file_path}: {e}")
            return []
        
        # Find the first function definition (with body, not declaration)
        # Match pattern: return_type function_name(param1, param2, ...) {
        # This skips function declarations like "int unknown();"
        func_match = re.search(r'\w+\s+\w+\s*\(([^)]*)\)\s*{', code)
        if not func_match:
            return []
        
        params_str = func_match.group(1).strip()
        if not params_str:
            return []
        
        # Extract parameter names (only int type)
        params = []
        for param in params_str.split(','):
            param = param.strip()
            # Match only int type parameters: 'int x', 'int* x', 'const int x', etc.
            # Pattern: (const)? int (*)? variable_name
            param_match = re.match(r'(?:const\s+)?int\s*(?:\*+\s*)?(\w+)', param)
            if param_match:
                param_name = param_match.group(1)
                params.append(param_name)
        
        return params

    def _generate_full_c_printf_call(self,params: List[str]) -> str:
        """
        将变量名列表格式化成完整的 C 语言 printf 函数调用字符串。

        :param params: 变量名列表 (例如 ['x', 'loop_count', 'sum_val', 'status'])。
        :return: 完整的 C 语言 printf 调用字符串。
        """
        if not params:
            return ""

        # 1. 构建格式字符串部分 (第一个参数)
        format_parts = []
        for var in params:
            # 格式: (var == %d)
            part = f"({var} == %d)"
            format_parts.append(part)
            
        # 连接格式部分，并在末尾添加 '*'
        # format_string = "*".join(format_parts) + "*"
        format_string = "*".join(format_parts)
        
        # 2. 构建变量列表部分 (第二个及以后参数)
        # 变量列表就是 params 本身，用逗号和空格连接
        var_list_string = ", ".join(params)
        
        # 3. 组合成完整的 printf 调用
        # 注意：格式字符串需要用双引号 "" 包裹
        full_call = f'printf("{format_string}\\n", {var_list_string});'
        
        return full_call


    def _get_vars_at_index(self, idx):
        """
        从循环代码中提取变量，不依赖 JSON 文件。
        
        Args:
            idx: 循环索引
            
        Returns:
            printf 调用字符串，用于打印循环变量（只包含变量输出，不包含标记）
        """
        # 如果 records 已初始化，从 records 中获取变量
        if self.records and 0 <= idx < len(self.records):
            record = self.records[idx]
            # 获取循环中的所有变量
            current_vars = record.get('current_vars', [])
            if current_vars:
                return self._generate_full_c_printf_call(current_vars)
        
        # 如果没有 records，尝试从循环内容中提取变量
        if self.loop_contents and 0 <= idx < len(self.loop_contents):
            loop_content = self.loop_contents[idx]
            # 提取变量名（排除关键字）
            vars_found = re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', loop_content)
            keywords = {'for', 'while', 'if', 'else', 'int', 'return', 'break', 'continue', 
                       'printf', 'scanf', 'void', 'char', 'float', 'double', 'long', 'short'}
            vars_found = [v for v in vars_found if v not in keywords and len(v) > 1]
            
            # 去重
            seen = set()
            params = []
            for v in vars_found:
                if v not in seen:
                    seen.add(v)
                    params.append(v)
            
            if params:
                return self._generate_full_c_printf_call(params)
        
        # 如果都失败了，尝试从函数参数中获取变量
        if hasattr(self, 'function_params') and self.function_params:
            return self._generate_full_c_printf_call(self.function_params)
        
        # 如果都失败了，返回一个空的 printf（不包含标记）
        return 'printf("");'
            
       

    def delete_file_if_exists(self, file_path):
        """
        Delete file if it exists.
        :param file_path: File path
        """
        file_path = os.path.join('../VST/test', file_path)
        if os.path.exists(file_path):
           # print(f"File found: {file_path}. Deleting the file.")
            os.remove(file_path)
        #else:
          #  print(f"File not found: {file_path}. No file to delete.")

    # Find the beginning and end of each loop
    def dynamic_loop(self, code):
        """
        在循环中插入 printf 语句来捕获变量值。
        确保采样到：进入循环前、循环迭代中、退出循环后。
        
        标记说明：
        - LoopEntry_{idx}_initial: 进入循环前的状态（在循环条件检查之前）
        - LoopEntry_{idx}: 循环迭代中的状态（每次迭代开始时，在循环体开始处）
        - LoopEntry_{idx}_final: 退出循环后的状态（循环条件为 false 后）
        """
        headers = '''
#include "stdio.h"
#include "stdlib.h"
'''

        # 使用字符串操作而不是字符列表，避免索引问题
        result_code = code

        # Find all for or while loop positions
        loop_pattern = r'\b(for|while)\s*\([^)]*\)\s*\{'
        matches = list(re.finditer(loop_pattern, code))

        # Max iterations to trace per loop (prevents OOM from infinite/very long loops)
        MAX_TRACE_ITERS = 10000

        # 从后往前处理，避免索引偏移问题
        for idx in range(len(matches) - 1, -1, -1):
            match = matches[idx]
            loop_start = match.start()

            # 获取循环变量
            try:
                params = self._get_vars_at_index(idx)
            except Exception as e:
                # 如果获取变量失败，使用默认的 printf
                params = f'printf("LoopEntry_{idx}:\\n");'

            # 1. 在循环开始前（进入循环前）插入 initial 标记和iteration counter
            # 位置：在循环条件检查之前，紧邻循环语句
            insert_str_initial = (
                f'printf("LoopEntry_{idx}_initial:\\n");\n{params}\n'
                f'int _trace_iter_{idx} = 0;\n'
            )
            result_code = result_code[:loop_start] + insert_str_initial + result_code[loop_start:]

            # 重新计算循环开始位置（因为已经插入了内容）
            updated_start = loop_start + len(insert_str_initial)

            # 找到循环体的开始 {
            pos = updated_start
            while pos < len(result_code) and result_code[pos] != '{':
                pos += 1

            if pos < len(result_code):
                # 2. 在循环体开始处（每次迭代开始时）插入迭代标记 + iteration guard
                # 位置：在循环体的第一个 { 之后，循环体代码之前
                pos += 1  # 跳过 {
                insert_str_iter = (
                    f'\nif (++_trace_iter_{idx} > {MAX_TRACE_ITERS}) {{ '
                    f'printf("LoopEntry_{idx}_final:\\n");\n{params}\nexit(0); }}\n'
                    f'printf("LoopEntry_{idx}:\\n");\n{params}\n'
                )
                result_code = result_code[:pos] + insert_str_iter + result_code[pos:]
                
                # 更新位置（跳过插入的内容）
                pos += len(insert_str_iter)
                brace_count = 1
                
                # 找到匹配的 }
                while pos < len(result_code) and brace_count > 0:
                    if result_code[pos] == '{':
                        brace_count += 1
                    elif result_code[pos] == '}':
                        brace_count -= 1
                    pos += 1
                
                # 3. 在循环结束后（退出循环后）插入 final 标记
                # 位置：在循环的 } 之后，紧邻循环结束
                if brace_count == 0:
                    loop_end = pos  # 循环结束后的位置（} 之后）
                    insert_str_final = f'\nprintf("LoopEntry_{idx}_final:\\n");\n{params}\n'
                    result_code = result_code[:loop_end] + insert_str_final + result_code[loop_end:]
        
        return headers + result_code
    
   

    # Find the beginning and end of each loop
    def process_loop(self,code):

        headers = '''
        #include "../../input/verification_stdlib.h"
        #include "../../input/verification_list.h"
        #include "../../input/int_array_def.h"

        /*@ Extern Coq (Result: Assertion) */
        /*@ Extern Coq (Results: Z -> Assertion) */

            '''

        preconditon = '''
        /*@
        Require emp
        Ensure emp
        */
        '''
        codes = code.split('{')
        code = headers + codes[0] + preconditon + '{' + '{'.join(codes[1:])
        


        def determine_inner_loops(loop_info):
            """
            Determine whether each loop is an inner loop.
            Parameters:
                loop_info: list of tuples, each element is (start_pos, end_pos, loop_index)
            Returns:
                list of bool, indicating whether each loop is an inner loop (in loop_info input order)
            """
            inner_flags = [False] * len(loop_info)
            
            
            # Traverse all loop pairs (i, j)
            for j in range(len(loop_info)):
                s_j, e_j, idx_j = loop_info[j]
                for i in range(len(loop_info)):
                    if i == j:
                        continue
                    s_i, e_i, idx_i = loop_info[i]
                    # If loop i completely contains loop j: i starts earlier and ends later
                    if s_i < s_j and e_i > e_j:
                        inner_flags[j] = True
                        break  # As long as it's contained by one outer loop, it can be determined as inner
            
            return inner_flags
        # Split code into single character list
        code_list = list(code)
        
        # Find all for or while loop positions
        loop_pattern = r'\b(for|while)\s*\((.*?)\)\s*{'
        matches = list(re.finditer(loop_pattern, code))
        loop_contents = []
        loop_indices=[]
        
        # Process each loop
        for idx, match in enumerate(matches):
            # Loop start position
            loop_start = match.start()    

            at_index = loop_start

            loop_head= code_list[at_index] 
            
            code_list[at_index-1] = f'\n {code_list[at_index -1 ]}/*@ Print user assertion at number LoopEntry_{idx}*/ \n'
            code_list[at_index] = f'/*{idx}*/ \n {code_list[at_index]}'

            
            # Find the first } corresponding to { after the loop
            brace_count = 0
            loop_end = match.end()
            end_index = loop_end
            while brace_count >= 0:
                if code_list[end_index] == '{':
                    brace_count += 1
                elif code_list[end_index] == '}':
                    brace_count -= 1
                end_index += 1

            # Push (at_index,end_index, idx) into list
            loop_indices.append((at_index,end_index, idx))
          

            # Extract loop content
            loop_content = loop_head + ''.join(code_list[loop_start +1:end_index])

           
            # Modify comments to ACSL format
            assert_pattern = r'/\*@\s*(.*?)\s*\*/'
    
            # Replace with /*@ assert xxxxxx ;*/
            loop_content = re.sub(assert_pattern, r'/*@ assert \1; */', loop_content)

            loop_content = loop_content.replace('=>','==>')
            
            
            # Print loop content
            # print(f"LoopContent_{idx}:\n{loop_content}\n")
            loop_contents.append(loop_content)
        
        # print(loop_indices)

        inner_flags = determine_inner_loops(loop_indices)

        
        # Sort by end_index from small to large
        sorted_indices = [x[2] for x in sorted(loop_indices, key=lambda x: x[1])]


        code = ''.join(code_list)
        unfolded_code = self._unfold(code)
        
            
        # Rejoin character list into string
        return unfolded_code,loop_contents,sorted_indices,inner_flags
    
    def extract_common_vars(self, loop_entry_text):
        """
        从 LoopEntry_X: 格式的字符串中提取 common_vars
        :param loop_entry_text: 例如 "LoopEntry_0:\n(z == 0) * (y == 0) * (x == 1)"
        :return: 变量名列表，例如 ['z', 'y', 'x']
        """
        # 使用正则表达式匹配变量名
        # 匹配形如 (var == value) 中的 var
        var_pattern = r'\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*=='
        
        # 提取所有匹配的变量名
        matches = re.findall(var_pattern, loop_entry_text)
        
        # 去重并保持顺序
        common_vars = []
        seen = set()
        for var in matches:
            if var not in seen:
                common_vars.append(var)
                seen.add(var)
        
        return common_vars

    def get_loop_content(self,code,ridx):

        # Find all for or while loop positions
        code_list = list(code)
        loop_pattern = r'\b(for|while)\s*\((.*?)\)\s*{'
        loop_content = None
        matches = list(re.finditer(loop_pattern, code))
        
        # Process each loop
        for idx, match in enumerate(matches):
            if idx == ridx:
                # Loop start position
                loop_start = match.start()    

                at_index = loop_start

                loop_head = code_list[at_index] 
            
                # Find the first } corresponding to { after the loop
                brace_count = 0
                loop_end = match.end()
                end_index = loop_end
                while brace_count >= 0:
                    if code_list[end_index] == '{':
                        brace_count += 1
                    elif code_list[end_index] == '}':
                        brace_count -= 1
                    end_index += 1

                # Extract loop content
                loop_content = loop_head + ''.join(code_list[loop_start +1:end_index])
                break

        return loop_content

    def _strip_contracts(self, code: str) -> str:
        """Remove ONLY ACSL requires/assert and store into self.precondition/self.goal.
        Targets patterns exactly:
          /*@ requires <phi> */
          /*@ assert <psi> */
        Case-sensitive; does not touch other ACSL annotations.
        Returns code with those specific blocks removed.
        """
        # Extract exactly 'requires' (lowercase, case-sensitive)
        req_pat = re.compile(r"/\*@\s*requires\b([\s\S]*?)\*/")
        m = req_pat.search(code)
        if m and self.precondition is None:
            self.precondition = m.group(1).replace(';','').replace('==>','=>').strip()
        code = req_pat.sub("", code)

        # Extract exactly 'assert' (lowercase, case-sensitive)
        asrt_pat = re.compile(r"/\*@\s*assert\b([\s\S]*?)\*/")
        m2 = asrt_pat.search(code)
        if m2 and self.goal is None:
            self.goal = m2.group(1).strip().replace(';','').replace('==>','=>').strip()
        code = asrt_pat.sub("", code)

        return code
    
    def replace_unknown_or_empty(self, s: str) -> str:
        """
        处理循环体中的 unknown() 函数：
        - 如果不包含 unknown()：直接返回原字符串
        - 如果包含 unknown()：每个 unknown() 随机替换为 0 或 1
        """
        # 检查是否包含 unknown() 函数
        if not re.search(r'unknown\d*\(\)', s):
            # 不包含 unknown()，直接返回原字符串
            return s
        
        # 将每个 unknown() 随机替换为 0 或 1
        def random_replace(match):
            return str(random.choice([0, 1]))
        
        return re.sub(r'unknown\d*\(\)', random_replace, s)

    # def _sample_values_with_llm(self, entry_cond, precondition: str):
    #     """Use LLM to sample concrete int values for params satisfying the precondition.
    #     Returns a dict name->int or empty dict on failure.
    #     """
    #     if not entry_cond:
    #         return {}

    #     if precondition:
    #         prompt = (
    #             "You are given a list of integer variables and a precondition. "
    #             "Produce ONE satisfying assignment as strict JSON object mapping variable to random small integer.\n"
    #             "Only remove var@pre to random integer under precondition.\n"
    #             f"vars: {entry_cond}\n"
    #             f"precondition: {precondition}\n"
    #             "Constraints: only output JSON like {\"x\":0,\"y\":1}."
    #         )
    #     else:
    #         prompt = (
    #             "You are given a list of integer variables. "
    #             "Produce ONE satisfying assignment as strict JSON object mapping variable to random samll integer.\n"
    #             "Only remove var@pre to random integer.\n"
    #             f"vars: {entry_cond}\n"
    #             "Constraints: only output JSON like {\"x\":0,\"y\":1}."
    #         )
    #     try:
    #         raw = self.llm.chat(prompt).strip()
    #         # strip code fences if any
    #         if raw.startswith('```'):
    #             raw = raw.strip('`')
    #         # extract first JSON object
    #         start = raw.find('{')
    #         end = raw.rfind('}')
    #         if start != -1 and end != -1 and end > start:
    #             raw = raw[start:end+1]
    #         data = json.loads(raw)
    #         if isinstance(data, dict):
    #             # keep only requested params and ints
    #             sampled = {}
    #             for p in params:
    #                 if p in data and isinstance(data[p], int):
    #                     sampled[p] = data[p]
    #             return sampled
    #     except Exception:
    #         return {}
    #     return {}



    def save_unique_random_samples(self, loop_body: str, entry_cond: str, base_path: str, func_name: str = "foo",idx = 0):
        """
        生成三个不同的随机采样文件，确保每次采样都不同
        :param loop_body: 循环体内容
        :param entry_cond: 入口条件
        :param base_path: 基础文件路径（不包含扩展名）
        :param func_name: 函数名
        """

        # 生成三个不同的文件路径
        sample_1_file = '.'.join(base_path.split('.')[:-1]) + f'_{idx}_1.c'
        sample_2_file = '.'.join(base_path.split('.')[:-1]) + f'_{idx}_2.c'
        sample_3_file = '.'.join(base_path.split('.')[:-1]) + f'_{idx}_3.c'
        
        # 用于存储已生成的采样值，避免重复
        used_samples = set()
        
        # 提取变量名
        vars_found = re.findall(r'\(\s*([A-Za-z_]\w*)\s*==', entry_cond)
        seen, params = set(), []
        for v in vars_found:
            if v not in seen:
                seen.add(v)
                params.append(v)
        
        # 组装形参列表
        param_list = ", ".join([f"int {v}" for v in params]) if params else ""
        
        # 处理循环体
        loop_body_processed = re.sub(r'\bfor\s*\(', 'if (', loop_body)
        loop_body_processed = re.sub(r'\bwhile\s*\(', 'if (', loop_body_processed)
        loop_body_indented = "\n".join(["    " + line if line.strip() else line
                                        for line in loop_body_processed.splitlines()])

        # 生成三个不同的采样
        require_cond_list = self.executor.substitute_pre_values(self.precondition,entry_cond,3)

        for i, out_path in enumerate([sample_1_file, sample_2_file, sample_3_file], 1):

            
          
            # 如果有前置条件，生成不同的采样值
            if '@pre' in entry_cond:
                

                # max_attempts = 10  # 最多尝试10次避免无限循环
                # attempt = 0
                # while attempt < max_attempts:
                #     sampled = self._sample_values_with_llm(entry_cond, self.precondition)
                #     print("sampled")
                #     print(sampled)
                #     if sampled:
                #         # 创建采样的字符串表示用于去重
                #         sample_key = tuple(sorted(sampled.items()))
                #         if sample_key not in used_samples:
                #             used_samples.add(sample_key)
                #             # 替换变量值
                #             for k, v in sampled.items():
                #                 require_cond = re.sub(rf"\b{k}@pre\b", str(v), require_cond)
                #             break
                #     attempt += 1
            
                
                # 如果无法生成不同的采样，至少确保每个文件有不同的函数名
                func_name_unique = f"{func_name}_{i}"
            else:
                func_name_unique = f"{func_name}_{i}"
            
            # 随机确定展开次数 (5-10次)
            num_unrolls = random.randint(5, 10)
            
            # 动态生成展开代码
            unroll_code = ""
            for _ in range(num_unrolls):
                unroll_code += f"    /*@ Print user assertion at number LoopEntry_{idx}*/\n"
                unroll_code += f"    {self.replace_unknown_or_empty(loop_body_indented)}\n"
            # 最后一个采样点
            unroll_code += f"    /*@ Print user assertion at number LoopEntry_{idx}*/\n"
            
            # 生成代码
            code = f"""
    #include "../../input/verification_stdlib.h"
    #include "../../input/verification_list.h"
    #include "../../input/int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

    void {func_name_unique}({param_list}) /*@
    Require {require_cond_list[i-1]}
    Ensure emp
    */
    {{

{unroll_code}
    }}
    """
            
            # 确保目录存在并写文件
            dirpath = os.path.dirname(out_path)
            if dirpath:
                os.makedirs(dirpath, exist_ok=True)
            with open(out_path, "w", encoding="utf-8") as f:
                f.write(code)
                self.sample_files.append(f'../{out_path}')
            # print(self.sample_files)
            print(f"generate sample file {i}: {out_path}")

    def save_outer_loop(self,loop_body: str, entry_cond: str, out_path: str, idx: int = 0, func_name: str = "foo"):

        # 1) 优先从 entry_cond 提取变量名；若为空则回退到 loop_body/函数参数，
        #    避免生成无参 foo() 但函数体使用自由变量导致 undeclared identifier。
        vars_found = re.findall(r'\(\s*([A-Za-z_]\w*)\s*==', entry_cond or "")
        seen, params = set(), []
        for v in vars_found:
            if v not in seen:
                seen.add(v)
                params.append(v)

        if not params:
            body_vars = re.findall(r'\b([A-Za-z_]\w*)\b', loop_body or "")
            keywords = {
                'for', 'while', 'if', 'else', 'int', 'return', 'break', 'continue',
                'printf', 'scanf', 'void', 'char', 'float', 'double', 'long', 'short'
            }
            for v in body_vars:
                if v in keywords:
                    continue
                if v not in seen:
                    seen.add(v)
                    params.append(v)

        if not params and getattr(self, 'function_params', None):
            for v in self.function_params:
                if v not in seen:
                    seen.add(v)
                    params.append(v)

        # 2) 组装形参列表：int x, int y
        param_list = ", ".join([f"int {v}" for v in params]) if params else ""
        # 3) 生成源代码（最小头文件 + 函数定义+循环体）
        #    将循环体按缩进嵌入函数内
        # 将 for/while 循环头替换为 if 语句头
        loop_body = re.sub(r'\bfor\s*\(', 'if (', loop_body)
        loop_body = re.sub(r'\bwhile\s*\(', 'if (', loop_body)

        loop_body_indented = "\n".join(["    " + line if line.strip() else line
                                        for line in loop_body.splitlines()])

        loop_body_indented = re.sub(r'unknown\d*\(\)','1', loop_body_indented)

        code = f"""
    #include "../../input/verification_stdlib.h"
    #include "../../input/verification_list.h"
    #include "../../input/int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

    void {func_name}({param_list}) /*@
    Require emp
    Ensure emp
    */
    {{

    /*@ Print user assertion at number LoopEntry_begin*/ 
    {loop_body_indented}
    /*@ Print user assertion at number LoopEntry_end*/ 

    }}
    """
        # 4) 确保目录存在并写文件
        out_path = '.'.join(out_path.split('.')[:-1]) + f'_{idx}.c'

        dirpath = os.path.dirname(out_path)
        if dirpath:
            os.makedirs(dirpath, exist_ok=True)
            
        
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(code)

    def dynamic_loop_file(self,input_file_path,output_file_path):
        # Read original file content
        if input_file_path != None:
            with open(input_file_path, 'r', encoding='utf-8') as infile:
                code = infile.read()
        else:
            code = self.code
        

        code = self.dynamic_loop(code)
        print(code)
        return code

    
    def _replace_unknown_for_symexec(self, code: str) -> str:
        """
        Replace unknown() calls for symexec/Frama-C compatibility:
        - while(unknown()) -> while(1)
        - if(unknown()) -> if(1)
        - Remove 'int unknown();' declarations
        """
        result = code
        # Replace while(unknown()) with while(1)
        result = re.sub(r'while\s*\(\s*unknown\d*\s*\(\s*\)\s*\)', 'while(1)', result)
        # Replace if(unknown()) with if(1)
        result = re.sub(r'if\s*\(\s*unknown\d*\s*\(\s*\)\s*\)', 'if(1)', result)
        # Remove unknown() function declarations
        result = re.sub(r'int\s+unknown\d*\s*\(\s*\)\s*;?\s*\n?', '', result)
        return result

    def process_loop_file(self,input_file_path,output_file_path):
        # Read original file content
        if input_file_path != None:
            with open(input_file_path, 'r', encoding='utf-8') as infile:
                code = infile.read()
        else:
            code = self.code
        
        # Strip ACSL contracts before processing
        code = self._strip_contracts(code)

        # Replace unknown() for symexec compatibility
        code = self._replace_unknown_for_symexec(code)

        # Call process_code to process code

        processed_code = self.process_loop(code)[0]
        loop_contents = self.process_loop(code)[1]
        sorted_indices = self.process_loop(code)[2]
        inner_flags = self.process_loop(code)[3]
        

        # Ensure output directory exists
        output_dir = os.path.dirname(output_file_path)
        if output_dir:
            os.makedirs(output_dir, exist_ok=True)
        
        # Write processed code to new file
        with open(output_file_path, 'w', encoding='utf-8') as outfile:
            outfile.write(processed_code)

        return loop_contents,sorted_indices,inner_flags

    def _extract_rhs_map(self,block: str) -> Dict[str, str]:
        """
        extract (var == RHS) or var == RHS assignments
        :param text: Input text
        :return {var: RHS}。
        """
        assignments: Dict[str, str] = {}

        # 直接在括号内提取 LHS == RHS，避免把乘法符号 '*' 误当分隔符
        # 形式示例： (x == x@pre + y@pre)
        # 捕获到右括号为止，RHS 内允许空格和运算符
        for m in re.finditer(r"\(\s*([^()\s]+)\s*==\s*([^)]*?)\s*\)", block):
            lhs = m.group(1).strip()
            rhs = m.group(2).strip()

            # 忽略左值含有 '@pre' 的赋值
            if '@pre' in lhs:
                continue

            assignments[lhs] = rhs

        # 兼容无括号但换行或以空格分隔的写法，例如：x == x@pre
        # 逐行尝试匹配
        if not assignments:
            for line in block.splitlines():
                line_stripped = line.strip().strip('()')
                if not line_stripped:
                    continue
                m = re.match(r"([^()\s]+)\s*==\s*(.+)$", line_stripped)
                if not m:
                    continue
                lhs = m.group(1).strip()
                rhs = m.group(2).strip()
                if '@pre' in lhs:
                    continue
                assignments[lhs] = rhs

        return assignments

    def _extract_precondition_values(self, precondition: str) -> Dict[str, str]:
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
        # 先标准化分隔符
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

    def _build_static_precondition_from_code(self, code: str, loop_content: str) -> Optional[str]:
        """
        Build a fallback precondition from code text when no explicit requires exists.
        Strategy:
        - Keep the last assignment to each variable before loop entry.
        - Add parameter identity facts (p == p@pre).
        """
        if not code or not loop_content:
            return None

        loop_pos = code.find(loop_content)
        if loop_pos < 0:
            return None
        prefix = code[:loop_pos]

        last_assign: Dict[str, str] = {}
        for lhs, rhs in re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*=\s*([^;{}]+);', prefix):
            last_assign[lhs.strip()] = rhs.strip()

        clauses: List[str] = []
        for var, expr in sorted(last_assign.items()):
            clauses.append(f"({var} == {expr})")
        for param in sorted(self.function_params):
            clauses.append(f"({param} == {param}@pre)")

        if not clauses:
            return None
        return " && ".join(clauses)

    def _fix_at_pre_on_non_params(self, code: str) -> str:
        """
        修复代码中错误使用 \\at(..., Pre) 在非参数变量上的问题。

        规则：
        - 如果 \\at(var, Pre) 中的 var 不是函数参数
        - 就从 precondition 中找到该变量的初始值并替换

        Args:
            code: 输入代码字符串

        Returns:
            修复后的代码字符串
        """
        if not self.precondition:
            return code

        # 提取 precondition 中的变量值
        pre_values = self._extract_precondition_values(self.precondition)

        # 获取函数参数集合
        param_set = set(self.function_params)

        # 查找所有 \\at(var, Pre) 模式
        # 匹配 \at(var, Pre) 格式
        pattern = r'\\at\((\w+),\s*Pre\)'

        def replacement(match):
            var_name = match.group(1)

            # 如果是函数参数，保留原样
            if var_name in param_set:
                return match.group(0)

            # 如果不是函数参数，但 precondition 中有定义，替换为对应的值
            if var_name in pre_values:
                return pre_values[var_name]

            # 如果都不是，保留原样（可能是误用但不处理）
            return match.group(0)

        fixed_code = re.sub(pattern, replacement, code)

        return fixed_code

    def get_unchaned_non_inductive_vars(self, text) -> Tuple[List[str], List[str]]:
        """
        Extract LoopEntry_X conditions from text using regular expressions.
        :param text: Input text
        :return: List of extracted unchanged vars and non inductive vars
        """
    
        # 1. 提取 begin 和 end 块的内容
        begin_match = re.search(r'LoopEntry_begin:\s*([\s\S]*?)LoopEntry_end:', text)
        end_match = re.search(r'LoopEntry_end:\s*([\s\S]*)', text)

        if not begin_match or not end_match:
            print("错误: 输入字符串格式错误，未能找到 LoopEntry_begin 或 LoopEntry_end 块。")
            return [], [], []

        begin_block = begin_match.group(1).strip()
        end_block = end_match.group(1).strip()
        
        # 2. 解析两个块中的所有赋值：{var: RHS}
        begin_assignments = self._extract_rhs_map(begin_block)
        end_assignments = self._extract_rhs_map(end_block)
        
        unchanged_vars = []
        non_inductive_vars = []
        
        # 3. 确定需要比较的公共变量集
        # 必须同时存在于 begin 和 end 中才有比较的意义
        common_vars: Set[str] = begin_assignments.keys() & end_assignments.keys()

        # 4. 遍历公共变量并进行 RHS 比较
        for var in common_vars:
            begin_rhs = begin_assignments[var]
            end_rhs = end_assignments[var]
            
            # 规范化：去除所有空格，以确保精确匹配的可靠性
            begin_rhs_normalized = begin_rhs.replace(" ", "")
            end_rhs_normalized = end_rhs.replace(" ", "")
            
            # --- 规则 1: Unchanged (不变的变量) ---
            if begin_rhs_normalized == end_rhs_normalized:
                # 右值精确相等
                unchanged_vars.append(var)
                continue
                
            # --- 规则 2: Non-Inductive (非归纳/已改变的变量) ---
            # 检查：begin RHS 不为 end RHS 的子串
            # 也就是说，end RHS 必须与 begin RHS 完全不同，且不包含 begin RHS
            
            # 判断：begin RHS 是否是 end RHS 的子串
            is_substring = begin_rhs_normalized in end_rhs_normalized
            
            if not is_substring:
                non_inductive_vars.append(var)

                
        return list(common_vars), unchanged_vars, non_inductive_vars

    
    



       

    def get_loop_entries(self, text):
        """
        Extract LoopEntry_X conditions from text using regular expressions.
        :param text: Input text
        :return: List of extracted loop entries
        """
       
        pattern = r"LoopEntry_(\d+):\s*\n([^\n]*)"
        matches = re.findall(pattern, text)

        self.loop_entries = []
        for match in matches:
            loop_id = int(match[0])  # Extract number
            condition = match[1].strip()  # Extract condition and remove leading/trailing whitespace
            self.loop_entries.append((loop_id, condition))

        # Sort by loop_id
        self.loop_entries.sort(key=lambda x: x[0])
        return self.loop_entries

    def get_loop_begin_end_maps(self, text):
        """
        提取 LoopEntry_begin 和 LoopEntry_end 的字符串
        :param text: 输入文本
        :return: 包含 begin 和 end 字符串的字典
        """
        # 提取 LoopEntry_begin 的条件
        begin_pattern = r"LoopEntry_begin:\s*\n([^\n]*)"
        begin_matches = re.findall(begin_pattern, text)
        
        # 提取 LoopEntry_end 的条件  
        end_pattern = r"LoopEntry_end:\s*\n([^\n]*)"
        end_matches = re.findall(end_pattern, text)
        
        # 获取第一个匹配的条件（假设只有一个）
        begin_condition = begin_matches[0].strip() if begin_matches else ""
        end_condition = end_matches[0].strip() if end_matches else ""
        
        # 将 @pre 替换为 @last
        begin_condition = begin_condition.replace('@pre', '@last')
        end_condition = end_condition.replace('@pre', '@last')
            
        return {
            'begin': begin_condition,
            'end': end_condition
        }

    def write_loops_to_json(self):
        """
        Write loop content and entries to JSON file.
        """

        if len(self.loop_contents) != len(self.loop_entries):

            diff = abs(len(self.loop_contents) - len(self.loop_entries))

            for i in range(diff):
                id = len(self.loop_entries) + i
                print(id)
                self.loop_entries.append((id,''))

        data = []
        for entry, content in zip(self.loop_entries, self.loop_contents):
            loop_id, condition = entry
            data.append({
                "loop_id": loop_id,
                "condition": condition,
                "content": content,
            })

        # Ensure directory exists
        json_dir = os.path.dirname(self.json_file)
        if json_dir:
            os.makedirs(json_dir, exist_ok=True)
        
        with open(self.json_file, 'w') as f:
            json.dump(data, f, indent=4)

        print(f"Successfully generated {self.json_file}")



    def run_symexec(self, input_file, loop_idx: Optional[int] = None):
        """
        Run symexec command and process output.
        
        Args:
            input_file: Input file path
            loop_idx: Optional loop index for filtering variables in sample parsing
        """
        command = [
            "build/symexec",
            f"--goal-file={self.goal_file}",
            f"--proof-auto-file={self.proof_auto_file}",
            f"--proof-manual-file={self.proof_manual_file}",
            f"--input-file={input_file}"
        ]

        try:
            result = subprocess.run(
                command,
                cwd='../VST/test',
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )

            

            if result.stderr:
                print(result.stderr.strip())
                if input_file == f'../{self.unfold_file}':
                    print('update loop file entries')
                    self.get_loop_entries(result.stderr)
                    self.write_loops_to_json()
                    self.global_unchanged_vars = self.extract_common_vars(result.stderr)
                #elif input_file == f'../{self.outer_file}':
                elif 'outer' in input_file:
                    has_begin_end = ("LoopEntry_begin:" in result.stderr) and ("LoopEntry_end:" in result.stderr)
                    if has_begin_end:
                        begin_end_maps = self.get_loop_begin_end_maps(result.stderr)
                        self.begin_map = begin_end_maps['begin']
                        self.end_map = begin_end_maps['end']
                        common_vars, unchanged_vars, non_inductive_vars  = self.get_unchaned_non_inductive_vars(result.stderr)
                        self.common_vars = common_vars
                        self.unchanged_vars = unchanged_vars
                        self.non_inductive_vars = non_inductive_vars
                    else:
                        # 外层路径若仅返回编译/类型错误，不再触发 begin/end 解析报错噪音
                        self.begin_map = ''
                        self.end_map = ''
                        self.common_vars = []
                        self.unchanged_vars = []
                        self.non_inductive_vars = []
                else:
                    print('start sample static')
                    print(result.stderr)
                    
                    # Get allowed variables: current_vars U param_pre_vars
                    allowed_vars = None
                    if loop_idx is not None and loop_idx < len(self.records):
                        record = self.records[loop_idx]
                        current_vars = set(record.get('current_vars', []))
                        param_pre_vars = set(record.get('param_pre_vars', []))
                        allowed_vars = current_vars | param_pre_vars
                        print(f"Allowed vars for loop {loop_idx}: {allowed_vars}")
                    
                    sample_content = parse_samples(result.stderr, allowed_vars)
                    self.sample_contents.append(sample_content)
                    print(f"sample_contents: {self.sample_contents}")
                    print('end sample static')

              
                

        except Exception as e:
            print(f"An error occurred: {e}")

    def unfold(self):
        # Process input file
        self.loop_contents, self.sorted_indices,self.inner_flags = self.process_loop_file(self.input_file,self.unfold_file)
        
        
        for idx in self.sorted_indices:
            print(f"Loop {idx} : {'Inner' if self.inner_flags[idx] else 'Outer'}")

        print(f"inner_flags: {self.inner_flags}")
        print(f"Sorted indices: {self.sorted_indices}")

    def dynamic(self, num_samples: int = None):
        """
        执行动态采样，多次运行程序收集数据点。

        每组采样对应一次独立的完整程序执行，采样结果按独立执行组存储。
        这样验证不变量时可以用每组独立的 traces 来验证。

        Args:
            num_samples: 采样次数（每次是一个独立的完整执行）
                        如果为 None，则使用配置文件中的 DYNAMIC_SAMPLING_CONFIG['num_groups']
        """
        from config import DYNAMIC_SAMPLING_CONFIG
        import logging
        logger = logging.getLogger('SE2INV')

        # 使用配置文件中的采样组数，如果没有指定
        if num_samples is None:
            num_samples = DYNAMIC_SAMPLING_CONFIG.get('num_groups', 10)

        code = self.dynamic_loop_file(self.input_file, self.unfold_file)

        # 清空之前的采样内容，重新按独立执行组存储
        self.sample_contents = []

        logger.info(f"Dynamic sampling: {num_samples} independent execution groups...")

        timeout_count = 0
        error_count = 0
        for i in range(num_samples):
            try:
                main, param_values = self.executor.generate_random_test_case(code)

                if param_values:
                    param_str = ', '.join([f"{k}={v}" for k, v in param_values.items()])
                    logger.info(f"Execution {i+1}/{num_samples}: params: {param_str}")

                result, timeout = self.executor.execute_c_code(main)
                self.timeout = timeout

                if timeout:
                    timeout_count += 1
                    logger.info(f"Execution {i+1}/{num_samples}: timeout, skipping")
                    continue

                sample_content = parse_samples(result, None)

                if sample_content:
                    sample_content['_params'] = param_values  # Store param_values

                    # 对每个 run 的 traces 进行截断：保留前 m 个和后 m 个
                    sample_content = self._truncate_traces_per_run(sample_content)

                    self.sample_contents.append(sample_content)
                    logger.info(f"Execution {i+1}/{num_samples}: collected traces for {list([k for k in sample_content.keys() if k != '_params'])}")
                else:
                    logger.info(f"Execution {i+1}/{num_samples}: no traces collected")
            except Exception as e:
                error_count += 1
                logger.warning(f"Execution {i+1}/{num_samples}: error: {e}")
                continue

        logger.info(f"Dynamic sampling completed: {len(self.sample_contents)} groups "
                     f"({timeout_count} timeouts, {error_count} errors)")
        
        # 验证每个循环都有足够的 run 和 traces
        self._validate_runs_and_traces_per_loop()

    # def unfold_execute(self):
    #     """
    #     Run unfold process for loop.
    #     """
    #     unfold_file = f'../{self.unfold_file}'
    #     self.run_symexec(unfold_file)

    def sample_execute(self, loop_idx: Optional[int] = None):
        """
        Run sample process for loop.
        
        Args:
            loop_idx: Optional loop index for filtering variables in sample parsing
        """
        for i in range(len(self.sample_files)):
            sample_file = self.sample_files[i]
            self.run_symexec(sample_file, loop_idx)
    
    def outer_execute(self,idx: int = 0):
        """
        Run outer process for loop.
        """
        outer_file = '.'.join(self.outer_file.split('.')[:-1]) + f'_{idx}.c'
        outer_file = f'../{outer_file}'
        self.run_symexec(outer_file)

    def unfold_execute(self):

        # Check and delete old files
        for file_path in [self.goal_file, self.proof_auto_file, self.proof_manual_file]:
            self.delete_file_if_exists(file_path)

        unfold_file = f'../{self.unfold_file}'
        # Run symexec command
        self.run_symexec(unfold_file)
        
        # 将 begin_map 合并到 records 的 pre_condition 中
        self._merge_begin_map_to_pre_condition()

    
    def update_loop_content(self,code,new_loop_content,ridx):
        # Split code into single character list

        code_list = list(code)
        
        # Find all for or while loop positions
        loop_pattern = r'\b(for|while)\s*\((.*?)\)\s*{'
        matches = list(re.finditer(loop_pattern, code))
       
        # Process each loop
        for idx, match in enumerate(matches):
           
            # Loop start position
            if idx == ridx:

                loop_start = match.start()  
                 
                at_index = -1  # Default value, return -1 if '@' not found
                for i in range(loop_start - 1, -1, -1):  # Start from loop_start - 1, traverse backwards
                    if code_list[i] == '@':
                        at_index = i
                        break  # Found first '@', break loop

                at_index = at_index -2

                # Find the first } corresponding to { after the loop
                brace_count = 0
                loop_end = match.end()
                end_index = loop_end
                while brace_count >= 0:
                    if code_list[end_index] == '{':
                        brace_count += 1
                    elif code_list[end_index] == '}':
                        brace_count -= 1
                    end_index += 1
                


        # Replace loop content
        updated_code = (
            ''.join(code_list[:at_index]) +  # Part before loop
            new_loop_content +                   # Replaced loop content
            ''.join(code_list[end_index:])   # Part after loop
        )
            
        # Rejoin character list into string
        return updated_code

    def _merge_begin_map_to_pre_condition(self):
        """
        Persist begin_map into loop records.
        """
        if not hasattr(self, 'begin_map') or not self.begin_map:
            return
        
        begin_condition = self.begin_map
        
        for record in self.records:
            record['begin_map'] = begin_condition
            print(f"Updated begin_map for loop {record.get('loop_idx', '?')}: {begin_condition}")

    def _enrich_records_with_symexec_begin_map(self):
        """
        Populate pre_condition/begin_map from symbolic execution.
        - pre_condition: first reach of loop entry (LoopEntry_<idx>)
        - begin_map: LoopEntry_begin from outer symexec path
        """
        try:
            self.unfold_execute()
            entry_map = {loop_id: cond for loop_id, cond in self.loop_entries}
            record_by_idx = {record.get('loop_idx'): record for record in self.records}
            for idx in self.sorted_indices:
                entry_cond = entry_map.get(idx, '')
                loop_content = self.loop_contents[idx]
                if idx in record_by_idx and entry_cond:
                    record_by_idx[idx]['pre_condition'] = entry_cond
                self.save_outer_loop(loop_content, entry_cond, self.outer_file, idx=idx)
                self.outer_execute(idx)
                if idx in record_by_idx and self.begin_map:
                    record_by_idx[idx]['begin_map'] = self.begin_map
                if idx in record_by_idx and self.end_map:
                    record_by_idx[idx]['end_map'] = self.end_map
                if idx in record_by_idx:
                    record_by_idx[idx]['transition_relation'] = self._build_nl_transition_relation(
                        record_by_idx[idx].get('begin_map', ''),
                        record_by_idx[idx].get('end_map', ''),
                    )
        except Exception as e:
            print(f"Warning: symexec-based precondition enrichment failed: {e}")

    def _to_conjuncts(self, expr: str) -> List[str]:
        if not expr:
            return []
        text = expr.replace('*', '&&')
        return [x.strip().strip('()') for x in text.split('&&') if x.strip()]

    def _extract_eq_map(self, expr: str) -> Dict[str, str]:
        out: Dict[str, str] = {}
        for c in self._to_conjuncts(expr):
            m = re.match(r'^([A-Za-z_]\w*(?:@(?:pre|last))?)\s*==\s*(.+)$', c)
            if m:
                out[m.group(1).strip()] = m.group(2).strip()
        return out

    def _build_nl_transition_relation(self, begin_expr: str, end_expr: str) -> str:
        """
        Build natural-language one-step transition summary from begin/end maps.
        """
        if not begin_expr or not end_expr:
            return ""
        bmap = self._extract_eq_map(begin_expr)
        emap = self._extract_eq_map(end_expr)
        end_conj = self._to_conjuncts(end_expr)
        guard_parts = [c for c in end_conj if not re.search(r'==', c)]
        guard_text = "; ".join(guard_parts) if guard_parts else "no explicit guard captured"

        vars_all = sorted(set(bmap.keys()) | set(emap.keys()))
        changed: List[str] = []
        unchanged: List[str] = []
        for v in vars_all:
            b = bmap.get(v, "?")
            e = emap.get(v, "?")
            if b == e:
                unchanged.append(f"{v} keeps {e}")
            else:
                changed.append(f"{v}: {b} -> {e}")

        parts: List[str] = [f"One-step transition under loop guard ({guard_text})."]
        if changed:
            parts.append("Changed: " + "; ".join(changed) + ".")
        if unchanged:
            parts.append("Unchanged: " + "; ".join(unchanged) + ".")
        return " ".join(parts)

  
#    def unfold(self, code) -> str:
#         """
#         读取 self.output_file，对其中的所有 for/while 循环头改写为 if，并将改写后的代码
#         写入 self.unfold_file 对应路径。返回写入文件的路径。
#         仅改写循环头（for(init; cond; inc){ -> if(cond){，while(cond){ -> if(cond){），其余代码保持不变。
#         """
#         # 读取 output 文件
#         try:
#             with open(self.output_file, 'r', encoding='utf-8') as f:
#                 code = f.read()
#         except Exception as e:
#             raise RuntimeError(f"读取输出文件失败: {self.output_file}, {e}")

#         # 更稳健：仅替换头部关键字与条件，不要求后紧跟 “{”，兼容注释/空白等
#         loop_head_pat = re.compile(r"\b(for|while)\s*\(([^)]*)\)")

#         def _replace_head(m: re.Match) -> str:
#             kind = m.group(1)
#             inside = m.group(2)
#             if kind == 'while':
#                 cond = inside.strip() if inside.strip() else '1'
#             else:
#                 parts = [p.strip() for p in inside.split(';')]
#                 cond = parts[1] if len(parts) >= 2 and parts[1] else '1'
#             return f"if ({cond})"

#         unfolded_code = loop_head_pat.sub(_replace_head, code)
#         unfolded_code = unfolded_code.replace("/*@ Inv emp */","")

#         # 确保目录存在
#         out_dir = os.path.dirname(self.unfold_file)
#         if out_dir:
#             os.makedirs(out_dir, exist_ok=True)
#         # 写入文件
#         with open(self.unfold_file, 'w', encoding='utf-8') as f:
#             f.write(unfolded_code)

#         print(f"Successfully generated {self.unfold_file}")

#         return self.unfold_file 

    
    def _unfold(self, code) -> str:
        """
        仅改写循环头（for(init; cond; inc){ -> if(cond){，while(cond){ -> if(cond){），其余代码保持不变。
        """

        # 更稳健：仅替换头部关键字与条件，不要求后紧跟 “{”，兼容注释/空白等
        loop_head_pat = re.compile(r"\b(for|while)\s*\(([^)]*)\)")

        def _replace_head(m: re.Match) -> str:
            kind = m.group(1)
            inside = m.group(2)
            if kind == 'while':
                cond = inside.strip() if inside.strip() else '1'
            else:
                parts = [p.strip() for p in inside.split(';')]
                cond = parts[1] if len(parts) >= 2 and parts[1] else '1'
            return f"if ({cond})"

        unfolded_code = loop_head_pat.sub(_replace_head, code)

        return unfolded_code

        
    def intersect(self,list1,list2):
        return list(set(list1) & set(list2))

    def issubset(self,list1,list2):
        return set(list1).issubset(set(list2))
    
    def _truncate_traces_per_run(self, sample_content: Dict) -> Dict:
        """
        对每个 run 的 traces 进行截断，保留前 m 个和后 m 个 traces。
        确保保留 initial 和 final 状态（如果存在）。
        
        配置由 DYNAMIC_SAMPLING_CONFIG['keep_traces_per_run'] 控制。
        """
        from config import DYNAMIC_SAMPLING_CONFIG
        from collections import defaultdict
        
        m = DYNAMIC_SAMPLING_CONFIG.get('keep_traces_per_run', 3)
        truncated_content = {}
        
        for loop_idx_str, traces in sample_content.items():
            if loop_idx_str == '_params':
                truncated_content[loop_idx_str] = traces
                continue
            
            if not isinstance(traces, list):
                truncated_content[loop_idx_str] = traces
                continue
            
            num_traces = len(traces)
            
            # 检查是否有 initial 和 final 标记（通过解析 simple.py 的输出格式）
            # 注意：parse_samples 返回的是简化后的字符串列表，不包含标记信息
            # 我们需要在解析时保留这些信息，或者在这里通过其他方式识别
            
            if num_traces <= 2 * m:
                # 如果总 traces 数小于等于 2m，保留全部
                truncated_content[loop_idx_str] = traces
            else:
                # 保留前 m 个和后 m 个 traces
                # 注意：第一个可能是 initial，最后一个可能是 final
                truncated_traces = traces[:m] + traces[num_traces - m:]
                truncated_content[loop_idx_str] = truncated_traces
                print(f"Loop {loop_idx_str}: truncated {num_traces} traces to {len(truncated_traces)} (kept first {m} and last {m})")
        
        return truncated_content
    
    def _validate_runs_and_traces_per_loop(self):
        """
        验证每个循环都有足够的 run 和 traces。
        验证每个 run 的 traces 都被正确截断（<= 2 * keep_traces_per_run）。
        """
        from config import DYNAMIC_SAMPLING_CONFIG
        from collections import defaultdict
        
        expected_runs = DYNAMIC_SAMPLING_CONFIG.get('num_runs_per_loop', 10)
        expected_max_traces_per_run = 2 * DYNAMIC_SAMPLING_CONFIG.get('keep_traces_per_run', 3)
        
        loop_runs_map = defaultdict(list)
        for sample_dict in self.sample_contents:
            for loop_idx_str, traces in sample_dict.items():
                if loop_idx_str != '_params':
                    loop_runs_map[loop_idx_str].append(len(traces))
        
        print(f"\n{'='*60}")
        print("Validating runs and traces per loop")
        print(f"  Expected runs per loop: {expected_runs}")
        print(f"  Expected traces per run: {DYNAMIC_SAMPLING_CONFIG.get('keep_traces_per_run', 3)} (first) + {DYNAMIC_SAMPLING_CONFIG.get('keep_traces_per_run', 3)} (last) = {expected_max_traces_per_run} total")
        print(f"{'='*60}")
        
        all_loops_valid = True
        if not loop_runs_map:
            print("Warning: No traces collected for any loop.")
            all_loops_valid = False
        
        for loop_idx_str, traces_counts in loop_runs_map.items():
            num_actual_runs = len(traces_counts)
            max_actual_traces = max(traces_counts) if traces_counts else 0
            min_actual_traces = min(traces_counts) if traces_counts else 0
            avg_actual_traces = sum(traces_counts) / num_actual_runs if num_actual_runs > 0 else 0
            
            run_status = "✓" if num_actual_runs >= expected_runs else "✗"
            traces_status = "✓" if max_actual_traces <= expected_max_traces_per_run else "✗"
            
            print(f"{run_status} Loop {loop_idx_str}: {num_actual_runs} runs, traces per run: {min_actual_traces}-{max_actual_traces} (avg: {avg_actual_traces:.1f})")
            
            if num_actual_runs < expected_runs:
                print(f"    Warning: Expected {expected_runs} runs, but only found {num_actual_runs}")
                all_loops_valid = False
            
            if max_actual_traces > expected_max_traces_per_run:
                print(f"    Warning: Some runs have {max_actual_traces} traces, expected <= {expected_max_traces_per_run} (may need truncation)")
                all_loops_valid = False
        
        if all_loops_valid:
            print(f"{'='*60}")
            print("✓ All loops passed validation for runs and traces.")
            print(f"{'='*60}")
        else:
            print(f"{'='*60}")
            print("✗ Some loops failed validation for runs or traces.")
            print(f"{'='*60}")

    

    def sample(self):
        """
        执行动态采样流程（简化版本）

        只执行动态采样，不进行符号执行分析。
        从代码中提取基本的循环信息创建 records。
        """
        import re
        import logging
        logger = logging.getLogger('SE2INV')

        # 1. 提取循环信息（简化版本，不需要符号执行）
        logger.info('Extracting loops...')
        try:
            # 读取输入文件
            with open(self.input_file, 'r', encoding='utf-8') as f:
                code = f.read()

            # 提取循环内容（使用 process_loop_file 但不执行符号执行）
            self.loop_contents, self.sorted_indices, self.inner_flags = self.process_loop_file(self.input_file, self.unfold_file)

            # 初始化 records
            self.records = []
            self.loop_slices = []

            # 为每个循环创建基本 record
            for idx in self.sorted_indices:
                loop_content = self.loop_contents[idx]

                # 提取循环条件
                loop_condition = None
                for_loop_match = re.search(r'for\s*\([^;]*;\s*([^;]+);', loop_content)
                while_loop_match = re.search(r'while\s*\(([^)]+)\)', loop_content)
                if for_loop_match:
                    loop_condition = for_loop_match.group(1).strip()
                elif while_loop_match:
                    loop_condition = while_loop_match.group(1).strip()

                # 提取变量（简单提取）- 从循环体中提取
                current_vars = set(re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', loop_content))
                # 排除关键字
                keywords = {'for', 'while', 'if', 'else', 'int', 'return', 'break', 'continue', 'printf', 'scanf',
                            'char', 'float', 'double', 'void', 'do', 'switch', 'case', 'sizeof', 'struct',
                            'union', 'enum', 'typedef', 'static', 'extern', 'const', 'volatile',
                            'unsigned', 'signed', 'short', 'long', 'goto', 'main'}
                current_vars = {v for v in current_vars if v not in keywords}

                # 从完整代码中提取局部变量声明（循环前的 int x = ...; 声明）
                # 这样 LLM 生成包含这些变量的不变式不会被语法过滤器误杀
                local_var_pattern = r'\b(?:int|long|short|unsigned|signed|char|float|double)\s+([a-zA-Z_]\w*)\s*[=;,]'
                local_vars = set(re.findall(local_var_pattern, code))
                current_vars.update(local_vars)

                # Extract function parameters (just the parameter names, not the full \\at format)
                # The filter expects parameter names, not the full \\at(param, Pre) format
                param_pre_vars = list(self.function_params)

                # 提取 requires 子句（函数级前置条件，仅保留作参考）
                requires_match = re.search(r'(?:/\*@|//@)\s*requires\s+([^@]+?)(?:\*/|$)', code, re.DOTALL)
                function_precondition = requires_match.group(1).strip() if requires_match else None
                pre_condition = None

                # 创建简化的 record
                record = {
                    'loop_idx': idx,
                    'loop_content': loop_content,
                    'begin': {},
                    'end': {},
                    'begin_map': '',
                    'end_map': '',
                    'transition_relation': '',
                    'common_vars': list(current_vars),
                    'unchanged_vars': [],
                    'non_inductive_vars': [],
                    'function_precondition': function_precondition,
                    'pre_condition': pre_condition,
                    'loop_condition': loop_condition,
                    'updated_loop_conditions': [],
                    'var_maps': {},
                    'path_conds': [],
                    'current_vars': list(current_vars),
                    'param_pre_vars': param_pre_vars,
                    'function_params': self.function_params,
                    'loop_bound': None,
                }
                self.records.append(record)
                self.loop_slices.append([idx])
                logger.info(f"Loop {idx}: extracted basic info")

            logger.info(f"Found {len(self.records)} loops")
        except Exception as e:
            logger.error(f"Error extracting loops: {e}")
            import traceback
            logger.error(traceback.format_exc())
            return

        # Enrich loop-entry precondition from symbolic execution begin-map.
        self._enrich_records_with_symexec_begin_map()

        # 2. 执行动态采样
        logger.info('Starting dynamic sampling...')
        try:
            self.dynamic()
            logger.info(f"Dynamic sampling completed: {len(self.sample_contents)} execution groups")
        except Exception as e:
            logger.error(f"Dynamic sampling failed: {e}")
            import traceback
            logger.error(traceback.format_exc())
            logger.warning("Proceeding without trace data")

    def sample_without_traces(self):
        """
        只提取循环信息，不执行动态采样（不生成 traces）

        当 USE_TRACES=False 时使用此方法，跳过程序执行和 traces 收集。
        """
        import re

        # 1. 提取循环信息（与 sample() 相同的逻辑）
        print('------------------------------------extracting loops (no traces)------------------------------------')
        try:
            # 读取输入文件
            with open(self.input_file, 'r', encoding='utf-8') as f:
                code = f.read()

            # 提取循环内容
            self.loop_contents, self.sorted_indices, self.inner_flags = self.process_loop_file(self.input_file, self.unfold_file)

            # 初始化 records
            self.records = []
            self.loop_slices = []
            self.sample_contents = []  # 空的 traces

            # 为每个循环创建基本 record
            for idx in self.sorted_indices:
                loop_content = self.loop_contents[idx]

                # 提取循环条件
                loop_condition = None
                for_loop_match = re.search(r'for\s*\([^;]*;\s*([^;]+);', loop_content)
                while_loop_match = re.search(r'while\s*\(([^)]+)\)', loop_content)
                if for_loop_match:
                    loop_condition = for_loop_match.group(1).strip()
                elif while_loop_match:
                    loop_condition = while_loop_match.group(1).strip()

                # 提取变量 - 从循环体中提取
                current_vars = set(re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', loop_content))
                keywords = {'for', 'while', 'if', 'else', 'int', 'return', 'break', 'continue', 'printf', 'scanf',
                            'char', 'float', 'double', 'void', 'do', 'switch', 'case', 'sizeof', 'struct',
                            'union', 'enum', 'typedef', 'static', 'extern', 'const', 'volatile',
                            'unsigned', 'signed', 'short', 'long', 'goto', 'main'}
                current_vars = {v for v in current_vars if v not in keywords}

                # 从完整代码中提取局部变量声明（循环前的 int x = ...; 声明）
                local_var_pattern = r'\b(?:int|long|short|unsigned|signed|char|float|double)\s+([a-zA-Z_]\w*)\s*[=;,]'
                local_vars = set(re.findall(local_var_pattern, code))
                current_vars.update(local_vars)

                # Extract function parameters
                param_pre_vars = [f"\\at({param}, Pre)" for param in self.function_params]

                # 提取 requires 子句（函数级前置条件，仅保留作参考）
                requires_match = re.search(r'(?:/\*@|//@)\s*requires\s+([^@]+?)(?:\*/|$)', code, re.DOTALL)
                function_precondition = requires_match.group(1).strip() if requires_match else None
                pre_condition = None

                # 创建简化的 record
                record = {
                    'loop_idx': idx,
                    'loop_content': loop_content,
                    'begin': {},
                    'end': {},
                    'begin_map': '',
                    'end_map': '',
                    'transition_relation': '',
                    'common_vars': list(current_vars),
                    'unchanged_vars': [],
                    'non_inductive_vars': [],
                    'function_precondition': function_precondition,
                    'pre_condition': pre_condition,
                    'loop_condition': loop_condition,
                    'updated_loop_conditions': [],
                    'var_maps': {},
                    'path_conds': [],
                    'current_vars': list(current_vars),
                    'param_pre_vars': param_pre_vars,
                    'function_params': self.function_params,
                    'loop_bound': None,
                }
                self.records.append(record)
                self.loop_slices.append([idx])
                print(f"Loop {idx}: extracted basic info (no traces)")

            print(f"Found {len(self.records)} loops (traces disabled)")
            self._enrich_records_with_symexec_begin_map()
            print('----------------------------------------------------------------------------------------')
        except Exception as e:
            print(f"Error extracting loops: {e}")
            import traceback
            traceback.print_exc()


        





def main():
  # Create parser
    parser = argparse.ArgumentParser(description="Read file_name from command-line arguments.")
    parser.add_argument('file_name', type=str, help="The name of the file without extension")

    # Parse arguments
    args = parser.parse_args()
    # Create LoopSampler and execute

    sampler = LoopSampler(args.file_name, input_subdir='NLA_lipus')
    sampler.sample()





   
   

if __name__ == "__main__":
    main()
