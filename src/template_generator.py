#!/usr/bin/env python3
"""
Template Generator for Loop Invariants
参考 inv_gen.py 的实现，为循环 record 生成包含 ACSL 不变量模板的代码
"""

import re
import json
from typing import Dict, List, Optional


class TemplateGenerator:
    """生成包含 ACSL 不变量模板的代码"""
    
    def __init__(self):
        pass
    
    def filter_condition(self, condition: str) -> str:
        """过滤条件字符串，移除特殊字符，并将 v@pre 转换为 \at(v, Pre)"""
        if not condition:
            return condition
        
        # 移除多余的空白字符
        condition = re.sub(r'\s+', ' ', condition.strip())
        
        # 将 v@pre 替换为 \at(v, Pre)
        # 解释: (\w+) 捕获变量名, @pre 匹配后缀
        # 替换为: \at(捕获的变量名, Pre)
        condition = re.sub(r'(\w+)@pre', r'\\at(\1, Pre)', condition)
        
        return condition
    
    def extract_var_map_from_state(self, text: str) -> Dict[str, str]:
        """从状态字符串中提取变量映射"""
        var_map = {}
        # 匹配模式如 "var == value"，支持嵌套括号
        pattern = r'(\w+)\s*==\s*(\((?:[^()]*|\((?:[^()]*|\([^()]*\))*\))*\)|[^()]+)'
        matches = re.findall(pattern, text)
        
        for var, value in matches:
            value = value.strip()
            if value.startswith('(') and value.endswith(')'):
                value = value[1:-1]
            var_map[var] = value
        
        return var_map
    
    def contains_no_letters(self, condition: Optional[str]) -> bool:
        """检查条件是否不包含字母（即是否为常量）"""
        if condition is None:
            return True
        if 'unknown' in condition:
            return True
        if re.search(r'[a-zA-Z]', condition):
            return False
        return True
    
    def _append_after_last_annotation(self, annotations: str, new_annotations: List[str]) -> str:
        """在最后一个注释行之后追加新注释"""
        if not new_annotations:
            return annotations
        
        lines = annotations.splitlines()
        updated_code = []
        inserted = False
        
        for i, line in enumerate(lines):
            updated_code.append(line)
            # 找到最后一个注释行（loop invariant 或 loop assigns），在其后插入
            if ('loop invariant' in line or 'loop assigns' in line) and not inserted:
                # 检查下一行是否是 */ 或空行
                if i + 1 < len(lines):
                    next_line = lines[i + 1].strip()
                    if next_line == '*/' or (not next_line and i + 2 < len(lines) and lines[i + 2].strip() == '*/'):
                        for inv in new_annotations:
                            updated_code.append(f"          {inv}")
                        inserted = True
        
        # 如果没有找到插入位置，在第一个 /*@ 之后插入
        if not inserted:
            updated_code = []
            found_first_annotation = False
            for line in lines:
                if not found_first_annotation and '/*@' in line:
                    updated_code.append(line)
                    for inv in new_annotations:
                        updated_code.append(f"          {inv}")
                    found_first_annotation = True
                else:
                    updated_code.append(line)
        
        return "\n".join(updated_code)
    
    def append_const_annotations(self, annotations: str, unchanged_vars: List[str], 
                                 var_map: Dict[str, str], path_cond: Optional[str] = None) -> str:
        """添加常量变量的不变量注释"""
        invariant_annotations = []
        
        for var_name in unchanged_vars:
            if var_name in var_map:
                value = self.filter_condition(var_map[var_name])
                var_name = self.filter_condition(var_name)
                
                if path_cond is not None:
                    path_cond_filtered = self.filter_condition(path_cond)
                    invariant_annotations.append(
                        f"loop invariant ({path_cond_filtered}) ==> ({var_name} == {value});"
                    )
                else:
                    invariant_annotations.append(f"loop invariant {var_name} == {value};")
        
        return self._append_after_last_annotation(annotations, invariant_annotations)
    
    def append_notin_annotations(self, annotations: str, var_map: Dict[str, str],
                                updated_loop_condition: Optional[str], 
                                path_cond: Optional[str] = None) -> str:
        """添加循环条件不满足时的初始状态不变量"""
        init_invariants = []
        for var in var_map:
            init_value = self.filter_condition(var_map[var])
            var_filtered = self.filter_condition(var)
            init_invariants.append(f'({var_filtered} == {init_value})')
        
        init_invariant = ' && '.join(init_invariants)
        invariant_annotation = None
        
        if not self.contains_no_letters(updated_loop_condition):
            if path_cond is not None:
                path_cond_filtered = self.filter_condition(path_cond)
                invariant_annotation = (
                    f"loop invariant ({path_cond_filtered}) ==> "
                    f"((!({updated_loop_condition})) ==> ({init_invariant}));"
                )
            else:
                invariant_annotation = (
                    f"loop invariant (!({updated_loop_condition})) ==> ({init_invariant});"
                )
        
        if invariant_annotation:
            return self._append_after_last_annotation(annotations, [invariant_annotation])
        return annotations
    
    def append_annotations(self, annotations: str, updated_loop_condition: Optional[str],
                          key: str, path_cond: Optional[str] = None) -> str:
        """添加一般变量的不变量注释"""
        if self.contains_no_letters(updated_loop_condition):
            if path_cond is not None:
                path_cond_filtered = self.filter_condition(path_cond)
                invariant_annotation = f"loop invariant ({path_cond_filtered}) ==> (PLACE_HOLDER_{key});"
            else:
                invariant_annotation = f"loop invariant PLACE_HOLDER_{key};"
        else:
            if path_cond is not None:
                path_cond_filtered = self.filter_condition(path_cond)
                invariant_annotation = (
                    f"loop invariant ({path_cond_filtered}) ==> "
                    f"(({updated_loop_condition}) ==> (PLACE_HOLDER_{key}));"
                )
            else:
                invariant_annotation = (
                    f"loop invariant ({updated_loop_condition}) ==> (PLACE_HOLDER_{key});"
                )
        
        return self._append_after_last_annotation(annotations, [invariant_annotation])

    def append_trivial_placeholder(self, annotations: str, key: str) -> str:
        """为变量添加仅包含占位符的简单模板，便于大模型自由填充。"""
        trivial_inv = f"loop invariant PLACE_HOLDER_{key};"
        return self._append_after_last_annotation(annotations, [trivial_inv])
    
    def append_non_inductive_annotations(self, annotations: str, var_map: Dict[str, str],
                                        updated_loop_condition: Optional[str], key: str,
                                        path_cond: Optional[str] = None) -> str:
        """添加非归纳变量的不变量注释"""
        init_invariants = []
        for var in var_map:
            init_value = self.filter_condition(var_map[var])
            var_filtered = self.filter_condition(var)
            init_invariants.append(f'({var_filtered} == {init_value})')
        
        init_invariant = ' && '.join(init_invariants)
        
        if self.contains_no_letters(updated_loop_condition):
            if path_cond is not None:
                path_cond_filtered = self.filter_condition(path_cond)
                invariant_annotation = (
                    f"loop invariant ({path_cond_filtered}) ==> "
                    f"(({init_invariant}) || (PLACE_HOLDER_{key}));"
                )
            else:
                invariant_annotation = f"loop invariant ({init_invariant}) || (PLACE_HOLDER_{key});"
        else:
            if path_cond is not None:
                path_cond_filtered = self.filter_condition(path_cond)
                invariant_annotation = (
                    f"loop invariant ({path_cond_filtered}) ==> "
                    f"(({updated_loop_condition}) ==> (({init_invariant}) || (PLACE_HOLDER_{key})));"
                )
            else:
                invariant_annotation = (
                    f"loop invariant ({updated_loop_condition}) ==> "
                    f"(({init_invariant}) || (PLACE_HOLDER_{key}));"
                )
        
        return self._append_after_last_annotation(annotations, [invariant_annotation])
    
    def append_verification_goal_annotations(self, annotations: str, path_cond: Optional[str],
                                            updated_loop_condition: Optional[str]) -> str:
        """添加验证目标的不变量注释"""
        if self.contains_no_letters(updated_loop_condition):
            if path_cond is not None:
                path_cond_filtered = self.filter_condition(path_cond)
                invariant_annotation = (
                    f"loop invariant ({path_cond_filtered}) ==> "
                    f"(PLACE_HOLDER_VERFICATION_GOAL);"
                )
            else:
                invariant_annotation = "loop invariant PLACE_HOLDER_VERFICATION_GOAL;"
        else:
            if path_cond is not None:
                path_cond_filtered = self.filter_condition(path_cond)
                invariant_annotation = (
                    f"loop invariant ({path_cond_filtered}) ==> "
                    f"(({updated_loop_condition}) ==> (PLACE_HOLDER_VERFICATION_GOAL));"
                )
            else:
                invariant_annotation = (
                    f"loop invariant ({updated_loop_condition}) ==> (PLACE_HOLDER_VERFICATION_GOAL);"
                )
        
        return self._append_after_last_annotation(annotations, [invariant_annotation])
    
    def append_assignments_annotations(self, annotations: str) -> str:
        """添加循环赋值注释"""
        return self._append_after_last_annotation(annotations, ["loop assigns PLACE_HOLDER_ASSIGNMENTS;"])
    
    def append_inner_annotations(self, annotations: str) -> str:
        """添加内层循环的占位符注释"""
        return self._append_after_last_annotation(annotations, ["PLACE_HOLDER_LOOP"])
    
    def generate_template(self, record: Dict, simplified: bool = True) -> str:
        """
        根据循环 record 生成包含 ACSL 不变量模板的代码
        
        Args:
            record: 包含循环信息的字典，包含以下字段：
                - loop_content: 循环代码内容
                - pre_condition: 前置条件
                - var_maps: 变量映射列表
                - unchanged_vars: 未改变的变量列表
                - non_inductive_vars: 非归纳变量列表
                - updated_loop_conditions: 更新的循环条件列表
                - path_conds: 路径条件列表
                - loop_condition: 循环条件
            simplified: 是否使用简化模板（默认True，只生成基本占位符）
        
        Returns:
            包含 ACSL 注释模板的完整代码字符串
        """
        loop_content = record.get('loop_content', '')
        loop_bound = record.get('loop_bound')  # 可能的循环迭代上界/条件
        
        if simplified:
            # 简化模板：只生成基本的占位符，让 LLM 自由发挥
            tag = "/* >>> LOOP INVARIANT TO FILL <<< */"
            
            # 添加 pfit 部分有效的不变量（如果有）
            pfit_partial = record.get('pfit_partial_valid', [])
            pfit_section = ""
            if pfit_partial:
                for inv in pfit_partial:
                    pfit_section += f"      {inv}\n"
            
            annotations = f"""{tag}
/*@
{pfit_section}  loop invariant PLACE_HOLDER_VERIFICATION_GOAL;
  loop assigns PLACE_HOLDER_ASSIGNMENTS;
*/
{loop_content}"""
            return annotations
        
        # 以下是原有的复杂模板生成逻辑
        pre_condition = record.get('pre_condition', '')
        var_maps = record.get('var_maps', [])
        unchanged_vars = record.get('unchanged_vars', [])
        non_inductive_vars = record.get('non_inductive_vars', [])
        updated_loop_conditions = record.get('updated_loop_conditions', [])
        path_conds = record.get('path_conds', [])
        
        # 如果没有 var_maps，尝试从 pre_condition 中提取
        if not var_maps and pre_condition:
            var_map = self.extract_var_map_from_state(pre_condition)
            if var_map:
                var_maps = [var_map]
        
        # 如果没有 updated_loop_conditions，使用 loop_condition
        loop_condition = record.get('loop_condition', '')
        if not updated_loop_conditions:
            updated_loop_conditions = [loop_condition] if loop_condition else [None]
        
        # 如果没有 path_conds，使用 None
        if not path_conds:
            path_conds = [None]
        
        # 确保列表长度一致
        max_len = max(len(var_maps), len(updated_loop_conditions), len(path_conds))
        var_maps = var_maps[:max_len] if var_maps else [{}] * max_len
        updated_loop_conditions = (updated_loop_conditions[:max_len] 
                                   if updated_loop_conditions else [None] * max_len)
        path_conds = path_conds[:max_len] if path_conds else [None] * max_len
        
        # 创建基础注释模板
        tag = "/* >>> LOOP INVARIANT TO FILL <<< */"
        
        # 添加 pfit 部分有效的不变量作为第一行（如果有）
        pfit_partial = record.get('pfit_partial_valid', [])
        pfit_section = ""
        if pfit_partial:
            for inv in pfit_partial:
                pfit_section += f"      {inv}\n"
        
        annotations = f'''
        {tag}
        /*@
{pfit_section}        */
        {loop_content}
        '''
        
        # 处理每个路径条件组合
        for var_map, path_cond, updated_loop_condition in zip(var_maps, path_conds, updated_loop_conditions):
            # 过滤条件
            if updated_loop_condition:
                updated_loop_condition = self.filter_condition(updated_loop_condition)
            if path_cond:
                path_cond = self.filter_condition(path_cond)
            
            # 添加常量变量注释
            annotations = self.append_const_annotations(
                annotations, unchanged_vars, var_map, path_cond
            )
            
            # 添加循环条件不满足时的注释
            annotations = self.append_notin_annotations(
                annotations, var_map, updated_loop_condition, path_cond
            )
            
            # 添加一般变量注释
            for key in var_map.keys():
                if key not in unchanged_vars:
                    if key in non_inductive_vars:
                        annotations = self.append_non_inductive_annotations(
                            annotations, var_map, updated_loop_condition, key, path_cond
                        )
                    else:
                        annotations = self.append_annotations(
                            annotations, updated_loop_condition, key, path_cond
                        )
                # 为每个变量追加一个只含占位符的 trivial 模板
                annotations = self.append_trivial_placeholder(annotations, key)

        # 如有 loop_bound，追加为不变量（鼓励上下界）
        if loop_bound:
            annotations = self._append_after_last_annotation(
                annotations,
                [f"loop invariant {loop_bound};"]
            )
        
        # 添加验证目标注释
        # 使用最后一个路径条件组合
        if var_maps and updated_loop_conditions:
            last_path_cond = path_conds[-1] if path_conds else None
            last_loop_cond = updated_loop_conditions[-1] if updated_loop_conditions else None
            if last_loop_cond:
                last_loop_cond = self.filter_condition(last_loop_cond)
            if last_path_cond:
                last_path_cond = self.filter_condition(last_path_cond)
            annotations = self.append_verification_goal_annotations(
                annotations, last_path_cond, last_loop_cond
            )
        
        # 添加赋值注释（放在最后）
        annotations = self.append_assignments_annotations(annotations)
        
        return annotations
    
    def process_record(self, record: Dict) -> Dict:
        """
        处理单个 record，添加 template 字段
        
        Args:
            record: 循环 record 字典
        
        Returns:
            添加了 template 字段的 record
        """
        template = self.generate_template(record)
        record['template'] = template
        return record
    
    def process_records(self, records: List[Dict]) -> List[Dict]:
        """
        批量处理多个 records
        
        Args:
            records: record 列表
        
        Returns:
            处理后的 record 列表
        """
        return [self.process_record(record) for record in records]


def get_test_record():
    """返回写死的测试 JSON record"""
    return {
        "loop_idx": 0,
        "loop_content": "while (y < 100000) {\n        x = x + y;\n        y = y + 1;\n    }",
        "begin": "(x == x@last) * (y == y@last)",
        "end": "y@last < 100000 && (x == x@last + y@last) * (y == y@last + 1)",
        "common_vars": ["y", "x"],
        "unchanged_vars": [],
        "non_inductive_vars": [],
        "pre_condition": "(y == 0) * (x == 1)",
        "loop_condition": "y < 100000",
        "updated_loop_conditions": ["0 < 100000"],
        "var_maps": [
            {
                "y": "0",
                "x": "1"
            }
        ],
        "path_conds": [None],
        "current_vars": ["y", "x"]
    }


def main():
    """主函数：从 JSON 文件读取 records，添加 template 字段，输出结果"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="为循环 record 生成包含 ACSL 不变量模板的代码"
    )
    parser.add_argument('input_file', nargs='?', help='输入的 JSON 文件路径（包含 record 或 records 列表），如果不提供则使用测试数据')
    parser.add_argument('-o', '--output', help='输出文件路径（可选，默认覆盖输入文件）')
    parser.add_argument('--stdout', action='store_true', help='输出完整 JSON 到标准输出')
    parser.add_argument('--template-only', action='store_true', help='只输出 template 字段内容（不包含 JSON）')
    parser.add_argument('--test', action='store_true', help='使用内置测试数据')
    
    args = parser.parse_args()
    
    # 如果没有提供输入文件或使用 --test 选项，使用测试数据
    if args.test or not args.input_file:
        print("使用内置测试数据...")
        data = get_test_record()
    else:
        # 读取输入文件
        with open(args.input_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
    
    # 判断输入格式：单个 record 或 record 列表
    if isinstance(data, dict):
        records = [data]
    elif isinstance(data, list):
        records = data
    else:
        raise ValueError("输入必须是 JSON 对象或对象数组")
    
    # 生成模板
    generator = TemplateGenerator()
    processed_records = generator.process_records(records)
    
    # 输出结果
    if args.template_only:
        # 只输出 template 字段
        for i, record in enumerate(processed_records):
            if len(processed_records) > 1:
                print(f"=== Record {i+1} ===")
            print(record.get('template', ''))
            if len(processed_records) > 1 and i < len(processed_records) - 1:
                print()
    elif args.stdout:
        if len(processed_records) == 1:
            print(json.dumps(processed_records[0], indent=2, ensure_ascii=False))
        else:
            print(json.dumps(processed_records, indent=2, ensure_ascii=False))
    else:
        if args.test or not args.input_file:
            # 使用测试数据时，默认输出到标准输出
            print("生成的模板:")
            print("=" * 80)
            print(processed_records[0].get('template', ''))
            print("=" * 80)
        else:
            output_file = args.output or args.input_file
            with open(output_file, 'w', encoding='utf-8') as f:
                if len(processed_records) == 1:
                    json.dump(processed_records[0], f, indent=2, ensure_ascii=False)
                else:
                    json.dump(processed_records, f, indent=2, ensure_ascii=False)
            print(f"已处理 {len(processed_records)} 个 record，结果保存到 {output_file}")


if __name__ == '__main__':
    main()

