import json
import re
import openai
import logging
from bound_analysis import LoopBoundAnalyzer

class LoopAnalysis:
    def __init__(self,json_file,idx):
        """
        :param json_file: JSON file path or data
        :param idx: Loop index to extract
        """
        self.json_file = json_file
        self.idx = idx
        self.pre_condition =None
        self.path_conds = None
        self.loop_condition = None
        self.updated_loop_conditions = None
        self.var_maps = None
        self.current_vars = None
        

    
        

    def get_json_at_index(self):
        with open(self.json_file, 'r') as file:
            data = json.load(file)  # Read and parse JSON file
            
            if isinstance(data, list) and 0 <= self.idx < len(data):
                return data[self.idx]  # Return the idx-th JSON object
            else:
                raise IndexError("Index out of range or data is not a list")
            
    

    def extract_precond_from_file(self):
        
        loop = self.get_json_at_index()  
        condition = loop.get("condition", "")  
        return condition


    def extract_var_map_from_file(self):
        loop = self.get_json_at_index() 
        condition = loop.get("condition", "") 
        print(condition)

        sub_conditions = [s.strip() for s in condition.split("||")]

        var_maps = []
        path_conds = []

        def split_path_and_state(expression):
            """
            Split string by the last && to get path and state
            :param expression: Input expression string
            :return: Return path and state parts
            """
            # Find position of last &&
            last_and_index = expression.rfind("&&")

            if last_and_index == -1:
                # If no && found, path is empty, entire expression as state
                path = None
                state = expression.strip()
            else:
                # Split by last &&
                path = expression[:last_and_index].strip()
                path_parts = path.split('&&')
                valid_parts = []
                for part in path_parts:
                    if 'exists' in path_parts or 'forall' in path_parts:
                        continue
                    else:
                        valid_parts.append(part)

                if path_parts == []:
                    path =None
                else:
                    path = '&&'.join(valid_parts)

                state = expression[last_and_index + 2:].strip()

            return path, state

        # Regular expression matching patterns like "var == value", supporting nested parentheses


        def parse_expressions(s):
            var_map = {}
            remaining = s.strip()
            stack = []
            expr_start = 0
            i = 0
            n = len(remaining)
            
            while i < n:
                char = remaining[i]
                
                # Handle parenthesis nesting
                if char == '(':
                    stack.append(i)
                elif char == ')':
                    if stack:
                        stack.pop()
                
                # When encountering logical operators and not inside parentheses, split expression
                if i < n-1 and remaining[i:i+2] in ('&&', '* ') and not stack:
                    # Extract current expression
                    expr = remaining[expr_start:i].strip()
                    # Parse key-value pairs in expression
                    eq_pos = expr.find('==')
                    if eq_pos != -1:
                        var = expr[:eq_pos].strip(' ()')
                        value = expr[eq_pos+2:].strip(' ()')
                        var_map[var] = value
                    expr_start = i + 2
                    i += 1  # Skip second character of operator
                
                i += 1
            
            # Process last expression
            expr = remaining[expr_start:].strip()
            eq_pos = expr.find('==')
            if eq_pos != -1:
                var = expr[:eq_pos].strip(' ()')
                value = expr[eq_pos+2:].strip(' ()')
                var_map[var] = value
                
            return var_map

        for sub_condition in sub_conditions:

            path,state = split_path_and_state(sub_condition)
            var_map = {}  # Create a new var_map for each sub-condition
            path_cond = path
            path_conds.append(path_cond)
           
            var_map = parse_expressions(state)
            var_maps.append(var_map)  # Add var_map to list


        variables_to_exclude = set()
        for var_key in var_maps[0].keys():
            variables_to_exclude.add(f'{var_key}_v')
            variables_to_exclude.add(f'{var_key}_length')

        new_path_conds = []

        # print(variables_to_exclude)

        for p in path_conds:
            if p is None:
                new_path_conds.append(None)
                continue
            
            parts = p.split('&&')
            filtered_parts = [part.strip() for part in parts if not any(exclude_var in part for exclude_var in variables_to_exclude)]
            path_cond = ' && '.join(filtered_parts) or None
            new_path_conds.append(path_cond)

        variables_to_replace = set()
        for var_key in var_maps[0].keys():
            variables_to_replace.add(f'{var_key}_l')
        
        for replacement in variables_to_replace:
            for path_cond in new_path_conds:
                if path_cond:
                    # Only replace _l at the end of variable names, not in the middle
                    import re
                    pattern = r'\b' + re.escape(replacement) + r'\b'
                    path_cond = re.sub(pattern, replacement[:-2], path_cond)
            
            for var_map in var_maps:
                for key in var_map.keys():
                    # Only replace _l at the end of variable names, not in the middle
                    import re
                    pattern = r'\b' + re.escape(replacement) + r'\b'
                    var_map[key] = re.sub(pattern, replacement[:-2], var_map[key])
                    
        path_conds = new_path_conds
        # path_conds = [' && '.join([part.strip() for part in p.split('&&') if '{var_maps[0][keys]}_v' not in part]) or None for p in path_conds]

        return var_maps,path_conds
    
    def extract_first_loop_condition(self):
       
        loop = self.get_json_at_index()
        code = loop.get("content", "")
        
        # Find first occurrence of for or while keyword
        loop_keywords = ["for", "while"]
        first_pos = len(code)
        keyword_found = None
        for keyword in loop_keywords:
            pos = code.find(keyword)
            if pos != -1 and pos < first_pos:
                first_pos = pos
                keyword_found = keyword
        if keyword_found is None:
            return None  # Loop keyword not found
        
        # Ensure found is complete keyword
        if (first_pos > 0 and (code[first_pos-1].isalnum() or code[first_pos-1]=='_')) or \
        (first_pos + len(keyword_found) < len(code) and (code[first_pos+len(keyword_found)].isalnum() or code[first_pos+len(keyword_found)]=='_')):
            return None
        
        # Locate '(' (skip keyword and spaces)
        cursor = first_pos + len(keyword_found)
        while cursor < len(code) and code[cursor].isspace():
            cursor += 1
        if cursor >= len(code) or code[cursor] != '(':
            return None  # Left parenthesis not found
        cursor += 1  # Skip '('
        
        # Extract content inside parentheses, supporting nested parentheses
        condition_start = cursor
        paren_depth = 1
        while cursor < len(code) and paren_depth > 0:
            if code[cursor] == '(':
                paren_depth += 1
            elif code[cursor] == ')':
                paren_depth -= 1
            cursor += 1
        if paren_depth != 0:
            return None  # Parentheses don't match
        inner = code[condition_start: cursor-1].strip()
        
        # Extract condition
        condition = None
        if keyword_found == "while":
            # while loop condition is entire content inside parentheses
            condition = inner
        elif keyword_found == "for":
            # for loop usually contains three expressions: initialization; condition; iteration, condition is in the middle
            parts = []
            part = ""
            nested = 0  # Handle internal parenthesis nesting
            for ch in inner:
                if ch == '(':
                    nested += 1
                elif ch == ')':
                    nested -= 1
                if ch == ';' and nested == 0:
                    parts.append(part.strip())
                    part = ""
                else:
                    part += ch
            parts.append(part.strip())
            # Condition part is in the second semicolon-separated part (if exists)
            if len(parts) >= 2:
                condition = parts[1]
            else:
                condition = None

            if condition == '':
                condition = None
        return condition

    


    def replace_vars_with_values(self, loop_cond, var_maps):
        
        updated_loop_conditions = []

        if loop_cond == None:
            return [None]

        for var_map in var_maps:
            # Convert string to list for easy modification
            loop_cond_list = list(loop_cond)
            i = 0  # Current search position

            while i < len(loop_cond_list):
                # Search for variable names from left to right
                for var in var_map:
                    # Check if current position matches variable name
                    if loop_cond_list[i:i + len(var)] == list(var):
                        # Check if variable name is complete (word boundaries or non-alphanumeric characters before and after)
                        is_start_boundary = (i == 0 or not loop_cond_list[i - 1].isalnum())
                        is_end_boundary = (i + len(var) >= len(loop_cond_list) or not loop_cond_list[i + len(var)].isalnum())
                        if is_start_boundary and is_end_boundary:
                            # Replace variable name
                            loop_cond_list[i:i + len(var)] = list(var_map[var])
                            # Skip replaced part
                            i += len(var_map[var]) - 1
                            break
                i += 1

            # Convert list back to string and add to result
            updated_loop_conditions.append(''.join(loop_cond_list))

        return updated_loop_conditions
    
    def extract_current_vars(self):
        """
        从循环内容中提取变量名
        :return: 循环中出现的变量名列表
        """
        loop = self.get_json_at_index()
        content = loop.get("content", "")
        
        # 使用正则表达式匹配变量名
        # 匹配C语言标识符：字母或下划线开头，后跟字母、数字或下划线
        var_pattern = r'\b[a-zA-Z_][a-zA-Z0-9_]*\b'
        all_vars = re.findall(var_pattern, content)
        
        # 过滤掉C语言关键字和常见函数名
        keywords = {
            'int', 'char', 'float', 'double', 'void', 'if', 'else', 'for', 'while', 
            'do', 'switch', 'case', 'break', 'continue', 'return', 'sizeof', 'struct',
            'union', 'enum', 'typedef', 'static', 'extern', 'const', 'volatile',
            'register', 'auto', 'signed', 'unsigned', 'short', 'long', 'goto',
            'include', 'define', 'ifdef', 'ifndef', 'endif', 'pragma', 'main',
            'printf', 'scanf', 'malloc', 'free', 'strlen', 'strcpy', 'strcmp',
            'assert', 'require', 'ensure', 'invariant', 'loop', 'variant','unknown'
        }
        
        # 过滤掉关键字和数字
        current_vars = []
        for var in all_vars:
            if (var not in keywords and 
                not var.isdigit() and 
                not var.startswith('LoopEntry_') and
                var not in current_vars):
                current_vars.append(var)
        
        return current_vars
    



    def run(self):

        # Extract variable mapping
        var_maps,path_conds = self.extract_var_map_from_file()
        self.var_maps =var_maps
        self.path_conds = path_conds
        # print(f"Variable Maps:{var_maps}")
        # print(f"Path conditions: {path_conds}")
    
        # Extract precondition
        pre_condition = self.extract_precond_from_file()
        self.pre_condition =pre_condition
        # print(f"Pre condition: {pre_condition}")

        # Extract loop condition
        loop_condition = self.extract_first_loop_condition()
        self.loop_condition = loop_condition
        # print(f"Loop Condition: {loop_condition}")

        # Replace variables in loop condition with values
        if var_maps :
            updated_loop_conditions = self.replace_vars_with_values(loop_condition, var_maps)
            self.updated_loop_conditions = updated_loop_conditions
            # print(f"Updated Loop Conditions: {updated_loop_conditions}")

        # Extract current variables from loop content
        current_vars = self.extract_current_vars()
        self.current_vars = current_vars
        # print(f"Current Variables: {current_vars}")










# Example usage 
if __name__ == "__main__":
   
   json_file = 'loop/09.json'
   idx = 0
   analyzer= LoopAnalysis(json_file,idx)
   analyzer.run()