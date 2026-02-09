from typing import List, Dict, Any
import re
from config import LLMConfig
from llm import Chatbot

class PromptFormatter:
    """
    Formats structured loop execution trace data and its context 
    into a single, unrolled, structured English string for LLM analysis.
    """

    def __init__(self, 
                 sample_contents: List[Dict[str, List[str]]],
                 loop_code_snippet: str = "",
                 pre_condition: str = "",
                 transition_relation: str = ""):
        """
        Initializes the formatter with trace data and loop context.

        :param sample_contents: The raw execution trace data.
        :param loop_code_snippet: The code of the loop body.
        :param pre_condition: The condition before loop entry.
        :param transition_relation: The relation describing variable change across iterations.
        """
        self.sample_contents = sample_contents
        self.loop_code_snippet = loop_code_snippet
        # Use pre_condition and transition_relation directly without LLM translation to save tokens
        self.pre_condition = pre_condition if pre_condition else "No pre-condition specified"
        self.transition_relation = transition_relation if transition_relation else "No transition relation specified"
    
    # --- Main Method: Generate Full Prompt ---

    def full_prompt(self) -> str:
        """
        Generates the final, structured LLM prompt by combining the Role, Task, 
        and the formatted loop context/traces.
        """
        loop_context = self.loop_format_for_llm()
        
        # Use a text block structure and strip() to control indentation precisely.
        # The loop_context must be passed without any *leading* indent from Python.
        
        prompt = f"""
### Loop Context: ###
{loop_context}
"""
        # Strip all outer leading/trailing whitespace
        return prompt.strip()

    # --- Helper Method: Replace @pre with \at(v, Pre) ---
    
    def _replace_atpre(self, text: str) -> str:
        """
        将 traces 中的 v@pre 替换为 \at(v, Pre)
        
        Args:
            text: 包含 @pre 的文本
            
        Returns:
            替换后的文本
        """
        # 匹配变量名@pre，变量名可以是字母、数字、下划线的组合
        # 使用 \b 确保单词边界，避免误匹配
        # 将所有 var@pre 替换为 \at(var, Pre)
        return re.sub(r'(\w+)@pre', r'\\at(\1, Pre)', text)
    
    # --- Helper Method: Fully Unroll Trace ---

    def _unroll_trace(self, conditions: List[str]) -> str:
        """
        Unrolls all conditions into a structured, multi-line list style 
        without compression, matching the required output format.
        
        CRITICAL: Explicitly labels each state as "BEFORE loop body execution" 
        or "AFTER loop body execution" to help LLM distinguish temporal states.
        """
        if not conditions:
            return "    [EMPTY_TRACE]"
        
        formatted_lines = []
        num_steps = len(conditions)
        
        for i, step in enumerate(conditions):
            # 将 var@pre 替换为 \at(var, Pre)
            step_replaced = self._replace_atpre(step)
            
            # CRITICAL: Add temporal labels to distinguish loop body execution states
            # - First step (i==0): Initial state BEFORE entering loop
            # - Middle steps: State BEFORE each iteration's loop body execution
            # - Last step: State AFTER loop terminates (loop condition false)
            
            if i == 0:
                # Initial state before loop starts
                temporal_label = "BEFORE loop starts"
            elif i < num_steps - 1:
                # State at the beginning of iteration i (before loop body executes)
                temporal_label = f"BEFORE iteration {i} body executes"
            else:
                # Final state after loop terminates
                temporal_label = "AFTER loop terminates"
            
            # Format: [ CONDITION ] (temporal_label)
            line = f"    [ {step} ]  ({temporal_label})"
            
            # Add '->' to all but the last step
            if i < num_steps - 1:
                line += " ->"
                
            formatted_lines.append(line)
            
        return "\n".join(formatted_lines)

    # --- Data Formatting Method (loop_format_for_llm) ---

    def loop_format_for_llm(self, max_samples: int = 5, max_traces_per_sample: int = 10) -> str:
        """
        Formats the loop context and traces into the clean 'Inputs' block format.
        
        CRITICAL: Emphasizes temporal distinction between states BEFORE and AFTER 
        loop body execution to help LLM understand loop invariant semantics.
        
        Args:
            max_samples: Maximum number of execution groups (samples) to include
            max_traces_per_sample: Maximum number of traces per sample to include
        """
        
        # --- Part 1: Provide Loop Context and Constraints ---
        # Note: No leading spaces on these lines to avoid mis-alignment in the final output block.
        # 将 pre_condition 和 transition_relation 中的 @pre 转换为 \at(v, Pre) 格式
        pre_condition_converted = self._replace_atpre(self.pre_condition)
        transition_relation_converted = self._replace_atpre(self.transition_relation)

        output_lines = [
            "\n1. Loop Context",
            f"  A. Pre-Condition (Before Loop Entry): `{pre_condition_converted}`",
            f"  B. Loop Transition Relation: `{transition_relation_converted}`",
            f"  C. Loop Snippet:\n```c\n{self.loop_code_snippet}\n```",
            
            "\n2. Execution Traces",
            "   Each trace shows the full sequence of conditional evaluations, step by step.",
            "   ",
            "   ⚠️  CRITICAL TEMPORAL SEMANTICS:",
            "   - Each state is labeled as 'BEFORE loop body execution' or 'AFTER loop terminates'",
            "   - Loop invariants must hold at the START of each iteration (BEFORE body executes)",
            "   - When checking variable relationships, use values BEFORE the loop body executes",
            "   ",
            "   Example: If w and z are equal BEFORE each iteration's body executes,",
            "            then 'w == z' is a valid invariant, even if they differ AFTER execution."
        ]
        
        # --- Part 2: Process and Format Samples (with limits to avoid token overflow) ---
        
        # Limit the number of samples to avoid token overflow
        limited_samples = self.sample_contents[:max_samples]
        total_samples = len(self.sample_contents)
        
        if total_samples > max_samples:
            output_lines.append(f"\n   Note: Showing {max_samples} out of {total_samples} execution groups to avoid token overflow.")
        
        for sample_idx, sample in enumerate(limited_samples):
            loop_key = list(sample.keys())[0]
            conditions = sample[loop_key]
            
            # Limit traces per sample
            if len(conditions) > max_traces_per_sample:
                # Keep first few and last few traces
                keep_first = max_traces_per_sample // 2
                keep_last = max_traces_per_sample - keep_first
                limited_conditions = conditions[:keep_first] + conditions[-keep_last:]
                output_lines.append(f"\n[TRACE {sample_idx + 1}] (showing {len(limited_conditions)} out of {len(conditions)} traces)")
                unrolled_flow = self._unroll_trace(limited_conditions)
            else:
                output_lines.append(f"\n[TRACE {sample_idx + 1}]")
                unrolled_flow = self._unroll_trace(conditions)
            
            # Add the multi-line flow block
            output_lines.append(unrolled_flow)
            
        output_lines.append("\n--- END OF DATA ---")
        
        return "\n".join(output_lines)

# --- 示例使用 (Demonstration) ---

if __name__ == '__main__':
    # 示例输入数据
    SAMPLE_CONTENTS: List[Dict[str, List[str]]] = [
        {'0': ['x == 1 && y == 0', 'x == 1 && y == 1 && \\at(y, Pre) < 100000']},
        {'0': ['x == 1 && y == 0', 'x == 1 && y == 0', 'x == 1 && y == 0', 'x == 1 && y == 1 && \\at(y, Pre) < 100000']},
        {'0': ['x == 1 && y == 0', 'x == 1 && y == 1 && \\at(y, Pre) < 100000', 'x == 1 && y == 1 && \\at(y, Pre) < 100000', 'x == 1 && y == 1 && \\at(y, Pre) < 100000']}
    ]

    # 假设的循环上下文数据
    LOOP_SNIPPET = (
        "while (i < N) {\n"
        "    if (x == 1) { y++; }\n"
        "    else { x++; }\n"
        "}"
    )
    PRE_COND = "Initial state: i=0, N=100, x=1, y=0"
    TRANSITION_REL = "y@last < 100000 && (x == x@last + y@last) * (y == y@last + 1)"


    formatter = PromptFormatter(
        sample_contents=SAMPLE_CONTENTS,
        loop_code_snippet=LOOP_SNIPPET,
        pre_condition=PRE_COND,
        transition_relation=TRANSITION_REL
    )

    formatted_text = formatter.full_prompt()

    print("-" * 80)
    print("Formatted Output for LLM (Final, Corrected):")
    print("-" * 80)
    print(formatted_text)
    print("-" * 80)