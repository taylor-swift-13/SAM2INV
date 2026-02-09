#!/usr/bin/env python3
"""
Debug script to understand _replace_loop_content behavior
"""
import re
import logging

# Setup logging
logging.basicConfig(level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class DebugInvariantGenerator:
    """Minimal version of InvariantGenerator for debugging"""
    
    def _replace_loop_content(self, code: str, new_loop_content: str, loop_idx: int) -> str:
        """
        Replace loop content in code (aligned with ASGSE's update_loop_content)
        """
        # Find all for or while loop positions
        loop_pattern = r'\b(for|while)\s*\([^)]*\)\s*{'
        matches = list(re.finditer(loop_pattern, code))
        
        print(f"\n=== DEBUG: Found {len(matches)} loop(s) ===")
        for i, m in enumerate(matches):
            print(f"  Loop {i}: start={m.start()}, end={m.end()}, match='{m.group()}'")
        
        if loop_idx >= len(matches):
            logger.warning(f"Loop index {loop_idx} out of range (found {len(matches)} loops)")
            return code
        
        # Get the target loop match
        match = matches[loop_idx]
        loop_start = match.start()
        
        print(f"\n=== DEBUG: Targeting loop {loop_idx} ===")
        print(f"  loop_start (match.start()) = {loop_start}")
        print(f"  match.end() = {match.end()}")
        
        # Find the matching closing brace for the loop
        brace_count = 0
        loop_end = match.end()
        end_index = loop_end
        code_list = list(code)
        
        print(f"\n=== DEBUG: Finding matching closing brace ===")
        print(f"  Starting at index {end_index}")
        
        while end_index < len(code_list) and brace_count >= 0:
            char = code_list[end_index]
            if char == '{':
                brace_count += 1
                print(f"    Index {end_index}: found '{{', brace_count={brace_count}")
            elif char == '}':
                brace_count -= 1
                print(f"    Index {end_index}: found '}}', brace_count={brace_count}")
            end_index += 1
        
        print(f"\n=== DEBUG: Replacement boundaries ===")
        print(f"  loop_start = {loop_start}")
        print(f"  end_index = {end_index}")
        print(f"  Characters before loop: '{code[:loop_start]}'")
        print(f"  Characters being replaced: '{code[loop_start:end_index]}'")
        print(f"  Characters after loop: '{code[end_index:]}'")
        
        # Replace loop content (aligned with ASGSE)
        updated_code = (
            ''.join(code_list[:loop_start]) +  # Part before loop
            new_loop_content +                  # Replaced loop content with template
            ''.join(code_list[end_index:])      # Part after loop
        )
        
        return updated_code


def main():
    # Test Case 1 code
    original_code = '''/*@ requires a>=n && n==0;*/
int main1(int a,int n){
  int x,y,z;
  x=0;
  y=1;
  z=6;
  while(n<=a){
       n=n+1;
       x=x+y;
       y=y+z;
       z=z+6;
  }
  /*@ assert (n==a+1) && (y == 3*n*n + 3*n + 1) && (x == n*n*n) && (z == 6*n + 6);*/
}'''

    # Template with PLACE_HOLDER
    template_code = '''/*@
  loop invariant PLACE_HOLDER;
*/
while(n<=a){
     n=n+1;
     x=x+y;
     y=y+z;
     z=z+6;
}'''

    print("="*80)
    print("ORIGINAL CODE:")
    print("="*80)
    print(original_code)
    print()
    
    print("="*80)
    print("TEMPLATE CODE (new_loop_content):")
    print("="*80)
    print(template_code)
    print()
    
    # Create debug generator and run replacement
    gen = DebugInvariantGenerator()
    result = gen._replace_loop_content(original_code, template_code, loop_idx=0)
    
    print("\n" + "="*80)
    print("RESULT AFTER _replace_loop_content:")
    print("="*80)
    print(result)
    print()
    
    # Analyze the result
    print("="*80)
    print("ANALYSIS:")
    print("="*80)
    
    # Check if template annotation is in the right place
    if "/*@\n  loop invariant PLACE_HOLDER;" in result:
        # Find the position
        pos = result.find("/*@\n  loop invariant PLACE_HOLDER;")
        print(f"Template annotation found at position {pos}")
        
        # Show context around the annotation
        start = max(0, pos - 50)
        end = min(len(result), pos + 100)
        print(f"\nContext around annotation:")
        print("-"*40)
        print(result[start:end])
        print("-"*40)
    
    # Check for common issues
    if result.count("while(n<=a)") > 1:
        print("\n⚠ WARNING: Multiple 'while(n<=a)' found - loop may have been duplicated!")
    
    if "int x,y,z;" not in result:
        print("\n⚠ WARNING: Variable declarations lost!")
    
    if "/*@ assert" not in result:
        print("\n⚠ WARNING: Assert comment lost!")


if __name__ == "__main__":
    main()
