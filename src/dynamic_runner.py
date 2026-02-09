import tempfile
import subprocess
import os
from typing import Optional

def execute_c_code(c_code_string: str) -> str:
    """
    将 C 语言代码字符串保存到临时文件，使用 GCC 编译，然后执行。

    参数:
    - c_code_string: 完整的 C 语言源代码字符串。

    返回:
    - 程序执行结果的输出字符串，或编译/运行错误信息。
    """
    
    # C 语言的硬编码参数
    compiler_command = 'gcc'
    executable_name = '.out' # 编译后的可执行文件名称后缀
    language_extension = '.c' # 源代码的文件扩展名
    
    source_filename: Optional[str] = None
    executable_path: Optional[str] = None
    
    try:
        # 1. 创建临时文件路径并写入代码
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=language_extension) as tmp_file:
            tmp_file.write(c_code_string)
            source_filename = tmp_file.name

        # 确定可执行文件的路径，与源文件放在同一目录下
        executable_path = os.path.splitext(source_filename)[0] + executable_name

        print(f"✅ 源代码已保存到: {source_filename}")

        # 2. 编译代码
        compile_command = [compiler_command, source_filename, '-o', executable_path]
        print(f"⏳ 正在执行编译: {' '.join(compile_command)}")
        
        # check=True: 如果编译失败 (返回码非 0) 会抛出异常
        subprocess.run(
            compile_command, 
            check=True, 
            capture_output=True, 
            text=True,
            # 编译时间限制
            timeout=5
        ) 
        print("🎉 编译成功!")
        
        # 3. 运行代码
        run_command = [executable_path]
        print(f"⏳ 正在执行程序: {' '.join(run_command)}")
        
        # 执行程序，获取输出
        result = subprocess.run(
            run_command, 
            capture_output=True, 
            text=True, 
            # 运行时间限制
            timeout=10
        )
        
        # 4. 返回标准输出
        return result.stdout.strip()
        
    except subprocess.CalledProcessError as e:
        # 编译或运行失败
        return (f"❌ 编译或运行失败！\n"
                f"--- 错误详情 ---\n"
                f"STDOUT:\n{e.stdout}\n"
                f"STDERR:\n{e.stderr.strip()}")
    except FileNotFoundError:
        return f"❌ 编译器命令 '{compiler_command}' 未找到。请检查您的系统环境PATH设置。"
    except subprocess.TimeoutExpired:
        return "❌ 程序执行超时（超过10秒）。"
    except Exception as e:
        return f"❌ 发生意外错误: {e}"
    finally:
        # 确保清理临时文件
        if source_filename and os.path.exists(source_filename):
            os.remove(source_filename)
            print(f"🧹 已清理源代码: {source_filename}")
        if executable_path and os.path.exists(executable_path):
            os.remove(executable_path)
            print(f"🧹 已清理可执行文件: {executable_path}")

# --- 示例：运行一个简单的 C 程序 ---

if __name__ == "__main__":
    c_code = """
#include <stdio.h>

int main() {
    int sum = 0;
    for (int i = 1; i <= 5; i++) {
        sum += i;
    }
    printf("The sum is: %d\\n", sum);
    return 0;
}
"""

    print("--- 准备执行 C 代码 ---")
    print(c_code.strip())
    print("------------------------\n")
    
    execution_result = execute_c_code(c_code)
    
    print("\n--- 最终运行结果 (返回给调用方) ---")
    print(execution_result)
    print("-----------------------------------")
    
    # 示例：运行一个会编译失败的代码
    print("\n--- 示例：编译失败的代码 ---")
    error_code = """
#include <stdio.h>
int main() {
    prinntf("Hello"); // 拼写错误
    return 0;
}
"""
    error_result = execute_c_code(error_code)
    print(error_result)
