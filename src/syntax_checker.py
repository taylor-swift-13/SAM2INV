import subprocess
import argparse
from run_dirs import resolve_verified_output_path

class SyntaxChecker:
    def __init__(self):
        self.syntax_msg = ""  # Used to store all output content

    def parse_args(self):
        """Set up command line argument parser"""
        parser = argparse.ArgumentParser(description="Run Frama-C WP on a C file.")
        parser.add_argument('file_name', help="Path to the C file to analyze")
        return parser.parse_args()

    def _save_verified_file(self, file_path):
        """保存 Frama-C 验证的文件到 output 目录"""
        try:
            # 读取文件内容
            with open(file_path, 'r') as f:
                file_content = f.read()
            
            # 统一保存路径（避免回落到 output 根目录）
            output_path = resolve_verified_output_path(file_path)
            
            # 保存文件
            with open(output_path, 'w') as f:
                f.write(file_content)
            
        except Exception as e:
            print(f"[DEBUG] Failed to save verified file: {e}")

    def run(self, file_name=None):
        """Run Frama-C WP command and process output"""
        if file_name is None:
            # If no file_name passed, get from command line arguments
            args = self.parse_args()
            file_path = args.file_name
        else:
            # If file_name passed, use it directly
            file_path = file_name

        # 保存文件到 output 目录（无论成功或失败）
        self._save_verified_file(file_path)

        # Generate WP verification command
        wp_command = [
            "frama-c",
            "-wp",
            "-wp-print",
            "-wp-timeout",
            "10",
            file_path
        ]

        try:
            # Use subprocess.run to execute command and capture output
            result = subprocess.run(wp_command, capture_output=True, text=True)
            
            # Check both stdout and stderr for syntax errors
            output = result.stdout + result.stderr
            
            # Check for syntax errors in the output
            if 'syntax error' in output.lower() or 'parse error' in output.lower() or result.returncode != 0:
                self.syntax_msg = "syntax Error\n" + output[:1000]  # Store error information in syntax_msg
            else:
                self.syntax_msg = "syntax Correct"
        except Exception as e:
            # If command execution fails, capture error information
            self.syntax_msg = "syntax Error\n" + str(e)  # Store error information in syntax_msg


if __name__ == "__main__":
    checker = SyntaxChecker()
    checker.run()
