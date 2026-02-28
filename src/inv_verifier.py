"""
简洁的不变量验证器
参考 ASGSE 的实现，但更简洁
"""
import subprocess
import re
import logging
from typing import List, Tuple, Optional
from run_dirs import resolve_verified_output_path

class InvariantVerifier:
    """验证 ACSL 不变量的正确性"""
    
    def __init__(self, logger: Optional[logging.Logger] = None):
        self.logger = logger or logging.getLogger(__name__)
        self.syntax_error = ''
        self.validation_errors = []
        self.verify_errors = []
        self.validate_result = []
        self.verify_result = []
    
    def check_syntax(self, c_file_path: str) -> bool:
        """检查 ACSL 语法错误"""
        try:
            # 保存文件到 output 目录（无论成功或失败）
            self._save_verified_file(c_file_path)
            
            result = subprocess.run(
                ['frama-c', '-wp', '-wp-no-color', '-wp-no-simpl', c_file_path],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # 检查是否有语法错误
            if 'syntax error' in result.stdout.lower() or 'parse error' in result.stdout.lower():
                # 提取错误信息
                error_match = re.search(r'(error|warning):\s*(.+?)(?:\n|$)', result.stdout, re.IGNORECASE)
                if error_match:
                    self.syntax_error = error_match.group(2).strip()
                else:
                    self.syntax_error = result.stdout[:200]  # 取前200字符
                return False
            
            self.syntax_error = ''
            return True
            
        except subprocess.TimeoutExpired:
            self.syntax_error = 'Verification timeout'
            return False
        except Exception as e:
            self.syntax_error = f'Syntax check failed: {str(e)}'
            return False
    
    def _save_verified_file(self, c_file_path: str):
        """保存 Frama-C 验证的文件到 output 目录"""
        try:
            # 读取文件内容
            with open(c_file_path, 'r') as f:
                file_content = f.read()
            
            # 统一保存路径（避免回落到 output 根目录）
            output_path = resolve_verified_output_path(c_file_path)
            
            # 保存文件
            with open(output_path, 'w') as f:
                f.write(file_content)
            
        except Exception as e:
            if self.logger:
                self.logger.debug(f"Failed to save verified file: {e}")
    
    def verify_invariants(self, c_file_path: str) -> Tuple[bool, bool]:
        """
        验证不变量
        
        Returns:
            (syntax_valid, semantic_valid): 语法有效性，语义有效性
        """
        if not self.check_syntax(c_file_path):
            return False, False
        
        try:
            # 运行 Frama-C WP 进行验证
            cmd = [
                'frama-c', '-wp', '-wp-print',
                '-wp-timeout', '10',
                '-wp-prover', 'z3',
                c_file_path
            ]
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            # 解析验证结果
            return self._parse_verification_result(result.stdout)
            
        except subprocess.TimeoutExpired:
            self.logger.warning("Verification timeout")
            return True, False
        except Exception as e:
            self.logger.error(f"Verification failed: {e}")
            return True, False
    
    def _parse_verification_result(self, output: str) -> Tuple[bool, bool]:
        """解析 Frama-C 的输出结果"""
        self.validate_result = []
        self.verify_result = []
        self.validation_errors = []
        self.verify_errors = []
        
        # 提取不变量验证结果
        inv_pattern = r'(Goal (?:Establishment|Preservation) of Invariant[^\n]*\n(?:[^\n]*\n)*?)(?:Valid|Unknown|Failed)'
        inv_matches = list(re.finditer(inv_pattern, output))
        
        for i in range(0, len(inv_matches), 2):
            if i + 1 < len(inv_matches):
                est_match = inv_matches[i]
                pres_match = inv_matches[i + 1]
                
                est_valid = 'Valid' in est_match.group(0)
                pres_valid = 'Valid' in pres_match.group(0)
                
                self.validate_result.append(est_valid and pres_valid)
                
                if not est_valid or not pres_valid:
                    error_msg = est_match.group(1) + pres_match.group(1)
                    self.validation_errors.append(error_msg[:500])  # 限制长度
        
        # 提取后置条件验证结果
        assertion_pattern = r'Goal Assertion[^\n]*\n(?:[^\n]*\n)*?(Valid|Unknown|Failed)'
        assertion_matches = re.finditer(assertion_pattern, output)
        
        for match in assertion_matches:
            self.verify_result.append('Valid' in match.group(0))
            if 'Valid' not in match.group(0):
                self.verify_errors.append(match.group(0)[:500])
        
        # 判断是否全部通过
        all_valid = all(self.validate_result) if self.validate_result else False
        all_verify = all(self.verify_result) if self.verify_result else False
        
        return all_valid, all_verify
    
    def get_error_summary(self) -> str:
        """获取错误摘要"""
        errors = []
        
        if self.syntax_error:
            errors.append(f"Syntax Error: {self.syntax_error}")
        
        if self.validation_errors:
            errors.append(f"Invariant Validation Errors: {len(self.validation_errors)}")
            for i, err in enumerate(self.validation_errors[:3], 1):  # 只显示前3个
                errors.append(f"  {i}. {err[:100]}...")
        
        if self.verify_errors:
            errors.append(f"Postcondition Verification Errors: {len(self.verify_errors)}")
            for i, err in enumerate(self.verify_errors[:3], 1):
                errors.append(f"  {i}. {err[:100]}...")
        
        return "\n".join(errors) if errors else "No errors"
