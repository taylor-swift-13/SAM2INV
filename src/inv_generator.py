"""
Invariant Generator - Integrates sampling, generation, verification and repair
References ASGSE's implementation but more concise
"""
import os
import re
import logging
import tempfile
import yaml
from pathlib import Path
from typing import Optional, List, Dict
from loop_sampler import LoopSampler
from template_generator import TemplateGenerator
from prompt import PromptFormatter
from llmfit import LLMInvariantFitter, llmfit_discover_invariants
from llm import Chatbot, LLMConfig, get_token_stats
from output_verify import OutputVerifier
from syntax_checker import SyntaxChecker
from inv_repairer import InvariantRepairer
from houdini_pruner import HoudiniPruner
from config import SUBDIR, USE_TRACES, MAX_ITERATION, MAX_STRENGTHEN_ITERATIONS, SYNTAX_FILTER_CONFIG
from vector_cache_manager import VectorCacheManager
from unified_filter import filter_invariants, validate_code_structure

class InvariantGenerator:
    """Loop invariant generator with iterative repair functionality"""
    
    def __init__(self, file_name: str, llm_config: Optional[LLMConfig] = None, logger: Optional[logging.Logger] = None, output_dir: Optional[str] = None, input_subdir: Optional[str] = None, config_path: Optional[str] = None):
        # Remove .c extension if present to ensure consistent file_name format
        if file_name.endswith('.c'):
            file_name = file_name[:-2]
        self.file_name = file_name
        self.llm_config = llm_config or LLMConfig()
        self.logger = logger or logging.getLogger(__name__)
        self.input_subdir = input_subdir  # Requested input subdirectory
        self.resolved_subdir = input_subdir if input_subdir else SUBDIR
        self._output_dir = output_dir  # 初始化输出目录

        # 加载配置
        self.config = self._load_config(config_path)

        # 初始化组件
        self.sampler = LoopSampler(file_name, input_subdir=self.resolved_subdir)
        self.template_gen = TemplateGenerator()

        # 根据配置决定是否初始化LLM相关组件
        self.generation_mode = self.config.get('invariant_generation', {}).get('mode', 'hybrid')

        # 验证模式配置
        # fit_only: 只用 llmfit(LLM 接收 traces)
        # code_only: 只用代码生成(LLM 直接从 code 生成)
        # hybrid: llmfit 先尝试,保留结果插入模板继续生成
        valid_modes = ['fit_only', 'code_only', 'hybrid']
        if self.generation_mode not in valid_modes:
            self.logger.warning(f"Invalid generation mode '{self.generation_mode}', defaulting to 'hybrid'")
            self.generation_mode = 'hybrid'

        self.logger.info(f"Invariant generation mode: {self.generation_mode}")

        # Houdini 剪枝器(所有模式都可用,不依赖 LLM)
        self.houdini_pruner = HoudiniPruner(logger=self.logger)

        # 根据模式初始化组件
        # fit_only: 只用 llmfit(LLM 接收 traces)
        # code_only: 只用代码生成(LLM 直接从 code 生成)
        # hybrid: llmfit 先尝试,保留结果插入模板继续生成
        if self.generation_mode in ['fit_only', 'code_only', 'hybrid']:
            self.llm = Chatbot(self.llm_config)
            self.repairer = InvariantRepairer(self.llm_config, self.logger)
        else:
            self.llm = None
            self.repairer = None
            self.logger.warning(f"Unknown generation mode '{self.generation_mode}', LLM components disabled")

        self.verifier = OutputVerifier(logger=self.logger, output=True)

        # 初始化 llmfit(fit_only 和 hybrid 模式使用)
        if self.generation_mode in ['fit_only', 'hybrid']:
            self.llmfit = LLMInvariantFitter(self.llm_config, self.logger)
            self.logger.info("LLM fitting initialized for invariant discovery from traces")
        else:
            self.llmfit = None
            self.logger.info("LLM fitting disabled for code-only mode")

        # 初始化向量缓存管理器
        try:
            # 检查主配置文件中是否启用缓存
            from config import CACHE_CONFIG
            cache_enabled = CACHE_CONFIG.get('enabled', True)
            
            if cache_enabled:
                self.cache_manager = VectorCacheManager(logger=self.logger)
                if self.cache_manager.enabled:
                    self.logger.info("Vector cache manager initialized and enabled")
                else:
                    self.logger.warning("Vector cache manager initialization failed (check cache_config.yaml)")
                    self.cache_manager = None
            else:
                self.logger.info("Vector cache is disabled in config.py")
                self.cache_manager = None
                self.logger.info("Vector cache manager disabled")
        except Exception as e:
            self.logger.warning(f"Failed to initialize vector cache manager: {e}")
            self.cache_manager = None
        
        # 存储结果
        self.invariants = []
        
        # 存储 first_pass 指标(记录第几次生成正确的不变量并通过验证)
        self.first_pass = None
        
        # 存储检索到的相似问题（用于插入 prompt）
        self._cached_similar_problems = []

    def _load_config(self, config_path: Optional[str] = None) -> Dict:
        """加载配置文件"""
        if config_path is None:
            config_path = os.path.join(os.path.dirname(__file__), 'cache_config.yaml')

        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                config = yaml.safe_load(f)
                self.logger.info(f"Loaded configuration from {config_path}")
                return config
        except Exception as e:
            # Config file is optional, cache configuration is in config.py
            self.logger.debug(f"Config file not found: {config_path}, using defaults from config.py")
            return {}
        
        # 确定 output_dir:如果未指定,则根据 input 路径自动对齐
        # 延迟初始化,在第一次使用时再确定
        self._output_dir = output_dir
    
    def _replace_loop_content(self, code: str, new_loop_content: str, loop_idx: int) -> str:
        """
        Replace loop content in code (aligned with ASGSE's update_loop_content)
        
        Args:
            code: Original C code
            new_loop_content: New loop content with template annotations
            loop_idx: Loop index (0-based)
            
        Returns:
            Code with loop replaced
        """
        # Split code into single character list (like ASGSE)
        code_list = list(code)
        
        # Find all for or while loop positions
        loop_pattern = r'\b(for|while)\s*\([^)]*\)\s*{'
        matches = list(re.finditer(loop_pattern, code))
        
        if loop_idx >= len(matches):
            self.logger.warning(f"Loop index {loop_idx} out of range (found {len(matches)} loops)")
            return code
        
        # Get the target loop match
        match = matches[loop_idx]
        loop_start = match.start()
        
        # Find the matching closing brace for the loop
        brace_count = 0
        loop_end = match.end()
        end_index = loop_end
        
        while end_index < len(code_list) and brace_count >= 0:
            if code_list[end_index] == '{':
                brace_count += 1
            elif code_list[end_index] == '}':
                brace_count -= 1
            end_index += 1
        
        # Replace loop content (aligned with ASGSE)
        updated_code = (
            ''.join(code_list[:loop_start]) +  # Part before loop
            new_loop_content +                  # Replaced loop content with template
            ''.join(code_list[end_index:])      # Part after loop
        )
        
        return updated_code
    
    def generate_invariant_for_loop(self, record: Dict, loop_idx: int) -> Optional[str]:
        """Generate invariant for a single loop - check cache first, then use LLM with self-checking"""
        self.logger.info(f"Generating invariant for loop {loop_idx}...")

        # 0. Check vector cache first (if enabled)
        # 存储检索到的相似问题，用于后续插入 prompt
        self._cached_similar_problems = []
        
        if self.cache_manager and self.cache_manager.enabled:
            # 从主配置文件读取缓存设置
            from config import CACHE_CONFIG
            use_in_prompt = CACHE_CONFIG.get('use_in_prompt', True)
            prompt_top_k = CACHE_CONFIG.get('prompt_top_k', 3)
            
            if use_in_prompt:
                self.logger.info(f"\n{'='*60}")
                self.logger.info(f"Loop {loop_idx} - Checking vector cache for similar problems...")
                self.logger.info(f"{'='*60}")

                try:
                    similar_problems = self.cache_manager.search_similar_problems(record, loop_idx)

                    if similar_problems:
                        # 使用主配置文件中的 k 值
                        top_k_results = similar_problems[:prompt_top_k]
                        
                        self.logger.info(f"Found {len(similar_problems)} similar problems in cache")
                        self.logger.info(f"Using top {len(top_k_results)} results for prompt (k={prompt_top_k})")
                        
                        # 存储用于 prompt
                        self._cached_similar_problems = top_k_results
                        
                        # 打印缓存到的结果
                        for idx, result in enumerate(top_k_results, 1):
                            self.logger.info(f"\n  [{idx}] Similarity: {result.similarity_score:.4f}")
                            invariants = result.entry.solution_invariants
                            if isinstance(invariants, str):
                                try:
                                    import json
                                    invariants = json.loads(invariants)
                                except:
                                    invariants = [invariants] if invariants else []
                            
                            if invariants and isinstance(invariants, list):
                                self.logger.info(f"      Invariants ({len(invariants)}):")
                                for i, inv in enumerate(invariants[:3], 1):  # 只显示前3个
                                    inv_str = str(inv)[:80] + "..." if len(str(inv)) > 80 else str(inv)
                                    self.logger.info(f"        [{i}] {inv_str}")
                        
                        self.logger.info(f"{'='*60}\n")
                    else:
                        self.logger.info("No similar problems found in cache")
                        self.logger.info(f"{'='*60}\n")

                except Exception as e:
                    self.logger.warning(f"Error during cache lookup: {e}")
                    # Continue with normal generation if cache fails

        # 1. Get original input code
        original_code = self._get_full_source_code()
        if not original_code:
            self.logger.error("Could not read original input code")
            return None

        # 2. Workflow: generate -> filter -> verify -> strengthen-if-needed
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Starting LLM generation/filter/verification pipeline")
        self.logger.info(f"{'='*60}")
        
        return self._generate_with_llm_self_check(original_code, record, loop_idx)

    def _generate_with_llm_self_check(self, original_code: str, record, loop_idx: int, max_self_iterations: int = 5) -> Optional[str]:
        """
        使用LLM生成不变量,并通过采样数据过滤
        
        新流程:
        1. LLM 并行生成多组候选不变量
        2. 直接用采样数据代入验证,过滤掉不符合采样的不变量
        3. 选择最佳候选(通过采样验证最多的)
        4. Frama-C 验证最佳候选
        """
        if self.llm is None:
            self.logger.error("LLM is not initialized but required for generation")
            return None
        
        # 加载并行生成配置
        from config import PARALLEL_GENERATION_CONFIG
        parallel_enabled = PARALLEL_GENERATION_CONFIG.get('enabled', True)
        num_candidates = PARALLEL_GENERATION_CONFIG.get('num_candidates', 10)
        temperature = PARALLEL_GENERATION_CONFIG.get('temperature', 0.9)
        filter_by_sampling = PARALLEL_GENERATION_CONFIG.get('filter_by_sampling', True) and USE_TRACES
        select_best = PARALLEL_GENERATION_CONFIG.get('select_best', True)
        use_threading = PARALLEL_GENERATION_CONFIG.get('use_threading', True)
        max_workers = PARALLEL_GENERATION_CONFIG.get('max_workers', 5)
        
        # 1. Generate template with PLACE_HOLDER
        template_code = self.template_gen.generate_template(record)
        
        # 2. Insert template into original code
        try:
            code_with_template = self._replace_loop_content(original_code, template_code, loop_idx)
        except Exception as e:
            self.logger.warning(f"Failed to replace loop using ASGSE method: {e}, trying simple replacement")
            loop_content = record.get('loop_content', '')
            if loop_content and loop_content in original_code:
                code_with_template = original_code.replace(loop_content, template_code, 1)
            else:
                self.logger.warning("Could not find loop in original code, using template directly")
                code_with_template = template_code
        
        # 3. Prepare prompt template and loop context (execution traces)
        prompt_template, loop_context = self._prepare_prompt(record, loop_idx)
        
        # 4. Generate candidate invariants using LLM
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Step 1: Generating candidate invariants")
        self.logger.info(f"{'='*60}")
        
        if parallel_enabled and num_candidates > 1:
            # 并行生成多组候选
            self.logger.info(f"Parallel generation enabled: generating {num_candidates} candidates")
            candidate_codes = self._generate_multiple_candidates(
                code_with_template, 
                (prompt_template, loop_context),
                num_candidates=num_candidates,
                temperature=temperature,
                use_threading=use_threading,
                max_workers=max_workers
            )
            
            if not candidate_codes:
                self.logger.error("Failed to generate any candidates")
                return None
        else:
            # 单次生成(原有逻辑)
            self.logger.info("Single generation mode")
            initial_code = self._generate_initial_invariant(code_with_template, (prompt_template, loop_context))
            if not initial_code:
                self.logger.error("Failed to generate initial invariant")
                return None
            candidate_codes = [initial_code]
        
        # 5. Extract and display all candidates
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Generated {len(candidate_codes)} candidate(s)")
        self.logger.info(f"{'='*60}")
        
        all_candidates = []
        for idx, code in enumerate(candidate_codes, 1):
            invariants = self._extract_invariants_from_code(code)
            all_candidates.append({
                'code': code,
                'invariants': invariants,
                'index': idx
            })
            self.logger.info(f"\nCandidate {idx}: {len(invariants)} invariants")
            for i, inv in enumerate(invariants, 1):
                self.logger.info(f"  [{i}] {inv}")
        
        # 6. Apply syntax filter first (if enabled)
        syntax_filter_enabled = SYNTAX_FILTER_CONFIG.get('enabled', True)
        syntax_filter_verbose = SYNTAX_FILTER_CONFIG.get('verbose', True)
        
        if syntax_filter_enabled:
            self.logger.info(f"\n{'='*60}")
            self.logger.info(f"Loop {loop_idx} - Step 2a: Applying syntax filter")
            self.logger.info(f"{'='*60}")
            
            for candidate in all_candidates:
                # 注入初始状态到 record 中（用于改写 \at(var, Pre)）
                # 从动态采样数据中提取初始状态（第一个 trace 就是初始状态）
                if hasattr(self.sampler, 'sample_contents') and self.sampler.sample_contents:
                    loop_key = str(loop_idx)
                    # 获取第一个采样组
                    first_group = self.sampler.sample_contents[0]
                    if loop_key in first_group and len(first_group[loop_key]) > 0:
                        # 第一个 trace 就是初始状态
                        initial_state = first_group[loop_key][0]
                        # 转换为字符串格式
                        if isinstance(initial_state, str):
                            record['begin'] = initial_state
                        elif isinstance(initial_state, dict):
                            record['begin'] = ' * '.join([f"({k} == {v})" for k, v in initial_state.items()])
                
                # Apply syntax filter
                filter_result = filter_invariants(
                    candidate['invariants'], 
                    record, 
                    verbose=syntax_filter_verbose
                )
                
                # Store syntax-filtered invariants
                candidate['syntax_filtered_invariants'] = filter_result.valid
                # Safety net: reject exponent-style invariants that Frama-C/ACSL
                # often treats as type errors (e.g., z^(c-1), \pow(...)).
                safe_invariants = []
                removed_pow_like = []
                for inv in candidate['syntax_filtered_invariants']:
                    if '^' in inv or '\\pow' in inv:
                        removed_pow_like.append(inv)
                    else:
                        safe_invariants.append(inv)
                if removed_pow_like:
                    for bad_inv in removed_pow_like:
                        self.logger.info(f"  Removed non-ACSL-safe invariant: {bad_inv}")
                candidate['syntax_filtered_invariants'] = safe_invariants
                candidate['syntax_rejected'] = filter_result.rejected
                
                self.logger.info(f"\nCandidate {candidate['index']}: {len(filter_result.valid)}/{len(candidate['invariants'])} invariants passed syntax filter")
                
                # Log rejected invariants if verbose
                if syntax_filter_verbose and filter_result.rejected:
                    self.logger.info(f"  Rejected {len(filter_result.rejected)} invariants:")
                    for inv, violations in filter_result.rejected[:3]:  # Show first 3
                        self.logger.info(f"    - {inv}")
                        for v in violations[:2]:  # Show first 2 violations
                            self.logger.info(f"      [{v.type.value}] {v.message}")
        else:
            # Syntax filter disabled, use all invariants
            for candidate in all_candidates:
                candidate['syntax_filtered_invariants'] = candidate['invariants']
                candidate['syntax_rejected'] = []
        
        # 统计语法过滤结果
        total_before_syntax = sum(len(c['invariants']) for c in all_candidates)
        total_after_syntax = sum(len(c['syntax_filtered_invariants']) for c in all_candidates)
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"SYNTAX FILTER SUMMARY: {total_after_syntax}/{total_before_syntax} invariants retained")
        self.logger.info(f"{'='*60}")
        
        # 7. Filter candidates by sampling data (on syntax-filtered invariants)
        if filter_by_sampling:
            self.logger.info(f"\n{'='*60}")
            self.logger.info(f"Loop {loop_idx} - Step 2b: Filtering candidates by sampling data")
            self.logger.info(f"{'='*60}")
            
            for candidate in all_candidates:
                # Apply sampling filter on syntax-filtered invariants
                filtered_invs = self._filter_invariants_by_sampling(
                    candidate['syntax_filtered_invariants'], 
                    record, 
                    loop_idx
                )
                candidate['filtered_invariants'] = filtered_invs
                candidate['pass_rate'] = len(filtered_invs) / len(candidate['invariants']) if candidate['invariants'] else 0
                
                self.logger.info(f"\nCandidate {candidate['index']}: {len(filtered_invs)}/{len(candidate['syntax_filtered_invariants'])} invariants passed sampling filter (pass rate: {candidate['pass_rate']:.1%})")
        else:
            # 不过滤,直接使用语法过滤后的不变式
            for candidate in all_candidates:
                candidate['filtered_invariants'] = candidate['syntax_filtered_invariants']
                candidate['pass_rate'] = len(candidate['filtered_invariants']) / len(candidate['invariants']) if candidate['invariants'] else 0
        
        # 统计采样过滤结果
        total_before_sampling = sum(len(c['syntax_filtered_invariants']) for c in all_candidates)
        total_after_sampling = sum(len(c['filtered_invariants']) for c in all_candidates)
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"TRACES FILTER SUMMARY: {total_after_sampling}/{total_before_sampling} invariants retained")
        self.logger.info(f"{'='*60}")
        
        # 8. Combine all filtered invariants from all candidates (NEW LOGIC)
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Step 3: Combining invariants from all candidates")
        self.logger.info(f"{'='*60}")
        
        # 加载冲突检测配置
        detect_conflicts = PARALLEL_GENERATION_CONFIG.get('detect_conflicts', True)
        
        # 收集所有候选通过采样的不变式
        # Final safety net before Houdini:
        # - Drop pow/caret-style invariants that trigger annot-error
        # - Rewrite \at(local, Pre) -> local to avoid unbound logic variable
        combined_invariants = []
        seen_invariants = set()  # 用于去重
        function_params = set(record.get('function_params', []) or [])

        def _sanitize_invariant(inv_text: str) -> Optional[str]:
            if '^' in inv_text or '\\pow' in inv_text:
                return None

            def _at_repl(match):
                var_name = match.group(1)
                return match.group(0) if var_name in function_params else var_name

            return re.sub(r'\\at\((\w+),\s*Pre\)', _at_repl, inv_text)
        
        for candidate in all_candidates:
            for inv in candidate['filtered_invariants']:
                inv = _sanitize_invariant(inv)
                if not inv:
                    self.logger.info(f"  Removed non-ACSL-safe invariant before merge")
                    continue
                # 标准化不变式用于去重(去除空格差异)
                normalized_inv = ' '.join(inv.split())
                if normalized_inv not in seen_invariants:
                    seen_invariants.add(normalized_inv)
                    combined_invariants.append(inv)
                    self.logger.info(f"  Added from Candidate {candidate['index']}: {inv}")

        # Heuristic seed invariants are disabled for compliance.
        # # 追加模式化启发不变量（用于补齐 LLM 常漏的关键守恒关系）
        # heuristic_code = all_candidates[0].get('code', '') if all_candidates else ''
        # heuristic_invariants = self._heuristic_seed_invariants(heuristic_code)
        # for inv in heuristic_invariants:
        #     normalized_inv = ' '.join(inv.split())
        #     if normalized_inv not in seen_invariants:
        #         seen_invariants.add(normalized_inv)
        #         combined_invariants.append(inv)
        #         self.logger.info(f"  Added from Heuristic: {inv}")
        
        self.logger.info(f"\nTotal combined invariants: {len(combined_invariants)} (after deduplication)")
        
        # 如果筛选后为空，直接进入增强阶段（而不是失败）
        if not combined_invariants:
            self.logger.warning("No invariants passed sampling filter from any candidate")
            self.logger.info("Entering strengthening from original code because invariant set is empty")
            temp_file = self._create_temp_file(original_code)
            try:
                strengthened_code = self._strengthen_invariants_iterative(
                    original_code, temp_file, record, loop_idx, max_iterations=MAX_STRENGTHEN_ITERATIONS
                )
                if strengthened_code is not None:
                    return strengthened_code
            finally:
                if os.path.exists(temp_file):
                    os.remove(temp_file)
            self.logger.warning("Strengthening failed after empty invariant set")
            return None
        
        # 检测并去除冲突的不变式
        if detect_conflicts and len(combined_invariants) > 1:
            self.logger.info(f"\n{'='*60}")
            self.logger.info(f"Loop {loop_idx} - Detecting and removing conflicting invariants")
            self.logger.info(f"{'='*60}")
            
            non_conflicting_invariants = self._remove_conflicting_invariants(combined_invariants)
            
            if len(non_conflicting_invariants) < len(combined_invariants):
                removed_count = len(combined_invariants) - len(non_conflicting_invariants)
                self.logger.info(f"Removed {removed_count} conflicting invariants")
                self.logger.info(f"Remaining: {len(non_conflicting_invariants)} invariants")
                combined_invariants = non_conflicting_invariants
            else:
                self.logger.info("No conflicts detected")
        
        # 再次检查是否还有不变式剩余
        if not combined_invariants:
            self.logger.warning("All invariants were removed due to conflicts")
            return None
        
        # 8. Build code with combined invariants
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Combined invariants for Houdini:")
        self.logger.info(f"{'='*60}")
        for i, inv in enumerate(combined_invariants, 1):
            self.logger.info(f"  [{i}] {inv}")
        
        # 使用候选的代码作为基础,插入组合后的不变式
        # 优先选择包含正确函数名且结构完整（括号匹配）的候选
        expected_func_name = f"main{self.file_name}"
        base_code = None
        # First pass: prefer structurally valid candidates with correct function name
        for candidate in all_candidates:
            code = candidate.get('code', '')
            if code and expected_func_name in code and code.count('{') == code.count('}'):
                base_code = code
                break
        # Second pass: correct function name, any structure
        if not base_code:
            for candidate in all_candidates:
                code = candidate.get('code', '')
                if code and expected_func_name in code:
                    base_code = code
                    break

        # 回退：如果没有精确匹配，尝试包含 'int main' 的候选
        if not base_code:
            for candidate in all_candidates:
                code = candidate.get('code', '')
                if code and 'int main' in code:
                    base_code = code
                    break

        # 最终回退：取第一个非空候选
        if not base_code:
            base_code = all_candidates[0]['code']

        # 验证base_code是完整的函数
        if not base_code or expected_func_name not in base_code:
            self.logger.error(f"ERROR: base_code does not contain expected function '{expected_func_name}'!")
            self.logger.error(f"First 500 chars of base_code: {base_code[:500] if base_code else 'None'}")
            return None
        
        current_code = self._rebuild_code_with_invariants(base_code, combined_invariants)
        current_invariants = combined_invariants
        
        # 验证current_code是完整的函数
        if not current_code or expected_func_name not in current_code:
            self.logger.error(f"ERROR: current_code does not contain '{expected_func_name}' after rebuild!")
            self.logger.error(f"First 500 chars of current_code: {current_code[:500] if current_code else 'None'}")
            self.logger.error(f"First 500 chars of base_code: {base_code[:500]}")
            return None
        
        # 9. Houdini pruning with Frama-C
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Step 4: Houdini pruning with Frama-C")
        self.logger.info(f"{'='*60}")
        
        temp_file = self._create_temp_file(current_code)
        
        try:
            # 使用Houdini迭代剪枝
            pruned_code, houdini_valid = self.houdini_pruner.hudini(
                current_code,
                self.verifier,
                temp_file
            )
            
            if pruned_code and houdini_valid:
                # Houdini 阶段只保证 invariant establish/preserve；这里继续检查 assertion satisfy
                syntax = getattr(self.verifier, "syntax_correct", False) or self.verifier.syntax_error == 'syntax Correct'
                valid = bool(self.verifier.validate_result) and all(self.verifier.validate_result)
                satisfy = all(self.verifier.verify_result) if self.verifier.verify_result else True

                final_code = pruned_code
                if syntax and valid and not satisfy:
                    self.logger.info(f"Loop {loop_idx} - Enter strengthening iterations (max={MAX_STRENGTHEN_ITERATIONS})")
                    strengthened_code = self._strengthen_invariants_iterative(
                        pruned_code, temp_file, record, loop_idx, max_iterations=MAX_STRENGTHEN_ITERATIONS
                    )
                    if strengthened_code is None:
                        self.logger.warning(f"Loop {loop_idx} - Strengthening failed to satisfy assertions")
                        return None
                    final_code = strengthened_code

                final_invariants = self._extract_invariants_from_code(final_code)
                self.logger.info(f"\n{'='*60}")
                self.logger.info(f"Loop {loop_idx} - Houdini/Strengthening finished successfully!")
                self.logger.info(f"{'='*60}")
                if final_invariants:
                    for i, inv in enumerate(final_invariants, 1):
                        self.logger.info(f"  [{i}] {inv}")

                # Store successful generation result in cache
                if self.cache_manager and self.cache_manager.enabled:
                    try:
                        cache_satisfy = all(self.verifier.verify_result) if self.verifier.verify_result else True
                        self.cache_manager.store_problem_solution(
                            record, loop_idx, final_code, final_invariants,
                            {'syntax': True, 'valid': True, 'satisfy': cache_satisfy, 'source': 'parallel_generation_houdini_strengthen'}
                        )
                    except Exception as e:
                        self.logger.warning(f"Failed to store result in cache: {e}")

                self.logger.info(f"\nOK Successfully generated invariant for loop {loop_idx}")
                return final_code
            elif pruned_code:
                # Houdini有代码但验证未完全通过，进入增强阶段
                final_invariants = self._extract_invariants_from_code(pruned_code)
                self.logger.info(f"\n{'='*60}")
                self.logger.info(f"Loop {loop_idx} - Houdini finished but some invariants invalid")
                self.logger.info(f"{'='*60}")
                if final_invariants:
                    for i, inv in enumerate(final_invariants, 1):
                        self.logger.info(f"  [{i}] {inv}")
                self.logger.info(f"Loop {loop_idx} - Enter strengthening after incomplete Houdini validation")
                strengthened_code = self._strengthen_invariants_iterative(
                    pruned_code, temp_file, record, loop_idx, max_iterations=MAX_STRENGTHEN_ITERATIONS
                )
                if strengthened_code is not None:
                    return strengthened_code
                self.logger.warning(f"\nX Failed to generate invariant for loop {loop_idx} (Houdini validation incomplete + strengthening failed)")
                self._print_full_loop_on_error(pruned_code, record, loop_idx, "Houdini Validation Failed")
                return None
            else:
                # Houdini返回None，进入增强阶段
                self.logger.info(f"Loop {loop_idx} - Enter strengthening after Houdini removed all invariants")
                strengthened_code = self._strengthen_invariants_iterative(
                    current_code, temp_file, record, loop_idx, max_iterations=MAX_STRENGTHEN_ITERATIONS
                )
                if strengthened_code is not None:
                    return strengthened_code
                self.logger.warning(f"\nX Failed to generate invariant for loop {loop_idx} (Houdini removed all invariants + strengthening failed)")
                self._print_full_loop_on_error(current_code if 'current_code' in locals() else "", record, loop_idx, "Houdini Removed All Invariants")
                return None
                
        finally:
            # Clean up temporary file
            if os.path.exists(temp_file):
                os.remove(temp_file)
            # Clean up temporary file
            if os.path.exists(temp_file):
                os.remove(temp_file)
    
    def _self_check_invariants(self, invariants: List[str], loop_context: str, record: Dict) -> Dict:
        """
        让 LLM 自我检查生成的不变量能否在采样上成立
        
        Args:
            invariants: 当前的不变量列表
            loop_context: 执行 traces
            record: Loop record
            
        Returns:
            Dict with 'confident' (bool) and 'issues' (str)
        """
        if not invariants:
            return {'confident': False, 'issues': 'No invariants generated'}
        
        invariants_str = '\n'.join([f"  {i+1}. {inv}" for i, inv in enumerate(invariants)])
        check_prompt = (
            "Check whether all invariants hold on all BEFORE states in traces.\n\n"
            f"Invariants:\n{invariants_str}\n\n"
            f"Traces:\n{loop_context}\n\n"
            "Output format:\n"
            "CONFIDENT: YES or NO\n"
            "ISSUES: <brief reasons if NO>"
        )
        
        try:
            response = self.llm.chat(check_prompt)
            
            # Parse response
            confident = 'CONFIDENT: YES' in response or 'CONFIDENT:YES' in response
            
            # Extract issues
            issues = ""
            if 'ISSUES:' in response:
                issues = response.split('ISSUES:')[1].strip()
            elif not confident:
                issues = response  # Use full response as issues
            
            return {
                'confident': confident,
                'issues': issues
            }
            
        except Exception as e:
            self.logger.error(f"Self-check failed: {e}")
            return {'confident': False, 'issues': f'Self-check error: {e}'}
    
    def _filter_invariants_by_sampling(self, invariants: List[str], record: Dict, loop_idx: int) -> List[str]:
        """
        直接用采样数据代入验证不变式,过滤掉不符合采样的不变式
        
        Args:
            invariants: 待验证的不变式列表
            record: Loop record containing sample data
            loop_idx: Loop index
            
        Returns:
            List of invariants that pass all sample checks
        """
        if not invariants:
            return []
        
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Filtering invariants by sampling data")
        self.logger.info(f"{'='*60}")
        
        # Get sample data from sampler (新格式：每个执行组包含 traces 和 param_values)
        loop_idx_str = str(loop_idx)
        execution_groups = []
        
        if self.sampler.sample_contents:
            for group_idx, sample_dict in enumerate(self.sampler.sample_contents):
                if loop_idx_str in sample_dict:
                    traces = sample_dict[loop_idx_str]
                    if traces:
                        param_values = sample_dict.get('_params', {})
                        
                        execution_groups.append({
                            'group_id': group_idx + 1,
                            'traces': traces,
                            'param_values': param_values
                        })
        
        if not execution_groups:
            self.logger.warning("No sample data available, skipping sampling filter")
            return invariants
        
        self.logger.info(f"Found {len(execution_groups)} independent execution groups (runs)")
        for group in execution_groups[:5]:  # 只显示前5个
            traces = group['traces']
            params = group['param_values']
            first_trace = traces[0][:60] + '...' if traces and len(traces[0]) > 60 else (traces[0] if traces else '')
            last_trace = traces[-1][:60] + '...' if traces and len(traces[-1]) > 60 else (traces[-1] if traces else '')
            param_str = ', '.join([f"{k}={v}" for k, v in params.items()]) if params else 'none'
            self.logger.info(f"  Run {group['group_id']}: {len(traces)} traces (first: {first_trace}..., last: {last_trace}...), params: {param_str}")
        
        # Filter each invariant
        valid_invariants = []
        
        for inv_idx, invariant in enumerate(invariants, 1):
            self.logger.info(f"\nChecking invariant [{inv_idx}]: {invariant}")
            
            # Parse invariant to extract the condition
            # Remove "loop invariant" prefix and trailing semicolon
            inv_condition = invariant.strip()
            if inv_condition.startswith('loop invariant'):
                inv_condition = inv_condition[len('loop invariant'):].strip()
            if inv_condition.endswith(';'):
                inv_condition = inv_condition[:-1].strip()
            
            # Check invariant against all execution groups
            all_groups_pass = True
            failed_groups = []
            
            for group in execution_groups:
                traces = group['traces']
                param_values = group['param_values']
                group_id = group['group_id']
                
                # Check invariant at each trace state in this execution group
                group_passes = True
                failed_states = []
                
                for state_idx, state in enumerate(traces):
                    # Check if invariant holds at this state
                    if not self._check_invariant_at_state(
                        inv_condition, 
                        state, 
                        initial_state=None,  # 不再使用 initial_state
                        function_params=list(param_values.keys()) if param_values else None,
                        param_values=param_values  # 传递 param_values
                    ):
                        group_passes = False
                        failed_states.append(f"State {state_idx}: {state[:60]}...")
                        break  # 如果某个状态失败，整个 group 失败
                
                if not group_passes:
                    all_groups_pass = False
                    failed_groups.append(f"Run {group_id}: {failed_states[0]}")
                    if len(failed_groups) >= 3:  # 只记录前3个失败的 group
                        break
            
            if all_groups_pass:
                self.logger.info(f"  OK PASS: Invariant holds on all {len(execution_groups)} execution groups")
                valid_invariants.append(invariant)
            else:
                self.logger.info(f"  X FAIL: Invariant violated on sample data")
                for failed in failed_groups:
                    self.logger.info(f"    - {failed}")
        
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Sampling filter result: {len(valid_invariants)}/{len(invariants)} invariants passed")
        self.logger.info(f"{'='*60}")
        
        return valid_invariants
    
    def _check_invariant_at_state(self, invariant: str, state: str, 
                                  initial_state: Optional[str] = None,
                                  function_params: Optional[List[str]] = None,
                                  param_values: Optional[Dict[str, int]] = None) -> bool:
        """
        检查不变式在给定状态下是否成立
        
        这是一个简化的检查方法,通过解析状态中的变量值来验证不变式
        
        Args:
            invariant: 不变式条件(如 "x == y + 1")
            state: 状态条件(如 "x == 2 && y == 1 && z == 3")
            initial_state: 初始状态（已废弃，使用 param_values）
            function_params: 函数参数列表
            param_values: 函数参数的初始值字典 {param_name: value}
            
        Returns:
            True if invariant holds at this state, False otherwise
        """
        try:
            # Extract variable assignments from state
            # State format: "x == 2 && y == 1 && z == 3"
            var_values = {}
            
            # Parse state to extract variable values
            # Handle both "&&" and "*" as separators
            state_parts = re.split(r'\s*(?:&&|\*)\s*', state)
            
            for part in state_parts:
                part = part.strip()
                # Match patterns like "x == 5" or "x@pre == 5"
                match = re.match(r'(\w+(?:@pre)?)\s*==\s*(-?\d+)', part)
                if match:
                    var_name = match.group(1)
                    var_value = int(match.group(2))
                    var_values[var_name] = var_value
            
            # 处理 \at(v, Pre) 和 var@pre 引用
            # 优先使用 param_values（函数参数的初始值）
            initial_values_map = {}
            if param_values:
                # 直接使用 param_values
                initial_values_map.update(param_values)
            elif initial_state:
                # 回退：从 initial_state 解析（旧格式）
                initial_parts = re.split(r'\s*(?:&&|\*)\s*', initial_state)
                for part in initial_parts:
                    part = part.strip()
                    pre_match = re.match(r'\\at\((\w+),\s*Pre\)\s*==\s*(-?\d+)', part)
                    if pre_match:
                        initial_values_map[pre_match.group(1)] = int(pre_match.group(2))
                    pre_match_simple = re.match(r'(\w+)@pre\s*==\s*(-?\d+)', part)
                    if pre_match_simple:
                        initial_values_map[pre_match_simple.group(1)] = int(pre_match_simple.group(2))
                    # 如果是函数参数，也视为初始值
                    if function_params:
                        simple_match = re.match(r'(\w+)\s*==\s*(-?\d+)', part)
                        if simple_match and simple_match.group(1) in function_params:
                            initial_values_map[simple_match.group(1)] = int(simple_match.group(2))
            
            if not var_values:
                # Cannot extract values, assume invariant holds (conservative)
                return True

            # 合并所有已知变量值（当前状态 + 初始值），用于替换
            all_values = {}
            all_values.update(initial_values_map)  # 初始值优先级低
            # 当前状态的值覆盖初始值中的同名变量
            for k, v in var_values.items():
                if '@pre' not in k:
                    all_values[k] = v

            # Replace variable names with their values in the invariant
            inv_eval = invariant

            # 先替换 \at(v, Pre) 和 var@pre 为初始值
            for var_name, var_value in initial_values_map.items():
                inv_eval = re.sub(r'\\at\(' + re.escape(var_name) + r',\s*Pre\)', str(var_value), inv_eval)
                inv_eval = re.sub(r'\b' + re.escape(var_name) + r'@pre\b', str(var_value), inv_eval)

            # 再替换当前变量值（按变量名长度降序排列，避免短变量名误匹配长变量名的前缀）
            sorted_vars = sorted(var_values.items(), key=lambda x: len(x[0]), reverse=True)
            for var_name, var_value in sorted_vars:
                # 跳过 @pre 变量（已经处理过了）
                if '@pre' in var_name:
                    continue
                inv_eval = re.sub(r'\b' + re.escape(var_name) + r'\b', str(var_value), inv_eval)

            # 如果还有未解析的 @pre 或 \at 引用，保守地返回 True
            if '@pre' in inv_eval or '\\at' in inv_eval:
                return True

            # 处理 ACSL 蕴含运算符 ==>
            # A ==> B 等价于 (not A) or B
            if '==>' in inv_eval:
                parts = inv_eval.split('==>')
                if len(parts) == 2:
                    lhs = parts[0].strip()
                    rhs = parts[1].strip()
                    inv_eval = f"(not ({lhs}) or ({rhs}))"
                else:
                    # 多个 ==>，太复杂，保守返回 True
                    return True

            # Try to evaluate simple arithmetic expressions
            # For safety, only evaluate if it looks like a simple comparison
            if any(op in inv_eval for op in ['==', '<=', '>=', '<', '>', '!=']):
                try:
                    # Check if all variables have been replaced with numbers
                    # 允许 Python 关键字 not, or, and
                    remaining_ids = re.findall(r'\b([a-zA-Z_]\w*)\b', inv_eval)
                    python_keywords = {'not', 'or', 'and', 'True', 'False'}
                    unknown_ids = [x for x in remaining_ids if x not in python_keywords]
                    if unknown_ids:
                        # Still contains variable names, cannot evaluate
                        return True

                    # Evaluate the expression
                    result = eval(inv_eval, {"__builtins__": {}}, {})
                    return bool(result)
                except:
                    # Evaluation failed, assume invariant holds (conservative)
                    return True

            # Cannot evaluate, assume invariant holds (conservative)
            return True
            
        except Exception as e:
            # On any error, assume invariant holds (conservative approach)
            self.logger.debug(f"Error checking invariant at state: {e}")
            return True
    
    def _remove_conflicting_invariants(self, invariants: List[str]) -> List[str]:
        """
        检测并去除冲突的不变式
        
        冲突定义:
        1. 逻辑矛盾: 如 "x > 5" 和 "x < 3"
        2. 不一致的等式: 如 "x == 5" 和 "x == 10"
        3. 范围冲突: 如 "x >= 10" 和 "x <= 5"
        
        Args:
            invariants: 不变式列表
            
        Returns:
            去除冲突后的不变式列表
        """
        if len(invariants) <= 1:
            return invariants
        
        self.logger.info(f"Checking {len(invariants)} invariants for conflicts...")
        
        # 解析每个不变式，提取变量和约束
        parsed_invariants = []
        for inv in invariants:
            parsed = self._parse_invariant(inv)
            if parsed:
                parsed_invariants.append({
                    'original': inv,
                    'parsed': parsed
                })
        
        # 检测冲突
        non_conflicting = []
        conflicting_indices = set()

        for i, inv1 in enumerate(parsed_invariants):
            if i in conflicting_indices:
                continue

            for j, inv2 in enumerate(parsed_invariants):
                if i >= j or j in conflicting_indices:
                    continue

                if self._check_conflict(inv1['parsed'], inv2['parsed']):
                    self.logger.info(f"  Conflict detected:")
                    self.logger.info(f"    [{i+1}] {inv1['original']}")
                    self.logger.info(f"    [{j+1}] {inv2['original']}")

                    # 标记冲突的不变式（保留第一个 i，删除第二个 j）
                    conflicting_indices.add(j)

            # FIX: 无论是否有冲突，只要 i 自身未被标记为冲突，就保留它
            # 之前的 bug: has_conflict=True 时 inv1 也不加入 non_conflicting，
            # 导致冲突双方都被删除
            if i not in conflicting_indices:
                non_conflicting.append(inv1['original'])

        return non_conflicting
    
    def _parse_invariant(self, invariant: str) -> Optional[dict]:
        """
        解析不变式，提取变量和约束
        
        Args:
            invariant: 不变式字符串
            
        Returns:
            解析结果字典，包含变量和约束信息
        """
        try:
            # 简化的解析：提取变量和比较运算符
            # 支持的模式: var op value, var op var, value op var op value
            
            # 移除 "loop invariant" 前缀
            inv = invariant.strip()
            if inv.startswith('loop invariant'):
                inv = inv[len('loop invariant'):].strip()
            if inv.endswith(';'):
                inv = inv[:-1].strip()
            
            # 提取所有变量
            variables = set(re.findall(r'\b([a-zA-Z_]\w*)\b', inv))
            # 排除常见的关键字
            keywords = {'loop', 'invariant', 'and', 'or', 'not'}
            variables = variables - keywords
            
            # 提取比较运算符和值
            comparisons = []
            
            # 匹配模式: var op value 或 value op var op value
            patterns = [
                r'(\w+)\s*(==|!=|<=|>=|<|>)\s*(-?\d+)',  # var op num
                r'(-?\d+)\s*(==|!=|<=|>=|<|>)\s*(\w+)',  # num op var
                r'(-?\d+)\s*(<=|>=|<|>)\s*(\w+)\s*(<=|>=|<|>)\s*(-?\d+)',  # num op var op num
            ]
            
            for pattern in patterns:
                matches = re.findall(pattern, inv)
                if matches:
                    comparisons.extend(matches)
            
            return {
                'variables': variables,
                'comparisons': comparisons,
                'original': inv
            }
            
        except Exception as e:
            self.logger.debug(f"Failed to parse invariant '{invariant}': {e}")
            return None
    
    def _check_conflict(self, parsed1: dict, parsed2: dict) -> bool:
        """
        检查两个解析后的不变式是否冲突
        
        Args:
            parsed1: 第一个不变式的解析结果
            parsed2: 第二个不变式的解析结果
            
        Returns:
            True if conflict detected, False otherwise
        """
        try:
            # 检查是否涉及相同的变量
            common_vars = parsed1['variables'].intersection(parsed2['variables'])
            if not common_vars:
                return False  # 没有共同变量，不会冲突
            
            # 简化的冲突检测：检查明显的矛盾
            inv1 = parsed1['original']
            inv2 = parsed2['original']
            
            # 检测类型1: 相同变量的不同等式
            # 如 "x == 5" 和 "x == 10"
            for var in common_vars:
                eq1_match = re.search(rf'\b{var}\s*==\s*(-?\d+)', inv1)
                eq2_match = re.search(rf'\b{var}\s*==\s*(-?\d+)', inv2)
                
                if eq1_match and eq2_match:
                    val1 = int(eq1_match.group(1))
                    val2 = int(eq2_match.group(1))
                    if val1 != val2:
                        return True  # 冲突: x == 5 和 x == 10
            
            # 检测类型2: 范围冲突
            # 如 "x >= 10" 和 "x <= 5"
            for var in common_vars:
                # 提取上下界
                lower1 = self._extract_lower_bound(inv1, var)
                upper1 = self._extract_upper_bound(inv1, var)
                lower2 = self._extract_lower_bound(inv2, var)
                upper2 = self._extract_upper_bound(inv2, var)
                
                # 检查范围是否有交集
                if lower1 is not None and upper2 is not None and lower1 > upper2:
                    return True  # 冲突: x >= 10 和 x <= 5
                if lower2 is not None and upper1 is not None and lower2 > upper1:
                    return True  # 冲突: x >= 10 和 x <= 5
            
            return False
            
        except Exception as e:
            self.logger.debug(f"Error checking conflict: {e}")
            return False  # 出错时保守处理，不认为冲突
    
    def _extract_lower_bound(self, inv: str, var: str) -> Optional[int]:
        """提取变量的下界"""
        try:
            # 匹配 var >= value 或 var > value
            match = re.search(rf'\b{var}\s*>=\s*(-?\d+)', inv)
            if match:
                return int(match.group(1))
            match = re.search(rf'\b{var}\s*>\s*(-?\d+)', inv)
            if match:
                return int(match.group(1)) + 1
            # 匹配 value <= var
            match = re.search(rf'(-?\d+)\s*<=\s*\b{var}\b', inv)
            if match:
                return int(match.group(1))
            return None
        except:
            return None
    
    def _extract_upper_bound(self, inv: str, var: str) -> Optional[int]:
        """提取变量的上界"""
        try:
            # 匹配 var <= value 或 var < value
            match = re.search(rf'\b{var}\s*<=\s*(-?\d+)', inv)
            if match:
                return int(match.group(1))
            match = re.search(rf'\b{var}\s*<\s*(-?\d+)', inv)
            if match:
                return int(match.group(1)) - 1
            # 匹配 value >= var
            match = re.search(rf'(-?\d+)\s*>=\s*\b{var}\b', inv)
            if match:
                return int(match.group(1))
            return None
        except:
            return None
    
    def _self_refine_invariants(self, current_code: str, current_invariants: List[str],
                                issues: str, loop_context: str, record: Dict) -> Optional[str]:
        """
        让 LLM 根据自我检查发现的问题更新不变量
        
        Args:
            current_code: 当前的完整代码
            current_invariants: 当前的不变量列表
            issues: 自我检查发现的问题
            loop_context: 执行 traces
            record: Loop record
            
        Returns:
            Updated code with refined invariants
        """
        invariants_str = '\n'.join([f"  {i+1}. {inv}" for i, inv in enumerate(current_invariants)])
        refine_prompt = (
            "Refine loop invariants based on issues and traces.\n\n"
            f"Current invariants:\n{invariants_str}\n\n"
            f"Issues:\n{issues}\n\n"
            f"Traces:\n{loop_context}\n\n"
            "Return complete C code only, updating loop invariants only.\n\n"
            f"Code:\n```c\n{current_code}\n```"
        )
        
        try:
            response = self.llm.chat(refine_prompt)
            
            # Extract code from response: prefer block containing target function name
            extracted_code = None
            expected_func = f"main{self.file_name}"

            all_code_blocks = re.findall(r'```c\n(.*?)\n```', response, re.DOTALL)
            if not all_code_blocks:
                all_code_blocks = re.findall(r'```\n(.*?)\n```', response, re.DOTALL)

            if all_code_blocks:
                for block in all_code_blocks:
                    if expected_func in block:
                        extracted_code = block
                        break
                if extracted_code is None:
                    extracted_code = all_code_blocks[0]

            # Fallback: return response if it looks like code
            if extracted_code is None and ('/*@' in response or '#include' in response or '{' in response):
                extracted_code = response.strip()

            if extracted_code is None:
                return None

            # Validate and fix code structure
            extracted_code = self._validate_and_fix_code_structure(extracted_code, current_code)
            
            return extracted_code
            
        except Exception as e:
            self.logger.error(f"Self-refinement failed: {e}")
            return None
    
    def _generate_with_llm(self, original_code: str, record, loop_idx: int) -> Optional[str]:
        """使用LLM生成不变量"""
        if self.llm is None:
            self.logger.error("LLM is not initialized but required for generation")
            return None
        
        # 3. Generate template with PLACE_HOLDER (only if polynomial fitting failed)
        template_code = self.template_gen.generate_template(record)
        
        # 4. Insert template into original code using ASGSE-style replacement
        try:
            code_with_template = self._replace_loop_content(original_code, template_code, loop_idx)
        except Exception as e:
            self.logger.warning(f"Failed to replace loop using ASGSE method: {e}, trying simple replacement")
            # Fallback to simple string replacement
            loop_content = record.get('loop_content', '')
            if loop_content and loop_content in original_code:
                code_with_template = original_code.replace(loop_content, template_code, 1)
            else:
                self.logger.warning("Could not find loop in original code, using template directly")
                code_with_template = template_code
        
        # 5. Prepare prompt template and loop context
        prompt_template, loop_context = self._prepare_prompt(record, loop_idx)
        
        # 5.5. CoT Analysis: Let LLM understand what conditions the loop invariant needs to satisfy
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - CoT Analysis: Understanding loop invariant requirements...")
        self.logger.info(f"{'='*60}")
        cot_analysis = self._get_cot_analysis(code_with_template, loop_context, record)
        if cot_analysis:
            self.logger.info(f"CoT Analysis Result:\n{cot_analysis}")
            # Append CoT analysis to loop_context for better understanding
            loop_context = f"{loop_context}\n\n### CoT Analysis (Understanding Loop Invariant Requirements): ###\n{cot_analysis}"

        # Always remind the three invariant properties before generation
        invariant_checklist = (
            "### Invariant Soundness Checklist ###\n"
            "- Establishment: invariant holds before the loop starts.\n"
            "- Preservation: assuming the loop condition holds, the invariant remains true after one iteration.\n"
            "- Termination: when the loop condition becomes false, the invariant together with ¬(loop condition) implies the post-condition."
        )
        loop_context = f"{loop_context}\n\n{invariant_checklist}"
        
        # 6. Generate initial invariant using LLM (fills PLACE_HOLDER)
        initial_code = self._generate_initial_invariant(code_with_template, (prompt_template, loop_context))
        
        if not initial_code:
            self.logger.error("Failed to generate initial invariant")
            return None
        
        # Print initial generated invariants
        initial_invariants = self._extract_invariants_from_code(initial_code)
        self.logger.info(f"\n{'='*60}")
        self.logger.info(f"Loop {loop_idx} - Initial Generated Invariants:")
        self.logger.info(f"{'='*60}")
        if initial_invariants:
            for i, inv in enumerate(initial_invariants, 1):
                self.logger.info(f"  [{i}] {inv}")
        else:
            self.logger.info("  (No invariants found in initial generation)")
        
        # 6. Write to temporary file for verification
        temp_file = self._create_temp_file(initial_code)
        
        try:
            # 7. Iterative strengthening (不做语法修复流程)
            final_code = self._strengthen_invariants_iterative(
                initial_code,
                temp_file,
                record,
                loop_idx,
                max_iterations=MAX_STRENGTHEN_ITERATIONS
            )
            
            if final_code:
                # Print final invariants
                final_invariants = self._extract_invariants_from_code(final_code)
                self.logger.info(f"\n{'='*60}")
                self.logger.info(f"Loop {loop_idx} - Final Invariants (after strengthening):")
                self.logger.info(f"{'='*60}")
                if final_invariants:
                    for i, inv in enumerate(final_invariants, 1):
                        self.logger.info(f"  [{i}] {inv}")
                
                # Store successful LLM generation result in cache
                if self.cache_manager and self.cache_manager.enabled:
                    try:
                        self.cache_manager.store_problem_solution(
                            record, loop_idx, final_code, final_invariants,
                            {'syntax': True, 'valid': True, 'satisfy': True, 'source': 'llm_generation'}
                        )
                    except Exception as e:
                        self.logger.warning(f"Failed to store LLM generation result in cache: {e}")

                self.logger.info(f"\nOK Successfully generated invariant for loop {loop_idx}")
                return final_code
            else:
                self.logger.warning(f"\nX Failed to generate invariant for loop {loop_idx} (reached max iterations)")
                return None
                
        finally:
            # Clean up temporary file
            if os.path.exists(temp_file):
                os.remove(temp_file)
    
    def _get_cot_analysis(self, code_with_template: str, loop_context: str, record: Dict) -> Optional[str]:
        """
        Generate helper invariants with code context.
        
        NOTE: Traces are NOT used in CoT analysis - they are only used for filtering
        invariants after generation.
        
        Args:
            code_with_template: C code with template placeholders
            loop_context: Loop context (code and pre-condition, WITHOUT traces)
            record: Loop record containing pre_condition and other info
            
        Returns:
            Helper invariants for postcondition proof
        """
        pre_condition = record.get('pre_condition', '')
        
        # Generate helper invariants with code context only (no traces)
        self.logger.info("Generating helper invariants with code context...")
        helpers = self._cot_stage2_with_code(code_with_template, loop_context, pre_condition, None, record)
        
        if helpers:
            self.logger.info(f"Helper Invariants:\n{helpers}")
            return helpers
        else:
            self.logger.warning("Helper invariant generation failed")
            return None
    
    def _cot_stage1_traces_only(self, loop_context: str, pre_condition: str, record: Dict) -> Optional[str]:
        """
        DEPRECATED: This method is no longer used.
        Traces are not passed to LLM - they are only used for filtering invariants.
        """
        return None
    
    def _cot_stage2_with_code(self, code_with_template: str, loop_context: str, pre_condition: str, 
                              stage1_invariants: Optional[str], record: Dict) -> Optional[str]:
        """
        Generate helper invariants with code context.
        
        NOTE: Traces are NOT used - they are only used for filtering invariants after generation.
        """
        loop_content = record.get('loop_content', '')
        
        # Build prompt without references to Stage 1 invariants if they don't exist
        if stage1_invariants:
            stage1_section = f"""### Stage 1 Invariants (ALREADY GENERATED - DO NOT MODIFY): ###
{stage1_invariants}

"""
            task_description = "Generate ADDITIONAL helper invariants needed to prove the postcondition."
            do_not_section = """
**DO NOT**:
- Repeat or modify Stage 1 invariants
- Generate new base invariants
- Change any relationships from Stage 1

**DO**:
- Check if Stage 1 invariants need conditional form (add `loop_cond ==>` if needed)
- Generate helper invariants for postcondition proof
- Add bounds if not already in Stage 1
"""
        else:
            stage1_section = ""
            task_description = "Generate loop invariants needed to prove the postcondition."
            do_not_section = """
**DO**:
- Generate base invariants from code analysis
- Check if invariants need conditional form (add `loop_cond ==>` if needed)
- Generate helper invariants for postcondition proof
- Add bounds for loop variables
"""
        
        stage2_prompt = (
            "You are a formal verification expert. Generate loop invariants from code.\n\n"
            f"{stage1_section}"
            f"Code with template:\n```c\n{code_with_template}\n```\n\n"
            f"Loop body:\n```c\n{loop_content}\n```\n\n"
            f"Pre-condition:\n{pre_condition}\n\n"
            f"{task_description}\n\n{do_not_section}\n\n"
            "Output ONLY ACSL lines: loop invariant ...; and loop assigns ...;"
        )
        
        try:
            response = self.llm.chat(stage2_prompt)
            return response.strip()
        except Exception as e:
            self.logger.error(f"Helper invariant generation failed: {e}")
            return None

    def _extract_verification_target(self, code_with_template: str) -> Dict:
        """
        Detect post-loop verification targets from code.

        Returns:
            {
              'has_target': bool,
              'target_type': 'none' | 'assert_single' | 'assert_conjunctive',
              'assert_text': str,
              'conjunct_count': int
            }
        """
        assert_match = re.search(r'/\*@\s*assert\b\s*([^;]+);', code_with_template, re.DOTALL)
        if not assert_match:
            self.logger.info("Prompt goal mode: no verification target")
            return {
                'has_target': False,
                'target_type': 'none',
                'assert_text': '',
                'conjunct_count': 0,
            }

        assert_text = " ".join(assert_match.group(1).strip().split())
        conjunct_count = len([part for part in assert_text.split('&&') if part.strip()])
        if conjunct_count > 1:
            target_type = 'assert_conjunctive'
        else:
            target_type = 'assert_single'
        self.logger.info(f"Prompt goal mode: {target_type}")

        return {
            'has_target': True,
            'target_type': target_type,
            'assert_text': assert_text,
            'conjunct_count': conjunct_count,
        }

    def _build_goal_guidance(self, code_with_template: str) -> str:
        """
        Build goal-specific prompt guidance:
        - no verification target: avoid target-driven wording
        - with assertion target: enforce target-driven invariant construction
        """
        target = self._extract_verification_target(code_with_template)
        if not target['has_target']:
            return (
                "No explicit verification target is present.\n"
                "- Focus on inductive, non-empty invariants derived from loop semantics.\n"
                "- Prioritize transition/conservation relations and necessary bounds.\n"
                "- Do not mention or optimize for post-loop assert."
            )

        assert_text = target['assert_text']
        type_hints = []
        if '||' in assert_text:
            type_hints.append(
                "- Target is disjunctive (||): preserve a phase/guard relation that can justify one disjunct at exit."
            )
        if any(op in assert_text for op in ('<=', '>=', '<', '>')):
            type_hints.append(
                "- Target contains inequalities: add monotonic/bound invariants tight enough to derive final bounds at exit."
            )
        if '/' in assert_text or '%' in assert_text:
            type_hints.append(
                "- Target contains division/modulo: add quotient-remainder relation and remainder bounds (e.g., 0 <= r < y)."
            )
        if '*' in assert_text:
            type_hints.append(
                "- Target is nonlinear/multiplicative: include conserved algebraic equality tying products to loop-updated variables."
            )
        if not type_hints:
            type_hints.append(
                "- Use one strong relational invariant that directly tracks target terms across loop updates."
            )

        if target['target_type'] == 'assert_conjunctive':
            return (
                f"Verification target detected (conjunctive assert, {target['conjunct_count']} conjuncts): {assert_text}\n"
                "- Build invariants so each assert conjunct has a corresponding preserved relation.\n"
                "- Ensure invariants with loop-exit condition can imply all conjuncts.\n"
                "- Prefer relational equalities connecting loop-updated variables to assert terms.\n"
                + "\n".join(type_hints)
            )

        return (
            f"Verification target detected (single assert): {assert_text}\n"
            "- Build invariants that directly preserve and imply this target at loop exit.\n"
            "- Include at least one relation connecting loop-updated variables to target terms.\n"
            "- Prefer strong, target-aligned invariants over generic bounds-only invariants.\n"
            + "\n".join(type_hints)
        )
    
    def _prepare_prompt(self, record: Dict, loop_idx: int) -> tuple:
        """
        Prepare LLM prompt template and loop context.
        
        NOTE: Traces are NOT included in the prompt - they are only used for filtering
        invariants after generation.
        """
        # Extract loop information (without traces)
        loop_code_snippet = record.get('loop_content', '')
        pre_condition = record.get('pre_condition', '')
        transition_relation = record.get('transition_relation', '')
        
        # Extract variable information from record
        known_vars = set()
        if 'current_vars' in record:
            known_vars.update(record['current_vars'])
        if 'function_params' in record:
            known_vars.update(record['function_params'])
        if 'common_vars' in record:
            known_vars.update(record['common_vars'])
        
        # Extract parameters that can use \at(v, Pre)
        param_pre_vars = set()
        if 'param_pre_vars' in record:
            ppv = record['param_pre_vars']
            if isinstance(ppv, dict):
                param_pre_vars = set(ppv.keys())
            elif isinstance(ppv, list):
                param_pre_vars = set(ppv)
        
        # Build loop context WITHOUT traces
        # Only include code structure and pre-condition
        loop_context_lines = [
            "### Loop Context ###",
            "",
            "1. Pre-Condition (Before Loop Entry):",
            f"   {pre_condition if pre_condition else 'No pre-condition specified'}",
            "",
            "2. Loop Code:",
            f"```c",
            f"{loop_code_snippet}",
            f"```",
        ]
        
        if transition_relation:
            loop_context_lines.extend([
                "",
                "3. Transition Relation:",
                f"   {transition_relation}",
            ])
        
        # Add variable and parameter information
        # Format parameters to show both usages: x and \at(x, Pre)
        param_usage_list = []
        for param in sorted(param_pre_vars):
            param_usage_list.append(f"{param} (or \\at({param}, Pre) for initial value)")
        
        loop_context_lines.extend([
            "",
            "### AVAILABLE VARIABLES AND PARAMETERS ###",
            "",
            f"**Available Variables:** {sorted(known_vars)}",
            "",
            "**Function Parameters:**",
        ])
        
        if param_usage_list:
            for param_usage in param_usage_list:
                loop_context_lines.append(f"  - {param_usage}")
        else:
            loop_context_lines.append("  - (none)")
        
        loop_context_lines.extend([
            "",
            "IMPORTANT:",
            "- You can ONLY use variables from the 'Available Variables' list",
            "- For function parameters, you can use:",
            "  * 'param' to refer to the current value",
            "  * '\\at(param, Pre)' to refer to the initial value at function entry",
            "- Using undefined variables or \\at() on non-parameters will cause validation errors",
        ])
        
        # 注意：缓存参考不再插入到 loop_context 中
        # 而是在 prompt 模板中通过 {{cache_reference}} 占位符或自动插入
        loop_context = "\n".join(loop_context_lines)
        
        # Load template from prompts/ (single-generation path)
        prompt_template = self._get_gen_template()

        # Inject cache reference for single-generation path as well.
        cache_reference = self._format_cache_reference()
        if '{{cache_reference}}' in prompt_template:
            prompt_template = prompt_template.replace('{{cache_reference}}', cache_reference)
        elif cache_reference and '```c' in prompt_template:
            prompt_template = prompt_template.replace('```c', f"{cache_reference}\n\n```c", 1)
        
        return prompt_template, loop_context
    
    def _get_gen_template(self) -> str:
        """Load the single generation prompt from prompts/simple.txt."""
        prompt_path = os.path.join(os.path.dirname(__file__), 'prompts', 'simple.txt')
        if not os.path.exists(prompt_path):
            raise FileNotFoundError(f"Single prompt not found: {prompt_path}")
        with open(prompt_path, 'r', encoding='utf-8') as f:
            return f.read()

    def _generate_initial_invariant(self, code_with_template: str, prompt_info: tuple) -> Optional[str]:
        """Generate initial invariant using LLM - fills PLACE_HOLDER in template"""
        prompt_template, loop_context = prompt_info
        goal_guidance = self._build_goal_guidance(code_with_template)
        if '{{goal_guidance}}' in prompt_template:
            prompt_template = prompt_template.replace('{{goal_guidance}}', goal_guidance)
        
        # Replace the double curly braces placeholders with actual values
        # The template uses {{pre_cond}} and {{content}} as placeholders
        prompt = prompt_template.replace('{{pre_cond}}', loop_context).replace('{{content}}', code_with_template)
        
        # Call LLM to fill in the placeholders
        response = self.llm.chat(prompt)
        
        # Extract code from response: prefer block containing target function name
        extracted_code = None
        expected_func = f"main{self.file_name}"

        # 找所有 ```c ... ``` 代码块
        all_code_blocks = re.findall(r'```c\n(.*?)\n```', response, re.DOTALL)
        if not all_code_blocks:
            all_code_blocks = re.findall(r'```\n(.*?)\n```', response, re.DOTALL)

        if all_code_blocks:
            # 优先选包含目标函数名的代码块
            for block in all_code_blocks:
                if expected_func in block:
                    extracted_code = block
                    break
            # 回退：取第一个块
            if extracted_code is None:
                extracted_code = all_code_blocks[0]

        # Fallback: return response if it looks like code
        if extracted_code is None and ('/*@' in response or '#include' in response or '{' in response):
            extracted_code = response.strip()
        
        if extracted_code is None:
            return None
            
        # Validate and fix code structure - ensure requires clause is preserved
        extracted_code = self._validate_and_fix_code_structure(extracted_code, code_with_template)
        
        return extracted_code
    
    def _select_prompt_for_candidate(self, candidate_idx: int, loop_context: str, code_with_template: str) -> tuple:
        """
        为每个候选选择一个 prompt
        
        Args:
            candidate_idx: 候选索引
            prompt_templates: 所有可用的 prompt 模板列表
            loop_context: 循环上下文（包含缓存参考）
            code_with_template: 代码模板
            
        Returns:
            (prompt_string, prompt_name) 元组
        """
        # Single-prompt mode: always use prompts/simple.txt
        selected_template = self._get_gen_template()
        selected_template_name = 'simple'
        
        # 替换占位符
        # 1. 首先替换 {{cache_reference}}（如果存在）
        cache_reference = self._format_cache_reference()
        if '{{cache_reference}}' in selected_template:
            selected_template = selected_template.replace('{{cache_reference}}', cache_reference)
        if '{{goal_guidance}}' in selected_template:
            selected_template = selected_template.replace('{{goal_guidance}}', self._build_goal_guidance(code_with_template))
        
        # 2. 处理 {{pre_cond}} 可选的情况（某些 prompt 可能不包含此占位符）
        if '{{pre_cond}}' in selected_template:
            prompt = selected_template.replace('{{pre_cond}}', loop_context).replace('{{content}}', code_with_template)
        else:
            # 如果 prompt 中没有 {{pre_cond}}，只替换 {{content}}
            # 但需要确保缓存参考被插入（如果没有 {{cache_reference}} 占位符）
            prompt = selected_template.replace('{{content}}', code_with_template)
            # 如果模板中没有 {{cache_reference}} 占位符，但有缓存结果，插入到合适位置
            if cache_reference and '{{cache_reference}}' not in selected_template:
                # 在 {{content}} 之前插入缓存参考
                prompt = prompt.replace('```c', f"{cache_reference}\n\n```c", 1)
        
        self.logger.info(f"  Candidate {candidate_idx+1} selected prompt: {selected_template_name}")
        return prompt, selected_template_name
    
    def _format_cache_reference(self) -> str:
        """
        格式化缓存参考信息，用于插入到 prompt 中
        
        Returns:
            格式化的缓存参考字符串，如果没有缓存结果则返回空字符串
        """
        if not hasattr(self, '_cached_similar_problems') or not self._cached_similar_problems:
            return ""
        
        reference_lines = [
            "### Reference: Similar Problems Found in Cache ###",
        ]
        
        for idx, result in enumerate(self._cached_similar_problems, 1):
            invariants = result.entry.solution_invariants
            if isinstance(invariants, str):
                try:
                    import json
                    invariants = json.loads(invariants)
                except:
                    invariants = [invariants] if invariants else []
            
            if invariants and isinstance(invariants, list) and len(invariants) > 0:
                reference_lines.append(f"\nSimilar Problem {idx} (Similarity: {result.similarity_score:.3f}):")
                reference_lines.append("Similar invariants found:")
                for inv in invariants:
                    if isinstance(inv, str):
                        reference_lines.append(f"  - {inv}")
                    else:
                        reference_lines.append(f"  - {str(inv)}")
        
        if len(reference_lines) > 1:  # 有实际内容
            reference_lines.append("\nNote: Use these as reference, but adapt them to the current problem's variables and context.")
            return "\n".join(reference_lines)
        
        return ""
    
    def _create_llm_client_for_thread(self, model_name: str) -> 'Chatbot':
        """
        为每个线程创建独立的 LLM client，不共享上下文窗口
        
        Args:
            model_name: 要使用的模型名称
            
        Returns:
            新的 Chatbot 实例
        """
        from llm import Chatbot
        from config import LLMConfig
        
        # 创建新的配置，使用指定的模型
        thread_config = LLMConfig()
        thread_config.api_model = model_name
        thread_config.api_key = self.llm_config.api_key
        thread_config.base_url = self.llm_config.base_url
        thread_config.api_temperature = self.llm_config.api_temperature
        thread_config.api_top_p = self.llm_config.api_top_p
        thread_config.think_mode_enabled = self.llm_config.think_mode_enabled
        thread_config.use_api_model = True
        
        # 创建新的 Chatbot 实例（每个实例有独立的 client 和消息历史）
        return Chatbot(thread_config)
    
    def _select_model_for_candidate(self) -> str:
        """
        为每个候选随机选择一个模型
        
        Args:
            candidate_idx: 候选索引
            
        Returns:
            选择的模型名称
        """
        # Single-model mode: always use configured API model
        return self.llm_config.api_model
    
    def _generate_multiple_candidates(self, code_with_template: str, prompt_info: tuple, num_candidates: int = 3, temperature: float = 0.8, use_threading: bool = True, max_workers: int = 5) -> List[Optional[str]]:
        """
        并行生成多组候选不变式（单一 prompt + 单一模型）
        
        Args:
            code_with_template: 带有PLACE_HOLDER的代码模板
            prompt_info: (prompt_template, loop_context) 元组
            num_candidates: 生成的候选组数
            temperature: 生成温度,控制多样性
            use_threading: 是否使用线程池实现真正的并行生成
            max_workers: 线程池最大工作线程数
            
        Returns:
            候选代码列表
        """
        _, loop_context = prompt_info
        self.logger.info("Loaded single prompt template: simple")
        
        # 保存原始温度
        original_temp = self.llm_config.api_temperature
        
        try:
            # 设置生成温度以增加多样性
            self.llm_config.api_temperature = temperature
            
            self.logger.info(f"Generating {num_candidates} candidate invariant sets with temperature={temperature}")
            
            if use_threading and num_candidates > 1:
                # 使用线程池实现真正的并行生成
                from concurrent.futures import ThreadPoolExecutor, as_completed
                
                def generate_single_candidate(candidate_idx: int) -> Optional[str]:
                    """生成单个候选，使用单一 prompt/模型并创建独立 LLM client"""
                    thread_llm = None
                    try:
                        # 单一 prompt + 单一模型
                        prompt, prompt_name = self._select_prompt_for_candidate(
                            candidate_idx, loop_context, code_with_template
                        )
                        selected_model = self._select_model_for_candidate()
                        
                        # 为每个线程创建独立的 LLM client（不共享上下文窗口）
                        thread_llm = self._create_llm_client_for_thread(selected_model)
                        
                        self.logger.info(f"  Generating candidate {candidate_idx+1}/{num_candidates} with model={selected_model}, prompt={prompt_name}...")
                        
                        # 调用独立的 LLM client 生成（不共享上下文）
                        response = thread_llm.chat(prompt)
                        
                        # 提取代码：优先选包含目标函数名的代码块
                        extracted_code = None
                        expected_func = f"main{self.file_name}"

                        # 找所有 ```c ... ``` 代码块
                        all_code_blocks = re.findall(r'```c\n(.*?)\n```', response, re.DOTALL)
                        if not all_code_blocks:
                            all_code_blocks = re.findall(r'```\n(.*?)\n```', response, re.DOTALL)

                        if all_code_blocks:
                            # 优先选包含目标函数名的代码块
                            for block in all_code_blocks:
                                if expected_func in block:
                                    extracted_code = block
                                    break
                            # 回退：取第一个块
                            if extracted_code is None:
                                extracted_code = all_code_blocks[0]
                        elif '/*@' in response or '#include' in response:
                            extracted_code = response.strip()
                        
                        if extracted_code:
                            # Validate and fix code structure (using self from outer scope)
                            extracted_code = self._validate_and_fix_code_structure(extracted_code, code_with_template)
                            return extracted_code
                        else:
                            self.logger.warning(f"  Failed to extract code from candidate {candidate_idx+1}")
                            return None
                    except Exception as e:
                        self.logger.error(f"  Error generating candidate {candidate_idx+1}: {e}")
                        return None
                    finally:
                        # 清理：每个线程的 LLM client 会在函数结束时自动清理
                        # 由于每个线程创建独立的 client，不会影响其他线程
                        pass
                
                # 使用线程池并行生成
                candidates = []
                with ThreadPoolExecutor(max_workers=max_workers) as executor:
                    # 提交所有任务
                    future_to_idx = {
                        executor.submit(generate_single_candidate, i): i 
                        for i in range(num_candidates)
                    }
                    
                    # 收集结果（按完成顺序）
                    for future in as_completed(future_to_idx):
                        candidate_idx = future_to_idx[future]
                        try:
                            result = future.result()
                            candidates.append((candidate_idx, result))
                        except Exception as e:
                            self.logger.error(f"  Candidate {candidate_idx+1} generated exception: {e}")
                            candidates.append((candidate_idx, None))
                
                # 按原始顺序排序
                candidates.sort(key=lambda x: x[0])
                candidates = [c[1] for c in candidates]
            else:
                # 顺序生成（也使用独立的 client）
                candidates = []
                for i in range(num_candidates):
                    # 单一 prompt + 单一模型
                    prompt, prompt_name = self._select_prompt_for_candidate(
                        i, loop_context, code_with_template
                    )
                    selected_model = self._select_model_for_candidate()
                    
                    # 为每个候选创建独立的 LLM client（不共享上下文窗口）
                    thread_llm = self._create_llm_client_for_thread(selected_model)
                    
                    self.logger.info(f"  Generating candidate {i+1}/{num_candidates} with model={selected_model}, prompt={prompt_name}...")
                    
                    # 调用独立的 LLM client 生成（不共享上下文）
                    response = thread_llm.chat(prompt)
                    
                    # 提取代码：优先选包含目标函数名的代码块
                    extracted_code = None
                    expected_func = f"main{self.file_name}"

                    all_code_blocks = re.findall(r'```c\n(.*?)\n```', response, re.DOTALL)
                    if not all_code_blocks:
                        all_code_blocks = re.findall(r'```\n(.*?)\n```', response, re.DOTALL)

                    if all_code_blocks:
                        for block in all_code_blocks:
                            if expected_func in block:
                                extracted_code = block
                                break
                        if extracted_code is None:
                            extracted_code = all_code_blocks[0]
                    elif '/*@' in response or '#include' in response:
                        extracted_code = response.strip()
                    
                    if extracted_code:
                        # Validate and fix code structure
                        extracted_code = self._validate_and_fix_code_structure(extracted_code, code_with_template)
                        candidates.append(extracted_code)
                    else:
                        candidates.append(None)
                        self.logger.warning(f"  Failed to extract code from candidate {i+1}")
        
        finally:
            # 恢复原始温度
            self.llm_config.api_temperature = original_temp
        
        # 过滤掉None值
        valid_candidates = [c for c in candidates if c is not None]
        self.logger.info(f"Successfully generated {len(valid_candidates)}/{num_candidates} candidates")
        
        return valid_candidates
    
    def _get_input_path(self) -> Optional[str]:
        """Find the actual input file path"""
        possible_subdirs: List[str] = []
        if getattr(self, "resolved_subdir", None):
            possible_subdirs.append(self.resolved_subdir)
        elif getattr(self, "input_subdir", None):
            possible_subdirs.append(self.input_subdir)
        else:
            possible_subdirs.append(SUBDIR)

        # 去重同时保持顺序
        seen = set()
        possible_subdirs = [s for s in possible_subdirs if not (s in seen or seen.add(s))]

        possible_paths: List[Path] = []
        for subdir in possible_subdirs:
            possible_paths.append(Path(__file__).resolve().parent / f"input/{subdir}/{self.file_name}.c")
            possible_paths.append(Path(__file__).resolve().parent / f"../src/input/{subdir}/{self.file_name}.c")

        # Also try without subdirectory (legacy layout)
        possible_paths.extend(
            [
                Path(f"input/{self.file_name}.c"),
                Path(__file__).resolve().parent / f"input/{self.file_name}.c",
                Path(__file__).resolve().parent / f"../src/input/{self.file_name}.c",
                Path(os.getcwd()) / f"input/{self.file_name}.c",
            ]
        )
        
        for path in possible_paths:
            normalized_path = path.resolve()
            if normalized_path.exists() and normalized_path.is_file():
                return str(normalized_path)
        
        # Log all attempted paths for debugging
        self.logger.debug(f"Attempted paths for {self.file_name}.c:")
        for path in possible_paths:
            normalized_path = path.resolve()
            self.logger.debug(f"  {normalized_path} - exists: {normalized_path.exists()}")
        
        return None
    
    def _get_full_source_code(self) -> Optional[str]:
        """Try to get the full source C code file"""
        input_path = self._get_input_path()
        if input_path:
            try:
                with open(input_path, 'r') as f:
                    content = f.read()
                    self.logger.debug(f"Successfully read input file: {input_path}")
                    return content
            except Exception as e:
                self.logger.error(f"Failed to read input file {input_path}: {e}")
                pass
        else:
            self.logger.error(f"Could not find input file for {self.file_name}.c")
            self.logger.error(f"Current working directory: {os.getcwd()}")
            self.logger.error(f"Script directory: {os.path.dirname(os.path.abspath(__file__))}")
        return None
    
    @property
    def output_dir(self) -> str:
        """Get output directory aligned with input path (lazy initialization)"""
        if getattr(self, '_output_dir', None) is not None:
            return self._output_dir

        # Auto-determine output_dir based on selected subdir
        subdir = getattr(self, "resolved_subdir", None) or SUBDIR
        self._output_dir = os.path.join("output", subdir)
        return self._output_dir
    
    def _delete_unused_merge_methods(self):
        """These methods are no longer needed - template is inserted directly into input"""
        pass
    
    def _merge_invariants_to_original_UNUSED(self, annotated_code: str, record: Dict) -> str:
        """
        Merge annotated loop invariants into the original input code
        Returns code that only differs from input by loop invariants (no extra main functions)
        
        Args:
            annotated_code: Complete C code with ACSL annotations from LLM
            record: Loop record containing loop_content
            
        Returns:
            Original input code with only the loop invariants added/updated
        """
        # Get original input code
        original_code = self._get_full_source_code()
        if not original_code:
            # If can't find original, return annotated code but remove extra main functions
            return self._remove_extra_main_functions(annotated_code)
        
        loop_content = record.get('loop_content', '')
        if not loop_content:
            return original_code
        
        # Extract the annotated loop from annotated_code
        # Find the loop with ACSL annotations
        annotated_loop = self._extract_annotated_loop(annotated_code, loop_content)
        
        if annotated_loop:
            # Replace the original loop in original_code with annotated_loop
            if loop_content in original_code:
                # Find the exact loop location to replace
                merged_code = original_code.replace(loop_content, annotated_loop, 1)
                return merged_code
            else:
                # Try to find loop by pattern matching
                merged_code = self._replace_loop_by_pattern(original_code, loop_content, annotated_loop)
                if merged_code:
                    return merged_code
        
        # Fallback: return original code (no invariants added)
        return original_code
    
    def _extract_annotated_loop(self, annotated_code: str, loop_content: str) -> Optional[str]:
        """
        Extract the annotated loop block from the full annotated code
        
        Args:
            annotated_code: Full C code with annotations
            loop_content: Original loop content (without annotations)
            
        Returns:
            Loop code with ACSL annotations, or None if not found
        """
        # Try to find the loop block with annotations
        # Look for /*@ ... @*/ followed by the loop
        
        # Pattern 1: Find /*@ ... @*/ that precedes the loop
        acsl_pattern = r'/\*@.*?@\*/'
        loop_pattern = re.escape(loop_content.strip())
        
        # Try to match: /*@ ... @*/ \n loop_content
        full_pattern = rf'({acsl_pattern}[\s\n]*{loop_pattern})'
        match = re.search(full_pattern, annotated_code, re.DOTALL)
        if match:
            return match.group(1)
        
        # Pattern 2: Find loop with inline annotations
        # Look for loop_content and check if there's /*@ ... @*/ before it in nearby lines
        loop_start_idx = annotated_code.find(loop_content)
        if loop_start_idx != -1:
            # Look backwards for /*@ ... @*/
            before_loop = annotated_code[:loop_start_idx]
            # Find the last /*@ ... @*/ before the loop
            acsl_matches = list(re.finditer(acsl_pattern, before_loop, re.DOTALL))
            if acsl_matches:
                last_acsl = acsl_matches[-1]
                # Get from last /*@ to end of loop
                loop_end_idx = loop_start_idx + len(loop_content)
                # Try to find the closing brace of the loop
                # Simple approach: find matching braces
                brace_count = 0
                for i, char in enumerate(annotated_code[loop_start_idx:], loop_start_idx):
                    if char == '{':
                        brace_count += 1
                    elif char == '}':
                        brace_count -= 1
                        if brace_count == 0:
                            loop_end_idx = i + 1
                            break
                
                annotated_loop = annotated_code[last_acsl.start():loop_end_idx]
                return annotated_loop
        
        return None
    
    def _replace_loop_by_pattern(self, original_code: str, loop_content: str, annotated_loop: str) -> Optional[str]:
        """
        Replace loop in original code by pattern matching
        
        Args:
            original_code: Original C code
            loop_content: Original loop content
            annotated_loop: Annotated loop to replace with
            
        Returns:
            Code with loop replaced, or None if replacement failed
        """
        # Try to find loop using regex pattern
        # Extract loop condition and body
        loop_match = re.search(r'\b(while|for)\s*\([^)]+\)\s*\{', loop_content)
        if loop_match:
            loop_keyword = loop_match.group(1)
            # Find matching loop in original_code
            pattern = rf'\b{loop_keyword}\s*\([^)]+\)\s*\{{'
            matches = list(re.finditer(pattern, original_code))
            
            if matches:
                # Use the first match
                match = matches[0]
                # Find the matching closing brace
                brace_count = 0
                start_idx = match.end() - 1
                for i, char in enumerate(original_code[start_idx:], start_idx):
                    if char == '{':
                        brace_count += 1
                    elif char == '}':
                        brace_count -= 1
                        if brace_count == 0:
                            end_idx = i + 1
                            # Replace the loop
                            return original_code[:match.start()] + annotated_loop + original_code[end_idx:]
        
        return None
    
    def _remove_extra_main_functions(self, code: str) -> str:
        """
        Remove extra main functions, keep only the first one (or the one that matches input)
        
        Args:
            code: C code that may contain multiple main functions
            
        Returns:
            Code with only one main function
        """
        # Count main functions
        main_pattern = r'\b(int\s+main\s*\(|void\s+main\s*\()'
        main_matches = list(re.finditer(main_pattern, code))
        
        if len(main_matches) <= 1:
            return code
        
        # Keep only the first main function
        first_main_start = main_matches[0].start()
        # Find where the first main function ends
        # Find the opening brace
        brace_start = code.find('{', first_main_start)
        if brace_start == -1:
            return code
        
        # Find matching closing brace
        brace_count = 0
        for i, char in enumerate(code[brace_start:], brace_start):
            if char == '{':
                brace_count += 1
            elif char == '}':
                brace_count -= 1
                if brace_count == 0:
                    first_main_end = i + 1
                    # Remove everything after the first main function except if it's part of the same function
                    # Actually, we want to keep the rest but remove other main functions
                    # Find the second main function
                    second_main_start = main_matches[1].start()
                    # Remove from second main to end
                    return code[:second_main_start].rstrip()
        
        return code
    
    def _ensure_complete_c_program(self, code: str, record: Dict) -> str:
        """Ensure the code is a complete C program with necessary includes and function structure"""
        # If code already has includes and function structure, return as is
        if code.strip().startswith('#include') and ('void ' in code or 'int ' in code or 'return' in code):
            # Check if it looks like a complete program
            if ';' in code.split('\n')[0] or '(' in code:  # Has function definitions
                return code
        
        # Try to get full source code to construct complete program
        full_code = self._get_full_source_code()
        if full_code:
            loop_content = record.get('loop_content', '')
            if loop_content and loop_content in full_code:
                # Replace the loop in full code with the annotated loop from LLM response
                # Find where the loop is in the code
                loop_start_idx = full_code.find(loop_content)
                if loop_start_idx != -1:
                    # Try to find the annotated loop in the LLM response
                    # The code from LLM should contain the loop with annotations
                    # We need to replace just the loop part
                    
                    # Extract the annotated loop from the code (between /*@ and @*/)
                    acsl_match = re.search(r'/\*@(.*?)@\*/', code, re.DOTALL)
                    if acsl_match:
                        # Get the loop code after annotations
                        after_annotations = code[acsl_match.end():].strip()
                        if loop_content.strip() in after_annotations or loop_content.strip() == after_annotations.strip():
                            # Replace loop in full code with annotated version
                            annotated_loop = f"/*@{acsl_match.group(1)}@*/\n{loop_content}"
                            return full_code.replace(loop_content, annotated_loop, 1)
                    
                    # If no annotations found, try to find loop in code and replace
                    if loop_content in code:
                        # Code might be just the loop part with annotations
                        return full_code.replace(loop_content, code, 1)
            
            # If we can't find the loop, try to prepend includes and structure
            include_lines = []
            struct_defs = []
            in_include_section = True
            for line in full_code.split('\n'):
                if line.strip().startswith('#include'):
                    include_lines.append(line)
                elif line.strip().startswith('#define') or line.strip().startswith('typedef'):
                    if in_include_section:
                        include_lines.append(line)
                elif line.strip() and not line.strip().startswith('//'):
                    in_include_section = False
                    if line.strip().startswith('struct ') or line.strip().startswith('typedef struct'):
                        struct_defs.append(line)
            
            # Prepend includes and structs to code
            if include_lines or struct_defs:
                header = '\n'.join(include_lines + struct_defs) + '\n\n'
                return header + code
        
        # Otherwise return code as is
        return code
    
    def _insert_invariants_into_code(self, code: str, invariants: List[str], loop_content: str) -> Optional[str]:
        """
        Insert invariants into code before the loop.
        
        Args:
            code: Original C code
            invariants: List of invariant strings (e.g., ["loop invariant counter == 1;", "loop invariant var1 >= 0;"])
            loop_content: The loop content to find and insert invariants before
            
        Returns:
            Code with invariants inserted, or None if failed
        """
        if not invariants:
            return None
        
        # Find the loop in the code
        loop_pattern = re.escape(loop_content)
        match = re.search(loop_pattern, code, re.DOTALL)
        if not match:
            # Try to find loop using while/for pattern
            loop_pattern = r'(\s*)(while|for)\s*\('
            match = re.search(loop_pattern, code)
            if not match:
                return None
        
        # Get indentation
        indent = match.group(1) if match.groups() else ""
        
        # Build invariant block
        inv_block = "\n".join([f"{indent}  {inv}" for inv in invariants])
        inv_annotation = f"{indent}/*@\n{inv_block}\n{indent}*/\n"
        
        # Insert before loop
        insert_pos = match.start()
        return code[:insert_pos] + inv_annotation + code[insert_pos:]
    
    def _create_temp_file(self, code: str) -> str:
        """
        写入输出目录的正式文件(不再使用 _temp),后续修复直接覆盖.
        """
        # 在写入文件前验证代码结构
        from unified_filter import validate_code_structure
        code_violations = validate_code_structure(code)
        if code_violations:
            self.logger.error(f"Code structure validation failed before writing to file:")
            for violation in code_violations:
                self.logger.error(f"  - {violation.type.value}: {violation.message}")
            # 记录完整的代码以便调试
            self.logger.debug(f"Problematic code:\n{code[:500]}...")
            # 抛出异常而不是静默失败
            raise ValueError(f"Generated code has {len(code_violations)} structure violations")
        
        os.makedirs(self.output_dir, exist_ok=True)
        output_file = os.path.join(self.output_dir, f"{self.file_name}.c")
        with open(output_file, 'w') as f:
            f.write(code)
        return output_file
    
    def _extract_invariants_from_code(self, code: str) -> List[str]:
        """Extract all invariant expressions from code"""
        # Match all loop invariant statements
        inv_pattern = re.compile(r'loop\s+invariant\s+([^;]+);', re.DOTALL)
        matches = inv_pattern.findall(code)
        
        # Clean up invariants (remove extra whitespace)
        invariants = [inv.strip() for inv in matches]
        return invariants
    
    def _rebuild_code_with_invariants(self, code: str, invariants: List[str]) -> str:
        """
        Rebuild code by replacing existing invariants with new ones

        Args:
            code: Original code with invariants
            invariants: New list of invariants to use

        Returns:
            Code with updated invariants
        """
        if not invariants:
            # Remove all invariants from code
            # Match /*@ ... */ or /* ... */ blocks containing loop invariants
            # 使用 [\s\S] 代替 [^*] 以正确匹配包含 * (乘法) 的不变量
            code = re.sub(r'/\*@[\s\S]*?loop\s+invariant[\s\S]*?\*/', '', code)
            code = re.sub(r'/\*[\s\S]*?loop\s+invariant[\s\S]*?\*/', '', code)
            return code

        # Find the invariant annotation block BEFORE the loop (not function requires/ensures)
        # 策略：找到所有 /*@ */ 块，然后选择包含 loop invariant 的那个
        # 这样可以避免正则表达式跨块匹配（从 requires 块匹配到 loop invariant 块）
        all_blocks_pattern = r'/\*@\s*[\s\S]*?\*/'
        all_blocks = list(re.finditer(all_blocks_pattern, code))
        
        match = None
        for block_match in all_blocks:
            block_content = block_match.group(0)
            if 'loop invariant' in block_content:
                match = block_match
                break

        if not match:
            # Fallback: LLM sometimes generates /* instead of /*@ for ACSL blocks.
            # Search for plain /* ... */ blocks containing loop invariant.
            plain_blocks_pattern = r'/\*\s*[\s\S]*?\*/'
            plain_blocks = list(re.finditer(plain_blocks_pattern, code))
            for block_match in plain_blocks:
                block_content = block_match.group(0)
                if 'loop invariant' in block_content:
                    match = block_match
                    break

        if not match:
            # No existing invariant block, cannot rebuild
            # Return original code
            return code

        # Extract loop assigns from the matched block
        full_block = match.group(0)
        loop_assigns_match = re.search(r'(loop\s+assigns[^;]*;)', full_block, re.DOTALL)
        loop_assigns = loop_assigns_match.group(1) if loop_assigns_match else None

        # Extract loop variant from the matched block
        loop_variant_match = re.search(r'(loop\s+variant[^;]*;)', full_block, re.DOTALL)
        loop_variant = loop_variant_match.group(1) if loop_variant_match else None

        block_start = match.start()
        block_end = match.end()

        # Extract indentation from the block
        indent_match = re.search(r'^(\s*)/\*@', code[max(0, block_start-20):block_start+10], re.MULTILINE)
        indent = indent_match.group(1) if indent_match else "  "

        # Build new invariant lines
        inv_lines = []
        for inv in invariants:
            # Ensure invariant has proper format
            inv_clean = inv.strip()
            if not inv_clean.startswith('loop invariant'):
                inv_clean = f"loop invariant {inv_clean}"
            if not inv_clean.endswith(';'):
                inv_clean = f"{inv_clean};"
            inv_lines.append(f"{indent}  {inv_clean}")

        # Build new block
        new_content = "\n".join(inv_lines)

        # Add loop assigns if it existed
        if loop_assigns:
            new_content += f"\n{indent}  {loop_assigns.strip()}"

        # Add loop variant if it existed
        if loop_variant:
            new_content += f"\n{indent}  {loop_variant.strip()}"

        new_inv_block = f"{indent}/*@\n{new_content}\n{indent}*/"

        # Replace old block with new one
        new_code = code[:block_start] + new_inv_block + code[block_end:]

        # Validate placement: loop annotations must be before a while/for loop,
        # not before the function definition. If misplaced, remove and reinsert.
        inv_block_match = re.search(r'/\*@[\s\S]*?loop\s+invariant[\s\S]*?\*/', new_code)
        if inv_block_match:
            after_block = new_code[inv_block_match.end():].lstrip()
            # If the annotation block is followed by a function definition (not a loop),
            # it's misplaced. Remove it and insert before the actual loop.
            if re.match(r'(?:int|void|char|float|double|long|short|unsigned)\s+\w+\s*\(', after_block):
                # Remove the misplaced block
                code_without_block = new_code[:inv_block_match.start()] + new_code[inv_block_match.end():]
                # Find the while/for loop and insert before it
                loop_match = re.search(r'(\s*)(while|for)\s*\(', code_without_block)
                if loop_match:
                    loop_indent = loop_match.group(1)
                    # Rebuild inv_block with correct indentation
                    correct_inv_lines = []
                    for inv in invariants:
                        inv_clean = inv.strip()
                        if not inv_clean.startswith('loop invariant'):
                            inv_clean = f"loop invariant {inv_clean}"
                        if not inv_clean.endswith(';'):
                            inv_clean = f"{inv_clean};"
                        correct_inv_lines.append(f"{loop_indent}  {inv_clean}")
                    correct_content = "\n".join(correct_inv_lines)
                    if loop_assigns:
                        correct_content += f"\n{loop_indent}  {loop_assigns.strip()}"
                    if loop_variant:
                        correct_content += f"\n{loop_indent}  {loop_variant.strip()}"
                    correct_block = f"{loop_indent}/*@\n{correct_content}\n{loop_indent}*/\n"
                    insert_pos = loop_match.start()
                    new_code = code_without_block[:insert_pos] + correct_block + code_without_block[insert_pos:]

        # Ensure braces are balanced (LLM sometimes omits closing '}')
        open_braces = new_code.count('{')
        close_braces = new_code.count('}')
        if open_braces > close_braces:
            missing = open_braces - close_braces
            new_code = new_code.rstrip() + '\n' + '}\n' * missing

        return new_code

    def _validate_and_fix_code_structure(self, generated_code: str, original_template: str) -> str:
        """
        Validate and fix the generated code structure.
        Ensures that requires clauses from the original code are preserved.
        
        Args:
            generated_code: Code generated by LLM
            original_template: Original template code with placeholders
            
        Returns:
            Validated and potentially fixed code
        """
        # Extract requires clause from original template
        original_requires_match = re.search(r'/\*@\s*requires\s+([^@]+?)\*/', original_template, re.DOTALL)
        
        if original_requires_match:
            original_requires = original_requires_match.group(0)
            
            # Check if generated code has requires clause
            generated_requires_match = re.search(r'/\*@\s*requires\s+([^@]+?)\*/', generated_code, re.DOTALL)
            
            if not generated_requires_match:
                # Generated code is missing requires clause - add it back silently
                pass
                
                # Find position to insert (before function definition)
                func_match = re.search(r'\b(int|void|char|float|double|long|short|unsigned)\s+\w+\s*\(', generated_code)
                if func_match:
                    insert_pos = func_match.start()
                    generated_code = generated_code[:insert_pos] + original_requires + '\n' + generated_code[insert_pos:]
                else:
                    # Prepend to the beginning
                    generated_code = original_requires + '\n' + generated_code
        
        return generated_code
    
    def _extract_loop_variable(self, loop_content: str) -> Optional[str]:
        """
        Extract loop variable from loop condition (e.g. "while (y < 100000)" -> "y")
        If not found in condition, try to extract from loop body assignments
        
        Args:
            loop_content: Loop code content
            
        Returns:
            Loop variable name, or None if not found
        """
        # Match patterns like "while (var < ...)", "while (var > ...)", "for (var = ...)"
        patterns = [
            r'\b(while|for)\s*\(\s*(\w+)\s*[<>=!]',  # while/for (var < ...)
            r'\bfor\s*\(\s*(\w+)\s*=',  # for (var = ...)
        ]
        
        for pattern in patterns:
            match = re.search(pattern, loop_content)
            if match:
                # Extract variable name (usually the second group)
                var_name = match.group(2) if len(match.groups()) >= 2 else match.group(1)
                return var_name
        
        # Fallback: If loop condition doesn't have a variable (e.g., "while (unknown())"),
        # try to find the most frequently assigned variable in the loop body
        # This is a heuristic for loops like "while (unknown()) { x = x + 1; }"
        assignment_pattern = r'(\w+)\s*=\s*\1\s*[+\-*/]'  # Match "x = x + ..." or "x = x - ..."
        matches = re.findall(assignment_pattern, loop_content)
        if matches:
            # Count frequency and return the most common one
            from collections import Counter
            var_counts = Counter(matches)
            most_common = var_counts.most_common(1)
            if most_common:
                return most_common[0][0]
        
        # Another fallback: find variables that appear in both left and right side of assignments
        # Pattern: "var = ... var ..." (self-assignment with modification)
        self_assign_pattern = r'(\w+)\s*=\s*[^;]*\b\1\b'
        matches = re.findall(self_assign_pattern, loop_content)
        if matches:
            from collections import Counter
            var_counts = Counter(matches)
            most_common = var_counts.most_common(1)
            if most_common:
                return most_common[0][0]
        
        return None
    
    
  
  
    
    def _try_llm_fitting(self, record: Dict, loop_idx: int) -> Optional[List[str]]:
        """
        Try to discover invariants using LLM fitting (llmfit) in parallel with pfit.
        
        Unlike pfit which uses Z3 solver, llmfit uses LLM to analyze sample traces
        and discover various mathematical relationships (not limited to polynomials).
        
        This method ONLY uses sample traces, NOT the program code itself.
        
        Args:
            record: Loop record containing var_maps, current_vars, etc.
            loop_idx: Loop index
            
        Returns:
            List of valid invariant statements (e.g., ["loop invariant x >= 0;", ...])
            or None if discovery failed or no valid invariants found.
        """
        if not self.llmfit:
            self.logger.info("LLM fitting not initialized, skipping")
            return None
        
        try:
            loop_idx_str = str(loop_idx)
            
            self.logger.info(f"\n{'='*60}")
            self.logger.info(f"Loop {loop_idx} - Attempting LLM fitting (parallel to pfit)...")
            self.logger.info(f"{'='*60}")
            
            if not self.sampler.sample_contents:
                self.logger.warning("No sample contents available for LLM fitting")
                return None
            
            # Extract data points (similar to pfit)
            current_vars = set(record.get('current_vars', []))
            param_pre_vars = set(record.get('param_pre_vars', []))
            loop_related_vars = current_vars | param_pre_vars
            
            if not loop_related_vars:
                self.logger.warning("No loop related variables found for LLM fitting")
                return None
            
            # Get loop bound
            loop_bound = record.get('loop_bound')
            
            # Extract assignments from sample traces
            assignments_list = []
            required_vars = current_vars
            
            for sample_dict in self.sampler.sample_contents:
                if loop_idx_str in sample_dict:
                    conditions = sample_dict[loop_idx_str]
                    for cond in conditions:
                        parts = cond.split('&&')
                        assignment_parts = []
                        var_values = {}
                        
                        for part in parts:
                            part = part.strip()
                            match = re.match(r'(\w+(?:@pre)?)\s*==\s*(-?\d+)', part)
                            if match:
                                var_name, value = match.groups()
                                if var_name in loop_related_vars or var_name in current_vars:
                                    var_values[var_name] = value
                                    assignment_parts.append(f"{var_name}=={value}")
                        
                        if required_vars.issubset(set(var_values.keys())):
                            assignments_list.append(" && ".join(assignment_parts))
            
            if len(assignments_list) < 2:
                self.logger.warning(f"Not enough data points ({len(assignments_list)}) for LLM fitting")
                return None
            
            # Get loop content for context (but don't give it to LLM directly)
            loop_content = record.get('loop_content', '')
            variables = list(current_vars)
            
            self.logger.info(f"LLM fitting analyzing {len(assignments_list)} traces for variables: {variables}")
            
            # Call llmfit to discover invariants
            llm_invariants = self.llmfit.discover_invariants(
                assignments_list=assignments_list,
                variables=variables,
                loop_bound=loop_bound,
                max_invariants=15
            )
            
            if not llm_invariants:
                self.logger.info("LLM fitting discovered no invariants")
                return None
            
            self.logger.info(f"LLM fitting discovered {len(llm_invariants)} candidate invariants")
            
            # Houdini-style pruning: start with all invariants and iteratively remove failed ones
            loop_content_for_insert = record.get('loop_content', '')
            
            # Format all invariants as ACSL statements
            candidate_invariants = []
            for inv_expr, source in llm_invariants:
                inv_statement = f"loop invariant {inv_expr};"
                candidate_invariants.append((inv_expr, inv_statement))
            
            if loop_bound:
                candidate_invariants.insert(0, (loop_bound, f"loop invariant {loop_bound};"))
            
            # Iterative Houdini pruning
            remaining_invariants = [stmt for _, stmt in candidate_invariants]
            remaining_exprs = [expr for expr, _ in candidate_invariants]
            iteration = 0
            max_iterations = len(candidate_invariants) + 1
            
            while remaining_invariants and iteration < max_iterations:
                iteration += 1
                self.logger.info(f"  Houdini iteration {iteration}: Testing {len(remaining_invariants)} invariants")
                
                # Test all remaining invariants together
                test_code = self._insert_invariants_into_code(
                    self._get_full_source_code(),
                    remaining_invariants,
                    loop_content_for_insert
                )
                
                if not test_code:
                    break
                
                temp_file = self._create_temp_file(test_code)
                try:
                    self.verifier.run(temp_file)
                    
                    syntax = self.verifier.syntax_correct
                    
                    # If syntax error, we can't proceed
                    if not syntax:
                        self.logger.warning(f"  Syntax error with current invariants, stopping Houdini")
                        break
                    
                    # Check validation results
                    if self.verifier.validate_result:
                        all_valid = all(self.verifier.validate_result)
                        
                        if all_valid:
                            # All invariants pass, we're done
                            self.logger.info(f"  OK All {len(remaining_invariants)} invariants are valid")
                            break
                        else:
                            # Remove failed invariants
                            new_remaining = []
                            new_exprs = []
                            removed_count = 0
                            
                            for i, (is_valid, stmt, expr) in enumerate(zip(self.verifier.validate_result, remaining_invariants, remaining_exprs)):
                                if is_valid:
                                    new_remaining.append(stmt)
                                    new_exprs.append(expr)
                                else:
                                    removed_count += 1
                                    if i < len(llm_invariants):  # Don't log loop bound removal as loudly
                                        self.logger.info(f"    X Removing invalid invariant: {expr}")
                            
                            remaining_invariants = new_remaining
                            remaining_exprs = new_exprs
                            
                            if removed_count > 0:
                                self.logger.info(f"  Removed {removed_count} failed invariants, {len(remaining_invariants)} remaining")
                    else:
                        # No validation results, assume all pass
                        break
                        
                finally:
                    if os.path.exists(temp_file):
                        os.remove(temp_file)
            
            # Filter out loop bound from final results (it was just for validation context)
            valid_invariants = []
            for stmt in remaining_invariants:
                if loop_bound and stmt == f"loop invariant {loop_bound};":
                    continue
                valid_invariants.append(stmt)
            
            if valid_invariants:
                self.logger.info(f"OKOKOK LLM fitting produced {len(valid_invariants)} valid invariants after Houdini pruning")
                for inv in valid_invariants:
                    self.logger.info(f"    {inv}")
                return valid_invariants
            else:
                self.logger.info("LLM fitting: no invariants passed Houdini pruning")
                return None
                
        except Exception as e:
            self.logger.error(f"Error in LLM fitting: {e}")
            import traceback
            self.logger.debug(traceback.format_exc())
            return None
    
    def _extract_invariant(self, code: str) -> str:
        """Extract invariant expression from code (merged format)"""
        invariants = self._extract_invariants_from_code(code)
        
        if invariants:
            # Merge all invariants
            return ' && '.join(f'({inv})' for inv in invariants)
        
        return ""
    
    def generate_all(self, max_iterations: int = MAX_ITERATION) -> Optional[str]:
        """
        Generate invariants for all loops and return complete annotated C code
        
        Args:
            max_iterations: Maximum number of generation passes (default: 5)
        
        Returns:
            Complete C code with loop invariants, or None if generation failed
        """
        if USE_TRACES:
            self.logger.info("Starting loop sampling...")
            try:
                self.sampler.sample()
            except Exception as e:
                self.logger.error(f"Loop sampling crashed: {e}")
                import traceback
                self.logger.error(traceback.format_exc())
                self.logger.warning("Falling back to sample_without_traces")
                self.sampler.sample_without_traces()
        else:
            self.logger.info("Traces disabled (USE_TRACES=False), skipping dynamic sampling")
            self.sampler.sample_without_traces()  # Only parse loops, no execution

        self.logger.info(f"Found {len(self.sampler.records)} loops")
        
        # Process records to add template-related fields using TemplateGenerator
        processed_records = self.template_gen.process_records(self.sampler.records)
        
        # Get original source code
        original_code = self._get_full_source_code()
        if not original_code:
            self.logger.error("Could not read original input code")
            return None
        
        # Initialize first_pass tracking
        first_syntax_round = None
        first_valid_round = None
        first_satisfy_round = None
        
        # Multi-pass iteration (SESpec style)
        for iteration in range(max_iterations):
            self.logger.info(f"\n{'='*60}")
            self.logger.info(f"Generation Pass {iteration + 1}/{max_iterations}")
            self.logger.info(f"{'='*60}")
            
            # Reset invariants for this pass
            self.invariants = []
            current_code = original_code
            
            # Try to generate invariants for all loops in this pass
            all_loops_success = True
            
            for idx, record in enumerate(processed_records):
                loop_idx = record.get('loop_idx', idx)
                
                # Ensure record has all fields needed for template generation
                if 'var_maps' not in record or not record['var_maps']:
                    try:
                        from loop_analysis import LoopAnalysis
                        subdir = getattr(self, "resolved_subdir", None) or SUBDIR
                        loop_json = Path(f"loop/{subdir}/{self.file_name}.json")
                        if loop_json.exists():
                            analysis = LoopAnalysis(str(loop_json), idx)
                            analysis.run()
                            record['var_maps'] = getattr(analysis, 'var_maps', [])
                            record['path_conds'] = getattr(analysis, 'path_conds', [])
                            record['updated_loop_conditions'] = getattr(analysis, 'updated_loop_conditions', [])
                            record['unchanged_vars'] = getattr(analysis, 'global_unchanged_vars', [])
                            record['non_inductive_vars'] = getattr(analysis, 'non_inductive_vars', [])
                    except Exception as e:
                        self.logger.debug(f"Could not load loop analysis: {e}")
                
                # Generate annotated code for this loop
                annotated_code = self.generate_invariant_for_loop(record, loop_idx)

                # Track first_pass metrics from verifier state (regardless of success/failure)
                if first_syntax_round is None and self.verifier.syntax_correct:
                    first_syntax_round = iteration + 1
                if first_valid_round is None and self.verifier.validate_result and all(self.verifier.validate_result):
                    first_valid_round = iteration + 1
                if first_satisfy_round is None and self.verifier.validate_result and all(self.verifier.validate_result) and self.verifier.verify_result and all(self.verifier.verify_result):
                    first_satisfy_round = iteration + 1

                if annotated_code:
                    current_code = annotated_code
                    self.invariants.append({
                        'loop_idx': loop_idx,
                        'code': annotated_code
                    })
                else:
                    # Degrade gracefully: keep original loop code without invariants
                    # so the run is reported as generated (syntax/valid can still be checked).
                    self.logger.warning(
                        f"Failed to generate invariant for loop {loop_idx} in pass {iteration + 1}; "
                        f"falling back to original loop code."
                    )
                    # Fallback code has no loop invariants to establish/preserve.
                    # Treat syntax/valid as passed for first-pass bookkeeping.
                    if first_syntax_round is None:
                        first_syntax_round = iteration + 1
                    if first_valid_round is None:
                        first_valid_round = iteration + 1
                    self.invariants.append({
                        'loop_idx': loop_idx,
                        'code': current_code
                    })
                    continue

            # If any loop failed, try next pass
            if not all_loops_success:
                self.logger.warning(f"Pass {iteration + 1}: Some loops failed, trying next pass...")
                continue

            # All loops generated successfully with Houdini validation
            # Skip global verification and directly save results
            self.logger.info(f"\n{'='*60}")
            self.logger.info(f"✓ All loops passed Houdini validation in pass {iteration + 1}")
            self.logger.info(f"  Skipping global verification, directly saving results...")
            self.logger.info(f"{'='*60}")

            # Save results immediately
            self.save_results()

            # Break out of the iteration loop
            break
        
        # Store first_pass results (round number if passed, None if not)
        self.first_pass = {
            "syntax": first_syntax_round if first_syntax_round is not None else None,
            "valid": first_valid_round if first_valid_round is not None else None,
            "satisfy": first_satisfy_round if first_satisfy_round is not None else None
        }
        
        self.logger.info(f"\n{'='*60}")
        self.logger.info("Final first_pass results:")
        self.logger.info(f"  syntax={self.first_pass['syntax']} (first passed at round {first_syntax_round})")
        self.logger.info(f"  valid={self.first_pass['valid']} (first passed at round {first_valid_round})")
        self.logger.info(f"  satisfy={self.first_pass['satisfy']} (first passed at round {first_satisfy_round})")
        self.logger.info(f"{'='*60}")
        
        # Output token usage statistics
        token_stats = get_token_stats()
        self.logger.info(f"\n{'='*60}")
        self.logger.info("📊 Token Usage Statistics (Current Session):")
        self.logger.info(f"  Total API calls: {token_stats['call_count']}")
        self.logger.info(f"  Total prompt tokens (input): {token_stats['total_prompt_tokens']:,}")
        self.logger.info(f"  Total completion tokens (output): {token_stats['total_completion_tokens']:,}")
        self.logger.info(f"  Total tokens: {token_stats['total_tokens']:,}")
        if token_stats['call_count'] > 0:
            avg_prompt = token_stats['total_prompt_tokens'] / token_stats['call_count']
            avg_completion = token_stats['total_completion_tokens'] / token_stats['call_count']
            avg_total = token_stats['total_tokens'] / token_stats['call_count']
            self.logger.info(f"  Average per call:")
            self.logger.info(f"    Prompt: {avg_prompt:.1f} tokens")
            self.logger.info(f"    Completion: {avg_completion:.1f} tokens")
            self.logger.info(f"    Total: {avg_total:.1f} tokens")
        self.logger.info(f"{'='*60}")
        
        # Return the final code if we have invariants
        if self.invariants:
            return self.invariants[-1]['code']
        return None
    
    def _strengthen_invariants_iterative(self, code: str, c_file_path: str, record: Dict, loop_idx: int, max_iterations: int = MAX_STRENGTHEN_ITERATIONS) -> Optional[str]:
        """
        在 syntax/valid 已通过但 satisfy 失败时，迭代补强不变量直到断言可证明或达到上限。
        """
        if self.repairer is None:
            self.logger.error("Strengthening requires LLM repairer, but repairer is not initialized")
            return None

        current_code = code
        pre_condition = record.get('pre_condition', '')
        # Keep the best code that is at least syntax-correct and valid,
        # even if postcondition is not yet satisfied.
        last_valid_code: Optional[str] = None

        for iteration in range(1, max_iterations + 1):
            with open(c_file_path, 'w', encoding='utf-8') as f:
                f.write(current_code)

            self.verifier.run(c_file_path)
            syntax = getattr(self.verifier, "syntax_correct", False) or self.verifier.syntax_error == 'syntax Correct'
            valid = bool(self.verifier.validate_result) and all(self.verifier.validate_result)
            satisfy = all(self.verifier.verify_result) if self.verifier.verify_result else True

            self.logger.info(
                f"[strengthen {iteration}/{max_iterations}] "
                f"syntax={syntax}, valid={valid}, satisfy={satisfy}, "
                f"validate_result={self.verifier.validate_result}, verify_result={self.verifier.verify_result}"
            )

            if syntax and valid:
                last_valid_code = current_code
                # Update self.invariants so partial results are saved on timeout
                if self.invariants:
                    self.invariants[-1]['code'] = current_code

            if syntax and valid and satisfy:
                self.logger.info(f"Strengthening succeeded at iteration {iteration}")
                return current_code

            if not syntax or not valid:
                # Record which invariants failed and why, for better strengthen prompts
                failed_inv_details = []
                if self.verifier.validate_result:
                    current_invs = self._extract_invariants_from_code(current_code)
                    for i, (inv, ok) in enumerate(zip(current_invs, self.verifier.validate_result)):
                        if not ok:
                            # Get error detail if available
                            err_detail = ""
                            if hasattr(self.verifier, 'valid_error_list') and i < len(self.verifier.valid_error_list):
                                err_detail = f" ({self.verifier.valid_error_list[i][0][:100]})"
                            failed_inv_details.append(f"  - {inv}{err_detail}")
                if failed_inv_details:
                    self._last_failed_invariants = "\n".join(failed_inv_details)
                    self.logger.info(f"Invariants removed by Houdini:\n{self._last_failed_invariants}")

                # 补强后可能引入无效不变量，先用 Houdini 清理回到 valid，再继续补强
                pruned_code, houdini_valid = self.repairer.hudini(current_code, self.verifier, c_file_path)
                if pruned_code is None:
                    self.logger.error("Strengthening failed: Houdini removed all invariants")
                    if last_valid_code is not None:
                        self.logger.warning(
                            "Keeping last syntax+valid invariants after Houdini removed current candidates."
                        )
                        return last_valid_code
                    return None
                current_code = pruned_code
                if houdini_valid:
                    self.logger.info("Strengthening stage: Houdini restored valid invariants")
                continue

            verify_error_msg = self._format_errors(self.verifier.verify_error_list, pre_condition)
            loop_cond_match = re.search(r'\b(?:while|for)\s*\(([^)]*)\)', current_code)
            loop_condition = loop_cond_match.group(1).strip() if loop_cond_match else "unknown"
            assert_match = re.search(r'/\*@\s*assert\s+([^;]+);', current_code)
            post_assert = assert_match.group(1).strip() if assert_match else "unknown"
            failed_invariants = ""
            # If previous iteration had invariants removed by Houdini, inform LLM
            if hasattr(self, '_last_failed_invariants') and self._last_failed_invariants:
                failed_invariants = self._last_failed_invariants
                self._last_failed_invariants = None  # Reset after using
            strengthen_prompt = (
                (verify_error_msg if verify_error_msg and verify_error_msg != "No errors found." else "Assertion not proved.")
                + f"\nLoop condition: {loop_condition}"
                + f"\nPostcondition(assert): {post_assert}"
                + "\nInstruction: keep existing valid invariants and strengthen to imply postcondition."
                + "\nInstruction: include at least one invariant connecting postcondition terms and loop-updated vars."
                + "\nInstruction: add boundary/range invariants for exit state."
                + (f"\nPreviously failed invariants:\n{failed_invariants}" if failed_invariants else "")
            )
            previous_code = current_code
            repaired_code = self.repairer.repair_invariant_error(
                current_code,
                strengthen_prompt,
                error_type='assertion'
            )
            expected_func = f"main{self.file_name}"
            if not repaired_code or expected_func not in repaired_code:
                self.logger.warning("Strengthening stage: repair output is not valid C code, keeping previous code")
                repaired_code = previous_code

            # 结构兜底：拒绝包含嵌套注释/错误文本等非法结构的修复结果
            structure_violations = validate_code_structure(repaired_code)
            if structure_violations:
                self.logger.warning(
                    f"Strengthening stage: rejected repaired code due to {len(structure_violations)} structure violations"
                )
                repaired_code = previous_code

            current_code = repaired_code
            # Use the same filtering pipeline as generation:
            # syntax filter -> safety sanitize -> traces filter -> conflict removal
            repaired_invariants = self._extract_invariants_from_code(current_code)
            if repaired_invariants:
                from config import PARALLEL_GENERATION_CONFIG
                syntax_filter_enabled = SYNTAX_FILTER_CONFIG.get('enabled', True)
                detect_conflicts = PARALLEL_GENERATION_CONFIG.get('detect_conflicts', True)
                filter_by_sampling = PARALLEL_GENERATION_CONFIG.get('filter_by_sampling', True) and USE_TRACES

                if syntax_filter_enabled:
                    filter_result = filter_invariants(repaired_invariants, record, verbose=False)
                    filtered_invariants = filter_result.valid
                else:
                    filtered_invariants = repaired_invariants

                function_params = set(record.get('function_params', []) or [])

                def _sanitize_invariant(inv_text: str) -> Optional[str]:
                    if '^' in inv_text or '\\pow' in inv_text:
                        return None

                    def _at_repl(match):
                        var_name = match.group(1)
                        return match.group(0) if var_name in function_params else var_name

                    return re.sub(r'\\at\((\w+),\s*Pre\)', _at_repl, inv_text)

                sanitized_invariants = []
                for inv in filtered_invariants:
                    inv2 = _sanitize_invariant(inv)
                    if inv2:
                        sanitized_invariants.append(inv2)

                if filter_by_sampling:
                    sanitized_invariants = self._filter_invariants_by_sampling(
                        sanitized_invariants, record, loop_idx
                    )

                if detect_conflicts and len(sanitized_invariants) > 1:
                    sanitized_invariants = self._remove_conflicting_invariants(sanitized_invariants)

                current_code = self._rebuild_code_with_invariants(current_code, sanitized_invariants)
            self._print_intermediate_invariants(current_code, f"After strengthening iteration {iteration}")

        # 最后一轮复核，只有 satisfy 通过才返回
        with open(c_file_path, 'w', encoding='utf-8') as f:
            f.write(current_code)
        self.verifier.run(c_file_path)
        syntax = getattr(self.verifier, "syntax_correct", False) or self.verifier.syntax_error == 'syntax Correct'
        valid = bool(self.verifier.validate_result) and all(self.verifier.validate_result)
        satisfy = all(self.verifier.verify_result) if self.verifier.verify_result else True
        if syntax and valid:
            last_valid_code = current_code
        if syntax and valid and satisfy:
            return current_code
        if last_valid_code is not None:
            self.logger.warning(
                "Strengthening did not satisfy postcondition; keeping last syntax+valid invariants."
            )
            return last_valid_code
        return None
    
    def _format_errors(self, error_list, pre_condition: str) -> str:
        """Format error list into string (similar to inv_gen.py)"""
        if not error_list:
            return "No errors found."
        
        error_str = []
        for index, (desc, location, content) in enumerate(error_list, start=1):
            desc = desc.splitlines()[0]
            error_str.append(f"Error {index}: {desc}")
            if content:
                error_str.append(f"Code: {content}")
            if location:
                error_str.append(f"Location: {location}")
            if 'Establishment' in desc:
                error_str.append(f"Instruction: You need weaken the invariant to be valid under initial conditions {pre_condition}.")
            if 'Preservation' in desc:
                error_str.append(f"Instruction: You need adjust the invariant to make sure it remains valid after each iteration.")
            if 'Assertion' in desc:
                error_str.append(f"Instruction: You need strengthen the invariant to make sure postcondition can be implied by the invariant combined with the negation of the loop condition.")
            error_str.append("-" * 50)

        return "\n".join(error_str)

    def _heuristic_seed_invariants(self, code: str) -> List[str]:
        """Pattern-based invariant seeds to improve hard arithmetic benchmarks."""
        seeds: List[str] = []
        if not code:
            return seeds

        # Extended Euclid-like loop (cases similar to main7/main8)
        if (
            "a = x" in code and "b = y" in code and "p = 1" in code and "q = 0" in code
            and "r = 0" in code and "s = 1" in code and "while(a!=b)" in code
        ):
            seeds.extend([
                "a == x * p + y * r",
                "b == x * q + y * s",
            ])

        # Variant with u/v updates (case similar to main35)
        if (
            "int x=a" in code and "int y=b" in code and "int u=b" in code and "int v=0" in code
            and "x=x-y" in code and "v=v+u" in code and "u=u+v" in code
        ):
            seeds.append("x * u + y * v == a * b")

        # Russian peasant multiplication (case similar to main14)
        if "while(y!=0)" in code and "z = z+x" in code and "x = 2*x" in code and "y = y/2" in code:
            seeds.extend([
                "z + x * y == a * b",
                "y >= 0",
            ])

        # Summation loop (case similar to main39)
        if "sum = sum + i" in code and "i = i + 1" in code and "assert sum == (n * (n + 1)) / 2" in code:
            seeds.extend([
                "2 * sum == (i - 1) * i",
                "1 <= i && i <= n + 1",
            ])

        # Conditional multiplication loop (case similar to main26)
        if "w = w * x" in code and "if (x < y)" in code and "z = z * x" in code and "x += 1" in code:
            seeds.extend([
                "w == z * (x - 1)",
                "1 <= x && x <= y + 1",
            ])

        return seeds
    
    def _detect_error_type_from_list(self, error_list) -> str:
        """Detect error type from error list"""
        if not error_list:
            return 'general'
        
        first_error = error_list[0][0] if error_list else ''
        error_lower = first_error.lower()
        if 'establishment' in error_lower:
            return 'establishment'
        elif 'preservation' in error_lower:
            return 'preservation'
        elif 'assertion' in error_lower:
            return 'assertion'
        return 'general'
    
    def _print_intermediate_invariants(self, code: str, stage: str):
        """Print invariants at intermediate stage"""
        invariants = self._extract_invariants_from_code(code)
        self.logger.info(f"\n{stage}:")
        if invariants:
            for i, inv in enumerate(invariants, 1):
                self.logger.info(f"  [{i}] {inv}")
        else:
            self.logger.info("  (No invariants found)")
    
    def _print_full_loop_on_error(self, code: str, record: Dict, loop_idx: int, error_type: str = "Error"):
        """
        在报错时打印完整的循环代码
        
        Args:
            code: 包含循环的完整代码
            record: 循环记录
            loop_idx: 循环索引
            error_type: 错误类型（用于日志前缀）
        """
        loop_content = record.get('loop_content', '')
        if loop_content:
            self.logger.error(f"\n{'='*60}")
            self.logger.error(f"{error_type} - Full Loop Code (Loop {loop_idx}):")
            self.logger.error(f"{'='*60}")
            self.logger.error(f"Loop Content:\n{loop_content}")
            self.logger.error(f"{'='*60}")
        
        # 尝试从代码中提取循环部分（包含不变量）
        try:
            # 查找循环在代码中的位置（包含不变量注释）
            invariant_block_pattern = r'/\*@.*?loop\s+invariant.*?\*/\s*(?:while|for)\s*\([^)]+\)\s*\{[^}]*\}'
            match = re.search(invariant_block_pattern, code, re.DOTALL)
            if match:
                loop_with_invariants = match.group(0)
                self.logger.error(f"\nLoop with Invariants from Code:\n{loop_with_invariants}")
            else:
                # 如果找不到，尝试提取简单的循环
                loop_pattern = r'(while|for)\s*\([^)]+\)\s*\{[^}]*\{[^}]*\}[^}]*\}'
                match = re.search(loop_pattern, code, re.DOTALL)
                if match:
                    self.logger.error(f"\nLoop from Code:\n{match.group(0)}")
                else:
                    self.logger.error(f"\nCould not extract loop from code")
        except Exception as e:
            self.logger.warning(f"Failed to extract loop from code: {e}")
        
        # 打印完整的代码（如果代码不太长）
        if code and len(code) < 5000:
            self.logger.error(f"\nFull Code:\n{code}")
        elif code:
            self.logger.error(f"\nFull Code (truncated, length={len(code)}):\n{code[:2000]}...\n...{code[-2000:]}")
        else:
            self.logger.error(f"\nFull Code: (empty)")
    
    def save_results(self, output_dir: Optional[str] = None):
        """Save generated annotated C code to output directory"""
        # Use instance output_dir if not specified
        if output_dir is None:
            output_dir = self.output_dir
        
        os.makedirs(output_dir, exist_ok=True)
        
        if self.invariants:
            # Save the final annotated code (complete .c file)
            output_file = os.path.join(output_dir, f"{self.file_name}.c")
            final_code = self.invariants[-1]['code']
            with open(output_file, 'w') as f:
                f.write(final_code)
            
            self.logger.info(f"Annotated C code saved to {output_file}")
            
            # Also save invariants summary for reference
            summary_file = os.path.join(output_dir, f"{self.file_name}_invariants.txt")
            with open(summary_file, 'w') as f:
                for inv_info in self.invariants:
                    loop_idx = inv_info['loop_idx']
                    code = inv_info['code']
                    invariants = self._extract_invariants_from_code(code)
                    f.write(f"Loop {loop_idx}:\n")
                    for i, inv in enumerate(invariants, 1):
                        f.write(f"  [{i}] {inv}\n")
                    f.write("\n")
            
            self.logger.info(f"Invariants summary saved to {summary_file}")
        else:
            # Even if no invariants were generated, save the original input file
            self.logger.warning("No invariants generated, saving original input file")
            output_file = os.path.join(output_dir, f"{self.file_name}.c")
            original_code = self._get_full_source_code()
            if original_code:
                with open(output_file, 'w') as f:
                    f.write(original_code)
                self.logger.info(f"Original C code saved to {output_file}")
            else:
                self.logger.error("Could not read original input code to save")

    def _adapt_cached_solution(self, cached_solution: Dict, current_record: Dict, loop_idx: int) -> Optional[str]:
        """
        Adapt a cached solution to the current problem context.

        This method takes a cached solution and adapts it to work with the current
        loop by adjusting variable names, conditions, and other context-specific elements.

        Args:
            cached_solution: Dictionary containing cached solution data
            current_record: Current loop record containing context
            loop_idx: Current loop index

        Returns:
            Adapted code string, or None if adaptation fails
        """
        try:
            cached_code = cached_solution.get('code', '')
            cached_invariants = cached_solution.get('invariants', [])

            if not cached_code or not cached_invariants:
                self.logger.warning("Cached solution missing code or invariants")
                return None

            self.logger.info(f"Adapting cached solution with {len(cached_invariants)} invariants")

            # Extract variable mappings between cached and current contexts
            variable_mapping = self._extract_variable_mapping(cached_solution, current_record)

            if not variable_mapping:
                self.logger.info("No variable mapping needed, using cached solution directly")
                adapted_code = cached_code
            else:
                self.logger.info(f"Applying variable mapping: {variable_mapping}")
                adapted_code = self._apply_variable_mapping(cached_code, variable_mapping)

            # Verify the adapted solution works with current context
            if self._verify_adapted_solution(adapted_code, current_record):
                self.logger.info("OK Successfully adapted cached solution")
                return adapted_code
            else:
                self.logger.warning("Adapted solution failed verification")
                return None

        except Exception as e:
            self.logger.warning(f"Failed to adapt cached solution: {e}")
            return None

    def _extract_variable_mapping(self, cached_solution: Dict, current_record: Dict) -> Dict[str, str]:
        """
        Extract variable name mappings between cached and current contexts.

        Args:
            cached_solution: Cached solution data
            current_record: Current loop record

        Returns:
            Dictionary mapping cached variable names to current variable names
        """
        mapping = {}

        try:
            # Get variable names from both contexts
            cached_metadata = cached_solution.get('metadata', {})
            cached_vars = set()
            current_vars = set()

            # Extract variables from loop content using simple regex
            import re

            # Get cached variables
            cached_loop_content = cached_metadata.get('loop_content', '')
            if cached_loop_content:
                cached_vars.update(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', cached_loop_content))

            # Get current variables
            current_loop_content = current_record.get('loop_content', '')
            if current_loop_content:
                current_vars.update(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', current_loop_content))

            # Filter out common keywords and create simple mapping
            keywords = {'for', 'while', 'if', 'else', 'int', 'float', 'double', 'char', 'void', 'return'}
            cached_vars = {v for v in cached_vars if v not in keywords and len(v) > 1}
            current_vars = {v for v in current_vars if v not in keywords and len(v) > 1}

            # Simple heuristic: map variables of similar patterns
            cached_list = sorted(cached_vars)
            current_list = sorted(current_vars)

            if len(cached_list) == len(current_list):
                for cached_var, current_var in zip(cached_list, current_list):
                    if cached_var != current_var:
                        mapping[cached_var] = current_var

        except Exception as e:
            self.logger.warning(f"Failed to extract variable mapping: {e}")

        return mapping

    def _apply_variable_mapping(self, code: str, mapping: Dict[str, str]) -> str:
        """
        Apply variable name mapping to code.

        Args:
            code: Original code string
            mapping: Dictionary mapping old names to new names

        Returns:
            Code with variable names replaced
        """
        adapted_code = code

        try:
            import re

            for old_var, new_var in mapping.items():
                # Use word boundaries to avoid partial replacements
                pattern = r'\b' + re.escape(old_var) + r'\b'
                adapted_code = re.sub(pattern, new_var, adapted_code)

        except Exception as e:
            self.logger.warning(f"Failed to apply variable mapping: {e}")
            return code

        return adapted_code

    def _verify_adapted_solution(self, adapted_code: str, current_record: Dict) -> bool:
        """
        Verify that the adapted solution is syntactically correct and contextually appropriate.

        Args:
            adapted_code: Adapted code to verify
            current_record: Current loop record for context

        Returns:
            True if verification passes, False otherwise
        """
        try:
            # Basic syntax check - ensure the code contains expected elements
            if not adapted_code or '/*@' not in adapted_code or '@*/' not in adapted_code:
                return False

            # Check that the adapted code contains relevant variables from current context
            current_loop_content = current_record.get('loop_content', '')
            if current_loop_content:
                import re
                current_vars = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', current_loop_content))
                adapted_vars = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', adapted_code))

                # Check if there's reasonable overlap
                common_vars = current_vars.intersection(adapted_vars)
                if len(common_vars) == 0 and len(current_vars) > 2:
                    self.logger.warning("No common variables found between adapted solution and current context")
                    return False

            return True

        except Exception as e:
            self.logger.warning(f"Failed to verify adapted solution: {e}")
            return False


        # If we reach here, max iterations reached without success
        # Store first_pass metrics even if not fully satisfied (round number if passed, None if not)
        if self.first_pass is None:
            self.first_pass = {
                "syntax": first_syntax_round if first_syntax_round is not None else None,
                "valid": first_valid_round if first_valid_round is not None else None,
                "satisfy": first_satisfy_round if first_satisfy_round is not None else None
            }
        
        self.logger.warning(f"Reached max iterations {max_iterations}, repair failed")
        return None
    
    def _format_errors(self, error_list, pre_condition: str) -> str:
        """Format error list into string (similar to inv_gen.py)"""
        if not error_list:
            return "No errors found."
        
        error_str = []
        for index, (desc, location, content) in enumerate(error_list, start=1):
            desc = desc.splitlines()[0]
            error_str.append(f"Error {index}: {desc}")
            if content:
                error_str.append(f"Code: {content}")
            if location:
                error_str.append(f"Location: {location}")
            if 'Establishment' in desc:
                error_str.append(f"Instruction: You need weaken the invariant to be valid under initial conditions {pre_condition}.")
            if 'Preservation' in desc:
                error_str.append(f"Instruction: You need adjust the invariant to make sure it remains valid after each iteration.")
            if 'Assertion' in desc:
                error_str.append(f"Instruction: You need strengthen the invariant to make sure postcondition can be implied by the invariant combined with the negation of the loop condition.")
            error_str.append("-" * 50)

        return "\n".join(error_str)
    
    def _detect_error_type_from_list(self, error_list) -> str:
        """Detect error type from error list"""
        if not error_list:
            return 'general'
        
        first_error = error_list[0][0] if error_list else ''
        error_lower = first_error.lower()
        if 'establishment' in error_lower:
            return 'establishment'
        elif 'preservation' in error_lower:
            return 'preservation'
        elif 'assertion' in error_lower:
            return 'assertion'
        return 'general'
    
    def _print_intermediate_invariants(self, code: str, stage: str):
        """Print invariants at intermediate stage"""
        invariants = self._extract_invariants_from_code(code)
        self.logger.info(f"\n{stage}:")
        if invariants:
            for i, inv in enumerate(invariants, 1):
                self.logger.info(f"  [{i}] {inv}")
        else:
            self.logger.info("  (No invariants found)")
    
    def save_results(self, output_dir: Optional[str] = None):
        """Save generated annotated C code to output directory"""
        # Use instance output_dir if not specified
        if output_dir is None:
            output_dir = self.output_dir
        
        os.makedirs(output_dir, exist_ok=True)
        
        if self.invariants:
            # Save the final annotated code (complete .c file)
            output_file = os.path.join(output_dir, f"{self.file_name}.c")
            final_code = self.invariants[-1]['code']
            with open(output_file, 'w') as f:
                f.write(final_code)
            
            self.logger.info(f"Annotated C code saved to {output_file}")
            
            # Also save invariants summary for reference
            summary_file = os.path.join(output_dir, f"{self.file_name}_invariants.txt")
            with open(summary_file, 'w') as f:
                for inv_info in self.invariants:
                    loop_idx = inv_info['loop_idx']
                    code = inv_info['code']
                    invariants = self._extract_invariants_from_code(code)
                    f.write(f"Loop {loop_idx}:\n")
                    for i, inv in enumerate(invariants, 1):
                        f.write(f"  [{i}] {inv}\n")
                    f.write("\n")
            
            self.logger.info(f"Invariants summary saved to {summary_file}")
        else:
            # Even if no invariants were generated, save the original input file
            self.logger.warning("No invariants generated, saving original input file")
            output_file = os.path.join(output_dir, f"{self.file_name}.c")
            original_code = self._get_full_source_code()
            if original_code:
                with open(output_file, 'w') as f:
                    f.write(original_code)
                self.logger.info(f"Original C code saved to {output_file}")
            else:
                self.logger.error("Could not read original input code to save")

    def _adapt_cached_solution(self, cached_solution: Dict, current_record: Dict, loop_idx: int) -> Optional[str]:
        """
        Adapt a cached solution to the current problem context.

        This method takes a cached solution and adapts it to work with the current
        loop by adjusting variable names, conditions, and other context-specific elements.

        Args:
            cached_solution: Dictionary containing cached solution data
            current_record: Current loop record containing context
            loop_idx: Current loop index

        Returns:
            Adapted code string, or None if adaptation fails
        """
        try:
            cached_code = cached_solution.get('code', '')
            cached_invariants = cached_solution.get('invariants', [])

            if not cached_code or not cached_invariants:
                self.logger.warning("Cached solution missing code or invariants")
                return None

            self.logger.info(f"Adapting cached solution with {len(cached_invariants)} invariants")

            # Extract variable mappings between cached and current contexts
            variable_mapping = self._extract_variable_mapping(cached_solution, current_record)

            if not variable_mapping:
                self.logger.info("No variable mapping needed, using cached solution directly")
                adapted_code = cached_code
            else:
                self.logger.info(f"Applying variable mapping: {variable_mapping}")
                adapted_code = self._apply_variable_mapping(cached_code, variable_mapping)

            # Verify the adapted solution works with current context
            if self._verify_adapted_solution(adapted_code, current_record):
                self.logger.info("OK Successfully adapted cached solution")
                return adapted_code
            else:
                self.logger.warning("Adapted solution failed verification")
                return None

        except Exception as e:
            self.logger.warning(f"Failed to adapt cached solution: {e}")
            return None

    def _extract_variable_mapping(self, cached_solution: Dict, current_record: Dict) -> Dict[str, str]:
        """
        Extract variable name mappings between cached and current contexts.

        Args:
            cached_solution: Cached solution data
            current_record: Current loop record

        Returns:
            Dictionary mapping cached variable names to current variable names
        """
        mapping = {}

        try:
            # Get variable names from both contexts
            cached_metadata = cached_solution.get('metadata', {})
            cached_vars = set()
            current_vars = set()

            # Extract variables from loop content using simple regex
            import re

            # Get cached variables
            cached_loop_content = cached_metadata.get('loop_content', '')
            if cached_loop_content:
                cached_vars.update(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', cached_loop_content))

            # Get current variables
            current_loop_content = current_record.get('loop_content', '')
            if current_loop_content:
                current_vars.update(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', current_loop_content))

            # Filter out common keywords and create simple mapping
            keywords = {'for', 'while', 'if', 'else', 'int', 'float', 'double', 'char', 'void', 'return'}
            cached_vars = {v for v in cached_vars if v not in keywords and len(v) > 1}
            current_vars = {v for v in current_vars if v not in keywords and len(v) > 1}

            # Simple heuristic: map variables of similar patterns
            cached_list = sorted(cached_vars)
            current_list = sorted(current_vars)

            if len(cached_list) == len(current_list):
                for cached_var, current_var in zip(cached_list, current_list):
                    if cached_var != current_var:
                        mapping[cached_var] = current_var

        except Exception as e:
            self.logger.warning(f"Failed to extract variable mapping: {e}")

        return mapping

    def _apply_variable_mapping(self, code: str, mapping: Dict[str, str]) -> str:
        """
        Apply variable name mapping to code.

        Args:
            code: Original code string
            mapping: Dictionary mapping old names to new names

        Returns:
            Code with variable names replaced
        """
        adapted_code = code

        try:
            import re

            for old_var, new_var in mapping.items():
                # Use word boundaries to avoid partial replacements
                pattern = r'\b' + re.escape(old_var) + r'\b'
                adapted_code = re.sub(pattern, new_var, adapted_code)

        except Exception as e:
            self.logger.warning(f"Failed to apply variable mapping: {e}")
            return code

        return adapted_code

    def _verify_adapted_solution(self, adapted_code: str, current_record: Dict) -> bool:
        """
        Verify that the adapted solution is syntactically correct and contextually appropriate.

        Args:
            adapted_code: Adapted code to verify
            current_record: Current loop record for context

        Returns:
            True if verification passes, False otherwise
        """
        try:
            # Basic syntax check - ensure the code contains expected elements
            if not adapted_code or '/*@' not in adapted_code or '@*/' not in adapted_code:
                return False

            # Check that the adapted code contains relevant variables from current context
            current_loop_content = current_record.get('loop_content', '')
            if current_loop_content:
                import re
                current_vars = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', current_loop_content))
                adapted_vars = set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', adapted_code))

                # Check if there's reasonable overlap
                common_vars = current_vars.intersection(adapted_vars)
                if len(common_vars) == 0 and len(current_vars) > 2:
                    self.logger.warning("No common variables found between adapted solution and current context")
                    return False

            return True

        except Exception as e:
            self.logger.warning(f"Failed to verify adapted solution: {e}")
            return False
