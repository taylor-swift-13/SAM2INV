"""
循环不变量生成主程序
整合采样、生成、验证和迭代修复

使用方法:
    python3 loop_inv.py 2
"""
import argparse
import logging
import os
import re
import signal
import shutil
import sys
import tempfile
import time
from run_dirs import resolve_run_dirs
from inv_generator import InvariantGenerator
from llm import LLMConfig, reset_token_stats, get_token_stats
from config import SUBDIR, MAX_ITERATION
from output_verify import OutputVerifier

# 配置：input 子目录（单一入口）
INPUT_SUBDIR = SUBDIR  # 默认值，可以通过命令行参数覆盖
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def _mask_assertions(code: str):
    """Replace ACSL assertions with placeholders for mask-mode generation."""
    placeholders = []
    idx = 0

    def _next_placeholder() -> str:
        nonlocal idx
        token = f"/*__SAM2INV_MASK_ASSERT_{idx}__*/"
        idx += 1
        return token

    # Block-style assertions: /*@ assert ...; */
    block_pat = re.compile(r"/\*@\s*assert\b[\s\S]*?;\s*\*/", re.IGNORECASE)

    def _block_repl(match):
        token = _next_placeholder()
        placeholders.append((token, match.group(0)))
        return token

    masked = block_pat.sub(_block_repl, code)

    # Line-style assertions: //@ assert ...;
    line_pat = re.compile(r"^[ \t]*//@\s*assert\b[^\n]*(?:\n|$)", re.IGNORECASE | re.MULTILINE)

    def _line_repl(match):
        token = _next_placeholder() + "\n"
        placeholders.append((token.strip(), match.group(0)))
        return token

    masked = line_pat.sub(_line_repl, masked)
    return masked, placeholders


def _restore_assertions(code: str, placeholders):
    restored = code
    for token, original in placeholders:
        restored = restored.replace(token, original)
    return restored


def _prepare_masked_input(file_name: str, input_subdir: str, logger: logging.Logger):
    input_root = os.path.join(SCRIPT_DIR, "input")
    src_path = os.path.join(input_root, input_subdir, f"{file_name}.c")
    if not os.path.exists(src_path):
        raise FileNotFoundError(f"Input file not found: {src_path}")

    with open(src_path, "r", encoding="utf-8") as f:
        original = f.read()

    masked, placeholders = _mask_assertions(original)
    if not placeholders:
        logger.info("Mask mode enabled, but no assertion found; generation proceeds unchanged.")
        return None

    safe_subdir = re.sub(r"[^A-Za-z0-9_.-]+", "_", input_subdir)
    # Keep masked subdir as a single-level folder name (no "/"),
    # so relative includes like "../../input/verification_stdlib.h"
    # remain valid in unfold/outer intermediate files.
    mask_subdir = f"__masked__{safe_subdir}_{os.getpid()}_{int(time.time()*1000)}"
    abs_mask_dir = os.path.join(input_root, mask_subdir)
    os.makedirs(abs_mask_dir, exist_ok=True)

    masked_path = os.path.join(abs_mask_dir, f"{file_name}.c")
    with open(masked_path, "w", encoding="utf-8") as f:
        f.write(masked)

    logger.info(f"Mask mode: replaced {len(placeholders)} assertion(s) before generation.")
    return {
        "mask_subdir": mask_subdir,
        "mask_dir": abs_mask_dir,
        "placeholders": placeholders,
    }

def setup_logger(file_name: str, log_dir: str = None) -> logging.Logger:
    """
    设置日志记录器，将日志输出到文件和控制台
    日志目录会自动与 input/output 结构对齐
    
    Args:
        file_name: 文件名（不含扩展名）
        log_dir: 日志目录（如果为 None，则自动对齐 input 路径）
        
    Returns:
        配置好的日志记录器
    """
    # 如果未指定 log_dir，则按全局 subdir 自动对齐
    if log_dir is None:
        log_dir = os.path.join("log", INPUT_SUBDIR)
    
    # 确保日志目录存在
    os.makedirs(log_dir, exist_ok=True)
    
    # 创建日志记录器
    logger = logging.getLogger('SE2INV')
    logger.setLevel(logging.INFO)
    
    # 清除已有的处理器
    logger.handlers.clear()
    
    # 文件处理器
    # Remove .c extension if present to avoid duplicate extension in log filename
    log_file_name = file_name[:-2] if file_name.endswith('.c') else file_name
    log_file_path = os.path.join(log_dir, f'{log_file_name}.log')
    file_handler = logging.FileHandler(log_file_path, mode='w', encoding='utf-8')
    file_handler.setLevel(logging.INFO)
    file_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    file_handler.setFormatter(file_formatter)
    logger.addHandler(file_handler)
    
    # 控制台处理器
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.INFO)
    console_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    console_handler.setFormatter(console_formatter)
    logger.addHandler(console_handler)
    
    return logger

def main():
    global INPUT_SUBDIR
    parser = argparse.ArgumentParser(
        description="生成循环不变量（包含迭代修复）",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python3 loop_inv.py 2
        """
    )
    parser.add_argument('file_name', type=str, help="文件名（不含扩展名）")
    parser.add_argument('--input-subdir', type=str, default=INPUT_SUBDIR, help=f"input 子目录（默认: {INPUT_SUBDIR}）")
    parser.add_argument('--output-dir', type=str, default=None, help="输出目录（默认按配置自动生成）")
    parser.add_argument('--log-dir', type=str, default=None, help="日志目录（默认自动对齐 input 路径）")
    parser.add_argument('--max-iterations', type=int, default=MAX_ITERATION, help="最大迭代修复次数")
    parser.add_argument('--mask-mode', action='store_true', help="mask 模式：移除 assertion 生成不变量，再恢复 assertion 验证")
    
    args = parser.parse_args()
    INPUT_SUBDIR = args.input_subdir  # 更新全局配置
    
    # 统一输出/日志目录策略：output/<test_set>_<timestamp>, log/<test_set>_<timestamp>
    resolved_output_dir, resolved_log_dir, resolved_test_set, run_tag = resolve_run_dirs(
        test_set=args.input_subdir,
        output_dir=args.output_dir,
        log_dir=args.log_dir,
    )
    os.environ["SAM2INV_OUTPUT_DIR"] = resolved_output_dir
    os.environ["SAM2INV_LOG_DIR"] = resolved_log_dir
    os.environ["SAM2INV_TEST_SET"] = resolved_test_set
    os.environ["SAM2INV_RUN_TAG"] = run_tag

    # 重置 token 统计（开始新的分析时）
    reset_token_stats()
    
    # 设置日志记录器（自动对齐 input 路径）
    logger = setup_logger(args.file_name, log_dir=resolved_log_dir)
    
    # 记录开始时间
    start_time = time.time()
    
    # 创建不变量生成器（传入 input_subdir 配置）
    mask_ctx = None
    effective_input_subdir = INPUT_SUBDIR
    if args.mask_mode:
        mask_ctx = _prepare_masked_input(args.file_name, INPUT_SUBDIR, logger)
        if mask_ctx is not None:
            effective_input_subdir = mask_ctx["mask_subdir"]

    generator = InvariantGenerator(
        args.file_name,
        LLMConfig(),
        logger,
        output_dir=resolved_output_dir,
        input_subdir=effective_input_subdir,
        collect_dpo=False,
    )
    
    # 设置最大迭代次数（仅在 repairer 存在时）
    if generator.repairer is not None:
        generator.repairer.max_iterations = args.max_iterations
    
    # Register SIGTERM handler to save partial results on timeout
    def _sigterm_handler(signum, frame):
        logger.warning("Received SIGTERM (timeout), saving partial results...")
        generator.save_results(resolved_output_dir)
        # Log partial first_pass if available
        first_pass = generator.first_pass if hasattr(generator, 'first_pass') and generator.first_pass else None
        if first_pass:
            logger.info(f"syntax={first_pass.get('syntax', 'N/A')}, valid={first_pass.get('valid', 'N/A')}, satisfy={first_pass.get('satisfy', 'N/A')}")
        total_duration = time.time() - start_time
        logger.info(f"Total execution time before timeout: {total_duration:.2f} seconds")
        stats = get_token_stats()
        logger.info(f"Total API calls: {stats['call_count']}, Total tokens: {stats['total_tokens']:,}")
        sys.exit(1)

    signal.signal(signal.SIGTERM, _sigterm_handler)

    logger.info(f"开始为 {args.file_name} 生成循环不变量...")
    annotated_code = generator.generate_all(max_iterations=args.max_iterations)

    if args.mask_mode and mask_ctx is not None and annotated_code:
        annotated_code = _restore_assertions(annotated_code, mask_ctx["placeholders"])
        if generator.invariants:
            generator.invariants[-1]['code'] = annotated_code

        os.makedirs(resolved_output_dir, exist_ok=True)
        verify_fd, verify_path = tempfile.mkstemp(
            prefix=f"{args.file_name}_mask_verify_",
            suffix=".c",
            dir=resolved_output_dir,
        )
        os.close(verify_fd)
        try:
            with open(verify_path, "w", encoding="utf-8") as f:
                f.write(annotated_code)

            verifier = OutputVerifier(logger=logger, output=True)
            verifier.run(verify_path)
            syntax_ok = getattr(verifier, "syntax_correct", False)
            valid_ok = bool(verifier.validate_result) and all(verifier.validate_result)
            has_assert = re.search(r"/\*@\s*assert\b|//@\s*assert\b", annotated_code) is not None
            satisfy_ok = (all(verifier.verify_result) if verifier.verify_result else False) or (not has_assert)
            logger.info(
                f"Mask mode final verification: syntax={syntax_ok}, valid={valid_ok}, satisfy={satisfy_ok}, has_assert={has_assert}"
            )

            # Update first_pass satisfy with post-restore verification result
            if hasattr(generator, 'first_pass') and generator.first_pass is not None:
                fp = generator.first_pass
                if satisfy_ok and fp.get('satisfy') is None:
                    fp['satisfy'] = fp.get('valid') or fp.get('syntax') or 1
                elif not satisfy_ok and fp.get('satisfy') is not None:
                    fp['satisfy'] = None
        finally:
            if os.path.exists(verify_path):
                os.remove(verify_path)
    
    # 记录结束时间
    end_time = time.time()
    total_duration = end_time - start_time
    
    # 获取并输出 token 统计信息
    token_stats = get_token_stats()
    logger.info("=" * 60)
    logger.info("Token 使用统计:")
    logger.info(f"  总调用次数: {token_stats['call_count']}")
    logger.info(f"  Prompt Tokens: {token_stats['total_prompt_tokens']:,}")
    logger.info(f"  Completion Tokens: {token_stats['total_completion_tokens']:,}")
    logger.info(f"  总 Tokens: {token_stats['total_tokens']:,}")
    if token_stats['call_count'] > 0:
        avg_prompt = token_stats['total_prompt_tokens'] / token_stats['call_count']
        avg_completion = token_stats['total_completion_tokens'] / token_stats['call_count']
        avg_total = token_stats['total_tokens'] / token_stats['call_count']
        logger.info(f"  平均每次调用:")
        logger.info(f"    Prompt: {avg_prompt:.1f} tokens")
        logger.info(f"    Completion: {avg_completion:.1f} tokens")
        logger.info(f"    总计: {avg_total:.1f} tokens")
    logger.info("=" * 60)
    
    # Always save results, even if generation failed
    generator.save_results(resolved_output_dir)
    
    if annotated_code:
        logger.info(f"完成！已生成包含不变量的完整 C 代码")
    else:
        logger.error("生成失败：无法生成循环不变量，已保存原始输入文件")
    
    # 记录 first_pass 指标
    first_pass = generator.first_pass if hasattr(generator, 'first_pass') and generator.first_pass else None
    if first_pass:
        logger.info("="*50)
        logger.info("first_pass:")
        logger.info(f"syntax={first_pass.get('syntax', 'N/A')}, valid={first_pass.get('valid', 'N/A')}, satisfy={first_pass.get('satisfy', 'N/A')}")
        logger.info("="*50)
    
    # 记录执行时间统计
    logger.info("="*50)
    logger.info("⏰ OVERALL EXECUTION TIME STATISTICS")
    logger.info(f"Total execution time: {total_duration:.2f} seconds ({total_duration/60:.2f} minutes)")
    logger.info("="*50)
    
    # 记录 token 使用统计
    stats = get_token_stats()
    logger.info("="*50)
    logger.info("📊 TOKEN USAGE STATISTICS")
    logger.info(f"Total API calls: {stats['call_count']}")
    logger.info(f"Total prompt tokens (input): {stats['total_prompt_tokens']:,}")
    logger.info(f"Total completion tokens (output): {stats['total_completion_tokens']:,}")
    logger.info(f"Total tokens: {stats['total_tokens']:,}")
    if stats['call_count'] > 0:
        avg_prompt = stats['total_prompt_tokens'] / stats['call_count']
        avg_completion = stats['total_completion_tokens'] / stats['call_count']
        avg_total = stats['total_tokens'] / stats['call_count']
        logger.info(f"Average prompt tokens per call: {avg_prompt:.1f}")
        logger.info(f"Average completion tokens per call: {avg_completion:.1f}")
        logger.info(f"Average total tokens per call: {avg_total:.1f}")
    logger.info("="*50)

    if args.mask_mode and mask_ctx is not None:
        shutil.rmtree(mask_ctx["mask_dir"], ignore_errors=True)

if __name__ == "__main__":
    main()
