"""
批量处理 input/{AA} 目录中的所有 C 文件
"""
import argparse
import os
import sys
import time
import logging
from pathlib import Path
from loop_inv import setup_logger
from inv_generator import InvariantGenerator
from llm import LLMConfig, reset_token_stats, get_token_stats
from config import SUBDIR, MAX_ITERATION
from run_dirs import resolve_run_dirs

def batch_process(input_dir: str, output_dir: str = None, log_dir: str = None,
                  max_iterations: int = MAX_ITERATION, skip_existing: bool = False):
    """
    批量处理指定目录下的所有 C 文件
    
    Args:
        input_dir: 输入目录路径（如 'input/linear'）
        output_dir: 输出目录
        log_dir: 日志目录（默认自动对齐 input 路径）
        max_iterations: 最大迭代修复次数
        skip_existing: 是否跳过已存在的输出文件
    """
    # 获取绝对路径和子目录配置
    script_dir = os.path.dirname(os.path.abspath(__file__))
    input_path = os.path.join(script_dir, input_dir)
    input_subdir = os.path.basename(os.path.normpath(input_dir))
    resolved_output_dir, resolved_log_dir, resolved_test_set, run_tag = resolve_run_dirs(
        test_set=input_subdir,
        output_dir=output_dir,
        log_dir=log_dir,
    )
    os.environ["SAM2INV_OUTPUT_DIR"] = resolved_output_dir
    os.environ["SAM2INV_LOG_DIR"] = resolved_log_dir
    os.environ["SAM2INV_TEST_SET"] = resolved_test_set
    os.environ["SAM2INV_RUN_TAG"] = run_tag
    
    if not os.path.exists(input_path):
        print(f"错误: 输入目录不存在: {input_path}")
        return
    
    # 确保输出相关目录存在
    os.makedirs(resolved_output_dir, exist_ok=True)
    os.makedirs(resolved_log_dir, exist_ok=True)
    
    # 查找所有 .c 文件
    c_files = sorted([f for f in os.listdir(input_path) if f.endswith('.c')])
    
    if not c_files:
        print(f"警告: 在 {input_path} 中没有找到 .c 文件")
        return
    
    print(f"找到 {len(c_files)} 个 C 文件")
    print(f"输入目录: {input_path}")
    print(f"输出目录: {resolved_output_dir}")
    print("="*60)
    
    # 统计信息
    total_start_time = time.time()
    success_count = 0
    fail_count = 0
    skip_count = 0
    
    # 创建汇总日志
    summary_logger = logging.getLogger('BATCH_SUMMARY')
    summary_logger.setLevel(logging.INFO)
    summary_handler = logging.StreamHandler()
    summary_handler.setFormatter(logging.Formatter('%(message)s'))
    summary_logger.addHandler(summary_handler)
    
    # 处理每个文件
    for idx, c_file in enumerate(c_files, 1):
        file_name = c_file[:-2]  # 移除 .c 扩展名
        
        print(f"\n[{idx}/{len(c_files)}] 处理文件: {c_file}")
        print("-"*60)
        
        # 检查是否跳过已存在的文件
        if skip_existing:
            output_file = os.path.join(resolved_output_dir, c_file)
            if os.path.exists(output_file):
                print(f"跳过已存在的文件: {output_file}")
                skip_count += 1
                continue
        # 如果日志已存在则跳过
        log_file = os.path.join(resolved_log_dir, f"{file_name}.log")
        if os.path.exists(log_file):
            print(f"跳过已有日志的文件: {log_file}")
            skip_count += 1
            continue
        
        # 重置 token 统计（每个文件独立统计）
        reset_token_stats()
        
        # 设置日志记录器
        logger = setup_logger(file_name, log_dir=resolved_log_dir)
        
        # 记录开始时间
        start_time = time.time()
        
        try:
            # 创建不变量生成器
            generator = InvariantGenerator(
                file_name,
                LLMConfig(),
                logger,
                output_dir=resolved_output_dir,
                input_subdir=input_subdir,
            )
            
            # 设置最大迭代次数
            generator.repairer.max_iterations = max_iterations
            
            # 生成所有不变量
            logger.info(f"开始为 {file_name} 生成循环不变量...")
            annotated_code = generator.generate_all()
            
            # 记录结束时间
            end_time = time.time()
            duration = end_time - start_time
            
            if annotated_code:
                # 保存结果
                generator.save_results(resolved_output_dir)
                logger.info(f"完成！已生成包含不变量的完整 C 代码")
                success_count += 1
                print(f"✓ 成功 ({duration:.2f}秒)")
            else:
                logger.error("生成失败：无法生成循环不变量")
                fail_count += 1
                print(f"✗ 失败 ({duration:.2f}秒)")
            
            # 记录 first_pass 指标
            first_pass = generator.first_pass if hasattr(generator, 'first_pass') and generator.first_pass else None
            if first_pass:
                logger.info("="*50)
                logger.info("first_pass:")
                logger.info(f"syntax={first_pass.get('syntax', 'N/A')}, valid={first_pass.get('valid', 'N/A')}, satisfy={first_pass.get('satisfy', 'N/A')}")
                logger.info("="*50)
            
            # 记录执行时间统计
            logger.info("="*50)
            logger.info("⏰ EXECUTION TIME STATISTICS")
            logger.info(f"Total execution time: {duration:.2f} seconds ({duration/60:.2f} minutes)")
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
            
        except Exception as e:
            fail_count += 1
            end_time = time.time()
            duration = end_time - start_time
            print(f"✗ 处理失败: {e} ({duration:.2f}秒)")
            logger.error(f"处理文件 {c_file} 时发生错误: {e}", exc_info=True)
    
    # 打印汇总统计
    total_end_time = time.time()
    total_duration = total_end_time - total_start_time
    
    print("\n" + "="*60)
    print("批量处理完成！")
    print("="*60)
    print(f"总文件数: {len(c_files)}")
    print(f"成功: {success_count}")
    print(f"失败: {fail_count}")
    print(f"跳过: {skip_count}")
    print(f"总耗时: {total_duration:.2f} 秒 ({total_duration/60:.2f} 分钟)")
    if success_count > 0:
        print(f"平均每个文件耗时: {total_duration/success_count:.2f} 秒")
    print("="*60)

def main():
    parser = argparse.ArgumentParser(description="批量处理 input/{input_dir} 目录中的所有 C 文件")
    parser.add_argument('input_dir', type=str, nargs='?', default=SUBDIR, help="输入目录（默认使用配置的 subdir）")
    parser.add_argument('--output-dir', type=str, default=None, help="输出目录（默认按配置自动生成）")
    parser.add_argument('--log-dir', type=str, default=None, help="日志目录（默认自动对齐 input 路径）")
    parser.add_argument('--max-iterations', type=int, default=MAX_ITERATION, help="最大迭代修复次数")
    parser.add_argument('--skip-existing', action='store_true', help="跳过已存在的输出文件")
    
    args = parser.parse_args()
    
    # 构建完整的输入目录路径
    input_dir = f"input/{args.input_dir}"
    
    batch_process(
        input_dir=input_dir,
        output_dir=args.output_dir,
        log_dir=args.log_dir,
        max_iterations=args.max_iterations,
        skip_existing=args.skip_existing
    )

if __name__ == "__main__":
    main()
