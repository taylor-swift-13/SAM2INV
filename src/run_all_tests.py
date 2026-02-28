"""
并行运行测试集中所有测试用例

每个文件直接调用 loop_inv.py（内部已包含生成+验证），
运行结束后调用 analyze_logs.py 对日志文件夹进行统计。

使用方法:
    python3 run_all_tests.py NLA_lipus
    python3 run_all_tests.py NLA_lipus --workers 4 --max-iterations 3
    python3 run_all_tests.py NLA_lipus --files 1 2 3
"""
import argparse
import os
import sys
import time
import subprocess
from concurrent.futures import ProcessPoolExecutor, as_completed
from config import MAX_ITERATION
from run_dirs import resolve_run_dirs

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TIMEOUT_SECONDS = 1200


def run_single_test(file_name: str, input_subdir: str, output_dir: str,
                    log_dir: str, max_iterations: int) -> dict:
    """运行单个测试用例（在子进程中调用 loop_inv.py）"""
    start_time = time.time()
    result = {
        'file': file_name,
        'success': False,
        'duration': 0,
        'error': None,
    }

    cmd = [
        sys.executable, os.path.join(SCRIPT_DIR, 'loop_inv.py'),
        file_name,
        '--input-subdir', input_subdir,
        '--output-dir', output_dir,
        '--log-dir', log_dir,
        '--max-iterations', str(max_iterations),
    ]

    try:
        proc = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, cwd=SCRIPT_DIR
        )
        try:
            stdout, stderr = proc.communicate(timeout=TIMEOUT_SECONDS)
            result['success'] = (proc.returncode == 0)
            if proc.returncode != 0:
                result['error'] = stderr[-500:] if stderr else 'Unknown error'
        except subprocess.TimeoutExpired:
            proc.terminate()
            try:
                proc.communicate(timeout=15)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.communicate()
            result['error'] = f'Timeout ({TIMEOUT_SECONDS}s)'
    except Exception as e:
        result['error'] = str(e)

    result['duration'] = time.time() - start_time
    return result


def main():
    parser = argparse.ArgumentParser(
        description="并行运行测试集，完成后统计日志结果",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python3 run_all_tests.py NLA_lipus
  python3 run_all_tests.py NLA_lipus --workers 20
  python3 run_all_tests.py NLA_lipus --files 1 2 3
        """,
    )
    parser.add_argument('test_set', type=str, help="测试集目录名 (e.g., NLA_lipus, linear)")
    parser.add_argument('--workers', type=int, default=20, help="并行worker数量 (default: 20)")
    parser.add_argument(
        '--max-iterations', type=int, default=MAX_ITERATION,
        help=f"最大迭代修复次数 (default: {MAX_ITERATION})",
    )
    parser.add_argument('--output-dir', type=str, default=None, help="输出目录 (default: output/<test_set>)")
    parser.add_argument('--log-dir', type=str, default=None, help="日志目录 (default: log/<test_set>_<timestamp>)")
    parser.add_argument('--files', type=str, nargs='+', default=None, help="指定要运行的文件名列表 (不含.c扩展名)")

    args = parser.parse_args()

    # 构建输入目录路径
    input_path = os.path.join(SCRIPT_DIR, 'input', args.test_set)
    if not os.path.exists(input_path):
        print(f"Error: Input directory not found: {input_path}")
        sys.exit(1)

    # 查找所有 .c 文件
    all_c_files = sorted(
        [f[:-2] for f in os.listdir(input_path) if f.endswith('.c')],
        key=lambda x: int(x) if x.isdigit() else x,
    )

    if args.files:
        test_files = [f for f in args.files if f in all_c_files]
        missing = [f for f in args.files if f not in all_c_files]
        if missing:
            print(f"Warning: Files not found in {args.test_set}: {', '.join(missing)}")
    else:
        test_files = all_c_files

    if not test_files:
        print(f"Error: No test files found in {input_path}")
        sys.exit(1)

    # 统一输出/日志目录策略：output/<test_set>_<timestamp>, log/<test_set>_<timestamp>
    output_dir, log_dir, resolved_test_set, run_tag = resolve_run_dirs(
        test_set=args.test_set,
        output_dir=args.output_dir,
        log_dir=args.log_dir,
    )
    os.environ["SAM2INV_OUTPUT_DIR"] = output_dir
    os.environ["SAM2INV_LOG_DIR"] = log_dir
    os.environ["SAM2INV_TEST_SET"] = resolved_test_set
    os.environ["SAM2INV_RUN_TAG"] = run_tag

    os.makedirs(os.path.join(SCRIPT_DIR, output_dir), exist_ok=True)
    os.makedirs(os.path.join(SCRIPT_DIR, log_dir), exist_ok=True)

    print(f"{'='*60}")
    print(f"SAM2INV Test Runner")
    print(f"{'='*60}")
    print(f"Test set:         {args.test_set}")
    print(f"Test files:       {len(test_files)}")
    print(f"Workers:          {args.workers}")
    print(f"Max iterations:   {args.max_iterations}")
    print(f"Timeout:          {TIMEOUT_SECONDS}s")
    print(f"Output dir:       {output_dir}")
    print(f"Log dir:          {log_dir}")
    print(f"{'='*60}\n")

    total_start = time.time()

    # 并行运行所有测试
    print(f"Running {len(test_files)} files with {args.workers} workers...")
    results = []

    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(
                run_single_test, f, args.test_set, output_dir, log_dir, args.max_iterations
            ): f
            for f in test_files
        }

        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            status = 'OK' if result['success'] else 'FAIL'
            err = f"  ({result['error'][:40]})" if result['error'] else ''
            print(f"  [{status}] {result['file']}.c ({result['duration']:.1f}s){err}")

    # 按文件名排序
    results.sort(key=lambda x: int(x['file']) if x['file'].isdigit() else x['file'])

    total_time = time.time() - total_start
    succeeded = sum(1 for r in results if r['success'])
    print(f"\nAll runs finished: {succeeded}/{len(results)} succeeded, total {total_time:.1f}s\n")

    # 调用 analyze_logs.py 统计日志
    print(f"{'='*60}")
    print(f"Analyzing logs in {log_dir} ...")
    print(f"{'='*60}\n")

    subprocess.run(
        [sys.executable, os.path.join(SCRIPT_DIR, 'analyze_logs.py'), os.path.join(SCRIPT_DIR, log_dir)],
        cwd=SCRIPT_DIR,
    )


if __name__ == '__main__':
    main()
