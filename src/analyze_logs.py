"""
分析日志文件夹，统计正确率、平均时间和 token 消耗

使用方法:
    python3 analyze_logs.py log/NLA_lipus
    python3 analyze_logs.py /home/yangfp/SAM2INV/src/log/NLA_lipus
"""
import argparse
import os
import re
import sys


def parse_log_file(log_path: str) -> dict:
    """
    解析单个 .log 文件，提取 first_pass 结果、执行时间和 token 统计

    Returns:
        dict with keys: file, syntax, valid, satisfy, duration,
                        total_tokens, prompt_tokens, completion_tokens, api_calls
    """
    file_name = os.path.splitext(os.path.basename(log_path))[0]
    result = {
        'file': file_name,
        'syntax': None,
        'valid': None,
        'satisfy': None,
        'duration': None,
        'total_tokens': None,
        'prompt_tokens': None,
        'completion_tokens': None,
        'api_calls': None,
    }

    try:
        with open(log_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception:
        return result

    # 从后往前扫描，因为关键信息在日志末尾
    found_first_pass = False
    found_time = False
    found_tokens = False

    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()
        # 去掉日志前缀 "2026-02-09 15:13:55,257 - INFO - "
        content = re.sub(r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2},\d+ - \w+ - ', '', line)

        # 解析 first_pass 结果
        # 格式: syntax=1, valid=1, satisfy=1  或  syntax=None, valid=None, satisfy=None
        if not found_first_pass:
            m = re.match(r'syntax=(\S+),\s*valid=(\S+),\s*satisfy=(\S+)', content)
            if m:
                # 检查上一行是否是 "first_pass:"
                if i > 0:
                    prev = re.sub(r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2},\d+ - \w+ - ', '', lines[i-1].strip())
                    if 'first_pass' in prev:
                        result['syntax'] = _parse_bool(m.group(1))
                        result['valid'] = _parse_bool(m.group(2))
                        result['satisfy'] = _parse_bool(m.group(3))
                        found_first_pass = True

        # 解析执行时间
        # 格式: Total execution time: 22.53 seconds (0.38 minutes)
        if not found_time:
            m = re.search(r'Total execution time:\s*([\d.]+)\s*seconds', content)
            if m:
                result['duration'] = float(m.group(1))
                found_time = True

        # 解析 TOKEN USAGE STATISTICS 块（最后一个）
        if not found_tokens:
            # Total tokens: 70,943
            m = re.search(r'Total tokens:\s*([\d,]+)', content)
            if m:
                result['total_tokens'] = int(m.group(1).replace(',', ''))

            m = re.search(r'Total prompt tokens \(input\):\s*([\d,]+)', content)
            if m:
                result['prompt_tokens'] = int(m.group(1).replace(',', ''))

            m = re.search(r'Total completion tokens \(output\):\s*([\d,]+)', content)
            if m:
                result['completion_tokens'] = int(m.group(1).replace(',', ''))

            m = re.search(r'Total API calls:\s*(\d+)', content)
            if m:
                result['api_calls'] = int(m.group(1))

            if all(result[k] is not None for k in ['total_tokens', 'prompt_tokens', 'completion_tokens', 'api_calls']):
                found_tokens = True

        if found_first_pass and found_time and found_tokens:
            break

    # Fallback: if no first_pass found (e.g., process timed out), find the best
    # result across all strengthen iterations (prefer syntax+valid+satisfy, then syntax+valid)
    if not found_first_pass:
        best_syntax = False
        best_valid = False
        best_satisfy = False
        for i in range(len(lines)):
            line = lines[i].strip()
            content = re.sub(r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2},\d+ - \w+ - ', '', line)
            m = re.search(r'\[strengthen \d+/\d+\]\s*syntax=(\w+),\s*valid=(\w+),\s*satisfy=(\w+)', content)
            if m:
                s, v, sat = _parse_bool(m.group(1)), _parse_bool(m.group(2)), _parse_bool(m.group(3))
                if s:
                    best_syntax = True
                if s and v:
                    best_valid = True
                if s and v and sat:
                    best_satisfy = True
        if best_syntax or best_valid or best_satisfy:
            result['syntax'] = best_syntax
            result['valid'] = best_valid
            result['satisfy'] = best_satisfy

    return result


def _parse_bool(val: str):
    """将日志中的值转为 bool: 1/True -> True, None/0/False -> False"""
    if val in ('1', 'True', 'true'):
        return True
    return False


def analyze_log_dir(log_dir: str):
    """分析整个日志文件夹并打印统计结果"""
    if not os.path.isdir(log_dir):
        print(f"Error: Directory not found: {log_dir}")
        sys.exit(1)

    # 收集所有 .log 文件
    log_files = sorted(
        [f for f in os.listdir(log_dir) if f.endswith('.log')],
        key=lambda x: int(x[:-4]) if x[:-4].isdigit() else x[:-4],
    )

    if not log_files:
        print(f"Error: No .log files found in {log_dir}")
        sys.exit(1)

    # 解析每个日志文件
    results = []
    for lf in log_files:
        r = parse_log_file(os.path.join(log_dir, lf))
        results.append(r)

    total = len(results)

    # ===== 打印详细表格 =====
    header = f"{'File':>6} | {'Syntax':>6} | {'Valid':>5} | {'Satisfy':>7} | {'Time(s)':>8} | {'Tokens':>8} | {'API Calls':>9}"
    sep = "-" * len(header)
    print(sep)
    print(header)
    print(sep)

    for r in results:
        syn = 'Pass' if r['syntax'] else ('Fail' if r['syntax'] is False else '-')
        val = 'Pass' if r['valid'] else ('Fail' if r['valid'] is False else '-')
        sat = 'Pass' if r['satisfy'] else ('Fail' if r['satisfy'] is False else '-')
        t = f"{r['duration']:.1f}" if r['duration'] is not None else '-'
        tok = f"{r['total_tokens']:,}" if r['total_tokens'] is not None else '-'
        calls = str(r['api_calls']) if r['api_calls'] is not None else '-'
        print(f"{r['file']:>6} | {syn:>6} | {val:>5} | {sat:>7} | {t:>8} | {tok:>8} | {calls:>9}")

    print(sep)

    # ===== 统计汇总 =====
    syntax_pass = sum(1 for r in results if r['syntax'])
    valid_pass = sum(1 for r in results if r['valid'])
    satisfy_pass = sum(1 for r in results if r['satisfy'])

    durations = [r['duration'] for r in results if r['duration'] is not None]
    tokens_list = [r['total_tokens'] for r in results if r['total_tokens'] is not None]
    prompt_list = [r['prompt_tokens'] for r in results if r['prompt_tokens'] is not None]
    completion_list = [r['completion_tokens'] for r in results if r['completion_tokens'] is not None]
    calls_list = [r['api_calls'] for r in results if r['api_calls'] is not None]

    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    print(f"Total test cases:        {total}")
    print(f"Syntax correct:          {syntax_pass}/{total} ({syntax_pass/total*100:.1f}%)")
    print(f"Invariants valid:        {valid_pass}/{total} ({valid_pass/total*100:.1f}%)")
    print(f"Assertions satisfied:    {satisfy_pass}/{total} ({satisfy_pass/total*100:.1f}%)")
    print()
    print(f">>> Accuracy (satisfy):  {satisfy_pass}/{total} = {satisfy_pass/total*100:.1f}% <<<")
    print()

    # 时间统计
    if durations:
        avg_time = sum(durations) / len(durations)
        total_time = sum(durations)
        print(f"Time statistics ({len(durations)} files with data):")
        print(f"  Total time:            {total_time:.1f}s ({total_time/60:.1f}min)")
        print(f"  Average time:          {avg_time:.1f}s")
        print(f"  Min time:              {min(durations):.1f}s")
        print(f"  Max time:              {max(durations):.1f}s")
    else:
        print("Time statistics:         No data")
    print()

    # Token 统计
    if tokens_list:
        print(f"Token statistics ({len(tokens_list)} files with data):")
        print(f"  Total tokens:          {sum(tokens_list):,}")
        print(f"  Avg tokens per file:   {sum(tokens_list)/len(tokens_list):,.0f}")
        print(f"  Total prompt tokens:   {sum(prompt_list):,}")
        print(f"  Total compl. tokens:   {sum(completion_list):,}")
        if calls_list:
            print(f"  Total API calls:       {sum(calls_list)}")
            print(f"  Avg API calls/file:    {sum(calls_list)/len(calls_list):.1f}")
    else:
        print("Token statistics:        No data")

    print(f"{'='*60}")

    # 列出通过和失败的文件
    passed = sorted(
        [r['file'] for r in results if r['satisfy']],
        key=lambda x: int(x) if x.isdigit() else x,
    )
    failed = sorted(
        [r['file'] for r in results if not r['satisfy']],
        key=lambda x: int(x) if x.isdigit() else x,
    )

    if passed:
        print(f"\nPassed ({len(passed)}): {', '.join(passed)}")
    if failed:
        print(f"Failed ({len(failed)}): {', '.join(failed)}")


def main():
    parser = argparse.ArgumentParser(
        description="分析日志文件夹，统计正确率、平均时间和 token 消耗",
    )
    parser.add_argument('log_dir', type=str, help="日志文件夹路径 (e.g., log/NLA_lipus)")
    args = parser.parse_args()

    analyze_log_dir(args.log_dir)


if __name__ == '__main__':
    main()
