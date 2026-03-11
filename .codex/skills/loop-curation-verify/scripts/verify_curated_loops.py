#!/usr/bin/env python3
import argparse
import ast
import subprocess
import sys
from pathlib import Path


def parse_list(line: str):
    try:
        return ast.literal_eval(line.strip())
    except Exception:
        return None


def run_one(src_dir: Path, c_file: Path, timeout_sec: int):
    py = (
        "import sys; "
        f"sys.path.insert(0, {str(src_dir)!r}); "
        "from output_verify import OutputVerifier; "
        f"v=OutputVerifier(output=False); v.run({str(c_file)!r}); "
        "print('VALIDATE', v.validate_result); "
        "print('VERIFY', v.verify_result)"
    )
    try:
        proc = subprocess.run(
            [sys.executable, '-c', py],
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return {'status': 'TIMEOUT'}

    validate = None
    verify = None
    for ln in (proc.stdout or '').splitlines():
        if ln.startswith('VALIDATE '):
            validate = parse_list(ln[len('VALIDATE '):])
        if ln.startswith('VERIFY '):
            verify = parse_list(ln[len('VERIFY '):])

    if validate is None or verify is None:
        return {'status': 'PARSE_FAIL', 'stdout': proc.stdout, 'stderr': proc.stderr}

    validate_ok = all(validate) if validate else True
    verify_ok = (len(verify) == 0) or all(verify)
    passed = validate_ok and verify_ok
    return {
        'status': 'OK',
        'validate': validate,
        'verify': verify,
        'validate_ok': validate_ok,
        'verify_ok': verify_ok,
        'passed': passed,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--dir', required=True, help='Directory containing curated .c files')
    ap.add_argument('--src', required=True, help='Path to SAM2INV/src (contains output_verify.py)')
    ap.add_argument('--timeout-sec', type=int, default=90)
    args = ap.parse_args()

    root = Path(args.dir)
    src = Path(args.src)

    passed = 0
    total = 0
    for fp in sorted(root.glob('*.c')):
        total += 1
        res = run_one(src, fp, args.timeout_sec)
        if res['status'] != 'OK':
            print(f"{fp.name}\t{res['status']}")
            continue
        if res['passed']:
            passed += 1
        print(
            f"{fp.name}\tpassed={res['passed']}\t"
            f"validate_ok={res['validate_ok']}\tverify_ok={res['verify_ok']}\t"
            f"validate={res['validate']}\tverify={res['verify']}"
        )

    print(f'summary: passed={passed}/{total}')


if __name__ == '__main__':
    main()
