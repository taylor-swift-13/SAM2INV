#!/usr/bin/env python3
import argparse
import re
from pathlib import Path


def dedup_file(path: Path) -> int:
    lines = path.read_text(encoding='utf-8').splitlines(keepends=True)
    out = []
    in_acsl = False
    collecting = False
    buf = []
    seen = set()
    removed = 0

    def flush_inv(block):
        nonlocal removed
        first = block[0]
        idx = first.find('loop invariant')
        expr_text = first[idx + len('loop invariant'):] + ''.join(block[1:])
        semi = expr_text.find(';')
        expr = expr_text[:semi] if semi >= 0 else expr_text
        key = re.sub(r'\s+', '', expr)
        if key in seen:
            removed += 1
            return []
        seen.add(key)
        return block

    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()

        if collecting:
            buf.append(line)
            if ';' in line:
                out.extend(flush_inv(buf))
                buf = []
                collecting = False
            i += 1
            continue

        if '/*@' in line:
            in_acsl = True
            out.append(line)
            i += 1
            continue

        if in_acsl and '*/' in line:
            in_acsl = False
            out.append(line)
            i += 1
            continue

        if in_acsl and stripped.startswith('loop invariant'):
            collecting = True
            buf = [line]
            if ';' in line:
                out.extend(flush_inv(buf))
                buf = []
                collecting = False
            i += 1
            continue

        out.append(line)
        i += 1

    path.write_text(''.join(out), encoding='utf-8')
    return removed


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--dir', required=True, help='Directory containing curated .c files')
    args = ap.parse_args()

    root = Path(args.dir)
    total_removed = 0
    for fp in sorted(root.glob('*.c')):
        removed = dedup_file(fp)
        total_removed += removed
        if removed:
            print(f'{fp.name}: removed {removed}')
    print(f'total_removed={total_removed}')


if __name__ == '__main__':
    main()
