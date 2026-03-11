#!/usr/bin/env python3
import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


def main() -> None:
    ap = argparse.ArgumentParser(description='Batch verify curated loop files with OutputVerifier')
    ap.add_argument('--dir', required=True, help='Directory containing .c files')
    ap.add_argument('--src', required=True, help='Path to SAM2INV/src')
    ap.add_argument('--workers', type=int, default=4, help='Parallel workers')
    ap.add_argument(
        '--timeout-sec',
        type=int,
        default=0,
        help='Outer per-file timeout in seconds; 0 means disable outer timeout',
    )
    ap.add_argument('--out-json', default='verify_curated_batch.json', help='Output JSON path')
    args = ap.parse_args()

    sys.path.insert(0, str(Path('/home/yangfp/SAM2INV/.codex/skills/loop-curation-verify/scripts')))
    import verify_curated_loops as vcl  # noqa: E402

    src = Path(args.src)
    root = Path(args.dir)
    files = sorted(root.glob('*.c'))

    outer_timeout = args.timeout_sec if args.timeout_sec > 0 else 1000
    print(
        f'START total={len(files)} workers={args.workers} timeout={args.timeout_sec}(outer)',
        flush=True,
    )

    def task(fp: Path):
        return fp.name, vcl.run_one(src, fp, timeout_sec=outer_timeout)

    results = []
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(task, fp) for fp in files]
        done = 0
        for fut in as_completed(futs):
            name, res = fut.result()
            done += 1
            results.append((name, res))
            status = res.get('status')
            if status != 'OK':
                print(f'{name}\tstatus={status}', flush=True)
            else:
                print(
                    f"{name}\tpassed={res.get('passed')}\t"
                    f"validate_ok={res.get('validate_ok')}\tverify_ok={res.get('verify_ok')}",
                    flush=True,
                )
            if done % 20 == 0:
                print(f'PROGRESS {done}/{len(files)}', flush=True)

    results.sort(key=lambda x: x[0])
    out = {k: v for k, v in results}
    Path(args.out_json).write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding='utf-8')

    ok = [(n, r) for n, r in results if r.get('status') == 'OK']
    passed = [(n, r) for n, r in ok if r.get('passed')]
    failed = [(n, r) for n, r in ok if not r.get('passed')]
    timeout = [(n, r) for n, r in results if r.get('status') == 'TIMEOUT']
    nonok_other = [(n, r) for n, r in results if r.get('status') not in ('OK', 'TIMEOUT')]

    print(
        f"SUMMARY total={len(files)} ok={len(ok)} passed={len(passed)} "
        f"failed={len(failed)} timeout={len(timeout)} other_nonok={len(nonok_other)}"
    )
    print(f'WROTE {args.out_json}')


if __name__ == '__main__':
    main()
