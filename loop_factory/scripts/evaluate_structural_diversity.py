#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from batch_pipeline import compute_loop_skeleton_key, normalize_code


DEFAULT_DATASETS = {
    "linear": Path("/home/yangfp/SAM2INV/src/input/linear"),
    "NLA_lipus": Path("/home/yangfp/SAM2INV/src/input/NLA_lipus"),
    "question": Path("/home/yangfp/SAM2INV/src/input/question"),
    "annotated": Path("/home/yangfp/SAM2INV/loop_factory/generated/test/annotated"),
}


@dataclass(frozen=True)
class DatasetScore:
    name: str
    files: int
    control_unique: int
    skeleton_unique: int
    control_entropy: float
    skeleton_entropy: float
    control_score: float
    skeleton_score: float
    total_score: float


def _iter_c_files(root: Path) -> List[Path]:
    if root.is_file():
        return [root]
    return sorted(p for p in root.rglob("*.c") if p.is_file())


def _strip_comments(code: str) -> str:
    code = re.sub(r"/\*.*?\*/", "", code, flags=re.DOTALL)
    code = re.sub(r"//.*?$", "", code, flags=re.MULTILINE)
    return code


def _count_regex(pattern: str, text: str) -> int:
    return len(re.findall(pattern, text, flags=re.MULTILINE))


def _max_if_chain(text: str) -> int:
    best = 0
    for m in re.finditer(r"\bif\s*\(", text):
        tail = text[m.start() :]
        count = 1
        pos = 0
        while True:
            nxt = re.search(r"\belse\s+if\s*\(", tail[pos:])
            if not nxt:
                break
            count += 1
            pos += nxt.end()
        best = max(best, count)
    return best


def _max_loop_nesting(text: str) -> int:
    token_pat = re.compile(r"\bwhile\s*\(|\bfor\s*\(|\{|}")
    pending_loops = 0
    loop_depth = 0
    max_depth = 0
    stack: List[str] = []
    for tok in token_pat.finditer(text):
        s = tok.group(0)
        if s.startswith("while") or s.startswith("for"):
            pending_loops += 1
        elif s == "{":
            if pending_loops > 0:
                stack.append("loop")
                loop_depth += 1
                max_depth = max(max_depth, loop_depth)
                pending_loops -= 1
            else:
                stack.append("block")
        else:
            if stack:
                top = stack.pop()
                if top == "loop":
                    loop_depth = max(0, loop_depth - 1)
    return max_depth


def _control_signature(code: str) -> str:
    text = _strip_comments(code)
    text = re.sub(r"\s+", " ", text)
    feats = {
        "while": _count_regex(r"\bwhile\s*\(", text),
        "for": _count_regex(r"\bfor\s*\(", text),
        "while1": _count_regex(r"\bwhile\s*\(\s*1\s*\)", text),
        "break": _count_regex(r"\bbreak\s*;", text),
        "if": _count_regex(r"\bif\s*\(", text),
        "elseif": _count_regex(r"\belse\s+if\s*\(", text),
        "else": _count_regex(r"\belse\b", text),
        "max_if_chain": _max_if_chain(text),
        "loop_nesting": _max_loop_nesting(text),
        "mod_guard": _count_regex(r"%\s*\d+\s*==\s*0|%\s*\d+\s*[!<>=]", text),
        "has_return": int(bool(re.search(r"\breturn\b", text))),
    }
    return "|".join(f"{k}={v}" for k, v in feats.items())


def _entropy(counter: Counter[str]) -> float:
    total = sum(counter.values())
    if total <= 1:
        return 0.0
    ent = 0.0
    for count in counter.values():
        p = count / total
        ent -= p * math.log(p, 2)
    return ent


def _norm_entropy(counter: Counter[str]) -> float:
    total = sum(counter.values())
    if total <= 1:
        return 0.0
    support = max(2, min(total, len(counter)))
    return _entropy(counter) / math.log(support, 2)


def _score_counter(counter: Counter[str], total: int) -> float:
    if total <= 0:
        return 0.0
    uniq_ratio = len(counter) / total
    ent_score = _norm_entropy(counter)
    return 0.5 * uniq_ratio + 0.5 * ent_score


def _evaluate_files(name: str, files: Sequence[Path]) -> DatasetScore:
    control_counter: Counter[str] = Counter()
    skeleton_counter: Counter[str] = Counter()
    for path in files:
        code = path.read_text(encoding="utf-8", errors="ignore")
        norm = normalize_code(code)
        if not norm:
            continue
        control_counter[_control_signature(code)] += 1
        skeleton_counter[compute_loop_skeleton_key(code)] += 1

    total = sum(control_counter.values())
    control_score = _score_counter(control_counter, total)
    skeleton_score = _score_counter(skeleton_counter, total)
    total_score = 0.5 * control_score + 0.5 * skeleton_score
    return DatasetScore(
        name=name,
        files=total,
        control_unique=len(control_counter),
        skeleton_unique=len(skeleton_counter),
        control_entropy=_entropy(control_counter),
        skeleton_entropy=_entropy(skeleton_counter),
        control_score=control_score,
        skeleton_score=skeleton_score,
        total_score=total_score,
    )


def evaluate_dataset(name: str, root: Path) -> DatasetScore:
    return _evaluate_files(name, _iter_c_files(root))


def _format_table(rows: Sequence[DatasetScore]) -> str:
    headers = [
        "dataset",
        "files",
        "ctrl_u",
        "skel_u",
        "ctrl_H",
        "skel_H",
        "ctrl_score",
        "skel_score",
        "total",
    ]
    body = []
    for row in rows:
        body.append(
            [
                row.name,
                str(row.files),
                str(row.control_unique),
                str(row.skeleton_unique),
                f"{row.control_entropy:.3f}",
                f"{row.skeleton_entropy:.3f}",
                f"{row.control_score:.3f}",
                f"{row.skeleton_score:.3f}",
                f"{row.total_score:.3f}",
            ]
        )
    widths = [max(len(headers[i]), max((len(r[i]) for r in body), default=0)) for i in range(len(headers))]
    out = [
        "  ".join(headers[i].ljust(widths[i]) for i in range(len(headers))),
        "  ".join("-" * widths[i] for i in range(len(headers))),
    ]
    for row in body:
        out.append("  ".join(row[i].ljust(widths[i]) for i in range(len(headers))))
    return "\n".join(out)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Evaluate control-flow and skeleton diversity over loop datasets.")
    parser.add_argument(
        "--dataset",
        action="append",
        default=[],
        help="Dataset spec in the form name=/abs/or/relative/path. Can be repeated.",
    )
    parser.add_argument("--json", action="store_true", help="Print JSON instead of a text table.")
    return parser.parse_args()


def _resolve_datasets(specs: Sequence[str]) -> List[Tuple[str, Path]]:
    datasets: List[Tuple[str, Path]] = []
    if not specs:
        return list(DEFAULT_DATASETS.items())
    for spec in specs:
        if "=" not in spec:
            raise SystemExit(f"Invalid --dataset '{spec}', expected name=path")
        name, raw = spec.split("=", 1)
        datasets.append((name.strip(), Path(raw).expanduser().resolve()))
    return datasets


def main() -> None:
    args = parse_args()
    resolved = _resolve_datasets(args.dataset)
    rows = [evaluate_dataset(name, path) for name, path in resolved]
    if not args.dataset:
        benchmark_files: List[Path] = []
        for bench_name in ("linear", "NLA_lipus", "question"):
            benchmark_files.extend(_iter_c_files(DEFAULT_DATASETS[bench_name]))
        rows.insert(3, _evaluate_files("benchmark_all", sorted(benchmark_files)))
    if args.json:
        print(json.dumps([row.__dict__ for row in rows], ensure_ascii=False, indent=2))
        return
    print(_format_table(rows))


if __name__ == "__main__":
    main()
