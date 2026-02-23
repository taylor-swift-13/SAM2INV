#!/usr/bin/env python3
import argparse
import json
import logging
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from houdini_pruner import HoudiniPruner  # noqa: E402
from output_verify import OutputVerifier  # noqa: E402


INV_PATTERN = re.compile(r"^(\s*)loop\s+invariant\s+([^;]+?);", re.MULTILINE)


def _line_number_from_pos(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def _build_ok_flags(code: str, verifier: OutputVerifier) -> List[bool]:
    matches = list(INV_PATTERN.finditer(code))
    if not matches:
        return []

    line_map = getattr(verifier, "validate_result_by_line", {}) or {}
    if line_map:
        return [bool(line_map.get(_line_number_from_pos(code, m.start()), True)) for m in matches]

    validate_result = list(getattr(verifier, "validate_result", []) or [])
    if len(validate_result) != len(matches):
        n = min(len(validate_result), len(matches))
        validate_result = validate_result[:n] + [True] * (len(matches) - n)
    return [bool(x) for x in validate_result]


def _single_bad_rejects_from_round(
    code: str,
    ok_flags: List[bool],
    pruner: HoudiniPruner,
) -> List[str]:
    failed_indices = [i for i, ok in enumerate(ok_flags) if not ok]
    if not failed_indices:
        return []

    out: List[str] = []
    for idx in failed_indices:
        keep_flags = list(ok_flags)
        keep_flags[idx] = True
        # Keep all valid invariants + exactly one failed invariant.
        one_bad = pruner.hudini_annotations(keep_flags, code, validate_result_by_line=None).strip()
        if one_bad:
            out.append(one_bad)
    return out


def _augment_one_rejected(
    rejected_code: str,
    verifier: OutputVerifier,
    pruner: HoudiniPruner,
    tmp_c_path: Path,
    max_rounds: int,
) -> Tuple[bool, List[str]]:
    current = (rejected_code or "").strip()
    if not current:
        return False, []

    new_rejects: List[str] = []
    seen = set()
    syntax_ok = False

    for _ in range(max_rounds):
        tmp_c_path.write_text(current, encoding="utf-8")
        verifier.run(str(tmp_c_path))

        if not verifier.syntax_correct:
            break
        syntax_ok = True

        ok_flags = _build_ok_flags(current, verifier)
        if not ok_flags:
            break
        if all(ok_flags):
            break

        for rej in _single_bad_rejects_from_round(current, ok_flags, pruner):
            if rej not in seen:
                seen.add(rej)
                new_rejects.append(rej)

        next_code = pruner.hudini_annotations(ok_flags, current, validate_result_by_line=None).strip()
        if not next_code or next_code == current:
            break
        current = next_code

    return syntax_ok, new_rejects


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Augment DPO jsonl by splitting per-round failed invariants from rejected via Frama-C Houdini."
    )
    parser.add_argument(
        "--input-jsonl",
        type=Path,
        default=ROOT / "loop_factory/generated/batch/llama_factory_train_dpo.jsonl",
    )
    parser.add_argument(
        "--output-jsonl",
        type=Path,
        default=ROOT / "loop_factory/generated/batch/llama_factory_train_dpo_aug_houdini.jsonl",
    )
    parser.add_argument(
        "--tmp-dir",
        type=Path,
        default=ROOT / "loop_factory/generated/batch/tmp_houdini_aug",
    )
    parser.add_argument(
        "--mode",
        choices=["append", "only_augmented"],
        default="append",
        help="append: output original + augmented, only_augmented: output only new rows",
    )
    parser.add_argument("--max-rounds", type=int, default=20)
    parser.add_argument("--limit", type=int, default=0, help="Only process first N rows, 0 means all")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
    logger = logging.getLogger("augment_dpo_houdini")

    args.tmp_dir.mkdir(parents=True, exist_ok=True)
    tmp_c_path = args.tmp_dir / "tmp_aug_houdini.c"

    verifier = OutputVerifier(logger=logger, output=False)
    pruner = HoudiniPruner(logger=logger)

    all_rows: List[Dict] = []
    with args.input_jsonl.open("r", encoding="utf-8") as f:
        for i, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                logger.warning("Skip invalid JSON at line %d", i)
                continue
            all_rows.append(row)
            if args.limit > 0 and len(all_rows) >= args.limit:
                break

    output_rows: List[Dict] = []
    if args.mode == "append":
        output_rows.extend(all_rows)

    total = len(all_rows)
    syntax_ok_count = 0
    augmented_count = 0
    dedup_keys = set()
    for idx, row in enumerate(all_rows, start=1):
        rejected = row.get("rejected", "")
        syntax_ok, new_rejects = _augment_one_rejected(
            rejected_code=rejected,
            verifier=verifier,
            pruner=pruner,
            tmp_c_path=tmp_c_path,
            max_rounds=max(1, args.max_rounds),
        )
        if syntax_ok:
            syntax_ok_count += 1

        for rej in new_rejects:
            new_row = dict(row)
            new_row["rejected"] = rej
            key = (
                new_row.get("instruction", ""),
                new_row.get("input", ""),
                new_row.get("chosen", ""),
                new_row.get("rejected", ""),
            )
            if key in dedup_keys:
                continue
            dedup_keys.add(key)
            output_rows.append(new_row)
            augmented_count += 1

        if idx % 20 == 0 or idx == total:
            logger.info("Processed %d/%d rows, syntax_ok=%d, augmented=%d", idx, total, syntax_ok_count, augmented_count)

    args.output_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with args.output_jsonl.open("w", encoding="utf-8") as f:
        for row in output_rows:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")

    logger.info("Input rows: %d", total)
    logger.info("Syntax-correct rejected rows: %d", syntax_ok_count)
    logger.info("New augmented rows: %d", augmented_count)
    logger.info("Output rows: %d", len(output_rows))
    logger.info("Wrote: %s", args.output_jsonl)


if __name__ == "__main__":
    main()
