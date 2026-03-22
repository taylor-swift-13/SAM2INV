#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple


CODE_BLOCK_RE = re.compile(r"Code:\s*```c\n(.*?)\n```", re.DOTALL)
PLACEHOLDER_BLOCK_RE = re.compile(
    r"/\*\s*>>>\s*LOOP INVARIANT TO FILL\s*<<<\s*\*/\s*/\*@.*?\*/",
    re.DOTALL,
)
WHITESPACE_RE = re.compile(r"\s+")
REQUIRED_TAGS = ("<reasoning>", "</reasoning>", "<code>", "</code>")


DATASETS = {
    "iio": {"file": "llama_factory_train_iio_api_aligned.jsonl", "fields": ("output",)},
    "dpo_teacher": {"file": "llama_factory_train_dpo_teacher.jsonl", "fields": ("chosen", "rejected")},
    "dpo_aug": {"file": "llama_factory_train_dpo_aug.jsonl", "fields": ("chosen", "rejected")},
    "distill": {"file": "llama_factory_train_distill_sft.jsonl", "fields": ("output",)},
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Clean and synchronize loop dataset files.")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("/home/yangfp/SAM2INV/loop_factory/generated/test"),
        help="Dataset root containing raw/, annotated/, and JSONL files.",
    )
    return parser.parse_args()


def normalize_code(text: str) -> str:
    text = PLACEHOLDER_BLOCK_RE.sub("", text)
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    lines = [line.rstrip() for line in text.split("\n")]
    lines = [line for line in lines if line.strip()]
    return WHITESPACE_RE.sub(" ", "\n".join(lines)).strip()


def load_jsonl(path: Path) -> List[Dict]:
    rows: List[Dict] = []
    with path.open(encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            line = line.strip()
            if not line:
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}: invalid JSON at line {line_no}: {exc}") from exc
    return rows


def write_jsonl(path: Path, rows: Sequence[Dict]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")


def require_tags(text: str) -> bool:
    return all(tag in text for tag in REQUIRED_TAGS)


def extract_input_code(text: str, dataset_name: str, row_idx: int) -> str:
    match = CODE_BLOCK_RE.search(text)
    if not match:
        raise ValueError(f"{dataset_name}: row {row_idx} missing C code block in input")
    return match.group(1)


def load_file_ids(dir_path: Path) -> Set[int]:
    ids: Set[int] = set()
    for path in dir_path.glob("*.c"):
        try:
            ids.add(int(path.stem))
        except ValueError as exc:
            raise ValueError(f"{dir_path}: non-numeric file name {path.name}") from exc
    return ids


def parse_map_loop_id(row: Dict) -> int:
    raw_file = str(row.get("raw_file", "") or "")
    match = re.search(r"(\d+)\.c$", raw_file)
    if match:
        return int(match.group(1))
    row_id = str(row.get("id", "") or "")
    if row_id.isdigit():
        return int(row_id)
    match = re.search(r"(\d+)$", row_id)
    if match:
        return int(match.group(1))
    raise ValueError(f"Cannot parse loop id from map row: {row}")


def build_raw_map(raw_dir: Path) -> Dict[str, int]:
    code_to_id: Dict[str, int] = {}
    dupes: Dict[str, List[int]] = {}
    for path in sorted(raw_dir.glob("*.c"), key=lambda p: int(p.stem)):
        loop_id = int(path.stem)
        normalized = normalize_code(path.read_text(encoding="utf-8"))
        if normalized in code_to_id:
            dupes.setdefault(normalized, [code_to_id[normalized]]).append(loop_id)
            continue
        code_to_id[normalized] = loop_id
    if dupes:
        detail = ", ".join(str(ids) for ids in dupes.values())
        raise ValueError(f"Duplicate normalized raw loops found: {detail}")
    return code_to_id


def filter_rows_with_tags(rows: Sequence[Dict], fields: Sequence[str]) -> Tuple[List[Dict], int]:
    kept: List[Dict] = []
    dropped = 0
    for row in rows:
        if all(require_tags(str(row.get(field, "") or "")) for field in fields):
            kept.append(row)
        else:
            dropped += 1
    return kept, dropped


def map_rows_to_loop_ids(rows: Sequence[Dict], raw_map: Dict[str, int], dataset_name: str) -> Tuple[List[Tuple[Dict, int]], List[int]]:
    mapped: List[Tuple[Dict, int]] = []
    missing_rows: List[int] = []
    for idx, row in enumerate(rows, 1):
        code = extract_input_code(str(row.get("input", "") or ""), dataset_name, idx)
        loop_id = raw_map.get(normalize_code(code))
        if loop_id is None:
            missing_rows.append(idx)
            continue
        mapped.append((row, loop_id))
    return mapped, missing_rows


def two_phase_renumber(dir_path: Path, old_to_new: Dict[int, int]) -> None:
    temp_paths: List[Tuple[Path, Path]] = []
    final_paths: List[Tuple[Path, Path]] = []
    for old_id, new_id in sorted(old_to_new.items()):
        src = dir_path / f"{old_id}.c"
        temp = dir_path / f".tmp_sync_{old_id}.c"
        dst = dir_path / f"{new_id}.c"
        if not src.exists():
            raise FileNotFoundError(f"Missing source file during rename: {src}")
        temp_paths.append((src, temp))
        final_paths.append((temp, dst))
    for src, temp in temp_paths:
        src.replace(temp)
    for temp, dst in final_paths:
        temp.replace(dst)


def delete_non_intersection(dir_path: Path, keep_ids: Set[int]) -> None:
    for path in dir_path.glob("*.c"):
        loop_id = int(path.stem)
        if loop_id not in keep_ids:
            path.unlink()


def verify_contiguous(ids: Iterable[int], n: int) -> bool:
    return set(ids) == set(range(1, n + 1))


def main() -> None:
    args = parse_args()
    root = args.root.resolve()
    raw_dir = root / "raw"
    annotated_dir = root / "annotated"
    map_path = root / "file_template_map.jsonl"

    raw_ids = load_file_ids(raw_dir)
    annotated_ids = load_file_ids(annotated_dir)
    raw_map = build_raw_map(raw_dir)

    if raw_ids != annotated_ids:
        raise ValueError("raw and annotated ID sets differ before sync")

    dataset_stats: Dict[str, Dict] = {}
    dataset_keep_rows: Dict[str, List[Dict]] = {}
    dataset_id_sets: Dict[str, Set[int]] = {}
    missing_match_rows: Dict[str, List[int]] = {}

    for dataset_name, spec in DATASETS.items():
        path = root / spec["file"]
        rows_before = load_jsonl(path)
        rows_tagged, dropped_bad_tags = filter_rows_with_tags(rows_before, spec["fields"])
        mapped_rows, missing_rows = map_rows_to_loop_ids(rows_tagged, raw_map, dataset_name)
        dataset_keep_rows[dataset_name] = [row for row, _ in mapped_rows]
        dataset_id_sets[dataset_name] = {loop_id for _, loop_id in mapped_rows}
        missing_match_rows[dataset_name] = missing_rows
        dataset_stats[dataset_name] = {
            "path": path,
            "before": len(rows_before),
            "after_tag_filter": len(rows_tagged),
            "dropped_bad_tags": dropped_bad_tags,
            "unmatched_rows": len(missing_rows),
        }

    map_rows = load_jsonl(map_path)
    map_ids = {parse_map_loop_id(row) for row in map_rows}

    global_ids = set(raw_ids)
    global_ids &= annotated_ids
    global_ids &= map_ids
    for ids in dataset_id_sets.values():
        global_ids &= ids

    removed_ids = sorted(raw_ids - global_ids)
    sorted_keep_ids = sorted(global_ids)
    old_to_new = {old_id: new_idx for new_idx, old_id in enumerate(sorted_keep_ids, 1)}

    for dataset_name, spec in DATASETS.items():
        path = root / spec["file"]
        filtered_rows = []
        mapped_rows, _ = map_rows_to_loop_ids(
            filter_rows_with_tags(load_jsonl(path), spec["fields"])[0],
            raw_map,
            dataset_name,
        )
        for row, loop_id in mapped_rows:
            if loop_id in global_ids:
                filtered_rows.append(row)
        write_jsonl(path, filtered_rows)
        dataset_stats[dataset_name]["after"] = len(filtered_rows)

    delete_non_intersection(raw_dir, global_ids)
    delete_non_intersection(annotated_dir, global_ids)
    if global_ids:
        two_phase_renumber(raw_dir, old_to_new)
        two_phase_renumber(annotated_dir, old_to_new)

    new_map_rows = []
    for row in map_rows:
        old_id = parse_map_loop_id(row)
        if old_id not in global_ids:
            continue
        new_id = old_to_new[old_id]
        new_map_rows.append(
            {
                "id": new_id,
                "raw_file": f"raw/{new_id}.c",
                "annotated_file": f"annotated/{new_id}.c",
            }
        )
    new_map_rows.sort(key=lambda row: int(row["id"]))
    write_jsonl(map_path, new_map_rows)

    n = len(global_ids)
    final_raw_ids = load_file_ids(raw_dir)
    final_annotated_ids = load_file_ids(annotated_dir)
    final_map_rows = load_jsonl(map_path)
    final_map_ids = {parse_map_loop_id(row) for row in final_map_rows}
    final_raw_map = build_raw_map(raw_dir)

    verification = {
        "raw_count_ok": len(final_raw_ids) == n,
        "annotated_count_ok": len(final_annotated_ids) == n,
        "raw_ids_ok": verify_contiguous(final_raw_ids, n),
        "annotated_ids_ok": verify_contiguous(final_annotated_ids, n),
        "map_count_ok": len(final_map_rows) == n,
        "map_ids_ok": verify_contiguous(final_map_ids, n),
    }

    final_dataset_sets: Dict[str, Set[int]] = {}
    final_bad_tag_counts: Dict[str, int] = {}
    for dataset_name, spec in DATASETS.items():
        rows = load_jsonl(root / spec["file"])
        bad_count = sum(
            1 for row in rows if not all(require_tags(str(row.get(field, "") or "")) for field in spec["fields"])
        )
        final_bad_tag_counts[dataset_name] = bad_count
        mapped_rows, missing_rows = map_rows_to_loop_ids(rows, final_raw_map, dataset_name)
        final_dataset_sets[dataset_name] = {loop_id for _, loop_id in mapped_rows}
        verification[f"{dataset_name}_ids_ok"] = final_dataset_sets[dataset_name] == set(range(1, n + 1))
        verification[f"{dataset_name}_no_bad_tags"] = bad_count == 0
        verification[f"{dataset_name}_all_rows_matched"] = not missing_rows

    report = {
        "root": str(root),
        "rows_before_after": {
            name: {
                "before": stats["before"],
                "after_tag_filter": stats["after_tag_filter"],
                "after": stats["after"],
                "dropped_bad_tags": stats["dropped_bad_tags"],
                "unmatched_rows_dropped": stats["unmatched_rows"],
            }
            for name, stats in dataset_stats.items()
        },
        "removed_loop_ids": removed_ids,
        "final_n": n,
        "verification": verification,
        "final_jsonl_id_sets": {name: sorted(ids) for name, ids in final_dataset_sets.items()},
        "unmatched_rows_before_sync": missing_match_rows,
        "map_removed_ids": sorted(map_ids - global_ids),
    }
    print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
