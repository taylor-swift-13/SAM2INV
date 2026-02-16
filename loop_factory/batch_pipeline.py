#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import logging
import random
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
sys.path.insert(0, str(SRC))

import config  # type: ignore
import inv_generator as invgen_mod  # type: ignore
from inv_generator import InvariantGenerator  # type: ignore
from llm import LLMConfig, reset_token_stats, get_token_stats  # type: ignore


CPP_KEYWORDS = {
    "if", "else", "while", "for", "int", "return", "break", "continue", "char", "float",
    "double", "void", "do", "switch", "case", "sizeof", "struct", "union", "enum", "typedef",
    "static", "extern", "const", "volatile", "unsigned", "signed", "short", "long", "main",
    "loop", "invariant", "assigns", "variant", "requires", "assert", "Pre",
}


def count_loops(code: str) -> int:
    return len(re.findall(r"\bwhile\s*\(", code)) + len(re.findall(r"\bfor\s*\(", code))


def canonicalize_identifiers(text: str) -> str:
    """
    Canonicalize identifiers to make signature invariant to variable renaming.
    """
    token_pat = re.compile(r"\b([A-Za-z_]\w*)\b")
    mapping: Dict[str, str] = {}
    idx = 1

    def repl(m: re.Match) -> str:
        nonlocal idx
        tok = m.group(1)
        if tok in CPP_KEYWORDS or tok.startswith("main"):
            return tok
        if tok not in mapping:
            mapping[tok] = f"v{idx}"
            idx += 1
        return mapping[tok]

    return token_pat.sub(repl, text)


def make_logger(log_path: Path) -> logging.Logger:
    logger = logging.getLogger(f"batch_pipeline_{log_path.stem}")
    logger.setLevel(logging.INFO)
    logger.handlers.clear()
    fh = logging.FileHandler(log_path, mode="w", encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s - %(levelname)s - %(message)s"))
    logger.addHandler(fh)
    return logger


def normalize_code(s: str) -> str:
    s = re.sub(r"/\*.*?\*/", "", s, flags=re.DOTALL)
    s = re.sub(r"//.*?$", "", s, flags=re.MULTILINE)
    s = re.sub(r"\s+", "", s)
    return s


def compute_signature(raw_code: str, invariants: List[str]) -> str:
    raw_norm = normalize_code(canonicalize_identifiers(raw_code))
    inv_norm = "||".join(
        sorted(
            normalize_code(canonicalize_identifiers(re.sub(r"\s+", " ", x.strip())))
            for x in invariants
        )
    )
    payload = raw_norm + "##" + inv_norm
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def compute_raw_structure_key(raw_code: str) -> str:
    raw_norm = normalize_code(canonicalize_identifiers(raw_code))
    return hashlib.sha256(raw_norm.encode("utf-8")).hexdigest()


def has_no_assert(code: str) -> bool:
    return re.search(r"/\*@\s*assert\b", code) is None


def extract_updated_vars(loop_content: str) -> Set[str]:
    updated = set(re.findall(r"\b([A-Za-z_]\w*)\s*=", loop_content))
    return {v for v in updated if v not in CPP_KEYWORDS}


def is_tautological(inv: str) -> bool:
    x = re.sub(r"\s+", "", inv)
    if x in {"1", "true", "True"}:
        return True

    m = re.match(r"^([A-Za-z_]\w*)==(.+)$", x)
    if not m:
        m2 = re.match(r"^(.+)==([A-Za-z_]\w*)$", x)
        if not m2:
            return False
        lhs, rhs = m2.group(2), m2.group(1)
    else:
        lhs, rhs = m.group(1), m.group(2)

    def strip_mul1(e: str) -> str:
        e = e.strip("()")
        e = re.sub(r"^1\*", "", e)
        e = re.sub(r"\*1$", "", e)
        e = re.sub(r"\+0$", "", e)
        e = re.sub(r"-0$", "", e)
        e = re.sub(r"/1$", "", e)
        return e

    def is_zero_expr(e: str) -> bool:
        e = e.strip("()")
        if e == "0":
            return True
        if "-" in e and e.count("-") == 1:
            a, b = e.split("-", 1)
            if strip_mul1(a) == strip_mul1(b):
                return True
        return False

    rhs_norm = strip_mul1(rhs)
    if lhs == rhs_norm:
        return True
    if rhs.startswith(lhs + "+") and is_zero_expr(rhs[len(lhs) + 1 :]):
        return True
    if rhs.startswith(lhs + "-") and is_zero_expr(rhs[len(lhs) + 1 :]):
        return True
    return False


def is_relational(inv: str) -> bool:
    vars_found = set(re.findall(r"\b([A-Za-z_]\w*)\b", inv))
    vars_found = {v for v in vars_found if v not in CPP_KEYWORDS}
    has_rel_op = any(op in inv for op in ["==", "!=", "<=", ">=", "<", ">"])
    return len(vars_found) >= 2 and has_rel_op


def quality_gate(gen: InvariantGenerator, raw_code: str, annotated_code: str) -> Tuple[bool, str]:
    if count_loops(raw_code) != 1:
        return False, "not single-loop input"

    invariants = gen._extract_invariants_from_code(annotated_code)
    if not invariants:
        return False, "empty invariants"
    if len(invariants) < 2:
        return False, "too few invariants"
    if any(is_tautological(inv) for inv in invariants):
        return False, "contains tautology"
    relation_invs = [inv for inv in invariants if is_relational(inv) and not is_tautological(inv)]
    if len(relation_invs) < 2:
        return False, "insufficient relational invariants"

    loop_content = ""
    if gen.sampler.records:
        loop_content = gen.sampler.records[0].get("loop_content", "")
    updated_vars = extract_updated_vars(loop_content)
    if updated_vars:
        # Deterministic "behavior coverage": every updated var must appear in a non-trivial relation.
        for v in sorted(updated_vars):
            if not any(re.search(rf"\b{re.escape(v)}\b", inv) for inv in relation_invs):
                return False, f"updated var not covered by relational invariant: {v}"

        # Require one relation to tie loop progress variable to state variables.
        loop_var = gen._extract_loop_variable(loop_content) if loop_content else None
        if loop_var:
            if not any(re.search(rf"\b{re.escape(loop_var)}\b", inv) and len(set(re.findall(r'\b([A-Za-z_]\w*)\b', inv))) >= 2 for inv in relation_invs):
                return False, f"no progress-linked relational invariant for loop var {loop_var}"

    if not has_no_assert(raw_code):
        return False, "input unexpectedly contains assert"
    return True, "ok"


def generate_one_loop(out_dir: Path, seed: int) -> Path:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        sys.executable,
        str(ROOT / "loop_factory.py"),
        "--profile",
        "benchmark",
        "--out-dir",
        str(out_dir),
        "--count",
        "1",
        "--seed",
        str(seed),
        "--max-loops",
        "1",
        "--max-depth",
        "1",
        "--p-multi",
        "0.0",
        "--q-nest",
        "0.0",
    ]
    subprocess.run(cmd, check=True)
    c_files = sorted(out_dir.glob("*.c"), key=lambda p: int(p.stem))
    if not c_files:
        raise RuntimeError("loop_factory did not generate any .c")
    return c_files[0]


def extract_candidate_vars(code: str) -> List[str]:
    ids = set(re.findall(r"\b([A-Za-z_]\w*)\b", code))
    ids = {x for x in ids if x not in CPP_KEYWORDS and not x.startswith("main")}
    return sorted(ids)


def apply_var_rename(text: str, mapping: Dict[str, str]) -> str:
    out = text
    for src, dst in mapping.items():
        out = re.sub(rf"\b{re.escape(src)}\b", dst, out)
    return out


def convert_for_to_while(code: str) -> str:
    # Conservative conversion for simple one-block for loops.
    pattern = re.compile(r"for\s*\(([^;{}]*);([^;{}]*);([^){}]*)\)\s*\{", re.DOTALL)
    return pattern.sub(lambda m: f"{m.group(1).strip()};\nwhile ({m.group(2).strip()}) {{", code)


def build_augments(base_item: Dict, aug_per_sample: int, rng: random.Random) -> List[Dict]:
    augments: List[Dict] = []
    seen = set()

    base_raw = base_item["raw_c"]
    vars_list = extract_candidate_vars(base_raw)

    tries = 0
    while len(augments) < aug_per_sample and tries < max(8, aug_per_sample * 10):
        tries += 1
        i = len(augments)
        item = dict(base_item)
        mode = tries % 2

        if mode == 0 and vars_list:
            # Variable rename augmentation.
            shuffled = vars_list[:]
            rng.shuffle(shuffled)
            mapping = {a: b for a, b in zip(vars_list, shuffled) if a != b}
            if not mapping:
                continue
            for k in ["raw_c", "annotated_c", "user_prompt", "raw_model_output"]:
                item[k] = apply_var_rename(item[k], mapping)
            item["augmentation"] = {"type": "var_rename", "mapping": mapping}
        else:
            # for->while textual augmentation (often no-op for existing while-only loops).
            changed = False
            for k in ["raw_c", "annotated_c", "user_prompt", "raw_model_output"]:
                new_text = convert_for_to_while(item[k])
                if new_text != item[k]:
                    changed = True
                    item[k] = new_text
            if not changed:
                continue
            item["augmentation"] = {"type": "for_to_while"}

        key = hashlib.sha256((item["user_prompt"] + "##" + item["raw_model_output"]).encode("utf-8")).hexdigest()
        if key in seen:
            continue
        seen.add(key)
        # Recompute signature after semantic-preserving transformation.
        invs = [m.strip() for m in re.findall(r"loop invariant\s+([^;]+);", item.get("annotated_c", ""))]
        item["signature"] = compute_signature(item.get("raw_c", ""), invs)
        item["raw_structure_key"] = compute_raw_structure_key(item.get("raw_c", ""))
        augments.append(item)

    return augments


def main() -> None:
    parser = argparse.ArgumentParser(description="Batch generate high-quality training data with simple augmentation.")
    parser.add_argument("--target-count", type=int, default=100, help="Number of accepted base samples.")
    parser.add_argument("--aug-per-sample", type=int, default=1, help="Augmented copies per accepted sample.")
    parser.add_argument("--max-attempts", type=int, default=1200, help="Max generation attempts before stop.")
    parser.add_argument("--seed", type=int, default=2026, help="Base random seed.")
    parser.add_argument("--work-dir", type=str, default="", help="Optional work dir under loop_factory/generated.")
    args = parser.parse_args()

    work_root = ROOT / "generated" / (args.work_dir if args.work_dir else "hq_batch_100")
    raw_dir = work_root / "raw"
    ann_dir = work_root / "annotated"
    tmp_loops = work_root / "tmp_loops"
    logs_dir = work_root / "logs"
    for d in [raw_dir, ann_dir, tmp_loops, logs_dir]:
        d.mkdir(parents=True, exist_ok=True)

    input_subdir = "loop_factory_batch_tmp"
    src_input_dir = SRC / "input" / input_subdir
    src_output_dir = SRC / "output" / input_subdir
    if src_input_dir.exists():
        shutil.rmtree(src_input_dir)
    if src_output_dir.exists():
        shutil.rmtree(src_output_dir)
    src_input_dir.mkdir(parents=True, exist_ok=True)
    src_output_dir.mkdir(parents=True, exist_ok=True)

    # Align with single prompt + single model generation path.
    config.PARALLEL_GENERATION_CONFIG["num_candidates"] = 1
    config.PARALLEL_GENERATION_CONFIG["use_threading"] = False
    config.PARALLEL_GENERATION_CONFIG["max_workers"] = 1
    config.PARALLEL_GENERATION_CONFIG["temperature"] = 0.2
    invgen_mod.USE_TRACES = False

    llm_cfg = LLMConfig()
    llm_cfg.api_model = "gpt-5-mini"
    system_prompt = (SRC / "prompts" / "system_prompt.txt").read_text(encoding="utf-8")

    signatures: Set[str] = set()
    sig_file = work_root / "accepted_signatures.txt"
    if sig_file.exists():
        for line in sig_file.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line:
                signatures.add(line)
    raw_structures: Set[str] = set()
    raw_struct_file = work_root / "accepted_raw_structures.txt"
    if raw_struct_file.exists():
        for line in raw_struct_file.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line:
                raw_structures.add(line)

    accepted_records: List[Dict] = []
    reject_log: List[Dict] = []
    rng = random.Random(args.seed)

    for attempt in range(args.max_attempts):
        if len(accepted_records) >= args.target_count:
            break

        seed = args.seed + attempt
        src_c = generate_one_loop(tmp_loops, seed)
        raw_code = src_c.read_text(encoding="utf-8")
        if not has_no_assert(raw_code):
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": "input has assert"})
            continue

        file_id = "1"
        input_c = src_input_dir / f"{file_id}.c"
        input_c.write_text(raw_code, encoding="utf-8")

        reset_token_stats()
        logger = make_logger(logs_dir / f"attempt_{attempt+1}.log")
        gen = InvariantGenerator(
            file_id,
            llm_config=llm_cfg,
            logger=logger,
            output_dir=str(src_output_dir),
            input_subdir=input_subdir,
        )

        captured = {"user_prompt": "", "raw_response": ""}
        original_chat = gen.llm.chat

        def chat_capture(user_input: str) -> str:
            resp = original_chat(user_input)
            if not captured["user_prompt"]:
                captured["user_prompt"] = user_input
                captured["raw_response"] = resp
            return resp

        gen.llm.chat = chat_capture  # type: ignore[assignment]

        final_code = gen.generate_all(max_iterations=1)
        gen.save_results(str(src_output_dir))
        first_pass = gen.first_pass or {}
        syntax_ok = first_pass.get("syntax") is not None
        valid_ok = first_pass.get("valid") is not None
        if not (syntax_ok and valid_ok):
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": "syntax/valid failed"})
            continue

        out_c = src_output_dir / f"{file_id}.c"
        annotated = out_c.read_text(encoding="utf-8") if out_c.exists() else (final_code or "")
        ok, reason = quality_gate(gen, raw_code, annotated)
        if not ok:
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": reason})
            continue

        invariants = gen._extract_invariants_from_code(annotated)
        sig = compute_signature(raw_code, invariants)
        raw_key = compute_raw_structure_key(raw_code)
        if raw_key in raw_structures:
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": "duplicate raw structure"})
            continue
        if sig in signatures:
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": "duplicate signature"})
            continue

        signatures.add(sig)
        raw_structures.add(raw_key)
        idx = len(accepted_records) + 1
        (raw_dir / f"{idx}.c").write_text(raw_code, encoding="utf-8")
        (ann_dir / f"{idx}.c").write_text(annotated, encoding="utf-8")

        accepted_records.append(
            {
                "id": f"loop_factory_{idx}",
                "seed": seed,
                "model": "gpt-5-mini",
                "system_prompt": system_prompt,
                "user_prompt": captured["user_prompt"],
                "raw_model_output": captured["raw_response"],
                "raw_c": raw_code,
                "annotated_c": annotated,
                "invariants": invariants,
                "signature": sig,
                "raw_structure_key": raw_key,
                "first_pass": first_pass,
                "token_stats": get_token_stats(),
                "augmentation": {"type": "none"},
            }
        )

    # Augmentation pass.
    augmented_records: List[Dict] = []
    for rec in accepted_records:
        augmented_records.extend(build_augments(rec, args.aug_per_sample, rng))

    # Global dedup after augmentation (by signature then by i/o hash).
    deduped: List[Dict] = []
    seen_sig: Set[str] = set()
    seen_iio: Set[str] = set()
    seen_raw: Set[str] = set()
    for item in accepted_records + augmented_records:
        sig = item.get("signature", "")
        iio_key = hashlib.sha256(
            (item.get("system_prompt", "") + "##" + item.get("user_prompt", "") + "##" + item.get("raw_model_output", "")).encode("utf-8")
        ).hexdigest()
        if sig and sig in seen_sig:
            continue
        if iio_key in seen_iio:
            continue
        raw_key = item.get("raw_structure_key", "")
        if raw_key and raw_key in seen_raw:
            continue
        if sig:
            seen_sig.add(sig)
        seen_iio.add(iio_key)
        if raw_key:
            seen_raw.add(raw_key)
        deduped.append(item)

    # Build final datasets.
    full_items = deduped
    iio_items = [
        {
            "instruction": item["system_prompt"],
            "input": item["user_prompt"],
            "output": item["raw_model_output"],
        }
        for item in full_items
    ]

    full_path = work_root / "dataset_full.jsonl"
    iio_path = work_root / "dataset_train_iio.jsonl"
    with full_path.open("w", encoding="utf-8") as f:
        for item in full_items:
            f.write(json.dumps(item, ensure_ascii=False) + "\n")
    with iio_path.open("w", encoding="utf-8") as f:
        for item in iio_items:
            f.write(json.dumps(item, ensure_ascii=False) + "\n")

    sig_file.write_text("\n".join(sorted(signatures)) + "\n", encoding="utf-8")
    raw_struct_file.write_text("\n".join(sorted(raw_structures)) + "\n", encoding="utf-8")
    (work_root / "reject_log.json").write_text(json.dumps(reject_log, ensure_ascii=False, indent=2), encoding="utf-8")
    summary = {
        "status": "ok",
        "target_count": args.target_count,
        "accepted_count": len(accepted_records),
        "aug_per_sample": args.aug_per_sample,
        "augmented_count": len(augmented_records),
        "total_train_items": len(iio_items),
        "work_root": str(work_root),
        "dataset_full": str(full_path),
        "dataset_train_iio": str(iio_path),
        "reject_log": str(work_root / "reject_log.json"),
    }
    (work_root / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    if len(accepted_records) < args.target_count:
        raise RuntimeError(
            f"Accepted {len(accepted_records)} samples, below target_count={args.target_count}. "
            "No low-quality fallback will be written."
        )


if __name__ == "__main__":
    main()
