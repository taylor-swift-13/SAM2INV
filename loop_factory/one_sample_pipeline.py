#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import logging
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


def make_logger(log_path: Path) -> logging.Logger:
    logger = logging.getLogger("loop_factory_one_sample")
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
    inv_norm = "||".join(sorted(re.sub(r"\s+", " ", x.strip()) for x in invariants))
    payload = normalize_code(raw_code) + "##" + inv_norm
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def has_no_assert(code: str) -> bool:
    return re.search(r"/\*@\s*assert\b", code) is None


def extract_updated_vars(loop_content: str) -> Set[str]:
    updated = set(re.findall(r"\b([A-Za-z_]\w*)\s*=", loop_content))
    keywords = {
        "if", "while", "for", "int", "return", "else", "do", "switch", "case", "sizeof", "main"
    }
    return {v for v in updated if v not in keywords}


def is_tautological(inv: str) -> bool:
    x = re.sub(r"\s+", "", inv)
    if x in {"1", "true", "True"}:
        return True
    m = re.match(r"^([A-Za-z_]\w*)==\1$", x)
    return m is not None


def is_relational(inv: str) -> bool:
    vars_found = set(re.findall(r"\b([A-Za-z_]\w*)\b", inv))
    vars_found = {v for v in vars_found if v not in {"loop", "invariant", "Pre"}}
    has_rel_op = any(op in inv for op in ["==", "!=", "<=", ">=", "<", ">"])
    return len(vars_found) >= 2 and has_rel_op


def quality_gate(gen: InvariantGenerator, raw_code: str, annotated_code: str) -> Tuple[bool, str]:
    invariants = gen._extract_invariants_from_code(annotated_code)
    if not invariants:
        return False, "empty invariants"
    if len(invariants) < 2:
        return False, "too few invariants"
    if any(is_tautological(inv) for inv in invariants):
        return False, "contains tautology"
    if not any(is_relational(inv) for inv in invariants):
        return False, "no relational invariant"

    loop_content = ""
    if gen.sampler.records:
        loop_content = gen.sampler.records[0].get("loop_content", "")
    updated_vars = extract_updated_vars(loop_content)
    if updated_vars:
        coverage_ok = all(any(v in inv for inv in invariants) for v in updated_vars)
        if not coverage_ok:
            return False, f"insufficient coverage for updated vars: {sorted(updated_vars)}"

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
        "rich",
        "--out-dir",
        str(out_dir),
        "--count",
        "1",
        "--seed",
        str(seed),
        "--max-loops",
        "4",
        "--max-depth",
        "2",
        "--p-multi",
        "0.35",
        "--q-nest",
        "0.15",
    ]
    subprocess.run(cmd, check=True)
    c_files = sorted(out_dir.glob("*.c"), key=lambda p: int(p.stem))
    if not c_files:
        raise RuntimeError("loop_factory did not generate any .c file")
    return c_files[0]


def main() -> None:
    work_root = ROOT / "generated" / "hq_one_sample"
    raw_dir = work_root / "raw"
    ann_dir = work_root / "annotated"
    tmp_loops = work_root / "tmp_loops"
    logs_dir = work_root / "logs"
    for d in [raw_dir, ann_dir, tmp_loops, logs_dir]:
        d.mkdir(parents=True, exist_ok=True)

    input_subdir = "loop_factory_one"
    src_input_dir = SRC / "input" / input_subdir
    src_output_dir = SRC / "output" / input_subdir
    if src_input_dir.exists():
        shutil.rmtree(src_input_dir)
    if src_output_dir.exists():
        shutil.rmtree(src_output_dir)
    src_input_dir.mkdir(parents=True, exist_ok=True)
    src_output_dir.mkdir(parents=True, exist_ok=True)

    # Single-prompt single-model training mode.
    config.PARALLEL_GENERATION_CONFIG["num_candidates"] = 1
    config.PARALLEL_GENERATION_CONFIG["use_threading"] = False
    config.PARALLEL_GENERATION_CONFIG["max_workers"] = 1
    config.PARALLEL_GENERATION_CONFIG["temperature"] = 0.2
    invgen_mod.USE_TRACES = False

    llm_cfg = LLMConfig()
    llm_cfg.api_model = "gpt-5-mini"

    # Load existing signatures for dedup (if rerun).
    signatures: Set[str] = set()
    sig_file = work_root / "accepted_signatures.txt"
    if sig_file.exists():
        for line in sig_file.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line:
                signatures.add(line)

    max_attempts = 20
    accepted = None
    reject_log: List[Dict] = []

    for attempt in range(max_attempts):
        seed = 2026 + attempt
        src_c = generate_one_loop(tmp_loops, seed)
        raw_code = src_c.read_text(encoding="utf-8")
        if not has_no_assert(raw_code):
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": "generated input has assert"})
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

        # Capture the exact first API call pair to align training data with loop_inv.py.
        captured: Dict[str, str] = {"user_prompt": "", "raw_response": ""}
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
            reject_log.append(
                {
                    "attempt": attempt + 1,
                    "seed": seed,
                    "reason": "syntax/valid failed",
                    "first_pass": first_pass,
                }
            )
            continue

        out_c = src_output_dir / f"{file_id}.c"
        annotated = out_c.read_text(encoding="utf-8") if out_c.exists() else (final_code or "")
        ok, reason = quality_gate(gen, raw_code, annotated)
        if not ok:
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": reason})
            continue

        invariants = gen._extract_invariants_from_code(annotated)
        sig = compute_signature(raw_code, invariants)
        if sig in signatures:
            reject_log.append({"attempt": attempt + 1, "seed": seed, "reason": "duplicate sample"})
            continue

        signatures.add(sig)
        accepted = {
            "seed": seed,
            "raw_code": raw_code,
            "annotated_code": annotated,
            "invariants": invariants,
            "token_stats": get_token_stats(),
            "signature": sig,
            "first_pass": first_pass,
            "captured_user_prompt": captured["user_prompt"],
            "captured_raw_response": captured["raw_response"],
        }
        break

    (work_root / "reject_log.json").write_text(json.dumps(reject_log, ensure_ascii=False, indent=2), encoding="utf-8")
    if accepted is None:
        raise RuntimeError(f"Failed to build 1 high-quality sample in {max_attempts} attempts.")

    # Output files required by the user.
    raw_path = raw_dir / "1.c"
    ann_path = ann_dir / "1.c"
    raw_path.write_text(accepted["raw_code"], encoding="utf-8")
    ann_path.write_text(accepted["annotated_code"], encoding="utf-8")
    sig_file.write_text("\n".join(sorted(signatures)) + "\n", encoding="utf-8")

    # Llama-Factory compatible alpaca format.
    dataset_item = {
        "id": "loop_factory_1",
        "instruction": "Generate ACSL loop annotations (loop invariant and loop assigns) for this C program.",
        "input": accepted["raw_code"],
        "output": accepted["annotated_code"],
        "meta": {
            "model": "gpt-5-mini",
            "no_assert_target": True,
            "quality_gate": "pass",
            "invariant_count": len(accepted["invariants"]),
            "signature": accepted["signature"],
        },
    }
    jsonl_path = work_root / "llama_factory_train.jsonl"
    with jsonl_path.open("w", encoding="utf-8") as f:
            f.write(json.dumps(dataset_item, ensure_ascii=False) + "\n")

    # API-aligned I/O dataset:
    # instruction = system prompt (assistant role seed)
    # input       = exact user prompt sent in first generation call
    # output      = exact raw model response of that call
    system_prompt = (SRC / "prompts" / "system_prompt.txt").read_text(encoding="utf-8")
    api_aligned_item = {
        "instruction": system_prompt,
        "input": accepted["captured_user_prompt"],
        "output": accepted["captured_raw_response"],
    }
    api_jsonl_path = work_root / "llama_factory_train_iio_api_aligned.jsonl"
    with api_jsonl_path.open("w", encoding="utf-8") as f:
        f.write(json.dumps(api_aligned_item, ensure_ascii=False) + "\n")

    summary = {
        "status": "ok",
        "work_root": str(work_root),
        "raw_c": str(raw_path),
        "annotated_c": str(ann_path),
        "jsonl": str(jsonl_path),
        "api_aligned_jsonl": str(api_jsonl_path),
        "seed": accepted["seed"],
        "invariants": accepted["invariants"],
        "token_stats": accepted["token_stats"],
    }
    (work_root / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
