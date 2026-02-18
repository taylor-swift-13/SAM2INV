#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import os
import math
import hashlib
import json
import logging
import random
import re
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Dict, List, Set, Tuple

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
VST_GOAL = (ROOT / "../VST/goal").resolve()
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


def compute_loop_skeleton_key(raw_code: str) -> str:
    """
    Loop skeleton key:
    - Canonicalize identifiers.
    - Normalize whitespace/comments.
    - Abstract numeric constants to reduce near-duplicate loop bodies.
    """
    m = re.search(r"while\s*\([^)]*\)\s*\{", raw_code)
    if not m:
        payload = normalize_code(canonicalize_identifiers(raw_code))
        payload = re.sub(r"\b\d+\b", "C", payload)
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()

    i = m.end()
    depth = 1
    while i < len(raw_code):
        c = raw_code[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                body = raw_code[m.end() : i]
                body_norm = normalize_code(canonicalize_identifiers(body))
                body_norm = re.sub(r"\b\d+\b", "C", body_norm)
                return hashlib.sha256(body_norm.encode("utf-8")).hexdigest()
        i += 1

    payload = normalize_code(canonicalize_identifiers(raw_code))
    payload = re.sub(r"\b\d+\b", "C", payload)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def has_no_assert(code: str) -> bool:
    return re.search(r"/\*@\s*assert\b", code) is None


def extract_updated_vars(loop_content: str) -> Set[str]:
    updated = set(re.findall(r"\b([A-Za-z_]\w*)\s*=", loop_content))
    return {v for v in updated if v not in CPP_KEYWORDS}


def has_repetitive_loop_updates(loop_content: str) -> bool:
    """
    Detect low-value repetitive assignment patterns in loop body, e.g.:
    repeated identical updates or long same-target straight-line chains.
    """
    assigns = re.findall(r"\b([A-Za-z_]\w*)\s*=\s*([^;]+);", loop_content or "")
    if not assigns:
        return False

    # Pattern repetition cap by normalized assignment form.
    form_counts: Dict[Tuple[str, str], int] = {}
    for t, e in assigns:
        fp = (t, re.sub(r"\s+", "", e))
        form_counts[fp] = form_counts.get(fp, 0) + 1
        if form_counts[fp] > 2:
            return True

    # Consecutive same-target chain cap.
    prev_t = None
    run = 0
    for t, _ in assigns:
        if t == prev_t:
            run += 1
        else:
            prev_t = t
            run = 1
        if run > 3:
            return True
    return False


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


def inv_identifiers(inv: str) -> Set[str]:
    ids = set(re.findall(r"\b([A-Za-z_]\w*)\b", inv))
    return {x for x in ids if x not in CPP_KEYWORDS and x != "Pre"}


def has_arith_expr(inv: str) -> bool:
    return any(op in inv for op in ["+", "-", "*", "/", "%"])


def is_prestate_copy_only(inv: str) -> bool:
    """
    True for invariants that only state x == \\at(x, Pre)-style unchanged facts
    (possibly chained with &&), which are too weak alone.
    """
    parts = [p.strip() for p in inv.split("&&") if p.strip()]
    if not parts:
        return False
    pat = re.compile(r"^([A-Za-z_]\w*)\s*==\s*\\at\(\s*\1\s*,\s*Pre\s*\)$")
    return all(bool(pat.match(p)) for p in parts)


def is_nontrivial_inv(inv: str) -> bool:
    if is_tautological(inv):
        return False
    if not any(op in inv for op in ["==", "!=", "<=", ">=", "<", ">"]):
        return False
    return True


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
    useful_invs = [inv for inv in invariants if is_nontrivial_inv(inv)]
    if not useful_invs:
        return False, "no nontrivial invariants"

    loop_content = ""
    if gen.sampler.records:
        loop_content = gen.sampler.records[0].get("loop_content", "")
    if has_repetitive_loop_updates(loop_content):
        return False, "repetitive loop updates"
    updated_vars = extract_updated_vars(loop_content)
    if not updated_vars:
        return False, "no updated vars extracted from loop"
    loop_var = gen._extract_loop_variable(loop_content) if loop_content else None
    non_loop_updated = [v for v in sorted(updated_vars) if v != loop_var]
    if not non_loop_updated:
        return False, "counter-only loop body"

    vars_to_cover = set(updated_vars)
    if loop_var:
        vars_to_cover.add(loop_var)

    for v in sorted(vars_to_cover):
        if not any(re.search(rf"\b{re.escape(v)}\b", inv) for inv in useful_invs):
            return False, f"var lacks nontrivial invariant: {v}"

    # Prefer equality constraints for changed non-loop variables (soft ratio).
    eq_covered = 0
    for v in sorted(updated_vars):
        if v == loop_var:
            continue
        has_eq = any(("==" in inv) and re.search(rf"\b{re.escape(v)}\b", inv) for inv in useful_invs)
        if has_eq:
            eq_covered += 1
    if non_loop_updated:
        need_eq = max(1, math.ceil(0.7 * len(non_loop_updated)))
        if eq_covered < need_eq:
            return False, f"insufficient equality coverage: {eq_covered}/{len(non_loop_updated)}"

    # Loop variable should have explicit lower + upper bound.
    if loop_var:
        lo_ok = any(
            re.search(rf"\b{re.escape(loop_var)}\b\s*(>=|>)", inv)
            or re.search(rf"(<=|<)\s*\b{re.escape(loop_var)}\b", inv)
            for inv in useful_invs
        )
        hi_ok = any(
            re.search(rf"\b{re.escape(loop_var)}\b\s*(<=|<)", inv)
            or re.search(rf"(>=|>)\s*\b{re.escape(loop_var)}\b", inv)
            for inv in useful_invs
        )
        if not (lo_ok and hi_ok):
            return False, f"loop var lacks explicit bounds: {loop_var}"

    if not has_no_assert(raw_code):
        return False, "input unexpectedly contains assert"
    return True, "ok"


def generate_one_loop(out_dir: Path, seed: int) -> Path:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    hp = loop_factory_hyperparams(seed, out_dir)
    cmd = [
        sys.executable,
        str(ROOT / "loop_factory.py"),
        "--profile", str(hp["profile"]),
        "--out-dir", str(hp["out_dir"]),
        "--count", str(hp["count"]),
        "--seed", str(hp["seed"]),
        "--max-vars", str(hp["max_vars"]),
        "--params", str(hp["params"]),
        "--min-loops", str(hp["min_loops"]),
        "--max-loops", str(hp["max_loops"]),
        "--max-assign", str(hp["max_assign"]),
        "--max-ifelse", str(hp["max_ifelse"]),
        "--max-depth", str(hp["max_depth"]),
        "--p-multi", str(hp["p_multi"]),
        "--q-nest", str(hp["q_nest"]),
        "--p-nonlinear", str(hp["p_nonlinear"]),
        "--nonlinear-strength", str(hp["nonlinear_strength"]),
        "--p-semantic-core", str(hp["p_semantic_core"]),
        "--w-core-rel-guard", str(hp["w_core_rel_guard"]),
        "--w-core-cond-fixed", str(hp["w_core_cond_fixed"]),
        "--w-core-linear-state", str(hp["w_core_linear_state"]),
    ]
    subprocess.run(cmd, check=True)
    c_files = sorted(out_dir.glob("*.c"), key=lambda p: int(p.stem))
    if not c_files:
        raise RuntimeError("loop_factory did not generate any .c")
    return c_files[0]


def loop_factory_hyperparams(seed: int, out_dir: Path) -> Dict[str, object]:
    """
    Fully materialized loop_factory configuration for one generation call.
    Keep this aligned with loop_factory.py defaults + this pipeline constraints.
    """
    return {
        "profile": "benchmark",
        "out_dir": str(out_dir),
        "count": 1,
        "seed": seed,
        "max_vars": 3,
        "params": 2,
        "min_loops": 1,
        "max_loops": 1,
        "max_assign": 3,
        "max_ifelse": 6,
        "max_depth": 1,
        "p_multi": 0.0,
        "q_nest": 0.0,
        "p_nonlinear": 0.80,
        "nonlinear_strength": 0.50,
        "p_semantic_core": 0.30,
        "w_core_rel_guard": 1.0,
        "w_core_cond_fixed": 1.0,
        "w_core_linear_state": 1.0,
    }


def run_one_attempt(
    attempt: int,
    seed: int,
    work_root: Path,
    logs_dir: Path,
    llm_cfg: LLMConfig,
    model_name: str,
    system_prompt: str,
    run_tag: str,
    stop_event: threading.Event,
) -> Dict:
    if stop_event.is_set():
        return {"ok": False, "reason": "cancelled", "attempt": attempt, "seed": seed}
    attempt_tmp_loops = work_root / "tmp_loops" / f"a{attempt}"
    src_input_dir = SRC / "input" / f"loop_factory_batch_tmp_{run_tag}_{attempt}"
    src_output_dir = SRC / "output" / f"loop_factory_batch_tmp_{run_tag}_{attempt}"
    src_outer_dir = SRC / "outer" / f"loop_factory_batch_tmp_{run_tag}_{attempt}"
    src_input_dir.mkdir(parents=True, exist_ok=True)
    src_output_dir.mkdir(parents=True, exist_ok=True)
    file_id = ""
    goal_prefix = ""

    try:
        if stop_event.is_set():
            return {"ok": False, "reason": "cancelled", "attempt": attempt, "seed": seed}
        src_c = generate_one_loop(attempt_tmp_loops, seed)
        raw_code = src_c.read_text(encoding="utf-8")
        if not has_no_assert(raw_code):
            return {"ok": False, "reason": "input has assert", "attempt": attempt, "seed": seed}

        # Keep function naming stable (main1) for invariant insertion compatibility.
        file_id = "1"
        goal_prefix = f"{src_input_dir.name}_{file_id}"
        input_c = src_input_dir / f"{file_id}.c"
        input_c.write_text(raw_code, encoding="utf-8")

        reset_token_stats()
        logger = make_logger(logs_dir / f"attempt_{attempt}.log")
        gen = InvariantGenerator(
            file_id,
            llm_config=llm_cfg,
            logger=logger,
            output_dir=str(src_output_dir),
            input_subdir=src_input_dir.name,
        )

        captured = {"user_prompt": "", "raw_response": "", "prompt_count": 0}
        original_chat = gen.llm.chat
        original_select_prompt = getattr(gen, "_select_prompt_for_candidate", None)

        def chat_capture(user_input: str) -> str:
            if stop_event.is_set():
                raise RuntimeError("cancelled")
            captured["prompt_count"] += 1
            resp = original_chat(user_input)
            if not captured["user_prompt"]:
                captured["user_prompt"] = user_input
                captured["raw_response"] = resp
            return resp

        gen.llm.chat = chat_capture  # type: ignore[assignment]
        if callable(original_select_prompt):
            def select_prompt_capture(candidate_idx: int, loop_context: str, code_with_template: str):
                prompt, prompt_name = original_select_prompt(candidate_idx, loop_context, code_with_template)
                if not captured["user_prompt"] and isinstance(prompt, str) and prompt.strip():
                    # In multi-candidate mode, real LLM calls may bypass gen.llm.chat.
                    captured["user_prompt"] = prompt
                return prompt, prompt_name
            gen._select_prompt_for_candidate = select_prompt_capture  # type: ignore[assignment]

        if stop_event.is_set():
            return {"ok": False, "reason": "cancelled", "attempt": attempt, "seed": seed}
        final_code = gen.generate_all(max_iterations=1)
        gen.save_results(str(src_output_dir))
        # Hard guard: keep only samples with a real captured prompt from an actual LLM call.
        if not captured["user_prompt"].strip():
            return {"ok": False, "reason": "empty captured prompt", "attempt": attempt, "seed": seed}
        first_pass = gen.first_pass or {}
        syntax_ok = first_pass.get("syntax") is not None
        valid_ok = first_pass.get("valid") is not None
        if not (syntax_ok and valid_ok):
            return {"ok": False, "reason": "syntax/valid failed", "attempt": attempt, "seed": seed}

        out_c = src_output_dir / f"{file_id}.c"
        annotated = out_c.read_text(encoding="utf-8") if out_c.exists() else (final_code or "")
        ok, reason = quality_gate(gen, raw_code, annotated)
        if not ok:
            return {"ok": False, "reason": reason, "attempt": attempt, "seed": seed}

        invariants = gen._extract_invariants_from_code(annotated)
        sig = compute_signature(raw_code, invariants)
        raw_key = compute_raw_structure_key(raw_code)
        hparams = loop_factory_hyperparams(seed, attempt_tmp_loops)
        return {
            "ok": True,
            "attempt": attempt,
            "seed": seed,
            "raw_code": raw_code,
            "annotated": annotated,
            "invariants": invariants,
            "signature": sig,
            "raw_structure_key": raw_key,
            "first_pass": first_pass,
            "token_stats": get_token_stats(),
            "user_prompt": captured["user_prompt"],
            "raw_model_output": captured["raw_response"],
            "prompt_count": captured["prompt_count"],
            "model": model_name,
            "system_prompt": system_prompt,
            "loop_factory_hyperparams": hparams,
        }
    finally:
        for d in [src_input_dir, src_output_dir, src_outer_dir]:
            if d.exists():
                shutil.rmtree(d, ignore_errors=True)
        if goal_prefix and VST_GOAL.exists():
            for p in VST_GOAL.glob(f"{goal_prefix}_*.v"):
                try:
                    p.unlink()
                except OSError:
                    pass
        # LoopSampler creates loop/ and unfold/ dirs as side effects
        subdir_name = src_input_dir.name
        for parent in ["loop", "unfold", "outer"]:
            side_dir = SRC / parent / subdir_name
            if side_dir.exists():
                shutil.rmtree(side_dir, ignore_errors=True)


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
    parser.add_argument("--target-count", type=int, default=100, help="Total candidate attempts to run.")
    parser.add_argument("--aug-per-sample", type=int, default=0, help="(Deprecated, unused) Augmented copies per accepted sample.")
    parser.add_argument("--max-attempts", type=int, default=1200, help="Max generation attempts before stop.")
    parser.add_argument("--seed", type=int, default=2026, help="Base random seed.")
    parser.add_argument("--workers", type=int, default=20, help="Number of concurrent workers.")
    parser.add_argument("--model", type=str, default="gpt-5-mini", help="LLM model name for invariant generation.")
    parser.add_argument("--max-skeleton-repeat", type=int, default=3, help="Maximum accepted samples per loop skeleton key.")
    parser.add_argument(
        "--append",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Append to existing work-dir data and dedup against existing samples (default: true).",
    )
    parser.add_argument("--work-dir", type=str, default="", help="Optional work dir under loop_factory/generated.")
    args = parser.parse_args()

    # LoopSampler uses relative paths assuming CWD is src/
    os.chdir(SRC)

    work_root = ROOT / "generated" / (args.work_dir if args.work_dir else "hq_batch_100")
    raw_dir = work_root / "raw"
    ann_dir = work_root / "annotated"
    tmp_loops = work_root / "tmp_loops"
    logs_dir = work_root / "logs"
    for d in [raw_dir, ann_dir, tmp_loops, logs_dir]:
        d.mkdir(parents=True, exist_ok=True)

    # Keep one-candidate path; outer pipeline handles concurrency.
    config.PARALLEL_GENERATION_CONFIG["num_candidates"] = 5
    config.PARALLEL_GENERATION_CONFIG["use_threading"] = False
    config.PARALLEL_GENERATION_CONFIG["max_workers"] = 1
    config.PARALLEL_GENERATION_CONFIG["temperature"] = 0.2
    invgen_mod.USE_TRACES = False

    llm_cfg = LLMConfig()
    llm_cfg.api_model = args.model
    system_prompt = (SRC / "prompts" / "system_prompt.txt").read_text(encoding="utf-8")
    api_jsonl_path = work_root / "llama_factory_train_iio_api_aligned.jsonl"

    # Build in-memory dedup sets from existing raw/annotated pairs.
    signatures: Set[str] = set()
    raw_structures: Set[str] = set()
    loop_skeleton_counts: Dict[str, int] = {}
    existing_max_idx = 0
    existing_count = 0
    if args.append:
        existing_raw_files = sorted(raw_dir.glob("*.c"), key=lambda p: int(p.stem))
        existing_max_idx = max((int(p.stem) for p in existing_raw_files), default=0)
        for rf in existing_raw_files:
            af = ann_dir / rf.name
            if not af.exists():
                continue
            raw_code = rf.read_text(encoding="utf-8")
            ann_code = af.read_text(encoding="utf-8")
            invariants = [m.strip() for m in re.findall(r"loop invariant\s+([^;]+);", ann_code)]
            sig = compute_signature(raw_code, invariants)
            raw_key = compute_raw_structure_key(raw_code)
            skey = compute_loop_skeleton_key(raw_code)
            signatures.add(sig)
            raw_structures.add(raw_key)
            loop_skeleton_counts[skey] = loop_skeleton_counts.get(skey, 0) + 1
            existing_count += 1

    total_candidates = max(0, args.target_count)
    if args.max_attempts > 0:
        total_candidates = min(total_candidates, args.max_attempts)

    accepted_records: List[Dict] = []
    reject_log: List[Dict] = []
    workers = max(1, args.workers)
    run_tag = f"{os.getpid()}_{int(time.time())}"
    # In append mode, offset seeds to avoid regenerating loops already accepted.
    seed_offset = existing_max_idx if args.append else 0
    next_attempt = 1
    pending: Dict[concurrent.futures.Future, Tuple[int, int]] = {}
    stop_event = threading.Event()
    with api_jsonl_path.open("a" if args.append else "w", encoding="utf-8") as api_jsonl_file:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            while next_attempt <= total_candidates or pending:
                while next_attempt <= total_candidates and len(pending) < workers:
                    attempt = next_attempt
                    next_attempt += 1
                    seed = args.seed + seed_offset + (attempt - 1)
                    fut = ex.submit(
                        run_one_attempt,
                        attempt,
                        seed,
                        work_root,
                        logs_dir,
                        llm_cfg,
                        args.model,
                        system_prompt,
                        run_tag,
                        stop_event,
                    )
                    pending[fut] = (attempt, seed)

                if not pending:
                    break

                done, _ = concurrent.futures.wait(
                    pending.keys(),
                    return_when=concurrent.futures.FIRST_COMPLETED,
                )
                for fut in done:
                    attempt, seed = pending.pop(fut)
                    try:
                        result = fut.result()
                    except Exception as e:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": f"exception: {e}"})
                        continue

                    if not result.get("ok"):
                        reject_log.append(
                            {
                                "attempt": result.get("attempt", attempt),
                                "seed": result.get("seed", seed),
                                "reason": result.get("reason", "unknown"),
                            }
                        )
                        continue

                    raw_key = result["raw_structure_key"]
                    sig = result["signature"]
                    skeleton_key = compute_loop_skeleton_key(result["raw_code"])
                    if raw_key in raw_structures:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "duplicate raw structure"})
                        continue
                    if sig in signatures:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "duplicate signature"})
                        continue
                    if loop_skeleton_counts.get(skeleton_key, 0) >= max(1, args.max_skeleton_repeat):
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "duplicate loop skeleton"})
                        continue

                    signatures.add(sig)
                    raw_structures.add(raw_key)
                    loop_skeleton_counts[skeleton_key] = loop_skeleton_counts.get(skeleton_key, 0) + 1
                    idx = existing_max_idx + len(accepted_records) + 1
                    (raw_dir / f"{idx}.c").write_text(result["raw_code"], encoding="utf-8")
                    (ann_dir / f"{idx}.c").write_text(result["annotated"], encoding="utf-8")

                    accepted_records.append(
                        {
                            "id": f"loop_factory_{idx}",
                            "attempt": attempt,
                            "seed": result["seed"],
                            "model": result["model"],
                            "system_prompt": result["system_prompt"],
                            "user_prompt": result["user_prompt"],
                            "raw_model_output": result["raw_model_output"],
                            "prompt_count": result.get("prompt_count", 0),
                            "raw_c": result["raw_code"],
                            "annotated_c": result["annotated"],
                            "invariants": result["invariants"],
                            "signature": sig,
                            "raw_structure_key": raw_key,
                            "first_pass": result["first_pass"],
                            "token_stats": result["token_stats"],
                            "loop_factory_hyperparams": result["loop_factory_hyperparams"],
                            "augmentation": {"type": "none"},
                        }
                    )
                    api_item = {
                        "instruction": result["system_prompt"],
                        "input": result["user_prompt"],
                        "output": result["annotated"],
                    }
                    api_jsonl_file.write(json.dumps(api_item, ensure_ascii=False) + "\n")
                    api_jsonl_file.flush()

    # Clean up temp directories from this run and any previous incomplete runs.
    for pat in [f"loop_factory_batch_tmp_{run_tag}_*", "loop_factory_batch_tmp_*"]:
        for parent in ["input", "output", "loop", "unfold", "outer"]:
            for d in sorted(SRC.joinpath(parent).glob(pat)):
                if d.is_dir():
                    shutil.rmtree(d, ignore_errors=True)
    if VST_GOAL.exists():
        for p in VST_GOAL.glob(f"loop_factory_batch_tmp_{run_tag}_*_1_*.v"):
            try:
                p.unlink()
            except OSError:
                pass
    if tmp_loops.exists():
        shutil.rmtree(tmp_loops, ignore_errors=True)

    total = existing_count + len(accepted_records)
    reject_path = logs_dir / "reject_log.json"
    reject_path.write_text(json.dumps(reject_log, ensure_ascii=False, indent=2), encoding="utf-8")
    attempted = total_candidates
    accept_rate = (len(accepted_records) / attempted * 100.0) if attempted > 0 else 0.0
    print(
        f"Done: attempted={attempted}, accepted={len(accepted_records)} ({accept_rate:.1f}%), "
        f"new={len(accepted_records)}, existing={existing_count}, total={total}"
    )
    print(f"JSONL (instruction/input/output): {api_jsonl_path}")
    print(f"Reject log: {reject_path}")


if __name__ == "__main__":
    main()
