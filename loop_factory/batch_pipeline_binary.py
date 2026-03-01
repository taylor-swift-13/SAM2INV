#!/usr/bin/env python3
from __future__ import annotations

import argparse
import atexit
import concurrent.futures
import json
import logging
import os
import shutil
import signal
import subprocess
import sys
import threading
import tempfile
import time
from pathlib import Path
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
VST_GOAL = (ROOT / "../VST/goal").resolve()
sys.path.insert(0, str(SRC))

import config  # type: ignore
import inv_generator as invgen_mod  # type: ignore
from config import LLMConfig  # type: ignore
from inv_generator import InvariantGenerator  # type: ignore
from llm import get_token_stats, reset_token_stats  # type: ignore
from output_verify import OutputVerifier  # type: ignore

USER_CFG = getattr(config, "LOOP_FACTORY_USER_CONFIG", {})


def _lf_cfg(name: str, default):
    if name in USER_CFG:
        return USER_CFG[name]
    legacy = f"lf_{name}"
    return USER_CFG.get(legacy, default)


def make_logger(log_path: Path) -> logging.Logger:
    logger = logging.getLogger(f"batch_pipeline_binary_{log_path.stem}")
    logger.setLevel(logging.INFO)
    logger.handlers.clear()
    fh = logging.FileHandler(log_path, mode="w", encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s - %(levelname)s - %(message)s"))
    logger.addHandler(fh)
    return logger


def cleanup_transient_artifacts(run_tag: str | None = None) -> None:
    patterns: List[str] = []
    if run_tag:
        patterns.append(f"loop_factory_batch_tmp_{run_tag}_*")
    patterns.append("loop_factory_batch_tmp_*")

    for pat in patterns:
        for parent in ["input", "output", "loop", "unfold", "outer"]:
            for d in sorted(SRC.joinpath(parent).glob(pat)):
                if d.is_dir():
                    shutil.rmtree(d, ignore_errors=True)

    if VST_GOAL.exists():
        for pat in patterns:
            for p in VST_GOAL.glob(f"{pat}_1_*.v"):
                try:
                    p.unlink()
                except OSError:
                    pass


def has_no_assert(code: str) -> bool:
    return "/*@ assert" not in code


def loop_factory_hyperparams(seed: int, out_dir: Path, overrides: Dict[str, object] | None = None) -> Dict[str, object]:
    hp = {
        "profile": "benchmark",
        "out_dir": str(out_dir),
        "count": 1,
        "seed": seed,
        "max_vars": 6,
        "params": 2,
        "min_loops": 1,
        "max_loops": 1,
        "max_assign": 6,
        "max_ifelse": 3,
        "max_depth": 1,
        "p_multi": 0.0,
        "q_nest": 0.0,
        "p_nonlinear": 0.75,
        "nonlinear_strength": 0.82,
        "p_semantic_core": 0.88,
    }
    if overrides:
        for k, v in overrides.items():
            if v is not None and k in hp:
                hp[k] = v
    return hp


def generate_one_loop(out_dir: Path, seed: int, lf_overrides: Dict[str, object]) -> Path:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    hp = loop_factory_hyperparams(seed, out_dir, lf_overrides)
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
    ]
    subprocess.run(cmd, check=True)
    c_files = sorted(out_dir.glob("*.c"), key=lambda p: int(p.stem))
    if not c_files:
        raise RuntimeError("loop_factory did not generate any .c")
    return c_files[0]


def _to_label_by_verify(verifier: OutputVerifier) -> int:
    syntax_ok = bool(getattr(verifier, "syntax_correct", False)) or verifier.syntax_error == "syntax Correct"
    valid_ok = bool(verifier.validate_result) and all(verifier.validate_result)
    return 1 if (syntax_ok and valid_ok) else 0


def _collect_rejected_codes(loop_dpo_records: Dict) -> List[str]:
    rejected: List[str] = []
    seen = set()
    for _, loop_rec in sorted(loop_dpo_records.items()):
        pre_dedup_code = (loop_rec.get("pre_dedup_code", "") or "").strip()
        if pre_dedup_code and pre_dedup_code not in seen:
            seen.add(pre_dedup_code)
            rejected.append(pre_dedup_code)
        for rej in loop_rec.get("rejected_items", []):
            rej_code = (rej.get("code", "") or "").strip()
            if rej_code and rej_code not in seen:
                seen.add(rej_code)
                rejected.append(rej_code)
    return rejected


def _collect_candidate_codes(final_code: str, loop_dpo_records: Dict) -> List[str]:
    codes: List[str] = []
    seen = set()

    def _add(code: str) -> None:
        c = (code or "").strip()
        if not c or c in seen:
            return
        seen.add(c)
        codes.append(c)

    _add(final_code)
    for _, loop_rec in sorted(loop_dpo_records.items()):
        _add(loop_rec.get("chosen_code", "") or "")
        _add(loop_rec.get("pre_dedup_code", "") or "")
        for rej in loop_rec.get("rejected_items", []):
            _add((rej.get("code", "") or ""))
    return codes


def _label_candidates(codes: List[str], logger: logging.Logger) -> Tuple[List[str], List[str]]:
    positives: List[str] = []
    negatives: List[str] = []
    for code in codes:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".c", delete=False, encoding="utf-8") as tf:
            tf.write(code)
            temp_path = tf.name
        try:
            verifier = OutputVerifier(logger=logger, output=False)
            verifier.run(temp_path)
            label = _to_label_by_verify(verifier)
            if label == 1:
                positives.append(code)
            else:
                negatives.append(code)
        finally:
            try:
                os.remove(temp_path)
            except OSError:
                pass
    return positives, negatives


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
    lf_overrides: Dict[str, object],
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
        src_c = generate_one_loop(attempt_tmp_loops, seed, lf_overrides)
        raw_code = src_c.read_text(encoding="utf-8")
        if not has_no_assert(raw_code):
            return {"ok": False, "reason": "input has assert", "attempt": attempt, "seed": seed}

        file_id = "1"
        goal_prefix = f"{src_input_dir.name}_{file_id}"
        input_c = src_input_dir / f"{file_id}.c"
        input_c.write_text(raw_code, encoding="utf-8")

        reset_token_stats()
        logger = make_logger(logs_dir / f"attempt_{attempt}.log")
        local_cfg = LLMConfig()
        local_cfg.api_model = llm_cfg.api_model
        local_cfg.api_key = llm_cfg.api_key
        local_cfg.base_url = llm_cfg.base_url
        local_cfg.use_api_model = llm_cfg.use_api_model
        local_cfg.api_temperature = llm_cfg.api_temperature
        local_cfg.api_top_p = llm_cfg.api_top_p
        local_cfg.think_mode_enabled = llm_cfg.think_mode_enabled
        local_cfg.local_model_path = llm_cfg.local_model_path
        local_cfg.local_max_new_tokens = llm_cfg.local_max_new_tokens
        local_cfg.local_temperature = llm_cfg.local_temperature
        local_cfg.local_top_p = llm_cfg.local_top_p

        gen = InvariantGenerator(
            file_id,
            llm_config=local_cfg,
            logger=logger,
            output_dir=str(src_output_dir),
            input_subdir=src_input_dir.name,
        )

        captured = {
            "user_prompt": "",
            "raw_response": "",
            "prompt_count": 0,
            "all_prompts": [],
            "all_responses": [],
        }
        original_chat = gen.llm.chat
        original_select_prompt = getattr(gen, "_select_prompt_for_candidate", None)

        def chat_capture(user_input: str) -> str:
            if stop_event.is_set():
                raise RuntimeError("cancelled")
            captured["prompt_count"] += 1
            if isinstance(user_input, str) and user_input.strip():
                captured["all_prompts"].append(user_input)
            resp = original_chat(user_input)
            if isinstance(resp, str) and resp.strip():
                captured["all_responses"].append(resp)
            if not captured["user_prompt"] and isinstance(user_input, str) and user_input.strip():
                captured["user_prompt"] = user_input
            if not captured["raw_response"] and isinstance(resp, str) and resp.strip():
                captured["raw_response"] = resp
            return resp

        gen.llm.chat = chat_capture  # type: ignore[assignment]
        if callable(original_select_prompt):
            def select_prompt_capture(candidate_idx: int, loop_context: str, code_with_template: str):
                prompt, prompt_name = original_select_prompt(candidate_idx, loop_context, code_with_template)
                if isinstance(prompt, str) and prompt.strip():
                    captured["all_prompts"].append(prompt)
                    if not captured["user_prompt"]:
                        captured["user_prompt"] = prompt
                return prompt, prompt_name
            gen._select_prompt_for_candidate = select_prompt_capture  # type: ignore[assignment]

        final_code = gen.generate_all(max_iterations=1)
        gen.save_results(str(src_output_dir))
        first_pass = gen.first_pass or {}

        out_c = src_output_dir / f"{file_id}.c"
        annotated = out_c.read_text(encoding="utf-8") if out_c.exists() else (final_code or "")
        annotated = annotated or ""
        loop_dpo_records = getattr(gen, "loop_dpo_records", {})
        candidate_pool = _collect_candidate_codes(annotated, loop_dpo_records)
        if not candidate_pool:
            return {"ok": False, "reason": "empty output", "attempt": attempt, "seed": seed}
        positives, negatives = _label_candidates(candidate_pool, logger)

        return {
            "ok": True,
            "attempt": attempt,
            "seed": seed,
            "raw_code": raw_code,
            "annotated": annotated,
            "first_pass": first_pass,
            "token_stats": get_token_stats(),
            "user_prompt": captured["user_prompt"],
            "raw_model_output": captured["raw_response"],
            "prompt_count": captured["prompt_count"],
            "all_prompts": captured["all_prompts"],
            "model": model_name,
            "system_prompt": system_prompt,
            "loop_factory_hyperparams": loop_factory_hyperparams(seed, attempt_tmp_loops, lf_overrides),
            "positives": positives,
            "negatives": negatives,
            "candidate_count": len(candidate_pool),
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
        subdir_name = src_input_dir.name
        for parent in ["loop", "unfold", "outer"]:
            side_dir = SRC / parent / subdir_name
            if side_dir.exists():
                shutil.rmtree(side_dir, ignore_errors=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Batch 0/1 sampling pipeline (syntax+valid as label=1).")
    parser.add_argument("--target-count", type=int, default=int(USER_CFG.get("target_count", 100)), help="Total candidate attempts to run.")
    parser.add_argument("--aug-per-sample", type=int, default=0, help="(Deprecated, unused) Augmented copies per accepted sample.")
    parser.add_argument("--max-attempts", type=int, default=int(USER_CFG.get("max_attempts", 1200)), help="Max generation attempts before stop.")
    parser.add_argument("--seed", type=int, default=int(USER_CFG.get("seed", 2026)), help="Base random seed.")
    parser.add_argument("--workers", type=int, default=int(USER_CFG.get("workers", 20)), help="Number of concurrent workers.")
    parser.add_argument(
        "--model",
        type=str,
        default=LLMConfig().api_model,
        help="LLM model name for invariant generation (default from src/config.py LLMConfig.api_model).",
    )
    parser.add_argument("--max-skeleton-repeat", type=int, default=int(USER_CFG.get("max_skeleton_repeat", 3)), help="(Kept for CLI compatibility, unused).")
    parser.add_argument(
        "--append",
        action=argparse.BooleanOptionalAction,
        default=bool(USER_CFG.get("append", True)),
        help="Append to existing work-dir data (default: true).",
    )
    parser.add_argument("--work-dir", type=str, default=str(USER_CFG.get("work_dir", "")), help="Optional work dir under loop_factory/generated.")
    parser.add_argument("--max-vars", "--lf-max-vars", dest="max_vars", type=int, default=int(_lf_cfg("max_vars", 6)), help="Loop-factory max variable count.")
    parser.add_argument("--params", "--lf-params", dest="params", type=int, default=int(_lf_cfg("params", 2)), help="Loop-factory parameter count.")
    parser.add_argument("--min-loops", "--lf-min-loops", dest="min_loops", type=int, default=int(_lf_cfg("min_loops", 1)), help="Loop-factory min loop count.")
    parser.add_argument("--max-loops", "--lf-max-loops", dest="max_loops", type=int, default=int(_lf_cfg("max_loops", 1)), help="Loop-factory max loop count.")
    parser.add_argument("--max-assign", "--lf-max-assign", dest="max_assign", type=int, default=int(_lf_cfg("max_assign", 6)), help="Loop-factory max assignments per loop.")
    parser.add_argument("--max-ifelse", "--lf-max-ifelse", dest="max_ifelse", type=int, default=int(_lf_cfg("max_ifelse", 3)), help="Loop-factory max if/else blocks per loop.")
    parser.add_argument("--max-depth", "--lf-max-depth", dest="max_depth", type=int, default=int(_lf_cfg("max_depth", 1)), help="Loop-factory max loop nesting depth.")
    parser.add_argument("--p-multi", "--lf-p-multi", dest="p_multi", type=float, default=float(_lf_cfg("p_multi", 0.0)), help="Loop-factory p_multi.")
    parser.add_argument("--q-nest", "--lf-q-nest", dest="q_nest", type=float, default=float(_lf_cfg("q_nest", 0.0)), help="Loop-factory q_nest.")
    parser.add_argument("--p-nonlinear", "--lf-p-nonlinear", dest="p_nonlinear", type=float, default=float(_lf_cfg("p_nonlinear", 0.75)), help="Loop-factory nonlinear family probability.")
    parser.add_argument("--p-semantic-core", "--lf-p-semantic-core", dest="p_semantic_core", type=float, default=float(_lf_cfg("p_semantic_core", 0.88)), help="Loop-factory semantic core probability.")
    args = parser.parse_args()

    os.chdir(SRC)

    work_root = ROOT / "generated" / (args.work_dir if args.work_dir else "hq_batch_100_binary")
    raw_dir = work_root / "raw"
    ann_dir = work_root / "annotated"
    tmp_loops = work_root / "tmp_loops"
    logs_dir = work_root / "logs"
    for d in [raw_dir, ann_dir, tmp_loops, logs_dir]:
        d.mkdir(parents=True, exist_ok=True)

    config.PARALLEL_GENERATION_CONFIG["num_candidates"] = 10
    config.PARALLEL_GENERATION_CONFIG["use_threading"] = False
    config.PARALLEL_GENERATION_CONFIG["max_workers"] = 1
    config.PARALLEL_GENERATION_CONFIG["temperature"] = 1.0
    # Hard-coded filtering policy for batch_pipeline_binary: all disabled.
    config.SYNTAX_FILTER_CONFIG["enabled"] = False
    config.PARALLEL_GENERATION_CONFIG["filter_by_sampling"] = False
    config.PARALLEL_GENERATION_CONFIG["use_houdini"] = False
    invgen_mod.USE_TRACES = False

    llm_cfg = LLMConfig()
    llm_cfg.api_model = args.model
    system_prompt = (SRC / "prompts" / "system_prompt.txt").read_text(encoding="utf-8")
    api_jsonl_path = work_root / "llama_factory_train_iio_api_aligned.jsonl"
    dpo_jsonl_path = work_root / "llama_factory_train_dpo.jsonl"

    lf_overrides: Dict[str, object] = {
        "max_vars": args.max_vars,
        "params": args.params,
        "min_loops": args.min_loops,
        "max_loops": args.max_loops,
        "max_assign": args.max_assign,
        "max_ifelse": args.max_ifelse,
        "max_depth": args.max_depth,
        "p_multi": args.p_multi,
        "q_nest": args.q_nest,
        "p_nonlinear": args.p_nonlinear,
        "p_semantic_core": args.p_semantic_core,
    }

    existing_max_idx = 0
    if args.append:
        existing_raw_files = sorted(raw_dir.glob("*.c"), key=lambda p: int(p.stem))
        existing_max_idx = max((int(p.stem) for p in existing_raw_files), default=0)

    total_candidates = max(0, args.target_count)
    if args.max_attempts > 0:
        total_candidates = min(total_candidates, args.max_attempts)

    problem_records: List[Dict] = []
    reject_log: List[Dict] = []
    workers = max(1, args.workers)
    run_tag = f"{os.getpid()}_{int(time.time())}"
    cleanup_transient_artifacts()
    atexit.register(lambda: cleanup_transient_artifacts(run_tag))

    def _cleanup_on_signal(_signum, _frame):
        cleanup_transient_artifacts(run_tag)
        raise SystemExit(1)

    signal.signal(signal.SIGTERM, _cleanup_on_signal)
    signal.signal(signal.SIGINT, _cleanup_on_signal)

    seed_offset = existing_max_idx if args.append else 0
    next_attempt = 1
    pending: Dict[concurrent.futures.Future, Tuple[int, int]] = {}
    stop_event = threading.Event()

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
                    lf_overrides,
                )
                pending[fut] = (attempt, seed)

            if not pending:
                break

            done, _ = concurrent.futures.wait(pending.keys(), return_when=concurrent.futures.FIRST_COMPLETED)
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

                row = {
                    "attempt": result["attempt"],
                    "seed": result["seed"],
                    "instruction": result["system_prompt"],
                    "input": (result["user_prompt"] or "").strip(),
                    "raw_code": (result["raw_code"] or "").strip(),
                    "positives": result.get("positives", []),
                    "negatives": result.get("negatives", []),
                    "candidate_count": int(result.get("candidate_count", 0)),
                }
                if row["positives"] or row["negatives"]:
                    problem_records.append(row)
                else:
                    reject_log.append({"attempt": attempt, "seed": seed, "reason": "empty candidate pool after labeling"})

    file_mode = "a" if args.append else "w"
    with api_jsonl_path.open(file_mode, encoding="utf-8") as api_jsonl_file, dpo_jsonl_path.open(file_mode, encoding="utf-8") as dpo_jsonl_file:
        sample_idx = existing_max_idx
        sft_count = 0
        dpo_written = 0

        for p in problem_records:
            for pos_code in p["positives"]:
                sample_idx += 1
                (raw_dir / f"{sample_idx}.c").write_text(p["raw_code"], encoding="utf-8")
                (ann_dir / f"{sample_idx}.c").write_text(pos_code, encoding="utf-8")
                api_item = {
                    "instruction": p["instruction"],
                    "input": p["input"],
                    "output": pos_code,
                }
                api_jsonl_file.write(json.dumps(api_item, ensure_ascii=False) + "\n")
                sft_count += 1
        api_jsonl_file.flush()

        for p in problem_records:
            for pos_code in p["positives"]:
                for neg_code in p["negatives"]:
                    if not neg_code or neg_code == pos_code:
                        continue
                    dpo_item = {
                        "instruction": p["instruction"],
                        "input": p["input"],
                        "chosen": pos_code,
                        "rejected": neg_code,
                    }
                    dpo_jsonl_file.write(json.dumps(dpo_item, ensure_ascii=False) + "\n")
                    dpo_written += 1
        if dpo_written:
            dpo_jsonl_file.flush()

    cleanup_transient_artifacts(run_tag)
    if tmp_loops.exists():
        shutil.rmtree(tmp_loops, ignore_errors=True)

    reject_path = logs_dir / "reject_log.json"
    reject_path.write_text(json.dumps(reject_log, ensure_ascii=False, indent=2), encoding="utf-8")
    attempted = total_candidates
    ones = sum(len(x["positives"]) for x in problem_records)
    zeros = sum(len(x["negatives"]) for x in problem_records)
    print(
        f"Done: attempted={attempted}, label1={ones}, label0={zeros}, "
        f"label1_rate={(ones / (ones + zeros) * 100.0) if (ones + zeros) else 0.0:.1f}%, "
        f"sft={sft_count}, dpo={dpo_written}"
    )
    print(f"JSONL SFT (all label=1): {api_jsonl_path}")
    print(f"JSONL DPO (label1 vs label0): {dpo_jsonl_path}")
    print(f"Reject log: {reject_path}")


if __name__ == "__main__":
    main()
