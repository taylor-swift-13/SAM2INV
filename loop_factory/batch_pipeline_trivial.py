#!/usr/bin/env python3
"""
Trivial batch pipeline: generate loops, call LLM, write every raw model
response directly to SFT JSONL with no verification or filtering.

Format: {"instruction": <system_prompt>, "input": <user_prompt>, "output": <raw_response>}
"""
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

USER_CFG = getattr(config, "LOOP_FACTORY_USER_CONFIG", {})


def _lf_cfg(name: str, default):
    if name in USER_CFG:
        return USER_CFG[name]
    legacy = f"lf_{name}"
    return USER_CFG.get(legacy, default)


def make_logger(log_path: Path) -> logging.Logger:
    logger = logging.getLogger(f"batch_pipeline_trivial_{log_path.stem}")
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
    src_c_path: Path | None = None,
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
        if src_c_path is not None:
            raw_code = src_c_path.read_text(encoding="utf-8")
        else:
            src_c = generate_one_loop(attempt_tmp_loops, seed, lf_overrides)
            raw_code = src_c.read_text(encoding="utf-8")
        if not has_no_assert(raw_code):
            return {"ok": False, "reason": "input has assert", "attempt": attempt, "seed": seed}

        file_id = "1"
        goal_prefix = f"{src_input_dir.name}_{file_id}"
        (src_input_dir / f"{file_id}.c").write_text(raw_code, encoding="utf-8")

        logger = make_logger(logs_dir / f"attempt_{attempt}.log")
        local_cfg = LLMConfig()
        local_cfg.api_model = llm_cfg.api_model
        local_cfg.api_key = llm_cfg.api_key
        local_cfg.base_url = llm_cfg.base_url
        local_cfg.api_base_urls = llm_cfg.api_base_urls
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

        # Capture every (prompt, response) pair produced by LLM calls.
        pairs: List[Tuple[str, str]] = []
        original_chat = gen.llm.chat

        def chat_capture(user_input: str) -> str:
            if stop_event.is_set():
                raise RuntimeError("cancelled")
            resp = original_chat(user_input)
            prompt = (user_input or "").strip()
            response = (resp or "").strip()
            if prompt and response:
                pairs.append((prompt, response))
            return resp

        gen.llm.chat = chat_capture  # type: ignore[assignment]

        gen.generate_all(max_iterations=1)

        if not pairs:
            return {"ok": False, "reason": "no LLM calls captured", "attempt": attempt, "seed": seed}

        return {
            "ok": True,
            "attempt": attempt,
            "seed": seed,
            "raw_code": raw_code,
            "pairs": pairs,
            "model": model_name,
            "system_prompt": system_prompt,
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
    parser = argparse.ArgumentParser(
        description="Trivial batch pipeline: raw model output -> SFT JSONL, no verification."
    )
    parser.add_argument("--target-count", type=int, default=int(USER_CFG.get("target_count", 100)),
                        help="Total generation attempts to run.")
    parser.add_argument("--max-attempts", type=int, default=int(USER_CFG.get("max_attempts", 1200)),
                        help="Max generation attempts before stop.")
    parser.add_argument("--seed", type=int, default=int(USER_CFG.get("seed", 2026)), help="Base random seed.")
    parser.add_argument("--workers", type=int, default=int(USER_CFG.get("workers", 20)),
                        help="Number of concurrent workers.")
    parser.add_argument("--model", type=str, default=LLMConfig().api_model,
                        help="LLM model name (default from src/config.py LLMConfig.api_model).")
    parser.add_argument("--append", action=argparse.BooleanOptionalAction,
                        default=bool(USER_CFG.get("append", True)),
                        help="Append to existing work-dir data (default: true).")
    parser.add_argument("--work-dir", type=str, default=str(USER_CFG.get("work_dir", "")),
                        help="Optional work dir under loop_factory/generated.")
    parser.add_argument("--num-candidates", type=int, default=10,
                        help="Number of LLM candidates per loop (each becomes one SFT item, default: 10).")
    parser.add_argument("--max-vars", "--lf-max-vars", dest="max_vars", type=int,
                        default=int(_lf_cfg("max_vars", 6)))
    parser.add_argument("--params", "--lf-params", dest="params", type=int,
                        default=int(_lf_cfg("params", 2)))
    parser.add_argument("--min-loops", "--lf-min-loops", dest="min_loops", type=int,
                        default=int(_lf_cfg("min_loops", 1)))
    parser.add_argument("--max-loops", "--lf-max-loops", dest="max_loops", type=int,
                        default=int(_lf_cfg("max_loops", 1)))
    parser.add_argument("--max-assign", "--lf-max-assign", dest="max_assign", type=int,
                        default=int(_lf_cfg("max_assign", 6)))
    parser.add_argument("--max-ifelse", "--lf-max-ifelse", dest="max_ifelse", type=int,
                        default=int(_lf_cfg("max_ifelse", 3)))
    parser.add_argument("--max-depth", "--lf-max-depth", dest="max_depth", type=int,
                        default=int(_lf_cfg("max_depth", 1)))
    parser.add_argument("--p-multi", "--lf-p-multi", dest="p_multi", type=float,
                        default=float(_lf_cfg("p_multi", 0.0)))
    parser.add_argument("--q-nest", "--lf-q-nest", dest="q_nest", type=float,
                        default=float(_lf_cfg("q_nest", 0.0)))
    parser.add_argument("--p-nonlinear", "--lf-p-nonlinear", dest="p_nonlinear", type=float,
                        default=float(_lf_cfg("p_nonlinear", 0.75)))
    parser.add_argument("--p-semantic-core", "--lf-p-semantic-core", dest="p_semantic_core", type=float,
                        default=float(_lf_cfg("p_semantic_core", 0.88)))
    parser.add_argument("--input-dir", type=str, default="",
                        help="Read .c files from this directory instead of generating with loop_factory.")
    args = parser.parse_args()

    os.chdir(SRC)

    work_root = ROOT / "generated" / (args.work_dir if args.work_dir else "trivial_batch")
    raw_dir = work_root / "raw"
    ann_dir = work_root / "annotated"
    tmp_loops = work_root / "tmp_loops"
    logs_dir = work_root / "logs"
    for d in [raw_dir, ann_dir, tmp_loops, logs_dir]:
        d.mkdir(parents=True, exist_ok=True)

    # Disable all verification/filtering.
    config.PARALLEL_GENERATION_CONFIG["num_candidates"] = args.num_candidates
    config.PARALLEL_GENERATION_CONFIG["use_threading"] = False
    config.PARALLEL_GENERATION_CONFIG["max_workers"] = 1
    config.PARALLEL_GENERATION_CONFIG["temperature"] = 1.0
    config.SYNTAX_FILTER_CONFIG["enabled"] = False
    config.PARALLEL_GENERATION_CONFIG["filter_by_sampling"] = False
    config.PARALLEL_GENERATION_CONFIG["use_houdini"] = False
    invgen_mod.USE_TRACES = False

    llm_cfg = LLMConfig()
    llm_cfg.api_model = args.model
    system_prompt = (SRC / "prompts" / "system_prompt.txt").read_text(encoding="utf-8")
    sft_jsonl_path = work_root / "llama_factory_train_sft.jsonl"

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

    input_files: List[Path] | None = None
    if args.input_dir:
        input_dir_path = Path(args.input_dir)
        input_files = sorted(
            input_dir_path.glob("*.c"),
            key=lambda p: (int(p.stem) if p.stem.isdigit() else p.stem),
        )

    existing_max_idx = 0
    if args.append:
        existing_raw_files = sorted(raw_dir.glob("*.c"), key=lambda p: int(p.stem))
        existing_max_idx = max((int(p.stem) for p in existing_raw_files), default=0)

    total_candidates = max(0, args.target_count)
    if args.max_attempts > 0:
        total_candidates = min(total_candidates, args.max_attempts)

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
    if input_files is not None:
        total_candidates = min(total_candidates, max(0, len(input_files) - seed_offset))
    next_attempt = 1
    pending: Dict[concurrent.futures.Future, Tuple[int, int]] = {}
    stop_event = threading.Event()
    sft_count = 0
    raw_file_idx = existing_max_idx

    file_mode = "a" if args.append else "w"
    with sft_jsonl_path.open(file_mode, encoding="utf-8") as sft_file:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            while next_attempt <= total_candidates or pending:
                while next_attempt <= total_candidates and len(pending) < workers:
                    attempt = next_attempt
                    next_attempt += 1
                    seed = args.seed + seed_offset + (attempt - 1)
                    _src_c_path: Path | None = None
                    if input_files is not None:
                        _src_c_path = input_files[seed_offset + attempt - 1]
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
                        _src_c_path,
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
                        reject_log.append({
                            "attempt": result.get("attempt", attempt),
                            "seed": result.get("seed", seed),
                            "reason": result.get("reason", "unknown"),
                        })
                        continue

                    pairs: List[Tuple[str, str]] = result["pairs"]
                    raw_file_idx += 1
                    (raw_dir / f"{raw_file_idx}.c").write_text(result["raw_code"], encoding="utf-8")
                    # Save first response as annotated for reference.
                    (ann_dir / f"{raw_file_idx}.c").write_text(pairs[0][1], encoding="utf-8")

                    for prompt, response in pairs:
                        sft_item = {
                            "instruction": result["system_prompt"],
                            "input": prompt,
                            "output": response,
                        }
                        sft_file.write(json.dumps(sft_item, ensure_ascii=False) + "\n")
                        sft_count += 1
                    sft_file.flush()

    cleanup_transient_artifacts(run_tag)
    if tmp_loops.exists():
        shutil.rmtree(tmp_loops, ignore_errors=True)

    reject_path = logs_dir / "reject_log.json"
    reject_path.write_text(json.dumps(reject_log, ensure_ascii=False, indent=2), encoding="utf-8")
    raw_written = raw_file_idx - existing_max_idx
    print(f"Done: attempted={total_candidates}, raw_files={raw_written}, sft_items={sft_count}")
    print(f"JSONL SFT (no verification): {sft_jsonl_path}")
    print(f"Reject log: {reject_path}")


if __name__ == "__main__":
    main()
