#!/usr/bin/env python3
from __future__ import annotations

import json
import logging
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
PROMPTS_DIR = SRC / "prompts"

sys.path.insert(0, str(SRC))

import config  # type: ignore
import inv_generator as invgen_mod  # type: ignore
from inv_generator import InvariantGenerator  # type: ignore
from llm import LLMConfig, reset_token_stats, get_token_stats  # type: ignore


def make_logger(name: str, log_file: Path) -> logging.Logger:
    logger = logging.getLogger(name)
    logger.setLevel(logging.INFO)
    logger.handlers.clear()
    fh = logging.FileHandler(log_file, mode="w", encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s - %(levelname)s - %(message)s"))
    logger.addHandler(fh)
    return logger


def generate_loops(loop_count: int, seed: int, out_dir: Path) -> None:
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
        str(loop_count),
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


def normalize_for_frama(code: str) -> str:
    # Ensure there is an assertion target for Frama-C pipeline.
    if "/*@ assert" not in code:
        idx = code.rfind("}")
        if idx != -1:
            code = code[:idx] + "\n  /*@ assert 1; */\n" + code[idx:]
    return code


def prepare_input_subdir(gen_dir: Path, subdir: str) -> List[str]:
    input_dir = SRC / "input" / subdir
    if input_dir.exists():
        shutil.rmtree(input_dir)
    input_dir.mkdir(parents=True, exist_ok=True)

    file_ids: List[str] = []
    for src_file in sorted(gen_dir.glob("*.c"), key=lambda p: int(p.stem)):
        code = src_file.read_text(encoding="utf-8")
        norm = normalize_for_frama(code)
        dst = input_dir / src_file.name
        dst.write_text(norm, encoding="utf-8")
        file_ids.append(src_file.stem)
    return file_ids


def configure_for_prompt(prompt_name: str) -> None:
    config.PARALLEL_DIVERSITY_CONFIG["random_prompt"] = False
    config.PARALLEL_DIVERSITY_CONFIG["default_prompt"] = prompt_name
    config.PARALLEL_DIVERSITY_CONFIG["random_model"] = False

    # Reduce cost/time while keeping full verification flow.
    config.PARALLEL_GENERATION_CONFIG["num_candidates"] = 1
    config.PARALLEL_GENERATION_CONFIG["use_threading"] = False
    config.PARALLEL_GENERATION_CONFIG["max_workers"] = 1
    config.PARALLEL_GENERATION_CONFIG["temperature"] = 0.2

    # Use static analysis path to reduce runtime variance.
    invgen_mod.USE_TRACES = False


def build_prompt_input(gen: InvariantGenerator, prompt_name: str) -> str:
    if not gen.sampler.records:
        return ""

    rec = gen.template_gen.process_records(gen.sampler.records)[0]
    loop_idx = rec.get("loop_idx", 0)
    prompt_template_base, loop_context = gen._prepare_prompt(rec, loop_idx)

    prompt_path = PROMPTS_DIR / f"{prompt_name}.txt"
    selected_template = prompt_path.read_text(encoding="utf-8") if prompt_path.exists() else prompt_template_base

    template_code = gen.template_gen.generate_template(rec)
    original_code = gen._get_full_source_code()
    code_with_template = gen._replace_loop_content(original_code, template_code, loop_idx)

    cache_reference = gen._format_cache_reference()
    if "{{cache_reference}}" in selected_template:
        selected_template = selected_template.replace("{{cache_reference}}", cache_reference)

    if "{{pre_cond}}" in selected_template:
        prompt = selected_template.replace("{{pre_cond}}", loop_context).replace("{{content}}", code_with_template)
    else:
        prompt = selected_template.replace("{{content}}", code_with_template)
        if cache_reference and "{{cache_reference}}" not in selected_template:
            prompt = prompt.replace("```c", f"{cache_reference}\n\n```c", 1)
    return prompt


def run_one(file_id: str, subdir: str, prompt_name: str, model: str, out_dir: Path, log_dir: Path) -> Dict:
    llm_cfg = LLMConfig()
    llm_cfg.api_model = model

    reset_token_stats()
    logger = make_logger(f"sft_{prompt_name}_{file_id}", log_dir / f"{file_id}.log")
    gen = InvariantGenerator(file_id, llm_config=llm_cfg, logger=logger, output_dir=str(out_dir), input_subdir=subdir)
    final_code = gen.generate_all(max_iterations=1)
    gen.save_results(str(out_dir))

    first_pass = gen.first_pass or {}
    syntax_ok = first_pass.get("syntax") is not None
    valid_ok = first_pass.get("valid") is not None
    satisfy_ok = first_pass.get("satisfy") is not None

    output_file = out_dir / f"{file_id}.c"
    output_code = output_file.read_text(encoding="utf-8") if output_file.exists() else (final_code or "")

    prompt_input = build_prompt_input(gen, prompt_name)
    tokens = get_token_stats()

    return {
        "file": file_id,
        "prompt": prompt_name,
        "model": model,
        "syntax": syntax_ok,
        "valid": valid_ok,
        "satisfy": satisfy_ok,
        "first_pass": first_pass,
        "token_stats": tokens,
        "prompt_input": prompt_input,
        "output_code": output_code,
    }


def choose_best_prompt(prompt_names: List[str], eval_files: List[str], subdir: str, model: str, work_root: Path) -> Tuple[str, Dict[str, Dict[str, int]]]:
    stats: Dict[str, Dict[str, int]] = {}

    for p in prompt_names:
        configure_for_prompt(p)
        p_out = work_root / "prompt_eval" / p / "output"
        p_log = work_root / "prompt_eval" / p / "log"
        p_out.mkdir(parents=True, exist_ok=True)
        p_log.mkdir(parents=True, exist_ok=True)

        s = {"syntax": 0, "valid": 0, "satisfy": 0}
        for fid in eval_files:
            r = run_one(fid, subdir, p, model, p_out, p_log)
            s["syntax"] += int(r["syntax"])
            s["valid"] += int(r["valid"])
            s["satisfy"] += int(r["satisfy"])
        stats[p] = s

    best = sorted(prompt_names, key=lambda p: (stats[p]["satisfy"], stats[p]["valid"], stats[p]["syntax"], p), reverse=True)[0]
    return best, stats


def main() -> None:
    model = "gpt-5"
    subdir = "sft_gen"
    prompt_names = ["standard", "simple", "minimal", "detailed", "experiment"]

    work_root = ROOT / "generated" / "sft_pipeline"
    loops_dir = work_root / "loops"
    work_root.mkdir(parents=True, exist_ok=True)

    # 1) Generate 10 loops
    generate_loops(loop_count=10, seed=2026, out_dir=loops_dir)
    file_ids = prepare_input_subdir(loops_dir, subdir)

    # 2) Prompt selection on first 3 files
    eval_files = file_ids[:3]
    best_prompt, prompt_stats = choose_best_prompt(prompt_names, eval_files, subdir, model, work_root)

    # 3) Solve all 10 with best prompt and keep Frama-C fully passed pairs
    configure_for_prompt(best_prompt)
    final_out = work_root / "final" / "output"
    final_log = work_root / "final" / "log"
    final_out.mkdir(parents=True, exist_ok=True)
    final_log.mkdir(parents=True, exist_ok=True)

    results: List[Dict] = []
    passed_pairs: List[Dict] = []

    for fid in file_ids:
        r = run_one(fid, subdir, best_prompt, model, final_out, final_log)
        results.append(r)
        if r["satisfy"]:
            passed_pairs.append(
                {
                    "id": f"sft_{fid}",
                    "file": f"{fid}.c",
                    "model": model,
                    "prompt_name": best_prompt,
                    "input": r["prompt_input"],
                    "output": r["output_code"],
                }
            )

    # 4) Save dataset and report
    dataset_path = work_root / "sft_pairs.jsonl"
    with dataset_path.open("w", encoding="utf-8") as f:
        for item in passed_pairs:
            f.write(json.dumps(item, ensure_ascii=False) + "\n")

    report = {
        "model": model,
        "best_prompt": best_prompt,
        "prompt_stats_on_eval_files": prompt_stats,
        "num_total": len(file_ids),
        "num_passed": len(passed_pairs),
        "passed_files": [x["file"] for x in passed_pairs],
        "dataset_path": str(dataset_path),
    }
    report_path = work_root / "report.json"
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")

    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
