#!/usr/bin/env python3
"""
Generate a new DPO JSONL from an existing DPO JSONL.

For each input record:
1) Call model once with (instruction, input).
2) Verify the generated code once with Frama-C (via OutputVerifier).
3) Keep only failed generations in output DPO ("spec") file.
"""
from __future__ import annotations

import json
import logging
import re
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
sys.path.insert(0, str(SRC))

import openai
from config import LLMConfig
from output_verify import OutputVerifier


logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-7s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)


INPUT_FILE = ROOT / "generated/teacher/llama_factory_train_dpo.jsonl"
OUTPUT_FILE = ROOT / "generated/teacher/llama_factory_train_dpo_spec.jsonl"
PROGRESS_FILE = ROOT / "generated/teacher/.dpo_spec_progress.json"
TMP_VERIFY_DIR = ROOT / "generated/teacher/.tmp_dpo_spec_verify"

MAX_WORKERS = 8
MAX_RETRIES = 3
RETRY_DELAY = 5.0

_cfg = LLMConfig()
_client = openai.OpenAI(base_url=_cfg.base_url, api_key=_cfg.api_key)

log.info("Model : %s", _cfg.api_model)
log.info("URL   : %s", _cfg.base_url)
log.info("Temp  : %s  top_p: %s  max_tokens: %s",
         _cfg.api_temperature, _cfg.api_top_p, _cfg.api_max_tokens)


def call_once(system_prompt: str, user_msg: str) -> str:
    for attempt in range(MAX_RETRIES):
        try:
            resp = _client.chat.completions.create(
                model=_cfg.api_model,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": user_msg},
                ],
                temperature=_cfg.api_temperature,
                top_p=_cfg.api_top_p,
                max_tokens=_cfg.api_max_tokens,
            )
            return (resp.choices[0].message.content or "").strip()
        except Exception as exc:
            if attempt < MAX_RETRIES - 1:
                log.warning("API error (attempt %d/%d): %s — retry in %.0fs",
                            attempt + 1, MAX_RETRIES, exc, RETRY_DELAY)
                time.sleep(RETRY_DELAY)
            else:
                log.error("API failed after %d attempts: %s", MAX_RETRIES, exc)
                return f"ERROR: {exc}"
    return "ERROR: max retries exceeded"


def load_progress() -> Set[int]:
    if PROGRESS_FILE.exists():
        try:
            data = json.loads(PROGRESS_FILE.read_text(encoding="utf-8"))
            return set(data.get("done", []))
        except Exception:
            pass
    return set()


def save_progress(done: Set[int]) -> None:
    PROGRESS_FILE.write_text(
        json.dumps({"done": sorted(done)}, ensure_ascii=False),
        encoding="utf-8",
    )


def _all_true(items: List[bool]) -> bool:
    return bool(items) and all(items)


def verify_once(code_text: str, tmp_dir: Path) -> Dict[str, Any]:
    tmp_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".c",
        prefix="dpo_spec_",
        dir=str(tmp_dir),
        delete=False,
        encoding="utf-8",
    ) as fp:
        fp.write(code_text or "")
        c_path = Path(fp.name)

    verifier = OutputVerifier(logger=log, output=False)
    try:
        verifier.run(str(c_path))
        syntax_ok = bool(getattr(verifier, "syntax_correct", False) or verifier.syntax_error == "syntax Correct")
        valid_res = list(getattr(verifier, "validate_result", []) or [])
        verify_res = list(getattr(verifier, "verify_result", []) or [])
        valid_ok = _all_true(valid_res)
        # If there is no explicit assertion obligation, treat it as neutral/pass.
        verify_ok = all(verify_res) if verify_res else True
        pass_all = bool(syntax_ok and valid_ok and verify_ok)
        return {
            "pass": pass_all,
            "syntax_ok": syntax_ok,
            "valid_ok": valid_ok,
            "verify_ok": verify_ok,
            "validate_result": valid_res,
            "verify_result": verify_res,
            "syntax_error": getattr(verifier, "syntax_error", ""),
        }
    except Exception as exc:
        return {
            "pass": False,
            "syntax_ok": False,
            "valid_ok": False,
            "verify_ok": False,
            "validate_result": [],
            "verify_result": [],
            "syntax_error": f"verifier exception: {exc}",
        }
    finally:
        try:
            c_path.unlink(missing_ok=True)
        except Exception:
            pass


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Generate DPO spec data")
    parser.add_argument(
        "--enable-cot",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Enable reverse-COT export (default: enabled; use --no-enable-cot to disable).",
    )
    args = parser.parse_args()

    records: List[Dict[str, Any]] = []
    with INPUT_FILE.open(encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                records.append(json.loads(line))
    log.info("Loaded %d records from %s", len(records), INPUT_FILE)

    done_idx = load_progress()
    if done_idx:
        log.info("Resuming: %d / %d records already done", len(done_idx), len(records))

    remaining = [i for i in range(len(records)) if i not in done_idx]
    log.info("Records to process: %d", len(remaining))
    if not remaining:
        log.info("All records already processed. Output: %s", OUTPUT_FILE)
        return

    OUTPUT_FILE.parent.mkdir(parents=True, exist_ok=True)
    TMP_VERIFY_DIR.mkdir(parents=True, exist_ok=True)

    lock = threading.Lock()
    stats = {
        "processed": 0,
        "failed_written": 0,
        "passed_skipped": 0,
    }

    def worker(rec_idx: int) -> Tuple[int, Dict[str, Any], str, Dict[str, Any]]:
        rec = records[rec_idx]
        generated = call_once(rec.get("instruction", ""), rec.get("input", ""))
        verify = verify_once(generated, TMP_VERIFY_DIR)
        return rec_idx, rec, generated, verify

    with OUTPUT_FILE.open("a", encoding="utf-8") as out_fh:
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            future_map = {pool.submit(worker, i): i for i in remaining}
            for fut in as_completed(future_map):
                rec_idx = future_map[fut]
                try:
                    idx, rec, generated, verify = fut.result()
                except Exception as exc:
                    idx = rec_idx
                    rec = records[idx]
                    generated = f"ERROR: worker exception: {exc}"
                    verify = {
                        "pass": False,
                        "syntax_ok": False,
                        "valid_ok": False,
                        "verify_ok": False,
                        "validate_result": [],
                        "verify_result": [],
                        "syntax_error": str(exc),
                    }

                if not verify["pass"]:
                    out_item = {
                        "instruction": rec.get("instruction", ""),
                        "input": rec.get("input", ""),
                        "chosen": rec.get("chosen", ""),
                        "rejected": generated,
                        "error_type": "spec_failed",
                        "verify_meta": {
                            "syntax_ok": verify.get("syntax_ok", False),
                            "valid_ok": verify.get("valid_ok", False),
                            "verify_ok": verify.get("verify_ok", False),
                            "validate_result": verify.get("validate_result", []),
                            "verify_result": verify.get("verify_result", []),
                            "syntax_error": verify.get("syntax_error", ""),
                            "source_error_type": rec.get("error_type", None),
                        },
                    }
                    with lock:
                        out_fh.write(json.dumps(out_item, ensure_ascii=False) + "\n")
                        out_fh.flush()
                        stats["failed_written"] += 1
                else:
                    with lock:
                        stats["passed_skipped"] += 1

                with lock:
                    done_idx.add(idx)
                    save_progress(done_idx)
                    stats["processed"] += 1
                    if stats["processed"] % 20 == 0 or stats["processed"] == len(remaining):
                        log.info(
                            "Progress: %d / %d processed, spec_written=%d, passed_skipped=%d",
                            stats["processed"], len(remaining),
                            stats["failed_written"], stats["passed_skipped"],
                        )

    log.info(
        "Done. processed=%d, spec_written=%d, passed_skipped=%d, output=%s",
        stats["processed"], stats["failed_written"], stats["passed_skipped"], OUTPUT_FILE,
    )

    # ── Phase 2: Reverse-COT ──────────────────────────────────────────────
    if args.enable_cot:
        from reverse_cot import generate_reverse_cot, generate_reverse_cots_batch, prepend_cot, lookup_cot
        import openai as _oai

        cot_system_prompt = (SRC / "prompts" / "system_prompt_cot.txt").read_text(encoding="utf-8")
        cot_model = _cfg.api_model
        cot_client = _oai.OpenAI(base_url=_cfg.base_url, api_key=_cfg.api_key)

        # Read all output records
        all_output_records: List[Dict[str, Any]] = []
        with OUTPUT_FILE.open(encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    all_output_records.append(json.loads(line))

        # Move original output to no_cot/
        no_cot_dir = OUTPUT_FILE.parent / "no_cot"
        cot_dir_path = OUTPUT_FILE.parent / "cot"
        no_cot_dir.mkdir(parents=True, exist_ok=True)
        cot_dir_path.mkdir(parents=True, exist_ok=True)

        import shutil
        no_cot_path = no_cot_dir / OUTPUT_FILE.name
        shutil.copy2(OUTPUT_FILE, no_cot_path)
        log.info("Copied no-COT output to %s", no_cot_path)

        cot_tag_re = re.compile(r"<\s*(think|reasoning)\s*>", re.IGNORECASE)

        def _has_cot(text: str) -> bool:
            return bool(cot_tag_re.search(text or ""))

        # Collect COT tasks for missing-COT chosen/rejected only
        all_cot_tasks: List[Dict] = []
        for rec in all_output_records:
            if not _has_cot(rec.get("chosen", "")):
                all_cot_tasks.append({"system_prompt": rec["instruction"], "user_prompt": rec["input"], "code_output": rec["chosen"]})
            if not _has_cot(rec.get("rejected", "")):
                all_cot_tasks.append({"system_prompt": rec["instruction"], "user_prompt": rec["input"], "code_output": rec["rejected"]})

        log.info("COT Phase: generating reverse-COTs for %d records...", len(all_cot_tasks))
        cot_map = generate_reverse_cots_batch(all_cot_tasks, cot_client, cot_model)
        cot_ok = sum(1 for v in cot_map.values() if v)
        log.info("COT Phase: %d/%d unique COTs generated.", cot_ok, len(cot_map))

        cot_out_path = cot_dir_path / OUTPUT_FILE.name
        out_records: List[Dict[str, Any]] = []
        for rec in all_output_records:
            chosen_text = rec["chosen"]
            rejected_text = rec["rejected"]
            if not _has_cot(chosen_text):
                chosen_cot = lookup_cot(cot_map, rec["input"], chosen_text)
                if not chosen_cot:
                    chosen_cot = generate_reverse_cot(rec["instruction"], rec["input"], chosen_text, cot_client, cot_model)
                if not chosen_cot:
                    raise RuntimeError("Reverse-COT backfill failed: dpo_spec chosen has no COT.")
                chosen_text = prepend_cot(chosen_text, chosen_cot)
            if not _has_cot(rejected_text):
                rejected_cot = lookup_cot(cot_map, rec["input"], rejected_text)
                if not rejected_cot:
                    rejected_cot = generate_reverse_cot(rec["instruction"], rec["input"], rejected_text, cot_client, cot_model)
                if not rejected_cot:
                    raise RuntimeError("Reverse-COT backfill failed: dpo_spec rejected has no COT.")
                rejected_text = prepend_cot(rejected_text, rejected_cot)
            if not _has_cot(chosen_text) or not _has_cot(rejected_text):
                raise RuntimeError("Reverse-COT validation failed: dpo_spec sample has no COT after backfill.")
            out_rec = dict(rec)
            out_rec["instruction"] = cot_system_prompt
            out_rec["chosen"] = chosen_text
            out_rec["rejected"] = rejected_text
            out_records.append(out_rec)

        with cot_out_path.open("w", encoding="utf-8") as f:
            for out_rec in out_records:
                f.write(json.dumps(out_rec, ensure_ascii=False) + "\n")
        log.info("COT output written to %s", cot_out_path)


if __name__ == "__main__":
    main()
