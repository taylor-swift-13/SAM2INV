#!/usr/bin/env python3
"""
Generate distillation data using gpt-5-nano.

For each record in the teacher JSONL, call gpt-5-nano N_PER_RECORD times
independently. Each call produces one output line in the same format as the
original file: {"instruction": "...", "input": "...", "output": "..."}.

Total output: N_records × N_PER_RECORD lines.

Resume: a sidecar file (.progress) tracks which record indices are done.
"""
from __future__ import annotations

import json
import logging
import sys
import threading
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
sys.path.insert(0, str(SRC))

import openai
from config import LLMConfig

# ── Logging ───────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-7s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)

# ── Paths ─────────────────────────────────────────────────────────────────────
INPUT_FILE    = ROOT / "generated/teacher/llama_factory_train_iio_api_aligned.jsonl"
OUTPUT_FILE   = ROOT / "generated/teacher/gpt5nano_distill_10x.jsonl"
PROGRESS_FILE = ROOT / "generated/teacher/.distill_progress.json"

# ── Settings ──────────────────────────────────────────────────────────────────
N_PER_RECORD = 10   # outputs to generate per original record
MAX_WORKERS  = 20   # concurrent API calls
MAX_RETRIES  = 3
RETRY_DELAY  = 5.0  # seconds between retries

# ── API client ────────────────────────────────────────────────────────────────
_cfg    = LLMConfig()
_client = openai.OpenAI(base_url=_cfg.base_url, api_key=_cfg.api_key)

log.info("Model : %s", _cfg.api_model)
log.info("URL   : %s", _cfg.base_url)
log.info("Temp  : %s  top_p: %s  max_tokens: %s",
         _cfg.api_temperature, _cfg.api_top_p, _cfg.api_max_tokens)


# ── Core call ─────────────────────────────────────────────────────────────────
def call_once(system_prompt: str, user_msg: str) -> str:
    """Single stateless chat call with retry."""
    for attempt in range(MAX_RETRIES):
        try:
            resp = _client.chat.completions.create(
                model=_cfg.api_model,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user",   "content": user_msg},
                ],
                temperature=_cfg.api_temperature,
                top_p=_cfg.api_top_p,
                max_tokens=_cfg.api_max_tokens,
                #extra_body={"enable_thinking": False},
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


# ── Progress helpers ──────────────────────────────────────────────────────────
def load_progress() -> set[int]:
    if PROGRESS_FILE.exists():
        try:
            data = json.loads(PROGRESS_FILE.read_text(encoding="utf-8"))
            return set(data.get("done", []))
        except Exception:
            pass
    return set()


def save_progress(done: set[int]) -> None:
    PROGRESS_FILE.write_text(
        json.dumps({"done": sorted(done)}, ensure_ascii=False),
        encoding="utf-8",
    )


# ── Main ──────────────────────────────────────────────────────────────────────
def main() -> None:
    # 1. Load input records
    records: list[dict] = []
    with open(INPUT_FILE, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                records.append(json.loads(line))
    log.info("Loaded %d records from %s", len(records), INPUT_FILE)

    # 2. Resume: which record indices already have all N_PER_RECORD outputs written
    done_idx = load_progress()
    if done_idx:
        log.info("Resuming: %d / %d records already done", len(done_idx), len(records))

    remaining = [i for i in range(len(records)) if i not in done_idx]
    log.info("Records to process: %d  →  %d API calls", len(remaining), len(remaining) * N_PER_RECORD)

    if not remaining:
        log.info("All records already processed. Output: %s", OUTPUT_FILE)
        return

    # 3. Flat task list: (record_idx, sample_idx)
    tasks = [(i, s) for i in remaining for s in range(N_PER_RECORD)]

    # 4. Shared aggregation buffer
    buf: dict[int, list[tuple[int, str]]] = defaultdict(list)
    buf_lock   = threading.Lock()
    write_lock = threading.Lock()
    finished   = [0]

    def worker(rec_idx: int, samp_idx: int) -> tuple[int, int, str]:
        rec  = records[rec_idx]
        text = call_once(rec["instruction"], rec["input"])
        return rec_idx, samp_idx, text

    OUTPUT_FILE.parent.mkdir(parents=True, exist_ok=True)

    with open(OUTPUT_FILE, "a", encoding="utf-8") as out_fh:
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            future_map = {
                pool.submit(worker, ri, si): (ri, si)
                for ri, si in tasks
            }
            for fut in as_completed(future_map):
                try:
                    rec_idx, samp_idx, text = fut.result()
                except Exception as exc:
                    ri, si = future_map[fut]
                    log.error("Task (%d,%d) raised: %s", ri, si, exc)
                    rec_idx, samp_idx, text = ri, si, f"ERROR: {exc}"

                with buf_lock:
                    buf[rec_idx].append((samp_idx, text))
                    if len(buf[rec_idx]) < N_PER_RECORD:
                        continue

                    # All N outputs ready for this record → write N lines
                    pairs   = sorted(buf.pop(rec_idx), key=lambda x: x[0])
                    rec     = records[rec_idx]
                    lines   = [
                        json.dumps(
                            {"instruction": rec["instruction"],
                             "input":       rec["input"],
                             "output":      text},
                            ensure_ascii=False,
                        )
                        for _, text in pairs
                    ]
                    with write_lock:
                        out_fh.write("\n".join(lines) + "\n")
                        out_fh.flush()

                    done_idx.add(rec_idx)
                    save_progress(done_idx)
                    finished[0] += 1

                    total_done = len(done_idx)
                    if finished[0] % 20 == 0 or total_done == len(records):
                        log.info("Progress: %d / %d records  (%d / %d lines)",
                                 total_done, len(records),
                                 total_done * N_PER_RECORD,
                                 len(records) * N_PER_RECORD)

    log.info("Done. %d records → %d lines written to %s",
             len(done_idx), len(done_idx) * N_PER_RECORD, OUTPUT_FILE)


if __name__ == "__main__":
    main()
