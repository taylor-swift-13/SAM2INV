#!/usr/bin/env python3
from __future__ import annotations

import argparse
import atexit
import copy
import concurrent.futures
import os
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
import signal
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
VST_GOAL = (ROOT / "../VST/goal").resolve()
sys.path.insert(0, str(SRC))

import config  # type: ignore
import inv_generator as invgen_mod  # type: ignore
from inv_generator import InvariantGenerator
from llm import LLMConfig, Chatbot, reset_token_stats, get_token_stats  # type: ignore
from houdini_pruner import HoudiniPruner  # type: ignore
from output_verify import OutputVerifier  # type: ignore

USER_CFG = getattr(config, "LOOP_FACTORY_USER_CONFIG", {})
HOUDINI_CFG = getattr(config, "HOUDINI_CONFIG", {})
GEN_CFG = getattr(config, "PARALLEL_GENERATION_CONFIG", {})


def _lf_cfg(name: str, default):
    """Read shared loop_factory config key, with backward-compatible lf_* fallback."""
    if name in USER_CFG:
        return USER_CFG[name]
    legacy = f"lf_{name}"
    return USER_CFG.get(legacy, default)


# Class-level Chatbot patch: intercepts ALL Chatbot.chat calls in the current thread
# via thread-local storage, catching candidates created internally by _generate_multiple_candidates.
_capture = threading.local()  # per-thread: .pairs = List[Tuple[str,str]] | None
_orig_chatbot_chat = Chatbot.chat

def _capturing_chat(self, user_input: str) -> str:
    resp = _orig_chatbot_chat(self, user_input)
    pairs_list = getattr(_capture, "pairs", None)
    if pairs_list is not None:
        p, r = (user_input or "").strip(), (resp or "").strip()
        if p and r:
            pairs_list.append((p, r))
    return resp

Chatbot.chat = _capturing_chat  # type: ignore[method-assign]


def _is_codegen_distill_pair(prompt: str, response: str) -> bool:
    """
    Keep only code-generation conversation pairs for distillation SFT.
    Excludes auxiliary JSON tasks (e.g., semantic dedup / quality gate).
    """
    p = (prompt or "").strip()
    r = (response or "").strip()
    if not p or not r:
        return False

    p_low = p.lower()
    r_low = r.lower()

    # Exclude known non-code helper tasks.
    blocked_prompt_markers = (
        "you are deduplicating acsl loop invariants",
        "remove_indices",
        "return strict json",
        "quality reviewer",
        "\"ok\": true/false",
        "goal: decide whether loop invariants in annotated_code are high quality",
    )
    if any(m in p_low for m in blocked_prompt_markers):
        return False

    # Distill SFT should learn annotated-C generation, not JSON classification.
    if r.startswith("{") and r.endswith("}"):
        return False
    if "\"remove_indices\"" in r_low:
        return False

    return True


def _pick_rejected_candidate_text(rej: Dict[str, str]) -> str:
    """Prefer original candidate response (with COT) for dpo_teacher.rejected."""
    for key in ("raw_response", "cot_code", "response", "output", "code"):
        text = (rej.get(key, "") or "").strip()
        if text:
            return text
    return ""


_think_strip_re_global = re.compile(r"<\s*think\s*>[\s\S]*?<\s*/\s*think\s*>", re.IGNORECASE)
_reasoning_strip_re_global = re.compile(r"<\s*reasoning\s*>[\s\S]*?<\s*/\s*reasoning\s*>", re.IGNORECASE)
_code_open_re_global = re.compile(r"<\s*code\s*>\s*", re.IGNORECASE)
_code_close_re_global = re.compile(r"\s*<\s*/\s*code\s*>", re.IGNORECASE)
_reasoning_tag_re_global = re.compile(r"<\s*(think|reasoning)\s*>", re.IGNORECASE)
_code_tag_re_global = re.compile(r"<\s*code\s*>", re.IGNORECASE)
_reasoning_extract_re_global = re.compile(r"<\s*reasoning\s*>([\s\S]*?)<\s*/\s*reasoning\s*>", re.IGNORECASE)
_think_extract_re_global = re.compile(r"<\s*think\s*>([\s\S]*?)<\s*/\s*think\s*>", re.IGNORECASE)


def _strip_cot_wrappers(text: str) -> str:
    t = _think_strip_re_global.sub("", text or "")
    t = _reasoning_strip_re_global.sub("", t)
    t = _code_open_re_global.sub("", t)
    t = _code_close_re_global.sub("", t)
    return t.strip()


def _has_cot(text: str) -> bool:
    t = text or ""
    return bool(_reasoning_tag_re_global.search(t) and _code_tag_re_global.search(t))


def _extract_cot_text(text: str) -> str:
    t = text or ""
    m = _reasoning_extract_re_global.search(t)
    if m:
        return m.group(1).strip()
    m = _think_extract_re_global.search(t)
    if m:
        return m.group(1).strip()
    return ""


def _compose_rejected_with_reason(rej: Dict[str, str]) -> str:
    raw_text = _pick_rejected_candidate_text(rej)
    # Preserve original candidate COT if it is already well-formed.
    if _has_cot(raw_text):
        return raw_text.strip()

    # Keep original code/text; missing-COT rejected items are handled in COT Phase#3.
    return _strip_cot_wrappers(raw_text)


CPP_KEYWORDS = {
    "if", "else", "while", "for", "int", "return", "break", "continue", "char", "float",
    "double", "void", "do", "switch", "case", "sizeof", "struct", "union", "enum", "typedef",
    "static", "extern", "const", "volatile", "unsigned", "signed", "short", "long", "main",
    "loop", "invariant", "assigns", "variant", "requires", "assert", "Pre",
}


def count_loops(code: str) -> int:
    return len(re.findall(r"\bwhile\s*\(", code)) + len(re.findall(r"\bfor\s*\(", code))


def count_loops_with_invariants(code: str) -> Tuple[int, int]:
    loop_matches = list(re.finditer(r"\b(?:while|for)\s*\(", code))
    if not loop_matches:
        return 0, 0

    ann_pat = re.compile(r"/\*[\s\S]*?\*/")
    covered = 0
    for lm in loop_matches:
        prefix = code[: lm.start()]
        blocks = list(ann_pat.finditer(prefix))
        if not blocks:
            continue
        last = blocks[-1]
        # Only treat as loop annotation if directly attached (except whitespace).
        if prefix[last.end() :].strip():
            continue
        if "loop invariant" in last.group(0):
            covered += 1
    return covered, len(loop_matches)


def extract_per_loop_invariants(code: str) -> List[List[str]]:
    """
    Extract invariants for each loop in order.
    A loop gets invariants only from the immediately attached ACSL block.
    """
    loop_matches = list(re.finditer(r"\b(?:while|for)\s*\(", code))
    if not loop_matches:
        return []

    ann_pat = re.compile(r"/\*[\s\S]*?\*/")
    per_loop: List[List[str]] = []
    for lm in loop_matches:
        prefix = code[: lm.start()]
        blocks = list(ann_pat.finditer(prefix))
        if not blocks:
            per_loop.append([])
            continue
        last = blocks[-1]
        if prefix[last.end() :].strip():
            per_loop.append([])
            continue
        block = last.group(0)
        invs = [m.strip() for m in re.findall(r"loop invariant\s+([^;]+);", block)]
        per_loop.append(invs)
    return per_loop



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


def cleanup_transient_artifacts(run_tag: str | None = None) -> None:
    """Best-effort cleanup for temporary directories/files created outside generated/."""
    patterns = []
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


def normalize_code(s: str) -> str:
    s = re.sub(r"/\*.*?\*/", "", s, flags=re.DOTALL)
    s = re.sub(r"//.*?$", "", s, flags=re.MULTILINE)
    s = re.sub(r"\s+", "", s)
    return s


def strip_redundant_atom_parens(s: str) -> str:
    """
    Remove redundant parentheses around atomic terms, e.g. (x), (C), (123).
    Keep compound-expression parentheses intact.
    """
    out = s
    pat = re.compile(r"\(([_A-Za-z]\w*|\d+)\)")
    while True:
        nxt = pat.sub(r"\1", out)
        if nxt == out:
            return out
        out = nxt


def normalize_statement_forms(s: str) -> str:
    """
    Normalize common C statement forms to reduce syntactic-only skeleton mismatches.
    """
    out = s
    out = re.sub(
        r"\b([A-Za-z_]\w*)\s*([+\-*/%])=\s*([^;]+);",
        lambda m: f"{m.group(1)}={m.group(1)}{m.group(2)}({m.group(3)});",
        out,
    )
    out = re.sub(r"\b([A-Za-z_]\w*)\s*\+\+\s*;", r"\1=\1+1;", out)
    out = re.sub(r"\+\+\s*([A-Za-z_]\w*)\s*;", r"\1=\1+1;", out)
    out = re.sub(r"\b([A-Za-z_]\w*)\s*--\s*;", r"\1=\1-1;", out)
    out = re.sub(r"--\s*([A-Za-z_]\w*)\s*;", r"\1=\1-1;", out)
    out = re.sub(r"else\s*\{\s*\}", "", out)
    return out


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
    src = normalize_statement_forms(raw_code)
    m = re.search(r"while\s*\([^)]*\)\s*\{", src)
    if not m:
        payload = normalize_code(canonicalize_identifiers(src))
        payload = strip_redundant_atom_parens(payload)
        payload = re.sub(r"\b\d+\b", "C", payload)
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()

    i = m.end()
    depth = 1
    while i < len(src):
        c = src[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                body = src[m.end() : i]
                body_norm = normalize_code(canonicalize_identifiers(body))
                body_norm = strip_redundant_atom_parens(body_norm)
                body_norm = re.sub(r"\b\d+\b", "C", body_norm)
                return hashlib.sha256(body_norm.encode("utf-8")).hexdigest()
        i += 1

    payload = normalize_code(canonicalize_identifiers(src))
    payload = strip_redundant_atom_parens(payload)
    payload = re.sub(r"\b\d+\b", "C", payload)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def has_no_assert(code: str) -> bool:
    return re.search(r"/\*@\s*assert\b", code) is None


def extract_updated_vars(loop_content: str) -> Set[str]:
    updated = set(re.findall(r"\b([A-Za-z_]\w*)\s*=", loop_content))
    return {v for v in updated if v not in CPP_KEYWORDS}


def is_canonical_infinite_loop(loop_content: str) -> bool:
    text = loop_content or ""

    mw = re.search(r"\bwhile\s*\(([^)]*)\)", text)
    if mw:
        cond = re.sub(r"\s+", "", mw.group(1) or "")
        # Treat canonical infinite while as special: while(1)
        if cond in {"1", "(1)"}:
            return True

    # Also accept canonical infinite for-loop: for(;;)
    mf = re.search(r"\bfor\s*\(([^;]*);([^;]*);([^)]*)\)", text)
    if mf:
        init = re.sub(r"\s+", "", mf.group(1) or "")
        cond = re.sub(r"\s+", "", mf.group(2) or "")
        step = re.sub(r"\s+", "", mf.group(3) or "")
        if init == "" and cond == "" and step == "":
            return True

    return False


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




def strip_blank_lines(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if line.strip())


# ─────────────────────────────────────────────────────────────────────────────
# Houdini-based DPO augmentation helpers
# Mirrors HoudiniPruner.hudini() but collects "all valid + 1 bad" rejected
# variants at each round instead of returning the final pruned code.
# ─────────────────────────────────────────────────────────────────────────────

def _extract_invariant_spans(code: str) -> List[Tuple[int, int]]:
    inv_pat = re.compile(r"^[ \t]*loop\s+invariant\s+[^;]+;[ \t]*\n?", flags=re.MULTILINE)
    return [(m.start(), m.end()) for m in inv_pat.finditer(code or "")]


def _build_subset_invariant_code(code: str, keep_indices: Set[int]) -> str:
    spans = _extract_invariant_spans(code)
    if not spans:
        return (code or "").strip()
    out = code
    for idx in range(len(spans) - 1, -1, -1):
        if idx in keep_indices:
            continue
        s, e = spans[idx]
        out = out[:s] + out[e:]
    return out.strip()


def _sample_subset_code(
    code: str,
    rng: random.Random,
    force_proper_subset: bool = True,
) -> Tuple[Optional[str], int, int]:
    """
    Randomly keep k invariants where k in [1, max(n-2,1)].
    Returns (subset_code, k, n).
    """
    src = (code or "").strip()
    spans = _extract_invariant_spans(src)
    n = len(spans)
    if n <= 0:
        return None, 0, n
    hi = max(n - 2, 1)
    if force_proper_subset:
        hi = min(hi, n - 1)
    if hi < 1:
        return None, 0, n
    k = rng.randint(1, hi)
    keep = set(rng.sample(range(n), k))
    subset = _build_subset_invariant_code(src, keep)
    if not subset or subset == src:
        return None, k, n
    return subset, k, n


def _aug_error_subset_reject(rejected_code: str, rng: random.Random, max_tries: int = 16) -> Optional[str]:
    """Aug C: sample a random proper subset from an error candidate."""
    src = (rejected_code or "").strip()
    if not src:
        return None
    for _ in range(max_tries):
        subset, _m, _n = _sample_subset_code(src, rng, force_proper_subset=True)
        if subset and subset != src:
            return subset
    return None


def _aug_mixed_invariant_reject(
    chosen_code: str,
    bad_invariants: List[str],
    rng: random.Random,
    num_samples: int = 1,
) -> List[str]:
    """Unified DPO augmentation: randomly sample invariants from good+bad pool.

    good ∈ [0, m-2], bad ∈ [0, n], total k ∈ [1, k_max] where
    k_max ~ randint(max(m-2,1), m+2).  Result must differ from chosen.
    """
    src = (chosen_code or "").strip()
    if not src:
        return []

    # Extract invariant text and spans from chosen
    spans = _extract_invariant_spans(src)
    m = len(spans)
    if m <= 0:
        return []

    # Extract the text of each good invariant (normalized)
    inv_pat = re.compile(r'loop\s+invariant\s+([^;]+);')
    good_texts: List[str] = []
    for s_start, s_end in spans:
        match = inv_pat.search(src[s_start:s_end])
        if match:
            good_texts.append(re.sub(r'\s+', ' ', match.group(1).strip()))

    # Filter bad_invariants: remove those already in chosen (by normalized text)
    good_norm_set = set(good_texts)
    filtered_bad = [b for b in bad_invariants if re.sub(r'\s+', ' ', b.strip()) not in good_norm_set]
    n = len(filtered_bad)

    # Need at least one degree of freedom
    if n == 0 and m <= 1:
        return []

    # Determine indentation from existing invariants
    first_span_text = src[spans[0][0]:spans[0][1]]
    indent_match = re.match(r'^([ \t]*)', first_span_text)
    indent = indent_match.group(1) if indent_match else '      '

    # good ∈ [0, m-2], bad ∈ [0, n], total ≥ 1, total ≤ k_max, result ≠ chosen
    good_hi = max(m - 2, 0)
    if good_hi == 0 and n == 0:
        return []

    results: List[str] = []
    seen: set = set()
    for _ in range(num_samples * 4):
        if len(results) >= num_samples:
            break

        num_good = rng.randint(0, good_hi)
        num_bad = rng.randint(0, n)
        k = num_good + num_bad

        k_max = rng.randint(max(m - 2, 1), m + 2)
        if k < 1 or k > k_max:
            continue

        # Sample
        if num_good > 0:
            keep_indices = set(rng.sample(range(m), num_good))
        else:
            keep_indices = set()
        subset_code = _build_subset_invariant_code(src, keep_indices)

        if num_bad > 0:
            sampled_bad = rng.sample(filtered_bad, num_bad)
            inv_spans_in_subset = _extract_invariant_spans(subset_code)
            if inv_spans_in_subset:
                # Insert after the last remaining invariant line
                insert_pos = inv_spans_in_subset[-1][1]
            else:
                # No invariant lines left; insert before loop assigns or */ closing
                assigns_match = re.search(r'^[ \t]*loop\s+assigns\b', subset_code, re.MULTILINE)
                if assigns_match:
                    insert_pos = assigns_match.start()
                else:
                    # Find */ that closes an ACSL block before a loop keyword
                    close_match = re.search(r'\*/\s*(?:while|for)\s*\(', subset_code)
                    if close_match:
                        insert_pos = close_match.start()
                    else:
                        lm = re.search(r'\b(?:while|for)\s*\(', subset_code)
                        if not lm:
                            continue
                        insert_pos = lm.start()
            bad_lines = ''.join(f'{indent}loop invariant {b.strip()};\n' for b in sampled_bad)
            variant = (subset_code[:insert_pos] + bad_lines + subset_code[insert_pos:]).strip()
        else:
            variant = subset_code.strip()

        if variant == src or variant in seen:
            continue
        seen.add(variant)
        results.append(variant)

    return results


def _extract_first_json_object(text: str) -> Optional[Dict]:
    if not text:
        return None
    s = text.strip()
    if s.startswith("{") and s.endswith("}"):
        try:
            obj = json.loads(s)
            return obj if isinstance(obj, dict) else None
        except json.JSONDecodeError:
            pass
    m = re.search(r"\{[\s\S]*\}", s)
    if not m:
        return None
    try:
        obj = json.loads(m.group(0))
        return obj if isinstance(obj, dict) else None
    except json.JSONDecodeError:
        return None


def quality_gate(
    gen: InvariantGenerator,
    raw_code: str,
    annotated_code: str,
    llm_cfg: LLMConfig,
    logger: Optional[logging.Logger] = None,
) -> Tuple[bool, str]:
    gate_cfg = copy.copy(llm_cfg)
    # 门控评审稳定性优先，降低采样温度。
    gate_cfg.api_temperature = 0.0
    reviewer = Chatbot(gate_cfg)
    invs = gen._extract_invariants_from_code(annotated_code)
    judge_prompt = (
        "You are a C/ACSL loop-invariant quality reviewer. Return JSON only; no explanation.\n"
        "Goal: decide whether loop invariants in annotated_code are high quality.\n"
        "Judging criteria (semantic, not template-based):\n"
        "1) Invariants must be non-trivial, not unrelated identities or filler statements.\n"
        "2) They must effectively summarize loop behavior (update relations, bounds, conservation laws, etc.).\n"
        "3) Every variable modified inside the loop should be covered by the invariant set; do not miss key variables.\n"
        "4) If a loop can terminate, invariants must include explicit bound(s) for loop-control variable(s) "
        "to support a termination argument.\n"
        "\n"
        "Return strict JSON:\n"
        "{\n"
        "  \"ok\": true/false,\n"
        "  \"reason\": \"pass or fail\"\n"
        "}\n\n"
        f"raw_code:\n```c\n{raw_code}\n```\n\n"
        f"annotated_code:\n```c\n{annotated_code}\n```\n\n"
        f"extracted_invariants:\n{json.dumps(invs, ensure_ascii=False)}\n"
    )
    resp = reviewer.chat(judge_prompt)
    parsed = _extract_first_json_object(resp)
    if logger:
        logger.info("LLM quality-gate raw response: %s", (resp or "").strip())
    if not parsed:
        return False, "llm_gate_invalid_json"
    ok = bool(parsed.get("ok", False))
    reason = str(parsed.get("reason", "") or "").strip() or ("ok" if ok else "llm_gate_rejected")
    return ok, reason


def _loop_factory_base_cmd(hp: Dict[str, object], force_core: Optional[str] = None) -> List[str]:
    cmd = [
        sys.executable,
        str(ROOT / "loop_factory.py"),
        "--profile", str(hp["profile"]),
        "--out-dir", str(hp["out_dir"]),
        "--count", str(hp["count"]),
        "--seed", str(hp["seed"]),
        "--max-vars", str(hp["max_vars"]),
        "--params", str(hp["max_params"]),
        "--min-params", str(hp["min_params"]),
        "--min-loops", str(hp["min_loops"]),
        "--max-loops", str(hp["max_loops"]),
        "--max-assign", str(hp["max_assign"]),
        "--min-assign", str(hp["min_assign"]),
        "--max-ifelse", str(hp["max_ifelse"]),
        "--min-ifelse", str(hp["min_ifelse"]),
        "--min-vars",   str(hp["min_vars"]),
        "--max-depth", str(hp["max_depth"]),
        "--p-multi", str(hp["p_multi"]),
        "--q-nest", str(hp["q_nest"]),
        "--p-nonlinear", str(hp["p_nonlinear"]),
        "--nonlinear-strength", str(hp["nonlinear_strength"]),
        "--p-semantic-core", str(hp["p_semantic_core"]),
    ]
    allowed_templates = str(hp.get("allowed_templates", "") or "").strip()
    if allowed_templates:
        cmd.extend(["--allowed-templates", allowed_templates])
    if bool(hp.get("llm_core_gen", False)):
        cmd.append("--llm-core-gen")
    if force_core:
        cmd.extend(["--force-core", force_core])
    return cmd


def probe_usable_semantic_cores(seed: int, lf_overrides: Dict[str, object], probe_max_resample: int = 128) -> List[str]:
    hp = loop_factory_hyperparams(seed, ROOT / "generated" / "_core_probe_tmp", lf_overrides)
    cmd = _loop_factory_base_cmd(hp)
    cmd.extend(["--print-usable-cores-json", "--probe-max-resample", str(max(1, probe_max_resample))])
    out = subprocess.check_output(cmd, text=True).strip()
    try:
        parsed = json.loads(out)
    except json.JSONDecodeError as e:
        raise RuntimeError(f"Failed to parse usable-core JSON from loop_factory: {out}") from e
    if not isinstance(parsed, list):
        raise RuntimeError(f"Usable-core probe returned non-list payload: {parsed!r}")
    return [str(x) for x in parsed if isinstance(x, str) and x]


def build_even_core_plan(total_attempts: int, cores: List[str]) -> List[Optional[str]]:
    if total_attempts <= 0:
        return []
    if not cores:
        return [None] * total_attempts
    k = len(cores)
    base = total_attempts // k
    rem = total_attempts % k
    plan: List[Optional[str]] = []
    for i, c in enumerate(cores):
        quota = base + (1 if i < rem else 0)
        plan.extend([c] * quota)
    return plan


def _read_selected_core_from_meta(out_dir: Path) -> str:
    meta_path = out_dir / "generation_meta.json"
    if not meta_path.exists():
        return "none"
    try:
        data = json.loads(meta_path.read_text(encoding="utf-8"))
    except Exception:
        return "none"
    if not isinstance(data, list) or not data:
        return "none"
    first = data[0] if isinstance(data[0], dict) else {}
    primary = str(first.get("selected_core_primary", "none")).strip()
    return primary or "none"


def generate_one_loop(
    out_dir: Path,
    seed: int,
    lf_overrides: Dict[str, object],
    force_core: Optional[str] = None,
) -> Tuple[Path, str]:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    hp = loop_factory_hyperparams(seed, out_dir, lf_overrides)
    cmd = _loop_factory_base_cmd(hp, force_core=force_core)
    subprocess.run(cmd, check=True)
    c_files = sorted(out_dir.glob("*.c"), key=lambda p: int(p.stem))
    if not c_files:
        raise RuntimeError("loop_factory did not generate any .c")
    selected_core = _read_selected_core_from_meta(out_dir)
    return c_files[0], selected_core


def loop_factory_hyperparams(seed: int, out_dir: Path, overrides: Dict[str, object] | None = None) -> Dict[str, object]:
    """
    Fully materialized loop_factory configuration for one generation call.
    Keep this aligned with loop_factory.py defaults + this pipeline constraints.
    """
    hp = {
        "profile": "benchmark",
        "out_dir": str(out_dir),
        "count": 1,
        "seed": seed,
        # Bias generator toward harder, benchmark-like loops seen in src/input.
        "max_vars": 6,
        "max_params": 2,
        "min_params": 1,
        "min_loops": 1,
        "max_loops": 1,
        "max_assign": 6,
        "min_assign": 1,
        "max_ifelse": 3,
        "min_ifelse": 0,
        "min_vars": 1,
        "max_depth": 1,
        "p_multi": 0.0,
        "q_nest": 0.0,
        "p_nonlinear": 0.75,
        "nonlinear_strength": 0.82,
        "p_semantic_core": 0.88,
        "allowed_templates": "",
        "llm_core_gen": False,
    }
    if overrides:
        for k, v in overrides.items():
            if v is not None and k in hp:
                hp[k] = v
    return hp


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
    force_core: Optional[str] = None,
    forced_raw_code: Optional[str] = None,
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
        selected_core = "none"
        if forced_raw_code is not None:
            raw_code = forced_raw_code
        else:
            src_c, selected_core = generate_one_loop(attempt_tmp_loops, seed, lf_overrides, force_core=force_core)
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
        local_cfg = copy.copy(llm_cfg)
        gen = InvariantGenerator(
            file_id,
            llm_config=local_cfg,
            logger=logger,
            output_dir=str(src_output_dir),
            input_subdir=src_input_dir.name,
        )

        # Thread-local capture: class-level patch intercepts ALL Chatbot.chat calls
        # in this thread, including candidates created inside _generate_multiple_candidates.
        pairs: List[Tuple[str, str]] = []
        _capture.pairs = pairs
        try:
            if stop_event.is_set():
                return {"ok": False, "reason": "cancelled", "attempt": attempt, "seed": seed}
            final_code = gen.generate_all(max_iterations=1)
        finally:
            _capture.pairs = None
        gen.save_results(str(src_output_dir))
        # Hard guard: keep only samples with at least one real captured LLM call.
        if not pairs:
            return {"ok": False, "reason": "no LLM calls captured", "attempt": attempt, "seed": seed}

        user_prompt = pairs[0][0] if pairs else ""
        raw_model_output = pairs[0][1] if pairs else ""
        prompt_count = len(pairs)
        all_prompts = [p[0] for p in pairs]
        first_pass = gen.first_pass or {}
        syntax_ok = first_pass.get("syntax") is not None
        valid_ok = first_pass.get("valid") is not None
        if not (syntax_ok and valid_ok):
            return {"ok": False, "reason": "syntax/valid failed", "attempt": attempt, "seed": seed}

        out_c = src_output_dir / f"{file_id}.c"
        annotated_raw = out_c.read_text(encoding="utf-8") if out_c.exists() else (final_code or "")
        annotated = strip_blank_lines(annotated_raw)
        if out_c.exists() and annotated != annotated_raw:
            out_c.write_text(annotated, encoding="utf-8")

        ok, reason = quality_gate(gen, raw_code, annotated, llm_cfg=local_cfg, logger=logger)
        if not ok:
            return {
                "ok": False,
                "reason": reason,
                "attempt": attempt,
                "seed": seed,
            }

        invariants = gen._extract_invariants_from_code(annotated)
        raw_key = compute_raw_structure_key(raw_code)
        hparams = loop_factory_hyperparams(seed, attempt_tmp_loops, lf_overrides)
        loop_dpo_records = getattr(gen, "loop_dpo_records", {})
        return {
            "ok": True,
            "attempt": attempt,
            "seed": seed,
            "raw_code": raw_code,
            "annotated": annotated,
            "invariants": invariants,
            "raw_structure_key": raw_key,
            "first_pass": first_pass,
            "token_stats": get_token_stats(),
            "user_prompt": user_prompt,
            "raw_model_output": raw_model_output,
            "prompt_count": prompt_count,
            "all_prompts": all_prompts,
            "all_pairs": pairs,
            "model": model_name,
            "system_prompt": system_prompt,
            "loop_factory_hyperparams": hparams,
            "loop_dpo_records": loop_dpo_records,
            "selected_core": selected_core,
            "forced_core": force_core or "none",
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


def main() -> None:
    parser = argparse.ArgumentParser(description="Batch generate high-quality training data with simple augmentation.")
    parser.add_argument("--target-count", type=int, default=int(USER_CFG.get("target_count", 100)), help="Total candidate attempts to run.")
    parser.add_argument("--aug-per-sample", type=int, default=0, help="(Deprecated, unused) Augmented copies per accepted sample.")
    parser.add_argument("--max-attempts", type=int, default=int(USER_CFG.get("max_attempts", 1200)), help="Max generation attempts before stop.")
    parser.add_argument("--seed", type=int, default=int(USER_CFG.get("seed", 2026)), help="Base random seed.")
    parser.add_argument("--workers", type=int, default=int(USER_CFG.get("workers", 20)), help="Number of concurrent workers.")
    parser.add_argument(
        "--num-candidates",
        "--nums-candidate",
        dest="num_candidates",
        type=int,
        default=int(GEN_CFG.get("num_candidates", 3)),
        help="Number of candidate invariant sets generated per attempt.",
    )
    parser.add_argument(
        "--model",
        type=str,
        default=LLMConfig().api_model,
        help="LLM model name for invariant generation (default from src/config.py LLMConfig.api_model).",
    )
    parser.add_argument("--max-skeleton-repeat", type=int, default=int(USER_CFG.get("max_skeleton_repeat", 3)), help="Maximum accepted samples per loop skeleton key.")
    parser.add_argument(
        "--append",
        action=argparse.BooleanOptionalAction,
        default=bool(USER_CFG.get("append", True)),
        help="Append to existing work-dir data and dedup against existing samples (default: true).",
    )
    parser.add_argument("--work-dir", type=str, default=str(USER_CFG.get("work_dir", "")), help="Optional work dir under loop_factory/generated.")
    # Exposed loop_factory complexity controls.
    parser.add_argument("--max-vars", "--lf-max-vars", dest="max_vars", type=int, default=int(_lf_cfg("max_vars", 6)), help="Loop-factory max variable count.")
    parser.add_argument("--params", "--max-params", "--lf-params", dest="max_params", type=int, default=int(_lf_cfg("max_params", 2)), help="Loop-factory max parameter count.")
    parser.add_argument("--min-params", "--lf-min-params", dest="min_params", type=int, default=int(_lf_cfg("min_params", 1)), help="Loop-factory min parameter count.")
    parser.add_argument("--min-loops", "--lf-min-loops", dest="min_loops", type=int, default=int(_lf_cfg("min_loops", 1)), help="Loop-factory min loop count.")
    parser.add_argument("--max-loops", "--lf-max-loops", dest="max_loops", type=int, default=int(_lf_cfg("max_loops", 1)), help="Loop-factory max loop count.")
    parser.add_argument("--max-assign", "--lf-max-assign", dest="max_assign", type=int, default=int(_lf_cfg("max_assign", 6)), help="Loop-factory max assignments per loop.")
    parser.add_argument("--min-assign", "--lf-min-assign", dest="min_assign", type=int, default=int(_lf_cfg("min_assign", 1)), help="Loop-factory min assignments per loop.")
    parser.add_argument("--max-ifelse", "--lf-max-ifelse", dest="max_ifelse", type=int, default=int(_lf_cfg("max_ifelse", 3)), help="Loop-factory max if/else blocks per loop.")
    parser.add_argument("--min-ifelse", "--lf-min-ifelse", dest="min_ifelse", type=int, default=int(_lf_cfg("min_ifelse", 0)), help="Loop-factory min if/else blocks per loop.")
    parser.add_argument("--min-vars",   "--lf-min-vars",   dest="min_vars",   type=int, default=int(_lf_cfg("min_vars",   1)), help="Loop-factory min state-variable count.")
    parser.add_argument("--max-depth", "--lf-max-depth", dest="max_depth", type=int, default=int(_lf_cfg("max_depth", 1)), help="Loop-factory max loop nesting depth.")
    parser.add_argument("--p-multi", "--lf-p-multi", dest="p_multi", type=float, default=float(_lf_cfg("p_multi", 0.0)), help="Loop-factory p_multi.")
    parser.add_argument("--q-nest", "--lf-q-nest", dest="q_nest", type=float, default=float(_lf_cfg("q_nest", 0.0)), help="Loop-factory q_nest.")
    parser.add_argument("--p-nonlinear", "--lf-p-nonlinear", dest="p_nonlinear", type=float, default=float(_lf_cfg("p_nonlinear", 0.75)), help="Loop-factory nonlinear family probability.")
    parser.add_argument("--p-semantic-core", "--lf-p-semantic-core", dest="p_semantic_core", type=float, default=float(_lf_cfg("p_semantic_core", 0.88)), help="Loop-factory semantic core probability.")
    parser.add_argument(
        "--llm-core-gen",
        "--lf-llm-core-gen",
        dest="llm_core_gen",
        action=argparse.BooleanOptionalAction,
        default=bool(_lf_cfg("llm_core_gen", False)),
        help="Use LLM-guided generation for selected semantic cores inside loop_factory.",
    )
    parser.add_argument(
        "--allowed-templates",
        "--lf-allowed-templates",
        dest="allowed_templates",
        type=str,
        default=str(_lf_cfg("allowed_templates", "")),
        help="Comma-separated whitelist of semantic template/core names passed to loop_factory.",
    )
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

    config.PARALLEL_GENERATION_CONFIG["num_candidates"] = max(1, args.num_candidates)
    config.PARALLEL_GENERATION_CONFIG["use_threading"] = False
    config.PARALLEL_GENERATION_CONFIG["max_workers"] = 1
    config.PARALLEL_GENERATION_CONFIG["temperature"] = 1.0
    # Hard-coded filtering policy for batch_pipeline: all enabled.
    config.SYNTAX_FILTER_CONFIG["enabled"] = True
    config.PARALLEL_GENERATION_CONFIG["filter_by_sampling"] = True
    config.PARALLEL_GENERATION_CONFIG["use_houdini"] = True
    invgen_mod.USE_TRACES = False

    llm_cfg = LLMConfig()
    llm_cfg.api_model = args.model
    cot_mode = bool(getattr(llm_cfg, "enable_cot", False))
    prompt_filename = getattr(llm_cfg, "system_prompt_file", "system_prompt.txt")
    system_prompt = (SRC / "prompts" / prompt_filename).read_text(encoding="utf-8")
    api_jsonl_path = work_root / "llama_factory_train_iio_api_aligned.jsonl"
    dpo_teacher_jsonl_path = work_root / "llama_factory_train_dpo_teacher.jsonl"
    dpo_aug_jsonl_path = work_root / "llama_factory_train_dpo_aug.jsonl"
    distill_jsonl_path = work_root / "llama_factory_train_distill_sft.jsonl"
    template_map_jsonl_path = work_root / "file_template_map.jsonl"
    lf_overrides: Dict[str, object] = {
        "max_vars": args.max_vars,
        "max_params": args.max_params,
        "min_params": args.min_params,
        "min_loops": args.min_loops,
        "max_loops": args.max_loops,
        "max_assign": args.max_assign,
        "min_assign": args.min_assign,
        "max_ifelse": args.max_ifelse,
        "min_ifelse": args.min_ifelse,
        "min_vars":   args.min_vars,
        "max_depth": args.max_depth,
        "p_multi": args.p_multi,
        "q_nest": args.q_nest,
        "p_nonlinear": args.p_nonlinear,
        "p_semantic_core": args.p_semantic_core,
        "allowed_templates": args.allowed_templates,
        "llm_core_gen": args.llm_core_gen,
    }

    # Build in-memory skeleton-count index from existing corpus.
    loop_skeleton_counts: Dict[str, int] = {}
    existing_max_idx = 0
    existing_count = 0
    existing_raw_only_count = 0
    if args.append:
        existing_raw_files = sorted(raw_dir.glob("*.c"), key=lambda p: int(p.stem))
        existing_max_idx = max((int(p.stem) for p in existing_raw_files), default=0)
        for rf in existing_raw_files:
            # Dedup should always consider historical raw corpus in append mode,
            # even when annotated counterpart is missing (interrupted/partial runs).
            raw_code = rf.read_text(encoding="utf-8")
            skey = compute_loop_skeleton_key(raw_code)
            loop_skeleton_counts[skey] = loop_skeleton_counts.get(skey, 0) + 1

            af = ann_dir / rf.name
            if af.exists():
                existing_count += 1
            else:
                existing_raw_only_count += 1

    total_candidates = max(0, args.target_count)
    if args.max_attempts > 0:
        total_candidates = min(total_candidates, args.max_attempts)

    usable_cores = probe_usable_semantic_cores(args.seed, lf_overrides, probe_max_resample=128)
    core_plan = build_even_core_plan(total_candidates, usable_cores)
    core_quota: Dict[str, int] = {c: core_plan.count(c) for c in usable_cores}
    if usable_cores:
        print(
            f"Template balancing enabled: usable_cores={len(usable_cores)}, "
            f"attempts={total_candidates}, min_quota={min(core_quota.values())}, max_quota={max(core_quota.values())}"
        )
    else:
        print("Template balancing disabled: no usable semantic core found under current parameters.")
    if args.append and existing_raw_only_count > 0:
        print(
            f"Append dedup note: loaded {existing_raw_only_count} raw-only historical files "
            f"(without annotated pair) into dedup index."
        )

    accepted_records: List[Dict] = []
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

    # Seed generation policy:
    # - deterministic from user-provided base seed
    # - randomized per attempt (not linear seed+attempt)
    # - append mode shifts RNG stream to reduce overlap with previously accepted files
    seed_offset = existing_max_idx if args.append else 0
    seed_rng = random.Random(args.seed + seed_offset)
    used_attempt_seeds: Set[int] = set()
    next_attempt = 1
    pending: Dict[concurrent.futures.Future, Tuple[int, int, Optional[str]]] = {}
    stop_event = threading.Event()
    file_mode = "a" if args.append else "w"
    distill_count = 0
    with api_jsonl_path.open(file_mode, encoding="utf-8") as api_jsonl_file, \
         dpo_teacher_jsonl_path.open(file_mode, encoding="utf-8") as dpo_teacher_jsonl_file, \
         dpo_aug_jsonl_path.open(file_mode, encoding="utf-8") as dpo_aug_jsonl_file, \
         distill_jsonl_path.open(file_mode, encoding="utf-8") as distill_jsonl_file, \
        template_map_jsonl_path.open(file_mode, encoding="utf-8") as template_map_file:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            while next_attempt <= total_candidates or pending:
                while next_attempt <= total_candidates and len(pending) < workers:
                    attempt = next_attempt
                    next_attempt += 1
                    seed = seed_rng.randint(1, 2_147_483_647)
                    while seed in used_attempt_seeds:
                        seed = seed_rng.randint(1, 2_147_483_647)
                    used_attempt_seeds.add(seed)
                    forced_core = core_plan[attempt - 1] if attempt - 1 < len(core_plan) else None
                    forced_raw = None
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
                        forced_core,
                        forced_raw,
                    )
                    pending[fut] = (attempt, seed, forced_core)

                if not pending:
                    break

                done, _ = concurrent.futures.wait(
                    pending.keys(),
                    return_when=concurrent.futures.FIRST_COMPLETED,
                )
                for fut in done:
                    attempt, seed, forced_core = pending.pop(fut)
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

                    skeleton_key = compute_loop_skeleton_key(result["raw_code"])
                    if loop_skeleton_counts.get(skeleton_key, 0) >= max(1, args.max_skeleton_repeat):
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "duplicate loop skeleton"})
                        continue

                    loop_skeleton_counts[skeleton_key] = loop_skeleton_counts.get(skeleton_key, 0) + 1
                    idx = existing_max_idx + len(accepted_records) + 1
                    (raw_dir / f"{idx}.c").write_text(result["raw_code"], encoding="utf-8")
                    (ann_dir / f"{idx}.c").write_text(result["annotated"], encoding="utf-8")
                    template_map_file.write(json.dumps({
                        "id": f"loop_factory_{idx}",
                        "raw_file": f"raw/{idx}.c",
                        "annotated_file": f"annotated/{idx}.c",
                        "attempt": attempt,
                        "seed": result["seed"],
                        "template": result.get("selected_core", "none"),
                        "selected_core": result.get("selected_core", "none"),
                        "forced_core": forced_core or "none",
                    }, ensure_ascii=False) + "\n")
                    template_map_file.flush()

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
                            "raw_structure_key": result["raw_structure_key"],
                            "first_pass": result["first_pass"],
                            "token_stats": result["token_stats"],
                            "loop_factory_hyperparams": result["loop_factory_hyperparams"],
                            "augmentation": {"type": "none"},
                        }
                    )
                    # Distill SFT: write all raw candidate (prompt, response) pairs
                    # without verification — enables pure knowledge-distillation training.
                    all_pairs = result.get("all_pairs", [])
                    kept_distill_pairs = [
                        (pr_prompt, pr_resp)
                        for pr_prompt, pr_resp in all_pairs
                        if _is_codegen_distill_pair(pr_prompt, pr_resp)
                    ]
                    for pr_prompt, pr_resp in kept_distill_pairs:
                        if pr_prompt and pr_resp:
                            distill_jsonl_file.write(json.dumps({
                                "instruction": result["system_prompt"],
                                "input": pr_prompt,
                                "output": pr_resp,
                            }, ensure_ascii=False) + "\n")
                    if kept_distill_pairs:
                        distill_jsonl_file.flush()
                    distill_count += len(kept_distill_pairs)

                    # SFT: one accepted program -> exactly one JSONL item.
                    # user_prompt is guaranteed non-empty by the hard guard above.
                    prompt_text = result["user_prompt"]

                    api_item = {
                        "instruction": result["system_prompt"],
                        "input": prompt_text,
                        "output": result["annotated"],
                    }
                    api_jsonl_file.write(json.dumps(api_item, ensure_ascii=False) + "\n")
                    api_jsonl_file.flush()

                    # DPO: one accepted program -> one row per rejected candidate.
                    # chosen aligns with SFT output; rejected comes from inv_generator's
                    # loop_dpo_records, which tracks every candidate marked dpo_reject=True
                    # (failed syntax filter, sampling filter, or Houdini pruning),
                    # plus optional Houdini data augmentation rejects.
                    loop_dpo_records = result.get("loop_dpo_records", {})
                    dpo_teacher_written = 0
                    dpo_aug_written = 0
                    # Keep DPO chosen exactly aligned with SFT output, with invariant dedup applied.
                    chosen_code = (result["annotated"] or "").strip()
                    # Hard guard: chosen must be the final, quality-gated, deduplicated annotation.
                    if not chosen_code:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "accepted sample has empty final chosen"})
                        continue
                    aug_rng = random.Random((int(seed) << 32) ^ int(attempt))
                    seen_rejected = set()
                    for _loop_idx, loop_rec in sorted(loop_dpo_records.items()):
                        if not chosen_code:
                            continue
                        for rej in loop_rec.get("rejected_items", []):
                            rej_text = _compose_rejected_with_reason(rej)
                            if not rej_text or rej_text == chosen_code or rej_text in seen_rejected:
                                continue
                            seen_rejected.add(rej_text)
                            dpo_item = {
                                "instruction": result["system_prompt"],
                                "input": prompt_text,
                                "chosen": chosen_code,
                                "rejected": rej_text,
                            }
                            dpo_teacher_jsonl_file.write(json.dumps(dpo_item, ensure_ascii=False) + "\n")
                            dpo_teacher_written += 1
                            # Augmentation C: random subset from error candidate.
                            aug_c = _aug_error_subset_reject((rej.get("code", "") or "").strip(), aug_rng)
                            if aug_c:
                                aug_c = aug_c.strip()
                                if aug_c and aug_c != chosen_code and aug_c not in seen_rejected:
                                    # Normalized check: ensure subset is meaningfully different from chosen
                                    aug_c_invs = set(re.sub(r'\s+', '', inv) for inv in re.findall(r'loop\s+invariant\s+([^;]+);', aug_c))
                                    chosen_invs = set(re.sub(r'\s+', '', inv) for inv in re.findall(r'loop\s+invariant\s+([^;]+);', chosen_code))
                                    if aug_c_invs != chosen_invs:
                                        seen_rejected.add(aug_c)
                                        dpo_aug_jsonl_file.write(json.dumps({
                                            "instruction": result["system_prompt"],
                                            "input": prompt_text,
                                            "chosen": chosen_code,
                                            "rejected": aug_c,
                                        }, ensure_ascii=False) + "\n")
                                        dpo_aug_written += 1
                    # Unified mixed-invariant augmentation (replaces Aug A + Aug B)
                    bad_invs: List[str] = []
                    for _loop_idx, loop_rec in sorted(loop_dpo_records.items()):
                        bad_invs.extend(loop_rec.get("bad_invariants", []))
                    aug_num_samples = max(min(2 * len(bad_invs), 8), 2)
                    for aug_code in _aug_mixed_invariant_reject(
                        chosen_code, bad_invs, aug_rng,
                        num_samples=aug_num_samples,
                    ):
                        if aug_code and aug_code != chosen_code and aug_code not in seen_rejected:
                            seen_rejected.add(aug_code)
                            dpo_aug_jsonl_file.write(json.dumps({
                                "instruction": result["system_prompt"],
                                "input": prompt_text,
                                "chosen": chosen_code,
                                "rejected": aug_code,
                            }, ensure_ascii=False) + "\n")
                            dpo_aug_written += 1
                    if dpo_teacher_written or dpo_aug_written:
                        dpo_teacher_jsonl_file.flush()
                        dpo_aug_jsonl_file.flush()
                    else:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "accepted sample has no dpo rejects"})

    # ── Phase 2: Reverse-COT generation ────────────────────────────────────
    def _emit_cot_log(msg: str, level: str = "INFO") -> None:
        print(msg)
        ts = time.strftime("%Y-%m-%d %H:%M:%S")
        line = f"{ts} - {level} - {msg}\n"
        try:
            with (logs_dir / "cot_phase.log").open("a", encoding="utf-8") as f:
                f.write(line)
            for p in sorted(logs_dir.glob("attempt_*.log")):
                with p.open("a", encoding="utf-8") as f:
                    f.write(line)
        except Exception:
            # Best-effort logging; never break data generation due to log I/O.
            pass

    if not cot_mode:
        _emit_cot_log(f"COT Phase: skipped because system prompt mode is non-COT ({prompt_filename}).")
        return

    from reverse_cot import generate_reverse_cot_rejected, generate_reverse_cots_batch, prepend_cot, lookup_cot
    import openai as _oai

    cot_model = args.model
    cot_client = _oai.OpenAI(base_url=llm_cfg.base_url, api_key=llm_cfg.api_key)

    # Read full data from work_root JSONL (includes all historical + this run)
    def _read_jsonl(path: Path) -> List[Dict]:
        recs = []
        if path.exists():
            for line in path.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if line:
                    recs.append(json.loads(line))
        return recs

    # Strip <think>...</think>, <reasoning>...</reasoning>, and <code>...</code> tags from text
    _think_strip_re = re.compile(r"<\s*think\s*>[\s\S]*?<\s*/\s*think\s*>", re.IGNORECASE)
    _reasoning_strip_re = re.compile(r"<\s*reasoning\s*>[\s\S]*?<\s*/\s*reasoning\s*>", re.IGNORECASE)
    _code_open_re = re.compile(r"<\s*code\s*>\s*", re.IGNORECASE)
    _code_close_re = re.compile(r"\s*<\s*/\s*code\s*>", re.IGNORECASE)
    def _strip_think(text: str) -> str:
        text = _think_strip_re.sub("", text)
        text = _reasoning_strip_re.sub("", text)
        # Strip <code> wrapper, keep inner content
        text = _code_open_re.sub("", text)
        text = _code_close_re.sub("", text)
        return text.strip()

    sft_records = _read_jsonl(api_jsonl_path)
    distill_records = _read_jsonl(distill_jsonl_path)
    dpo_teacher_records = _read_jsonl(dpo_teacher_jsonl_path)
    dpo_aug_records = _read_jsonl(dpo_aug_jsonl_path)

    # Collect tasks for three reverse-COT passes.
    # Pass 1 (normal reverse-COT): api.output + all chosen fields.
    # Pass 2 (rejected reverse-COT): dpo_aug.rejected only.
    # Pass 3 (rejected reverse-COT): dpo_teacher.rejected only when missing COT.
    # Use a minimal neutral context for reverse-COT to avoid conflicting with
    # the full main generation system prompt.
    reverse_cot_context = "Derive loop invariants from code behavior."
    forced_code_tasks: Dict[str, Dict] = {}
    aug_rejected_tasks: Dict[str, Dict] = {}
    teacher_rejected_tasks: Dict[str, Dict] = {}
    forced_cot_by_code: Dict[str, str] = {}
    aug_rejected_cot_by_code: Dict[str, str] = {}
    teacher_rejected_cot_by_code: Dict[str, str] = {}

    for rec in sft_records:
        raw = rec.get("output", "") or ""
        code = _strip_think(raw)
        if not code:
            continue
        if _has_cot(raw):
            cot = _extract_cot_text(raw)
            if cot:
                forced_cot_by_code.setdefault(code, cot)
            continue
        if code not in forced_code_tasks:
            forced_code_tasks[code] = {"system_prompt": reverse_cot_context, "user_prompt": rec["input"], "code_output": code}
    for rec in dpo_teacher_records:
        raw_chosen = rec.get("chosen", "") or ""
        code = _strip_think(raw_chosen)
        if code:
            if _has_cot(raw_chosen):
                cot = _extract_cot_text(raw_chosen)
                if cot:
                    forced_cot_by_code.setdefault(code, cot)
            elif code not in forced_code_tasks:
                forced_code_tasks[code] = {"system_prompt": reverse_cot_context, "user_prompt": rec["input"], "code_output": code}
        rej_text = (rec.get("rejected", "") or "").strip()
        if rej_text and (not _has_cot(rej_text)):
            rej_code = _strip_think(rej_text)
            if rej_code and rej_code not in teacher_rejected_tasks:
                teacher_rejected_tasks[rej_code] = {"system_prompt": reverse_cot_context, "user_prompt": rec["input"], "code_output": rej_code}
        elif rej_text and _has_cot(rej_text):
            rej_code = _strip_think(rej_text)
            if rej_code:
                cot = _extract_cot_text(rej_text)
                if cot:
                    teacher_rejected_cot_by_code.setdefault(rej_code, cot)
    for rec in dpo_aug_records:
        raw_chosen = rec.get("chosen", "") or ""
        code = _strip_think(raw_chosen)
        if code:
            if _has_cot(raw_chosen):
                cot = _extract_cot_text(raw_chosen)
                if cot:
                    forced_cot_by_code.setdefault(code, cot)
            elif code not in forced_code_tasks:
                forced_code_tasks[code] = {"system_prompt": reverse_cot_context, "user_prompt": rec["input"], "code_output": code}
        # dpo_aug.rejected uses a separate rejected reverse-COT pass.
        rej_raw = rec.get("rejected", "") or ""
        rej_code = _strip_think(rej_raw)
        if not rej_code:
            continue
        if _has_cot(rej_raw):
            cot = _extract_cot_text(rej_raw)
            if cot:
                aug_rejected_cot_by_code.setdefault(rej_code, cot)
            continue
        if rej_code not in aug_rejected_tasks:
            aug_rejected_tasks[rej_code] = {"system_prompt": reverse_cot_context, "user_prompt": rec["input"], "code_output": rej_code}

    # Skip any queued code already covered by existing COT payloads in JSONL.
    forced_code_tasks = {k: v for k, v in forced_code_tasks.items() if k not in forced_cot_by_code}
    aug_rejected_tasks = {k: v for k, v in aug_rejected_tasks.items() if k not in aug_rejected_cot_by_code}
    teacher_rejected_tasks = {k: v for k, v in teacher_rejected_tasks.items() if k not in teacher_rejected_cot_by_code}

    all_cot_tasks: List[Dict] = list(forced_code_tasks.values())

    _emit_cot_log(
        f"COT Phase#1: generating reverse-COTs for {len(all_cot_tasks)} code pieces "
        f"(existing={len(forced_cot_by_code)}, dedup inside)..."
    )
    cot_map = generate_reverse_cots_batch(all_cot_tasks, cot_client, cot_model)
    cot_ok = sum(1 for v in cot_map.values() if v)
    _emit_cot_log(f"COT Phase#1: {cot_ok}/{len(cot_map)} unique COTs generated successfully.")

    missing_forced_codes: Set[str] = set()
    for code, task in forced_code_tasks.items():
        # Pass 1 outputs are reused by normalized code for api.output / dpo*.chosen.
        # generate once in batch and reuse by normalized code.
        cot = lookup_cot(cot_map, task["user_prompt"], code)
        if cot:
            forced_cot_by_code[code] = cot
        else:
            missing_forced_codes.add(code)

    if aug_rejected_tasks:
        _emit_cot_log(
            f"COT Phase#2: generating rejected reverse-COTs for {len(aug_rejected_tasks)} "
            f"unique dpo_aug.rejected code pieces (existing={len(aug_rejected_cot_by_code)})..."
        )
    for code, task in aug_rejected_tasks.items():
        cot = generate_reverse_cot_rejected(reverse_cot_context, task["user_prompt"], code, cot_client, cot_model)
        if cot:
            aug_rejected_cot_by_code[code] = cot
        else:
            missing_forced_codes.add(code)

    if teacher_rejected_tasks:
        _emit_cot_log(
            f"COT Phase#3: generating rejected reverse-COTs for {len(teacher_rejected_tasks)} "
            f"unique dpo_teacher.rejected code pieces (existing={len(teacher_rejected_cot_by_code)})..."
        )
    for code, task in teacher_rejected_tasks.items():
        cot = generate_reverse_cot_rejected(reverse_cot_context, task["user_prompt"], code, cot_client, cot_model)
        if cot:
            teacher_rejected_cot_by_code[code] = cot
        else:
            missing_forced_codes.add(code)

    def _force_reverse_cot(text: str, user_prompt: str) -> str:
        # Composed fields are normalized to code-only then always prepended with reverse-COT.
        code = _strip_think(text)
        cot = forced_cot_by_code.get(code, "")
        if not cot:
            missing_forced_codes.add(code)
            return ""
        return prepend_cot(code, cot)

    def _force_reverse_cot_aug_rejected(text: str) -> str:
        """Use pass-2 rejected reverse-COT for dpo_aug.rejected."""
        code = _strip_think(text)
        cot = aug_rejected_cot_by_code.get(code, "")
        if not cot:
            missing_forced_codes.add(code)
            return ""
        return prepend_cot(code, cot)

    def _force_reverse_cot_teacher_rejected(text: str) -> str:
        """Keep original teacher rejected COT; otherwise fill via pass-3 reverse-COT."""
        if _has_cot(text):
            return text
        code = _strip_think(text)
        cot = teacher_rejected_cot_by_code.get(code, "")
        if not cot:
            missing_forced_codes.add(code)
            return ""
        return prepend_cot(code, cot)

    api_out_records: List[Dict] = []
    distill_out_records: List[Dict] = []
    dpo_teacher_out_records: List[Dict] = []
    dpo_aug_out_records: List[Dict] = []
    skipped_counts = {"api": 0, "distill": 0, "dpo_teacher": 0, "dpo_aug": 0}

    for rec in sft_records:
        output = _force_reverse_cot(rec["output"], rec["input"])
        if not output:
            skipped_counts["api"] += 1
            continue
        api_out_records.append({
            "instruction": system_prompt,
            "input": rec["input"],
            "output": output,
        })

    for rec in distill_records:
        # Distill keeps original candidate COT; do not reverse-COT rewrite.
        output = rec["output"]
        if not output:
            skipped_counts["distill"] += 1
            continue
        distill_out_records.append({
            "instruction": system_prompt,
            "input": rec["input"],
            "output": output,
        })

    for rec in dpo_teacher_records:
        chosen = _force_reverse_cot(rec["chosen"], rec["input"])
        rejected = _force_reverse_cot_teacher_rejected(rec["rejected"])
        if not chosen or not rejected:
            skipped_counts["dpo_teacher"] += 1
            continue
        dpo_teacher_out_records.append({
            "instruction": system_prompt,
            "input": rec["input"],
            "chosen": chosen,
            "rejected": rejected,
        })

    for rec in dpo_aug_records:
        chosen = _force_reverse_cot(rec["chosen"], rec["input"])
        rejected = _force_reverse_cot_aug_rejected(rec["rejected"])
        if not chosen or not rejected:
            skipped_counts["dpo_aug"] += 1
            continue
        dpo_aug_out_records.append({
            "instruction": system_prompt,
            "input": rec["input"],
            "chosen": chosen,
            "rejected": rejected,
        })

    def _filter_records_without_cot(records: List[Dict], fields: List[str], dataset_name: str) -> List[Dict]:
        kept: List[Dict] = []
        dropped = 0
        for rec in records:
            if all(_has_cot(rec.get(f, "")) for f in fields):
                kept.append(rec)
            else:
                dropped += 1
        if dropped:
            _emit_cot_log(f"COT Phase: dropped {dropped} {dataset_name} records missing valid <reasoning>/<code>.", level="WARNING")
        return kept

    api_out_records = _filter_records_without_cot(api_out_records, ["output"], "api")
    distill_out_records = _filter_records_without_cot(distill_out_records, ["output"], "distill")
    dpo_teacher_out_records = _filter_records_without_cot(dpo_teacher_out_records, ["chosen", "rejected"], "dpo_teacher")
    dpo_aug_out_records = _filter_records_without_cot(dpo_aug_out_records, ["chosen", "rejected"], "dpo_aug")
    if skipped_counts["api"] or skipped_counts["distill"] or skipped_counts["dpo_teacher"] or skipped_counts["dpo_aug"]:
        _emit_cot_log(
            "COT Phase: skipped records due to COT failure "
            f"(api={skipped_counts['api']}, distill={skipped_counts['distill']}, "
            f"dpo_teacher={skipped_counts['dpo_teacher']}, dpo_aug={skipped_counts['dpo_aug']}).",
            level="WARNING",
        )
    if missing_forced_codes:
        _emit_cot_log(f"COT Phase: {len(missing_forced_codes)} unique code snippets failed COT generation.", level="WARNING")

    with api_jsonl_path.open("w", encoding="utf-8") as f:
        for rec in api_out_records:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    with distill_jsonl_path.open("w", encoding="utf-8") as f:
        for rec in distill_out_records:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    with dpo_teacher_jsonl_path.open("w", encoding="utf-8") as f:
        for rec in dpo_teacher_out_records:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    with dpo_aug_jsonl_path.open("w", encoding="utf-8") as f:
        for rec in dpo_aug_out_records:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    _emit_cot_log(f"COT output written to {work_root}")

    cleanup_transient_artifacts(run_tag)
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
    print(f"JSONL SFT (instruction/input/output): {api_jsonl_path}")
    print(f"JSONL DPO Teacher (instruction/input/chosen/rejected): {dpo_teacher_jsonl_path}")
    print(f"JSONL DPO Aug (instruction/input/chosen/rejected): {dpo_aug_jsonl_path}")
    print(f"JSONL Distill SFT (all raw candidates, {distill_count} items): {distill_jsonl_path}")
    print(f"Template map JSONL (file -> semantic core): {template_map_jsonl_path}")
    print(f"Reject log: {reject_path}")


if __name__ == "__main__":
    main()
