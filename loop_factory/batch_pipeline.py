#!/usr/bin/env python3
from __future__ import annotations

import argparse
import atexit
import copy
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
import signal
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

ROOT = Path(__file__).resolve().parent
SRC = (ROOT / "../src").resolve()
VST_GOAL = (ROOT / "../VST/goal").resolve()
sys.path.insert(0, str(SRC))

import config  # type: ignore
import inv_generator as invgen_mod  # type: ignore
from inv_generator import InvariantGenerator  # type: ignore
from llm import LLMConfig, Chatbot, reset_token_stats, get_token_stats  # type: ignore

USER_CFG = getattr(config, "LOOP_FACTORY_USER_CONFIG", {})


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
                body_norm = re.sub(r"\b\d+\b", "C", body_norm)
                return hashlib.sha256(body_norm.encode("utf-8")).hexdigest()
        i += 1

    payload = normalize_code(canonicalize_identifiers(src))
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


def _strip_balanced_outer_parens(expr: str) -> str:
    s = expr.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        balanced = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth < 0:
                    balanced = False
                    break
                if depth == 0 and i != len(s) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        s = s[1:-1].strip()
    return s


def _normalize_inv_expr(expr: str) -> str:
    s = re.sub(r"\s+", "", expr)
    s = _strip_balanced_outer_parens(s)
    s = s.replace("(", "").replace(")", "")
    # Canonicalize neutral operators so x, x+0, x*1, x/1 can collapse.
    while True:
        prev = s
        s = re.sub(r"^1\*", "", s)
        s = re.sub(r"\*1$", "", s)
        s = re.sub(r"\+0$", "", s)
        s = re.sub(r"-0$", "", s)
        s = re.sub(r"/1$", "", s)
        if s == prev:
            break
    return s


def _split_top_level_comparison(inv: str) -> Tuple[str, str, str] | None:
    s = inv.strip()
    if not s:
        return None
    ops = ("<=", ">=", "==", "!=", "<", ">")
    depth = 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        elif depth == 0:
            for op in ops:
                if s.startswith(op, i):
                    lhs = s[:i].strip()
                    rhs = s[i + len(op) :].strip()
                    if lhs and rhs:
                        return lhs, op, rhs
                    return None
        i += 1
    return None


def invariant_dedup_key(inv: str) -> str:
    cmp_parts = _split_top_level_comparison(inv)
    if cmp_parts is None:
        return _normalize_inv_expr(inv)
    lhs, op, rhs = cmp_parts
    lhs_n = _normalize_inv_expr(lhs)
    rhs_n = _normalize_inv_expr(rhs)
    if op in {"==", "!="}:
        a, b = sorted([lhs_n, rhs_n])
        return f"{a}{op}{b}"
    return f"{lhs_n}{op}{rhs_n}"


def is_tautological(inv: str) -> bool:
    x = re.sub(r"\s+", "", inv)
    if x in {"1", "true", "True"}:
        return True

    cmp_parts = _split_top_level_comparison(inv)
    if cmp_parts is not None:
        lhs, op, rhs = cmp_parts
        lhs_n = _normalize_inv_expr(lhs)
        rhs_n = _normalize_inv_expr(rhs)
        # Identity/contradiction with identical sides after stripping brackets and neutral ops.
        if lhs_n and rhs_n and lhs_n == rhs_n:
            return True
        # Explicitly reject x == (x + 0)-style equalities.
        if op == "==":
            if rhs_n.startswith(lhs_n + "+") and rhs_n[len(lhs_n) + 1 :] == "0":
                return True
            if rhs_n.startswith(lhs_n + "-") and rhs_n[len(lhs_n) + 1 :] == "0":
                return True
            if lhs_n.startswith(rhs_n + "+") and lhs_n[len(rhs_n) + 1 :] == "0":
                return True
            if lhs_n.startswith(rhs_n + "-") and lhs_n[len(rhs_n) + 1 :] == "0":
                return True

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

    m = re.match(r"^([A-Za-z_]\w*)==(.+)$", x)
    if not m:
        m2 = re.match(r"^(.+)==([A-Za-z_]\w*)$", x)
        if not m2:
            return False
        lhs, rhs = m2.group(2), m2.group(1)
    else:
        lhs, rhs = m.group(1), m.group(2)

    rhs_norm = strip_mul1(rhs)
    if lhs == rhs_norm:
        return True
    if rhs.startswith(lhs + "+") and is_zero_expr(rhs[len(lhs) + 1 :]):
        return True
    if rhs.startswith(lhs + "-") and is_zero_expr(rhs[len(lhs) + 1 :]):
        return True
    return False


def is_nontrivial_inv(inv: str) -> bool:
    if is_tautological(inv):
        return False
    if not any(op in inv for op in ["==", "!=", "<=", ">=", "<", ">"]):
        return False
    return True


def _attached_invariant_blocks(code: str) -> List[Tuple[int, int]]:
    loop_matches = list(re.finditer(r"\b(?:while|for)\s*\(", code))
    if not loop_matches:
        return []
    ann_pat = re.compile(r"/\*[\s\S]*?\*/")
    blocks = list(ann_pat.finditer(code))
    if not blocks:
        return []
    spans: List[Tuple[int, int]] = []
    seen = set()
    for lm in loop_matches:
        prefix = code[: lm.start()]
        cand = [b for b in blocks if b.end() <= lm.start()]
        if not cand:
            continue
        last = cand[-1]
        if prefix[last.end() :].strip():
            continue
        if "loop invariant" not in last.group(0):
            continue
        span = (last.start(), last.end())
        if span not in seen:
            seen.add(span)
            spans.append(span)
    return spans


def _prune_invariant_block(block_text: str) -> Tuple[str, List[str]]:
    line_pat = re.compile(r"^(\s*(?:\*\s*)?loop\s+invariant\s+)([^;]+)(;\s*(?:\r?\n)?)$")
    lines = block_text.splitlines(keepends=True)
    kept: List[str] = []
    removed_reasons: List[str] = []
    seen_keys: Set[str] = set()
    for line in lines:
        m = line_pat.match(line)
        if not m:
            kept.append(line)
            continue
        inv = m.group(2).strip()
        if is_tautological(inv):
            removed_reasons.append("identity_or_tautology")
            continue
        key = invariant_dedup_key(inv)
        if key in seen_keys:
            removed_reasons.append("duplicate_invariant")
            continue
        seen_keys.add(key)
        kept.append(line)
    return "".join(kept), removed_reasons


def _extract_invariant_entries(block_text: str) -> List[Tuple[int, str, str, str]]:
    line_pat = re.compile(r"^(\s*(?:\*\s*)?loop\s+invariant\s+)([^;]+)(;\s*(?:\r?\n)?)$")
    entries: List[Tuple[int, str, str, str]] = []
    for i, line in enumerate(block_text.splitlines(keepends=True)):
        m = line_pat.match(line)
        if not m:
            continue
        entries.append((i, m.group(1), m.group(2).strip(), m.group(3)))
    return entries


def _extract_json_object(text: str) -> Optional[Dict]:
    if not text:
        return None
    s = text.strip()
    try:
        obj = json.loads(s)
        return obj if isinstance(obj, dict) else None
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", s)
    if not m:
        return None
    try:
        obj = json.loads(m.group(0))
        return obj if isinstance(obj, dict) else None
    except Exception:
        return None


def _llm_semantic_dedup_invariant_block(
    block_text: str,
    llm_cfg: LLMConfig,
    logger: Optional[logging.Logger] = None,
) -> Tuple[str, int]:
    entries = _extract_invariant_entries(block_text)
    if len(entries) < 2:
        return block_text, 0

    invs = [expr for _, _, expr, _ in entries]
    prompt = (
        "You are deduplicating ACSL loop invariants.\n"
        "Task: remove only logically redundant invariants that are implied by others.\n"
        "Do NOT remove stronger invariants in favor of weaker ones.\n"
        "Do NOT rewrite expressions.\n"
        "Return strict JSON only: {\"remove_indices\": [int,...]}.\n"
        "Indices are 0-based within this list:\n"
    )
    for i, inv in enumerate(invs):
        prompt += f"{i}: {inv}\n"
    prompt += (
        "Rules:\n"
        "- Remove exact duplicates and obvious semantic duplicates/subsumed bounds.\n"
        "- If uncertain, keep the invariant.\n"
        "- Never return indices outside range.\n"
        "- Prefer minimal removals.\n"
    )

    try:
        dedup_cfg = copy.copy(llm_cfg)
        dedup_cfg.api_temperature = 0.0
        bot = Chatbot(dedup_cfg)
        resp = bot.chat(prompt)
        obj = _extract_json_object(resp)
        if not obj:
            if logger:
                logger.info("LLM dedup skipped: non-JSON response")
            return block_text, 0
        raw_indices = obj.get("remove_indices", [])
        if not isinstance(raw_indices, list):
            return block_text, 0
        remove_idx = set()
        for x in raw_indices:
            try:
                xi = int(x)
            except Exception:
                continue
            if 0 <= xi < len(entries):
                remove_idx.add(xi)
        if not remove_idx:
            return block_text, 0

        lines = block_text.splitlines(keepends=True)
        remove_line_indices = {entries[i][0] for i in sorted(remove_idx)}
        kept_lines = [line for i, line in enumerate(lines) if i not in remove_line_indices]
        return "".join(kept_lines), len(remove_line_indices)
    except Exception as e:
        if logger:
            logger.warning(f"LLM dedup failed, skip this block: {e}")
        return block_text, 0


def postprocess_invariants_for_quality(
    annotated_code: str,
    llm_cfg: Optional[LLMConfig] = None,
    logger: Optional[logging.Logger] = None,
) -> Tuple[str, List[Dict[str, str]]]:
    use_llm_semantic_dedup = bool(_lf_cfg("llm_semantic_dedup_enabled", False))
    blocks = _attached_invariant_blocks(annotated_code)
    if not blocks:
        return annotated_code, []

    new_code = annotated_code
    shift = 0
    removed_any_rule = False
    removed_any_llm = False
    for start, end in blocks:
        s = start + shift
        e = end + shift
        block = new_code[s:e]
        pruned, reasons = _prune_invariant_block(block)
        if reasons:
            removed_any_rule = True
        updated_block = pruned
        if use_llm_semantic_dedup and llm_cfg is not None:
            llm_dedup_block, llm_removed = _llm_semantic_dedup_invariant_block(updated_block, llm_cfg, logger=logger)
            if llm_removed > 0:
                updated_block = llm_dedup_block
                removed_any_llm = True
        if updated_block != block:
            new_code = new_code[:s] + updated_block + new_code[e:]
            shift += len(updated_block) - (e - s)

    rejected_items: List[Dict[str, str]] = []
    if removed_any_rule or removed_any_llm:
        rejected_items.append({"reason": "pre_invariant_dedup", "code": annotated_code})
    return new_code, rejected_items


def strip_blank_lines(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if line.strip())


def quality_gate(gen: InvariantGenerator, raw_code: str, annotated_code: str) -> Tuple[bool, str]:
    input_loops = count_loops(raw_code)
    if input_loops < 1:
        return False, "no loop in input"
    covered_loops, total_loops = count_loops_with_invariants(annotated_code)
    if total_loops < input_loops:
        return False, f"loop count mismatch after generation: {total_loops}/{input_loops}"
    if covered_loops < input_loops:
        return False, f"missing loop invariants: {covered_loops}/{input_loops}"

    invariants = gen._extract_invariants_from_code(annotated_code)
    if not invariants:
        return False, "empty invariants"
    if any(is_tautological(inv) for inv in invariants):
        return False, "contains tautology"
    if not [inv for inv in invariants if is_nontrivial_inv(inv)]:
        return False, "no nontrivial invariants"

    per_loop_invs = extract_per_loop_invariants(annotated_code)
    if len(per_loop_invs) < input_loops:
        return False, f"per-loop invariant extraction mismatch: {len(per_loop_invs)}/{input_loops}"

    if not gen.sampler.records or len(gen.sampler.records) < input_loops:
        return False, f"loop records missing: {len(gen.sampler.records) if gen.sampler.records else 0}/{input_loops}"

    for i in range(input_loops):
        loop_content = gen.sampler.records[i].get("loop_content", "")
        loop_invs = per_loop_invs[i]

        if len(loop_invs) < 2:
            return False, f"loop {i}: too few invariants"
        if any(is_tautological(inv) for inv in loop_invs):
            return False, f"loop {i}: contains tautology"
        useful_invs = [inv for inv in loop_invs if is_nontrivial_inv(inv)]
        if not useful_invs:
            return False, f"loop {i}: no nontrivial invariants"

        if has_repetitive_loop_updates(loop_content):
            return False, f"loop {i}: repetitive loop updates"
        updated_vars = extract_updated_vars(loop_content)
        if not updated_vars:
            return False, f"loop {i}: no updated vars extracted from loop"
        loop_var = gen._extract_loop_variable(loop_content) if loop_content else None
        non_loop_updated = [v for v in sorted(updated_vars) if v != loop_var]
        # Allow counter-only loops as long as loop-variable invariants remain sound.

        vars_to_cover = set(updated_vars)
        if loop_var:
            vars_to_cover.add(loop_var)

        for v in sorted(vars_to_cover):
            if not any(re.search(rf"\b{re.escape(v)}\b", inv) for inv in useful_invs):
                return False, f"loop {i}: var lacks nontrivial invariant: {v}"

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
                return False, f"loop {i}: insufficient equality coverage: {eq_covered}/{len(non_loop_updated)}"

        # Loop variable should have explicit lower + upper bound.
        # Exception: canonical infinite loop `while(1)` does not require this bound pair.
        if loop_var and not is_canonical_infinite_loop(loop_content):
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
                return False, f"loop {i}: loop var lacks explicit bounds: {loop_var}"

    if not has_no_assert(raw_code):
        return False, "input unexpectedly contains assert"
    return True, "ok"


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


def generate_one_loop(out_dir: Path, seed: int, lf_overrides: Dict[str, object], force_core: Optional[str] = None) -> Path:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    hp = loop_factory_hyperparams(seed, out_dir, lf_overrides)
    cmd = _loop_factory_base_cmd(hp, force_core=force_core)
    subprocess.run(cmd, check=True)
    c_files = sorted(out_dir.glob("*.c"), key=lambda p: int(p.stem))
    if not c_files:
        raise RuntimeError("loop_factory did not generate any .c")
    return c_files[0]


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
        src_c = generate_one_loop(attempt_tmp_loops, seed, lf_overrides, force_core=force_core)
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
        annotated, post_rejected_items = postprocess_invariants_for_quality(
            annotated_raw,
            llm_cfg=llm_cfg,
            logger=logger,
        )
        annotated = strip_blank_lines(annotated)
        if out_c.exists() and annotated != annotated_raw:
            out_c.write_text(annotated, encoding="utf-8")

        ok, reason = quality_gate(gen, raw_code, annotated)
        if not ok:
            return {"ok": False, "reason": reason, "attempt": attempt, "seed": seed}

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
            "post_rejected_items": post_rejected_items,
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
        default=5,
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
    system_prompt = (SRC / "prompts" / "system_prompt.txt").read_text(encoding="utf-8")
    api_jsonl_path = work_root / "llama_factory_train_iio_api_aligned.jsonl"
    dpo_jsonl_path = work_root / "llama_factory_train_dpo.jsonl"
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
    }

    # Build in-memory dedup sets from existing raw/annotated pairs.
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
            raw_key = compute_raw_structure_key(raw_code)
            skey = compute_loop_skeleton_key(raw_code)
            raw_structures.add(raw_key)
            loop_skeleton_counts[skey] = loop_skeleton_counts.get(skey, 0) + 1
            existing_count += 1

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
         dpo_jsonl_path.open(file_mode, encoding="utf-8") as dpo_jsonl_file, \
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

                    raw_key = result["raw_structure_key"]
                    skeleton_key = compute_loop_skeleton_key(result["raw_code"])
                    if raw_key in raw_structures:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "duplicate raw structure"})
                        continue
                    if loop_skeleton_counts.get(skeleton_key, 0) >= max(1, args.max_skeleton_repeat):
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "duplicate loop skeleton"})
                        continue

                    raw_structures.add(raw_key)
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
                        "template": forced_core or "none",
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
                            "raw_structure_key": raw_key,
                            "first_pass": result["first_pass"],
                            "token_stats": result["token_stats"],
                            "loop_factory_hyperparams": result["loop_factory_hyperparams"],
                            "augmentation": {"type": "none"},
                        }
                    )
                    # Distill SFT: write all raw candidate (prompt, response) pairs
                    # without verification — enables pure knowledge-distillation training.
                    all_pairs = result.get("all_pairs", [])
                    for pr_prompt, pr_resp in all_pairs:
                        if pr_prompt and pr_resp:
                            distill_jsonl_file.write(json.dumps({
                                "instruction": result["system_prompt"],
                                "input": pr_prompt,
                                "output": pr_resp,
                            }, ensure_ascii=False) + "\n")
                    if all_pairs:
                        distill_jsonl_file.flush()
                    distill_count += len([p for p in all_pairs if p[0] and p[1]])

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
                    # (failed syntax filter, sampling filter, or Houdini pruning).
                    loop_dpo_records = result.get("loop_dpo_records", {})
                    post_rejected_items = result.get("post_rejected_items", [])
                    dpo_written = 0
                    # Keep DPO chosen exactly aligned with SFT output, with invariant dedup applied.
                    chosen_code = (result["annotated"] or "").strip()
                    # Hard guard: chosen must be the final, quality-gated, deduplicated annotation.
                    if not chosen_code:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "accepted sample has empty final chosen"})
                        continue
                    seen_rejected = set()
                    for rej in post_rejected_items:
                        rej_code = (rej.get("code", "") or "").strip()
                        if not rej_code or rej_code == chosen_code or rej_code in seen_rejected:
                            continue
                        seen_rejected.add(rej_code)
                        dpo_item = {
                            "instruction": result["system_prompt"],
                            "input": prompt_text,
                            "chosen": chosen_code,
                            "rejected": rej_code,
                        }
                        dpo_jsonl_file.write(json.dumps(dpo_item, ensure_ascii=False) + "\n")
                        dpo_written += 1
                    for _loop_idx, loop_rec in sorted(loop_dpo_records.items()):
                        pre_dedup_code = (loop_rec.get("pre_dedup_code", "") or "").strip()
                        dedup_removed = int(loop_rec.get("dedup_removed", 0) or 0)
                        if chosen_code and dedup_removed > 0 and pre_dedup_code and pre_dedup_code != chosen_code:
                            if pre_dedup_code not in seen_rejected:
                                seen_rejected.add(pre_dedup_code)
                                dpo_item = {
                                    "instruction": result["system_prompt"],
                                    "input": prompt_text,
                                    "chosen": chosen_code,
                                    "rejected": pre_dedup_code,
                                }
                                dpo_jsonl_file.write(json.dumps(dpo_item, ensure_ascii=False) + "\n")
                                dpo_written += 1
                        if not chosen_code:
                            continue
                        for rej in loop_rec.get("rejected_items", []):
                            rej_code = (rej.get("code", "") or "").strip()
                            if not rej_code or rej_code == chosen_code or rej_code in seen_rejected:
                                continue
                            seen_rejected.add(rej_code)
                            dpo_item = {
                                "instruction": result["system_prompt"],
                                "input": prompt_text,
                                "chosen": chosen_code,
                                "rejected": rej_code,
                            }
                            dpo_jsonl_file.write(json.dumps(dpo_item, ensure_ascii=False) + "\n")
                            dpo_written += 1
                    if dpo_written:
                        dpo_jsonl_file.flush()
                    else:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "accepted sample has no dpo rejects"})

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
    print(f"JSONL DPO (instruction/input/chosen/rejected): {dpo_jsonl_path}")
    print(f"JSONL Distill SFT (all raw candidates, {distill_count} items): {distill_jsonl_path}")
    print(f"Template map JSONL (file -> semantic core): {template_map_jsonl_path}")
    print(f"Reject log: {reject_path}")


if __name__ == "__main__":
    main()
