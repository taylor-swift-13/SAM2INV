#!/usr/bin/env python3
from __future__ import annotations

import argparse
import atexit
import copy
import itertools
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
from inv_generator import InvariantGenerator, is_tautological, is_nontrivial_inv  # type: ignore
from llm import LLMConfig, Chatbot, reset_token_stats, get_token_stats  # type: ignore
from houdini_pruner import HoudiniPruner  # type: ignore
from output_verify import OutputVerifier  # type: ignore

USER_CFG = getattr(config, "LOOP_FACTORY_USER_CONFIG", {})
HOUDINI_CFG = getattr(config, "HOUDINI_CONFIG", {})


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

def _aug_single_bad_rejects(code: str, validate_result: List[bool], pruner: HoudiniPruner) -> List[str]:
    """Generate rejected variants by freely combining failing invariants with all valid ones.

    Iterates over subsets of failing invariants (size 1, 2, …) in order and stops once
    2 * K distinct variants have been collected, where K = number of failing invariants.
    The full failing set (= code itself) is already in DPO; subsets that reproduce it
    are filtered out by `variant != code`.
    """
    failed_indices = [i for i, ok in enumerate(validate_result) if not ok]
    if not failed_indices:
        return []
    limit = 2 * len(failed_indices)
    out: List[str] = []
    for size in range(1, len(failed_indices) + 1):
        for combo in itertools.combinations(failed_indices, size):
            if len(out) >= limit:
                return out
            keep_flags = list(validate_result)
            for idx in combo:
                keep_flags[idx] = True
            variant = pruner.hudini_annotations(keep_flags, code, validate_result_by_line=None).strip()
            if variant and variant != code:
                out.append(variant)
    return out


def _aug_houdini_rejects(
    rejected_code: str,
    verifier: OutputVerifier,
    pruner: HoudiniPruner,
    tmp_c_path: Path,
    patience: int = 2,
) -> List[str]:
    """Run Houdini rounds on a rejected code and return fine-grained rejected variants.

    Mirrors HoudiniPruner.hudini(): uses verifier.validate_result directly (positional),
    validate_result_by_line=None, and _extract_invariants_from_code to detect empty pruning.
    Stops when all invariants become valid or the annotation is pruned empty (natural
    convergence). `patience` is a safety guard: if the pruner makes no progress for that
    many consecutive rounds (should not occur in theory), abort to prevent infinite loops.
    """
    current = (rejected_code or "").strip()
    if not current:
        return []
    new_rejects: List[str] = []
    seen: Set[str] = set()
    no_progress = 0
    while True:
        tmp_c_path.write_text(current, encoding="utf-8")
        verifier.run(str(tmp_c_path))
        if not verifier.syntax_correct:
            break
        validate_result = list(getattr(verifier, "validate_result", []) or [])
        # Mirrors hudini(): if not validate_result → break; if all valid → break
        if not validate_result or all(validate_result):
            break
        for rej in _aug_single_bad_rejects(current, validate_result, pruner):
            if rej not in seen:
                seen.add(rej)
                new_rejects.append(rej)
        prev_code = current
        current = pruner.hudini_annotations(validate_result, current, validate_result_by_line=None).strip()
        # All invariants pruned away (mirrors hudini()'s after_invariants == 0 check)
        if not pruner._extract_invariants_from_code(current):
            break
        # No-progress guard (mirrors hudini()'s defensive break; patience allows for
        # transient Houdini bugs before giving up)
        if current == prev_code:
            no_progress += 1
            if no_progress >= patience:
                break
        else:
            no_progress = 0
    return new_rejects


def _extract_invariant_spans(code: str) -> List[Tuple[int, int]]:
    inv_pat = re.compile(r"^[ \t]*loop\s+invariant\s+[^;]+;\s*\n?", flags=re.MULTILINE)
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


def _aug_weak_chosen_subset_reject(chosen_code: str, rng: random.Random, max_tries: int = 16) -> Optional[str]:
    """Aug B: sample a small proper subset from chosen as a weaker rejected target."""
    src = (chosen_code or "").strip()
    if not src:
        return None
    for _ in range(max_tries):
        subset, _k, _n = _sample_subset_code(src, rng, force_proper_subset=True)
        if subset and subset != src:
            return subset
    return None


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
    llm_cfg.think_mode_enabled = True
    system_prompt = (SRC / "prompts" / "system_prompt_cot.txt").read_text(encoding="utf-8")
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
    # Houdini DPO augmentation resources (main-thread only, single temp file)
    use_houdini_aug = bool(_lf_cfg("houdini_dpo_augment", False))
    houdini_aug_patience = int(HOUDINI_CFG.get("patience", 2))
    _aug_verifier: Optional[OutputVerifier] = None
    _aug_pruner: Optional[HoudiniPruner] = None
    _aug_tmp_c: Optional[Path] = None
    if use_houdini_aug:
        _aug_log = logging.getLogger("houdini_aug")
        _aug_verifier = OutputVerifier(logger=_aug_log, output=False)
        _aug_pruner = HoudiniPruner(logger=_aug_log)
        _aug_tmp_dir = work_root / "tmp_houdini_aug"
        _aug_tmp_dir.mkdir(parents=True, exist_ok=True)
        _aug_tmp_c = _aug_tmp_dir / "tmp.c"
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
                            dpo_teacher_jsonl_file.write(json.dumps(dpo_item, ensure_ascii=False) + "\n")
                            dpo_teacher_written += 1
                            # Houdini augmentation: "all valid + 1 bad" variants of this rejected
                            if use_houdini_aug and _aug_verifier and _aug_pruner and _aug_tmp_c:
                                for aug_code in _aug_houdini_rejects(
                                    rej_code, _aug_verifier, _aug_pruner,
                                    _aug_tmp_c, houdini_aug_patience,
                                ):
                                    aug_code = aug_code.strip()
                                    if aug_code and aug_code != chosen_code and aug_code not in seen_rejected:
                                        seen_rejected.add(aug_code)
                                        dpo_aug_jsonl_file.write(json.dumps({
                                            "instruction": result["system_prompt"],
                                            "input": prompt_text,
                                            "chosen": chosen_code,
                                            "rejected": aug_code,
                                        }, ensure_ascii=False) + "\n")
                                        dpo_aug_written += 1
                            # Augmentation C: random subset from error candidate.
                            aug_c = _aug_error_subset_reject(rej_code, aug_rng)
                            if aug_c:
                                aug_c = aug_c.strip()
                                if aug_c and aug_c != chosen_code and aug_c not in seen_rejected:
                                    seen_rejected.add(aug_c)
                                    dpo_aug_jsonl_file.write(json.dumps({
                                        "instruction": result["system_prompt"],
                                        "input": prompt_text,
                                        "chosen": chosen_code,
                                        "rejected": aug_c,
                                    }, ensure_ascii=False) + "\n")
                                    dpo_aug_written += 1
                    # Augmentation B: weak proper subset from chosen only.
                    aug_b = _aug_weak_chosen_subset_reject(chosen_code, aug_rng)
                    if aug_b:
                        aug_b = aug_b.strip()
                        if aug_b and aug_b != chosen_code and aug_b not in seen_rejected:
                            seen_rejected.add(aug_b)
                            dpo_aug_jsonl_file.write(json.dumps({
                                "instruction": result["system_prompt"],
                                "input": prompt_text,
                                "chosen": chosen_code,
                                "rejected": aug_b,
                            }, ensure_ascii=False) + "\n")
                            dpo_aug_written += 1
                    if dpo_teacher_written or dpo_aug_written:
                        dpo_teacher_jsonl_file.flush()
                        dpo_aug_jsonl_file.flush()
                    else:
                        reject_log.append({"attempt": attempt, "seed": seed, "reason": "accepted sample has no dpo rejects"})

    # ── Phase 2: Reverse-COT generation ────────────────────────────────────
    from reverse_cot import generate_reverse_cot, generate_reverse_cots_batch, prepend_cot, lookup_cot
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

    # Strip <think>...</think> and <reasoning>...</reasoning> from text (model may have produced it during inference)
    _think_strip_re = re.compile(r"<\s*think\s*>[\s\S]*?<\s*/\s*think\s*>", re.IGNORECASE)
    _reasoning_strip_re = re.compile(r"<\s*reasoning\s*>[\s\S]*?<\s*/\s*reasoning\s*>", re.IGNORECASE)
    _cot_tag_re = re.compile(r"<\s*(think|reasoning)\s*>", re.IGNORECASE)
    def _strip_think(text: str) -> str:
        text = _think_strip_re.sub("", text)
        text = _reasoning_strip_re.sub("", text)
        return text.strip()
    def _has_cot(text: str) -> bool:
        return bool(_cot_tag_re.search(text or ""))

    sft_records = _read_jsonl(api_jsonl_path)
    distill_records = _read_jsonl(distill_jsonl_path)
    dpo_teacher_records = _read_jsonl(dpo_teacher_jsonl_path)
    dpo_aug_records = _read_jsonl(dpo_aug_jsonl_path)

    # Collect tasks needing reverse-COT.
    # Policy:
    # - Composed fields (SFT.output and all chosen) always use reverse-COT, dedup by code
    #   so identical composed code only generates COT once.
    # - Candidate-direct fields (distill.output and all rejected) keep native COT if present,
    #   otherwise use reverse-COT backfill.
    forced_code_tasks: Dict[str, Dict] = {}
    ensure_cot_tasks: List[Dict] = []

    for rec in sft_records:
        code = _strip_think(rec["output"])
        if code and code not in forced_code_tasks:
            forced_code_tasks[code] = {"system_prompt": system_prompt, "user_prompt": rec["input"], "code_output": code}
    for rec in distill_records:
        if not _has_cot(rec["output"]):
            ensure_cot_tasks.append({"system_prompt": system_prompt, "user_prompt": rec["input"], "code_output": _strip_think(rec["output"])})
    for rec in dpo_teacher_records:
        code = _strip_think(rec["chosen"])
        if code and code not in forced_code_tasks:
            forced_code_tasks[code] = {"system_prompt": system_prompt, "user_prompt": rec["input"], "code_output": code}
        if not _has_cot(rec["rejected"]):
            ensure_cot_tasks.append({"system_prompt": system_prompt, "user_prompt": rec["input"], "code_output": _strip_think(rec["rejected"])})
    for rec in dpo_aug_records:
        code = _strip_think(rec["chosen"])
        if code and code not in forced_code_tasks:
            forced_code_tasks[code] = {"system_prompt": system_prompt, "user_prompt": rec["input"], "code_output": code}
        # dpo_aug.rejected is augmentation-constructed; always reverse-COT.
        rej_code = _strip_think(rec["rejected"])
        if rej_code and rej_code not in forced_code_tasks:
            forced_code_tasks[rej_code] = {"system_prompt": system_prompt, "user_prompt": rec["input"], "code_output": rej_code}

    all_cot_tasks: List[Dict] = list(forced_code_tasks.values()) + ensure_cot_tasks

    print(f"COT Phase: generating reverse-COTs for {len(all_cot_tasks)} code pieces (dedup inside)...")
    cot_map = generate_reverse_cots_batch(all_cot_tasks, cot_client, cot_model)
    cot_ok = sum(1 for v in cot_map.values() if v)
    print(f"COT Phase: {cot_ok}/{len(cot_map)} unique COTs generated successfully.")

    forced_cot_by_code: Dict[str, str] = {}
    for code, task in forced_code_tasks.items():
        cot = lookup_cot(cot_map, task["user_prompt"], code)
        if not cot:
            cot = generate_reverse_cot(system_prompt, task["user_prompt"], code, cot_client, cot_model)
        if not cot:
            raise RuntimeError("Reverse-COT generation failed for composed training sample.")
        forced_cot_by_code[code] = cot

    # If record already has COT from inference, keep it; otherwise prepend reverse-COT.
    def _ensure_cot(text: str, user_prompt: str) -> str:
        if _has_cot(text):
            return text  # already has COT from inference
        code = _strip_think(text)
        cot = lookup_cot(cot_map, user_prompt, code)
        if not cot:
            cot = generate_reverse_cot(system_prompt, user_prompt, code, cot_client, cot_model)
        if not cot:
            raise RuntimeError("Reverse-COT backfill failed: empty COT for one training sample.")
        return prepend_cot(code, cot)

    def _force_reverse_cot(text: str, user_prompt: str) -> str:
        # Composed fields are normalized to code-only then always prepended with reverse-COT.
        code = _strip_think(text)
        cot = forced_cot_by_code.get(code, "")
        if not cot:
            cot = generate_reverse_cot(system_prompt, user_prompt, code, cot_client, cot_model)
            if cot:
                forced_cot_by_code[code] = cot
        if not cot:
            raise RuntimeError("Reverse-COT generation failed for composed training sample.")
        return prepend_cot(code, cot)

    api_out_records = [{
        "instruction": system_prompt,
        "input": rec["input"],
        "output": _force_reverse_cot(rec["output"], rec["input"]),
    } for rec in sft_records]
    distill_out_records = [{
        "instruction": system_prompt,
        "input": rec["input"],
        "output": _ensure_cot(rec["output"], rec["input"]),
    } for rec in distill_records]
    dpo_teacher_out_records = [{
        "instruction": system_prompt,
        "input": rec["input"],
        "chosen": _force_reverse_cot(rec["chosen"], rec["input"]),
        "rejected": _ensure_cot(rec["rejected"], rec["input"]),
    } for rec in dpo_teacher_records]
    dpo_aug_out_records = [{
        "instruction": system_prompt,
        "input": rec["input"],
        "chosen": _force_reverse_cot(rec["chosen"], rec["input"]),
        "rejected": _force_reverse_cot(rec["rejected"], rec["input"]),
    } for rec in dpo_aug_records]

    def _assert_records_have_cot(records: List[Dict], fields: List[str], dataset_name: str) -> None:
        for i, rec in enumerate(records):
            for field in fields:
                if not _has_cot(rec.get(field, "")):
                    raise RuntimeError(f"Reverse-COT validation failed: {dataset_name}[{i}].{field} has no COT.")

    _assert_records_have_cot(api_out_records, ["output"], "api")
    _assert_records_have_cot(distill_out_records, ["output"], "distill")
    _assert_records_have_cot(dpo_teacher_out_records, ["chosen", "rejected"], "dpo_teacher")
    _assert_records_have_cot(dpo_aug_out_records, ["chosen", "rejected"], "dpo_aug")

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

    print(f"COT output written to {work_root}")

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
