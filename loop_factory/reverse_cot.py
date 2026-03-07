#!/usr/bin/env python3
"""
Reverse Chain-of-Thought generation for loop invariant training data.

Given a (system_prompt, user_prompt, code_output) triple, generates a
<reasoning>...</reasoning> reasoning trace that explains how an expert would
arrive at the given solution.
"""
from __future__ import annotations

import hashlib
import logging
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Optional, Tuple

log = logging.getLogger(__name__)

REVERSE_COT_SYSTEM = """You are a formal verification reasoning assistant.
Given a C loop program with ACSL annotations (the solution), generate a first-person
chain-of-thought (3-8 sentences) explaining the reasoning steps to arrive at those
specific invariants.

REQUIREMENTS:
- You MUST reference specific variable names from the code (e.g., "q3 decreases by 3")
- You MUST explain WHY each key invariant holds (e.g., "since z is never modified, z == 9")
- You MUST connect invariants to the loop structure (guard, body, initialization)
- Use first-person perspective ("I notice...", "I need to track...")
- Output ONLY inside <reasoning>...</reasoning> tags

FORBIDDEN:
- Do NOT output generic strategies like "identify loop-updated variables"
- Do NOT paraphrase or quote the prompt instructions
- Do NOT use phrases like "keep invariants strong enough" without specific justification
- Every sentence must reference a concrete variable, expression, or code construct"""

REVERSE_COT_REJECTED_SYSTEM = """You are a formal verification reasoning assistant.
Given a C loop program with ACSL annotations that FAILED verification, generate a
first-person chain-of-thought (3-8 sentences) showing plausible but flawed reasoning
that would lead to these incorrect invariants.

REQUIREMENTS:
- Reference specific variable names and invariants from the code
- Show a reasoning process that seems logical but has a subtle flaw
- The flaw should relate to why the invariants are insufficient or incorrect
  (e.g., missing a bound, wrong relationship between variables, off-by-one)
- Use first-person perspective ("I think...", "I assume...")
- Output ONLY inside <reasoning>...</reasoning> tags

FORBIDDEN:
- Do NOT output generic strategies
- Do NOT paraphrase the prompt instructions
- Every sentence must reference a concrete variable, expression, or code construct"""

REVERSE_COT_USER = """## Task Context
{system_summary}

## Problem
{user_prompt}

## Proposed Solution
{code_output}

Generate the reasoning trace."""

_REASONING_RE = re.compile(r"<reasoning>(.*?)</reasoning>", re.DOTALL)
# Also match <think> in case the model still uses it
_THINK_RE = re.compile(r"<think>(.*?)</think>", re.DOTALL)


def _coerce_content_to_text(content) -> str:
    """Convert provider-specific message content shapes into plain text."""
    if content is None:
        return ""
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts: List[str] = []
        for p in content:
            if isinstance(p, str):
                parts.append(p)
                continue
            if isinstance(p, dict):
                t = p.get("text")
                if isinstance(t, str):
                    parts.append(t)
                    continue
                text_obj = p.get("text", {})
                if isinstance(text_obj, dict):
                    val = text_obj.get("value")
                    if isinstance(val, str):
                        parts.append(val)
                        continue
                continue
            t = getattr(p, "text", None)
            if isinstance(t, str):
                parts.append(t)
                continue
            text_obj = getattr(p, "text", None)
            if hasattr(text_obj, "value") and isinstance(getattr(text_obj, "value"), str):
                parts.append(getattr(text_obj, "value"))
                continue
        return "\n".join(x for x in parts if x).strip()
    return str(content).strip()


def _extract_think_block(text: str) -> str:
    """Extract <reasoning>...</reasoning> (or <think>) block from LLM response."""
    m = _REASONING_RE.search(text)
    if m:
        return f"<reasoning>\n{m.group(1).strip()}\n</reasoning>"
    # Fallback: model may still produce <think> tags
    m = _THINK_RE.search(text)
    if m:
        return f"<reasoning>\n{m.group(1).strip()}\n</reasoning>"
    # No tags found: return empty to trigger retry instead of wrapping arbitrary text.
    return ""


_TEMPLATE_PHRASES = [
    "Identify loop-updated variables and write an inductive relation",
    "Add minimal bounds for counters and preserved parameters",
    "Keep invariants strong enough so invariants with loop exit",
    "ensure loop assigns lists exactly mutated variables",
    "identify loop-updated variables",
    "write an inductive relation that links",
    "Required construction order",
]

_C_KEYWORDS = frozenset({
    'int', 'void', 'while', 'if', 'else', 'return', 'loop', 'invariant',
    'assigns', 'variant', 'assert', 'main', 'unsigned', 'char', 'long',
    'Pre', 'PLACE_HOLDER', 'PLACE_HOLDER_VERIFICATION_GOAL',
    'PLACE_HOLDER_ASSIGNMENTS', 'const', 'for', 'do', 'break', 'continue',
    'struct', 'typedef', 'include', 'define', 'sizeof', 'static', 'extern',
})


def _is_quality_cot(cot: str, code_output: str) -> bool:
    """Check that COT references concrete code elements, not generic templates."""
    if not cot:
        return False
    m = _REASONING_RE.search(cot)
    if not m:
        return False
    text = m.group(1)
    if len(text.strip()) < 50:
        return False
    # Reject template parroting
    for phrase in _TEMPLATE_PHRASES:
        if phrase.lower() in text.lower():
            return False
    # Require at least 1 concrete variable name from the code
    var_candidates = set(re.findall(r'\b([a-zA-Z_]\w*)\b', code_output))
    var_candidates -= _C_KEYWORDS
    return any(var in text for var in var_candidates)


def _generate_reverse_cot_impl(
    system_prompt: str,
    user_prompt: str,
    code_output: str,
    client,
    model: str,
    cot_system: str,
    temperature: float = 0.7,
    max_tokens: int = 1024,
    max_retries: int = 3,
) -> str:
    """Internal reverse-COT generation with retry and quality check."""
    user_msg = REVERSE_COT_USER.format(
        system_summary=system_prompt,
        user_prompt=user_prompt,
        code_output=code_output,
    )
    for attempt in range(max_retries):
        try:
            resp = client.chat.completions.create(
                model=model,
                messages=[
                    {"role": "system", "content": cot_system},
                    {"role": "user", "content": user_msg},
                ],
                temperature=temperature,
                max_tokens=max_tokens,
            )
            choice = resp.choices[0]
            msg = choice.message
            raw = _coerce_content_to_text(getattr(msg, "content", None)).strip()
            cot = _extract_think_block(raw)
            if cot and _is_quality_cot(cot, code_output):
                return cot
            if cot:
                log.warning(
                    "COT failed quality check (attempt %d/%d): template text or no variable refs",
                    attempt + 1, max_retries,
                )
            else:
                preview = raw[:240].replace("\n", "\\n")
                log.warning(
                    "Empty COT extraction (attempt %d/%d): finish_reason=%s, content_type=%s, content_len=%d, raw_preview=%r",
                    attempt + 1,
                    max_retries,
                    getattr(choice, "finish_reason", None),
                    type(getattr(msg, "content", None)).__name__,
                    len(_coerce_content_to_text(getattr(msg, "content", None))),
                    preview,
                )
        except Exception as exc:
            log.warning("COT API error (attempt %d/%d): %s", attempt + 1, max_retries, exc)
            if attempt < max_retries - 1:
                time.sleep(2.0)
    log.error("Reverse-COT generation failed after %d attempts; returning empty COT.", max_retries)
    return ""


def generate_reverse_cot(
    system_prompt: str,
    user_prompt: str,
    code_output: str,
    client,
    model: str,
    temperature: float = 0.7,
    max_tokens: int = 1024,
    max_retries: int = 3,
) -> str:
    """Generate reverse-COT for correct code (first-person, correct reasoning)."""
    return _generate_reverse_cot_impl(
        system_prompt, user_prompt, code_output,
        client, model, REVERSE_COT_SYSTEM,
        temperature=temperature, max_tokens=max_tokens, max_retries=max_retries,
    )


def generate_reverse_cot_rejected(
    system_prompt: str,
    user_prompt: str,
    code_output: str,
    client,
    model: str,
    temperature: float = 0.7,
    max_tokens: int = 1024,
    max_retries: int = 3,
) -> str:
    """Generate reverse-COT for rejected/incorrect code (plausible but flawed reasoning)."""
    return _generate_reverse_cot_impl(
        system_prompt, user_prompt, code_output,
        client, model, REVERSE_COT_REJECTED_SYSTEM,
        temperature=temperature, max_tokens=max_tokens, max_retries=max_retries,
    )


def _hash_str(s: str) -> str:
    return hashlib.md5(s.encode("utf-8")).hexdigest()[:16]


def generate_reverse_cots_batch(
    tasks: List[Dict],
    client,
    model: str,
    max_workers: int = 16,
    temperature: float = 0.7,
    max_tokens: int = 1024,
) -> Dict[Tuple[str, str], str]:
    """
    Batch-generate reverse COTs with deduplication.

    Args:
        tasks: List of dicts with keys: system_prompt, user_prompt, code_output
        client: OpenAI-compatible client
        model: Model name
        max_workers: Thread pool size

    Returns:
        Mapping from (prompt_hash, code_hash) -> "<reasoning>...</reasoning>"
    """
    # Deduplicate by (prompt_hash, code_hash)
    unique_tasks: Dict[Tuple[str, str], Dict] = {}
    for t in tasks:
        key = (_hash_str(t["user_prompt"]), _hash_str(t["code_output"]))
        if key not in unique_tasks:
            unique_tasks[key] = t

    log.info("COT batch: %d total tasks, %d unique after dedup", len(tasks), len(unique_tasks))

    results: Dict[Tuple[str, str], str] = {}

    def _worker(key: Tuple[str, str], task: Dict) -> Tuple[Tuple[str, str], str]:
        cot = generate_reverse_cot(
            task["system_prompt"],
            task["user_prompt"],
            task["code_output"],
            client,
            model,
            temperature=temperature,
            max_tokens=max_tokens,
        )
        return key, cot

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = {
            pool.submit(_worker, k, t): k
            for k, t in unique_tasks.items()
        }
        done_count = 0
        for fut in as_completed(futures):
            try:
                key, cot = fut.result()
                results[key] = cot
            except Exception as exc:
                key = futures[fut]
                log.error("COT worker failed for %s: %s", key, exc)
                results[key] = ""
            done_count += 1
            if done_count % 50 == 0 or done_count == len(futures):
                log.info("COT progress: %d / %d", done_count, len(futures))

    return results


def prepend_cot(code: str, cot: str) -> str:
    """Prepend COT block and wrap code in <code> tags. If cot is empty, return code unchanged."""
    if not cot:
        return code
    # Strip existing <code> wrapper if present
    clean = re.sub(r'<\s*code\s*>\s*', '', code, flags=re.IGNORECASE)
    clean = re.sub(r'\s*<\s*/\s*code\s*>', '', clean, flags=re.IGNORECASE)
    clean = clean.strip()
    return f"{cot}\n<code>\n{clean}\n</code>"


def lookup_cot(cot_map: Dict[Tuple[str, str], str], user_prompt: str, code: str) -> str:
    """Look up a COT from the batch results map."""
    key = (_hash_str(user_prompt), _hash_str(code))
    result = cot_map.get(key, "")
    if result:
        return result
    # Fallback: match by code_hash only (same code under different prompts)
    code_hash = _hash_str(code)
    for (_, ch), v in cot_map.items():
        if ch == code_hash and v:
            return v
    return ""
