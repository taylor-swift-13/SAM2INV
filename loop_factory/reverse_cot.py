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
Given a C loop program with ACSL annotations (the final candidate solution), produce
first-person reasoning that derives the loop invariants.

STRICT REQUIREMENTS:
- Output only the reasoning process that leads to the invariants.
- Reason in order from initialization, loop guard, and loop-body updates to the
  invariant relationships.
- Treat invariants as conclusions produced by analysis, never as pre-given facts.
- Do not evaluate, judge, or label invariants as correct/incorrect.
- Do not output summaries, meta commentary, or post-hoc explanation.
- 3-8 concise sentences in plain natural language.

OUTPUT FORMAT:
- Output only plain natural-language reasoning text.
- Do NOT output XML tags, markdown, code blocks, or any extra wrappers.
"""

REVERSE_COT_REJECTED_SYSTEM = REVERSE_COT_SYSTEM

REVERSE_COT_USER = """## Task Context
{system_summary}

## Problem
{user_prompt}

## Proposed Solution
{code_output}

Generate the reasoning trace in plain natural language only."""

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


def _extract_reasoning_text(text: str) -> str:
    """Extract plain reasoning text from model output."""
    m = _REASONING_RE.search(text)
    if m:
        return m.group(1).strip()
    # Fallback: model may still produce <think> tags
    m = _THINK_RE.search(text)
    if m:
        return m.group(1).strip()
    # Keep plain text fallback; tags are added by post-processing.
    plain = re.sub(r"<\s*code\s*>[\s\S]*?<\s*/\s*code\s*>", " ", text, flags=re.IGNORECASE)
    plain = re.sub(r"```[\s\S]*?```", " ", plain)
    return plain.strip()


_REFUSAL_RE = re.compile(
    r"\b(i\s+can(?:not|'t)|i\s+am\s+unable|sorry,\s*i\s+cannot|can't\s+assist|cannot\s+provide)\b",
    re.IGNORECASE,
)


def _is_valid_reasoning_text(cot_text: str) -> bool:
    """Minimal validation: non-empty natural language and not explicit refusal."""
    t = (cot_text or "").strip()
    if not t:
        return False
    if _REFUSAL_RE.search(t):
        return False
    return True


def _wrap_reasoning(cot_text: str) -> str:
    """Normalize plain reasoning text into canonical <reasoning> wrapper."""
    inner = re.sub(r"<\s*/?\s*reasoning\s*>", " ", cot_text, flags=re.IGNORECASE).strip()
    return f"<reasoning>\n{inner}\n</reasoning>"


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
    """Internal reverse-COT generation with retry and minimal validation."""
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
            cot_text = _extract_reasoning_text(raw)
            if _is_valid_reasoning_text(cot_text):
                return cot_text
            preview = raw[:240].replace("\n", "\\n")
            log.warning(
                "Empty/invalid COT text (attempt %d/%d): finish_reason=%s, content_type=%s, content_len=%d, raw_preview=%r",
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
    log.error("Reverse-COT generation failed after %d attempts; returning empty COT text.", max_retries)
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
        Mapping from (prompt_hash, code_hash) -> plain reasoning text
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


def prepend_cot(code: str, cot_text: str) -> str:
    """Prepend wrapped reasoning and wrap code in <code> tags."""
    if not cot_text:
        return code
    # Strip existing <code> wrapper if present
    clean = re.sub(r'<\s*code\s*>\s*', '', code, flags=re.IGNORECASE)
    clean = re.sub(r'\s*<\s*/\s*code\s*>', '', clean, flags=re.IGNORECASE)
    clean = clean.strip()
    wrapped_cot = _wrap_reasoning(cot_text)
    return f"{wrapped_cot}\n<code>\n{clean}\n</code>"


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
