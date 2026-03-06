#!/usr/bin/env python3
"""
Reverse Chain-of-Thought generation for loop invariant training data.

Given a (system_prompt, user_prompt, code_output) triple, generates a
<think>...</think> reasoning trace that explains how an expert would
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
Given a loop invariant synthesis task and a proposed solution, generate a brief
chain-of-thought (3-8 sentences) explaining how an expert would reason to arrive
at that solution. Output ONLY inside <think>...</think> tags. Be concise and technical."""

REVERSE_COT_USER = """## Task Context
{system_summary}

## Problem
{user_prompt}

## Proposed Solution
{code_output}

Generate the reasoning trace."""

_THINK_RE = re.compile(r"<think>(.*?)</think>", re.DOTALL)


def _extract_think_block(text: str) -> str:
    """Extract <think>...</think> block from LLM response."""
    m = _THINK_RE.search(text)
    if m:
        return f"<think>{m.group(1).strip()}</think>"
    # If no tags but content looks like a reasoning trace (short, no code fences),
    # wrap it automatically.
    text = text.strip()
    if text and "```" not in text and len(text) < 2000:
        return f"<think>{text}</think>"
    return ""


def generate_reverse_cot(
    system_prompt: str,
    user_prompt: str,
    code_output: str,
    client,
    model: str,
    temperature: float = 0.7,
    max_tokens: int = 512,
    max_retries: int = 3,
) -> str:
    """Single reverse-COT generation with retry. Returns <think>...</think> or empty string."""
    # Truncate system prompt to a summary for the reverse-COT prompt
    system_summary = system_prompt[:500] + ("..." if len(system_prompt) > 500 else "")
    user_msg = REVERSE_COT_USER.format(
        system_summary=system_summary,
        user_prompt=user_prompt,
        code_output=code_output,
    )
    for attempt in range(max_retries):
        try:
            resp = client.chat.completions.create(
                model=model,
                messages=[
                    {"role": "system", "content": REVERSE_COT_SYSTEM},
                    {"role": "user", "content": user_msg},
                ],
                temperature=temperature,
                max_tokens=max_tokens,
            )
            raw = (resp.choices[0].message.content or "").strip()
            cot = _extract_think_block(raw)
            if cot:
                return cot
            log.warning("Empty COT extraction (attempt %d/%d)", attempt + 1, max_retries)
        except Exception as exc:
            log.warning("COT API error (attempt %d/%d): %s", attempt + 1, max_retries, exc)
            if attempt < max_retries - 1:
                time.sleep(2.0)
    return ""


def _hash_str(s: str) -> str:
    return hashlib.md5(s.encode("utf-8")).hexdigest()[:16]


def generate_reverse_cots_batch(
    tasks: List[Dict],
    client,
    model: str,
    max_workers: int = 16,
    temperature: float = 0.7,
    max_tokens: int = 512,
) -> Dict[Tuple[str, str], str]:
    """
    Batch-generate reverse COTs with deduplication.

    Args:
        tasks: List of dicts with keys: system_prompt, user_prompt, code_output
        client: OpenAI-compatible client
        model: Model name
        max_workers: Thread pool size

    Returns:
        Mapping from (prompt_hash, code_hash) -> "<think>...</think>"
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
    """Prepend COT block to code. If cot is empty, return code unchanged."""
    if not cot:
        return code
    return f"{cot}\n\n{code}"


def lookup_cot(cot_map: Dict[Tuple[str, str], str], user_prompt: str, code: str) -> str:
    """Look up a COT from the batch results map."""
    key = (_hash_str(user_prompt), _hash_str(code))
    return cot_map.get(key, "")
