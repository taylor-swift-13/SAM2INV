#!/usr/bin/env python3
"""Test script to verify COT reasoning quality in generated JSONL files."""
import json
import re
import sys
from pathlib import Path

_REASONING_RE = re.compile(r"<reasoning>(.*?)</reasoning>", re.DOTALL)
_THINK_RE = re.compile(r"<think>(.*?)</think>", re.DOTALL)
_COT_TAG_RE = re.compile(r"<\s*(think|reasoning)\s*>", re.IGNORECASE)

_TEMPLATE_PHRASES = [
    "identify loop-updated variables and write an inductive relation",
    "add minimal bounds for counters and preserved parameters",
    "keep invariants strong enough so invariants with loop exit",
    "ensure loop assigns lists exactly mutated variables",
    "write an inductive relation that links",
    "required construction order",
]

_C_KEYWORDS = frozenset({
    'int', 'void', 'while', 'if', 'else', 'return', 'loop', 'invariant',
    'assigns', 'variant', 'assert', 'main', 'unsigned', 'char', 'long',
    'Pre', 'PLACE_HOLDER', 'PLACE_HOLDER_VERIFICATION_GOAL',
    'PLACE_HOLDER_ASSIGNMENTS', 'const', 'for', 'do', 'break', 'continue',
    'struct', 'typedef', 'include', 'define', 'sizeof', 'static', 'extern',
})


def extract_reasoning(text: str) -> str:
    m = _REASONING_RE.search(text)
    if m:
        return m.group(1).strip()
    m = _THINK_RE.search(text)
    if m:
        return m.group(1).strip()
    return ""


def has_cot_tag(text: str) -> bool:
    return bool(_COT_TAG_RE.search(text or ""))


def is_template(reasoning_text: str) -> bool:
    low = reasoning_text.lower()
    return any(p in low for p in _TEMPLATE_PHRASES)


def has_var_ref(reasoning_text: str, code: str) -> bool:
    var_candidates = set(re.findall(r'\b([a-zA-Z_]\w*)\b', code))
    var_candidates -= _C_KEYWORDS
    return any(v in reasoning_text for v in var_candidates)


def check_field(text: str, field_name: str, rec_idx: int) -> dict:
    result = {"field": field_name, "idx": rec_idx, "issues": []}
    if not has_cot_tag(text):
        result["issues"].append("NO_COT_TAG")
        return result
    reasoning = extract_reasoning(text)
    if not reasoning:
        result["issues"].append("EMPTY_REASONING")
        return result
    if len(reasoning) < 50:
        result["issues"].append(f"TOO_SHORT ({len(reasoning)} chars)")
    if is_template(reasoning):
        result["issues"].append("TEMPLATE_PARROT")
    # Extract code portion (after </reasoning>)
    code = re.sub(r"<reasoning>.*?</reasoning>", "", text, flags=re.DOTALL).strip()
    if code and not has_var_ref(reasoning, code):
        result["issues"].append("NO_VAR_REF")
    return result


def check_file(path: Path) -> None:
    records = []
    with path.open(encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                records.append(json.loads(line))

    if not records:
        print(f"  EMPTY FILE")
        return

    total_fields = 0
    ok_fields = 0
    issue_counts = {}

    for i, rec in enumerate(records):
        fields_to_check = []
        if "output" in rec:
            fields_to_check.append(("output", rec["output"]))
        if "chosen" in rec:
            fields_to_check.append(("chosen", rec["chosen"]))
        if "rejected" in rec:
            fields_to_check.append(("rejected", rec["rejected"]))

        for field_name, text in fields_to_check:
            total_fields += 1
            result = check_field(text, field_name, i)
            if not result["issues"]:
                ok_fields += 1
            else:
                for issue in result["issues"]:
                    issue_counts[issue] = issue_counts.get(issue, 0) + 1

    print(f"  {ok_fields}/{total_fields} fields OK")
    if issue_counts:
        for issue, count in sorted(issue_counts.items(), key=lambda x: -x[1]):
            print(f"  {issue}: {count}")

    # Show first bad example
    for i, rec in enumerate(records):
        for field_name in ["output", "chosen", "rejected"]:
            if field_name not in rec:
                continue
            result = check_field(rec[field_name], field_name, i)
            if result["issues"]:
                text = rec[field_name]
                reasoning = extract_reasoning(text)
                print(f"  Example bad [{field_name}][{i}]: issues={result['issues']}")
                if reasoning:
                    print(f"    reasoning preview: {reasoning[:120]}...")
                else:
                    print(f"    output preview: {text[:120]}...")
                return


def main():
    if len(sys.argv) > 1:
        paths = [Path(p) for p in sys.argv[1:]]
    else:
        # Default: scan generated/test/
        test_dir = Path(__file__).parent / "generated" / "test"
        paths = sorted(test_dir.glob("llama_factory_*.jsonl"))

    if not paths:
        print("No JSONL files found.")
        sys.exit(1)

    all_ok = True
    for path in paths:
        print(f"\n{path.name} ({sum(1 for _ in path.open())} records):")
        check_file(path)
        # Re-check for overall pass/fail
        with path.open() as f:
            for line in f:
                if not line.strip():
                    continue
                rec = json.loads(line)
                for field in ["output", "chosen", "rejected"]:
                    if field in rec and not has_cot_tag(rec[field]):
                        all_ok = False

    print()
    if all_ok:
        print("PASS: All output fields have COT tags.")
    else:
        print("FAIL: Some output fields are missing COT tags.")
        sys.exit(1)


if __name__ == "__main__":
    main()
