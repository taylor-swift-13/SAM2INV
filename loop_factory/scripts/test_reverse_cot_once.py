#!/usr/bin/env python3
"""One-shot or repeated reverse COT call diagnostic."""

from pathlib import Path
import sys
import argparse


def run_once() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(repo_root / "loop_factory"))
    sys.path.insert(0, str(repo_root / "src"))

    from config import LLMConfig
    import openai
    import reverse_cot

    cfg = LLMConfig()
    client = openai.OpenAI(base_url=cfg.base_url, api_key=cfg.api_key)

    system_prompt = "Derive loop invariants from code behavior."
    user_prompt = "Generate reasoning only."
    code_output = """int main(){
  int i=0,n=10,s=0;
  /*@ loop invariant 0 <= i <= n; loop invariant s >= 0; loop assigns i,s; */
  while(i<n){ s += i; i++; }
}"""

    user_msg = reverse_cot.REVERSE_COT_USER.format(
        system_summary=system_prompt,
        user_prompt=user_prompt,
        code_output=code_output,
    )

    resp = client.chat.completions.create(
        model=cfg.api_model,
        messages=[
            {"role": "system", "content": reverse_cot.REVERSE_COT_SYSTEM},
            {"role": "user", "content": user_msg},
        ],
        temperature=0.7,
        max_tokens=1024,
    )

    choice = resp.choices[0]
    msg = choice.message
    raw = reverse_cot._coerce_content_to_text(getattr(msg, "content", None))

    print("MODEL:", cfg.api_model)
    print("BASE_URL:", cfg.base_url)
    print("FINISH_REASON:", getattr(choice, "finish_reason", None))
    print("CONTENT_TYPE:", type(getattr(msg, "content", None)).__name__)
    print("RAW_LEN:", len(raw))
    print("RAW_PREVIEW:", repr(raw[:300]))

    helper_out = reverse_cot.generate_reverse_cot(
        system_prompt=system_prompt,
        user_prompt=user_prompt,
        code_output=code_output,
        client=client,
        model=cfg.api_model,
        max_retries=1,
    )
    print("---")
    print("HELPER_OUT_LEN:", len(helper_out))
    print("HELPER_OUT_PREVIEW:", repr(helper_out[:300]))
    return 0


def run_many(n: int) -> int:
    ok_raw = 0
    empty_raw = 0
    errors = 0
    for i in range(1, n + 1):
        try:
            print(f"===== RUN {i} =====")
            run_once()
            # Heuristic: run_once already prints RAW_LEN; do one lightweight re-check here.
            # Keep counters by invoking once more with max_retries=1 through helper path.
            # We avoid deep parsing to keep this script simple and robust.
            # Count success based on execution success only.
            ok_raw += 1
        except Exception as exc:
            errors += 1
            print(f"RUN {i} ERROR: {type(exc).__name__}: {exc}")
        print()
    print("===== SUMMARY =====")
    print("requested_runs:", n)
    print("completed_runs:", ok_raw)
    print("errors:", errors)
    print("note: inspect each RUN block for FINISH_REASON and RAW_LEN")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--runs", type=int, default=1, help="Number of repeated runs")
    args = parser.parse_args()
    if args.runs <= 1:
        return run_once()
    return run_many(args.runs)


if __name__ == "__main__":
    raise SystemExit(main())
