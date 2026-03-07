# Dataset Files Summary

| File | Main Fields | COT Required | COT Source | Notes |
|---|---|---|---|---|
| `generated/test/llama_factory_train_iio_api_aligned.jsonl` | `instruction`, `input`, `output` | `output` must have `<reasoning>+<code>` | reverse-cot (Phase#1) | Same composed solution should match `dpo_teacher.chosen` / `dpo_aug.chosen`. |
| `generated/test/llama_factory_train_distill_sft.jsonl` | `instruction`, `input`, `output` | `output` must have `<reasoning>+<code>` | original candidate cot+code | No reverse-cot rewrite. |
| `generated/test/llama_factory_train_dpo_teacher.jsonl` | `instruction`, `input`, `chosen`, `rejected` | both `chosen` and `rejected` must have `<reasoning>+<code>` | `chosen`: reverse-cot (Phase#1); `rejected`: original candidate cot+code | `rejected` is kept as failed/raw candidate output. |
| `generated/test/llama_factory_train_dpo_aug.jsonl` | `instruction`, `input`, `chosen`, `rejected` | both `chosen` and `rejected` must have `<reasoning>+<code>` | `chosen`: reverse-cot (Phase#1); `rejected`: reverse-cot-rejected (Phase#2) | Uses second cot pass for augmented rejected branch. |
| `generated/teacher/llama_factory_train_dpo_spec.jsonl` | `instruction`, `input`, `chosen`, `rejected` | both `chosen` and `rejected` must have `<reasoning>+<code>` in cot output | `chosen`: unchanged (no reverse-cot rewrite); `rejected`: original failed output cot+code | Produced by `generate_dpo_spec.py`; no `error_type` / `verify_meta` fields. |

## Consistency Rules

- Missing required COT records are dropped before final write.
- For the same normalized composed code, these three fields should be text-identical:
  - `iio_api_aligned.output`
  - `dpo_teacher.chosen`
  - `dpo_aug.chosen`
