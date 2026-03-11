---
name: loop-dataset-sync
description: Clean and synchronize loop-invariant training datasets under generated/test. Use when handling jsonl files (iio/dpo/distill), raw/*.c, annotated/*.c, and file_template_map.jsonl to (1) remove samples missing <reasoning>/<code> tags, (2) keep only loops that exist one-to-one across all required sources, (3) renumber files to continuous IDs (1..N), and (4) verify final consistency.
---

# Loop Dataset Sync/Clean Skill

## Required Inputs

Work in `/home/yangfp/SAM2INV/loop_factory/generated/test` with:

- `llama_factory_train_iio_api_aligned.jsonl` (`output`)
- `llama_factory_train_dpo_teacher.jsonl` (`chosen`, `rejected`)
- `llama_factory_train_dpo_aug.jsonl` (`chosen`, `rejected`)
- `llama_factory_train_distill_sft.jsonl` (`output`)
- `raw/*.c`
- `annotated/*.c`
- `file_template_map.jsonl`

## Rules

1. Keep a JSONL row only if target text fields contain all tags:
`<reasoning>`, `</reasoning>`, `<code>`, `</code>`.
2. Use loop-level intersection:
keep only loops that are present in all required sources.
3. Ensure `raw` and `annotated` are one-to-one with same ID set.
4. Renumber loop files to continuous IDs `1..N`.
5. Update `file_template_map.jsonl` (`id`, `raw_file`, `annotated_file`) to the new IDs.
6. Final state must satisfy: every source maps to exactly the same loop ID set.

## Matching Strategy (JSONL row -> loop ID)

Extract the first C code block from `input` with regex:

Code:\s*```c\n(.*?)\n```

Normalize before matching:

1. Remove placeholder loop-annotation block:
`/* >>> LOOP INVARIANT TO FILL <<< */` + following `/*@ ... */`.
2. Normalize line endings.
3. Trim trailing spaces per line.
4. Remove blank lines.
5. Collapse whitespace runs to one space.

Build normalized map from `raw/*.c` content to loop ID, then map each JSONL row by normalized `input` code.

## Execution Workflow

1. Validate JSONL field schema (`output` vs `chosen/rejected`).
2. Remove rows missing required tags from corresponding fields.
3. Compute loop ID sets per JSONL file using matching strategy.
4. Compute global intersection:
`raw_ids ∩ annotated_ids ∩ iio_ids ∩ dpo_teacher_ids ∩ dpo_aug_ids ∩ distill_ids`.
5. Delete non-intersection loops from:
- all JSONL rows
- `raw/*.c`
- `annotated/*.c`
6. Renumber remaining raw/annotated files to continuous `1..N` (two-phase rename to avoid collisions).
7. Rewrite `file_template_map.jsonl` to new IDs and paths.
8. Re-verify consistency.

## Verification Checklist

Pass only if all are true:

1. `raw` count == `annotated` count == `N`.
2. `raw` ID set == `annotated` ID set == `{1..N}`.
3. `file_template_map.jsonl` has exactly `N` rows and IDs `{1..N}`.
4. Each JSONL maps to loop ID set `{1..N}`.
5. No remaining bad tag rows in any target text field.

## Output Format

Report:

1. Rows before/after per JSONL.
2. Removed loop IDs.
3. Final `N`.
4. Verification results for `raw`, `annotated`, `file_template_map`, and all JSONL files.
