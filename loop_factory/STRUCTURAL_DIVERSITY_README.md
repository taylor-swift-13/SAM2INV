# Structural Diversity Evaluation

This note documents the control-flow and skeleton diversity metric used to compare benchmark loop sets against `generated/test/annotated`.

## Scope

Datasets evaluated:
- `linear`: `/home/yangfp/SAM2INV/src/input/linear`
- `NLA_lipus`: `/home/yangfp/SAM2INV/src/input/NLA_lipus`
- `question`: `/home/yangfp/SAM2INV/src/input/question`
- `benchmark_all`: union of `linear + NLA_lipus + question`
- `annotated`: `/home/yangfp/SAM2INV/loop_factory/generated/test/annotated`

Implementation:
- metric script: `scripts/evaluate_structural_diversity.py:1`
- results JSON: `analysis/structural_diversity/results.json:1`
- table figure: `analysis/structural_diversity/results_table.png`

## Metric

The metric has two components.

### 1. Control-flow diversity

Each C file is mapped to a control-flow signature built from:
- number of `while`
- number of `for`
- number of `while(1)`
- number of `break`
- number of `if`
- number of `else if`
- number of `else`
- maximum `if-else` chain length
- maximum loop nesting depth
- whether modulo-based guards appear
- whether `return` appears

This measures how varied the loop/control organization is.

### 2. Skeleton diversity

Each C file is also mapped to a loop skeleton key using the existing `compute_loop_skeleton_key(...)` implementation from `batch_pipeline.py`.

This key normalizes away superficial differences such as:
- variable renaming
- whitespace and comments
- common statement-form variations
- some constant-level differences

This measures how varied the loop bodies are at the structural skeleton level.

### 3. Scores

For both control-flow signatures and skeleton keys:

- `unique_ratio = unique_signatures / total_files`
- `normalized_entropy = entropy(signature_distribution) / log2(min(total_files, unique_signatures))`
- `component_score = 0.5 * unique_ratio + 0.5 * normalized_entropy`

Final score:

- `total_score = 0.5 * control_score + 0.5 * skeleton_score`

Interpretation:
- higher `control_score` means more varied control organization
- higher `skeleton_score` means more varied normalized loop skeletons
- higher `total_score` means stronger structural diversity overall

## Final Statistics

| Dataset | Files | Control Unique | Skeleton Unique | Control Score | Skeleton Score | Total Score |
|---|---:|---:|---:|---:|---:|---:|
| linear | 316 | 26 | 119 | 0.343 | 0.652 | 0.498 |
| NLA_lipus | 50 | 8 | 34 | 0.438 | 0.817 | 0.628 |
| question | 200 | 21 | 152 | 0.374 | 0.865 | 0.619 |
| benchmark_all | 566 | 45 | 296 | 0.325 | 0.731 | 0.528 |
| annotated | 1502 | 41 | 1166 | 0.350 | 0.880 | 0.615 |

## Reading the current result

- `annotated` is clearly stronger than `benchmark_all` on skeleton diversity: `0.880` vs `0.731`
- `annotated` is only slightly above `benchmark_all` on control-flow diversity: `0.350` vs `0.325`
- `annotated` therefore has a higher total structural diversity score than `benchmark_all`: `0.615` vs `0.528`
- the current gap is mainly due to skeleton diversity, not control-flow diversity

Practical conclusion:
- `generated/test/annotated` is not structurally narrow overall
- but its control-flow diversity is still much flatter than its skeleton diversity
- if more diversity is needed, the next useful expansion target is control-flow shape rather than simple arithmetic-body variation

## Reproduce

Generate JSON:

```bash
python3 scripts/evaluate_structural_diversity.py --json > analysis/structural_diversity/results.json
```

Generate text table:

```bash
python3 scripts/evaluate_structural_diversity.py
```

Render the PNG table:

```bash
python3 scripts/render_structural_diversity_table.py \
  --input analysis/structural_diversity/results.json \
  --output analysis/structural_diversity/results_table.png
```
