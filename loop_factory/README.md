# loop_factory

`loop_factory` synthesizes C loop programs using a DSL-based generator and provides pipelines to batch-generate verification tasks.

## What It Produces

- C programs formatted for the SAM2INV pipeline input style.
- Single-loop or multi-loop programs (based on configuration).
- Linear and nonlinear loop families controlled by probability parameters.

The generated programs are intended to be consumed by `src/loop_inv.py` and batch pipelines.

## Main Scripts

- `loop_factory.py`: core program generator.
- `batch_pipeline.py`: end-to-end generation + invariant generation + quality gating.
- `one_sample_pipeline.py`: single-sample workflow.
- `sft_pipeline.py`: prompt evaluation and dataset-style workflow.

## Quick Start

Generate 50 programs:

```bash
cd loop_factory
python3 loop_factory.py --profile benchmark --out-dir generated/demo --count 50 --seed 2026
```

Generate richer programs:

```bash
python3 loop_factory.py \
  --profile rich \
  --out-dir generated/rich_demo \
  --count 100 \
  --seed 2026 \
  --params 3 \
  --max-loops 6 \
  --max-depth 2 \
  --p-multi 0.45 \
  --q-nest 0.15
```

## `loop_factory.py` Key Parameters

- `--profile`: `benchmark` or `rich`
- `--out-dir`: output directory
- `--count`: number of C files
- `--seed`: random seed
- `--max-vars`: maximum variable count
- `--params`: function parameter count
- `--min-loops`, `--max-loops`: while-loop count bounds
- `--max-assign`: max assignments per loop
- `--max-ifelse`: max if/else blocks per loop
- `--max-depth`: max nesting depth
- `--p-multi`: loop continuation probability
- `--q-nest`: loop nesting probability
- `--p-nonlinear`: probability of nonlinear loop family
- `--p-semantic-core`: probability of semantic-core injection

Note: advanced semantic-core weight options exist in `loop_factory.py`, but higher-level workflows can hide them.

## `batch_pipeline.py` Configuration

`batch_pipeline.py` reads defaults from `src/config.py` under `LOOP_FACTORY_USER_CONFIG`.

User-facing knobs include:

- Runtime: `target_count`, `max_attempts`, `seed`, `workers`, `model`, `max_skeleton_repeat`
- Complexity: `lf_max_vars`, `lf_params`, `lf_min_loops`, `lf_max_loops`, `lf_max_assign`, `lf_max_ifelse`, `lf_max_depth`, `lf_p_multi`, `lf_q_nest`, `lf_p_nonlinear`, `lf_p_semantic_core`

Equivalent CLI flags are available with `--lf-*` names for these exposed fields.

## Output

Typical outputs include:

- Generated C files (`1.c`, `2.c`, ...)
- Logs and intermediate artifacts under `loop_factory/generated/`
- Accepted samples that can be copied into `src/input/<subdir>/` for verification runs

## Notes

- Current repository state removes cache-based prompt/reference logic from the invariant generation path.
- Keep `src/config.py` and `loop_factory` parameters aligned when tuning generation complexity.
