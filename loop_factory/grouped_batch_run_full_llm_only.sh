#!/usr/bin/env bash
set -euo pipefail

ROOT=/home/yangfp/SAM2INV/loop_factory
PIPELINE="$ROOT/batch_pipeline.py"

run_llm_only() {
  local ts
  ts="$(date '+%Y-%m-%d %H:%M:%S')"
  echo "[$ts] START grouped_batch_run_full_llm_only: python3 $PIPELINE $* --llm-core-gen --append"
  python3 "$PIPELINE" "$@" --llm-core-gen --append
  ts="$(date '+%Y-%m-%d %H:%M:%S')"
  echo "[$ts] DONE grouped_batch_run_full_llm_only: python3 $PIPELINE $* --llm-core-gen --append"
}


# LLM-only full sweep.
# This script does not pass --allowed-templates, so batch_pipeline probes and
# balances across all usable semantic cores under each budget configuration.
#
# Note: current loop_factory behavior for --llm-core-gen is "try LLM first, then
# fall back internally if needed". This script removes the baseline DSL pass, but
# does not change that internal fallback policy.

# =========================
# Compact single-loop sweeps
# =========================
# run_llm_only --num-candidates 5 --work-dir test --target-count 80 --workers 20 --p-nonlinear 0.0  --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0
# run_llm_only --num-candidates 5 --work-dir test --target-count 80 --workers 20 --p-nonlinear 0.0  --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0
# run_llm_only --num-candidates 5 --work-dir test --target-count 80 --workers 20 --p-nonlinear 1.0  --max-params 2 --min-params 1 --min-vars 2 --max-vars 6 --max-assign 6 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0
# run_llm_only --num-candidates 5 --work-dir test --target-count 80 --workers 20 --p-nonlinear 1.0  --max-params 1 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0

# =========================
# High-density single-loop sweeps
# =========================
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.08 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 12 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.12 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 11 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.92 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 12 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.95 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 11 --min-assign 4 --max-ifelse 4 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.55 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 12 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0

# =========================
# Structural mix sweeps
# =========================
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.08 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0  --q-nest 0.0  --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.12 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 1 --p-multi 0.15 --q-nest 0.0  --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.94 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0  --q-nest 0.0  --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.96 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 1 --p-multi 0.12 --q-nest 0.0  --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.58 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 2 --p-multi 0.16 --q-nest 0.08 --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 120 --workers 6 --p-nonlinear 0.50 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 1 --p-multi 0.18 --q-nest 0.0  --p-semantic-core 1.0

# =========================
# Branch-heavy sweeps
# =========================
run_llm_only --num-candidates 8 --work-dir test --target-count 100 --workers 6 --p-nonlinear 0.40 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 11 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0  --q-nest 0.0  --p-semantic-core 1.0
run_llm_only --num-candidates 8 --work-dir test --target-count 100 --workers 6 --p-nonlinear 0.35 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 5 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 2 --p-multi 0.14 --q-nest 0.08 --p-semantic-core 1.0

# =========================
# Coverage recovery sweeps
# =========================
run_llm_only --num-candidates 5 --work-dir test --target-count 160 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 8 --max-assign 6 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0
run_llm_only --num-candidates 5 --work-dir test --target-count 200 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0
