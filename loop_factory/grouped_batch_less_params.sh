#!/usr/bin/env bash
set -euo pipefail

# Directly self-estimated from current generated/test/raw by matching generated
# loops to benchmark-template feature centroids (not copied from prior helper scripts).
#
# Clearly sparse templates under that analysis:
# - zero / near-zero: N13_affine_geometric, N3_square_sum,
#   L20_decaying_stride, L4_conservation, L5_countdown_triple,
#   L9_sliding_window, L1_affine_accumulator
# - weak but nonzero: L16_min_tracking, L19_linked_countdown,
#   L18_sawtooth_modular, L17_geometric_doubling, L2_countdown,
#   L6_snapshot_chase, L15_multi_countdown
#
# Requirement: every group is run twice:
# 1) baseline DSL path
# 2) LLM-enhanced core generation path

ROOT=/home/yangfp/SAM2INV/loop_factory
PIPELINE="$ROOT/batch_pipeline.py"

run_pair() {
  python3 "$PIPELINE" "$@" --append
  python3 "$PIPELINE" "$@" --llm-core-gen --append
}

# =========================
# Zero / near-zero linear semantics
# =========================
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L1_affine_accumulator,L4_conservation
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L5_countdown_triple,L19_linked_countdown
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L9_sliding_window,L20_decaying_stride

# =========================
# Weak linear state / countdown / modular semantics
# =========================
run_pair --num-candidates 5 --work-dir test --target-count 12 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L2_countdown,L16_min_tracking
run_pair --num-candidates 5 --work-dir test --target-count 12 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L17_geometric_doubling,L18_sawtooth_modular
run_pair --num-candidates 5 --work-dir test --target-count 12 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L6_snapshot_chase,L15_multi_countdown

# =========================
# Zero / near-zero NLA semantics
# =========================
run_pair --num-candidates 5 --work-dir test --target-count 12 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N3_square_sum
run_pair --num-candidates 5 --work-dir test --target-count 12 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N13_affine_geometric
