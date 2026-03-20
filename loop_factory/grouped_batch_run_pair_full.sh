#!/usr/bin/env bash
set -euo pipefail

ROOT=/home/yangfp/SAM2INV/loop_factory
PIPELINE="$ROOT/batch_pipeline.py"

run_pair() {
  python3 "$PIPELINE" "$@" --append
  python3 "$PIPELINE" "$@" --llm-core-gen --append
}

# Benchmark-used template full set (34 templates), run as baseline + llm-core-gen pairs.

# =========================
# Linear templates
# =========================
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L1_affine_accumulator,L4_conservation
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L2_countdown,L5_countdown_triple,L19_linked_countdown
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L3_proportional_stride,L20_decaying_stride
run_pair --num-candidates 5 --work-dir test --target-count 14 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L6_snapshot_chase,L14_cache_coherence
run_pair --num-candidates 5 --work-dir test --target-count 14 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L7_parity_flipflop,L13_binary_toggle
run_pair --num-candidates 5 --work-dir test --target-count 14 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L8_saturation_guard,L10_piecewise_multirate
run_pair --num-candidates 5 --work-dir test --target-count 14 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L9_sliding_window,L16_min_tracking
run_pair --num-candidates 5 --work-dir test --target-count 14 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L11_triple_modular_step,L12_monotone_increment
run_pair --num-candidates 5 --work-dir test --target-count 12 --workers 20 --p-nonlinear 0.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L15_multi_countdown,L17_geometric_doubling,L18_sawtooth_modular

# =========================
# NLA templates
# =========================
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N1_poly_finite_diff,N2_triangular_sum
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N3_square_sum,N4_higher_power_sums
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N5_quotient_remainder,N6_extended_euclid
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N7_geometric_affine,N13_affine_geometric
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N8_int_sqrt,N10_russian_multiply
run_pair --num-candidates 5 --work-dir test --target-count 16 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N9_cauchy_schwarz,N14_quadratic_piecewise
run_pair --num-candidates 5 --work-dir test --target-count 12 --workers 20 --p-nonlinear 1.0 --max-params 1 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N11_product_by_addition,N12_squared_invariant
