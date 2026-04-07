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

# Expanded semantic run-pair suite:
# - merges the single-loop high-density groups from grouped_batch_large_semantic_loops.sh
# - merges the structural mix groups from grouped_batch_high_budget_suite.sh
# - adds extra branch-heavy groups using existing supported templates/cores

# =========================
# Single-loop high-density semantic groups
# =========================
run_pair --num-candidates 8 --work-dir test --target-count 90 --workers 6 --p-nonlinear 0.08 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 12 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates mod_bucket_cascade,remainder_buckets,equal_pair_piecewise_increment,phase_switch,turn_based_state_machine
run_pair --num-candidates 8 --work-dir test --target-count 90 --workers 6 --p-nonlinear 0.12 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 11 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates linear_conservation_family,cache_coherence,multi_countdown_parallel,min_update_guarded_bound,ramped_transfer_conservation,carry_pair_counter,alternating_swap_transfer,scheduled_queue_occupancy
run_pair --num-candidates 8 --work-dir test --target-count 90 --workers 6 --p-nonlinear 0.92 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 12 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates multi_branch_swap_recurrence,piecewise_recurrence,qr_division_step,qr_countdown_bucket,euclid_matrix,euclid_coupled_accumulator,residual_branch_walk
run_pair --num-candidates 8 --work-dir test --target-count 90 --workers 6 --p-nonlinear 0.95 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 11 --min-assign 4 --max-ifelse 4 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates russian_multiply,triple_recurrence_inc,mul_affine_param_pair,cauchy_schwarz_triple,euclid_coupled_accumulator,power_accumulate,quadratic_form_triplet,parity_decomposition_product,alternating_series_accumulator
run_pair --num-candidates 8 --work-dir test --target-count 90 --workers 6 --p-nonlinear 0.55 --max-params 2 --min-params 0 --min-vars 6 --max-vars 11 --max-assign 12 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates mod_bucket_cascade,cache_coherence,multi_branch_swap_recurrence,qr_division_step,russian_multiply,ramped_transfer_conservation,turn_based_state_machine

# =========================
# Structural mix groups
# =========================
run_pair --num-candidates 8 --work-dir test --target-count 80 --workers 6 --p-nonlinear 0.08 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates mod_bucket_cascade,remainder_buckets,phase_switch,equal_pair_piecewise_increment,turn_based_state_machine,nondeterministic_multi_decrement
run_pair --num-candidates 8 --work-dir test --target-count 80 --workers 6 --p-nonlinear 0.12 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 1 --p-multi 0.15 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates linear_conservation_family,cache_coherence,multi_countdown_parallel,min_update_guarded_bound,ramped_transfer_conservation,carry_pair_counter,prefix_sum_family
run_pair --num-candidates 8 --work-dir test --target-count 80 --workers 6 --p-nonlinear 0.94 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates multi_branch_swap_recurrence,piecewise_recurrence,qr_division_step,qr_countdown_bucket,euclid_matrix,euclid_coupled_accumulator,residual_branch_walk
run_pair --num-candidates 8 --work-dir test --target-count 80 --workers 6 --p-nonlinear 0.96 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 1 --p-multi 0.12 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates russian_multiply,triple_recurrence_inc,mul_affine_param_pair,cauchy_schwarz_triple,power_accumulate,quadratic_form_triplet
run_pair --num-candidates 8 --work-dir test --target-count 80 --workers 6 --p-nonlinear 0.58 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 2 --p-multi 0.16 --q-nest 0.08 --p-semantic-core 1.0 --allowed-templates mod_bucket_cascade,cache_coherence,multi_branch_swap_recurrence,qr_division_step,russian_multiply,ramped_transfer_conservation,nested_grid_checkerboard,nested_block_drain,nested_block_staircase
run_pair --num-candidates 8 --work-dir test --target-count 80 --workers 6 --p-nonlinear 0.50 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 4 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 1 --p-multi 0.18 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates prefix_sum_family,linear_conservation_family,mod_bucket_cascade,qr_division_step,euclid_matrix,russian_multiply,cache_coherence

# =========================
# Extra branch-heavy groups
# =========================
run_pair --num-candidates 8 --work-dir test --target-count 80 --workers 6 --p-nonlinear 0.40 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 11 --min-assign 4 --max-ifelse 5 --min-ifelse 2 --min-loops 1 --max-loops 1 --max-depth 1 --p-multi 0.0 --q-nest 0.0 --p-semantic-core 1.0 --allowed-templates turn_based_state_machine,equal_pair_piecewise_increment,scheduled_queue_occupancy,alternating_swap_transfer,nondeterministic_multi_decrement,gap_drift_piecewise,residual_branch_walk
run_pair --num-candidates 8 --work-dir test --target-count 70 --workers 6 --p-nonlinear 0.35 --max-params 2 --min-params 0 --min-vars 5 --max-vars 10 --max-assign 10 --min-assign 4 --max-ifelse 5 --min-ifelse 1 --min-loops 1 --max-loops 2 --max-depth 2 --p-multi 0.14 --q-nest 0.08 --p-semantic-core 1.0 --allowed-templates nested_grid_checkerboard,nested_block_drain,nested_block_staircase,turn_based_state_machine,phase_switch

# =========================
# Missing templates (count=0)
# =========================
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 176 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X3_bisection --append
# =========================
# Low templates (count < 5)
# =========================
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 15 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 8 --max-assign 6 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X24_scheduled_queue_occupancy --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 46 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N9_cauchy_schwarz --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 113 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X6_newton_sqrt --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 45 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 4 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N5_quotient_remainder --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 45 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 6 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N10_russian_multiply --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 113 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X16_carry_chain --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 113 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 2 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N11_product_by_addition --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 176 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N7_geometric_affine --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 45 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N13_affine_geometric --append
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 113 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N12_squared_invariant --append