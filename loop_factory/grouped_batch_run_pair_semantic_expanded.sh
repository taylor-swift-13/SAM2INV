#!/usr/bin/env bash
set -euo pipefail

ROOT=/home/yangfp/SAM2INV/loop_factory
PIPELINE="$ROOT/batch_pipeline.py"

run_pair() {
  python3 "$PIPELINE" "$@" --append
  python3 "$PIPELINE" "$@" --llm-core-gen --append
}

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
