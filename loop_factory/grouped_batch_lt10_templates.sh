#!/usr/bin/env bash
set -euo pipefail

# Auto-generated: templates with generated count < 10 (including 0)
# Source map: generated/test/file_template_map.jsonl
# Source params: grouped_batch_min_params.sh (active commands only)

# L10_piecewise_multirate: current_count=8
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 8 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates L10_piecewise_multirate --append
# X17_harmonic_step_reduction: current_count=9
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 15 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 5 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X17_harmonic_step_reduction --append
# X19_rolling_sum_window: current_count=6
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 15 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 6 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X19_rolling_sum_window --append
# X22_ramped_transfer_conservation: current_count=7
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 15 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X22_ramped_transfer_conservation --append
# X23_alternating_swap_transfer: current_count=6
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 8 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 5 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates  X23_alternating_swap_transfer --append
# X24_scheduled_queue_occupancy: current_count=3
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 8 --workers 20 --p-nonlinear 0.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 8 --max-assign 6 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates  X24_scheduled_queue_occupancy --append
# N9_cauchy_schwarz: current_count=2
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 23 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N9_cauchy_schwarz --append
# N8_int_sqrt: current_count=6
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 58 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N8_int_sqrt --append
# X6_newton_sqrt: current_count=1
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 58 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X6_newton_sqrt --append
# N5_quotient_remainder: current_count=2
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 23 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 4 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N5_quotient_remainder --append
# N10_russian_multiply: current_count=1
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 23 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 6 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N10_russian_multiply --append
# X16_carry_chain: current_count=1
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 58 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X16_carry_chain --append
# X8_dual_phase_recurrence: current_count=8
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 23 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 9 --max-assign 7 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X8_dual_phase_recurrence --append
# N1_poly_finite_diff: current_count=5
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 58 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 6 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N1_poly_finite_diff --append
# N11_product_by_addition: current_count=4
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 57 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 2 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N11_product_by_addition --append
# G2_nla_generic_expandable: current_count=9
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 89 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 8 --max-assign 7 --min-assign 1 --max-ifelse 3 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates G2_nla_generic_expandable --append
# N7_geometric_affine: current_count=1
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 89 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 7 --max-assign 5 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N7_geometric_affine --append
# X3_bisection: current_count=0
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 89 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X3_bisection --append
# X11_odd_sum_square: current_count=5
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 89 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates X11_odd_sum_square --append
# N13_affine_geometric: current_count=1
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 23 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 4 --min-assign 1 --max-ifelse 2 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N13_affine_geometric --append
# N3_square_sum: current_count=8
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 57 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N3_square_sum --append
# N4_higher_power_sums: current_count=8
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 57 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 6 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N4_higher_power_sums --append
# N12_squared_invariant: current_count=4
python3 /home/yangfp/SAM2INV/loop_factory/batch_pipeline.py --num-candidates 5 --work-dir test --target-count 57 --workers 20 --p-nonlinear 1.0 --max-params 2 --min-params 0 --min-vars 1 --max-vars 5 --max-assign 3 --min-assign 1 --max-ifelse 1 --min-ifelse 0 --min-loops 1 --max-loops 1 --p-semantic-core 1.0 --allowed-templates N12_squared_invariant --append