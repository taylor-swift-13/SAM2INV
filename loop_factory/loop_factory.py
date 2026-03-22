#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import logging
import random
import re
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

DEFAULT_CORE_KNOBS = {
    "w_core_rel_guard": 0.5,
    "w_core_cond_fixed": 0.5,
    "w_core_linear_state": 0.5,
    "w_core_min_update": 2.0,
    "w_core_qr_division": 2.3,
    "w_core_euclid_matrix": 1.2,
}
CORE_WEIGHT_TEMPERATURE = 0.70
CORE_REPEAT_PENALTY = 0.60
DEFAULT_EXTRA_VAR_BEHAVIOR_PROBS = {
    "none": 0.45,
    "simple": 0.35,
    "native": 0.20,
}
# Per-core native extension style (template-specific judgment).
# Styles:
# - linear: direct affine extension over more vars
# - branch: piecewise direct extension
# - modular: modular/bucketized extension
# - recurrence: recurrence-chain extension
# - multiplicative: multiplicative/affine-nonlinear extension
# - qr: quotient-remainder style coupled extension
# - euclid: reduction/coupled-difference extension
# - state: state-machine/phase extension
CORE_NATIVE_EXTENSION_STYLE: Dict[str, str] = {
    "cond_fixed": "multiplicative",
    "linear_conservation_family": "linear",
    "affine_chain": "linear",
    "remainder_buckets": "modular",
    "monotone_bound": "linear",
    "phase_switch": "state",
    "saturation": "branch",
    "scaling_pair": "multiplicative",
    "counter_decomp": "linear",
    "gcd_compare": "euclid",
    "snapshot_family": "linear",
    "complement_step": "linear",
    "triple_decrease": "linear",
    "stride_family": "linear",
    "min_update_guarded_bound": "branch",
    "negative_cross_progress": "linear",
    "triplet_lockstep_stride": "linear",
    "threshold_tail_accumulate": "branch",
    "half_split_balance": "branch",
    "mod_bucket_cascade": "modular",
    "nested_guarded_transitions": "state",
    "piecewise_recurrence": "recurrence",
    "qr_division_step": "qr",
    "euclid_matrix": "euclid",
    "while_one_break_counter": "linear",
    "triple_recurrence_inc": "recurrence",
    "qr_countdown_bucket": "qr",
    "triple_recurrence_step": "recurrence",
    "accumulate_family": "linear",
    "prefix_sum_family": "linear",
    "mul_affine_param_pair": "multiplicative",
    "power_accumulate": "multiplicative",
    "parity_decomposition_product": "modular",
    "odd_step_accumulator": "recurrence",
    "square_sync_progress": "multiplicative",
    "multiplicative_shadow_progress": "multiplicative",
    "quadratic_form_triplet": "recurrence",
    "euclid_coupled_accumulator": "euclid",
    "fixed_point_root_refinement": "euclid",
    "residual_branch_walk": "branch",
    "multi_branch_swap_recurrence": "state",
    "while_one_min_break": "branch",
    "while_one_qr_break": "qr",
    "while_one_mul_break": "multiplicative",
    "while_one_recurrence_break": "recurrence",
    "parity_alternating": "state",
    "russian_multiply": "multiplicative",
    "cauchy_schwarz_triple": "multiplicative",
    "int_sqrt_sieve": "linear",
    "countdown_triple": "linear",
    "binary_toggle": "state",
    "gap_drift_piecewise": "branch",
    "alternating_series_accumulator": "recurrence",
    "turn_based_state_machine": "state",
    "equal_pair_piecewise_increment": "branch",
    "cache_coherence": "state",
    "multi_countdown_parallel": "state",
    "geometric_doubling_bound": "multiplicative",
    "sawtooth_modular_counter": "modular",
    "decaying_stride": "linear",
    "bouncing_counter": "state",
    "modular_equality_race": "modular",
    "transfer_conservation": "linear",
    "carry_pair_counter": "linear",
    "ramped_transfer_conservation": "linear",
    "alternating_swap_transfer": "state",
    "scheduled_queue_occupancy": "state",
    "nested_triangular_accumulate": "linear",
    "nested_triangular_balance": "linear",
    "nested_grid_rowcol_sum": "linear",
    "nested_grid_checkerboard": "branch",
    "nested_block_drain": "linear",
    "nested_block_staircase": "linear",
    "x1_geometric_growth_bound": "multiplicative",
    "x17_harmonic_step_reduction": "branch",
    "x19_rolling_sum_window": "state",
    "random_walk_bounded": "branch",
    "ghost_sync_pair": "linear",
    "product_reduction_walk": "multiplicative",
    "partial_product_conservation": "multiplicative",
    "cumulative_double_sum": "multiplicative",
    "power_sum_series": "multiplicative",
    "newton_sqrt_convergence": "euclid",
    "bresenham_line_step": "branch",
    "nondeterministic_multi_decrement": "state",
    "L1_trivial": "linear",
    "L2_trivial": "linear",
}

CORE_LLM_REQUIREMENTS: Dict[str, str] = {
    "L1_trivial": "Semantics: minimal linear progress only. Must still have a meaningful progress variable and avoid dead-state noise.",
    "L2_trivial": "Semantics: minimal guarded progress only. Must remain simple but not degenerate into unrelated updates.",
    "accumulate_family": "Semantics: simple accumulation driven by progress or another live state. Must update an accumulator meaningfully.",
    "affine_chain": "Semantics: chained affine recurrence across multiple variables. Must preserve a clear dependency chain.",
    "alternating_series_accumulator": "Semantics: alternating-sign or alternating-phase accumulation. Must include a phase or sign state that affects accumulation.",
    "alternating_swap_transfer": "Semantics: alternating transfer or swap-like state exchange across iterations. Must include turn-dependent transfer.",
    "binary_toggle": "Semantics: binary or two-state toggle. Must switch between a small number of discrete states with clear control meaning.",
    "bouncing_counter": "Semantics: counter moves between bounds and changes direction or mode near boundaries.",
    "bresenham_line_step": "Semantics: Bresenham-style decision-variable update. Must maintain a step counter and an error or decision state.",
    "cache_coherence": "Semantics: two related resource states stay coherent under transfer or rebalance.",
    "carry_pair_counter": "Semantics: radix carry pair with quotient-remainder style relation. Must maintain bounded remainder behavior.",
    "cauchy_schwarz_triple": "Semantics: triple accumulation over square and cross terms. Must update at least three coupled accumulators.",
    "complement_step": "Semantics: one variable complements another under progress, such as y = n - x style evolution.",
    "cond_fixed": "Semantics: branch-controlled multiplicative or fixed-step updates. Must include a meaningful conditional that changes state evolution.",
    "countdown_triple": "Semantics: three counters progress together, typically with coordinated decreases or offset motion.",
    "counter_decomp": "Semantics: a counter is decomposed into multiple live components or derived running parts.",
    "cumulative_double_sum": "Semantics: cumulative summation where one accumulator feeds another.",
    "decaying_stride": "Semantics: stride or step size changes over time, usually shrinking while progress continues.",
    "equal_pair_piecewise_increment": "Semantics: two states receive equal or mirrored updates under piecewise conditions.",
    "euclid_coupled_accumulator": "Semantics: Euclid-like reduction plus another coupled accumulator that tracks the reduction process.",
    "euclid_matrix": "Semantics: Euclid-like coupled reduction or affine-coupled convergence. Must update at least two coupled states and preserve convergence flavor.",
    "fixed_point_root_refinement": "Semantics: iterative refinement toward an integer root or fixed point. Must monotonically reduce approximation error or residual.",
    "gap_drift_piecewise": "Semantics: update depends on the gap between states and uses piecewise drift rules.",
    "gcd_compare": "Semantics: compare-driven dual-state convergence, similar to gcd-style reduction.",
    "geometric_doubling_bound": "Semantics: repeated doubling or geometric growth until a bound or threshold is approached.",
    "ghost_sync_pair": "Semantics: a shadow-like state remains synchronized with another live state under progress.",
    "half_split_balance": "Semantics: first half and second half of execution apply opposite or balancing updates.",
    "int_sqrt_sieve": "Semantics: integer square-root style reduction using odd steps or residual subtraction.",
    "linear_conservation_family": "Semantics: conservation or lockstep relation across variables. Must preserve a sum, difference, or exact relational law.",
    "min_update_guarded_bound": "Semantics: bounded progress with guarded min-style tracking or monotone tightening.",
    "mod_bucket_cascade": "Semantics: modular bucket or divisibility cascade with several residue-driven states.",
    "modular_equality_race": "Semantics: modular equality or residue race between two states.",
    "monotone_bound": "Semantics: monotone variable evolves toward or against an explicit bound.",
    "mul_affine_param_pair": "Semantics: multiplicative-affine pair of states, often parameterized. Must include a multiplicative relation.",
    "multi_branch_swap_recurrence": "Semantics: multi-branch recurrence with swaps or role changes across branches.",
    "multi_countdown_parallel": "Semantics: several countdown-like states progress in parallel under one loop.",
    "multiplicative_shadow_progress": "Semantics: product-like main state with another shadow state tracking progress or approximation.",
    "negative_cross_progress": "Semantics: a negative state crosses a threshold through coupled progress with another variable.",
    "nested_block_drain": "Semantics: nested loop drains or consumes block-local work in bounded chunks.",
    "nested_block_staircase": "Semantics: nested staircase pattern where inner work changes systematically with outer progress.",
    "nested_grid_checkerboard": "Semantics: nested grid traversal with parity or checkerboard-dependent updates.",
    "nested_grid_rowcol_sum": "Semantics: nested row and column traversal with row or column accumulators or counters.",
    "nested_guarded_transitions": "Semantics: nested or multi-phase guarded state transitions. Must include meaningful branch or state-machine behavior.",
    "nested_triangular_accumulate": "Semantics: nested triangular accumulation over outer and inner counters.",
    "nested_triangular_balance": "Semantics: nested triangular traversal maintaining two balanced accumulators or coupled states.",
    "newton_sqrt_convergence": "Semantics: Newton-style integer square-root refinement. Must preserve clear convergence semantics.",
    "nondeterministic_multi_decrement": "Semantics: several guarded decrements compete or fire under different conditions.",
    "odd_step_accumulator": "Semantics: accumulation over an odd-step ladder or increment sequence.",
    "parity_alternating": "Semantics: parity or a flag determines alternating behavior across iterations.",
    "parity_decomposition_product": "Semantics: parity-guided multiplicative decomposition, such as product or multiply-by-doubling logic.",
    "partial_product_conservation": "Semantics: conservation law over partial products or bilinear forms.",
    "phase_switch": "Semantics: execution switches between phases with distinct update rules.",
    "piecewise_recurrence": "Semantics: recurrence law changes by branch or phase. Must preserve interpretable piecewise semantics.",
    "power_accumulate": "Semantics: accumulate powers, higher-order terms, or polynomial-growth quantities.",
    "power_sum_series": "Semantics: running sum of polynomial or power-series-like terms.",
    "prefix_sum_family": "Semantics: progress counter plus at least one meaningful accumulator. Must update a progress variable and an accumulator tied to progress.",
    "product_reduction_walk": "Semantics: reduce a product-related quantity while another factor walks toward termination.",
    "qr_countdown_bucket": "Semantics: quotient-remainder countdown with bucketized carry or rollover behavior.",
    "qr_division_step": "Semantics: quotient-remainder style reduction. Must contain quotient or remainder-like roles and clear progress.",
    "quadratic_form_triplet": "Semantics: three-way quadratic-form accumulation with coupled polynomial terms.",
    "ramped_transfer_conservation": "Semantics: transfer between states with a ramping or capped step size while preserving a relation.",
    "random_walk_bounded": "Semantics: bounded random-walk-like drift with an explicit progress or safety bound.",
    "remainder_buckets": "Semantics: classify or count progress into remainder buckets under modular arithmetic.",
    "residual_branch_walk": "Semantics: residual or error state walks differently depending on branch outcomes.",
    "russian_multiply": "Semantics: multiplication decomposition via doubling, halving, and parity accumulation. Must preserve decomposition meaning.",
    "saturation": "Semantics: growth or drift saturates at a threshold or switches to capped behavior.",
    "sawtooth_modular_counter": "Semantics: modular counter repeatedly rises and wraps in a sawtooth pattern.",
    "scaling_pair": "Semantics: one state scales while another tracks or compensates the scaling.",
    "scheduled_queue_occupancy": "Semantics: queue or occupancy state changes by scheduled pushes and pops.",
    "snapshot_family": "Semantics: snapshot or shadow tracking with delayed synchronization. Must relate a current value and a lagging shadow value.",
    "square_sync_progress": "Semantics: one state tracks a square or synchronized quadratic relation with progress.",
    "stride_family": "Semantics: fixed or proportional stride progression. Must preserve clear stride-based movement.",
    "threshold_tail_accumulate": "Semantics: accumulation only activates after crossing a threshold or in the tail region.",
    "transfer_conservation": "Semantics: quantity transfers from one state to another while preserving a total or exact relation.",
    "triple_decrease": "Semantics: three related states decrease together under guard conditions.",
    "triple_recurrence_inc": "Semantics: three-state recurrence with explicit monotone progress variable.",
    "triple_recurrence_step": "Semantics: chained three-state recurrence where each iteration advances the recurrence.",
    "triplet_lockstep_stride": "Semantics: three states move in lockstep with the same stride or synchronized update.",
    "turn_based_state_machine": "Semantics: a turn or phase variable controls a small state machine with different updates per turn.",
    "while_one_break_counter": "Semantics: canonical while(1)+break counter loop with explicit break condition and meaningful state progress.",
    "while_one_min_break": "Semantics: while(1) loop with min-style tracking and explicit break on reaching a bound.",
    "while_one_mul_break": "Semantics: while(1) loop with multiplicative-affine updates and break-triggered termination.",
    "while_one_qr_break": "Semantics: while(1) loop implementing quotient-remainder style updates until the break condition holds.",
    "while_one_recurrence_break": "Semantics: while(1) loop running a recurrence until an explicit threshold triggers break.",
    "x17_harmonic_step_reduction": "Semantics: denominator-ladder or harmonic-style reduction with shrinking effective steps.",
    "x19_rolling_sum_window": "Semantics: rolling window sum where entering and leaving contributions are updated incrementally.",
    "x1_geometric_growth_bound": "Semantics: geometric growth until crossing a bound, maintaining a simple bound witness.",
}


def _build_core_personalized_variant_spec() -> Dict[str, str]:
    """
    Build per-core personalized small-variant spec.
    Each semantic core gets its own semantics-preserving mode entry.
    """
    spec: Dict[str, str] = {}
    for core, style in CORE_NATIVE_EXTENSION_STYLE.items():
        h = int(hashlib.sha256(core.encode("utf-8")).hexdigest()[:8], 16)
        if style in {"linear"}:
            mode_pool = ["plus_swap", "minus_to_plus_neg", "add_const_split", "mul2_split"]
        elif style in {"multiplicative"}:
            mode_pool = ["mul2_split", "plus_swap", "minus_to_plus_neg"]
        elif style in {"branch", "state"}:
            mode_pool = ["ifelse_swap_negate", "cond_flip_order", "cond_demorgan"]
        else:
            mode_pool = ["plus_swap", "minus_to_plus_neg", "ifelse_swap_negate"]
        mode = mode_pool[h % len(mode_pool)]
        spec[core] = mode
    return spec


CORE_PERSONALIZED_VARIANT_SPEC: Dict[str, str] = _build_core_personalized_variant_spec()
if set(CORE_PERSONALIZED_VARIANT_SPEC) != set(CORE_NATIVE_EXTENSION_STYLE):
    raise RuntimeError("Personalized variant spec must cover every semantic core.")

# ─── Semantic Template Registry ───────────────────────────────────────────────
# Maps template names to their source family and which existing core(s) implement them.
# New entries require a matching elif branch in _sample_core_loop.
SEMANTIC_TEMPLATES: Dict[str, Dict] = {
    # ── Generic fallback templates for full input coverage mapping ────────────
    "G1_linear_generic_expandable": {"family": "linear", "cores": ["affine_chain", "linear_conservation_family", "stride_family"]},
    "G2_nla_generic_expandable":    {"family": "nla",    "cores": ["power_accumulate", "mul_affine_param_pair", "piecewise_recurrence"]},
    # ── L-series (linear arithmetic) ──────────────────────────────────────────
    "L1_affine_accumulator":      {"family": "linear", "cores": ["prefix_sum_family", "accumulate_family"]},
    "L2_countdown":               {"family": "linear", "cores": ["complement_step"]},
    "L3_proportional_stride":     {"family": "linear", "cores": ["stride_family"]},
    "L4_conservation":            {"family": "linear", "cores": ["linear_conservation_family"]},
    "L5_countdown_triple":        {"family": "linear", "cores": ["countdown_triple", "triple_decrease"]},
    "L6_snapshot_chase":          {"family": "linear", "cores": ["snapshot_family"]},
    "L7_parity_flipflop":         {"family": "linear", "cores": ["parity_alternating", "half_split_balance"]},
    "L8_saturation_guard":        {"family": "linear", "cores": ["saturation", "mod_bucket_cascade"]},
    "L9_sliding_window":          {"family": "linear", "cores": ["threshold_tail_accumulate"]},
    "L10_piecewise_multirate":    {"family": "linear", "cores": ["phase_switch"]},
    "L11_triple_modular_step":    {"family": "linear", "cores": ["mod_bucket_cascade", "triplet_lockstep_stride", "remainder_buckets"]},
    "L12_monotone_increment":     {"family": "linear", "cores": ["monotone_bound", "negative_cross_progress"]},
    "L13_binary_toggle":          {"family": "linear", "cores": ["binary_toggle"]},
    "L14_cache_coherence":        {"family": "linear", "cores": ["cache_coherence"]},          # NEW
    "L15_multi_countdown":        {"family": "linear", "cores": ["multi_countdown_parallel"]}, # NEW
    "L16_min_tracking":           {"family": "linear", "cores": ["min_update_guarded_bound"]},
    "L17_geometric_doubling":     {"family": "linear", "cores": ["geometric_doubling_bound"]}, # NEW
    "L18_sawtooth_modular":       {"family": "linear", "cores": ["sawtooth_modular_counter"]}, # NEW
    "L19_linked_countdown":       {"family": "linear", "cores": ["triple_decrease"]},
    "L20_decaying_stride":        {"family": "linear", "cores": ["decaying_stride"]},          # NEW
    # ── N-series (non-linear arithmetic) ──────────────────────────────────────
    "N1_poly_finite_diff":        {"family": "nla", "cores": ["triple_recurrence_inc", "triple_recurrence_step", "while_one_recurrence_break"]},
    "N2_triangular_sum":          {"family": "nla", "cores": ["prefix_sum_family"]},
    "N3_square_sum":              {"family": "nla", "cores": ["power_accumulate"]},
    "N4_higher_power_sums":       {"family": "nla", "cores": ["power_accumulate"]},
    "N5_quotient_remainder":      {"family": "nla", "cores": ["qr_division_step", "qr_countdown_bucket", "while_one_qr_break"]},
    "N6_extended_euclid":         {"family": "nla", "cores": ["euclid_matrix", "euclid_coupled_accumulator"]},
    "N7_geometric_affine":        {"family": "nla", "cores": ["mul_affine_param_pair", "while_one_mul_break"]},
    "N8_int_sqrt":                {"family": "nla", "cores": ["odd_step_accumulator", "int_sqrt_sieve"]},
    "N9_cauchy_schwarz":          {"family": "nla", "cores": ["cauchy_schwarz_triple", "quadratic_form_triplet"]},
    "N10_russian_multiply":       {"family": "nla", "cores": ["russian_multiply", "cond_fixed", "parity_decomposition_product"]},
    "N11_product_by_addition":    {"family": "nla", "cores": ["accumulate_family"]},
    "N12_squared_invariant":      {"family": "nla", "cores": ["square_sync_progress"]},
    "N13_affine_geometric":       {"family": "nla", "cores": ["multiplicative_shadow_progress", "scaling_pair"]},
    "N14_quadratic_piecewise":    {"family": "nla", "cores": ["multi_branch_swap_recurrence", "piecewise_recurrence"]},
    # ── X-series (novel patterns not directly sourced from benchmarks) ─────────
    "X2_gcd_convergence":         {"family": "linear", "cores": ["gcd_compare"]},
    "X3_bisection":               {"family": "nla",    "cores": ["fixed_point_root_refinement"]},
    "X4_coupled_counter_acc":     {"family": "linear", "cores": ["prefix_sum_family"]},
    "X5_bouncing_counter":        {"family": "linear", "cores": ["bouncing_counter"]},         # NEW
    "X6_newton_sqrt":             {"family": "nla",    "cores": ["fixed_point_root_refinement", "int_sqrt_sieve"]},
    "X8_dual_phase_recurrence":   {"family": "nla",    "cores": ["euclid_matrix"]},
    "X9_accumulated_difference":  {"family": "linear", "cores": ["linear_conservation_family"]},
    "X10_prefix_sum_count":       {"family": "linear", "cores": ["prefix_sum_family"]},
    "X11_odd_sum_square":         {"family": "nla",    "cores": ["odd_step_accumulator"]},
    "X12_modular_equality_race":  {"family": "linear", "cores": ["modular_equality_race"]},    # NEW
    "X13_convergent_pair":        {"family": "linear", "cores": ["linear_conservation_family"]},
    "X14_interval_shrinking":     {"family": "linear", "cores": ["gcd_compare"]},
    "X15_diagonal_walk":          {"family": "linear", "cores": ["stride_family"]},
    "X16_carry_chain":            {"family": "nla",    "cores": ["qr_countdown_bucket"]},
    "X17_harmonic_step_reduction":{"family": "linear", "cores": ["x17_harmonic_step_reduction"]},
    "X18_matrix_trace":           {"family": "linear", "cores": ["linear_conservation_family"]},
    "X19_rolling_sum_window":     {"family": "linear", "cores": ["x19_rolling_sum_window"]},
    "X20_amortized_credit":       {"family": "linear", "cores": ["complement_step"]},
    "X21_carry_pair_counter":     {"family": "linear", "cores": ["carry_pair_counter"]},
    "X22_ramped_transfer_conservation": {"family": "linear", "cores": ["ramped_transfer_conservation"]},
    "X23_alternating_swap_transfer": {"family": "linear", "cores": ["alternating_swap_transfer"]},
    "X24_scheduled_queue_occupancy": {"family": "linear", "cores": ["scheduled_queue_occupancy"]},
    "X25_nested_triangular_patterns": {"family": "linear", "cores": ["nested_triangular_accumulate", "nested_triangular_balance"]},
    "X26_nested_grid_patterns": {"family": "linear", "cores": ["nested_grid_rowcol_sum", "nested_grid_checkerboard"]},
    "X27_nested_block_patterns": {"family": "linear", "cores": ["nested_block_drain", "nested_block_staircase"]},
    "X1_geometric_growth_bound":  {"family": "linear", "cores": ["x1_geometric_growth_bound"]},
    "X7_carry_propagation_accumulator": {"family": "nla", "cores": ["x7_carry_propagation_accumulator"]},
}

# ─── Multi-Loop Semantic Template Pairs ───────────────────────────────────────
# Maps multi-loop pattern names to (loop1_core, loop2_core) pairs.
# Loop 1 computes a quantity; Loop 2 uses or verifies it.
# Used by sample_program() when p_multi_semantic triggers.
MULTI_LOOP_TEMPLATES: Dict[str, Tuple[str, str]] = {
    "ML1_accumulate_verify":   ("prefix_sum_family",       "complement_step"),
    "ML2_gcd_then_multiple":   ("gcd_compare",             "accumulate_family"),
    "ML3_multiply_check":      ("russian_multiply",        "accumulate_family"),
    "ML4_normalize_process":   ("snapshot_family",         "accumulate_family"),
    "ML5_sqrt_then_bound":     ("int_sqrt_sieve",          "cauchy_schwarz_triple"),
    "ML6_phase_split_merge":   ("mod_bucket_cascade",      "prefix_sum_family"),
    "ML7_decompose_recompose": ("qr_division_step",        "accumulate_family"),
    "ML8_refine_saturate":     ("fixed_point_root_refinement", "saturation"),
}

# Generic core banks used for per-file template instantiation.
INPUT_TEMPLATE_CORE_BANK: Dict[str, List[List[str]]] = {
    "linear": [
        ["affine_chain", "linear_conservation_family", "stride_family"],
        ["snapshot_family", "complement_step", "monotone_bound"],
        ["phase_switch", "threshold_tail_accumulate", "countdown_triple"],
        ["mod_bucket_cascade", "binary_toggle", "gap_drift_piecewise"],
    ],
    "NLA_lipus": [
        ["power_accumulate", "mul_affine_param_pair", "piecewise_recurrence"],
        ["qr_division_step", "qr_countdown_bucket", "while_one_qr_break"],
        ["euclid_matrix", "euclid_coupled_accumulator", "fixed_point_root_refinement"],
        ["odd_step_accumulator", "cauchy_schwarz_triple", "russian_multiply"],
    ],
    "test": [
        ["affine_chain", "linear_conservation_family", "accumulate_family"],
        ["prefix_sum_family", "snapshot_family", "phase_switch"],
    ],
}


def _normalize_input_family(name: str) -> str:
    if name in {"linear", "NLA_lipus", "test"}:
        return name
    if name.upper() == "NLA":
        return "NLA_lipus"
    return "linear"


def _input_template_meta_for_file(rel_path: str) -> Dict[str, object]:
    # rel_path: e.g., "linear/123.c"
    fam_raw, fname = rel_path.split("/", 1) if "/" in rel_path else ("linear", rel_path)
    fam = _normalize_input_family(fam_raw)
    stem = Path(fname).stem
    try:
        idx = int(stem)
    except ValueError:
        idx = abs(hash(rel_path))
    bank = INPUT_TEMPLATE_CORE_BANK.get(fam, INPUT_TEMPLATE_CORE_BANK["linear"])
    cores = bank[idx % len(bank)]
    return {"family": "nla" if fam == "NLA_lipus" else "linear", "cores": cores}


def _semantic_id_to_name_map() -> Dict[str, str]:
    out: Dict[str, str] = {}
    for name in SEMANTIC_TEMPLATES:
        m = re.match(r"^([A-Z]+\d+)_", name)
        if m:
            out[m.group(1)] = name
    return out


def _semantic_templates_by_prefix(prefix: str) -> List[str]:
    pref = prefix.upper()
    out = [k for k in SEMANTIC_TEMPLATES.keys() if re.match(rf"^{re.escape(pref)}\d+_", k)]
    out.sort(key=lambda x: int(re.match(rf"^{re.escape(pref)}(\d+)_", x).group(1)) if re.match(rf"^{re.escape(pref)}(\d+)_", x) else 10**9)
    return out


def _parse_sources_refs(raw: str) -> List[Tuple[str, int]]:
    """Parse docs sources line like 'linear/1, 2, 172' or 'NLA/5, 6'."""
    s = raw.replace("–", "-").replace("—", "-")
    parts = [p.strip() for p in s.split(",")]
    refs: List[Tuple[str, int]] = []
    fam: Optional[str] = None
    for p in parts:
        p = re.sub(r"\([^)]*\)", "", p).strip()
        m1 = re.match(r"(?i)(linear|NLA_lipus|NLA|nla_lipus)\s*/\s*(\d+)\s*-\s*(\d+)$", p)
        if m1:
            fam = "linear" if m1.group(1).lower() == "linear" else "NLA_lipus"
            a, b = int(m1.group(2)), int(m1.group(3))
            lo, hi = min(a, b), max(a, b)
            refs.extend((fam, i) for i in range(lo, hi + 1))
            continue
        m2 = re.match(r"(?i)(linear|NLA_lipus|NLA|nla_lipus)\s*/\s*(\d+)$", p)
        if m2:
            fam = "linear" if m2.group(1).lower() == "linear" else "NLA_lipus"
            refs.append((fam, int(m2.group(2))))
            continue
        m3 = re.match(r"^(\d+)\s*-\s*(\d+)$", p)
        if m3 and fam is not None:
            a, b = int(m3.group(1)), int(m3.group(2))
            lo, hi = min(a, b), max(a, b)
            refs.extend((fam, i) for i in range(lo, hi + 1))
            continue
        m4 = re.match(r"^(\d+)$", p)
        if m4 and fam is not None:
            refs.append((fam, int(m4.group(1))))
    return refs


def build_full_input_template_map(
    docs_path: Optional[Path] = None,
    src_input_root: Optional[Path] = None,
    strategy: str = "doc_granularity",
) -> Dict[str, str]:
    """
    Build a full mapping: every input file -> semantic template.
    strategy:
      - doc_granularity: follow semantic_templates.md granularity (default)
      - min_cover: minimum template set (2 templates) for all files
      - max_cover: few generic templates cover most files
      - one_to_one: each input file gets a unique template id
    """
    root = src_input_root or (Path(__file__).resolve().parent.parent / "src" / "input")
    docs = docs_path or (Path(__file__).resolve().parent.parent / "docs" / "semantic_templates.md")
    text = docs.read_text(encoding="utf-8") if docs.exists() else ""
    strategy = strategy.strip().lower()
    mapping: Dict[str, str] = {}

    all_files = sorted(root.rglob("*.c"))
    if strategy == "one_to_one":
        for p in all_files:
            fam = _normalize_input_family(p.parent.name)
            stem = p.stem
            key = f"{fam}/{p.name}"
            mapping[key] = f"IF_{fam}_{stem}"
        return mapping

    if strategy == "min_cover":
        for p in all_files:
            fam = _normalize_input_family(p.parent.name)
            key = f"{fam}/{p.name}"
            mapping[key] = "G2_nla_generic_expandable" if fam == "NLA_lipus" else "G1_linear_generic_expandable"
        return mapping

    # doc_granularity / max_cover / doc_hybrid:
    # keep explicit docs mapping where available.
    input_template_overrides: Dict[str, str] = {}
    id_map = _semantic_id_to_name_map()
    for m in re.finditer(r"^###\s+([A-Z]+\d+)\s+·\s+(.+)$", text, flags=re.M):
        tid = m.group(1)
        sec_start = m.start()
        next_h = re.search(r"^###\s+[A-Z]+\d+\s+·\s+.+$", text[m.end():], flags=re.M)
        sec_end = len(text) if not next_h else (m.end() + next_h.start())
        sec = text[sec_start:sec_end]
        sm = re.search(r"\*\*Sources\*\*:\s*([^\n]+)", sec)
        if not sm:
            continue
        tmpl = id_map.get(tid)
        if not tmpl:
            continue
        for fam, idx in _parse_sources_refs(sm.group(1).strip()):
            key = f"{_normalize_input_family(fam)}/{idx}.c"
            mapping[key] = tmpl

    for key, tmpl in input_template_overrides.items():
        mapping[key] = tmpl

    l_bank = _semantic_templates_by_prefix("L")
    n_bank = _semantic_templates_by_prefix("N")
    x_bank = _semantic_templates_by_prefix("X")
    l_i = 0
    n_i = 0
    x_i = 0
    for p in all_files:
        fam = _normalize_input_family(p.parent.name)
        key = f"{fam}/{p.name}"
        if key in mapping:
            continue
        if strategy == "doc_granularity":
            if fam == "NLA_lipus":
                if n_bank:
                    mapping[key] = n_bank[n_i % len(n_bank)]
                    n_i += 1
                else:
                    mapping[key] = "G2_nla_generic_expandable"
            elif fam == "test":
                # test inputs are mostly linear-style; blend L/X templates.
                bank = (l_bank + x_bank) or l_bank or x_bank
                if bank:
                    mapping[key] = bank[x_i % len(bank)]
                    x_i += 1
                else:
                    mapping[key] = "G1_linear_generic_expandable"
            else:
                if l_bank:
                    mapping[key] = l_bank[l_i % len(l_bank)]
                    l_i += 1
                else:
                    mapping[key] = "G1_linear_generic_expandable"
        elif fam == "NLA_lipus":
            mapping[key] = "G2_nla_generic_expandable"
        else:
            mapping[key] = "G1_linear_generic_expandable"
    return mapping


def write_input_template_map_csv(out_csv: Path, strategy: str = "doc_granularity") -> None:
    mapping = build_full_input_template_map(strategy=strategy)
    out_csv.parent.mkdir(parents=True, exist_ok=True)
    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["input_file", "semantic_template", "family", "cores", "native_styles"])
        for k in sorted(mapping):
            tmpl = mapping[k]
            if tmpl in SEMANTIC_TEMPLATES:
                meta = SEMANTIC_TEMPLATES.get(tmpl, {"family": "unknown", "cores": []})
            elif tmpl.startswith("IF_"):
                meta = _input_template_meta_for_file(k)
            else:
                meta = {"family": "unknown", "cores": []}
            cores = list(meta.get("cores", []))
            styles = [CORE_NATIVE_EXTENSION_STYLE.get(c, "linear") for c in cores]
            w.writerow([k, tmpl, meta.get("family", "unknown"), "|".join(cores), "|".join(styles)])


def audit_loop_template_coverage(strategy: str = "doc_granularity") -> Dict[str, int]:
    """
    Hard audit: every input file that contains while/for loops must map to a semantic template.
    Returns counters and raises RuntimeError on any uncovered loop-file.
    """
    root = (Path(__file__).resolve().parent.parent / "src" / "input").resolve()
    mapping = build_full_input_template_map(strategy=strategy)

    loop_files = 0
    loop_count = 0
    uncovered_files: List[str] = []

    for fam in ["linear", "NLA_lipus", "test"]:
        d = root / fam
        if not d.exists():
            continue
        for p in sorted(d.glob("*.c")):
            text = p.read_text(encoding="utf-8", errors="ignore")
            n_loops = len(re.findall(r"\b(?:while|for)\s*\(", text))
            if n_loops <= 0:
                continue
            loop_files += 1
            loop_count += n_loops
            key = f"{_normalize_input_family(fam)}/{p.name}"
            tmpl = mapping.get(key, "")
            if not tmpl:
                uncovered_files.append(key)

    if uncovered_files:
        preview = ", ".join(uncovered_files[:10])
        raise RuntimeError(
            f"Uncovered loop files: {len(uncovered_files)}. examples: {preview}"
        )

    return {
        "loop_files_total": loop_files,
        "loops_total": loop_count,
        "mapped_files_total": len(mapping),
        "unique_templates": len(set(mapping.values())),
    }

def _load_user_cfg() -> Dict[str, object]:
    """Best-effort load of src/config.py LOOP_FACTORY_USER_CONFIG."""
    src_dir = (Path(__file__).resolve().parent / "../src").resolve()
    if not src_dir.exists():
        return {}
    if str(src_dir) not in sys.path:
        sys.path.insert(0, str(src_dir))
    try:
        import config as user_config  # type: ignore
        cfg = getattr(user_config, "LOOP_FACTORY_USER_CONFIG", {})
        return cfg if isinstance(cfg, dict) else {}
    except Exception:
        return {}


USER_CFG = _load_user_cfg()


def _load_llm_runtime():
    """Best-effort import of src/llm.py runtime."""
    src_dir = (Path(__file__).resolve().parent / "../src").resolve()
    if not src_dir.exists():
        return None, None
    if str(src_dir) not in sys.path:
        sys.path.insert(0, str(src_dir))
    try:
        from llm import LLMConfig, Chatbot  # type: ignore
        return LLMConfig, Chatbot
    except Exception:
        return None, None


def _cfg_or_default(name: str, default: float) -> float:
    if name in USER_CFG:
        return float(USER_CFG[name])
    legacy = f"lf_{name}"
    if legacy in USER_CFG:
        return float(USER_CFG[legacy])
    return float(default)


def _cfg_list(name: str) -> List[str]:
    """Read list-like config key with backward-compatible lf_* fallback."""
    raw = USER_CFG.get(name, USER_CFG.get(f"lf_{name}", []))
    if raw is None:
        return []
    if isinstance(raw, str):
        return [x.strip() for x in raw.split(",") if x.strip()]
    if isinstance(raw, (list, tuple, set)):
        out: List[str] = []
        for x in raw:
            if x is None:
                continue
            s = str(x).strip()
            if s:
                out.append(s)
        return out
    return []


def _cfg_bool(name: str, default: bool = False) -> bool:
    raw = USER_CFG.get(name, USER_CFG.get(f"lf_{name}", default))
    if isinstance(raw, bool):
        return raw
    if isinstance(raw, (int, float)):
        return bool(raw)
    if isinstance(raw, str):
        return raw.strip().lower() in {"1", "true", "yes", "on"}
    return bool(default)


def _resolve_allowed_cores(items: Sequence[str]) -> Set[str]:
    """
    Resolve user-specified template/core selectors into concrete core names.
    Supports:
    - semantic template names in SEMANTIC_TEMPLATES (e.g. L1_affine_accumulator)
    - core names (e.g. affine_chain)
    """
    allowed: Set[str] = set()
    declared = set(_declared_semantic_cores())
    for token in items:
        t = token.strip()
        if not t:
            continue
        meta = SEMANTIC_TEMPLATES.get(t)
        if isinstance(meta, dict):
            for c in meta.get("cores", []):
                cs = str(c).strip()
                if cs:
                    allowed.add(cs)
            continue
        if t in declared:
            allowed.add(t)
    return allowed


@dataclass(frozen=True)
class HyperParams:
    m: int = 10
    p: int = 3          # max params (upper bound)
    min_params: int = 1 # min params (lower bound; sampled in [min_params, p], can be 0)
    min_while_fuel: int = 0
    while_fuel: int = 3         # program-level upper bound for while loops
    assign_fuel: int = 6        # per-loop assign upper bound (including loop-step)
    ifelse_fuel: int = 4        # per-loop if/if-else upper bound (kept for compatibility)
    min_assign: int = 1         # per-loop assign lower bound (sampled in [min_assign, assign_fuel])
    min_ifelse: int = 0         # per-loop if/if-else lower bound (sampled in [min_ifelse, ifelse_fuel])
    min_vars: int = 1           # per-loop state-variable lower bound
    d_max: int = 2
    p_multi: float = 0.35
    q_nest: float = 0.12
    p_nonlinear: float = 0.55   # probability a loop is NLA-like family
    nonlinear_strength: float = 0.60
    p_semantic_core: float = 1.0       # 1.0 = every loop gets a named semantic template
    p_multi_semantic: float = 0.75    # probability multi-loop program uses ML-series pairing
    p_while_one: float = 0.22
    w_core_rel_guard: float = DEFAULT_CORE_KNOBS["w_core_rel_guard"]
    w_core_cond_fixed: float = DEFAULT_CORE_KNOBS["w_core_cond_fixed"]
    w_core_linear_state: float = DEFAULT_CORE_KNOBS["w_core_linear_state"]
    w_core_min_update: float = DEFAULT_CORE_KNOBS["w_core_min_update"]
    w_core_qr_division: float = DEFAULT_CORE_KNOBS["w_core_qr_division"]
    w_core_euclid_matrix: float = DEFAULT_CORE_KNOBS["w_core_euclid_matrix"]
    allowed_cores: Tuple[str, ...] = ()
    llm_core_gen: bool = False


class Stmt:
    def render(self, indent: int = 0) -> List[str]:
        raise NotImplementedError


@dataclass(frozen=True)
class Assign(Stmt):
    target: str
    expr: str

    def _stable_bucket(self, key: str, k: int) -> int:
        return sum(ord(ch) for ch in key) % max(1, k)

    def _render_assign_code(self) -> str:
        t = self.target
        norm = re.sub(r"\s+", "", self.expr)

        # i = i + 1  <->  i += 1  <->  i++
        if norm == f"{t}+1":
            b = self._stable_bucket(f"{t}:{norm}", 3)
            if b == 0:
                return f"{t} = {t} + 1"
            if b == 1:
                return f"{t} += 1"
            return f"{t}++"
        # i = i - 1  <->  i -= 1  <->  i--
        if norm == f"{t}-1":
            b = self._stable_bucket(f"{t}:{norm}", 3)
            if b == 0:
                return f"{t} = {t} - 1"
            if b == 1:
                return f"{t} -= 1"
            return f"{t}--"

        m_num = re.fullmatch(rf"{re.escape(t)}([+-])(\d+)", norm)
        if m_num:
            op, n = m_num.group(1), int(m_num.group(2))
            if n > 1:
                if self._stable_bucket(f"{t}:{norm}", 2) == 0:
                    return f"{t} = {t} {op} {n}"
                return f"{t} {'+=' if op == '+' else '-='} {n}"

        m_var = re.fullmatch(rf"{re.escape(t)}([+-])([A-Za-z_]\w*)", norm)
        if m_var:
            op, v = m_var.group(1), m_var.group(2)
            if self._stable_bucket(f"{t}:{norm}", 2) == 0:
                return f"{t} = {t} {op} {v}"
            return f"{t} {'+=' if op == '+' else '-='} {v}"

        return f"{t} = {self.expr}"

    def render(self, indent: int = 0) -> List[str]:
        return [f"{' ' * indent}{self._render_assign_code()};"]

    def render_for_step(self) -> str:
        return self._render_assign_code()


@dataclass(frozen=True)
class Break(Stmt):
    def render(self, indent: int = 0) -> List[str]:
        return [f"{' ' * indent}break;"]


@dataclass(frozen=True)
class IfOnly(Stmt):
    cond: str
    then_body: List[Stmt]

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        out = [f"{pad}if ({self.cond}) {{"]
        for s in self.then_body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        return out


@dataclass(frozen=True)
class IfElse(Stmt):
    cond: str
    then_body: List[Stmt]
    else_body: List[Stmt]

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        out = [f"{pad}if ({self.cond}) {{"]
        for s in self.then_body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        out.append(f"{pad}else {{")
        for s in self.else_body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        return out


@dataclass(frozen=True)
class WhileLoop(Stmt):
    cond: str
    body: List[Stmt]

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        out = [f"{pad}while ({self.cond}) {{"]
        for s in self.body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        return out


@dataclass(frozen=True)
class ForLoop(Stmt):
    cond: str
    step: Optional[Assign]
    body: List[Stmt]

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        if self.step is None:
            # No step in header: render as while loop (init written in preamble)
            out = [f"{pad}while ({self.cond}) {{"]
        else:
            step_code = self.step.render_for_step()
            out = [f"{pad}for (; {self.cond}; {step_code}) {{"]
        for s in self.body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        return out


@dataclass
class Program:
    name: str
    params: List[str]
    local_inits: List[Tuple[str, str]]
    body: List[Stmt]
    selected_cores: List[str] = field(default_factory=list)

    def render(self) -> str:
        sig = ",".join(f"int {p}" for p in self.params)
        lines = [f"int {self.name}({sig}){{"]
        if self.local_inits:
            lines.append(f"  int {', '.join(v for v, _ in self.local_inits)};")
            lines.append("")
            for v, e in self.local_inits:
                lines.append(f"  {v}={e};")
            lines.append("")

        for s in self.body:
            lines.extend(s.render(2))
            lines.append("")

        lines.append("}")
        return "\n".join(lines)


class NameAllocator:
    def __init__(self, params: Sequence[str], rng: random.Random):
        self.used = set(params)
        self.rng = rng
        self.max_names = 4096
        self.first_chars = "abcdefghijklmnopqrstuvwxyz"
        self.rest_chars = "abcdefghijklmnopqrstuvwxyz0123456789"
        self.c_keywords = {
            "auto", "break", "case", "char", "const", "continue", "default", "do", "double",
            "else", "enum", "extern", "float", "for", "goto", "if", "inline", "int", "long",
            "register", "restrict", "return", "short", "signed", "sizeof", "static", "struct",
            "switch", "typedef", "union", "unsigned", "void", "volatile", "while",
        }

    def alloc(self, hint: str = "v") -> str:
        if len(self.used) >= self.max_names:
            raise RuntimeError("No available variable names remain")
        for _ in range(5000):
            length = self.rng.choices([1, 2, 3, 4], weights=[0.20, 0.40, 0.28, 0.12], k=1)[0]
            name = self.rng.choice(self.first_chars)
            for _j in range(length - 1):
                name += self.rng.choice(self.rest_chars)
            if name in self.used or name in self.c_keywords:
                continue
            self.used.add(name)
            return name
        raise RuntimeError("Failed to allocate unique variable name")

    def remaining(self) -> int:
        return max(0, self.max_names - len(self.used))


def _get_written_vars(stmts: List["Stmt"]) -> List[str]:
    """Return deduplicated list of variable names that are targets of Assign stmts."""
    written: List[str] = []
    for s in stmts:
        if isinstance(s, Assign):
            if s.target not in written:
                written.append(s.target)
        elif isinstance(s, IfOnly):
            for v in _get_written_vars(s.then_body):
                if v not in written:
                    written.append(v)
        elif isinstance(s, IfElse):
            for v in _get_written_vars(s.then_body) + _get_written_vars(s.else_body):
                if v not in written:
                    written.append(v)
    return written


def _expr_contains_symbol(expr: str, symbols: Sequence[str]) -> bool:
    for s in symbols:
        if re.search(rf"\b{re.escape(s)}\b", expr):
            return True
    return False


class ProbabilisticLoopFactory:
    def __init__(self, hp: HyperParams, rng: random.Random):
        self.hp = hp
        self.rng = rng
        self.param_candidates = list("abcdefghijklmnopqrstuvwxyz")
        self.var_extension_shortfall = 0

    def _pick_params(self) -> List[str]:
        hi = max(0, min(self.hp.p, len(self.param_candidates)))
        lo = max(0, min(self.hp.min_params, hi))
        p = self.rng.randint(lo, hi)
        return self.rng.sample(self.param_candidates, k=p)

    def _sample_loop_count(self) -> int:
        # Fuel is an upper bound. Actual loop count is sampled in [0, while_fuel].
        lo = max(1, self.hp.min_while_fuel)
        hi = max(lo, self.hp.while_fuel)
        count = lo
        while count < hi and self.rng.random() < self.hp.p_multi:
            count += 1
        return count

    def _sample_const(self) -> int:
        if self.rng.random() < 0.15:
            return self.rng.choice([7, 10, 11, 12, 13, 16, 20, 25])
        return self.rng.choice([-8, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 8])

    def _scale_init(self, val: int) -> int:
        """Occasionally multiply an initial value to produce larger-scale loops (20% chance)."""
        if self.rng.random() < 0.20:
            return val * self.rng.choice([2, 3, 5])
        return val

    def _core_const(self, lo: int, hi: int) -> int:
        """Sample constant from [lo,hi] with 15% chance of outlier."""
        if self.rng.random() < 0.15:
            return self.rng.choice([max(1, lo - 2), hi + 3, min(hi * 2, 99)])
        return self.rng.randint(lo, hi)

    def _diverse_init(self, base: int, role: str = "acc", src: str = "1") -> str:
        """Diversify init value. role='acc'|'ctr'|'param'."""
        if role == "acc" and self.rng.random() < 0.20:
            offset = self.rng.randint(1, 5)
            return str(base + offset)
        if role == "ctr" and self.rng.random() < 0.10:
            return str(-self.rng.randint(1, 4))
        if role == "param" and self.rng.random() < 0.15:
            if self.rng.random() < 0.5:
                return f"{src}+{self.rng.randint(1, 6)}"
            return f"{src}*{self.rng.randint(2, 4)}"
        return str(self._scale_init(base))

    def _diversify_guard(self, guard: str) -> str:
        """Randomly rewrite guard to an equivalent form."""
        r = self.rng.random()
        # Pattern: "x>0" → "x>=1"
        m = re.match(r'^(\w+)>(\d+)$', guard)
        if m and r < 0.30:
            return f"{m.group(1)}>={int(m.group(2))+1}"
        # Pattern: "i<n" → "i<=n-1"
        m = re.match(r'^(\w+)<(\w+)$', guard)
        if m and r < 0.25:
            return f"{m.group(1)}<={m.group(2)}-1"
        # Pattern: "x>0" → "x!=0" (only for non-negative loops)
        m = re.match(r'^(\w+)>0$', guard)
        if m and r < 0.15:
            return f"{m.group(1)}!=0"
        # Pattern: "i<n" → "!(i>=n)"
        m = re.match(r'^(\w+)<(\w+)$', guard)
        if m and r < 0.10:
            return f"!({m.group(1)}>={m.group(2)})"
        return guard

    def _guard_vars(self, guard: str) -> List[str]:
        """Extract guard variable names in stable encounter order."""
        toks = re.findall(r"\b([a-zA-Z_]\w*)\b", guard)
        banned = {"if", "else", "while", "for", "break"}
        out: List[str] = []
        seen: Set[str] = set()
        for t in toks:
            if t in banned or t.isdigit():
                continue
            if t not in seen:
                seen.add(t)
                out.append(t)
        return out

    def _build_guard_progress_assign(self, guard: str, guard_vars: Sequence[str]) -> Optional[Assign]:
        """
        Build one progress assignment that tends to falsify at least one guard atom.
        This is a cross-core safety net when templates do not update guard drivers.
        """
        for v in guard_vars:
            ve = re.escape(v)
            # v < rhs  -> set v = rhs
            m = re.search(rf"\b{ve}\b\s*<\s*([^&|)]+)", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, rhs)
            # v <= rhs -> set v = rhs + 1
            m = re.search(rf"\b{ve}\b\s*<=\s*([^&|)]+)", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, f"({rhs})+1")
            # v > rhs  -> set v = rhs
            m = re.search(rf"\b{ve}\b\s*>\s*([^&|)]+)", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, rhs)
            # v >= rhs -> set v = rhs - 1
            m = re.search(rf"\b{ve}\b\s*>=\s*([^&|)]+)", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, f"({rhs})-1")
            # v != rhs -> set v = rhs
            m = re.search(rf"\b{ve}\b\s*!=\s*([^&|)]+)", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, rhs)

            # rhs < v
            m = re.search(rf"([^&|(]+)\s*<\s*\b{ve}\b", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, rhs)
            # rhs <= v
            m = re.search(rf"([^&|(]+)\s*<=\s*\b{ve}\b", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, f"({rhs})-1")
            # rhs > v
            m = re.search(rf"([^&|(]+)\s*>\s*\b{ve}\b", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, rhs)
            # rhs >= v
            m = re.search(rf"([^&|(]+)\s*>=\s*\b{ve}\b", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, f"({rhs})+1")
            # rhs != v
            m = re.search(rf"([^&|(]+)\s*!=\s*\b{ve}\b", guard)
            if m:
                rhs = m.group(1).strip()
                return Assign(v, rhs)

        if guard_vars:
            # Last-resort deterministic progress to avoid frozen guards.
            v = guard_vars[0]
            return Assign(v, f"{v}+1")
        return None

    def _shuffle_independent(self, body: list) -> list:
        """Shuffle consecutive statements that don't have data dependencies."""
        if len(body) <= 1:
            return body

        def _reads(stmt: Stmt) -> Set[str]:
            if isinstance(stmt, Assign):
                return set(re.findall(r'\b([a-zA-Z_]\w*)\b', stmt.expr))
            return set()  # barrier: don't analyze IfOnly/IfElse

        def _writes(stmt: Stmt) -> Set[str]:
            if isinstance(stmt, Assign):
                return {stmt.target}
            return set()

        result: list = []
        run: list = []

        def flush_run():
            if len(run) > 1:
                self.rng.shuffle(run)
            result.extend(run)
            run.clear()

        for st in body:
            if not isinstance(st, Assign):
                flush_run()
                result.append(st)
                continue
            # Check if this stmt depends on anything in the current run
            st_reads = _reads(st)
            conflict = False
            for prev in run:
                if _writes(prev) & st_reads:
                    conflict = True
                    break
                if _reads(prev) & _writes(st):
                    conflict = True
                    break
                if _writes(prev) & _writes(st):
                    conflict = True
                    break
            if conflict:
                flush_run()
            run.append(st)

        flush_run()
        return result

    def _sample_operand(self, vars_pool: Sequence[str], allow_const: bool = True) -> str:
        if allow_const and self.rng.random() < 0.35:
            return str(self._sample_const())
        return self.rng.choice(list(vars_pool))

    def _sample_expr(self, target: str, vars_pool: Sequence[str], nla_family: bool) -> str:
        if self.rng.random() < 0.14:
            return self._sample_operand(vars_pool, allow_const=True)

        left = target if self.rng.random() < 0.6 else self.rng.choice(list(vars_pool))
        if nla_family:
            op = self.rng.choices(["+", "-", "*", "%"], weights=[0.25, 0.17, 0.46, 0.12], k=1)[0]
        else:
            # Linear family: forbid '*' and '/' in loop-body updates.
            op = self.rng.choices(["+", "-", "%"], weights=[0.62, 0.34, 0.04], k=1)[0]

        if op == "%":
            rhs = str(self.rng.randint(2, 11))
        else:
            rhs = self._sample_operand(vars_pool, allow_const=True)
            if rhs == "0" and op in {"+", "-"}:
                rhs = str(self.rng.randint(1, 6))

        if rhs.startswith("-"):
            rhs = f"({rhs})"
        return f"{left}{op}{rhs}"

    def _sample_limit_expr(self, src: str) -> str:
        # Diversify loop-limit initialization: constant, parameter, or simple affine/mod form.
        mode = self.rng.choices(
            ["const", "src", "src_plus", "src_minus", "src_mod", "src_product"],
            weights=[0.25, 0.20, 0.22, 0.07, 0.16, 0.10],
            k=1,
        )[0]
        if mode == "const":
            # 20% chance of a larger bound (50-200) for more loop iterations
            if self.rng.random() < 0.20:
                return str(self.rng.randint(50, 200))
            return str(self.rng.randint(8, 80))
        if mode == "src":
            return src
        if mode == "src_plus":
            return f"{src}+{self.rng.randint(3, 25)}"
        if mode == "src_minus":
            return f"{src}-{self.rng.randint(1, 10)}"
        if mode == "src_product":
            k = self.rng.randint(2, 5)
            return f"{src}*{k}"
        base = self.rng.randint(6, 40)
        off = self.rng.randint(4, 20)
        return f"({src}%{base})+{off}"

    def _sample_loop_control(self, src: str, ctr: str, lim: str, nla_family: bool) -> Tuple[List[Tuple[str, str]], str, Assign]:
        lim_expr = self._sample_limit_expr(src)
        if self.rng.random() < self.hp.p_while_one:
            start = "0" if self.rng.random() < 0.7 else str(self.rng.randint(1, 3))
            return [(lim, lim_expr), (ctr, start)], "1", Assign(ctr, f"{ctr}+1")

        if nla_family:
            # Mix linear and nonlinear controls for richer guard shapes.
            weights = [0.23, 0.13, 0.11, 0.12, 0.16, 0.11, 0.08, 0.06]
        else:
            # Linear family: disable mul/div loop controls.
            weights = [0.34, 0.16, 0.19, 0.19, 0.0, 0.0, 0.0, 0.12]

        mode = self.rng.choices(
            ["inc1", "dec1", "inc_step", "dec_step", "mul_up", "div_down", "dist_to_limit", "while_one_progress"],
            weights=weights,
            k=1,
        )[0]

        if mode == "inc1":
            r = self.rng.random()
            if r < 0.15:
                start = str(self.rng.randint(-6, -1))   # negative start
            elif r < 0.85:
                start = "0"
            else:
                start = str(self.rng.randint(1, 4))
            g = self.rng.choice([f"{ctr}<{lim}", f"{ctr}<={lim}-1", f"{ctr}+1<={lim}"])
            return [(lim, lim_expr), (ctr, start)], g, Assign(ctr, f"{ctr}+1")

        if mode == "dec1":
            g = self.rng.choice([f"{ctr}>0", f"{ctr}>=1", f"{ctr}-1>=0"])
            return [(lim, lim_expr), (ctr, lim)], g, Assign(ctr, f"{ctr}-1")

        if mode == "inc_step":
            d = self.rng.randint(2, 8)
            start = "0" if self.rng.random() < 0.8 else str(self.rng.randint(1, d))
            g = self.rng.choice([f"{ctr}<{lim}", f"{ctr}+{d}<={lim}", f"{ctr}<={lim}-{d}"])
            return [(lim, lim_expr), (ctr, start)], g, Assign(ctr, f"{ctr}+{d}")

        if mode == "dec_step":
            d = self.rng.randint(2, 6)
            g = self.rng.choice([f"{ctr}>{d-1}", f"{ctr}>={d}", f"{ctr}-{d}>=0"])
            return [(lim, lim_expr), (ctr, lim)], g, Assign(ctr, f"{ctr}-{d}")

        if mode == "mul_up":
            mul = self.rng.randint(2, 4)
            g = self.rng.choice([f"{ctr}<{lim}", f"{ctr}*{mul}<={lim}", f"{ctr}<={lim}/{mul}"])
            return [(lim, lim_expr), (ctr, "1")], g, Assign(ctr, f"{ctr}*{mul}")

        if mode == "div_down":
            start = f"{lim}+{self.rng.randint(1, 6)}" if self.rng.random() < 0.5 else lim
            g = self.rng.choice([f"{ctr}>0", f"{ctr}>=1", f"{ctr}>1"])
            return [(lim, lim_expr), (ctr, start)], g, Assign(ctr, f"{ctr}/2")

        if mode == "while_one_progress":
            start = "0" if self.rng.random() < 0.7 else str(self.rng.randint(1, 3))
            return [(lim, lim_expr), (ctr, start)], "1", Assign(ctr, f"{ctr}+1")

        # ctr tracks distance-to-limit; guard references both ctr and lim explicitly.
        d = self.rng.randint(1, 3)
        init = f"{lim}+{self.rng.randint(2, 7)}"
        g = self.rng.choice([f"{ctr}>{lim}", f"{ctr}>={lim}+1", f"{ctr}-{lim}>0"])
        return [(lim, lim_expr), (ctr, init)], g, Assign(ctr, f"{ctr}-{d}")

    def _semantic_assign(self, tgt: str, peer: str, ctr: str, lim: str, vars_pool: Sequence[str], nla_family: bool) -> Assign:
        p = self.rng.random()
        if not nla_family:
            if p < 0.22:
                expr = f"{tgt}+1"
            elif p < 0.44:
                expr = f"{tgt}+{ctr}"
            elif p < 0.64:
                expr = f"{tgt}+{peer}"
            elif p < 0.80:
                expr = f"{peer}-{tgt}"
            elif p < 0.92:
                expr = f"{tgt}+{self.rng.randint(1, 6)}"
            else:
                expr = self._sample_expr(tgt, vars_pool + [lim], nla_family=False)
        else:
            s = max(0.0, min(1.0, self.hp.nonlinear_strength))
            weak = 0.32 * (1.0 - s)
            if p < weak:
                expr = f"{tgt}+{peer}" if self.rng.random() < 0.5 else f"{peer}+{ctr}"
            elif p < weak + 0.18:
                expr = f"{tgt}*2"
            elif p < weak + 0.36:
                expr = f"{peer}*{peer}"
            elif p < weak + 0.56:
                expr = f"{tgt}*{peer}"
            elif p < weak + 0.76:
                expr = f"{tgt}*{tgt}+{peer}"
            elif p < weak + 0.90:
                expr = f"{tgt}%{self.rng.randint(2, 9)}"
            else:
                expr = self._sample_expr(tgt, vars_pool + [lim], nla_family=True)
        return Assign(tgt, expr)

    def _normalize_expr(self, expr: str) -> str:
        return re.sub(r"\s+", "", expr).strip("()")

    def _dedup_loop_body(self, body: List[Stmt], ctr: str) -> List[Stmt]:
        """
        Suppress low-value repetitive updates, e.g. repeated `v=v-v`/`v=v+1` chains.
        Keep control-flow statements unchanged and only trim top-level Assign noise.
        """
        out: List[Stmt] = []
        assign_seen: Dict[Tuple[str, str], int] = {}
        prev_assign_fp: Tuple[str, str] | None = None
        prev_target: str | None = None
        same_target_run = 0

        for st in body:
            if not isinstance(st, Assign):
                out.append(st)
                prev_assign_fp = None
                prev_target = None
                same_target_run = 0
                continue

            tgt = st.target
            expr_n = self._normalize_expr(st.expr)
            fp = (tgt, expr_n)

            if tgt == prev_target:
                same_target_run += 1
            else:
                same_target_run = 1
                prev_target = tgt

            # 1) Drop exact consecutive duplicates.
            if prev_assign_fp == fp:
                continue
            # 2) Keep at most one explicit self-zeroing update like x=x-x.
            if expr_n == f"{tgt}-{tgt}" and assign_seen.get(fp, 0) >= 1:
                continue
            # 3) Cap repeated same assignment forms.
            if assign_seen.get(fp, 0) >= 2:
                continue
            # 4) Avoid long same-target straight-line update chains (except loop counter).
            if tgt != ctr and same_target_run > 2:
                continue

            out.append(st)
            assign_seen[fp] = assign_seen.get(fp, 0) + 1
            prev_assign_fp = fp

        return out

    def _sample_cond(self, ctr: str, lim: str, aux: str, vars_pool: Sequence[str], nla_family: bool) -> str:
        r = self.rng.random()
        if r < 0.30:
            return f"({ctr}%{self.rng.randint(2, 9)})==0"
        if r < 0.56:
            return f"{aux}+{self.rng.randint(1, 7)}<{lim}"
        if r < 0.80:
            v = self.rng.choice(list(vars_pool))
            return f"{ctr}+{self.rng.randint(1, 7)}<={v}+{lim}"
        if nla_family:
            v = self.rng.choice(list(vars_pool))
            return f"{v}*{v}<={lim}+{self.rng.randint(1, 6)}"
        v1 = self.rng.choice(list(vars_pool))
        v2 = self.rng.choice(list(vars_pool))
        return f"{v1}<{v2}+{self.rng.randint(1, 5)}"

    def _sample_state_vars(self, alloc: NameAllocator, nla_family: bool, max_count: int) -> List[str]:
        # Do not cap state-vars at a fixed small constant. Let templates scale to
        # larger variable sets as long as allocator/budget permits.
        max_state = max(1, min(max_count, alloc.remaining()))
        lo_default = 4 if (nla_family and max_state >= 4) else 1
        lo = max(lo_default, min(self.hp.min_vars, max_state))
        hi = max_state
        count = self.rng.randint(lo, hi)
        return [alloc.alloc("v") for _ in range(count)]

    def _sample_extra_var_behavior(self, native_enabled: bool) -> str:
        p_none = DEFAULT_EXTRA_VAR_BEHAVIOR_PROBS["none"]
        p_simple = DEFAULT_EXTRA_VAR_BEHAVIOR_PROBS["simple"]
        p_native = DEFAULT_EXTRA_VAR_BEHAVIOR_PROBS["native"] if native_enabled else 0.0
        total = p_none + p_simple + p_native
        if total <= 0.0:
            return "none"
        return self.rng.choices(
            ["none", "simple", "native"],
            weights=[p_none / total, p_simple / total, p_native / total],
            k=1,
        )[0]

    def _sample_native_extension_expr(
        self,
        style: str,
        v: str,
        drivers: Sequence[str],
        prev_native: str,
        ctr: str,
        lim: str,
    ) -> str:
        d1 = self.rng.choice(list(drivers) or [ctr, lim])
        d2 = self.rng.choice(list(drivers) or [ctr, lim])
        if style == "linear":
            mode = self.rng.choice(["const", "ctr", "lim_delta", "chain"])
            if mode == "const":
                return f"{v}+{self.rng.randint(1, 3)}"
            if mode == "ctr":
                return f"{v}+{ctr}"
            if mode == "lim_delta":
                return f"{v}+{lim}-{ctr}"
            return f"{v}+{prev_native}"
        if style == "branch":
            return f"{v}+{d1}-{d2}"
        if style == "modular":
            base = self.rng.randint(2, 9)
            return f"({v}+{d1})%{base}"
        if style == "recurrence":
            return f"{v}+{d1}+{d2}"
        if style == "multiplicative":
            k = self.rng.randint(2, 4)
            b = self.rng.randint(0, 3)
            return f"{v}*{k}+({d1}%{self.rng.randint(2, 7)})+{b}"
        if style == "qr":
            return f"{v}+{d1}-{d2}"
        if style == "euclid":
            return f"{v}+{d1}-{d2}"
        if style == "state":
            if self.rng.random() < 0.5:
                return f"{v}+({ctr}%2)"
            return f"{v}+{d1}"
        return f"{v}+{d1}"

    def _apply_template_small_variant(self, core_name: str, body: List[Stmt], ctr: str) -> List[Stmt]:
        """
        Template-specific lightweight variants using per-core personalized spec.
        """
        if not body:
            return body

        prof = CORE_PERSONALIZED_VARIANT_SPEC.get(core_name)
        if prof is None:
            return body
        mode = prof

        assign_idx = [i for i, st in enumerate(body) if isinstance(st, Assign) and st.target != ctr]
        if_idx = [i for i, st in enumerate(body) if isinstance(st, (IfOnly, IfElse))]

        def _rewrite_cond(cond: str, c_mode: str) -> str:
            c = cond.strip()
            if c_mode == "cond_demorgan":
                if "&&" in c:
                    a, b = c.split("&&", 1)
                    return f"!(!({a})||!({b}))"
                if "||" in c:
                    a, b = c.split("||", 1)
                    return f"!(!({a})&&!({b}))"
                return f"!(!({c}))"

            m = re.search(r"^\s*([A-Za-z_]\w*|-?\d+)\s*(<=|>=|<|>|==|!=)\s*([A-Za-z_]\w*|-?\d+)\s*$", c)
            if not m:
                return f"!(!({c}))"
            l, op, r = m.group(1), m.group(2), m.group(3)
            if c_mode in {"cond_negate_cmp", "ifelse_swap_negate"}:
                neg = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "=="}[op]
                return f"!({l}{neg}{r})"
            if c_mode == "cond_flip_order":
                flip = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "==": "==", "!=": "!="}[op]
                return f"{r}{flip}{l}"
            return c

        def _rewrite_expr(expr: str, e_mode: str) -> str:
            e = expr.strip()
            if e_mode == "plus_swap":
                m = re.match(r"^\s*(.+?)\s*\+\s*(.+?)\s*$", e)
                if m:
                    return f"({m.group(2)})+({m.group(1)})"
                return e
            if e_mode == "minus_to_plus_neg":
                m = re.match(r"^\s*(.+?)\s*-\s*(.+?)\s*$", e)
                if m:
                    return f"({m.group(1)})+(-({m.group(2)}))"
                return e
            if e_mode == "mul2_to_add":
                m = re.match(r"^\s*(.+?)\s*\*\s*2\s*$", e)
                if m:
                    return f"({m.group(1)})+({m.group(1)})"
                m2 = re.match(r"^\s*2\s*\*\s*(.+?)\s*$", e)
                if m2:
                    return f"({m2.group(1)})+({m2.group(1)})"
                return e
            if e_mode == "add_const_refactor":
                m = re.match(r"^\s*(.+?)\s*\+\s*(-?\d+)\s*$", e)
                if m:
                    base, k = m.group(1), int(m.group(2))
                    if k >= 2:
                        return f"(({base})+1)+{k-1}"
                    if k <= -2:
                        return f"(({base})-1)+{k+1}"
                return e
            return e

        if mode in {"cond_negate_cmp", "cond_flip_order", "cond_demorgan"}:
            if if_idx:
                i = self.rng.choice(if_idx)
                st = body[i]
                if isinstance(st, IfOnly):
                    body[i] = IfOnly(cond=_rewrite_cond(st.cond, mode), then_body=st.then_body)
                    return body
                if isinstance(st, IfElse):
                    body[i] = IfElse(
                        cond=_rewrite_cond(st.cond, mode),
                        then_body=st.then_body,
                        else_body=st.else_body,
                    )
                    return body
            if not assign_idx:
                return body
            i = self.rng.choice(assign_idx)
            st = body[i]
            assert isinstance(st, Assign)
            body[i] = Assign(st.target, _rewrite_expr(st.expr, "minus_to_plus_neg"))
            return body

        if mode == "ifelse_swap_negate":
            if if_idx:
                # Prefer IfElse to expose stronger structural variation.
                ifelse_ids = [j for j in if_idx if isinstance(body[j], IfElse)]
                pick = self.rng.choice(ifelse_ids) if ifelse_ids else self.rng.choice(if_idx)
                st = body[pick]
                if isinstance(st, IfElse):
                    body[pick] = IfElse(
                        cond=_rewrite_cond(st.cond, "ifelse_swap_negate"),
                        then_body=st.else_body,
                        else_body=st.then_body,
                    )
                    return body
                if isinstance(st, IfOnly):
                    body[pick] = IfOnly(cond=_rewrite_cond(st.cond, "ifelse_swap_negate"), then_body=st.then_body)
                    return body
            if not assign_idx:
                return body
            i = self.rng.choice(assign_idx)
            st = body[i]
            assert isinstance(st, Assign)
            body[i] = Assign(st.target, _rewrite_expr(st.expr, "minus_to_plus_neg"))
            return body

        if mode in {"plus_swap", "minus_to_plus_neg", "mul2_to_add", "add_const_refactor"}:
            if not assign_idx:
                return body
            i = self.rng.choice(assign_idx)
            st = body[i]
            assert isinstance(st, Assign)
            body[i] = Assign(st.target, _rewrite_expr(st.expr, mode))
            return body

        if mode == "add_const_split":
            if not assign_idx:
                return body
            i = self.rng.choice(assign_idx)
            st = body[i]
            assert isinstance(st, Assign)
            m = re.match(r"^\s*(.+?)\s*\+\s*(-?\d+)\s*$", st.expr.strip())
            if not m:
                body[i] = Assign(st.target, _rewrite_expr(st.expr, "add_const_refactor"))
                return body
            base, k = m.group(1), int(m.group(2))
            if abs(k) < 2:
                body[i] = Assign(st.target, _rewrite_expr(st.expr, "add_const_refactor"))
                return body
            sign = 1 if k > 0 else -1
            head = k - sign
            body[i] = Assign(st.target, f"({base})+{head}")
            body.insert(i + 1, Assign(st.target, f"{st.target}+{sign}"))
            return body

        if mode == "mul2_split":
            if not assign_idx:
                return body
            i = self.rng.choice(assign_idx)
            st = body[i]
            assert isinstance(st, Assign)
            e = st.expr.strip()
            m = re.match(r"^\s*(.+?)\s*\*\s*2\s*$", e)
            m2 = re.match(r"^\s*2\s*\*\s*(.+?)\s*$", e)
            term = m.group(1) if m else (m2.group(1) if m2 else "")
            if not term:
                body[i] = Assign(st.target, _rewrite_expr(st.expr, "mul2_to_add"))
                return body
            body[i] = Assign(st.target, term)
            body.insert(i + 1, Assign(st.target, f"{st.target}+{st.target}"))
            return body

        return body

    def _llm_supported_core(self, core_name: str) -> bool:
        return core_name in CORE_LLM_REQUIREMENTS

    def _extract_first_json_object(self, text: str) -> Optional[Dict[str, object]]:
        s = (text or "").strip()
        if not s:
            return None
        try:
            obj = json.loads(s)
            return obj if isinstance(obj, dict) else None
        except json.JSONDecodeError:
            pass
        m = re.search(r"\{[\s\S]*\}", s)
        if not m:
            return None
        try:
            obj = json.loads(m.group(0))
            return obj if isinstance(obj, dict) else None
        except json.JSONDecodeError:
            return None

    def _build_llm_core_prompt(
        self,
        core_name: str,
        ctr: str,
        lim: str,
        state_vars: Sequence[str],
        params: Sequence[str],
        if_budget: int,
        assign_total: int,
        nla_family: bool,
    ) -> str:
        allowed_vars = [ctr, lim] + list(state_vars) + list(params)
        family = "nla" if nla_family else "linear"
        role_text = CORE_LLM_REQUIREMENTS.get(core_name, "Preserve the named semantic core faithfully.")
        return (
            "You generate ONLY strict JSON for a numeric C loop fragment. No markdown. No explanation.\n"
            f"Target semantic core: {core_name}\n"
            f"Family: {family}\n"
            f"Semantic requirements: {role_text}\n"
            f"Available variables only: {json.dumps(allowed_vars)}\n"
            f"Counter variable: {ctr}\n"
            f"Limit/bound variable: {lim}\n"
            f"State variables: {json.dumps(list(state_vars))}\n"
            f"Function parameters: {json.dumps(list(params))}\n"
            f"Max assignment statements in body: {assign_total}\n"
            f"Max if/if-else statements in body: {if_budget}\n"
            "Rules:\n"
            "- Use only the provided variables.\n"
            "- Return a loop fragment, not a full function.\n"
            "- Ensure there is clear loop progress.\n"
            "- Do not declare variables or call functions.\n"
            "- Keep expressions C-compatible.\n"
            "- Prefer meaningful semantics over superficial randomness.\n"
            "- Body statements allowed types: assign, if_only, if_else.\n"
            "Return strict JSON with this schema:\n"
            "{\n"
            "  \"guard\": \"...\",\n"
            "  \"init_overrides\": {\"var\": \"expr\"},\n"
            "  \"body\": [\n"
            "    {\"type\": \"assign\", \"target\": \"x\", \"expr\": \"x+1\"},\n"
            "    {\"type\": \"if_only\", \"cond\": \"...\", \"then\": [assign statements only]},\n"
            "    {\"type\": \"if_else\", \"cond\": \"...\", \"then\": [assign statements only], \"else\": [assign statements only]}\n"
            "  ],\n"
            "  \"semantic_summary\": \"one short sentence\"\n"
            "}\n"
        )

    def _expr_uses_only_allowed_vars(self, expr: str, allowed_vars: Set[str]) -> bool:
        toks = re.findall(r"\b([A-Za-z_]\w*)\b", expr or "")
        reserved = {"int", "if", "else", "while", "for", "break", "return"}
        return all(tok in allowed_vars or tok in reserved for tok in toks)

    def _llm_json_to_stmt_list(self, items: Sequence[object]) -> Optional[List[Stmt]]:
        out: List[Stmt] = []
        for item in items:
            if not isinstance(item, dict):
                return None
            kind = str(item.get("type", "") or "").strip()
            if kind == "assign":
                target = str(item.get("target", "") or "").strip()
                expr = str(item.get("expr", "") or "").strip()
                if not target or not expr:
                    return None
                out.append(Assign(target, expr))
            elif kind == "if_only":
                cond = str(item.get("cond", "") or "").strip()
                then_raw = item.get("then", [])
                if not cond or not isinstance(then_raw, list):
                    return None
                then_body = self._llm_json_to_stmt_list(then_raw)
                if then_body is None or any(not isinstance(x, Assign) for x in then_body):
                    return None
                out.append(IfOnly(cond=cond, then_body=then_body))
            elif kind == "if_else":
                cond = str(item.get("cond", "") or "").strip()
                then_raw = item.get("then", [])
                else_raw = item.get("else", [])
                if not cond or not isinstance(then_raw, list) or not isinstance(else_raw, list):
                    return None
                then_body = self._llm_json_to_stmt_list(then_raw)
                else_body = self._llm_json_to_stmt_list(else_raw)
                if (
                    then_body is None or else_body is None
                    or any(not isinstance(x, Assign) for x in then_body)
                    or any(not isinstance(x, Assign) for x in else_body)
                ):
                    return None
                out.append(IfElse(cond=cond, then_body=then_body, else_body=else_body))
            else:
                return None
        return out

    def _validate_llm_core_payload(
        self,
        core_name: str,
        payload: Dict[str, object],
        ctr: str,
        lim: str,
        state_vars: Sequence[str],
        params: Sequence[str],
        if_budget: int,
        assign_total: int,
    ) -> Optional[Tuple[str, Dict[str, str], List[Stmt], str]]:
        guard = str(payload.get("guard", "") or "").strip()
        if not guard:
            return None
        init_raw = payload.get("init_overrides", {})
        body_raw = payload.get("body", [])
        summary = str(payload.get("semantic_summary", "") or "").strip()
        if not isinstance(init_raw, dict) or not isinstance(body_raw, list):
            return None
        body = self._llm_json_to_stmt_list(body_raw)
        if body is None or not body:
            return None
        assign_count = sum(1 for st in body if isinstance(st, Assign))
        if_count = sum(1 for st in body if isinstance(st, (IfOnly, IfElse)))
        if assign_count > assign_total or if_count > if_budget:
            return None

        allowed_vars = set([ctr, lim] + list(state_vars) + list(params))
        if not self._expr_uses_only_allowed_vars(guard, allowed_vars):
            return None

        init_overrides: Dict[str, str] = {}
        for key, value in init_raw.items():
            k = str(key or "").strip()
            v = str(value or "").strip()
            if not k or not v or k not in allowed_vars or not self._expr_uses_only_allowed_vars(v, allowed_vars):
                return None
            init_overrides[k] = v

        written: Set[str] = set()
        expr_texts: List[str] = [guard]
        for st in body:
            if isinstance(st, Assign):
                if st.target not in allowed_vars or not self._expr_uses_only_allowed_vars(st.expr, allowed_vars):
                    return None
                written.add(st.target)
                expr_texts.append(st.expr)
            elif isinstance(st, IfOnly):
                if not self._expr_uses_only_allowed_vars(st.cond, allowed_vars):
                    return None
                expr_texts.append(st.cond)
                for sub in st.then_body:
                    if sub.target not in allowed_vars or not self._expr_uses_only_allowed_vars(sub.expr, allowed_vars):
                        return None
                    written.add(sub.target)
                    expr_texts.append(sub.expr)
            elif isinstance(st, IfElse):
                if not self._expr_uses_only_allowed_vars(st.cond, allowed_vars):
                    return None
                expr_texts.append(st.cond)
                for sub in st.then_body + st.else_body:
                    if sub.target not in allowed_vars or not self._expr_uses_only_allowed_vars(sub.expr, allowed_vars):
                        return None
                    written.add(sub.target)
                    expr_texts.append(sub.expr)

        if ctr not in written and ctr not in " ".join(expr_texts):
            return None

        text_blob = " ".join(expr_texts)
        if core_name == "prefix_sum_family":
            non_ctr_written = [v for v in written if v != ctr]
            if ctr not in written or not non_ctr_written:
                return None
        elif core_name == "snapshot_family":
            if len(written & set(state_vars)) < 2:
                return None
        elif core_name == "qr_division_step":
            if not any(sym in text_blob for sym in ["/", "%", "-", "+1", "-1"]):
                return None
            if len(written & set(state_vars)) < 2:
                return None
        elif core_name == "euclid_matrix":
            if len(written & set(state_vars)) < 2:
                return None
        elif core_name == "russian_multiply":
            if not any(sym in text_blob for sym in ["%2", "/2", "*2"]):
                return None

        return guard, init_overrides, body, summary

    def _generate_core_loop_with_llm(
        self,
        core_name: str,
        ctr: str,
        lim: str,
        state_vars: Sequence[str],
        params: Sequence[str],
        if_budget: int,
        assign_total: int,
        nla_family: bool,
    ) -> Optional[Tuple[str, Dict[str, str], List[Stmt], str]]:
        if not self.hp.llm_core_gen or not self._llm_supported_core(core_name):
            return None
        LLMConfig, Chatbot = _load_llm_runtime()
        if LLMConfig is None or Chatbot is None:
            return None
        try:
            cfg = LLMConfig()
            if hasattr(cfg, "api_temperature"):
                cfg.api_temperature = 0.7
            bot = Chatbot(cfg)
            resp = bot.chat(
                self._build_llm_core_prompt(
                    core_name=core_name,
                    ctr=ctr,
                    lim=lim,
                    state_vars=state_vars,
                    params=params,
                    if_budget=if_budget,
                    assign_total=assign_total,
                    nla_family=nla_family,
                )
            )
            payload = self._extract_first_json_object(resp or "")
            if not payload:
                return None
            return self._validate_llm_core_payload(
                core_name=core_name,
                payload=payload,
                ctr=ctr,
                lim=lim,
                state_vars=state_vars,
                params=params,
                if_budget=if_budget,
                assign_total=assign_total,
            )
        except Exception:
            logging.getLogger(__name__).debug("LLM core generation failed for %s", core_name, exc_info=True)
            return None

    def _inject_multivar_extension(
        self,
        body: List[Stmt],
        core_name: str,
        free_vars: Sequence[str],
        driver_vars: Sequence[str],
        ctr: str,
        lim: str,
        nla_family: bool,
        assign_budget_left: int,
    ) -> int:
        """
        Extend a template with additional vars using a three-way policy:
        1) no participation
        2) simple linear update (non-intrusive)
        3) template-native expansion (only if this core supports it)
        """
        if not free_vars or assign_budget_left <= 0:
            return 0
        written = set(_get_written_vars(body))
        untouched = [v for v in free_vars if v not in written]
        if not untouched:
            return 0

        drivers = list(driver_vars) or [ctr, lim]
        native_style = CORE_NATIVE_EXTENSION_STYLE.get(core_name, "linear")
        native_enabled = True
        added = 0
        considered = 0
        prev_native = ctr
        symbolic_added = False
        last_added_idx = -1
        symbol_pool = list(dict.fromkeys(list(drivers) + [ctr, lim]))
        for v in untouched:
            if added >= assign_budget_left:
                break
            considered += 1
            behavior = self._sample_extra_var_behavior(native_enabled=native_enabled)
            if behavior == "none":
                continue

            d1 = self.rng.choice(drivers)
            if behavior == "simple":
                if nla_family and self.rng.random() < 0.35:
                    expr = f"{v}+({d1}%{self.rng.randint(2, 9)})"
                elif self.rng.random() < 0.55:
                    expr = f"{v}+{self.rng.randint(1, 3)}"
                else:
                    expr = f"{v}+{d1}"
            else:
                expr = self._sample_native_extension_expr(
                    style=native_style,
                    v=v,
                    drivers=drivers,
                    prev_native=prev_native,
                    ctr=ctr,
                    lim=lim,
                )
                prev_native = v
            body.append(Assign(v, expr))
            last_added_idx = len(body) - 1
            if _expr_contains_symbol(expr, symbol_pool):
                symbolic_added = True
            added += 1
        # Generalization guardrail:
        # if we added extension updates but all became constant-like,
        # force one symbolic dependency on loop/context variables.
        if added > 0 and not symbolic_added and 0 <= last_added_idx < len(body):
            tgt = body[last_added_idx].target if isinstance(body[last_added_idx], Assign) else None
            if tgt:
                d = self.rng.choice(symbol_pool or [ctr])
                body[last_added_idx] = Assign(tgt, f"{tgt}+{d}")
        # Guarantee: if probabilistic pass skipped every free var despite having
        # budget, force-assign at least one so no program has purely dead state vars.
        if added == 0 and untouched and assign_budget_left > 0:
            v = untouched[0]
            d = self.rng.choice(symbol_pool or [ctr])
            body.append(Assign(v, f"{v}+{d}"))
            added = 1
        elif considered > 0 and added == 0:
            self.var_extension_shortfall += 1
        return added

    def _seed_family_kernel(
        self,
        body: List[Stmt],
        writable: Sequence[str],
        ctr: str,
        assign_budget: int,
        nla_family: bool,
    ) -> int:
        used = 0
        if len(writable) < 2:
            return used

        if nla_family:
            # NLA-like recurrences with generalized semantic motifs:
            # affine chains, multiply-add, scaling pairs.
            a, b = writable[0], writable[1]
            c = writable[2] if len(writable) >= 3 else b
            d = writable[3] if len(writable) >= 4 else a
            mul = self.rng.randint(2, 4)
            off = self.rng.randint(1, 5)
            kernels = [
                [Assign(a, f"{a}+{b}"), Assign(b, f"{b}+{c}"), Assign(c, f"{c}+{self.rng.randint(1, 6)}")],
                [Assign(a, f"{a}*2"), Assign(b, f"{b}+{a}"), Assign(c, f"{c}%{self.rng.randint(2, 9)}")],
                [Assign(a, f"{a}+{ctr}"), Assign(b, f"{b}*{b}"), Assign(c, f"{c}+{a}*{b}")],
                [Assign(a, f"{a}*{mul}+{off}"), Assign(b, f"{b}*{a}+{off}")],
                [Assign(a, f"{a}*{mul}"), Assign(b, f"{b}/{mul}")],
                [Assign(d, f"{d}*{d}+{a}"), Assign(a, f"{a}%{self.rng.randint(2, 9)}")],
            ]
        else:
            # linear-like transitions with generalized semantic motifs:
            # conservation pairs, affine chains, counter decomposition.
            a, b = writable[0], writable[1]
            c = writable[2] if len(writable) >= 3 else b
            d = writable[3] if len(writable) >= 4 else a
            off = self.rng.randint(1, 5)
            kernels = [
                [Assign(a, f"{a}+1"), Assign(b, f"{b}+{a}")],
                [Assign(a, f"{a}+{self.rng.randint(1, 5)}"), Assign(c, f"{c}+{self.rng.randint(1, 4)}")],
                [Assign(b, f"{b}+{c}"), Assign(c, f"{c}+{a}")],
                [Assign(a, f"{a}+1"), Assign(b, f"{b}-1")],
                [Assign(a, f"{a}+{off}"), Assign(b, f"{b}+{a}"), Assign(c, f"{c}+{b}")],
                [Assign(d, f"{a}+{b}+{c}"), Assign(a, f"{a}+1")],
            ]

        k = self.rng.choice(kernels)
        for st in k:
            if used < assign_budget:
                body.append(st)
                used += 1
            else:
                break
        return used

    def _sample_core_loop(
        self,
        alloc: NameAllocator,
        params: Sequence[str],
        universe: List[str],
        remaining_local_budget: int,
        core_usage: Dict[str, int],
        force_core: Optional[str] = None,
    ) -> Tuple[List[Tuple[str, str]], Stmt, List[str], str, List[str]]:
        src = self.rng.choice(list(params)) if params else "1"
        nla_family = self.rng.random() < self.hp.p_nonlinear

        # Allow loops to share existing locals when new-local budget is tight.
        reusable = [v for v in dict.fromkeys(universe) if v not in params]
        use_shared_locals = remaining_local_budget < 3 and len(reusable) >= 3
        state_cap = max(1, remaining_local_budget - 2)

        if use_shared_locals:
            ctr = self.rng.choice(reusable)
            lim_candidates = [v for v in reusable if v != ctr]
            lim = self.rng.choice(lim_candidates) if lim_candidates else ctr
            state_pool = [v for v in reusable if v not in {ctr, lim}] or [ctr]
            max_state = max(1, min(len(state_pool), 6))
            if nla_family:
                lo = 2 if max_state >= 2 else 1
                state_n = self.rng.randint(lo, max_state)
            else:
                state_n = self.rng.randint(1, max_state)
            state_vars = self.rng.sample(state_pool, k=min(state_n, len(state_pool)))
        else:
            ctr_hint = self.rng.choice(["i", "j", "k", "t", "u", "v"])
            lim_hint = self.rng.choice(["l", "h", "n", "m", "r", "b"])
            ctr = alloc.alloc(ctr_hint)
            lim = alloc.alloc(lim_hint)
            # Reserve 2 locals for loop control (ctr/lim), others for state vars.
            state_vars = self._sample_state_vars(alloc, nla_family, state_cap)

        # Forced core mode is used by probing/auditing and can bypass candidate gating.
        # Ensure enough distinct state vars for that core; otherwise resample upstream.
        if force_core is not None:
            req = max(1, CORE_MIN_STATE_VARS.get(force_core, 4))
            if len(state_vars) < req:
                if use_shared_locals:
                    raise RuntimeError(
                        f"insufficient shared state vars for forced core {force_core}: "
                        f"need {req}, got {len(state_vars)}"
                    )
                while len(state_vars) < min(req, state_cap):
                    state_vars.append(alloc.alloc("v"))
                if len(state_vars) < req:
                    raise RuntimeError(
                        f"insufficient state vars for forced core {force_core}: "
                        f"need {req}, got {len(state_vars)}"
                    )

        ctrl_inits, guard, step_stmt = self._sample_loop_control(src, ctr, lim, nla_family)
        init_pool = universe + list(params) + [ctr, lim]

        inits: List[Tuple[str, str]] = []
        if not use_shared_locals:
            inits.extend(ctrl_inits)
        for sv in state_vars:
            if not use_shared_locals or sv not in reusable:
                if self.rng.random() < 0.15:
                    inits.append((sv, self._diverse_init(0, role="param", src=src)))
                else:
                    inits.append((sv, self._sample_operand(init_pool, allow_const=True)))

        vars_pool = list(dict.fromkeys(universe + list(params) + state_vars + [ctr, lim]))

        # Per-loop sampled fuel:
        # - if/if-else blocks in [0, ifelse_fuel]
        # - assigns in [1, assign_fuel], with one assign reserved for loop-step
        if_lo = max(0, self.hp.min_ifelse)
        if_hi = max(if_lo, self.hp.ifelse_fuel)
        if_budget = self.rng.randint(if_lo, if_hi)
        asg_lo = max(1, self.hp.min_assign)
        asg_hi = max(asg_lo, self.hp.assign_fuel)
        assign_total = self.rng.randint(asg_lo, asg_hi)

        body: List[Stmt] = []
        used_if = 0
        used_assign = 0
        append_step = True

        def set_init(name: str, expr: str) -> None:
            for i, (v, _) in enumerate(inits):
                if v == name:
                    inits[i] = (name, expr)
                    return

        # Generalized core rules extracted from target datasets (not exact copies).
        # Covers additional semantic motifs:
        # linear conservation, affine chain, multiply-add,
        # remainder buckets, quotient-remainder coupling,
        # monotone-bound update, phase switching,
        # saturation/truncation, scaling pair,
        # two-var compare driven, branch + fixed updates,
        # counter decomposition.
        core_applied = False

        # State variable aliases — always set (needed even when force_core bypasses sampling).
        a = state_vars[0]
        b = state_vars[1] if len(state_vars) > 1 else state_vars[0]
        c = state_vars[2] if len(state_vars) > 2 else state_vars[0]
        d = state_vars[3] if len(state_vars) > 3 else state_vars[0]
        e = state_vars[4] if len(state_vars) > 4 else state_vars[0]

        # Determine which semantic template to apply.
        # Enters if: (a) force_core specified by multi-loop pairing, or (b) passes probabilistic gate.
        if force_core is not None or self.rng.random() < self.hp.p_semantic_core:
            chosen = force_core if force_core is not None else ""
            if chosen and self.hp.allowed_cores and chosen not in self.hp.allowed_cores:
                chosen = ""
            if not chosen:
                candidates: List[str] = []
                weights: List[float] = []

                def allow(name: str, w: float, need_if: int, need_asg: int, need_vars: int) -> None:
                    if self.hp.allowed_cores and name not in self.hp.allowed_cores:
                        return
                    if w > 0 and if_budget >= need_if and assign_total >= need_asg and len(state_vars) >= need_vars:
                        repeat = core_usage.get(name, 0)
                        # Flatten core selection and penalize repeated motifs per program.
                        shaped = w ** max(0.25, CORE_WEIGHT_TEMPERATURE)
                        novelty = CORE_REPEAT_PENALTY ** repeat
                        candidates.append(name)
                        weights.append(shaped * novelty)

                # Existing controls reused as coarse weights.
                rel_w = self.hp.w_core_rel_guard
                cond_w = self.hp.w_core_cond_fixed
                lin_w = self.hp.w_core_linear_state
                min_w = self.hp.w_core_min_update
                qr_w = self.hp.w_core_qr_division
                euclid_w = self.hp.w_core_euclid_matrix

                allow("cond_fixed", cond_w if nla_family else 0.0, 1, 4, 3)       # branch + fixed updates
                allow("linear_conservation_family", lin_w + cond_w + 0.2, 0, 2, 2) # conservation/lockstep/counter-compensation
                allow("affine_chain", lin_w + cond_w + 0.5, 0, 3, 3)              # affine recurrence chain
                allow("remainder_buckets", cond_w, 2, 2, 3)                        # remainder bucket counting
                allow("monotone_bound", lin_w + 1.0, 1, 1, 2)                     # monotone bound-tied update
                allow("phase_switch", cond_w + 1.0, 1, 2, 2)                      # phase-dependent update law
                allow("saturation", cond_w, 1, 1, 2)                               # saturation/truncation
                allow("scaling_pair", cond_w if nla_family else 0.0, 0, 2, 2)      # nonlinear-only scaling pair
                allow("counter_decomp", lin_w, 0, 4, 4)                            # counter decomposition
                allow("gcd_compare", cond_w if nla_family else lin_w, 1, 1, 2)     # compare-driven dual decrease

                # Extra linear cores inspired by src/input/linear motifs.
                allow("snapshot_family", lin_w + cond_w, 1, 2, 3)                   # snapshot/guarded_snapshot/chase
                allow("complement_step", lin_w + 0.5 * cond_w, 0, 2, 2)             # y=n-x; x=x+1
                allow("triple_decrease", lin_w + cond_w, 2, 3, 3)                   # if(a>0) if(b>0) x-=1,y-=1,z-=1
                allow("stride_family", lin_w + 0.5 * cond_w, 0, 1, 2)               # fixed/proportional strides
                allow("min_update_guarded_bound", min_w + 0.6, 1, 2, 3)             # while(x<lim) {x+=1; if(z<=y) y=z;}
                allow("negative_cross_progress", lin_w + 1.1, 0, 2, 2)              # x<0; x+=y; y+=1 (linear/84,85-like)
                allow("triplet_lockstep_stride", lin_w + 0.9, 0, 3, 3)              # i/j/k synchronized +s (linear/315,316-like)
                allow("threshold_tail_accumulate", lin_w + 0.8, 1, 2, 2)            # second-half gated accumulate (linear/304-like)
                allow("half_split_balance", lin_w + cond_w, 1, 2, 2)                # y++ first half, y-- second half (linear/296-like)
                allow("mod_bucket_cascade", lin_w + cond_w + 0.4, 3, 5, 5)          # divisibility bucket chain (linear/313-like)

                # Generic complex paradigms (dataset-agnostic).
                allow("nested_guarded_transitions", lin_w + cond_w, 2, 5, 4)
                allow("piecewise_recurrence", (cond_w + rel_w) if nla_family else 0.0, 2, 6, 5)
                allow("qr_division_step", qr_w, 1, 2, 4)                            # x>y*q+r with q/r updates
                allow("euclid_matrix", euclid_w, 1, 6, 6)                           # coupled Euclid-style updates
                allow("while_one_break_counter", lin_w + cond_w + 0.8, 1, 2, 2)     # explicit while(1) + break
                allow("triple_recurrence_inc", qr_w, 0, 4, 4)                       # n++; x=x+y; y=y+z; z=z+c
                allow("qr_countdown_bucket", qr_w, 1, 3, 4)                         # if(r+1==B){q++;r=0;t--}else{r++;t--}
                # Body-first cores requested by user (not bound to while(1)).
                allow("triple_recurrence_step", qr_w + 0.5, 0, 4, 4)                # x=x+y; y=y+z; z=z+const; n++
                allow("accumulate_family", lin_w + 0.2, 0, 1, 2)                    # simple_accumulate/linear_product_reduce
                allow("prefix_sum_family", lin_w + 0.3, 0, 2, 3)                    # triangular/sum-before/prefix-sum
                allow("mul_affine_param_pair", (cond_w + 0.8) if nla_family else (lin_w + 0.6), 0, 2, 4)  # merged mul-affine family
                allow("power_accumulate", cond_w if nla_family else (lin_w + 0.5), 0, 2, 3)  # y++; x+=y^k
                allow("parity_decomposition_product", cond_w + qr_w + 0.9, 2, 5, 4)          # parity-driven multiplicative decomposition
                allow("odd_step_accumulator", lin_w + cond_w + 0.8, 0, 3, 3)                  # odd-step ladder with monotone counter
                allow("square_sync_progress", lin_w + cond_w + 0.7, 0, 2, 2)                  # y++ and x=y*y synchronization
                allow("multiplicative_shadow_progress", cond_w + 0.9, 1, 3, 3)                # coupled product with guarded shadow product
                allow("quadratic_form_triplet", cond_w + 0.9, 0, 4, 4)                        # three-way quadratic-form accumulation
                allow("euclid_coupled_accumulator", euclid_w + 0.7, 1, 3, 4)                  # Euclid-style reduction with coupled drift
                allow("fixed_point_root_refinement", cond_w + rel_w + 0.7, 0, 2, 3)           # fixed-point integer root refinement
                allow("residual_branch_walk", cond_w + 0.9, 1, 3, 4)                           # branch-controlled residual walk
                allow("multi_branch_swap_recurrence", qr_w + cond_w + 1.0, 3, 8, 6)           # 4-way swap recurrence with moving threshold
                # while(1)-specific cores (all unique by body shape + break condition).
                allow("while_one_min_break", min_w + 1.0, 2, 3, 3)                  # break on ctr>=lim; min-update + ctr++
                allow("while_one_qr_break", qr_w + 1.0, 2, 3, 4)                    # break on x<=y*q+r; qr step
                allow("while_one_mul_break", cond_w + 1.0, 1, 4, 4)                 # break on c>=lim; mul-affine pair
                allow("while_one_recurrence_break", qr_w + 0.9, 1, 5, 4)            # break on n>lim; 3-var recurrence
                # ── Cores derived from linear/ and NLA_lipus/ real benchmarks ──────────
                allow("parity_alternating", cond_w, 1, 2, 4)                         # flag-flip dual counter (linear/176)
                allow("russian_multiply", cond_w if nla_family else 0.0, 1, 3, 3)   # z+=x;x*=2;y/=2 (NLA/14)
                allow("cauchy_schwarz_triple", qr_w if nla_family else (lin_w * 0.3), 0, 4, 4)  # z+=x²;w+=y²;p+=xy (NLA/29)
                allow("int_sqrt_sieve", lin_w + 0.5, 0, 2, 2)                       # x-=r; r++ (NLA/36)
                allow("countdown_triple", lin_w + 1.1, 0, 3, 3)                     # lo++;hi--;mid-- (linear/145)
                # Extra targeted cores for uncovered linear patterns.
                allow("binary_toggle", cond_w + 0.3, 1, 1, 1)                       # if(x==1)x=2; else if(x==2)x=1
                allow("gap_drift_piecewise", cond_w + 0.7, 1, 3, 2)                 # if(x-y<k){x--;y+=2}else{y++}
                allow("alternating_series_accumulator", cond_w + 0.8, 1, 5, 4)      # term recurrence + alternating sign
                allow("turn_based_state_machine", cond_w + rel_w + 0.8, 3, 5, 4)    # turn-driven multi-phase updates
                allow("equal_pair_piecewise_increment", cond_w + 0.7, 2, 5, 3)      # a/b same-step piecewise increments
                # ── New templates from semantic plan (boosted weights for coverage) ──────
                allow("cache_coherence",         lin_w + cond_w + 0.8, 1, 3, 2)   # L14: free+owned conservation
                allow("multi_countdown_parallel", lin_w + 1.3, 1, 2, 2)            # L15: alternating countdown
                allow("geometric_doubling_bound", lin_w + 1.2, 0, 2, 2)            # L17: z*=2, assert z > n
                allow("sawtooth_modular_counter", lin_w + 1.3, 0, 2, 2)            # L18: c=(c+1)%PERIOD
                allow("decaying_stride",          lin_w + 1.3, 0, 3, 3)            # L20: i++;j+=k;k--
                allow("bouncing_counter",          lin_w + 1.2, 1, 3, 2)           # X5: x bounces between lo and hi
                allow("modular_equality_race",     lin_w + 1.2, 0, 2, 2)           # X12: a%m==b%m
                # ── New cores from benchmark analysis (10 new semantic classes) ────────────
                allow("transfer_conservation",    lin_w + 1.0, 0, 2, 2)           # linear/100: x=N,y=0;y+=S;x-=S; x+y==N
                allow("carry_pair_counter",      lin_w + 1.0, 1, 3, 3)           # radix-B carry pair: t=q*B+r, 0<=r<B
                allow("ramped_transfer_conservation", lin_w + 1.0, 1, 4, 4)      # capped transfer with ramped step
                allow("alternating_swap_transfer", lin_w + cond_w + 0.7, 1, 4, 3) # toggle-based two-way transfer
                allow("scheduled_queue_occupancy", lin_w + cond_w + 0.8, 2, 5, 5) # periodic push/pop occupancy tracking
                allow("nested_triangular_accumulate", lin_w + 1.1, 0, 2, 4)        # nested while: reset+inner accumulate
                allow("nested_triangular_balance", lin_w + 1.0, 0, 2, 4)           # nested while: dual accumulator balance
                allow("nested_grid_rowcol_sum", lin_w + 1.1, 0, 2, 4)              # nested while: row/col traversal
                allow("nested_grid_checkerboard", lin_w + cond_w + 0.8, 1, 2, 4)   # nested while + parity branch
                allow("nested_block_drain", lin_w + cond_w + 0.9, 0, 2, 4)         # nested while: bounded drain per outer block
                allow("nested_block_staircase", lin_w + 1.0, 0, 2, 4)              # nested while: staircase inner work
                allow("x1_geometric_growth_bound", lin_w + 0.9, 0, 2, 2)          # doubling growth until bound exceeded
                allow("x17_harmonic_step_reduction", lin_w + cond_w + 0.7, 1, 4, 3) # denominator-ladder reduction pattern
                allow("x19_rolling_sum_window", lin_w + cond_w + 0.8, 1, 5, 4)    # rolling add/remove window sum
                allow("random_walk_bounded",      lin_w + cond_w + 0.8, 1, 3, 2)  # linear/158: ±1 walk; |a|<=step_counter
                allow("ghost_sync_pair",          lin_w + 1.0, 1, 3, 2)           # linear/220: x=w; always move together
                allow("product_reduction_walk",   cond_w if nla_family else (lin_w * 0.5), 0, 2, 3)  # NLA/24,27: z=x*y;x--;z-=y
                allow("partial_product_conservation", cond_w if nla_family else 0.0, 0, 2, 4)        # NLA/34,35: x*u+y*v==a*b
                allow("cumulative_double_sum",    cond_w if nla_family else (lin_w * 0.3), 0, 3, 4)  # NLA/28: z+=x;p+=z; 2p==x*w*(w+1)
                allow("power_sum_series",         cond_w if nla_family else (lin_w * 0.4), 0, 3, 3)  # NLA/15-16: c++;y++;x+=y*y
                allow("newton_sqrt_convergence",  cond_w if nla_family else 0.0, 0, 2, 2)            # NLA/37,38: Newton int-sqrt
                allow("bresenham_line_step",      lin_w + 0.8, 1, 3, 3)           # NLA/41: Bresenham line; decision var v
                allow("nondeterministic_multi_decrement", lin_w + 0.9, 3, 4, 3)   # linear/200: 3-var guarded decrement
                # ── Trivial fallbacks: always qualify, guarantee 100% template coverage ──
                # Low weight (0.6) so they only fire when richer templates are unavailable.
                allow("L1_trivial", 0.6, 0, 1, 1)
                allow("L2_trivial", 0.6, 0, 1, 1)

                chosen = self.rng.choices(candidates, weights=weights, k=1)[0] if candidates else ""

            llm_generated = self._generate_core_loop_with_llm(
                core_name=chosen,
                ctr=ctr,
                lim=lim,
                state_vars=state_vars,
                params=params,
                if_budget=if_budget,
                assign_total=assign_total,
                nla_family=nla_family,
            ) if chosen else None
            if llm_generated is not None:
                llm_guard, llm_init_overrides, llm_body, _llm_summary = llm_generated
                for name, expr in llm_init_overrides.items():
                    set_init(name, expr)
                guard = llm_guard
                body.extend(llm_body)
                used_if = sum(1 for st in llm_body if isinstance(st, (IfOnly, IfElse)))
                used_assign = sum(1 for st in llm_body if isinstance(st, Assign))
                core_applied = True

            if core_applied:
                pass
            elif chosen == "cond_fixed":
                # Branch updates + fixed updates outside branch.
                set_init(a, f"({src}%20)+1")
                set_init(b, f"({src}%25)+1")
                set_init(c, "0")
                guard = f"{b}!=0"
                body.append(IfElse(cond=f"{b}%2==1", then_body=[Assign(c, f"{c}+{a}"), Assign(b, f"{b}-1")], else_body=[]))
                body.append(Assign(a, f"2*{a}"))
                body.append(Assign(b, f"{b}/2"))
                used_if += 1
                used_assign += 4
                core_applied = True
            elif chosen == "linear_conservation_family":
                # Merged family:
                # - conservation pair
                # - lockstep equal increments
                # - counter compensation (sum conservation)
                mode = self.rng.choice(["conservation", "lockstep", "counter_comp"])
                if mode == "conservation":
                    step = self.rng.randint(1, 4)
                    if self.rng.random() < 0.4:
                        body.extend([Assign(a, f"{a}+{step}"), Assign(b, f"{b}-{step}")])
                    elif self.rng.random() < 0.7:
                        body.extend([Assign(a, f"{a}+{step}"), Assign(b, f"{b}+{step}")])
                    else:
                        body.extend([Assign(a, f"{a}+{step}"), Assign(b, f"{b}+{a}")])
                    used_assign += 2
                elif mode == "lockstep":
                    body.extend([Assign(a, f"{a}+1"), Assign(b, f"{b}+1")])
                    used_assign += 2
                else:
                    set_init(a, "0")
                    set_init(b, lim)
                    guard = f"{a}<{lim}&&{b}>0"
                    body.extend([Assign(a, f"{a}+1"), Assign(b, f"{b}-1")])
                    used_assign += 2
                core_applied = True
            elif chosen == "affine_chain":
                # Affine recurrence chain variants: 2/3-node chain or branch-conditioned chain.
                mode = self.rng.choice(["chain2", "chain3", "branch_chain"])
                k = self._core_const(1, 6)
                body.append(Assign(a, f"{a}+{k}"))
                if mode == "chain2":
                    body.append(Assign(b, f"{b}+{a}"))
                    used_assign += 2
                elif mode == "chain3":
                    body.append(Assign(b, f"{b}+{a}"))
                    body.append(Assign(c, f"{c}+{b}"))
                    used_assign += 3
                else:
                    body.append(
                        IfElse(
                            cond=f"{ctr}%2==0",
                            then_body=[Assign(b, f"{b}+{a}")],
                            else_body=[Assign(b, f"{b}+{c}")],
                        )
                    )
                    used_if += 1
                    used_assign += 3
                core_applied = True
            elif chosen == "remainder_buckets":
                # Remainder bucket counting with 2-way split (generalizable).
                k = self.rng.randint(2, 6)
                r = self.rng.randint(0, k - 1)
                body.append(IfElse(cond=f"{ctr}%{k}=={r}", then_body=[Assign(a, f"{a}+1")], else_body=[Assign(b, f"{b}+1")]))
                # second split to mimic multi-bucket partitions
                body.append(IfElse(cond=f"{ctr}%{k}=={(r+1)%k}", then_body=[Assign(c, f"{c}+1")], else_body=[]))
                used_if += 2
                used_assign += 2
                core_applied = True
            elif chosen == "monotone_bound":
                # Monotone variable tied to guard, with speed variants.
                guard = f"{a}<{lim}"
                mode = self.rng.choice(["base", "var_step", "piecewise"])
                if mode == "base":
                    body.append(Assign(a, f"{a}+1"))
                    used_assign += 1
                elif mode == "var_step":
                    body.append(Assign(a, f"{a}+{self._core_const(1, 4)}"))
                    used_assign += 1
                else:
                    body.append(
                        IfElse(
                            cond=f"{a}<{lim}/2",
                            then_body=[Assign(a, f"{a}+2")],
                            else_body=[Assign(a, f"{a}+1")],
                        )
                    )
                    used_if += 1
                    used_assign += 1
                core_applied = True
            elif chosen == "phase_switch":
                # Phase-dependent update law.
                body.append(
                    IfElse(
                        cond=f"{ctr}<{lim}/2",
                        then_body=[Assign(a, f"{a}+{b}")],
                        else_body=[Assign(a, f"{a}*{b}") if nla_family else Assign(a, f"{a}+1")],
                    )
                )
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "saturation":
                # Saturation/truncation via if-else (DSL equivalent).
                cst = self.rng.randint(1, 6)
                body.append(IfElse(cond=f"{a}+{cst}<={lim}", then_body=[Assign(a, f"{a}+{cst}")], else_body=[Assign(a, lim)]))
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "scaling_pair":
                # Scaling pair.
                k = self.rng.randint(2, 4)
                body.extend([Assign(a, f"{a}*{k}"), Assign(b, f"{b}/{k}")])
                used_assign += 2
                core_applied = True
            elif chosen == "counter_decomp":
                # Decomposition: c1+c2+c3 tracks step-like progress.
                body.extend([Assign(a, f"{a}+1"), Assign(b, f"{b}+1"), Assign(c, f"{c}+1"), Assign(d, f"{a}+{b}+{c}")])
                used_assign += 4
                core_applied = True
            elif chosen == "gcd_compare":
                # Compare-driven dual-variable decrease.
                guard = f"{a}!=0&&{b}!=0"
                body.append(IfElse(cond=f"{a}>{b}", then_body=[Assign(a, f"{a}-{b}")], else_body=[Assign(b, f"{b}-{a}")]))
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "snapshot_family":
                # Merged family:
                # - snapshot_step: m=x; x=x+c
                # - guarded_snapshot: if(g<lim)m=x; x++
                # - snapshot_chase: while(x!=0){x--;y--;}
                mode = self.rng.choice(["snapshot_step", "guarded_snapshot", "offset_snapshot", "snapshot_chase"])
                if mode == "snapshot_step":
                    step = self._core_const(1, 5)
                    set_init(a, self._diverse_init(0, role="ctr"))
                    guard = self.rng.choice([f"{a}<{lim}", f"{a}<={lim}-1", f"{a}+1<={lim}"])
                    body.extend([Assign(b, a), Assign(a, f"{a}+{step}")])
                    used_assign += 2
                elif mode == "guarded_snapshot":
                    guard_var = c
                    set_init(a, self._diverse_init(0, role="ctr"))
                    set_init(guard_var, self._diverse_init(0, role="ctr"))
                    guard = self.rng.choice([f"{a}<{lim}", f"{a}<={lim}-1", f"{a}+1<={lim}"])
                    body.append(IfOnly(cond=f"{guard_var}<{lim}", then_body=[Assign(b, a)]))
                    body.append(Assign(a, f"{a}+1"))
                    if self.rng.random() < 0.5:
                        body.append(Assign(guard_var, f"{guard_var}+{self._core_const(1, 3)}"))
                    used_if += 1
                    used_assign += 3 if any(isinstance(st, Assign) and st.target == guard_var for st in body[-1:]) else 2
                elif mode == "offset_snapshot":
                    off = self._core_const(1, 6)
                    step = self._core_const(1, 4)
                    set_init(a, self._diverse_init(0, role="ctr"))
                    guard = self.rng.choice([f"{a}<{lim}", f"{a}<={lim}-1", f"{a}+{step}<={lim}+{step}-1"])
                    body.extend([Assign(b, f"{a}+{off}"), Assign(a, f"{a}+{step}")])
                    used_assign += 2
                else:
                    set_init(c, a)
                    set_init(a, f"({src}%18)+5")
                    set_init(b, f"({src}%15)+3")
                    guard = f"{a}!=0"
                    body.extend([Assign(a, f"{a}-1"), Assign(b, f"{b}-1")])
                    used_assign += 2
                core_applied = True
            elif chosen == "complement_step":
                # linear motif variants: y=n-x with variable/reordered step.
                set_init(a, self._diverse_init(0, role="ctr"))
                guard = f"{a}<{lim}"
                mode = self.rng.choice(["base", "var_step", "reversed"])
                if mode == "base":
                    body.extend([Assign(b, f"{lim}-{a}"), Assign(a, f"{a}+1")])
                elif mode == "var_step":
                    step = self._core_const(1, 5)
                    body.extend([Assign(b, f"{lim}-{a}"), Assign(a, f"{a}+{step}")])
                else:
                    body.extend([Assign(a, f"{a}+1"), Assign(b, f"{lim}-{a}")])
                used_assign += 2
                core_applied = True
            elif chosen == "triple_decrease":
                # linear motif: nested guards + synchronized decreases
                set_init(a, f"({src}%20)+5")
                set_init(b, f"({src}%20)+5")
                set_init(c, f"({src}%20)+5")
                guard = f"{a}>0"
                body.append(
                    IfOnly(
                        cond=f"{b}>0",
                        then_body=[
                            IfOnly(cond=f"{c}>0", then_body=[Assign(a, f"{a}-1"), Assign(b, f"{b}-1"), Assign(c, f"{c}-1")])
                        ],
                    )
                )
                used_if += 2
                used_assign += 3
                core_applied = True
            elif chosen == "stride_family":
                # Merged family:
                # - stride_progress / fixed_stride_progress
                # - proportional_stride
                mode = self.rng.choice(["fixed", "proportional"])
                if mode == "fixed":
                    set_init(a, self._diverse_init(0, role="ctr"))
                    guard = f"{a}<{lim}"
                    step = self._core_const(2, 8)
                    v = self.rng.choice(["base", "skip", "jitter"])
                    if v == "base":
                        body.append(Assign(a, f"{a}+{step}"))
                        used_assign += 1
                    elif v == "skip":
                        k = self._core_const(2, 7)
                        body.append(Assign(a, f"{a}+{step}"))
                        body.append(IfOnly(cond=f"{a}%{k}==0", then_body=[Assign(a, f"{a}+1")]))
                        used_if += 1
                        used_assign += 2
                    else:
                        body.append(Assign(a, f"{a}+{step}+{ctr}%2"))
                        used_assign += 1
                else:
                    step_ratio = self._core_const(2, 8)
                    set_init(a, self._diverse_init(0, role="ctr"))
                    set_init(b, self._diverse_init(0, role="acc"))
                    guard = f"{a}<{lim}"
                    body.append(Assign(b, f"{b}+{step_ratio}"))
                    body.append(Assign(a, f"{a}+1"))
                    used_assign += 2
                core_applied = True
            elif chosen == "min_update_guarded_bound":
                # Strong linear target: bounded progress + guarded min-update.
                set_init(a, "0")
                guard = f"{a}<{lim}"
                step = self.rng.randint(1, 2)
                body.append(Assign(a, f"{a}+{step}"))
                if self.rng.random() < 0.5:
                    body.append(IfOnly(cond=f"{d}<={c}", then_body=[Assign(c, d)]))
                else:
                    body.append(IfOnly(cond=f"{c}<={b}", then_body=[Assign(b, c)]))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "negative_cross_progress":
                # Variant family inspired by linear/84.c and linear/85.c,
                # but intentionally avoids exact same shape.
                # Examples:
                #   while (x <= -k) { x = x + y + c1; y = y + c2; }
                #   while (x + k < 0) { x = x + y - c1; y = y + c2; }
                neg_start = self.rng.randint(20, 20000)
                bias = self.rng.randint(1, 3)
                y_step = self.rng.randint(1, 3)
                thresh = self.rng.randint(1, 8)
                set_init(a, f"-{neg_start}")
                if self.rng.random() < 0.5:
                    guard = f"{a}<=-{thresh}"
                else:
                    guard = f"{a}+{thresh}<0"
                if self.rng.random() < 0.5:
                    body.append(Assign(a, f"{a}+{b}+{bias}"))
                else:
                    body.append(Assign(a, f"{a}+{b}-{bias}"))
                body.append(Assign(b, f"{b}+{y_step}"))
                used_assign += 2
                core_applied = True
            elif chosen == "triplet_lockstep_stride":
                # Three counters progress in lockstep with identical stride.
                stride = self.rng.randint(2, 5)
                set_init(a, "0")
                set_init(b, str(self.rng.randint(0, 2)))
                set_init(c, str(self.rng.randint(0, 2)))
                guard = f"{a}<{lim}"
                body.append(Assign(a, f"{a}+{stride}"))
                body.append(Assign(b, f"{b}+{stride}"))
                body.append(Assign(c, f"{c}+{stride}"))
                used_assign += 3
                core_applied = True
            elif chosen == "threshold_tail_accumulate":
                # Threshold-gated tail accumulation with explicit progress.
                step = self.rng.choice([2, 4])
                set_init(a, "0")
                guard = f"{a}<{lim}"
                body.append(IfOnly(cond=f"{a}>={lim}/2", then_body=[Assign(b, f"{b}+{step}")]))
                body.append(Assign(a, f"{a}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "half_split_balance":
                # First-half increment, second-half decrement: balanced piecewise drift.
                step = self.rng.randint(1, 3)
                set_init(a, "0")
                set_init(b, "0")
                guard = f"{a}<{lim}"
                body.append(
                    IfElse(
                        cond=f"{a}<{lim}/2",
                        then_body=[Assign(b, f"{b}+{step}")],
                        else_body=[Assign(b, f"{b}-{step}")],
                    )
                )
                body.append(Assign(a, f"{a}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "mod_bucket_cascade":
                # Generic modular/divisibility classification loop with many buckets,
                # optional weighted accumulation, and a long else-if chain.
                mod_pool = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
                self.rng.shuffle(mod_pool)
                bucket_vars = list(state_vars[1:])
                max_branches = min(len(bucket_vars), max(4, if_budget + 1), max(4, assign_total - 1), 8)
                branch_slots = max(4, min(max_branches, len(bucket_vars)))
                chosen_buckets = bucket_vars[:branch_slots]
                chosen_mods = sorted(mod_pool[: max(1, len(chosen_buckets) - 1)], reverse=True)
                agg = state_vars[1 + len(chosen_buckets)] if len(state_vars) > 1 + len(chosen_buckets) else None
                drift = state_vars[2 + len(chosen_buckets)] if len(state_vars) > 2 + len(chosen_buckets) else None
                set_init(a, "0")
                for bucket in chosen_buckets:
                    set_init(bucket, "0")
                if agg is not None:
                    set_init(agg, "0")
                if drift is not None:
                    set_init(drift, "0")
                limit_expr = lim if self.rng.random() < 0.6 else f"{lim}+({src}%7)"
                guard = f"{a}<{limit_expr}"

                weighted = agg is not None and assign_total >= (2 * len(chosen_buckets) + 1)
                fallback_body = [Assign(chosen_buckets[-1], f"{chosen_buckets[-1]}+1")]
                if weighted:
                    fallback_body.append(Assign(agg, f"{agg}+{len(chosen_buckets)}"))
                nested_branch: Stmt = IfOnly(cond="1", then_body=fallback_body)
                for idx, (mod, bucket) in enumerate(reversed(list(zip(chosen_mods, chosen_buckets[:-1]))), start=1):
                    then_body = [Assign(bucket, f"{bucket}+1")]
                    if weighted:
                        then_body.append(Assign(agg, f"{agg}+{len(chosen_buckets) - idx}"))
                    nested_branch = IfElse(
                        cond=f"{a}%{mod}==0",
                        then_body=then_body,
                        else_body=[nested_branch],
                    )
                body.append(nested_branch)
                body.append(Assign(a, f"{a}+1"))
                if drift is not None:
                    drift_base = chosen_mods[self.rng.randrange(len(chosen_mods))]
                    body.append(Assign(drift, f"{drift}+{a}%{drift_base}"))
                used_if += max(0, len(chosen_buckets) - 1)
                used_assign += 1 + len(chosen_buckets) + (len(chosen_buckets) if weighted else 0) + (1 if drift is not None else 0)
                core_applied = True
            elif chosen == "qr_division_step":
                # Quotient-remainder coupling: x > y*q+r.
                set_init(a, f"({src}%60)+60")
                set_init(b, f"({src}%9)+2")
                set_init(c, "0")
                set_init(d, "0")
                guard = f"{a}>{b}*{c}+{d}"
                body.append(
                    IfElse(
                        cond=f"{d}=={b}-1",
                        then_body=[Assign(d, "0"), Assign(c, f"{c}+1")],
                        else_body=[Assign(d, f"{d}+1")],
                    )
                )
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "euclid_matrix":
                # Euclid-style pair reduction with coupled matrix-like updates.
                e = state_vars[4] if len(state_vars) > 4 else a
                f = state_vars[5] if len(state_vars) > 5 else b
                set_init(a, f"({src}%35)+15")
                set_init(b, f"({src}%35)+15")
                set_init(c, "1")
                set_init(d, "0")
                set_init(e, "0")
                set_init(f, "1")
                guard = f"{a}!={b}"
                body.append(
                    IfElse(
                        cond=f"{a}>{b}",
                        then_body=[Assign(a, f"{a}-{b}"), Assign(c, f"{c}-{d}"), Assign(e, f"{e}-{f}")],
                        else_body=[Assign(b, f"{b}-{a}"), Assign(d, f"{d}-{c}"), Assign(f, f"{f}-{e}")],
                    )
                )
                used_if += 1
                used_assign += 6
                core_applied = True
            elif chosen == "while_one_break_counter":
                # Canonical while(1) pattern with explicit break condition.
                guard = "1"
                body.append(IfOnly(cond=f"{ctr}>={lim}", then_body=[Break()]))
                body.append(Assign(a, f"{a}+{self.rng.randint(1, 3)}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "triple_recurrence_inc":
                # n<=a; n++; x=x+y; y=y+z; z=z+c pattern.
                set_init(a, "0")
                set_init(b, "1")
                set_init(c, "6")
                set_init(d, "0")
                guard = f"{d}<={lim}"
                body.append(Assign(d, f"{d}+1"))
                body.append(Assign(a, f"{a}+{b}"))
                body.append(Assign(b, f"{b}+{c}"))
                body.append(Assign(c, f"{c}+{self.rng.choice([2,4,6])}"))
                used_assign += 4
                core_applied = True
            elif chosen == "qr_countdown_bucket":
                # merged qr countdown family:
                # while(t!=0){ if(r+1==B){q++;r=0;t--} else {r++;t--} }
                # or while(t!=0){ if(r+1==B){q++;r=0}else{r++}; t--; }
                set_init(a, "0")  # q
                set_init(b, "0")  # r
                set_init(c, f"({src}%50)+20")  # t
                set_init(d, f"({src}%8)+2")    # B
                guard = f"{c}!=0"
                split_tail = self.rng.random() < 0.5
                body.append(
                    IfElse(
                        cond=f"{b}+1=={d}",
                        then_body=[Assign(a, f"{a}+1"), Assign(b, "0")] + ([] if split_tail else [Assign(c, f"{c}-1")]),
                        else_body=[Assign(b, f"{b}+1")] + ([] if split_tail else [Assign(c, f"{c}-1")]),
                    )
                )
                if split_tail:
                    body.append(Assign(c, f"{c}-1"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "triple_recurrence_step":
                # x=x+y; y=y+z; z=z+const; n++;
                k = self.rng.choice([2, 4, 6])
                guard = f"{d}<={lim}"
                body.append(Assign(a, f"{a}+{b}"))
                body.append(Assign(b, f"{b}+{c}"))
                body.append(Assign(c, f"{c}+{k}"))
                body.append(Assign(d, f"{d}+1"))
                used_assign += 4
                core_applied = True
            elif chosen == "accumulate_family":
                # Merged family:
                # - simple_accumulate: y += x
                # - linear_product_reduce: product += param; i++
                if self.rng.random() < 0.60:
                    set_init(b, self._diverse_init(0, role="acc"))
                    mode = self.rng.choice(["plain", "weighted", "parity"])
                    if mode == "plain":
                        body.append(Assign(b, f"{b}+{a}"))
                        used_assign += 1
                    elif mode == "weighted":
                        body.append(Assign(b, f"{b}+{a}*{ctr}"))
                        used_assign += 1
                    else:
                        body.append(
                            IfElse(
                                cond=f"{ctr}%2==0",
                                then_body=[Assign(b, f"{b}+{a}")],
                                else_body=[Assign(b, f"{b}+{a}+1")],
                            )
                        )
                        used_if += 1
                        used_assign += 1
                else:
                    xp = params[0] if params else src
                    set_init(a, self._diverse_init(0, role="acc"))
                    set_init(b, self._diverse_init(0, role="ctr"))
                    guard = f"{b}<{lim}"
                    body.append(Assign(a, f"{a}+{xp}"))
                    body.append(Assign(b, f"{b}+1"))
                    used_assign += 2
                core_applied = True
            elif chosen == "prefix_sum_family":
                # Merged family with extra arithmetic variants.
                mode = self.rng.choice(["triangular", "sum_before", "squares", "odds"])
                if mode == "triangular":
                    set_init(a, self._diverse_init(0, role="ctr"))
                    set_init(b, self._diverse_init(0, role="acc"))
                    body.append(Assign(a, f"{a}+1"))
                    body.append(Assign(b, f"{b}+{a}"))
                elif mode == "sum_before":
                    set_init(a, self._diverse_init(0, role="ctr"))
                    set_init(b, self._diverse_init(0, role="acc"))
                    guard = f"{a}<{lim}"
                    body.append(Assign(b, f"{b}+{a}"))
                    body.append(Assign(a, f"{a}+1"))
                elif mode == "squares":
                    set_init(a, self._diverse_init(1, role="ctr"))
                    set_init(b, self._diverse_init(0, role="acc"))
                    guard = f"{a}<={lim}"
                    body.append(Assign(b, f"{b}+{a}*{a}"))
                    body.append(Assign(a, f"{a}+1"))
                else:
                    set_init(a, self._diverse_init(1, role="ctr"))
                    set_init(b, self._diverse_init(0, role="acc"))
                    guard = f"{a}<={lim}"
                    body.append(Assign(b, f"{b}+2*{a}-1"))
                    body.append(Assign(a, f"{a}+1"))
                used_assign += 2
                core_applied = True
            elif chosen == "mul_affine_param_pair":
                # merged mul-affine family:
                # c = c + 1; x = x*z + bias; y = y*z
                zvar = d
                set_init(zvar, f"({src}%6)+2")
                guard = f"{c}<{lim}"
                bias_expr = src if self.rng.random() < 0.5 else str(self.rng.randint(1, 4))
                if self.rng.random() < 0.7:
                    body.append(Assign(c, f"{c}+1"))
                    used_assign += 1
                body.append(Assign(a, f"{a}*{zvar}+{bias_expr}"))
                body.append(Assign(b, f"{b}*{zvar}"))
                used_assign += 2
                core_applied = True
            elif chosen == "power_accumulate":
                # y = y + 1; x = x + y^k (k in [2..5], using repeated mul)
                k = self.rng.randint(2, 5)
                term = "*".join([b] * k)
                body.append(Assign(b, f"{b}+1"))
                body.append(Assign(a, f"{a}+{term}"))
                used_assign += 2
                core_applied = True
            elif chosen == "parity_decomposition_product":
                # Parity decomposition with branch-specific multiplicative updates.
                set_init(c, "0")
                set_init(d, "1")
                guard = f"{a}!=0&&{b}!=0"
                body.append(
                    IfElse(
                        cond=f"{a}%2==0&&{b}%2==0",
                        then_body=[Assign(a, f"{a}/2"), Assign(b, f"{b}/2"), Assign(d, f"4*{d}")],
                        else_body=[
                            IfElse(
                                cond=f"{a}%2==1&&{b}%2==0",
                                then_body=[Assign(a, f"{a}-1"), Assign(c, f"{c}+{b}*{d}")],
                                else_body=[
                                    IfElse(
                                        cond=f"{a}%2==0&&{b}%2==1",
                                        then_body=[Assign(b, f"{b}-1"), Assign(c, f"{c}+{a}*{d}")],
                                        else_body=[Assign(a, f"{a}-1"), Assign(b, f"{b}-1"), Assign(c, f"{c}+({a}+{b}+1)*{d}")],
                                    )
                                ],
                            )
                        ],
                    )
                )
                used_if += 3
                used_assign += 5
                core_applied = True
            elif chosen == "odd_step_accumulator":
                # Odd-step ladder (s,t) with monotone counter.
                set_init(a, "0")
                set_init(b, "1")
                set_init(c, "1")
                guard = f"{b}<={lim}"
                body.append(Assign(a, f"{a}+1"))
                body.append(Assign(c, f"{c}+2"))
                body.append(Assign(b, f"{b}+{c}"))
                used_assign += 3
                core_applied = True
            elif chosen == "square_sync_progress":
                # y++ and x=y*y synchronization.
                body.append(Assign(b, f"{b}+1"))
                body.append(Assign(a, f"{b}*{b}"))
                used_assign += 2
                core_applied = True
            elif chosen == "multiplicative_shadow_progress":
                # Shared multiplicative progress with branch-guarded shadow product.
                set_init(c, "1")
                guard = f"{a}<={lim}"
                body.append(Assign(b, f"{b}*{a}"))
                body.append(IfOnly(cond=f"{a}<{lim}", then_body=[Assign(c, f"{c}*{a}")]))
                body.append(Assign(a, f"{a}+1"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "quadratic_form_triplet":
                # Quadratic-form accumulation triplet.
                set_init(d, f"({src}%35)+8")
                guard = f"{d}>0"
                body.append(Assign(a, f"{a}+{b}*{b}"))
                body.append(Assign(c, f"{c}+{d}*{d}"))
                body.append(Assign(b, f"{b}+{d}*{d}"))
                body.append(Assign(d, f"{d}-1"))
                used_assign += 4
                core_applied = True
            elif chosen == "euclid_coupled_accumulator":
                # Euclid-style reduction with coupled accumulator swaps.
                guard = f"{a}!={b}"
                body.append(
                    IfElse(
                        cond=f"{a}>{b}",
                        then_body=[Assign(a, f"{a}-{b}"), Assign(d, f"{d}+{c}")],
                        else_body=[Assign(b, f"{b}-{a}"), Assign(c, f"{c}+{d}")],
                    )
                )
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "fixed_point_root_refinement":
                # Newton-style integer square-root refinement.
                set_init(a, f"({src}%40)+2")
                set_init(b, "0")
                guard = f"{a}!={b}"
                body.append(Assign(b, a))
                body.append(Assign(a, f"({a}+{lim}/{a})/2"))
                used_assign += 2
                core_applied = True
            elif chosen == "residual_branch_walk":
                # Branch-controlled residual walk + synchronized step.
                set_init(c, "0")
                set_init(d, "0")
                guard = f"{c}<={lim}"
                body.append(
                    IfElse(
                        cond=f"{a}<0",
                        then_body=[Assign(a, f"{a}+2*{b}")],
                        else_body=[Assign(a, f"{a}+2*({b}-{lim})"), Assign(d, f"{d}+1")],
                    )
                )
                body.append(Assign(c, f"{c}+1"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "multi_branch_swap_recurrence":
                # Generic piecewise nonlinear recurrence with role swaps, moving thresholds,
                # and 3-4 branches over a coupled residual/drift system.
                e = state_vars[4] if len(state_vars) > 4 else a
                f = state_vars[5] if len(state_vars) > 5 else b
                g = state_vars[6] if len(state_vars) > 6 else None
                alpha = self.rng.choice([2, 3])
                step = self.rng.choice([2, 4, 6])
                inc = self.rng.choice([1, 2, 3])
                shift = self.rng.choice([0, 1, 2])
                set_init(a, f"{src}*{src}+({src}%7)")
                set_init(b, f"({src}%9)+3")
                set_init(c, f"{a}%{b}")
                set_init(d, "0")
                set_init(e, f"{a}%({b}-1)")
                set_init(f, f"({step}/2)*({a}/({b}-1)-{a}/{b})")
                if g is not None:
                    set_init(g, "0")
                guard = f"{src}+{shift}>={b}&&{c}!=0"

                last_else: List[Stmt] = [
                    Assign(d, c),
                    Assign(c, f"{alpha}*{c}-{e}+{f}-2*{b}-{step}"),
                    Assign(e, d),
                    Assign(f, f"{f}-{step}"),
                    Assign(b, f"{b}+{inc}"),
                ]
                if g is not None:
                    last_else.append(Assign(g, f"{g}+{c}%({inc}+2)"))
                branch3 = IfElse(
                    cond=f"{alpha}*{c}+{f}<2*{b}+{e}+{step}",
                    then_body=[Assign(d, c), Assign(c, f"{alpha}*{c}-{e}+{f}-{b}"), Assign(e, d), Assign(f, f"{f}-{step//2}"), Assign(b, f"{b}+{inc}")],
                    else_body=last_else,
                )
                branch2_then = [Assign(d, c), Assign(c, f"{alpha}*{c}-{e}+{f}"), Assign(e, d), Assign(b, f"{b}+{inc}")]
                if g is not None:
                    branch2_then.append(Assign(g, f"{g}+{e}%({inc}+3)"))
                nested = IfElse(
                    cond=f"{alpha}*{c}+{f}<{b}+{e}+{step//2+1}",
                    then_body=branch2_then,
                    else_body=[branch3],
                )
                first_then = [Assign(d, c), Assign(c, f"{alpha}*{c}-{e}+{f}+{b}+{inc}"), Assign(e, d), Assign(f, f"{f}+{step}"), Assign(b, f"{b}+{inc}")]
                if g is not None:
                    first_then.append(Assign(g, f"{g}+{b}%({step}+1)"))
                body.append(
                    IfElse(
                        cond=f"{alpha}*{c}+{f}<{e}+{shift}",
                        then_body=first_then,
                        else_body=[nested],
                    )
                )
                used_if += 3
                used_assign += 8 + (3 if g is not None else 0)
                core_applied = True
            elif chosen == "while_one_min_break":
                # while(1){ if(ctr>=lim) break; if(z<=y) y=z; ctr++; }
                guard = "1"
                body.append(IfOnly(cond=f"{a}>={lim}", then_body=[Break()]))
                body.append(IfOnly(cond=f"{c}<={b}", then_body=[Assign(b, c)]))
                body.append(Assign(a, f"{a}+1"))
                used_if += 2
                used_assign += 3
                core_applied = True
            elif chosen == "while_one_qr_break":
                # while(1){ if(x<=y*q+r) break; if(r==y-1){r=0;q++;} else {r++;} }
                set_init(a, f"({src}%60)+60")  # x
                set_init(b, f"({src}%9)+2")    # y
                set_init(c, "0")               # q
                set_init(d, "0")               # r
                guard = "1"
                body.append(IfOnly(cond=f"{a}<={b}*{c}+{d}", then_body=[Break()]))
                body.append(
                    IfElse(
                        cond=f"{d}=={b}-1",
                        then_body=[Assign(d, "0"), Assign(c, f"{c}+1")],
                        else_body=[Assign(d, f"{d}+1")],
                    )
                )
                used_if += 2
                used_assign += 3
                core_applied = True
            elif chosen == "while_one_mul_break":
                # while(1){ if(c>=lim) break; c++; x=x*z+src; y=y*z; }
                zvar = d
                set_init(zvar, f"({src}%6)+2")
                guard = "1"
                body.append(IfOnly(cond=f"{c}>={lim}", then_body=[Break()]))
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(a, f"{a}*{zvar}+{src}"))
                body.append(Assign(b, f"{b}*{zvar}"))
                used_if += 1
                used_assign += 4
                core_applied = True
            elif chosen == "while_one_recurrence_break":
                # while(1){ if(n>lim) break; x=x+y; y=y+z; z=z+2/4/6; n++; }
                k = self.rng.choice([2, 4, 6])
                guard = "1"
                body.append(IfOnly(cond=f"{d}>{lim}", then_body=[Break()]))
                body.append(Assign(a, f"{a}+{b}"))
                body.append(Assign(b, f"{b}+{c}"))
                body.append(Assign(c, f"{c}+{k}"))
                body.append(Assign(d, f"{d}+1"))
                used_if += 1
                used_assign += 5
                core_applied = True
            elif chosen == "nested_guarded_transitions":
                # Generic nested guarded state transitions:
                # - outer compare guard
                # - nested reset/advance branch
                # - affine accumulator drift
                # - explicit progress update
                x1, x2, x3, x4 = self.rng.sample(state_vars, k=4)
                set_init(x1, str(self.rng.randint(0, 2)))
                set_init(x2, str(self.rng.randint(0, 2)))
                set_init(x3, f"({src}%{self.rng.randint(20, 50)})+{self.rng.randint(1, 6)}")
                set_init(x4, f"({src}%{self.rng.randint(15, 40)})+{self.rng.randint(1, 6)}")
                guard = f"{ctr}<{lim}"
                step1 = self.rng.randint(1, 2)
                step2 = self.rng.randint(1, 2)
                drift = self.rng.choice([f"{x2}-{x1}", f"{x2}+{x1}", f"{x2}+{step1}"])
                body.append(
                    IfElse(
                        cond=f"{x1}>{x3}",
                        then_body=[
                            Assign(x1, f"{x1}+{step1}"),
                            Assign(x2, f"{x2}+{x1}"),
                        ],
                        else_body=[
                            IfElse(
                                cond=f"{x3}=={lim}",
                                then_body=[Assign(x3, str(self.rng.randint(1, 4)))],
                                else_body=[Assign(x3, f"{x3}+{step2}")],
                            )
                        ],
                    )
                )
                body.append(Assign(x4, f"{x4}+{drift}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 2
                used_assign += 5
                core_applied = True
            elif chosen == "piecewise_recurrence":
                # Generic piecewise nonlinear recurrence:
                # - predicate built from linear form over state
                # - branch-dependent affine/nonlinear updates
                # - monotone progress on one control variable
                pool = state_vars[:]
                if len(pool) < 5:
                    pool = (pool * 5)[:5]
                u, v, w, t, extra = self.rng.sample(pool, k=5)

                denom = self.rng.randint(3, 9)
                set_init(u, f"{src}*{src}")
                set_init(v, f"({src}%{denom})+{self.rng.randint(2, 5)}")
                set_init(w, f"{u}%{v}")
                set_init(t, f"{self.rng.randint(2, 5)}*({u}/{v}+1)")
                set_init(extra, f"{u}%({v}-1)")

                guard = f"{ctr}<{lim}&&{w}!=0"
                k1 = self.rng.randint(1, 3)
                k2 = self.rng.randint(1, 3)
                c1 = self.rng.randint(1, 3)
                c2 = self.rng.randint(1, 3)
                body.append(
                    IfElse(
                        cond=f"{k1}*{w}+{t}<{extra}",
                        then_body=[
                            Assign(w, f"{k2}*{w}-{extra}+{t}+{v}+{c1}"),
                            Assign(t, f"{t}+{self.rng.choice([2,4,6])}"),
                            Assign(extra, w),
                        ],
                        else_body=[
                            IfElse(
                                cond=f"{k1}*{w}+{t}<{v}+{extra}+{c2}",
                                then_body=[
                                    Assign(w, f"{k2}*{w}-{extra}+{t}"),
                                    Assign(v, f"{v}+{self.rng.choice([1,2])}"),
                                ],
                                else_body=[
                                    Assign(w, f"{k2}*{w}-{extra}+{t}-{v}-{c2}"),
                                    Assign(t, f"{t}-{self.rng.choice([2,4,6])}"),
                                ],
                            )
                        ],
                    )
                )
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 2
                used_assign += 6
                core_applied = True
            elif chosen == "parity_alternating":
                # Flip-flop bit flag; increments alternating counters.
                # linear/176: b=1; n=0; i=0; j=0; while(n<2k){n++;if(b==1){b=0;i++;}else{b=1;j++;}}
                # inv: |i-j| <= 1
                set_init(a, "0")   # counter n
                set_init(b, "1")   # flip-flop flag (0 or 1)
                set_init(c, "0")   # bucket 0 count
                set_init(d, "0")   # bucket 1 count
                guard = f"{a}<{lim}"
                body.append(
                    IfElse(
                        cond=f"{b}==1",
                        then_body=[Assign(b, "0"), Assign(c, f"{c}+1")],
                        else_body=[Assign(b, "1"), Assign(d, f"{d}+1")],
                    )
                )
                body.append(Assign(a, f"{a}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "russian_multiply":
                # Binary multiplication by repeated halving/doubling.
                # NLA/14: while(y!=0){if(y%2==1){z+=x;y--;} x*=2; y/=2;}
                # inv: z + x*y == a_init * b_init
                set_init(a, f"({src}%28)+8")   # x
                set_init(b, f"({src}%22)+5")   # y
                set_init(c, "0")               # z (accumulates result)
                guard = f"{b}!=0"
                body.append(IfOnly(cond=f"{b}%2==1", then_body=[Assign(c, f"{c}+{a}"), Assign(b, f"{b}-1")]))
                body.append(Assign(a, f"2*{a}"))
                body.append(Assign(b, f"{b}/2"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "cauchy_schwarz_triple":
                # Three accumulators: z=Σx², w=Σy², p=Σxy; countdown n.
                # NLA/29,30: while(n>0){z+=x*x; w+=y*y; p+=x*y; n--;} inv: z*w>=p*p
                xp = params[0] if params else src
                yp = params[1] if len(params) > 1 else src
                set_init(a, "0")                   # z = Σ x²
                set_init(b, "0")                   # w = Σ y²
                set_init(c, "0")                   # p = Σ x*y
                set_init(d, f"({src}%18)+5")       # n countdown
                guard = f"{d}>0"
                body.append(Assign(a, f"{a}+{xp}*{xp}"))
                body.append(Assign(b, f"{b}+{yp}*{yp}"))
                body.append(Assign(c, f"{c}+{xp}*{yp}"))
                body.append(Assign(d, f"{d}-1"))
                used_assign += 4
                core_applied = True
            elif chosen == "int_sqrt_sieve":
                # Integer square root by successive subtraction.
                # NLA/36,43,44: r=0; x=A/2; while(x>r){x-=r; r++;} inv: A==2*x+r²-r
                xp = params[0] if params else src
                set_init(a, "0")                   # r
                set_init(b, f"({xp}%28)+10")       # x (initial approximation)
                guard = f"{b}>{a}"
                body.append(Assign(b, f"{b}-{a}"))
                body.append(Assign(a, f"{a}+1"))
                used_assign += 2
                core_applied = True
            elif chosen == "countdown_triple":
                # Three-way linear countdown with conservation.
                # linear/145: lo=0; hi=2*mid; while(mid>0){lo++;hi--;mid--;} inv: lo+hi==2*mid_init
                mid_init = self._core_const(4, 35)
                set_init(a, self._diverse_init(0, role="acc"))  # lo
                set_init(b, str(2 * mid_init))     # hi = 2*mid_init
                set_init(c, str(mid_init))         # mid (countdown)
                guard = f"{c}>0"
                mode = self.rng.choice(["base", "asymmetric", "conditional"])
                if mode == "base":
                    body.append(Assign(a, f"{a}+1"))
                    body.append(Assign(b, f"{b}-1"))
                    body.append(Assign(c, f"{c}-1"))
                    used_assign += 3
                elif mode == "asymmetric":
                    s = self._core_const(1, 4)
                    body.append(Assign(a, f"{a}+{s}"))
                    body.append(Assign(b, f"{b}-{s}"))
                    body.append(Assign(c, f"{c}-1"))
                    used_assign += 3
                else:
                    body.append(
                        IfElse(
                            cond=f"{a}<{c}",
                            then_body=[Assign(a, f"{a}+1"), Assign(c, f"{c}-1")],
                            else_body=[Assign(b, f"{b}-1"), Assign(c, f"{c}-1")],
                        )
                    )
                    used_if += 1
                    used_assign += 2
                core_applied = True
            elif chosen == "binary_toggle":
                # Two-state toggling system.
                set_init(a, "1" if self.rng.random() < 0.5 else "2")
                body.append(
                    IfElse(
                        cond=f"{a}==1",
                        then_body=[Assign(a, "2")],
                        else_body=[IfOnly(cond=f"{a}==2", then_body=[Assign(a, "1")])],
                    )
                )
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "gap_drift_piecewise":
                # Piecewise drift driven by inter-variable gap.
                k = self.rng.randint(1, 4)
                body.append(
                    IfElse(
                        cond=f"{a}-{b}<{k}",
                        then_body=[Assign(a, f"{a}-1"), Assign(b, f"{b}+2")],
                        else_body=[Assign(b, f"{b}+1")],
                    )
                )
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "alternating_series_accumulator":
                # Series-like term recurrence with parity-controlled sign.
                srcv = params[0] if params else src
                set_init(a, "1")  # term
                set_init(b, "1")  # sum
                set_init(c, "1")  # count
                set_init(d, "1")  # sign
                guard = f"{c}<={lim}"
                body.append(Assign(a, f"{a}*({srcv}/{c})"))
                body.append(
                    IfElse(
                        cond=f"({c}/2)%2==0",
                        then_body=[Assign(d, "1")],
                        else_body=[Assign(d, "-1")],
                    )
                )
                body.append(Assign(b, f"{b}+{d}*{a}"))
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(a, f"{a}*({srcv}/{c})"))
                used_if += 1
                used_assign += 5
                core_applied = True
            elif chosen == "turn_based_state_machine":
                # Turn variable orchestrates a small multi-phase state machine.
                set_init(a, "0")  # turn
                set_init(b, "1")  # i
                set_init(c, "0")  # j
                guard = f"{a}>=0&&{a}<3"
                body.append(
                    IfElse(
                        cond=f"{a}==0&&{b}>={lim}",
                        then_body=[Assign(a, "3")],
                        else_body=[
                            IfElse(
                                cond=f"{a}==1&&{c}<{b}",
                                then_body=[Assign(d, f"{d}+{b}-{c}"), Assign(c, f"{c}+1")],
                                else_body=[
                                    IfElse(
                                        cond=f"{a}==1&&{c}>={b}",
                                        then_body=[Assign(a, "2")],
                                        else_body=[IfOnly(cond=f"{a}==2", then_body=[Assign(b, f"{b}+1"), Assign(a, "0")])],
                                    )
                                ],
                            )
                        ],
                    )
                )
                used_if += 3
                used_assign += 5
                core_applied = True
            elif chosen == "equal_pair_piecewise_increment":
                # Keep two accumulators synchronized under piecewise increments.
                body.append(
                    IfElse(
                        cond=f"{c}=={lim}+1",
                        then_body=[Assign(a, f"{a}+3"), Assign(b, f"{b}+3")],
                        else_body=[Assign(a, f"{a}+2"), Assign(b, f"{b}+2")],
                    )
                )
                body.append(IfOnly(cond=f"{c}=={lim}", then_body=[Assign(a, f"{a}+1"), Assign(c, f"{c}+1")]))
                used_if += 2
                used_assign += 5
                core_applied = True
            # ── New templates from the semantic plan (L14, L15, L17, L18, L20, X5, X12) ──
            elif chosen == "cache_coherence":
                # L14: 2-state resource conservation: free + owned == n_init.
                # inv: free + owned == n_init  (linear conservation).
                n_init = self._scale_init(self.rng.randint(5, 15))
                set_init(a, str(n_init))   # free
                set_init(b, "0")           # owned
                guard = f"{ctr}<{lim}"
                body.append(
                    IfElse(
                        cond=f"{ctr}%2==0",
                        then_body=[IfOnly(cond=f"{a}>0", then_body=[Assign(a, f"{a}-1"), Assign(b, f"{b}+1")])],
                        else_body=[IfOnly(cond=f"{b}>0", then_body=[Assign(b, f"{b}-1"), Assign(a, f"{a}+1")])],
                    )
                )
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 2
                used_assign += 3
                core_applied = True
            elif chosen == "multi_countdown_parallel":
                # L15: Two counters decremented by deterministic alternation (ctr%2 schedule).
                # At least one reaches 0 when the loop terminates.
                set_init(a, f"({src}%20)+10")  # x1
                set_init(b, f"({src}%15)+8")   # x2
                guard = f"{a}>0&&{b}>0"
                body.append(
                    IfElse(
                        cond=f"{ctr}%2==0",
                        then_body=[Assign(a, f"{a}-1")],
                        else_body=[Assign(b, f"{b}-1")],
                    )
                )
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "geometric_doubling_bound":
                # L17: z doubles each step; linear lower bound z > n is verifiable.
                # inv (Frama-C safe): z >= n + 1  (NOT z == 2^n which is non-linear).
                set_init(a, "1")   # z (starts at 1)
                set_init(b, "0")   # n (step counter)
                guard = f"{a}<{lim}"
                body.append(Assign(a, f"2*{a}"))
                body.append(Assign(b, f"{b}+1"))
                used_assign += 2
                core_applied = True
            elif chosen == "sawtooth_modular_counter":
                # L18: c = (c + 1) % PERIOD — sawtooth that wraps.
                # inv: 0 <= c < PERIOD.
                period = self.rng.randint(3, 8)
                set_init(a, "0")   # c (modular counter)
                set_init(b, "0")   # outer iteration counter
                guard = f"{b}<{lim}"
                body.append(Assign(a, f"({a}+1)%{period}"))
                body.append(Assign(b, f"{b}+1"))
                used_assign += 2
                core_applied = True
            elif chosen == "decaying_stride":
                # L20: i++; j += k; k-- — stride k decreases each step.
                # inv: i + k <= k0 + 2 (i grew by steps, k shrank by same count).
                k0 = self.rng.randint(3, 8)
                set_init(a, "0")       # i (iteration counter)
                set_init(b, "0")       # j (accumulator)
                set_init(c, str(k0))   # k (decaying stride)
                guard = f"{a}<{lim}&&{c}>0"
                body.append(Assign(a, f"{a}+1"))
                body.append(Assign(b, f"{b}+{c}"))
                body.append(Assign(c, f"{c}-1"))
                used_assign += 3
                core_applied = True
            elif chosen == "bouncing_counter":
                # X5: x bounces between lo and hi — direction reverses at edges.
                # inv: lo_val <= x <= hi_val throughout.
                lo_val = self.rng.randint(0, 3)
                hi_val = lo_val + self.rng.randint(4, 10)
                set_init(a, str(lo_val))   # x (position)
                set_init(b, "1")           # d (direction: +1 or -1)
                guard = f"{ctr}<{lim}"
                body.append(IfOnly(cond=f"{a}>={hi_val}", then_body=[Assign(b, "-1")]))
                body.append(IfOnly(cond=f"{a}<={lo_val}", then_body=[Assign(b, "1")]))
                body.append(Assign(a, f"{a}+{b}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 2
                used_assign += 4
                core_applied = True
            elif chosen == "modular_equality_race":
                # X12: a and b both advance by m each step — same residue class maintained.
                # inv: a % m == b % m (both start in same residue and step by m).
                m_val = self.rng.randint(2, 7)
                r_val = self.rng.randint(0, m_val - 1)
                set_init(a, str(r_val))               # a starts at residue r
                set_init(b, str(r_val + m_val))        # b starts at r + m (same residue)
                guard = f"{ctr}<{lim}"
                body.append(Assign(a, f"{a}+{m_val}"))
                body.append(Assign(b, f"{b}+{m_val}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_assign += 3
                core_applied = True
            elif chosen == "transfer_conservation":
                # linear/100: x=N; y=0; while(x>0){y+=S; x-=S;}
                # inv: x + y == N  (additive conservation, incremental form)
                N_val = self._core_const(3, 50)
                S_val = self._core_const(1, 6)
                set_init(a, str(N_val))                     # x (countdown)
                set_init(b, self._diverse_init(0, role="acc"))  # y (accumulator)
                guard = f"{a}>0"
                mode = self.rng.choice(["base", "modular", "guarded"])
                if mode == "base":
                    body.append(Assign(b, f"{b}+{S_val}"))
                    body.append(Assign(a, f"{a}-{S_val}"))
                    used_assign += 2
                elif mode == "modular":
                    K_val = self._core_const(2, 9)
                    set_init(c, "0")  # amt
                    body.append(Assign(c, f"{a}%{K_val}"))
                    body.append(
                        IfElse(
                            cond=f"{c}==0",
                            then_body=[Assign(c, "1")],
                            else_body=[],
                        )
                    )
                    body.append(
                        IfElse(
                            cond=f"{c}>{a}",
                            then_body=[Assign(c, a)],
                            else_body=[],
                        )
                    )
                    body.append(Assign(b, f"{b}+{c}"))
                    body.append(Assign(a, f"{a}-{c}"))
                    used_if += 2
                    used_assign += 5
                else:
                    body.append(
                        IfElse(
                            cond=f"{a}>={S_val}",
                            then_body=[Assign(b, f"{b}+{S_val}"), Assign(a, f"{a}-{S_val}")],
                            else_body=[Assign(b, f"{b}+{a}"), Assign(a, "0")],
                        )
                    )
                    used_if += 1
                    used_assign += 2
                core_applied = True
            elif chosen == "carry_pair_counter":
                # Radix-B two-digit counter.
                # inv: t == q*B + r, 0 <= r < B
                base = self._core_const(2, 12)
                set_init(a, self._diverse_init(0, role="acc"))   # q: high digit
                set_init(b, self._diverse_init(0, role="acc"))   # r: low digit
                set_init(c, self._diverse_init(0, role="ctr"))   # t: total count
                guard = f"{ctr}<{lim}"
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(b, f"{b}+1"))
                body.append(
                    IfOnly(
                        cond=f"{b}>={base}",
                        then_body=[Assign(b, f"{b}-{base}"), Assign(a, f"{a}+1")],
                    )
                )
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 6
                core_applied = True
            elif chosen == "ramped_transfer_conservation":
                # Transfer from src to dst with a growing step cap.
                # inv: src + dst == src_init, src >= 0, step grows monotonically.
                src_init = self._core_const(8, 45)
                set_init(a, str(src_init))   # src
                set_init(b, "0")             # dst
                set_init(c, "1")             # step cap
                set_init(d, "0")             # pay this round
                guard = f"{a}>0&&{ctr}<{lim}"
                mode = self.rng.choice(["tmp_min", "direct_split", "biased_ramp"])
                if mode == "tmp_min":
                    body.append(
                        IfElse(
                            cond=f"{a}<={c}",
                            then_body=[Assign(d, a)],
                            else_body=[Assign(d, c)],
                        )
                    )
                    body.append(Assign(a, f"{a}-{d}"))
                    body.append(Assign(b, f"{b}+{d}"))
                    body.append(Assign(c, f"{c}+1"))
                    body.append(Assign(ctr, f"{ctr}+1"))
                    used_if += 1
                    used_assign += 6
                elif mode == "direct_split":
                    body.append(Assign(d, c))
                    body.append(
                        IfElse(
                            cond=f"{a}>={c}",
                            then_body=[Assign(a, f"{a}-{c}"), Assign(b, f"{b}+{c}")],
                            else_body=[Assign(b, f"{b}+{a}"), Assign(a, "0")],
                        )
                    )
                    body.append(Assign(c, f"{c}+1"))
                    body.append(Assign(ctr, f"{ctr}+1"))
                    used_if += 1
                    used_assign += 5
                else:
                    body.append(
                        IfElse(
                            cond=f"{a}<{c}",
                            then_body=[Assign(d, a)],
                            else_body=[Assign(d, c)],
                        )
                    )
                    body.append(Assign(b, f"{b}+{d}"))
                    body.append(Assign(a, f"{a}-{d}"))
                    body.append(
                        IfElse(
                            cond=f"{ctr}%2==0",
                            then_body=[Assign(c, f"{c}+2")],
                            else_body=[Assign(c, f"{c}+1")],
                        )
                    )
                    body.append(Assign(ctr, f"{ctr}+1"))
                    used_if += 2
                    used_assign += 5
                core_applied = True
            elif chosen == "alternating_swap_transfer":
                # Alternating two-way transfer controlled by a binary flag.
                # inv: a + b == const, flag in {0,1}
                delta = self.rng.randint(1, 3)
                set_init(a, str(self.rng.randint(8, 20)))
                set_init(b, str(self.rng.randint(8, 20)))
                set_init(c, "0")   # flag
                guard = f"{ctr}<{lim}"
                body.append(
                    IfElse(
                        cond=f"{c}==0",
                        then_body=[Assign(a, f"{a}+{delta}"), Assign(b, f"{b}-{delta}"), Assign(c, "1")],
                        else_body=[Assign(a, f"{a}-{delta}"), Assign(b, f"{b}+{delta}"), Assign(c, "0")],
                    )
                )
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 7
                core_applied = True
            elif chosen == "scheduled_queue_occupancy":
                # Periodic queue push/pop schedule with hard capacity.
                # inv: 0 <= q <= cap, q == push - pop
                e = state_vars[4]
                cap = self.rng.randint(3, 8)
                q0 = self.rng.randint(0, cap)
                set_init(a, str(q0))   # q
                set_init(b, str(q0))   # push
                set_init(c, "0")       # pop
                set_init(d, str(cap))  # cap
                set_init(e, "0")       # epoch marker
                guard = f"{ctr}<{lim}"
                body.append(
                    IfElse(
                        cond=f"{ctr}%3==0",
                        then_body=[IfOnly(cond=f"{a}>0", then_body=[Assign(a, f"{a}-1"), Assign(c, f"{c}+1")])],
                        else_body=[IfOnly(cond=f"{a}<{d}", then_body=[Assign(a, f"{a}+1"), Assign(b, f"{b}+1")])],
                    )
                )
                body.append(Assign(e, f"{e}+1"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 3
                used_assign += 6
                core_applied = True
            elif chosen == "nested_triangular_accumulate":
                # Outer progress + nested inner accumulation.
                # Modes:
                # - unit_ramp: sum += 1..bound
                # - weighted_ramp: sum += (j + outer parity)
                # - quadratic_ramp: sum += (2*j + 1)
                # - outer_weighted: bound and increment depend on outer counter
                mode = self.rng.choice(["unit_ramp", "weighted_ramp", "quadratic_ramp", "outer_weighted"])
                append_step = False
                guard = f"{ctr}<{lim}"
                set_init(ctr, "0")
                set_init(a, "0")
                set_init(c, "0")
                alpha = self.rng.randint(1, 3)
                body.append(Assign(d, f"({ctr}%4)+1"))
                body.append(Assign(b, "0"))
                if mode == "unit_ramp":
                    inner_body = [Assign(a, f"{a}+{b}+1"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<{d}"
                elif mode == "weighted_ramp":
                    inner_body = [Assign(a, f"{a}+{b}+({ctr}%2)"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<{d}"
                elif mode == "quadratic_ramp":
                    inner_body = [Assign(a, f"{a}+2*{b}+1"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<{d}"
                else:
                    body[-1] = Assign(d, f"({ctr}%3)+{alpha}")
                    inner_body = [Assign(a, f"{a}+{alpha}*{ctr}+{b}"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<({ctr}+{alpha})"
                body.append(WhileLoop(cond=inner_cond, body=inner_body))
                body.append(Assign(c, f"{c}+{ctr}+1"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_assign += 4
                core_applied = True
            elif chosen == "nested_triangular_balance":
                # Nested loop with dual accumulators and inner reset.
                # Modes:
                # - add_sub
                # - dual_add
                # - paired_shift
                # - budget_shave
                mode = self.rng.choice(["add_sub", "dual_add", "paired_shift", "budget_shave"])
                append_step = False
                guard = f"{ctr}<{lim}"
                set_init(ctr, "0")
                set_init(a, "0")
                set_init(c, f"({src}%9)+6")
                body.append(Assign(d, f"({ctr}%3)+2"))
                body.append(Assign(b, "0"))
                if mode == "add_sub":
                    inner_body = [Assign(a, f"{a}+1"), Assign(c, f"{c}-{b}"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<{d}"
                elif mode == "dual_add":
                    inner_body = [Assign(a, f"{a}+{b}+1"), Assign(c, f"{c}+1"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<{d}"
                elif mode == "paired_shift":
                    inner_body = [Assign(a, f"{a}+{b}"), Assign(c, f"{c}-1"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<{d}"
                else:
                    step = self.rng.randint(1, 2)
                    set_init(c, f"({lim})*({lim})+({src}%5)")
                    inner_body = [Assign(c, f"{c}-{step}"), Assign(a, f"{a}+{ctr}+1"), Assign(b, f"{b}+1")]
                    inner_cond = f"{b}<({ctr}%4+2)"
                    body.append(Assign(c, f"{c}+({ctr}%2)"))
                body.append(WhileLoop(cond=inner_cond, body=inner_body))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_assign += 4
                core_applied = True
            elif chosen == "nested_grid_rowcol_sum":
                # 2D traversal style nested loop.
                # Modes: row_plus_col / row_scaled / col_biased
                mode = self.rng.choice(["row_plus_col", "row_scaled", "col_biased"])
                append_step = False
                guard = f"{ctr}<{lim}"
                set_init(ctr, "0")
                set_init(a, "0")
                body.append(Assign(d, f"({e}%3)+2"))
                body.append(Assign(b, "0"))
                if mode == "row_plus_col":
                    inner_body = [Assign(a, f"{a}+{ctr}+{b}"), Assign(b, f"{b}+1")]
                elif mode == "row_scaled":
                    inner_body = [Assign(a, f"{a}+2*{ctr}+{b}"), Assign(b, f"{b}+1")]
                else:
                    inner_body = [Assign(a, f"{a}+{ctr}+2*{b}"), Assign(b, f"{b}+1")]
                body.append(WhileLoop(cond=f"{b}<{d}", body=inner_body))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_assign += 3
                core_applied = True
            elif chosen == "nested_grid_checkerboard":
                # Nested traversal with parity branch.
                # Modes: toggle_pm1 / toggle_pm2 / toggle_pm3
                mode = self.rng.choice(["toggle_pm1", "toggle_pm2", "toggle_pm3"])
                append_step = False
                guard = f"{ctr}<{lim}"
                set_init(ctr, "0")
                set_init(a, "0")
                body.append(Assign(d, f"({c}%4)+2"))
                body.append(Assign(b, "0"))
                delta = "1" if mode == "toggle_pm1" else ("2" if mode == "toggle_pm2" else "3")
                inner_body = [
                    IfElse(
                        cond=f"({ctr}+{b})%2==0",
                        then_body=[Assign(a, f"{a}+{delta}")],
                        else_body=[Assign(a, f"{a}-{delta}")],
                    ),
                    Assign(b, f"{b}+1"),
                ]
                body.append(WhileLoop(cond=f"{b}<{d}", body=inner_body))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "nested_block_drain":
                # Outer block budget + inner drain.
                # Modes: unit_drain / fast_drain / gentle_drain / budget_trace
                mode = self.rng.choice(["unit_drain", "fast_drain", "gentle_drain", "budget_trace"])
                append_step = False
                guard = f"{ctr}<{lim}"
                set_init(ctr, "0")
                set_init(a, f"({src}%20)+10")
                set_init(c, "0")
                if mode == "budget_trace":
                    set_init(c, f"{lim}*{lim}+({src}%7)")
                    body.append(Assign(d, f"({ctr}%4)+1"))
                    body.append(
                        WhileLoop(
                            cond=f"{d}>0&&{c}>0&&{a}>0",
                            body=[Assign(a, f"{a}-1"), Assign(c, f"{c}-1"), Assign(d, f"{d}-1")],
                        )
                    )
                    used_assign += 5
                else:
                    body.append(Assign(d, f"({ctr}%3)+2"))
                    inner_step = "1" if mode in {"unit_drain", "gentle_drain"} else "2"
                    body.append(
                        WhileLoop(
                            cond=f"{d}>0&&{a}>0",
                            body=[Assign(a, f"{a}-{inner_step}"), Assign(d, f"{d}-1")],
                        )
                    )
                if mode == "gentle_drain":
                    body.append(Assign(a, f"{a}+({ctr}%2)"))
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(ctr, f"{ctr}+1"))
                if mode != "budget_trace":
                    used_assign += 5 if mode == "gentle_drain" else 4
                core_applied = True
            elif chosen == "nested_block_staircase":
                # Inner workload grows with outer index.
                # Modes: stair_add1 / stair_add2 / stair_mix
                mode = self.rng.choice(["stair_add1", "stair_add2", "stair_mix"])
                append_step = False
                guard = f"{ctr}<{lim}"
                set_init(ctr, "0")
                set_init(a, "0")
                set_init(c, "0")
                body.append(Assign(d, f"{ctr}+1"))
                body.append(Assign(b, "0"))
                if mode == "stair_mix":
                    inner = [Assign(a, f"{a}+{b}+1"), Assign(b, f"{b}+1")]
                else:
                    inc = "1" if mode == "stair_add1" else "2"
                    inner = [Assign(a, f"{a}+{inc}"), Assign(b, f"{b}+1")]
                body.append(WhileLoop(cond=f"{b}<{d}", body=inner))
                body.append(Assign(c, f"{c}+{d}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_assign += 5
                core_applied = True
            elif chosen == "x1_geometric_growth_bound":
                # Geometric growth against a linear bound.
                # inv: a >= 1 and a strictly increases; when loop exits a > lim.
                set_init(a, "1")
                set_init(b, "0")
                guard = f"{a}<={lim}"
                body.append(Assign(a, f"2*{a}"))
                body.append(Assign(b, f"{b}+1"))
                used_assign += 2
                core_applied = True
            elif chosen == "x17_harmonic_step_reduction":
                # Denominator-ladder style reduction with bounded decrement.
                # inv: debt >= 0, step increases monotonically.
                debt_init = self.rng.randint(10, 40)
                set_init(a, str(debt_init))  # debt
                set_init(b, "1")             # step
                set_init(c, "0")             # rounds
                guard = f"{a}>0&&{b}<={lim}"
                body.append(
                    IfElse(
                        cond=f"{a}>{b}",
                        then_body=[Assign(a, f"{a}-{b}")],
                        else_body=[Assign(a, "0")],
                    )
                )
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(b, f"{b}+1"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 5
                core_applied = True
            elif chosen == "x19_rolling_sum_window":
                # Rolling sum with add/remove update once the window is full.
                # inv: win_sum tracks last W inserted pseudo-items.
                W = self.rng.randint(3, 7)
                set_init(a, "0")       # win_sum
                set_init(b, "0")       # incoming
                set_init(c, "0")       # outgoing
                set_init(d, str(W))    # window length
                guard = f"{ctr}<{lim}"
                body.append(Assign(b, f"{ctr}%5"))
                body.append(
                    IfElse(
                        cond=f"{ctr}>={d}",
                        then_body=[
                            Assign(c, f"({ctr}-{d})%5"),
                            Assign(a, f"{a}+{b}-{c}"),
                        ],
                        else_body=[Assign(a, f"{a}+{b}")],
                    )
                )
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 5
                core_applied = True
            elif chosen == "random_walk_bounded":
                # linear/158: j=1; a=0; while(j<=m){if(even) a++; else a--; j++;}
                # inv: -j <= a <= j  (|a| bounded by step counter)
                set_init(a, "0")   # a (random walker)
                set_init(b, "1")   # j (step counter)
                guard = f"{b}<={lim}"
                body.append(
                    IfElse(
                        cond=f"{ctr}%2==0",
                        then_body=[Assign(a, f"{a}+1")],
                        else_body=[Assign(a, f"{a}-1")],
                    )
                )
                body.append(Assign(b, f"{b}+1"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "ghost_sync_pair":
                # linear/220: w=x=init; always update both together.
                # inv: w == x  (ghost-variable synchrony)
                init_val = self._core_const(1, 15)
                set_init(a, str(init_val))   # w
                set_init(b, str(init_val))   # x (ghost, must equal w)
                guard = f"{ctr}<{lim}"
                mode = self.rng.choice(["parallel_stride", "conditional_sync", "lag_copy"])
                if mode == "parallel_stride":
                    step_up = self._core_const(1, 5)
                    body.append(Assign(a, f"{a}+{step_up}"))
                    body.append(Assign(b, f"{b}+{step_up}"))
                    body.append(Assign(ctr, f"{ctr}+1"))
                    used_assign += 3
                elif mode == "conditional_sync":
                    body.append(IfOnly(cond=f"{ctr}%3==0", then_body=[Assign(a, b)]))
                    body.append(Assign(b, f"{b}+1"))
                    body.append(Assign(ctr, f"{ctr}+1"))
                    used_if += 1
                    used_assign += 3
                else:
                    body.append(Assign(a, b))
                    body.append(Assign(b, f"{b}+1"))
                    body.append(Assign(ctr, f"{ctr}+1"))
                    used_assign += 3
                core_applied = True
            elif chosen == "product_reduction_walk":
                # NLA/24,27: z = x*y; while(x>0){x--; z -= y;}
                # inv: z == x * y  (product decremented in sync with x)
                x_init = self.rng.randint(2, 8)
                y_val = self.rng.randint(2, 6)
                set_init(a, str(x_init))              # x
                set_init(b, str(y_val))               # y (fixed step)
                set_init(c, str(x_init * y_val))      # z = x * y
                guard = f"{a}>0"
                body.append(Assign(a, f"{a}-1"))
                body.append(Assign(c, f"{c}-{b}"))
                body.append(Assign(b, b))              # protect y: mark as core_var so extension won't touch it
                used_assign += 3
                core_applied = True
            elif chosen == "partial_product_conservation":
                # NLA/34,35: x=A; y=B; u=B; v=0; while(x>y){x-=y; v+=u;}
                # inv: x*u + y*v == A*B  (partial-product conservation)
                B_val = self.rng.randint(2, 6)
                A_val = B_val + self.rng.randint(1, 8)   # A > B so loop runs at least once
                set_init(a, str(A_val))   # x
                set_init(b, str(B_val))   # y
                set_init(c, str(B_val))   # u = B (constant in this simplified form)
                set_init(d, "0")           # v
                guard = f"{a}>{b}"
                body.append(Assign(a, f"{a}-{b}"))   # x -= y
                body.append(Assign(d, f"{d}+{c}"))   # v += u
                # Protect b (y) and c (u): mark as core_vars so extension won't corrupt x*u+y*v==A*B
                body.append(Assign(b, b))
                body.append(Assign(c, c))
                used_assign += 4
                core_applied = True
            elif chosen == "cumulative_double_sum":
                # NLA/28: z=0; p=0; w=0; while(w<lim){z+=x; p+=z; w++;}
                # inv: 2*p == x * w * (w+1)  (triangular-product invariant)
                x_val = self.rng.randint(1, 5)
                set_init(a, str(x_val))   # x (constant addend)
                set_init(b, "0")           # z (running partial sum)
                set_init(c, "0")           # p (cumulative sum of z)
                set_init(d, "0")           # w (step counter)
                guard = f"{d}<{lim}"
                body.append(Assign(b, f"{b}+{a}"))   # z += x
                body.append(Assign(c, f"{c}+{b}"))   # p += z
                body.append(Assign(d, f"{d}+1"))     # w++
                body.append(Assign(a, a))             # protect x: mark as core_var so extension won't change it
                used_assign += 4
                core_applied = True
            elif chosen == "power_sum_series":
                # NLA/15-16: c=0; y=0; x=0; while(c<k){c++; y++; x += y*y;}
                # inv (NLA/16): 6*x == 2*c^3 + 3*c^2 + c  (sum of squares closed form)
                set_init(a, "0")    # x (accumulator)
                set_init(b, "0")    # y (current index value)
                set_init(c, "0")    # c (loop counter, matches loop limit)
                guard = f"{c}<{lim}"
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(b, f"{b}+1"))
                body.append(Assign(a, f"{a}+{b}*{b}"))   # x += y*y
                used_assign += 3
                core_applied = True
            elif chosen == "newton_sqrt_convergence":
                # NLA/37,38: guess=N/2; prev=0; while(guess!=prev){prev=guess; guess=(guess+N/guess)/2;}
                # inv: guess*guess <= N  (convergent integer sqrt, from above)
                # Use lim as N; guard against guess==0 to avoid division by zero.
                set_init(a, f"({lim}/2)+1")   # guess (starts above sqrt(N))
                set_init(b, "0")               # prev
                guard = f"{a}!={b}&&{a}>0"
                body.append(Assign(b, a))                           # prev = guess
                body.append(Assign(a, f"({a}+{lim}/{a})/2"))       # guess = (guess + N/guess) / 2
                used_assign += 2
                core_applied = True
            elif chosen == "bresenham_line_step":
                # NLA/41: v=2*Y-X; while(x<=X){if(v<0){v+=2*Y}else{v+=2*(Y-X); y++;} x++;}
                # inv: 2*Y*x - 2*x*y + 2*y == X + v  (Bresenham decision-variable invariant)
                X_val = self.rng.randint(8, 20)
                Y_val = self.rng.randint(3, X_val)   # 0 < Y <= X
                set_init(a, str(2 * Y_val - X_val))   # v (decision variable)
                set_init(b, "0")                       # x (column)
                set_init(c, "0")                       # y (row)
                guard = f"{b}<={X_val}"
                body.append(
                    IfElse(
                        cond=f"{a}<0",
                        then_body=[Assign(a, f"{a}+{2 * Y_val}")],
                        else_body=[Assign(a, f"{a}+{2 * (Y_val - X_val)}"), Assign(c, f"{c}+1")],
                    )
                )
                body.append(Assign(b, f"{b}+1"))
                used_if += 1
                used_assign += 4
                core_applied = True
            elif chosen == "nondeterministic_multi_decrement":
                # linear/200: while(x1>0&&x2>0&&x3>0){if(?){x1--} if(?){x2--} if(?){x3--}}
                # At loop exit: at least one of x1,x2,x3 reaches 0.
                # Simulated with ctr%3 schedule (deterministic proxy for independent guards).
                x1_init = self.rng.randint(5, 15)
                x2_init = self.rng.randint(5, 15)
                x3_init = self.rng.randint(5, 15)
                set_init(a, str(x1_init))   # x1
                set_init(b, str(x2_init))   # x2
                set_init(c, str(x3_init))   # x3
                guard = f"{a}>0&&{b}>0&&{c}>0"
                body.append(IfOnly(cond=f"{ctr}%3==0", then_body=[Assign(a, f"{a}-1")]))
                body.append(IfOnly(cond=f"{ctr}%3==1", then_body=[Assign(b, f"{b}-1")]))
                body.append(IfOnly(cond=f"{ctr}%3==2", then_body=[Assign(c, f"{c}-1")]))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 3
                used_assign += 4
                core_applied = True
            # ── Trivial fallback templates: always qualify ─────────────────────────────
            elif chosen == "L1_trivial":
                # Guaranteed backstop: simple affine accumulator with bounded counter.
                step = self.rng.randint(1, 3)
                guard = f"{ctr}<{lim}"
                body.append(Assign(a, f"{a}+{step}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_assign += 2
                core_applied = True
            elif chosen == "L2_trivial":
                # Guaranteed backstop: simple countdown.
                set_init(a, f"({src}%20)+5")
                guard = f"{a}>0"
                body.append(Assign(a, f"{a}-1"))
                used_assign += 1
                core_applied = True

        # core_vars: variables whose values are governed by the template's invariant.
        # Extra DSL additions are restricted to free_vars = state_vars - core_vars
        # so they cannot corrupt the invariant the template established.
        core_vars: List[str] = []
        if core_applied:
            append_step = False
            core_vars = [v for v in _get_written_vars(body) if v in state_vars]

        # Free vars for extension/padding:
        # include non-core state vars and input params so both local/input variables
        # can participate in loop updates.
        #
        # Guardrail: do not let extension phase rewrite guard-driving variables
        # (including explicit break-guards in while(1) cores). Core semantics
        # should own those variables to keep termination behavior stable.
        guard_protected: Set[str] = set(self._guard_vars(guard))
        for st in body:
            if isinstance(st, IfOnly) and len(st.then_body) == 1 and isinstance(st.then_body[0], Break):
                g = st.cond.strip()
                m = re.match(r"^\s*!\((.*)\)\s*$", g)
                if m:
                    g = m.group(1).strip()
                for t in self._guard_vars(g):
                    guard_protected.add(t)

        writable_pool = list(dict.fromkeys(state_vars + list(params)))
        _free = [
            v for v in writable_pool
            if v not in core_vars and v not in {ctr, lim} and v not in guard_protected
        ]
        if not _free:
            _free = [v for v in state_vars if v not in core_vars and v not in guard_protected] or [
                v for v in state_vars if v not in guard_protected
            ] or state_vars

        assign_budget = max(0, assign_total - (1 if append_step else 0))

        # Guarantee extension slots: when free vars exist, ensure assign_budget
        # covers at least used_assign + len(_free) so every free var has a chance
        # to receive a loop-body update.  Hard-capped at assign_fuel to avoid bloat.
        if core_applied and _free:
            assign_budget = min(
                max(assign_budget, used_assign + len(_free)),
                self.hp.assign_fuel,
            )

        # ── Minimum if/else floor enforcement ───────────────────────────────────
        # Inject guaranteed if-blocks when the core has used fewer ifs than min_ifelse.
        # These are appended before the extension phase so free_vars are already known.
        # Each injected if costs 1 assign slot; we bump assign_budget to accommodate.
        if self.hp.min_ifelse > 0 and used_if < self.hp.min_ifelse and _free:
            need_extra_if = self.hp.min_ifelse - used_if
            for _ in range(need_extra_if):
                t = self.rng.choice(_free)
                p = self.rng.choice([w for w in _free if w != t] or [t])
                cond = self._sample_cond(ctr, lim, t, vars_pool, nla_family)
                body.append(IfOnly(cond=cond, then_body=[self._semantic_assign(t, p, ctr, lim, vars_pool, nla_family)]))
                used_if += 1
                used_assign += 1
                assign_budget += 1   # expand budget so the rest of extension still runs

        if core_applied and used_assign < assign_budget:
            # Template-aware three-way behavior on extra vars:
            # none / simple / native-expansion.
            used_assign += self._inject_multivar_extension(
                body=body,
                core_name=chosen,
                free_vars=_free,
                driver_vars=core_vars or state_vars,
                ctr=ctr,
                lim=lim,
                nla_family=nla_family,
                assign_budget_left=assign_budget - used_assign,
            )
        if used_assign < assign_budget:
            used_assign += self._seed_family_kernel(body, _free, ctr, assign_budget - used_assign, nla_family)

        while used_assign < assign_budget:
            rem_assign = assign_budget - used_assign
            can_if = used_if < if_budget and rem_assign >= 1
            can_ifelse = used_if < if_budget and rem_assign >= 2
            # Force an if when below the minimum if/else floor; otherwise 40% random.
            must_if = can_if and used_if < self.hp.min_ifelse
            choose_if = must_if or (can_if and self.rng.random() < 0.40)

            if choose_if:
                aux = self.rng.choice(_free)
                cond = self._sample_cond(ctr, lim, aux, vars_pool, nla_family)
                if can_ifelse and self.rng.random() < 0.55:
                    t1 = self.rng.choice(_free)
                    p1 = self.rng.choice([w for w in _free if w != t1] or [t1])
                    t2 = self.rng.choice(_free)
                    p2 = self.rng.choice([w for w in _free if w != t2] or [t2])
                    body.append(
                        IfElse(
                            cond=cond,
                            then_body=[self._semantic_assign(t1, p1, ctr, lim, vars_pool, nla_family)],
                            else_body=[self._semantic_assign(t2, p2, ctr, lim, vars_pool, nla_family)],
                        )
                    )
                    used_assign += 2
                    used_if += 1
                else:
                    t = self.rng.choice(_free)
                    p = self.rng.choice([w for w in _free if w != t] or [t])
                    body.append(IfOnly(cond=cond, then_body=[self._semantic_assign(t, p, ctr, lim, vars_pool, nla_family)]))
                    used_assign += 1
                    used_if += 1
                continue

            t = self.rng.choice(_free)
            p = self.rng.choice([w for w in _free if w != t] or [t])
            body.append(self._semantic_assign(t, p, ctr, lim, vars_pool, nla_family))
            used_assign += 1

        body = self._dedup_loop_body(body, ctr)
        body = self._shuffle_independent(body)

        if append_step:
            body.append(step_stmt)

        # Safety net: while(1) loops without an explicit break will spin forever.
        # If the guard is "1" and no template/DSL has inserted a break, append one
        # based on the counter reaching the limit.
        # Also ensure ctr is progressing; if a template took ownership (append_step=False)
        # and didn't write to ctr, we add the step so the break condition can eventually fire.
        if guard == "1" and not _has_break(body):
            if ctr not in _get_written_vars(body):
                body.append(step_stmt)
            body.append(IfOnly(cond=f"{ctr}>={lim}", then_body=[Break()]))

        # Cross-core guard-progress safety net:
        # If no guard variable is updated at all, inject one update so guard
        # is not structurally frozen. Prefer replacement to keep assign count stable.
        if guard != "1":
            gvars = self._guard_vars(guard)
            gw = set(gvars)
            if gw and not (gw & set(_get_written_vars(body))):
                progress = self._build_guard_progress_assign(guard, gvars)
                if progress is not None:
                    replaced = False
                    for i in range(len(body) - 1, -1, -1):
                        st = body[i]
                        if isinstance(st, Assign) and st.target not in gw:
                            body[i] = progress
                            replaced = True
                            break
                    if not replaced:
                        body.append(progress)

        if core_applied and self.rng.random() < 0.60:
            body = self._apply_template_small_variant(chosen, body, ctr)

        selected_core = chosen if core_applied else "none"
        guard = self._diversify_guard(guard)

        loop_stmt: Stmt = WhileLoop(cond=guard, body=body)
        # Equivalent control-flow variants:
        # while / for / while(1)+break ≈ 33/33/34
        if guard != "1":
            form = self.rng.choices(["while", "for", "while_one_break"], weights=[0.33, 0.33, 0.34], k=1)[0]
            if form == "for":
                if body and isinstance(body[-1], Assign) and body[-1] == step_stmt:
                    loop_stmt = ForLoop(cond=guard, step=step_stmt, body=body[:-1])
                # else: step not available (core-managed) — fall through to default WhileLoop
            elif form == "while_one_break":
                loop_stmt = WhileLoop(
                    cond="1",
                    body=[IfOnly(cond=f"!({guard})", then_body=[Break()])] + body,
                )
        return inits, loop_stmt, [ctr, lim] + state_vars, selected_core, core_vars

    def _arrange_loops(self, loops: List[Stmt]) -> List[Stmt]:
        if not loops:
            return []

        max_depth = max(1, self.hp.d_max)
        top_level: List[Stmt] = [loops[0]]
        prev_loop: Stmt = loops[0]
        prev_container: List[Stmt] = top_level
        prev_depth = 1

        for cur in loops[1:]:
            can_nest = prev_depth < max_depth
            do_nest = can_nest and (self.rng.random() < self.hp.q_nest)
            if do_nest and isinstance(prev_loop, (WhileLoop, ForLoop)):
                prev_loop.body.append(cur)
                cur_container = prev_loop.body
                cur_depth = prev_depth + 1
            else:
                prev_container.append(cur)
                cur_container = prev_container
                cur_depth = prev_depth
            prev_loop = cur
            prev_container = cur_container
            prev_depth = cur_depth

        return top_level

    def sample_program(self, idx: int, forced_loop_cores: Optional[List[Optional[str]]] = None) -> Program:
        params = self._pick_params()
        alloc = NameAllocator(params=params, rng=self.rng)

        local_inits: List[Tuple[str, str]] = []
        loops: List[Stmt] = []
        selected_cores: List[str] = []
        seen = set()
        universe: List[str] = []
        core_usage: Dict[str, int] = {}

        loop_count = self._sample_loop_count()

        # Program-level semantic pairing: when multiple loops exist and the
        # p_multi_semantic gate fires, pick a paired template (ML-series) so
        # Loop 1 and Loop 2 share a coherent inter-loop invariant.
        force_cores: List[Optional[str]] = [None] * loop_count
        if forced_loop_cores:
            for i, c in enumerate(forced_loop_cores):
                if i < loop_count and c:
                    force_cores[i] = c
        if loop_count >= 2 and self.rng.random() < self.hp.p_multi_semantic:
            ml_key = self.rng.choice(list(MULTI_LOOP_TEMPLATES.keys()))
            c1, c2 = MULTI_LOOP_TEMPLATES[ml_key]
            force_cores[0] = c1
            force_cores[1] = c2

        max_local_vars = self.hp.m
        for loop_idx in range(loop_count):
            remaining = max_local_vars - len(seen)
            force_c = force_cores[loop_idx] if loop_idx < len(force_cores) else None
            inits, loop, produced, core_name, _ = self._sample_core_loop(
                alloc, params, universe, remaining, core_usage, force_core=force_c
            )
            for v, e in inits:
                if v not in seen:
                    local_inits.append((v, e))
                    seen.add(v)
            loops.append(loop)
            selected_cores.append(core_name)
            universe.extend(produced)
            core_usage[core_name] = core_usage.get(core_name, 0) + 1

        arranged = self._arrange_loops(loops)

        # ── Dead-local pruning ────────────────────────────────────────────────
        # Collect every identifier mentioned in any loop (guard + body).
        # Then expand transitively: if local v is needed, every var in its
        # init expression is also needed (so the C declaration stays valid).
        # Drop locals that are unreachable by this closure — they are truly
        # dead and inflate the declared-variable count beyond hp.m's intent.
        loop_text = "\n".join(line for s in arranged for line in s.render(0))
        needed: set = set(re.findall(r"\b([a-z_]\w*)\b", loop_text))
        init_map = {v: e for v, e in local_inits}
        changed = True
        while changed:
            changed = False
            for v, e in local_inits:
                if v in needed:
                    for dep in re.findall(r"\b([a-z_]\w*)\b", e):
                        if dep not in needed and dep in init_map:
                            needed.add(dep)
                            changed = True
        local_inits = [(v, e) for v, e in local_inits if v in needed]

        return Program(
            name=f"main{idx + 1}",
            params=params,
            local_inits=local_inits,
            body=arranged,
            selected_cores=selected_cores,
        )


# ─── Trace-based semantic scorer ─────────────────────────────────────────────
def _c_to_py(s: str) -> str:
    """Minimal C-to-Python expression conversion for eval()."""
    s = re.sub(r"&&", " and ", s)
    s = re.sub(r"\|\|", " or ", s)
    # Replace logical ! but not !=
    s = re.sub(r"!(?!=)", " not ", s)
    return s


_TRACE_MAX_INT = (1 << 31) - 1  # clamp to signed 32-bit range to avoid bignum slowdown


def _c_eval_int(expr: str, env: Dict[str, int]) -> int:
    try:
        result = int(eval(_c_to_py(expr), {"__builtins__": {}}, dict(env)))
        return max(-_TRACE_MAX_INT, min(_TRACE_MAX_INT, result))
    except Exception:
        return 0


def _c_eval_bool(cond: str, env: Dict[str, int]) -> bool:
    try:
        return bool(eval(_c_to_py(cond), {"__builtins__": {}}, dict(env)))
    except Exception:
        return False


def _exec_stmts(stmts: List[Stmt], env: Dict[str, int], budget: List[int]) -> bool:
    """Execute statement list in-place; return False if a Break was hit."""
    for stmt in stmts:
        if budget[0] <= 0:
            return True  # timeout – continue outer loop
        if isinstance(stmt, Assign):
            env[stmt.target] = _c_eval_int(stmt.expr, env)
        elif isinstance(stmt, Break):
            return False
        elif isinstance(stmt, IfOnly):
            if _c_eval_bool(stmt.cond, env):
                if not _exec_stmts(stmt.then_body, env, budget):
                    return False
        elif isinstance(stmt, IfElse):
            branch = stmt.then_body if _c_eval_bool(stmt.cond, env) else stmt.else_body
            if not _exec_stmts(branch, env, budget):
                return False
        elif isinstance(stmt, WhileLoop):
            while _c_eval_bool(stmt.cond, env) and budget[0] > 0:
                budget[0] -= 1
                if not _exec_stmts(stmt.body, env, budget):
                    break  # Break stmt exits while
        elif isinstance(stmt, ForLoop):
            while _c_eval_bool(stmt.cond, env) and budget[0] > 0:
                budget[0] -= 1
                if not _exec_stmts(stmt.body, env, budget):
                    break
                if stmt.step is not None:
                    env[stmt.step.target] = _c_eval_int(stmt.step.expr, env)
    return True


def _has_break(stmts: List[Stmt]) -> bool:
    """Return True if any Break occurs directly or inside an if-branch."""
    for s in stmts:
        if isinstance(s, Break):
            return True
        if isinstance(s, IfOnly) and _has_break(s.then_body):
            return True
        if isinstance(s, IfElse) and (_has_break(s.then_body) or _has_break(s.else_body)):
            return True
    return False


def trace_score(
    program: "Program",
    n_trials: int = 16,
    max_steps: int = 150,
    seed: int = 777,
) -> float:
    """
    Evaluate semantic quality of a generated Program.  Returns a score in [0,1].

    Three components weighted 50/30/20:
      termination_rate  – fraction of random inputs that finish within max_steps
      diversity         – normalised unique final-state count across trials
      coverage          – fraction of local vars that actually change

    Typical thresholds: score >= 0.50 → keep; < 0.35 → reject garbage loops.
    max_steps=150 is enough for the typical generated loop bounds (8-105 iterations).

    Usage::
        prog = factory.sample_program(0)
        if trace_score(prog) >= 0.45:
            submit(prog)
    """
    rng = random.Random(seed)
    local_names = [v for v, _ in program.local_inits]
    param_range = max(1, 60 // max(1, len(program.params)))

    # Fast-reject: while(1) loops without any Break are non-terminating by design.
    for stmt in program.body:
        if isinstance(stmt, WhileLoop) and stmt.cond.strip() == "1" and not _has_break(stmt.body):
            return 0.0

    terminated = 0
    final_states: List[Tuple] = []

    for _ in range(n_trials):
        env: Dict[str, int] = {p: rng.randint(1, param_range) for p in program.params}
        for v, e in program.local_inits:
            env[v] = _c_eval_int(e, env)

        budget = [max_steps]
        _exec_stmts(program.body, env, budget)

        if budget[0] > 0:
            terminated += 1
        final_states.append(tuple(env.get(v, 0) for v in local_names))

    term_rate = terminated / n_trials

    # Diversity: fraction of unique final states
    diversity = len(set(final_states)) / max(1, n_trials)

    # Coverage: fraction of local vars that differ across trials
    if local_names and len(final_states) >= 2:
        coverage = sum(
            1 for i in range(len(local_names))
            if len(set(s[i] for s in final_states)) > 1
        ) / len(local_names)
    else:
        coverage = 0.0

    return 0.50 * term_rate + 0.30 * diversity + 0.20 * coverage


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Probabilistic DSL numeric loop synthesis")
    parser.add_argument("--profile", choices=["benchmark", "rich"], default="benchmark")
    parser.add_argument("--out-dir", type=Path, default=Path("generated"), help="Output directory")
    parser.add_argument("--count", type=int, default=50, help="Number of generated C files")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    parser.add_argument("--max-vars", type=int, default=10, help="Maximum number of variables")
    parser.add_argument("--params", "--max-params", type=int, default=3, help="Max number of parameter variables (upper bound)")
    parser.add_argument("--min-params", type=int, default=1, help="Min number of parameter variables (lower bound, can be 0)")

    parser.add_argument("--top-loops", type=int, default=3, help="Deprecated compatibility alias of --max-loops")
    parser.add_argument("--min-loops", type=int, default=1, help="Program-level while lower bound")
    parser.add_argument("--max-loops", type=int, default=None, help="Program-level while upper bound; actual sampled in [1, max-loops]")
    parser.add_argument("--max-assign", type=int, default=6, help="Per-loop assign upper bound; actual sampled in [min-assign, max-assign], includes loop-step")
    parser.add_argument("--min-assign", type=int, default=1, help="Per-loop assign lower bound (default 1)")
    parser.add_argument("--max-ifelse", type=int, default=4, help="Per-loop if/if-else upper bound; actual sampled in [min-ifelse, max-ifelse]")
    parser.add_argument("--min-ifelse", type=int, default=0, help="Per-loop if/if-else lower bound (default 0)")
    parser.add_argument("--min-vars", type=int, default=1, help="Per-loop state-variable lower bound (default 1)")

    parser.add_argument("--max-depth", type=int, default=2, help="Max loop nesting depth")
    parser.add_argument("--p-multi", type=float, default=0.12, help="Loop continuation probability p")
    parser.add_argument("--q-nest", type=float, default=0.12, help="Loop nesting probability q")

    parser.add_argument("--p-nonlinear", type=float, default=0.58, help="Probability of NLA-like loop family")
    parser.add_argument("--nonlinear-strength", type=float, default=0.70, help="Strength of nonlinear updates in NLA-like loops")
    parser.add_argument("--p-semantic-core", type=float, default=_cfg_or_default("p_semantic_core", 1.0), help="Probability to inject one semantic core rule in a loop")
    parser.add_argument("--p-multi-semantic", type=float, default=0.75, help="Probability that a multi-loop program uses an ML-series semantic pairing")
    parser.add_argument("--allowed-templates", type=str, default="", help="Comma-separated whitelist of template names and/or core names. Empty means all templates.")
    parser.add_argument("--force-core", type=str, default="", help="Force semantic core for loop 0 (single-loop generation is recommended).")
    parser.add_argument(
        "--llm-core-gen",
        action="store_true",
        default=_cfg_bool("llm_core_gen", False),
        help="Use LLM-guided loop generation for selected semantic cores before falling back to DSL.",
    )
    parser.add_argument("--print-usable-cores-json", action="store_true", help="Print usable semantic cores as JSON and exit.")
    parser.add_argument("--probe-max-resample", type=int, default=128, help="Max resamples per core when probing usable semantic cores.")
    parser.add_argument(
        "--dump-input-template-map-csv",
        type=Path,
        default=None,
        help="Optional: write full input->template mapping CSV and exit.",
    )
    parser.add_argument(
        "--input-template-map-strategy",
        choices=["doc_granularity", "min_cover", "max_cover", "one_to_one"],
        default="doc_granularity",
        help="Strategy for input->template mapping export.",
    )
    parser.add_argument(
        "--audit-loop-template-coverage",
        action="store_true",
        help="Audit that all loop-containing input files are covered by template mapping and exit.",
    )
    return parser


def _iter_loops(stmts: Sequence[Stmt]) -> List[Stmt]:
    out: List[Stmt] = []
    for s in stmts:
        if isinstance(s, (WhileLoop, ForLoop)):
            out.append(s)
            out.extend(_iter_loops(s.body))
        elif isinstance(s, IfOnly):
            out.extend(_iter_loops(s.then_body))
        elif isinstance(s, IfElse):
            out.extend(_iter_loops(s.then_body))
            out.extend(_iter_loops(s.else_body))
    return out


def _declared_semantic_cores() -> List[str]:
    """
    Parse core names from allow("...") declarations in this source file.
    Keeps probe/list behavior aligned with the actual candidate registry.
    """
    src = Path(__file__).read_text(encoding="utf-8")
    names = sorted(set(re.findall(r'allow\("([A-Za-z0-9_]+)"', src)))
    return names


def _declared_core_min_state_vars() -> Dict[str, int]:
    """
    Parse required state-var lower bound from allow("core", w, need_if, need_asg, need_vars).
    Keeps forced-core feasibility checks aligned with the candidate registry.
    """
    src = Path(__file__).read_text(encoding="utf-8")
    out: Dict[str, int] = {}
    pat = re.compile(
        r'allow\("([A-Za-z0-9_]+)"\s*,\s*[^,]+,\s*\d+\s*,\s*\d+\s*,\s*(\d+)\)'
    )
    for m in pat.finditer(src):
        out[m.group(1)] = int(m.group(2))
    return out


CORE_MIN_STATE_VARS = _declared_core_min_state_vars()
_DECLARED_LLM_CORES = set(_declared_semantic_cores()) - {"core"}
_MISSING_LLM_REQS = _DECLARED_LLM_CORES - set(CORE_LLM_REQUIREMENTS)
if _MISSING_LLM_REQS:
    raise RuntimeError(
        "Missing LLM prompt requirements for semantic cores: "
        + ", ".join(sorted(_MISSING_LLM_REQS))
    )


def _count_assigns_in_loop(loop_stmt: Stmt) -> int:
    def _count(stmts: Sequence[Stmt]) -> int:
        n = 0
        for s in stmts:
            if isinstance(s, Assign):
                n += 1
            elif isinstance(s, IfOnly):
                n += _count(s.then_body)
            elif isinstance(s, IfElse):
                n += _count(s.then_body) + _count(s.else_body)
        return n

    if isinstance(loop_stmt, ForLoop):
        return _count(loop_stmt.body) + (1 if loop_stmt.step is not None else 0)
    if isinstance(loop_stmt, WhileLoop):
        return _count(loop_stmt.body)
    return 0


def _count_if_nodes_in_loop(loop_stmt: Stmt) -> int:
    def _count(stmts: Sequence[Stmt]) -> int:
        n = 0
        for s in stmts:
            if isinstance(s, IfOnly):
                n += 1 + _count(s.then_body)
            elif isinstance(s, IfElse):
                n += 1 + _count(s.then_body) + _count(s.else_body)
        return n

    if isinstance(loop_stmt, (WhileLoop, ForLoop)):
        return _count(loop_stmt.body)
    return 0


def _guard_vars_from_cond(cond: str) -> Set[str]:
    toks = re.findall(r"\b([A-Za-z_]\w*)\b", cond or "")
    banned = {"if", "else", "while", "for", "break"}
    out: Set[str] = set()
    for t in toks:
        if t in banned or t.isdigit():
            continue
        out.add(t)
    return out


def _looks_like_break_guard(st: Stmt) -> Optional[str]:
    """
    Detect synthesized `if (!(guard)) break;` wrapper and return the inner guard.
    """
    if not isinstance(st, IfOnly):
        return None
    if len(st.then_body) != 1 or not isinstance(st.then_body[0], Break):
        return None
    m = re.match(r"^\s*!\((.*)\)\s*$", st.cond.strip())
    if not m:
        return None
    return m.group(1).strip()


def _loop_has_guard_driver_update(loop_stmt: Stmt) -> bool:
    """
    Structural termination sanity check:
    guard-driving variables must be written in loop body/step.
    """
    if isinstance(loop_stmt, ForLoop):
        gvars = _guard_vars_from_cond(loop_stmt.cond)
        if not gvars:
            return True
        written = set(_get_written_vars(loop_stmt.body))
        if loop_stmt.step is not None:
            written.add(loop_stmt.step.target)
        return bool(gvars & written)

    if not isinstance(loop_stmt, WhileLoop):
        return True

    cond = (loop_stmt.cond or "").strip()
    if cond != "1":
        gvars = _guard_vars_from_cond(cond)
        if not gvars:
            return True
        written = set(_get_written_vars(loop_stmt.body))
        return bool(gvars & written)

    # while(1): must have break; if it's the canonical guard-wrapper form,
    # require updates to the wrapped guard drivers in the remaining body.
    if not _has_break(loop_stmt.body):
        return False
    if not loop_stmt.body:
        return True
    wrapped_guard = _looks_like_break_guard(loop_stmt.body[0])
    if wrapped_guard is None:
        return True
    gvars = _guard_vars_from_cond(wrapped_guard)
    if not gvars:
        return True
    written = set(_get_written_vars(loop_stmt.body[1:]))
    return bool(gvars & written)


def _satisfy_hard_constraints(program: Program, hp: HyperParams) -> bool:
    if not (hp.min_params <= len(program.params) <= hp.p):
        return False
    if len(program.local_inits) > hp.m:
        return False

    loops = _iter_loops(program.body)
    if not (hp.min_while_fuel <= len(loops) <= hp.while_fuel):
        return False

    for lp in loops:
        n_assign = _count_assigns_in_loop(lp)
        if not (hp.min_assign <= n_assign <= hp.assign_fuel):
            return False
        n_if = _count_if_nodes_in_loop(lp)
        if not (hp.min_ifelse <= n_if <= hp.ifelse_fuel):
            return False
        if not _loop_has_guard_driver_update(lp):
            return False
    return True


def _probe_usable_semantic_cores(hp: HyperParams, base_seed: int, max_resample: int) -> List[str]:
    usable: List[str] = []
    declared = _declared_semantic_cores()
    if hp.allowed_cores:
        declared = [c for c in declared if c in set(hp.allowed_cores)]
    for idx, core in enumerate(declared):
        # Keep each core probe deterministic and independent.
        rng = random.Random(base_seed + 1000003 * (idx + 1))
        factory = ProbabilisticLoopFactory(hp, rng)
        ok = False
        for _ in range(max_resample):
            try:
                cand = factory.sample_program(0, forced_loop_cores=[core])
                if _satisfy_hard_constraints(cand, hp):
                    ok = True
                    break
            except Exception:
                # Forced core may be incompatible with sampled variable budgets; treat as unusable.
                continue
        if ok:
            usable.append(core)
    return usable


def main() -> None:
    args = build_arg_parser().parse_args()
    if args.dump_input_template_map_csv is not None:
        write_input_template_map_csv(args.dump_input_template_map_csv, strategy=args.input_template_map_strategy)
        print(f"Wrote input-template mapping CSV to {args.dump_input_template_map_csv}")
        return
    if args.audit_loop_template_coverage:
        stats = audit_loop_template_coverage(strategy=args.input_template_map_strategy)
        print(
            "Loop template coverage OK:",
            f"loop_files={stats['loop_files_total']}",
            f"loops={stats['loops_total']}",
            f"mapped_files={stats['mapped_files_total']}",
            f"unique_templates={stats['unique_templates']}",
        )
        return
    max_loops_arg = args.max_loops if args.max_loops is not None else args.top_loops
    allowed_items = _cfg_list("allowed_templates")
    if args.allowed_templates.strip():
        allowed_items = [x.strip() for x in args.allowed_templates.split(",") if x.strip()]
    allowed_cores = tuple(sorted(_resolve_allowed_cores(allowed_items)))

    hp = HyperParams(
        m=max(1, args.max_vars),
        p=max(0, args.params),
        min_params=max(0, min(args.min_params, args.params)),
        min_while_fuel=max(1, args.min_loops),
        while_fuel=max(1, max_loops_arg),
        assign_fuel=max(1, args.max_assign),
        ifelse_fuel=max(0, args.max_ifelse),
        min_assign=max(1, min(args.min_assign, args.max_assign)),
        min_ifelse=max(0, min(args.min_ifelse, args.max_ifelse)),
        min_vars=max(1, args.min_vars),
        d_max=max(1, args.max_depth),
        p_multi=max(0.0, min(1.0, args.p_multi)),
        q_nest=max(0.0, min(1.0, args.q_nest)),
        p_nonlinear=max(0.0, min(1.0, args.p_nonlinear)),
        nonlinear_strength=max(0.0, min(1.0, args.nonlinear_strength)),
        p_semantic_core=max(0.0, min(1.0, args.p_semantic_core)),
        p_multi_semantic=max(0.0, min(1.0, args.p_multi_semantic)),
        w_core_rel_guard=DEFAULT_CORE_KNOBS["w_core_rel_guard"],
        w_core_cond_fixed=DEFAULT_CORE_KNOBS["w_core_cond_fixed"],
        w_core_linear_state=DEFAULT_CORE_KNOBS["w_core_linear_state"],
        w_core_min_update=DEFAULT_CORE_KNOBS["w_core_min_update"],
        w_core_qr_division=DEFAULT_CORE_KNOBS["w_core_qr_division"],
        w_core_euclid_matrix=DEFAULT_CORE_KNOBS["w_core_euclid_matrix"],
        allowed_cores=allowed_cores,
        llm_core_gen=bool(args.llm_core_gen),
    )

    if args.print_usable_cores_json:
        usable = _probe_usable_semantic_cores(hp, args.seed, max(1, args.probe_max_resample))
        print(json.dumps(usable, ensure_ascii=False))
        return

    rng = random.Random(args.seed)
    factory = ProbabilisticLoopFactory(hp, rng)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    max_resample = 512
    generation_meta: List[Dict[str, object]] = []
    for i in range(args.count):
        program = None
        for _ in range(max_resample):
            forced = [args.force_core] if args.force_core else None
            candidate = factory.sample_program(i, forced_loop_cores=forced)
            if _satisfy_hard_constraints(candidate, hp):
                program = candidate
                break
        if program is None:
            raise RuntimeError(
                "Failed to satisfy hard constraints after "
                f"{max_resample} tries for index={i} with "
                f"max_vars={hp.m}, min/max params={hp.min_params}/{hp.p}, "
                f"min/max loops={hp.min_while_fuel}/{hp.while_fuel}, "
                f"min/max assign={hp.min_assign}/{hp.assign_fuel}, "
                f"min/max ifelse={hp.min_ifelse}/{hp.ifelse_fuel}."
            )
        out_file = args.out_dir / f"{i + 1}.c"
        out_file.write_text(program.render() + "\n", encoding="utf-8")
        primary_core = next((c for c in program.selected_cores if c != "none"), "none")
        generation_meta.append(
            {
                "index": i + 1,
                "file": out_file.name,
                "selected_cores": program.selected_cores,
                "selected_core_primary": primary_core,
                "loop_count": len(program.selected_cores),
                "llm_core_gen": bool(args.llm_core_gen),
            }
        )

    (args.out_dir / "generation_meta.json").write_text(
        json.dumps(generation_meta, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    print(f"Generated {args.count} files under {args.out_dir}")


if __name__ == "__main__":
    main()
