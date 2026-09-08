#!/usr/bin/env python3
"""Restyle the archived gold-augmented coverage figure without rescoring.

ROC display geometry comes from the original vector PDF. Statistical values
and Wilson intervals come from the canonical archived summary, not from
integrating the simplified display paths.
"""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from paper_style import FAINT, GREEN, GREEN_TINT, INK, MUTED, OCHRE, RUST, SLATE, use_paper_style

OUT = Path(__file__).resolve().parent


def main() -> None:
    artifacts = OUT.parent / "artifacts/v4"
    summary = json.loads((artifacts / "negative_coverage_predictiveness.json").read_text())
    geometry = json.loads((artifacts / "negative_coverage_plot_geometry.json").read_text())
    use_paper_style()
    fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.5))
    for name, suite, color, style in (
        ("All", None, GREEN, "-"),
        ("Linear", "linear", SLATE, "--"),
        ("NLA", "NLA_lipus", OCHRE, "-."),
        ("Loopy", "Loopy", RUST, ":"),
    ):
        points = np.asarray(geometry["curves"][name])
        auc = (summary if suite is None else summary["by_suite"][suite])["macro_within_program_auroc"]
        axes[0].plot(points[:, 0], points[:, 1], color=color, linestyle=style,
                     linewidth=1.4, label=f"{name} ({auc:.3f})")
    axes[0].plot([0, 1], [0, 1], color=MUTED, linestyle="--", linewidth=1, alpha=0.6)
    axes[0].set(xlabel="False-positive rate", ylabel="True-positive rate",
                title="(a) Within-program ROC", xlim=(0, 1), ylim=(0, 1))
    axes[0].legend(title="Macro AUROC", loc="lower right", fontsize=9.2,
                   title_fontsize=9.4, labelspacing=0.35)

    bands = summary["coverage_bands"]
    x = np.arange(len(bands))
    rates = np.asarray([b["success_rate"] for b in bands])
    lower = rates - np.asarray([b["wilson_ci95"][0] for b in bands])
    upper = np.asarray([b["wilson_ci95"][1] for b in bands]) - rates
    axes[1].bar(x, rates, width=0.72, color=GREEN_TINT, edgecolor=GREEN, linewidth=1)
    axes[1].errorbar(x, rates, yerr=np.vstack([lower, upper]), fmt="none",
                     ecolor=INK, capsize=3.5, linewidth=1)
    axes[1].set_xticks(x, [b["band"] for b in bands], rotation=35, ha="right")
    axes[1].set(xlabel="Negative-coverage band", ylabel="Target verification rate",
                title="(b) Verification by coverage", ylim=(0, 1))
    for ax in axes:
        ax.grid(axis="y", color=FAINT, linewidth=0.55, alpha=0.8)
        ax.set_axisbelow(True)
    fig.subplots_adjust(left=0.09, right=0.985, bottom=0.30, top=0.86, wspace=0.36)
    fig.savefig(OUT / "negative_coverage_predictiveness.pdf", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    main()
