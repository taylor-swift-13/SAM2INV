#!/usr/bin/env python3
"""Generate the reward-function ablation figure (RQ5).

Budget grid: k in {1, 4, 8, 16, 32}.  Both panels report Qwen3-8B reward
ablations initialized from Bare.  Reference checkpoints before RL are dotted.
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from paper_style import GREEN, MUTED, OCHRE, RUST, SLATE, TEAL, use_paper_style


OUT = Path(__file__).resolve().parent

K = [1, 4, 8, 16, 32]

VARIANTS = {
    "Binary": {
        "pass": [3.78, 6.21, 7.72, 9.40, 11.26],
        "combine": [7.21, 12.26, 16.71, 20.31, 23.32],
        "color": RUST,   # baseline family
        "marker": "o",
        "style": "-",
    },
    "Whole-rollout": {
        "pass": [16.67, 19.17, 20.03, 20.90, 21.92],
        "combine": [18.87, 19.95, 20.31, 21.27, 22.72],
        "color": OCHRE,  # weak ablation
        "marker": "s",
        "style": "--",
    },
    "Clause-decomposed": {
        "pass": [4.10, 9.35, 12.27, 14.88, 17.14],
        "combine": [48.08, 57.33, 60.22, 61.54, 61.90],
        "color": SLATE,  # decomposed ablation
        "marker": "^",
        "style": "-.",
    },
    "Full (ours)": {
        "pass": [6.80, 13.41, 16.80, 20.17, 23.44],
        "combine": [57.93, 66.95, 70.43, 72.60, 73.20],
        "color": GREEN,  # ours
        "marker": "D",
        "style": "-",
    },
}

UNTRAINED = {
    "pass": [6.43, 13.24, 17.33, 21.62, 25.96],
    "combine": [37.86, 50.60, 54.21, 56.37, 57.81],
}

def configure() -> None:
    use_paper_style(base_size=8.2)


def style_axis(ax: plt.Axes) -> None:
    ax.set_xscale("log", base=2)
    ax.minorticks_off()
    ax.set_xticks(K)
    ax.set_xticklabels([str(k) for k in K])
    ax.set_xlabel("Number of responses, $k$")
    ax.set_ylabel("Verified (%)")
    ax.grid(axis="y", alpha=0.8)
    ax.tick_params(color="#92A39A", width=0.6)
    ax.spines[["top", "right"]].set_visible(False)


def plot_panel(
    ax: plt.Axes, metric: str, reference: dict, variants: dict
) -> None:
    ax.plot(
        K,
        reference[metric],
        label="Before RL",
        color=MUTED,
        marker="x",
        linestyle=":",
        linewidth=1.19,
        markersize=4.5,
        markeredgewidth=0.9,
        alpha=0.9,
    )
    for label, values in variants.items():
        ax.plot(
            K,
            values[metric],
            label=label,
            color=values["color"],
            marker=values["marker"],
            linestyle=values["style"],
            linewidth=1.4,
            markersize=4.8,
            markeredgewidth=0.5,
            markeredgecolor="white",
        )


def reward_ablation() -> None:
    fig, axes = plt.subplots(1, 2, figsize=(3.65, 2.7))
    panels = [
        (axes[0], "combine", UNTRAINED, VARIANTS,
         "(a) compose@$k$", (0, 80)),
        (axes[1], "pass", UNTRAINED, VARIANTS,
         "(b) pass@$k$", (0, 36)),
    ]
    for panel_idx, (ax, metric, reference, variants, title, ylim) in enumerate(panels):
        plot_panel(ax, metric, reference, variants)
        style_axis(ax)
        ax.set_xlabel("Responses, $k$")
        if panel_idx:
            ax.set_ylabel("")
        ax.set_title(title, pad=7)
        ax.set_ylim(*ylim)
        ax.set_xlim(0.85, 38)

    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False,
               handlelength=1.8, columnspacing=1.1, bbox_to_anchor=(0.54, 1.01))
    fig.subplots_adjust(left=0.13, right=0.985, bottom=0.20, top=0.65,
                        wspace=0.30)
    fig.savefig(OUT / "reward_ablation.pdf", bbox_inches=None)
    plt.close(fig)


if __name__ == "__main__":
    configure()
    reward_ablation()
