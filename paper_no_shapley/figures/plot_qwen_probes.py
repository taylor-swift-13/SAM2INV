#!/usr/bin/env python3
"""Generate the base-checkpoint exploration and paired RL figures.

Probe grid: k in {1, 4, 8, 16, 32}.  Qwen3-8B uses a 128-response saved
pool, Qwen3-30B-A3B and Llama 3.1-8B use 100, and the remaining base probes
use 32.  The paired RL comparison uses k in {1, 4, 8, 16, 32}.
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from paper_style import GREEN, RUST, SLATE, use_paper_style


OUT = Path(__file__).resolve().parent

RQ1_K = [1, 4, 8, 16, 32]
RL_K = [1, 4, 8, 16, 32]

OFFICIAL = {
    "Qwen3-1.7B": {
        "direct": [5.76, 10.87, 13.71, 16.72, 19.81],
        "combine": [19.47, 28.97, 33.05, 35.34, 37.86],
        "color": "#b47a5f",
        "marker": "P",
        "style": "-",
    },
    "Qwen3-4B": {
        "direct": [5.27, 9.93, 12.50, 15.14, 17.88],
        "combine": [32.93, 44.11, 47.60, 50.72, 52.76],
        "color": "#9d6652",
        "marker": "o",
        "style": "-",
    },
    "Qwen3-8B": {
        "direct": [6.43, 13.24, 17.33, 21.62, 25.96],
        "combine": [37.86, 50.60, 54.21, 56.37, 57.81],
        "color": "#4f8a6b",
        "marker": "s",
        "style": "--",
    },
    "Qwen3-14B": {
        "direct": [7.67, 14.17, 17.97, 22.04, 26.13],
        "combine": [43.51, 58.29, 61.54, 63.70, 64.54],
        "color": "#2d7053",
        "marker": "^",
        "style": "-.",
    },
    "Qwen3-30B-A3B": {
        "direct": [1.40, 4.53, 7.65, 12.15, 17.53],
        "combine": [17.43, 30.65, 36.54, 42.31, 43.87],
        "color": "#5b7185",
        "marker": "D",
        "style": ":",
    },
    "Llama 3.1-8B": {
        "direct": [0.61, 2.16, 3.81, 6.30, 9.76],
        "combine": [27.88, 46.03, 51.20, 51.68, 52.16],
        "color": "#75618f",
        "marker": "v",
        "style": "-",
    },
}

# Matched Qwen3-8B composition curves reported in RQ4 and the appendix.
RL_PAIRS = {
    "(a) Bare initialization": {
        "Before RL": [37.86, 50.60, 54.21, 56.37, 57.81],
        "After RL": [57.93, 66.95, 70.43, 72.60, 73.20],
    },
    "(b) SFT initialization": {
        "Before RL": [63.90, 73.80, 76.20, 77.30, 77.90],
        "After RL": [69.23, 75.24, 76.80, 77.64, 78.37],
    },
}


def require_complete(data: dict, name: str, ks: list[int]) -> None:
    """SystemExit on placeholder data so stale plots are never rendered."""
    missing = [
        f"{label}.{metric}"
        for label, values in data.items()
        for metric in ("direct", "combine")
        if values[metric] is None or any(v is None for v in values[metric])
    ]
    if missing:
        raise SystemExit(
            f"plot_qwen_probes ({name}): placeholder data on the k={ks} "
            "grid; fill from the new-grid recomputation first: "
            + ", ".join(missing)
        )


def configure() -> None:
    use_paper_style()


def style_axis(ax: plt.Axes, display_ticks: list[int]) -> None:
    ax.set_xscale("log", base=2)
    ax.minorticks_off()
    ax.set_xticks(display_ticks)
    ax.set_xticklabels([str(k) for k in display_ticks])
    ax.set_xlabel("Responses, $k$")
    ax.set_ylabel("Verification rate (%)")
    ax.grid(axis="y", alpha=0.8)
    ax.spines[["top", "right"]].set_visible(False)


def plot_lines(ax: plt.Axes, data: dict, metric: str, ks: list[int]) -> None:
    for label, values in data.items():
        ax.plot(
            ks,
            values[metric],
            label=label,
            color=values["color"],
            marker=values["marker"],
            linestyle=values["style"],
            linewidth=1.4,
            markersize=4.7,
            markeredgewidth=0.5,
            markeredgecolor="white",
        )


def official_probe() -> None:
    require_complete(OFFICIAL, "official_probe", RQ1_K)
    fig, axes = plt.subplots(1, 4, figsize=(7.2, 2.25), sharex=True, sharey=True)
    panel_names = ["(a)", "(b)", "(c)", "(d)"]
    # Additional small and MoE backbones remain in the appendix tables.
    main_models = ("Qwen3-4B", "Qwen3-8B", "Qwen3-14B", "Llama 3.1-8B")
    for panel, model in enumerate(main_models):
        values = OFFICIAL[model]
        ax = axes.flat[panel]
        ax.plot(
            RQ1_K,
            values["direct"],
            label="pass@$k$",
            color=RUST,
            marker="o",
            linestyle="-",
            linewidth=1.4,
            markersize=4.1,
            markeredgewidth=0.5,
            markeredgecolor="white",
        )
        ax.plot(
            RQ1_K,
            values["combine"],
            label="compose@$k$",
            color=GREEN,
            marker="s",
            linestyle="--",
            linewidth=1.4,
            markersize=4.1,
            markeredgewidth=0.5,
            markeredgecolor="white",
        )
        ax.set_xscale("log", base=2)
        ax.minorticks_off()
        ax.set_xlim(0.85, 38)
        ax.set_xticks(RQ1_K)
        ax.set_xticklabels([str(k) for k in RQ1_K])
        ax.set_xlabel("Responses, $k$")
        ax.set_ylabel("Verification rate (%)")
        ax.grid(axis="y", alpha=0.8)
        ax.spines[["top", "right"]].set_visible(False)
        ax.set_title(f"{panel_names[panel]} {model}", fontsize=9.2, pad=7)
        ax.tick_params(labelsize=8.2)
        ax.set_ylim(0, 72)
        ax.set_yticks([0, 20, 40, 60])

    # Shared axis labels leave room for readable titles and ticks.
    for ax in axes.flat:
        ax.set_xlabel("")
        ax.set_ylabel("")
    fig.supxlabel("Responses, $k$", y=0.01, fontsize=10)
    fig.supylabel("Verified (%)", x=0.01, fontsize=10)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2,
               bbox_to_anchor=(0.54, 1.0), columnspacing=2.5)
    fig.subplots_adjust(left=0.07, right=0.985, bottom=0.27, top=0.72,
                        wspace=0.22)
    fig.savefig(OUT / "base_model_probe.pdf", bbox_inches="tight")
    plt.close(fig)


def rl_comparison_probe() -> None:
    use_paper_style(base_size=8.2)
    fig, axes = plt.subplots(1, 2, figsize=(3.65, 2.7), sharey=True)
    styles = {
        "Before RL": (GREEN, "D", "-"),
        "After RL": (RUST, "^", "--"),
    }
    for ax, (title, pair) in zip(axes, RL_PAIRS.items()):
        for label, values in pair.items():
            color, marker, linestyle = styles[label]
            ax.plot(
                RL_K,
                values,
                label=label,
                color=color,
                marker=marker,
                linestyle=linestyle,
                linewidth=1.4,
                markersize=4.7,
                markeredgewidth=0.5,
                markeredgecolor="white",
            )
        style_axis(ax, RL_K)
        ax.set_title(title.replace(" initialization", ""), fontsize=8.5)
        ax.set_ylabel("Verified (%)")
        ax.set_ylim(34, 82)
        ax.set_xlim(0.85, 38)
    axes[1].set_ylabel("")
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False,
               bbox_to_anchor=(0.54, 0.88))
    fig.subplots_adjust(left=0.13, right=0.985, bottom=0.20, top=0.65,
                        wspace=0.23)
    fig.savefig(OUT / "qwen_rlzero_probe.pdf", bbox_inches=None)
    plt.close(fig)


if __name__ == "__main__":
    configure()
    official_probe()
    rl_comparison_probe()
