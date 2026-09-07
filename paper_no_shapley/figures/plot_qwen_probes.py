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
    ax.set_xscale("log")
    ax.set_xticks(display_ticks)
    ax.set_xticklabels([str(k) for k in display_ticks])
    ax.set_xlabel("Number of responses, $k$")
    ax.set_ylabel("Verification rate (%)")
    ax.grid(True, which="major", alpha=0.8)
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
            linewidth=1.7,
            markersize=4.2,
            markeredgewidth=0.6,
            markeredgecolor="white",
        )


def official_probe() -> None:
    require_complete(OFFICIAL, "official_probe", RQ1_K)
    fig, axes = plt.subplots(2, 3, figsize=(7.2, 3.75), sharex=True, sharey=True)
    panel_names = ["(a)", "(b)", "(c)", "(d)", "(e)", "(f)"]
    for panel, (model, values) in enumerate(OFFICIAL.items()):
        ax = axes.flat[panel]
        ax.plot(
            RQ1_K,
            values["direct"],
            label="pass@$k$",
            color=RUST,
            marker="o",
            linestyle="-",
            linewidth=1.6,
            markersize=3.8,
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
            linewidth=1.6,
            markersize=3.8,
            markeredgewidth=0.5,
            markeredgecolor="white",
        )
        ax.set_xscale("log")
        ax.set_xticks(RQ1_K)
        ax.set_xticklabels([str(k) for k in RQ1_K])
        ax.set_xlabel("Number of responses, $k$")
        ax.set_ylabel("Verification rate (%)")
        ax.grid(True, which="major", alpha=0.8)
        ax.spines[["top", "right"]].set_visible(False)
        ax.set_title(f"{panel_names[panel]} {model}")
        ax.set_ylim(0, 72)

    # Shared labels keep the six model-specific panels compact.
    axes[0, 0].set_xlabel("")
    axes[0, 1].set_xlabel("")
    axes[0, 2].set_xlabel("")
    axes[0, 1].set_ylabel("")
    axes[0, 2].set_ylabel("")
    axes[1, 1].set_ylabel("")
    axes[1, 2].set_ylabel("")
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False)
    fig.tight_layout(rect=(0, 0, 1, 0.90), h_pad=0.9, w_pad=1.0)
    fig.savefig(OUT / "base_model_probe.pdf", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    configure()
    official_probe()
