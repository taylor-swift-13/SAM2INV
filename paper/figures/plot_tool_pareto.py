#!/usr/bin/env python3
"""Plot RQ3 verification rates against token use and end-to-end time."""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from paper_style import FAINT, GREEN, INK, MUTED, RUST, use_paper_style

OUT = Path(__file__).resolve().parent

# (mean total tokens / called task, verified %, mean seconds / task).
# Source: appendix.tex, tab:tools-complete, reasoning-disabled rows.
BASELINES = {
    "AutoSpec": (2181.72, 42.19, 27.34),
    "SESpec": (22081.61, 29.69, 68.50),
    "Clause2Inv": (1056.25, 7.93, 8.41),
    "Loopy": (14513.37, 18.75, 147.16),
}
NAIVE = (225.95, 16.47, 2.98)
DAIKON = (0, 20.91, 4.89)
# GPT-5-nano CRAFT times combine archived generation latency with measured
# prefix filtering and verification; see artifacts/v4/tool_compose_cost.json.
OURS = {
    "@1": (1136.82, 33.89, 24.52),
    "@4": (1905.10, 49.04, 46.40),
    "@8": (2929.47, 55.53, 69.99),
}
# User-supplied trained-checkpoint measurements, including end-to-end time.
TRAINED = {
    "@1": (1348, 70.31, 28.2),
    "@4": (2053, 75.60, 33.5),
    "@8": (2993, 77.28, 40.9),
}


def plot_panel(ax: plt.Axes, cost_index: int) -> None:
    is_time = cost_index == 2
    baseline_labels = {
        "AutoSpec": ((-5, 5), "right") if is_time else ((5, -5), "left"),
        "SESpec": ((7, 2), "left") if is_time else ((-3, -5), "right"),
        "Clause2Inv": ((5, -3), "left") if is_time else ((2, 1), "left"),
        "Loopy": ((-2, -10), "center") if is_time else ((-2, -12), "center"),
    }
    for name, value in BASELINES.items():
        point = (value[cost_index], value[1])
        ax.scatter(*point, s=26, marker="o", color=MUTED,
                   edgecolor="white", linewidth=0.5, zorder=3)
        offset, alignment = baseline_labels[name]
        ax.annotate(name, point, xytext=offset, ha=alignment,
                    textcoords="offset points", color=INK, fontsize=7.0)

    for name, value in [("Naive", NAIVE), *([("Daikon", DAIKON)] if is_time else [])]:
        point = (value[cost_index], value[1])
        ax.scatter(*point, s=26, marker="o", color=MUTED,
                   edgecolor="white", linewidth=0.5, zorder=3)
        ax.annotate(name, point, xytext=(0, -12) if is_time and name == "Naive" else (5, 6),
                    textcoords="offset points",
                    color=INK, fontsize=7.0)

    for data, label, color, marker, style in (
        (OURS, "CRAFT (GPT-5-nano)", GREEN, "D", "-"),
        (TRAINED, "CRAFT (trained)", RUST, "^", "--"),
    ):
        xs = [value[cost_index] for value in data.values()]
        ys = [value[1] for value in data.values()]
        ax.plot(xs, ys, color=color, marker=marker, markersize=5.6,
                markeredgecolor="white", markeredgewidth=0.5,
                linewidth=1.4, linestyle=style, label=label, zorder=4)
        for budget, value in data.items():
            offset, alignment = (5, -3), "left"
            if is_time and budget == "@4":
                offset, alignment = (0, 11), "center"
            if data is TRAINED:
                offset, alignment = {
                    "@1": ((-4, -9), "right"),
                    "@4": ((-1, 9), "center"),
                    "@8": ((4, 0), "left"),
                }[budget]
            ax.annotate(budget, (value[cost_index], value[1]), xytext=offset,
                        textcoords="offset points", va="center", ha=alignment,
                        color=color, fontsize=7.4, fontweight="bold")

    ax.set_xscale("log")
    if is_time:
        ax.set_xlim(2.2, 220)
        ax.set_xticks([3, 30, 200])
        ax.set_xticklabels(["3", "30", "200"])
        ax.set_xlabel("Time / task (s)", labelpad=5)
        ax.set_title("(b) Time", loc="left", pad=7)
    else:
        ax.set_xlim(170, 30000)
        ax.set_xticks([200, 2000, 20000])
        ax.set_xticklabels(["0.2k", "2k", "20k"])
        ax.set_xlabel("Tokens / called task", labelpad=5)
        ax.set_title("(a) Tokens", loc="left", pad=7)
    ax.set_ylim(0, 90)
    ax.set_yticks([0, 20, 40, 60, 80])
    ax.grid(axis="y", color=FAINT, linewidth=0.55, alpha=0.9)
    ax.spines[["top", "right"]].set_visible(False)
    ax.tick_params(color="#92A39A", width=0.6)


def main() -> None:
    use_paper_style(base_size=8.2)
    plt.rcParams.update({"axes.titlesize": 8.5, "axes.labelsize": 8.2,
                         "legend.fontsize": 8.2, "xtick.labelsize": 7.4,
                         "ytick.labelsize": 7.4})
    fig, axes = plt.subplots(1, 2, figsize=(3.65, 2.3), sharey=True)
    plot_panel(axes[0], 0)
    plot_panel(axes[1], 2)
    axes[0].set_ylabel("Verified (%)", labelpad=5)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False,
               bbox_to_anchor=(0.53, 1.02), handlelength=1.8, columnspacing=1.2)
    fig.subplots_adjust(left=0.13, right=0.985, bottom=0.25, top=0.72,
                        wspace=0.23)
    fig.savefig(OUT / "tool_pareto.pdf", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    main()
