#!/usr/bin/env python3
"""Plot target visibility for the fixed Qwen3-8B SFT+RL checkpoint."""

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from paper_style import GREEN, SLATE, use_paper_style


def main() -> None:
    output = Path(__file__).resolve().parent
    data = json.loads((output.parent / "artifacts/target_visibility.json").read_text())
    k = data["k"]
    hidden = data["target_hidden"]
    visible = data["target_visible"]
    visible_compose = [100 * n / data["programs"] for n in visible["compose_counts"]]

    use_paper_style()
    fig, axes = plt.subplots(1, 2, figsize=(7.15, 2.85))
    panels = [
        ("(a) compose@$k$", hidden["compose_percent"], visible_compose,
         (65, 85), [65, 70, 75, 80, 85]),
        ("(b) pass@$k$", hidden["pass_percent"], visible["pass_percent"],
         (25, 65), [25, 35, 45, 55, 65]),
    ]
    for ax, (title, hidden_values, visible_values, limits, ticks) in zip(axes, panels):
        for label, values, color, marker, linestyle in [
            ("Target-hidden", hidden_values, SLATE, "s", "--"),
            ("Target-visible", visible_values, GREEN, "o", "-"),
        ]:
            ax.plot(k, values, label=label, color=color, marker=marker,
                    linestyle=linestyle, linewidth=1.7, markersize=4.2,
                    markeredgewidth=0.6, markeredgecolor="white")
            ax.annotate(f"{values[-1]:.2f}", (k[-1], values[-1]),
                        xytext=(5, 0), textcoords="offset points",
                        va="center", color=color, fontsize=7.2)
        ax.set_title(title)
        ax.set_xscale("log", base=2)
        ax.set_xlim(0.85, 55)
        ax.set_xticks(k, labels=[str(value) for value in k])
        ax.minorticks_off()
        ax.set_ylim(*limits)
        ax.set_yticks(ticks)
        ax.set_xlabel("Number of responses, $k$")
        ax.set_ylabel("Verification rate (%)")
        ax.grid(True, which="major", alpha=0.8)
        ax.set_axisbelow(True)
        ax.spines[["top", "right"]].set_visible(False)

    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False)
    fig.tight_layout(rect=(0, 0, 1, 0.89), w_pad=2)
    fig.savefig(output / "target_visibility.pdf", bbox_inches="tight")
    fig.savefig(output / "target_visibility.png", dpi=200, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    main()
