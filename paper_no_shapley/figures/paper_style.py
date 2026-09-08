#!/usr/bin/env python3
"""Shared visual style for every CRAFT paper figure.

One palette for all matplotlib PDFs and the overview SVG, so the paper reads
as a single visual system.  Keep in sync with:
  - the \\definecolor block in paper/main.tex (green/teal/olive/rust family)
  - the <style> tokens in paper/figures/overview.html

Usage in a plot script:
    from paper_style import GREEN, RUST, ..., use_paper_style
    use_paper_style()
"""

# ---------------------------------------------------------------- core hues
GREEN = "#2E7D5B"   # verified / ours / primary method
TEAL = "#347F78"    # SFT stage, secondary series
OCHRE = "#B87A2C"   # scorer / weak-baseline series
SLATE = "#5B7185"   # RL stage, "before" series
RUST = "#B85C47"    # rejected / baseline series
INK = "#1F3128"     # text
MUTED = "#66786F"   # secondary text, axes, untrained reference
FAINT = "#D8E2DC"   # hairlines, grids

# ------------------------------------------------- tints (fills, grid cells)
GREEN_TINT = "#E8F3EC"
TEAL_TINT = "#E6F2F0"
OCHRE_TINT = "#F8F0E2"
SLATE_TINT = "#E9EEF3"
RUST_TINT = "#F6E3DF"
PANEL_BG = "#FBFCFB"

# --------------------------- clause identity shades (overview figure only)
# Six distinguishable greens; a clause keeps its color across
# rollout -> decompose -> pool so provenance is visually traceable.
CLAUSE = ["#2E7D5B", "#4C9A74", "#7FB99C", "#A9D0BD", "#3A8F83", "#62A98A"]


def use_paper_style(base_size: float = 10.0) -> None:
    """Matplotlib rcParams shared by all CRAFT data figures."""
    import matplotlib.pyplot as plt

    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": base_size,
            "axes.titlesize": base_size + 0.5,
            "axes.labelsize": base_size,
            "legend.fontsize": base_size,
            "xtick.labelsize": base_size - 0.8,
            "ytick.labelsize": base_size - 0.8,
            "axes.edgecolor": MUTED,
            "text.color": INK,
            "axes.labelcolor": INK,
            "axes.titlecolor": INK,
            "axes.titlelocation": "left",
            "axes.titlepad": 10,
            "axes.labelpad": 7,
            "axes.axisbelow": True,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "legend.frameon": False,
            "legend.handlelength": 2.5,
            "lines.linewidth": 1.4,
            "lines.markersize": 4.6,
            "axes.linewidth": 0.6,
            "axes.facecolor": "white",
            "figure.facecolor": "white",
            "grid.color": FAINT,
            "grid.linewidth": 0.55,
            "pdf.fonttype": 42,
        }
    )
