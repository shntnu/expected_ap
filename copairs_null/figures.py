# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy", "matplotlib"]
# ///
"""Three figures for copairs#151, drawn from figure_data.json.

  map_null_curves.png        the p-value each null reports for an observed mAP
  map_null_consequences.png  what copairs reports when the truth is p, and
                             the share of real hits each null detects
  map_null_bookkeeping.png   the same four APs under five control-count patterns

Run:  uv run figures.py   (after figure_data.py)
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = Path(__file__).resolve().parent
DATA = json.loads((HERE / "figure_data.json").read_text())
OUT = HERE / "figures"
OUT.mkdir(exist_ok=True)

SURFACE, INK, INK2, MUTED, GRID, AXIS = (
    "#fcfcfb",
    "#0b0b0b",
    "#52514e",
    "#898781",
    "#e1e0d9",
    "#c3c2b7",
)
BLUE, ORANGE, AQUA = (
    "#2a78d6",
    "#eb6834",
    "#1baf7a",
)  # this PR, copairs main, separate draws
ORANGE_RAMP = {
    "4": "#f0a070",
    "8": "#d95926",
    "20": "#8a3412",
}  # replicates, light to dark
BAND = dict(color=BLUE, lw=7, alpha=0.22, solid_capstyle="round", zorder=1)
LINE = dict(lw=2, solid_joinstyle="round", solid_capstyle="round", zorder=3)
DOT = dict(ms=7, mec=SURFACE, mew=1.5)

plt.rcParams.update(
    {
        "font.family": "sans-serif",
        "font.size": 10,
        "axes.edgecolor": AXIS,
        "axes.labelcolor": INK2,
        "axes.titlecolor": INK,
        "axes.titlesize": 10.5,
        "axes.titleweight": "bold",
        "axes.titlelocation": "left",
        "axes.facecolor": SURFACE,
        "figure.facecolor": SURFACE,
        "xtick.color": MUTED,
        "ytick.color": MUTED,
        "xtick.labelcolor": INK2,
        "ytick.labelcolor": INK2,
        "grid.color": GRID,
        "grid.linewidth": 1,
        "legend.frameon": False,
        "legend.fontsize": 9,
        "legend.labelcolor": INK2,
        "savefig.dpi": 200,
    }
)


def quiet(ax):
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    ax.tick_params(length=0)
    ax.grid(True, axis="y")
    ax.set_axisbelow(True)


def fmt_p(p):
    return f"{p:.3f}" if p >= 0.01 else f"{p:.4f}" if p >= 0.001 else f"{p:.0e}"


# --- Figure 1: the curves at 8 replicates -----------------------------------------
c = DATA["curves"]["8"]
x = np.arange(len(c["main"])) * DATA["grid_step"]
fig, ax = plt.subplots(figsize=(8, 4.4), layout="constrained")
quiet(ax)
ax.set_yscale("log")
ax.set_xlim(0, 0.5)
ax.set_ylim(1e-4, 1.05)
ax.set_yticks([1, 0.1, 0.01, 0.001, 0.0001], ["1", "0.1", "0.01", "0.001", "0.0001"])
ax.axhline(0.05, color=AXIS, lw=1, zorder=0)
ax.text(0.499, 0.05, "0.05 ", color=MUTED, fontsize=8.5, ha="right", va="bottom")


def curve(key, **kw):
    y = np.array(c[key])
    keep = (y >= 1e-4) & (x <= 0.5)
    ax.plot(x[keep], y[keep], **kw)


curve(
    "plates", label="re-running the whole experiment (100,000 no-effect plates)", **BAND
)
curve("separate", label="separate draws, one per replicate", color=AQUA, **LINE)
curve(
    "main",
    label="copairs main: one draw, copied to every replicate",
    color=ORANGE,
    **LINE,
)
curve("joint", label="this PR: one draw per pair", color=BLUE, **LINE)

# the worked example from the PR body: a compound truly at p = 0.001
joint, main = np.array(c["joint"]), np.array(c["main"])
i = int(np.argmax(joint <= 0.001))
xs, rep = x[i], main[i]
ax.plot([xs, xs], [0.001, rep], color=INK2, lw=1, zorder=2)
ax.plot([xs], [0.001], "o", color=BLUE, **DOT)
ax.plot([xs], [rep], "o", color=ORANGE, **DOT)
ax.annotate(
    f"same compound, mAP {xs:.2f}\nthis PR: p = 0.001\ncopairs main: p = {rep:.3f}",
    xy=(xs, np.sqrt(0.001 * rep)),
    xytext=(xs + 0.05, 0.0005),
    color=INK,
    fontsize=9,
    va="center",
    arrowprops=dict(arrowstyle="-", color=INK2, lw=1, shrinkA=0, shrinkB=4),
)
ax.set_xlabel("observed mAP of the group")
ax.set_ylabel("p-value the null reports (log scale)")
ax.set_title(
    "8 replicates against 100 controls: the p-value each null gives an observed mAP"
)
ax.legend(loc="upper right")
fig.savefig(OUT / "map_null_curves.png")
plt.close(fig)

# --- Figure 2: consequences -----------------------------------------------------------
fig, axes = plt.subplots(1, 3, figsize=(13, 4.2), layout="constrained")

ax = axes[0]
quiet(ax)
ax.grid(True, axis="x")
ax.set_xscale("log")
ax.set_yscale("log")
ax.set_xlim(1e-4, 0.5)
ax.set_ylim(1e-4, 1)
ticks = [0.0001, 0.001, 0.01, 0.1]
ax.set_xticks(ticks, ["0.0001", "0.001", "0.01", "0.1"])
ax.set_yticks(ticks + [1], ["0.0001", "0.001", "0.01", "0.1", "1"])
ax.plot([1e-4, 0.5], [1e-4, 0.5], color=AXIS, lw=1, zorder=0)
ax.text(
    0.3,
    0.3,
    "no error ",
    color=MUTED,
    fontsize=8.5,
    ha="right",
    va="bottom",
    rotation=38,
)
for n in ("4", "8", "20"):
    r = DATA["reported_for_true"][n]
    ax.plot(
        r["true"], r["reported"], color=ORANGE_RAMP[n], label=f"{n} replicates", **LINE
    )
    ax.text(
        1.15e-4,
        r["reported"][-1],
        f"{n} ",
        color=INK2,
        fontsize=8.5,
        ha="left",
        va="bottom",
    )
ax.set_xlabel("the compound's true p-value")
ax.set_ylabel("p-value copairs main reports")
ax.set_title("What copairs main reports")
ax.legend(loc="lower right", title="replicates per compound", title_fontsize=9)

for ax, n in zip(axes[1:], ("8", "20"), strict=True):
    quiet(ax)
    rows = [r for r in DATA["power"][n] if r["median_map"] <= 0.72]
    xs = [r["median_map"] for r in rows]
    ax.set_xlim(0, 0.7)
    ax.set_ylim(0, 1.02)
    ax.set_yticks([0, 0.25, 0.5, 0.75, 1], ["0%", "25%", "50%", "75%", "100%"])
    ax.axhline(0.05, color=AXIS, lw=1, zorder=0)
    ax.text(
        0.698, 0.05, "alpha 0.05 ", color=MUTED, fontsize=8.5, ha="right", va="bottom"
    )
    ax.plot(
        xs,
        [r["plates"] for r in rows],
        label="re-running the experiment",
        **BAND,
    )
    for key, col, lab in (("main", ORANGE, "copairs main"), ("joint", BLUE, "this PR")):
        ax.plot(xs, [r[key] for r in rows], "-o", color=col, label=lab, **LINE, **DOT)
    ax.set_xlabel("typical mAP of the compound (effect size)")
    ax.set_ylabel("share of compounds called active at alpha 0.05")
    ax.set_title(f"{n} replicates: real hits detected")
    ax.legend(loc="center right", bbox_to_anchor=(1.0, 0.45))
fig.savefig(OUT / "map_null_consequences.png")
plt.close(fig)

# --- Figure 3: bookkeeping ------------------------------------------------------------
b = DATA["bookkeeping"]
rows = b["rows"]
fig, ax = plt.subplots(figsize=(8, 3.4), layout="constrained")
quiet(ax)
ax.grid(False)
ax.grid(True, axis="x")
ys = np.arange(len(rows))[::-1]
ax.set_xlim(0, 0.07)
ax.set_ylim(-0.6, len(rows) - 0.4)
ax.set_yticks(ys, [" / ".join(str(k) for k in r["controls"]) for r in rows])
ax.axvline(0.05, color=INK2, lw=1, zorder=0)
ax.text(0.0505, -0.55, "0.05", color=INK2, fontsize=8.5, ha="left", va="bottom")
for y, r in zip(ys, rows, strict=True):
    ax.plot([r["joint_p"], r["main_p"]], [y, y], color=AXIS, lw=1, zorder=1)
    ax.plot([r["main_p"]], [y], "o", color=ORANGE, **DOT)
    ax.text(
        r["main_p"],
        y + 0.22,
        fmt_p(r["main_p"]),
        color=INK2,
        fontsize=8.5,
        ha="center",
        va="bottom",
    )
    ax.plot([r["joint_p"]], [y], "o", color=BLUE, **DOT)
ax.plot([], [], "o", color=ORANGE, label="copairs main", **DOT)
ax.plot(
    [],
    [],
    "o",
    color=BLUE,
    label=f"this PR ({fmt_p(min(r['joint_p'] for r in rows))} to {fmt_p(max(r['joint_p'] for r in rows))})",
    **DOT,
)
ax.set_xlabel("p-value")
ax.set_ylabel("controls ranked by each of the four wells")
ax.set_title(f"Same four APs (mAP {b['map']:.3f}), five control-count patterns")
ax.legend(loc="upper left")
fig.savefig(OUT / "map_null_bookkeeping.png")
plt.close(fig)
print("wrote", *sorted(p.name for p in OUT.glob("*.png")))
