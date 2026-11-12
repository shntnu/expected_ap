"""Compare the paper's Figure 2 mAP recall under its copied null and under copairs#151's null."""
import os, sys
from pathlib import Path
import numpy as np, pandas as pd
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

S = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent / "results"
REPO = Path(os.environ.get("KALININ_MAP_REPO", "/home/user/carpenter-singh-lab/2025_kalinin_map"))
paper = pd.read_csv(REPO / "experiments/1_simulations/results/fig2_results.csv")
cp = pd.read_csv(S / "fig2_copied.csv").rename(columns={"mean_ap": "copied"})
jt = pd.read_csv(S / "fig2_joint.csv").rename(columns={"mean_ap": "joint"})
# the committed table stores features_differ as a percentage of features; the current script stores counts
key = ["n_feats", "# replicates", "n_controls", "pct"]
for d in (cp, jt):
    d["pct"] = (100 * d["features_differ"] / d["n_feats"]).round(6)
paper = paper.rename(columns={"mAP p-value": "paper_mAP", "features_differ": "pct"})
paper["pct"] = paper["pct"].astype(float)
m = cp.merge(jt.drop(columns="features_differ"), on=key).merge(paper, on=key, how="left")
assert m["paper_mAP"].notna().all(), "some cells did not match the committed table"
m["gain"] = m["joint"] - m["copied"]
print(f"{len(m)} cells; my copied-null recall vs the paper's committed mAP recall: max |diff| {np.abs(m['copied'] - m['paper_mAP']).max():.2f}, "
      f"mean |diff| {np.abs(m['copied'] - m['paper_mAP']).mean():.3f}, identical in {(m['copied'].round(2) == m['paper_mAP'].round(2)).mean():.0%} of cells")
print("\nRecall gain (joint - copied) by replicates and % differing features (mean over feature counts and control counts):")
piv = m.pivot_table(index="# replicates", columns="pct", values="gain", aggfunc="mean").round(2)
piv.columns = [f"{c:g}%" for c in piv.columns]
print(piv.to_string())
print("\nMean recall by replicates (over all cells):")
print(m.groupby("# replicates")[["copied", "joint", "mp-value", "MMD", "k-means"]].mean().round(3).to_string())
print("\nCells where mAP recall changes by more than 0.25:")
big = m[m["gain"].abs() > 0.25].sort_values("gain", ascending=False)
print(big[key + ["pct", "copied", "joint", "mp-value"]].to_string(index=False))
for col, lab in (("copied", "paper's null"), ("joint", "corrected null")):
    print(f"mAP recall vs mp-value under the {lab}: higher in {(m[col] > m['mp-value']).mean():.0%} of cells, equal in {(m[col] == m['mp-value']).mean():.0%}, lower in {(m[col] < m['mp-value']).mean():.0%}")
m.to_csv(S / "fig2_compare.csv", index=False)

# --- figure: one scatter (every cell) + the paper's own view for one slice ---
SURFACE, INK, INK2, MUTED, GRID, AXIS = "#fcfcfb", "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7"
BLUE, ORANGE = "#2a78d6", "#eb6834"
RAMP = {2: "#86b6ef", 3: "#2a78d6", 4: "#104281"}
plt.rcParams.update({"font.family": "sans-serif", "font.size": 10, "axes.edgecolor": AXIS, "axes.labelcolor": INK2,
                     "axes.titlecolor": INK, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
                     "axes.facecolor": SURFACE, "figure.facecolor": SURFACE, "xtick.color": MUTED, "ytick.color": MUTED,
                     "xtick.labelcolor": INK2, "ytick.labelcolor": INK2, "grid.color": GRID, "legend.frameon": False,
                     "legend.fontsize": 9, "legend.labelcolor": INK2, "savefig.dpi": 200})
def quiet(ax):
    for s in ("top", "right"): ax.spines[s].set_visible(False)
    ax.tick_params(length=0); ax.grid(True); ax.set_axisbelow(True)

fig, axes = plt.subplots(1, 4, figsize=(14, 4.3), layout="constrained", gridspec_kw={"width_ratios": [1.25, 1, 1, 1]})
ax = axes[0]; quiet(ax)
ax.plot([0, 1], [0, 1], color=AXIS, lw=1, zorder=0)
for n, g in m.groupby("# replicates"):
    ax.scatter(g["copied"], g["joint"], s=18, color=RAMP[n], label=f"{n} replicates", edgecolor=SURFACE, linewidth=0.6, zorder=3)
ax.set_xlabel("recall with the paper's null (one draw, copied)")
ax.set_ylabel("recall with the per-similarity null (this PR)")
ax.set_title(f"All {len(m)} Figure 2 cells")
ax.set_xlim(-0.02, 1.02); ax.set_ylim(-0.02, 1.02)
ax.legend(loc="lower right", title="replicates per perturbation", title_fontsize=9)
NF, NC = 1000, 24
for ax, n in zip(axes[1:], (2, 3, 4), strict=True):
    quiet(ax)
    g = m[(m["n_feats"] == NF) & (m["n_controls"] == NC) & (m["# replicates"] == n)].sort_values("pct")
    x = np.arange(len(g))
    ax.plot(x, g["copied"], "-o", color=ORANGE, lw=2, ms=6, mec=SURFACE, mew=1.2, label="paper's null (copied)")
    ax.plot(x, g["joint"], "-o", color=BLUE, lw=2, ms=6, mec=SURFACE, mew=1.2, label="this PR")
    ax.plot(x, g["mp-value"], "-", color=MUTED, lw=1.5, label="mp-value (paper)")
    ax.set_xticks(x, [f"{p:g}" for p in g["pct"]])
    ax.set_ylim(-0.02, 1.02); ax.set_yticks([0, 0.25, 0.5, 0.75, 1], ["0%", "25%", "50%", "75%", "100%"])
    ax.set_xlabel("% of features that differ from control")
    ax.set_title(f"{n} replicates")
handles, labels = axes[1].get_legend_handles_labels()
fig.legend(handles, labels, loc="outside upper right", ncol=3)
fig.suptitle(f"mAP recall in the paper's Figure 2 simulation. Right: {NC} controls, {NF:,} features, 100 perturbations per point", x=0.01, ha="left", fontsize=10, color=INK2, fontweight="normal")
fig.savefig(S / "fig2_compare.png")
print("wrote", S / "fig2_compare.png")
