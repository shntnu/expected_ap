"""Reproduce the paper figure and tables: uv run python demo.py.

All plotted moments use the existing exact rational implementation.
The finite law and small-case checks independently score binary label vectors.
No simulation or random seed is needed: every displayed quantity is deterministic.
"""

import csv
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import pi, sqrt
from operator import index
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from moments import expected_ap, var_ap

OUTPUT = Path(__file__).resolve().parent / "build"


def enumerate_ap(length, positives):
    """Score every binary label vector by cumulative precision at positive ranks."""
    length, positives = index(length), index(positives)
    if length < 1 or not 0 <= positives <= length:
        raise ValueError("require length >= 1 and 0 <= positives <= length")
    if positives == 0:
        return Counter({Fraction(0): 1})
    counts = Counter()
    for positions in combinations(range(length), positives):
        labels = [0] * length
        for position in positions:
            labels[position] = 1
        hits = 0
        total = Fraction(0)
        for rank, label in enumerate(labels, 1):
            hits += label
            if label:
                total += Fraction(hits, rank)
        counts[total / positives] += 1
    return counts


def validate():
    cases = 0
    for length in range(1, 11):
        for positives in range(length + 1):
            counts = enumerate_ap(length, positives)
            n = sum(counts.values())
            mean = sum(value * count for value, count in counts.items()) / n
            variance = (
                sum((value - mean) ** 2 * count for value, count in counts.items()) / n
            )
            assert mean == expected_ap(length, positives), (length, positives, "mean")
            assert variance == var_ap(length, positives), (
                length,
                positives,
                "variance",
            )
            cases += 1
    for counts in [(0, 0), (1, -1), (1, 2)]:
        for function in (expected_ap, var_ap, enumerate_ap):
            try:
                function(*counts)
            except ValueError:
                pass
            else:
                raise AssertionError((function.__name__, counts, "invalid counts"))
    return cases


def write_csv(name, rows):
    with (OUTPUT / name).open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    cases = validate()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 10,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.titlelocation": "left",
            "pdf.fonttype": 42,
        }
    )
    fig = plt.figure(figsize=(7.2, 6.4), layout="constrained")
    grid = fig.add_gridspec(2, 2)
    axes = [
        fig.add_subplot(grid[0, 0]),
        fig.add_subplot(grid[0, 1]),
        fig.add_subplot(grid[1, :]),
    ]
    blue, orange = "#21617A", "#B95B32"
    lengths = sorted({int(x) * 10 for x in np.geomspace(1, 200, 40)})
    rows = []
    for regime, color in [
        ("Fixed prevalence: M/L = 0.1", blue),
        ("Fixed positives: M = 3", orange),
    ]:
        subset = []
        for length in lengths:
            positives = length // 10 if color == blue else 3
            mean = expected_ap(length, positives)
            variance = var_ap(length, positives)
            row = {
                "regime": regime,
                "L": length,
                "M": positives,
                "prevalence": positives / length,
                "mean": float(mean),
                "variance": float(variance),
                "sd": sqrt(variance),
                "mean_exact": str(mean),
                "variance_exact": str(variance),
            }
            rows.append(row)
            subset.append(row)
        axes[0].plot(
            lengths,
            [r["mean"] / r["prevalence"] for r in subset],
            color=color,
            label=regime,
        )
        axes[1].plot(lengths, [r["L"] * r["variance"] for r in subset], color=color)
    axes[0].axhline(1, color="0.55", linestyle=":")
    axes[0].set(
        xscale="log",
        xlabel="List length L",
        ylabel="E[AP] / prevalence",
        title="A  Chance exceeds prevalence",
    )
    axes[0].legend(frameon=False, fontsize=8, loc="upper left")
    axes[1].axhline(0.1 * 0.9, color=blue, linestyle=":")
    axes[1].axhline(pi**2 / 18, color=orange, linestyle=":")
    axes[1].set(
        xscale="log",
        xlabel="List length L",
        ylabel="L Var(AP)",
        title="B  Two variance limits",
    )
    axes[1].text(
        0.98,
        0.96,
        "Dotted: limiting constants",
        transform=axes[1].transAxes,
        ha="right",
        va="top",
        fontsize=8,
    )
    counts = enumerate_ap(8, 2)
    n = sum(counts.values())
    mean, sd = float(expected_ap(8, 2)), sqrt(var_ap(8, 2))
    x = [float(value) for value in sorted(counts)]
    y = [counts[value] / n for value in sorted(counts)]
    axes[2].vlines(x, 0, y, color=blue, linewidth=1.5)
    axes[2].scatter(x, y, color=blue, s=15)
    axes[2].axvspan(
        mean - sd, mean + sd, color=orange, alpha=0.12, label="Mean +/- 1 SD"
    )
    axes[2].axvline(mean, color=orange, linestyle="--", label="Mean")
    axes[2].set(
        xlabel="AP",
        ylabel="Probability mass",
        title="C  Exact law: L = 8, M = 2",
        ylim=(0, max(y) * 1.45),
    )
    axes[2].legend(frameon=False, fontsize=8, loc="upper right")
    for ax in axes:
        ax.grid(axis="y", color="0.92", linewidth=0.6)
        ax.set_axisbelow(True)
    fig.savefig(
        OUTPUT / "ap_baseline_variability.pdf",
        metadata={"CreationDate": None, "ModDate": None},
    )
    fig.savefig(OUTPUT / "ap_baseline_variability.png", dpi=180)
    plt.close(fig)
    write_csv("moments.csv", rows)
    write_csv(
        "finite_law.csv",
        [
            {
                "AP_exact": str(value),
                "AP": float(value),
                "count": counts[value],
                "probability_exact": str(Fraction(counts[value], n)),
            }
            for value in sorted(counts)
        ],
    )
    print(
        f"Exact enumeration agrees with both formulas for all {cases} cases with 1 <= L <= 10 and 0 <= M <= L (55 positive-count and 10 zero-positive cases)."
    )
    print(f"Wrote figure (PDF/PNG) and two CSV tables to {OUTPUT}")
    print(
        f"Illustrated law: {n} label vectors, {len(counts)} distinct AP values; mean={mean:.6f}, SD={sd:.6f}."
    )


if __name__ == "__main__":
    main()
