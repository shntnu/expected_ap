# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy"]
# ///
"""Everything the figures and the explainer page plot, in one JSON file.

Three nulls for a group's mAP are compared throughout:

  main      copairs main: one AP draw per distinct (positives, total pairs)
            configuration, copied to every member with that configuration
            (the behaviour copairs#151 fixes)
  joint     copairs#151: one random number per ranked similarity, drawn once
            where two members share it (joint_map_null in copairs_joint_null.py)
  separate  one independent AP draw per member (the opposite shortcut)

and "plates" is the answer all three estimate: whole simulated experiments
with no effect (independent standard normal profiles, 50 features, cosine
similarity, 100 controls), each replicate ranking its own list.  Compounds
with a real effect add a random direction of a given length to every
replicate's profile, as in the explainer page.

Run:  uv run figure_data.py        # about ten minutes
Writes figure_data.json beside this file.
"""

from __future__ import annotations

import json
import time
from pathlib import Path

import numpy as np

from calibration_check import _ap_from_sims, sample_marginal_ap, sim_gram_aps
from copairs_joint_null import joint_map_null, p_value, replicate_group

K = 100  # controls ranked by each replicate
D = 50  # features per profile
GRID_STEP, GRID_MAX = 0.0005, 0.6  # the page's observed-mAP grid
STRENGTHS = [0.5 * i for i in range(13)]  # signal lengths, as on the page
SWEEP_N = [3, 4, 6, 8, 12, 16, 20]
OUT = Path(__file__).resolve().parent / "figure_data.json"
t0 = time.perf_counter()


def log(msg):
    print(f"[{time.perf_counter() - t0:6.0f} s] {msg}", flush=True)


def survival(samples, step=GRID_STEP, top=GRID_MAX):
    """P(null >= x) on the grid x = 0, step, ..., top; same tie rule as p_value."""
    s = np.sort(samples)
    grid = np.arange(0, top + step / 2, step)
    return ((len(s) - np.searchsorted(s, grid - 1e-9)) / len(s)).round(6).tolist()


def main_null(totals, N, seed):
    """copairs main's null for one group: members with equal totals share a draw."""
    rng = np.random.default_rng(seed)
    rows = {}
    out = np.zeros(N)
    for L in totals:
        if L not in rows:
            rows[L] = sample_marginal_ap(L, 3, N, seed=int(rng.integers(2**31)))
        out += rows[L]
    return out / len(totals)


def separate_null(n, N, seed):
    """n independent AP draws per sample, averaged."""
    L, M = n - 1 + K, n - 1
    return np.mean(
        [sample_marginal_ap(L, M, N, seed=seed + i) for i in range(n)], axis=0
    )


def signal_maps(n, strength, n_sim, rng, chunk=500):
    """mAPs of simulated compounds whose n replicates share a signal of this length."""
    pos_idx = np.array([[j for j in range(n) if j != i] for i in range(n)])
    out = np.empty(n_sim)
    for b0 in range(0, n_sim, chunk):
        b = min(chunk, n_sim - b0)
        v = rng.standard_normal((b, 1, D))
        v /= np.linalg.norm(v, axis=2, keepdims=True)
        X = rng.standard_normal((b, n + K, D))
        X[:, :n] += strength * v
        X /= np.linalg.norm(X, axis=2, keepdims=True)
        S = X @ np.transpose(X, (0, 2, 1))
        pos = S[:, np.arange(n)[:, None], pos_idx]
        neg = S[:, :n, n:]
        out[b0 : b0 + b] = _ap_from_sims(
            np.concatenate([pos, neg], axis=-1), n - 1
        ).mean(axis=1)
    return out


def pvals(null_sorted, x):
    hits = len(null_sorted) - np.searchsorted(null_sorted, x - 1e-9)
    return (hits + 1) / (len(null_sorted) + 1)


out = {
    "K": K,
    "features": D,
    "grid_step": GRID_STEP,
    "reported_for_true": {},
    "curves": {},
    "power": {},
    "sweep": {},
    "bookkeeping": {},
}

# 1. What copairs main reports when the truth is p, and the n = 8 curves.
TRUE_P = np.logspace(np.log10(0.5), -4, 40)
for n in (4, 8, 20):
    members, edges = replicate_group(n, K)
    joint = np.sort(joint_map_null(members, edges, 1_000_000, 1))
    copied = np.sort(sample_marginal_ap(n - 1 + K, n - 1, 2_000_000, seed=2))
    thresholds = np.quantile(joint, 1 - TRUE_P)
    reported = (len(copied) - np.searchsorted(copied, thresholds - 1e-12)) / len(copied)
    out["reported_for_true"][str(n)] = {
        "true": TRUE_P.round(6).tolist(),
        "reported": reported.round(6).tolist(),
        "sd_ratio": round(float(copied.std() / joint.std()), 4),
    }
    if n == 4:
        out["joint_sf_n4"] = survival(joint)
    if n == 8:
        plates = sim_gram_aps(n, K, D, 100_000, seed=5).mean(axis=1)
        out["curves"]["8"] = {
            "main": survival(copied),
            "joint": survival(joint),
            "separate": survival(separate_null(n, 1_000_000, 7)),
            "plates": survival(plates),
            "n_plates": 100_000,
        }
    log(f"reported-for-true n={n}: sd ratio {copied.std() / joint.std():.2f}")

# 2. Detection rates by signal strength, three nulls, three group sizes.
rng = np.random.default_rng(11)
for n in (4, 8, 20):
    members, edges = replicate_group(n, K)
    nulls = {
        "main": np.sort(sample_marginal_ap(n - 1 + K, n - 1, 400_000, seed=21)),
        "joint": np.sort(joint_map_null(members, edges, 400_000, 22)),
        "plates": np.sort(sim_gram_aps(n, K, D, 40_000, seed=23).mean(axis=1)),
    }
    rows = []
    for s in STRENGTHS:
        maps = signal_maps(n, s, 6000, rng)
        row = {"strength": s, "median_map": float(np.median(maps)), "n_sim": 6000}
        for key, null in nulls.items():
            p = pvals(null, maps)
            row[key] = float(np.mean(p <= 0.05))
            row[key + "_01"] = float(np.mean(p <= 0.01))
            row[key + "_001"] = float(np.mean(p <= 0.001))
        rows.append(row)
    out["power"][str(n)] = rows
    log(
        f"power n={n}: at strength 2.0 joint {rows[4]['joint']:.3f} main {rows[4]['main']:.3f}"
    )

# 3. Spread and false-positive rate of the joint null by replicate count.
for n in SWEEP_N:
    members, edges = replicate_group(n, K)
    joint = np.sort(joint_map_null(members, edges, 400_000, 31))
    plates = sim_gram_aps(n, K, D, 40_000, seed=32).mean(axis=1)
    p = pvals(joint, plates)
    out["sweep"][str(n)] = {
        "sd_joint": float(joint.std()),
        "fpr_joint_05": float(np.mean(p <= 0.05)),
        "fpr_joint_01": float(np.mean(p <= 0.01)),
        "n_plates": 40_000,
    }
    log(f"sweep n={n}: joint sd {joint.std():.4f} fpr {np.mean(p <= 0.05):.4f}")

# 4. Bookkeeping: the four-wells APs under every control-count pattern.
APS = [0.2448107448107448, 0.2125, 0.11492673992673992, 0.19555555555555557]
score = float(np.mean(APS))
patterns = [
    [100] * 4,
    [100, 100, 100, 99],
    [100, 100, 99, 99],
    [100, 100, 99, 98],
    [100, 99, 98, 97],
]
rows = []
for neg in patterns:
    totals = [3 + k for k in neg]
    members, edges = replicate_group(4, neg)
    rows.append(
        {
            "controls": neg,
            "totals": totals,
            "main_p": p_value(main_null(totals, 200_000, 41), score),
            "joint_p": p_value(joint_map_null(members, edges, 400_000, 42), score),
        }
    )
    log(
        f"bookkeeping {neg}: main {rows[-1]['main_p']:.4f} joint {rows[-1]['joint_p']:.4f}"
    )
out["bookkeeping"] = {"aps": APS, "map": score, "rows": rows}
out["example_p_joint"] = rows[0]["joint_p"]

OUT.write_text(json.dumps(out))
log(f"wrote {OUT} ({OUT.stat().st_size // 1024} KB)")
