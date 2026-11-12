# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy"]
# ///
"""How much copairs' copied mAP null costs, by group size and threshold.

copairs main builds a group's mAP null from one AP draw copied across its members
(see copairs_joint_null.py).  Two tables measure what that does to a user:

1. The p-value copairs reports for a group whose true p-value is 0.05, 0.01 or
   0.001, i.e. where the joint null's tail quantile falls in the copied null.
2. The share of real hits detected under each null, for replicates that share a
   signal direction, measured with cosine similarity on iid features.

Run:  uv run map_null_effect.py     # about three minutes
"""

from __future__ import annotations

import numpy as np

from calibration_check import _ap_from_sims, sample_marginal_ap
from copairs_joint_null import joint_map_null, replicate_group

K = 100  # negatives ranked by each replicate


def reported_p(n, true_p, null_joint, null_copied):
    """copairs main's p-value for a mAP sitting at the joint null's 1 - true_p quantile."""
    t = np.quantile(null_joint, 1 - true_p)
    return (len(null_copied) - np.searchsorted(null_copied, t - 1e-12)) / len(
        null_copied
    )


def table_reported():
    print(
        f"What copairs main reports for a given true p-value ({K} negatives per replicate)"
    )
    print(
        f"{'reps':>4} {'sd ratio':>8}  "
        + "  ".join(f"{'true ' + str(p):>12}" for p in (0.05, 0.01, 0.001))
    )
    for n in (4, 8, 20):
        members, edges = replicate_group(n, K)
        joint = np.sort(joint_map_null(members, edges, 1_000_000, 1))
        copied = np.sort(sample_marginal_ap(n - 1 + K, n - 1, 2_000_000, seed=2))
        cells = [
            f"{reported_p(n, p, joint, copied):12.4f}" for p in (0.05, 0.01, 0.001)
        ]
        print(f"{n:>4} {copied.std() / joint.std():8.2f}  " + "  ".join(cells))


def sim_signal_maps(n, strength, n_exp, d, rng):
    """Replicates share a direction with the given strength; controls are noise; cosine."""
    pos_idx = np.array([[j for j in range(n) if j != i] for i in range(n)])
    out = np.empty(n_exp)
    for b0 in range(0, n_exp, 500):
        b = min(500, n_exp - b0)
        v = rng.standard_normal((b, 1, d))
        v /= np.linalg.norm(v, axis=2, keepdims=True)
        X = rng.standard_normal((b, n + K, d)) / np.sqrt(d)
        X[:, :n] += strength * v
        X /= np.linalg.norm(X, axis=2, keepdims=True)
        S = X @ np.transpose(X, (0, 2, 1))
        pos = S[:, np.arange(n)[:, None], pos_idx]
        neg = S[:, :n, n:]
        out[b0 : b0 + b] = _ap_from_sims(
            np.concatenate([pos, neg], axis=-1), n - 1
        ).mean(axis=1)
    return out


def p_values(null_sorted, maps):
    hits = len(null_sorted) - np.searchsorted(null_sorted, maps - 1e-9)
    return (hits + 1) / (len(null_sorted) + 1)


def table_detection(n_exp=4000, d=50):
    rng = np.random.default_rng(3)
    print()
    print(
        f"Share of real hits detected, joint null / copied null ({K} controls, {d} features, {n_exp} experiments per row)"
    )
    print(
        f"{'reps':>4} {'signal':>6} {'mean mAP':>8}  {'p <= 0.05':>14}  {'p <= 0.001':>14}"
    )
    for n, strengths in [(4, (0.4, 0.6)), (8, (0.3, 0.45)), (20, (0.2, 0.3))]:
        members, edges = replicate_group(n, K)
        joint = np.sort(joint_map_null(members, edges, 400_000, 1))
        copied = np.sort(sample_marginal_ap(n - 1 + K, n - 1, 400_000, seed=2))
        for s in strengths:
            maps = sim_signal_maps(n, s, n_exp, d, rng)
            pj, pc = p_values(joint, maps), p_values(copied, maps)
            cells = [
                f"{np.mean(pj <= a):6.2f} / {np.mean(pc <= a):.2f}"
                for a in (0.05, 0.001)
            ]
            print(
                f"{n:>4} {s:>6} {maps.mean():8.3f}  "
                + "  ".join(f"{c:>14}" for c in cells)
            )


if __name__ == "__main__":
    table_reported()
    table_detection()
