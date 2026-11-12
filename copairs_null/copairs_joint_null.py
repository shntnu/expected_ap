# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy", "scipy", "pandas", "duckdb>=1.4.4", "tqdm", "statsmodels"]
# ///
"""Joint structure-free null for copairs' mAP p-value, and the checks that it is right.

copairs builds the mAP null of a group by drawing one AP sample per distinct
(n_pos_pairs, n_total_pairs) configuration and averaging the rows its members point
at.  Members with matching counts point at the same row, so the "average" is one
draw copied n times and the null never narrows as replicates are added.

The fix changes the unit of randomness from the binary list to the pair.  Every pair
gets one uniform random number; a pair inside the group (replicate i with replicate j)
puts that same number into both members' lists; each member's AP then falls out of
its own sorted list.  The coupling between members is automatic, and the only inputs
are bookkeeping copairs already has: how many negatives each member ranks and which
positive pairs lie inside the group.  No similarity values are used, so the null is
as data-free as the current one.

The marginal of each member is unchanged (a uniformly random placement of its
positives), so per-profile AP p-values are untouched; only the mAP null changes.

Run:
    uv run copairs_joint_null.py            # all checks, about a minute
    uv run copairs_joint_null.py --quick    # moments and KS only
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

import numpy as np

from ap_moments import (
    cov_ap,
    cov_ap_hetero,
    expected_ap,
    map_null_sd,
    var_ap,
)
from calibration_check import sample_marginal_ap, sim_gram_aps, sim_shared_only_aps

Member = tuple[int, int]  # (M_i, K_i): positives and negatives ranked by member i
Edge = tuple[
    int, int, int
]  # (i, j, label): a pair inside the group, label 1 = positive


# ----------------------------------------------------------------------------------
# the sampler
# ----------------------------------------------------------------------------------


def replicate_group(n: int, negatives) -> tuple[list[Member], list[Edge]]:
    """The standard copairs case: n replicates, each one's positives are the other n-1.

    `negatives` is one count for all members or a sequence of per-member counts.
    """
    K = [int(negatives)] * n if np.isscalar(negatives) else [int(k) for k in negatives]
    if len(K) != n:
        raise ValueError("need one negative count per member")
    members = [(n - 1, k) for k in K]
    edges = [(i, j, 1) for i in range(n) for j in range(i + 1, n)]
    return members, edges


def _signature_seed(seed: int, members, edges) -> int:
    """A seed that is a pure function of (master seed, group signature).

    Distinct signatures must not share a seed: copairs main reuses one seed across
    configurations, which makes their early samples overlap.
    """
    key = repr((int(seed), tuple(sorted(members)), tuple(sorted(edges))))
    return int.from_bytes(
        hashlib.blake2b(key.encode(), digest_size=8).digest(), "little"
    )


def joint_ap_null(
    members: list[Member],
    edges: list[Edge],
    null_size: int,
    seed: int,
    chunk: int = 200_000,
) -> np.ndarray:
    """Samples of the group's APs under the joint structure-free null: (null_size, n).

    Model: every pair's similarity is an iid continuous random number.  A pair inside
    the group (an edge) is ONE number present in both members' lists.  Everything
    else a member ranks (positives outside the group, negatives) is private to it.

    Per member: the values it shares, plus its private positives, are drawn explicitly
    and sorted; its private negatives are then dropped into the gaps between those
    sorted values with one multinomial draw, so the cost does not depend on how many
    negatives it ranks.  Ranks follow, and AP = (1/M) sum_t t / rank_t.
    """
    n = len(members)
    rng = np.random.default_rng(_signature_seed(seed, members, edges))
    incident: list[list[tuple[int, int]]] = [[] for _ in range(n)]
    for e, (i, j, label) in enumerate(edges):
        if i == j or not (0 <= i < n and 0 <= j < n) or label not in (0, 1):
            raise ValueError(f"bad edge {(i, j, label)}")
        incident[i].append((e, label))
        incident[j].append((e, label))
    plan = []
    for i, (M, K) in enumerate(members):
        shared_pos = sum(label for _, label in incident[i])
        shared_neg = len(incident[i]) - shared_pos
        private_pos, private_neg = M - shared_pos, K - shared_neg
        if M < 1 or private_pos < 0 or private_neg < 0:
            raise ValueError(
                f"member {i}: (M, K) = {(M, K)} inconsistent with its edges"
            )
        labels = np.array(
            [label for _, label in incident[i]] + [1] * private_pos, dtype=np.int64
        )
        plan.append(
            (
                np.array([e for e, _ in incident[i]], dtype=np.int64),
                labels,
                M,
                private_neg,
            )
        )

    out = np.empty((null_size, n))
    done = 0
    while done < null_size:
        b = min(chunk, null_size - done)
        U = rng.random((b, max(len(edges), 1)))  # one number per pair inside the group
        for i, (edge_ix, labels, M, private_neg) in enumerate(plan):
            n_private_pos = len(labels) - len(edge_ix)
            vals = np.concatenate(
                [U[:, edge_ix], rng.random((b, n_private_pos))], axis=1
            )
            order = np.argsort(-vals, axis=1)
            s = np.take_along_axis(vals, order, axis=1)  # descending explicit values
            lab = labels[order]  # (b, E)
            # private negatives fall into the E + 1 gaps between the sorted values
            gaps = -np.diff(
                np.concatenate([np.ones((b, 1)), s, np.zeros((b, 1))], axis=1), axis=1
            )
            counts = (
                rng.multinomial(private_neg, gaps)
                if private_neg
                else np.zeros_like(gaps, dtype=np.int64)
            )
            above = np.cumsum(counts, axis=1)[:, :-1]  # negatives above explicit item t
            rank = np.arange(1, lab.shape[1] + 1) + above
            t = np.cumsum(lab, axis=1)  # index among positives, valid where lab == 1
            out[done : done + b, i] = ((t / rank) * lab).sum(axis=1) / M
        done += b
    return out


def joint_map_null(members, edges, null_size, seed, **kw) -> np.ndarray:
    return joint_ap_null(members, edges, null_size, seed, **kw).mean(axis=1)


def p_value(null: np.ndarray, score: float, tol: float = 1e-9) -> float:
    """(1 + #{null >= score}) / (N + 1); the tolerance keeps exact ties on the >= side."""
    return (1 + int(np.count_nonzero(null >= score - tol))) / (len(null) + 1)


# ----------------------------------------------------------------------------------
# checks
# ----------------------------------------------------------------------------------


def _z_mean(x, target):
    return (x.mean() - target) / (x.std() / np.sqrt(len(x)))


def _z_var(x, target):
    """Sample variance against a target, in standard errors (large-N approximation)."""
    m4 = np.mean((x - x.mean()) ** 4)
    return (x.var() - target) / np.sqrt((m4 - x.var() ** 2) / len(x))


def _z_cov(x, y, target):
    """Sample covariance against a target, in standard errors."""
    prod = (x - x.mean()) * (y - y.mean())
    return (prod.mean() - target) / (prod.std() / np.sqrt(len(x)))


def check_moments(n, K, N, seed):
    """Marginals against the Lean-proven mean and variance, joint against cov_ap."""
    members, edges = replicate_group(n, K)
    A = joint_ap_null(members, edges, N, seed)
    M, L = n - 1, n - 1 + K
    mu, v, c = float(expected_ap(L, M)), float(var_ap(L, M)), cov_ap(L, M, exact=False)
    sd_map = map_null_sd([(L, M)] * n)
    ap0 = A[:, 0]
    z_mu, z_v, z_c = _z_mean(ap0, mu), _z_var(ap0, v), _z_cov(A[:, 0], A[:, 1], c)
    m = A.mean(axis=1)
    print(
        f"  n={n:>2} K={K:>4}  E[AP] {ap0.mean():.5f} vs {mu:.5f} (z={z_mu:+.2f})"
        f"  Var(AP) {ap0.var():.6f} vs {v:.6f} (z={z_v:+.2f})"
        f"  Cov {np.cov(A[:, 0], A[:, 1])[0, 1]:.6f} vs {c:.6f} (z={z_c:+.2f})"
        f"  sd(mAP) {m.std():.5f} vs {sd_map:.5f} ({m.std() / sd_map:.4f}x)"
    )
    return max(abs(z_mu), abs(z_v), abs(z_c)) < 4 and abs(m.std() / sd_map - 1) < 0.01


def check_hetero(N, seed):
    """One member sees one control fewer: covariance against cov_ap_hetero."""
    members, edges = replicate_group(4, [100, 100, 100, 99])
    A = joint_ap_null(members, edges, N, seed)
    c_th = cov_ap_hetero(103, 3, 102, 3, exact=False)
    z_c = _z_cov(A[:, 0], A[:, 3], c_th)
    sd_th = map_null_sd([(103, 3)] * 3 + [(102, 3)])
    sd_meas = A.mean(axis=1).std()
    print(
        f"  members (3,103)x3 + (3,102): Cov(AP_0, AP_3) {np.cov(A[:, 0], A[:, 3])[0, 1]:.6f}"
        f" vs cov_ap_hetero {c_th:.6f} (z={z_c:+.2f});"
        f" sd(mAP) {sd_meas:.5f} vs map_null_sd {sd_th:.5f} ({sd_meas / sd_th:.4f}x)"
    )
    return abs(z_c) < 4 and abs(sd_meas / sd_th - 1) < 0.01


def check_distribution(n, K, N, seed):
    """Whole distribution: KS against the explicit simulator of the same model."""
    from scipy.stats import ks_2samp

    members, edges = replicate_group(n, K)
    fast = joint_map_null(members, edges, N, seed)
    slow = sim_shared_only_aps(n, K, N, seed=seed + 1).mean(axis=1)
    ks = ks_2samp(fast, slow)
    q = [0.5, 0.9, 0.95, 0.99, 0.999]
    qf, qs = np.quantile(fast, q), np.quantile(slow, q)
    print(
        f"  n={n:>2} K={K:>4}  KS D={ks.statistic:.4f} p={ks.pvalue:.3f}   quantiles 50/90/95/99/99.9:"
        f"  shortcut {np.array2string(qf, precision=4)}  explicit {np.array2string(qs, precision=4)}"
    )
    return ks.pvalue > 0.01


def explicit_ap_null(members, edges, N, seed, chunk=50_000):
    """Brute force for any graph: draw every similarity explicitly, shared where the pair
    is inside the group, and sort each member's full list.  (N, n) APs."""
    rng = np.random.default_rng(seed)
    n = len(members)
    out = np.empty((N, n))
    done = 0
    while done < N:
        b = min(chunk, N - done)
        U = rng.random((b, len(edges)))
        for i, (M, K) in enumerate(members):
            mine = [(e, lab) for e, (a, c, lab) in enumerate(edges) if i in (a, c)]
            lab_shared = np.array([lab for _, lab in mine], dtype=float)
            n_priv_pos = M - int(lab_shared.sum())
            n_priv_neg = K - (len(mine) - int(lab_shared.sum()))
            vals = np.concatenate(
                [U[:, [e for e, _ in mine]], rng.random((b, n_priv_pos + n_priv_neg))],
                axis=1,
            )
            labels = np.concatenate(
                [lab_shared, np.ones(n_priv_pos), np.zeros(n_priv_neg)]
            )
            out[done : done + b, i] = _ap_labeled(vals, labels, M)
        done += b
    return out


def _ap_labeled(vals, labels, M):
    order = np.argsort(-vals, axis=1)
    rel = labels[order]
    precision = np.cumsum(rel, axis=1) / np.arange(1, vals.shape[1] + 1)
    return (precision * rel).sum(axis=1) / M


def check_graph(N, seed):
    """Non-complete graphs, private positives and a shared negative, against brute force."""
    from scipy.stats import ks_2samp

    cases = {
        "4-cycle, one private positive each": (
            [(3, 50), (3, 60), (3, 50), (3, 60)],
            [(0, 1, 1), (1, 2, 1), (2, 3, 1), (3, 0, 1)],
        ),
        "path of 5, shared negative 0-4": (
            [(1, 31), (2, 40), (2, 40), (2, 40), (1, 31)],
            [(0, 1, 1), (1, 2, 1), (2, 3, 1), (3, 4, 1), (0, 4, 0)],
        ),
    }
    ok = True
    for name, (members, edges) in cases.items():
        fast = joint_ap_null(members, edges, N, seed)
        slow = explicit_ap_null(members, edges, N, seed + 1)
        ks = ks_2samp(fast.mean(axis=1), slow.mean(axis=1))
        per = max(
            ks_2samp(fast[:, i], slow[:, i]).statistic for i in range(len(members))
        )
        z = max(
            abs(_z_mean(fast[:, i], slow[:, i].mean())) for i in range(len(members))
        )
        print(
            f"  {name:<36} mAP KS D={ks.statistic:.4f} p={ks.pvalue:.3f};"
            f" worst member KS D={per:.4f}, mean z={z:.2f};"
            f" sd(mAP) {fast.mean(axis=1).std():.5f} vs {slow.mean(axis=1).std():.5f}"
        )
        ok &= ks.pvalue > 0.01 and per < 0.01
    return ok


def check_atom(N, seed):
    """Two members, four controls, perfect retrieval: P(mAP = 1) = E[p^8] = 1/9."""
    members, edges = replicate_group(2, 4)
    m = joint_map_null(members, edges, N, seed)
    rate = np.mean(m >= 1 - 1e-12)
    se = np.sqrt((1 / 9) * (8 / 9) / N)
    print(
        f"  P(both APs = 1) = {rate:.5f} vs 1/9 = {1 / 9:.5f} ({(rate - 1 / 9) / se:+.2f} se)"
    )
    print(
        "  (the cosine-circle fixture in copairs_null_evidence.json gives 2/15; that is a different model)"
    )
    return abs(rate - 1 / 9) < 4 * se


def check_singleton(N, seed):
    """A group of one must follow copairs' existing per-AP null exactly."""
    from scipy.stats import ks_2samp

    members, edges = [(3, 100)], []
    joint = joint_map_null(members, edges, N, seed)
    exact = sample_marginal_ap(103, 3, N, seed=seed + 1)
    ks = ks_2samp(joint, exact)
    line = f"  n=1 (3 positives among 103): KS vs the exact AP law D={ks.statistic:.4f} p={ks.pvalue:.3f}"
    try:
        sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "copairs" / "src"))
        from copairs.compute import random_ap

        cp = random_ap(N, 3, 103, seed=seed + 2).astype(float)
        ks2 = ks_2samp(joint, cp)
        line += (
            f"; vs copairs.compute.random_ap D={ks2.statistic:.4f} p={ks2.pvalue:.3f}"
        )
        ok = ks.pvalue > 0.01 and ks2.pvalue > 0.01
    except ImportError as exc:  # no copairs checkout next to this repo
        line += f" (copairs not importable: {exc})"
        ok = ks.pvalue > 0.01
    print(line)
    return ok


def check_fixture(N, seed):
    """The four-wells example from copairs_null_evidence.json, and the bookkeeping case."""
    path = Path(__file__).resolve().parent / "copairs_null_evidence.json"
    if not path.exists():
        print("  copairs_null_evidence.json missing; skipped")
        return None
    ev = json.loads(path.read_text())
    aps = np.array(ev["four_wells"]["manual_APs"])
    score = float(aps.mean())
    truth = ev["four_wells"]["empirical_p_value"]
    cp = ev["versions"]["baseline"]["concrete"]["four_wells"]["p_value"]
    members, edges = replicate_group(4, 100)
    p_joint = p_value(joint_map_null(members, edges, N, seed), score)
    members2, edges2 = replicate_group(4, [100, 100, 100, 99])
    p_book = p_value(joint_map_null(members2, edges2, N, seed), score)
    print(
        f"  four wells, mAP {score:.4f}: joint null p = {p_joint:.4f};"
        f" whole-experiment re-run {truth:.4f}; copairs {cp:.4f}"
    )
    print(
        f"  same APs, fourth well one control fewer: joint null p = {p_book:.4f}"
        f" (copairs swings 0.011 to 0.060 on this bookkeeping change)"
    )
    return abs(p_joint - truth) < 0.005 and abs(p_book - p_joint) < 0.003


def check_fpr(n, K, N_null, N_exp, seed, n_feat=50):
    """False-positive rate of the joint-null p-value on two kinds of true-null data."""
    members, edges = replicate_group(n, K)
    null = np.sort(joint_map_null(members, edges, N_null, seed))
    rows = []
    for name, maps in [
        (
            "model-matched (shared pairs only)",
            sim_shared_only_aps(n, K, N_exp, seed=seed + 11).mean(axis=1),
        ),
        (
            f"cosine on {n_feat} iid features",
            sim_gram_aps(n, K, n_feat, N_exp, seed=seed + 12).mean(axis=1),
        ),
    ]:
        hits = len(null) - np.searchsorted(null, maps - 1e-9, side="left")
        p = (hits + 1) / (len(null) + 1)
        f05, f01 = np.mean(p <= 0.05), np.mean(p <= 0.01)
        rows.append((f05, f01))
        print(
            f"  n={n:>2} K={K:>4}  {name:<36} FPR at 0.05: {f05:.4f}   at 0.01: {f01:.4f}"
        )
    se05, se01 = np.sqrt(0.05 * 0.95 / N_exp), np.sqrt(0.01 * 0.99 / N_exp)
    f05, f01 = rows[0]
    return abs(f05 - 0.05) < 4 * se05 and abs(f01 - 0.01) < 4 * se01


def check_timing(N, seed):
    for n, K in [(4, 100), (20, 100), (4, 10_000), (4, 1_000_000)]:
        members, edges = replicate_group(n, K)
        t0 = time.perf_counter()
        joint_map_null(members, edges, N, seed)
        dt = time.perf_counter() - t0
        print(f"  n={n:>2} K={K:>8}  {N:,} samples: {dt:.2f} s")
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--seed", type=int, default=20261009)
    args = ap.parse_args()
    N = 400_000
    results = {}
    print(
        "Moments against the closed forms (E[AP], Var(AP) are Lean-proven; Cov is the tier-2 model)"
    )
    results["moments"] = all(
        [
            check_moments(3, 20, N, args.seed),
            check_moments(4, 100, N, args.seed),
            check_moments(8, 100, N, args.seed),
            check_moments(20, 100, N, args.seed),
        ]
    )
    print("Heterogeneous configurations")
    results["hetero"] = check_hetero(N, args.seed)
    print("Whole distribution against the explicit simulator (no multinomial shortcut)")
    results["distribution"] = all(
        [
            check_distribution(4, 100, 200_000, args.seed),
            check_distribution(3, 20, 200_000, args.seed),
        ]
    )
    print("Non-complete graphs against brute force")
    results["graph"] = check_graph(200_000, args.seed)
    print("Closed-form atom")
    results["atom"] = check_atom(N, args.seed)
    print("Singleton group")
    results["singleton"] = check_singleton(N, args.seed)
    if not args.quick:
        print("The four-wells fixture")
        results["fixture"] = check_fixture(200_000, args.seed)
        print("False-positive rates (30,000 true-null experiments each)")
        results["fpr"] = all(
            [
                check_fpr(4, 100, 200_000, 30_000, args.seed),
                check_fpr(8, 100, 200_000, 30_000, args.seed),
                check_fpr(20, 100, 200_000, 30_000, args.seed),
            ]
        )
        print("Timing")
        results["timing"] = check_timing(100_000, args.seed)
    print()
    for k, ok in results.items():
        print(f"{'SKIP' if ok is None else 'PASS' if ok else 'FAIL'}  {k}")
    sys.exit(0 if all(ok is not False for ok in results.values()) else 1)


if __name__ == "__main__":
    main()
