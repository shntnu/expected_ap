# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy"]
# ///
"""Calibration test for the shape-corrected mAP null, mirroring calibration_check.py.

False-positive rate on TRUE-NULL data at nominal 0.05 and 0.01 for:
  (a) uncorrected independent null      (what copairs uses)
  (b) variance-only design-effect null  (prior work: fixes 0.05, misses 0.01)
  (c) shape-corrected null              (this work: match mu, sd, skew)
plus oracle references (measured-sd, measured-shape) that bound any variance-only /
any three-moment fix.

Two true-null generators, reusing calibration_check.py's simulators:
  * shared-only : the tier-2 model itself (my moments are EXACT here) -> clean test of
    whether matching three moments is enough.
  * gram        : the realistic iid-feature cosine replicate retrieval -> the residual
    Gram coupling lies outside the tier-2 model, so this is the honest realistic test.

>= 100k true-null observations per config (0.01 FPR se ~ 3e-4).
"""

from __future__ import annotations

import argparse
import math
import time

import numpy as np

from calibration_check import sample_marginal_ap, sim_gram_aps
from map_shape import (
    cf_sf,
    gamma3_null_sample,
    map_shape,
    mc_sf,
    norm_sf,
    sim_shared_only,
)

CONFIGS = [
    (3, 20),
    (4, 20),
    (6, 20),
    (10, 20),
    (4, 100),
    (10, 100),
    (20, 100),
    (30, 50),
    (50, 100),
]

METHODS = [
    "indep_mc",
    "de_normal",
    "de_mc",
    "cf",
    "gamma_mc",
    "oracle_sd",
    "oracle_shape",
]


def resample_mean_null(pool, n, n_null, rng):
    out = np.empty(n_null)
    step = max(1, 20_000_000 // n)
    done = 0
    while done < n_null:
        b = min(step, n_null - done)
        out[done : done + b] = pool[rng.integers(0, pool.size, size=(b, n))].mean(1)
        done += b
    return out


def rescaled(src, mu, target_sd):
    return np.sort(mu + (src - src.mean()) * (target_sd / src.std(ddof=1)))


def emp_moments(x):
    m = x.mean()
    d = x - m
    v = (d * d).mean()
    sk = (d**3).mean() / v**1.5
    return m, math.sqrt(v), sk


def fpr_row(obs, mu, sd_ind, sd_de, skew_model, pool, n, meas, rng, alphas):
    """Return {(method, alpha): fpr}.  meas = (mu_meas, sd_meas, skew_meas)."""
    Z = resample_mean_null(pool, n, N_NULL, rng)
    nulls = {
        "indep_mc": rescaled(Z, mu, sd_ind),
        "de_mc": rescaled(Z, mu, sd_de),
        "oracle_sd": rescaled(Z, mu, meas[1]),
    }
    p = {}
    p["indep_mc"] = mc_sf(obs, nulls["indep_mc"])
    p["de_mc"] = mc_sf(obs, nulls["de_mc"])
    p["oracle_sd"] = mc_sf(obs, nulls["oracle_sd"])
    p["de_normal"] = norm_sf((obs - mu) / sd_de)
    p["cf"] = cf_sf(obs, mu, sd_de, skew_model)
    gsamp = gamma3_null_sample(mu, sd_de, skew_model, N_NULL, seed=98765)
    p["gamma_mc"] = mc_sf(obs, gsamp)
    gora = gamma3_null_sample(meas[0], meas[1], meas[2], N_NULL, seed=54321)
    p["oracle_shape"] = mc_sf(obs, gora)
    return {(m, a): float((p[m] < a).mean()) for m in METHODS for a in alphas}


def run(generator, label, args):
    print("\n" + "#" * 96)
    print(f"# TRUE-NULL GENERATOR: {label}")
    print("#" * 96)
    alphas = (0.05, 0.01)
    diag = []
    results = {}
    for n_rep, n_ctl in CONFIGS:
        t0 = time.time()
        M, L = n_rep - 1, n_rep - 1 + n_ctl
        n = n_rep
        sh = map_shape(L, M, n)
        mu, sd_de, skew_model = sh["mu"], sh["sd"], sh["skew"]
        sd_ind = math.sqrt(sh["mu2"] / n)

        if generator == "gram":
            A = sim_gram_aps(n_rep, n_ctl, args.n_feat, args.n_sim, seed=1000 + n_rep)
        else:
            A = sim_shared_only(n_rep, n_ctl, args.n_sim, seed=1000 + n_rep)
        obs = A.mean(axis=1)
        meas = emp_moments(obs)

        pool = sample_marginal_ap(L, M, args.pool, seed=2000 + n_rep)
        rng = np.random.default_rng(3000 + n_rep)
        results[(n_rep, n_ctl)] = fpr_row(
            obs, mu, sd_ind, sd_de, skew_model, pool, n, meas, rng, alphas
        )
        diag.append(
            dict(
                n_rep=n_rep,
                n_ctl=n_ctl,
                mu=mu,
                mu_m=meas[0],
                sd_de=sd_de,
                sd_m=meas[1],
                sk_mod=skew_model,
                sk_m=meas[2],
            )
        )
        print(f"  done ({n_rep},{n_ctl}) in {time.time() - t0:4.0f}s", flush=True)

    nsim = args.n_sim
    for a in alphas:
        se = math.sqrt(a * (1 - a) / nsim)
        print(f"\n--- {label}: FPR at nominal alpha = {a}  (binom se ~ {se:.4f}) ---")
        head = " ".join(f"{m:>12}" for m in METHODS)
        print(f"{'n_rep':>5} {'n_ctl':>5} {'M':>3} {'L':>4} | {head}")
        print("-" * (23 + 13 * len(METHODS)))
        for n_rep, n_ctl in CONFIGS:
            M, L = n_rep - 1, n_rep - 1 + n_ctl
            r = results[(n_rep, n_ctl)]
            cells = " ".join(f"{r[(m, a)]:>12.4f}" for m in METHODS)
            print(f"{n_rep:>5} {n_ctl:>5} {M:>3} {L:>4} | {cells}")

    print(f"\n--- {label}: skew diagnostics (model vs measured true-null mAP) ---")
    print(
        f"{'n_rep':>5} {'n_ctl':>5} | {'mu_mod':>9} {'mu_meas':>9} | {'sd_de':>9} "
        f"{'sd_meas':>9} {'sd_ratio':>9} | {'skew_mod':>9} {'skew_meas':>9}"
    )
    for d in diag:
        print(
            f"{d['n_rep']:>5} {d['n_ctl']:>5} | {d['mu']:>9.5f} {d['mu_m']:>9.5f} | "
            f"{d['sd_de']:>9.5f} {d['sd_m']:>9.5f} {d['sd_m'] / d['sd_de']:>9.4f} | "
            f"{d['sk_mod']:>9.4f} {d['sk_m']:>9.4f}"
        )
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-sim", type=int, default=100_000)
    ap.add_argument("--n-null", type=int, default=2_000_000)
    ap.add_argument("--pool", type=int, default=4_000_000)
    ap.add_argument("--n-feat", type=int, default=50)
    ap.add_argument("--only", choices=["gram", "shared", "both"], default="both")
    args = ap.parse_args()
    global N_NULL
    N_NULL = args.n_null
    print(
        f"n_sim={args.n_sim:,} true-null obs/config; n_null={args.n_null:,}; "
        f"pool={args.pool:,}; n_feat={args.n_feat}"
    )
    print(
        "methods: indep_mc=(a) uncorrected | de_normal,de_mc=(b) variance-only | "
        "cf,gamma_mc=(c) shape | oracle_sd,oracle_shape=ceilings"
    )
    if args.only in ("shared", "both"):
        run("shared", "shared-only (tier-2 model; analytic moments EXACT here)", args)
    if args.only in ("gram", "both"):
        run(
            "gram", "gram (realistic cosine; residual Gram coupling out of model)", args
        )


if __name__ == "__main__":
    main()
