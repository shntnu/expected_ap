# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy"]
# ///
"""Does the shared-positive covariance correction actually fix the mAP false-positive rate?

Two questions, answered against true-null simulated data (random gaussian features, no
real signal, copairs-style replicate retrieval: for replicate profile i the positives are
the other n_rep-1 replicates and the negatives are the n_ctl controls, so M = n_rep-1 and
L = n_rep-1+n_ctl).

1. PREDICTION TEST.  ap_moments.cov_ap / var_ap predicts a design effect
   DE = 1 + (n-1) * cov/var for the variance of mAP over n profiles that pairwise share
   one positive.  Compare it to the variance inflation actually measured in simulation.

2. CALIBRATION TEST.  Build corrected mAP nulls (moment-matched Monte Carlo shape, and a
   Normal approximation, both using the corrected sd) and measure the false-positive rate
   at nominal 0.05 and 0.01, before and after correction, with Monte Carlo standard errors.

Also reported: an "oracle" null rescaled to the sd measured from the simulation itself.
If the oracle is calibrated but the corrected null is not, the residual is a variance
error; if even the oracle misses nominal, the residual is distribution shape (skewness).

Run:  uv run calibration_check.py
      uv run --with pandas --with copairs calibration_check.py --validate

`--validate` re-checks the fast simulator against copairs and needs those two extra
packages, which is why they are not in the script header.
"""

from __future__ import annotations

import argparse
import math
import time

import numpy as np

from ap_moments import cov_ap, design_effect, expected_ap, map_null_sd, var_ap

# ----------------------------------------------------------------------------------
# simulators
# ----------------------------------------------------------------------------------


def _ap_from_sims(sims: np.ndarray, n_pos: int) -> np.ndarray:
    """AP for each row of `sims` (..., L) whose first n_pos columns are the positives."""
    L = sims.shape[-1]
    lab = np.zeros(L)
    lab[:n_pos] = 1.0
    order = np.argsort(-sims, axis=-1, kind="stable")
    rel = lab[order]
    tp = np.cumsum(rel, axis=-1)
    k = np.arange(1, L + 1, dtype=float)
    return ((tp / k) * rel).sum(axis=-1) / n_pos


def sim_gram_aps(n_rep, n_ctl, n_feat, n_sim, seed, max_elems=4_000_000):
    """True-null replicate retrieval from a shared Gram matrix.  -> (n_sim, n_rep) APs.

    Same construction as the validated fast simulator: iid standard normal features,
    row-normalised, cosine similarity, profile i ranks the other n_rep-1 replicates
    (positives) against the n_ctl controls (negatives).
    """
    rng = np.random.default_rng(seed)
    M, L = n_rep - 1, n_rep - 1 + n_ctl
    N = n_rep + n_ctl
    pos_idx = np.array([[j for j in range(n_rep) if j != i] for i in range(n_rep)])
    rows = np.arange(n_rep)[:, None]
    chunk = max(1, int(max_elems // (n_rep * L)))
    out = np.empty((n_sim, n_rep))
    done = 0
    while done < n_sim:
        b = min(chunk, n_sim - done)
        X = rng.standard_normal((b, N, n_feat))
        X /= np.linalg.norm(X, axis=2, keepdims=True)
        S = X @ np.transpose(X, (0, 2, 1))
        pos = S[:, rows, pos_idx]  # (b, n_rep, M)
        neg = S[:, :n_rep, n_rep:]  # (b, n_rep, n_ctl)
        out[done : done + b] = _ap_from_sims(np.concatenate([pos, neg], axis=-1), M)
        done += b
    return out


def sim_shared_only_aps(n_rep, n_ctl, n_sim, seed, max_elems=4_000_000):
    """Combinatorial control: every similarity iid, but profiles i and j still SHARE the
    single value of pair (i,j).  Isolates the shared-positive coupling that cov_ap models
    from any extra coupling induced by the Gram structure."""
    rng = np.random.default_rng(seed)
    M, L = n_rep - 1, n_rep - 1 + n_ctl
    iu = np.triu_indices(n_rep, 1)
    pos_idx = np.array([[j for j in range(n_rep) if j != i] for i in range(n_rep)])
    rows = np.arange(n_rep)[:, None]
    chunk = max(1, int(max_elems // (n_rep * L)))
    out = np.empty((n_sim, n_rep))
    done = 0
    while done < n_sim:
        b = min(chunk, n_sim - done)
        P = np.zeros((b, n_rep, n_rep))
        vals = rng.standard_normal((b, len(iu[0])))
        P[:, iu[0], iu[1]] = vals
        P[:, iu[1], iu[0]] = vals
        pos = P[:, rows, pos_idx]
        neg = rng.standard_normal((b, n_rep, n_ctl))
        out[done : done + b] = _ap_from_sims(np.concatenate([pos, neg], axis=-1), M)
        done += b
    return out


def sample_marginal_ap(L, M, n, seed, chunk=200_000):
    """iid draws from the EXACT marginal AP law: relevant ranks uniform over the C(L,M)
    size-M subsets, AP = (1/M) sum_j j/R_j.  This is the per-profile null that the
    independent-convolution mAP null is built from."""
    rng = np.random.default_rng(seed)
    j = np.arange(1, M + 1, dtype=float)
    out = np.empty(n)
    done = 0
    while done < n:
        b = min(chunk, n - done)
        keys = rng.random((b, L))
        idx = np.argpartition(keys, M - 1, axis=1)[:, :M]
        idx.sort(axis=1)
        out[done : done + b] = (j / (idx + 1.0)).sum(axis=1) / M
        done += b
    return out


# ----------------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------------


def norm_sf(z):
    """P(Z >= z) for standard normal, via erfc (no scipy)."""
    return 0.5 * np.vectorize(math.erfc)(np.asarray(z, dtype=float) / math.sqrt(2.0))


def mc_pvalues(obs, null_sorted):
    """P(null >= obs), the standard +1 Monte Carlo p-value."""
    n = null_sorted.size
    ge = n - np.searchsorted(null_sorted, obs, side="left")
    return (1.0 + ge) / (1.0 + n)


def skew(x):
    d = x - x.mean()
    return (d**3).mean() / d.std() ** 3


def exkurt(x):
    d = x - x.mean()
    return (d**4).mean() / d.std() ** 4 - 3.0


def se_prop(p, n):
    return math.sqrt(max(p * (1 - p), 0.0) / n)


def validate_against_copairs(n_rep=4, n_ctl=20, n_feat=50, reps=200, seed=7):
    import pandas as pd
    from copairs.map import average_precision as cp_ap

    meta = pd.DataFrame(
        {
            "compound": ["c0"] * n_rep + [f"d{i}" for i in range(n_ctl)],
            "control": [False] * n_rep + [True] * n_ctl,
        }
    )
    rng = np.random.default_rng(seed)
    mine, theirs = [], []
    for _ in range(reps):
        X = rng.standard_normal((n_rep + n_ctl, n_feat))
        Xn = X / np.linalg.norm(X, axis=1, keepdims=True)
        S = Xn @ Xn.T
        pos_idx = np.array([[j for j in range(n_rep) if j != i] for i in range(n_rep)])
        pos = S[np.arange(n_rep)[:, None], pos_idx]
        neg = S[:n_rep, n_rep:]
        mine.append(_ap_from_sims(np.concatenate([pos, neg], axis=-1), n_rep - 1))
        r = cp_ap(
            meta,
            X.astype(np.float32),
            pos_sameby=["compound"],
            pos_diffby=[],
            neg_sameby=[],
            neg_diffby=["compound"],
            progress_bar=False,
        )
        theirs.append(r[~r["control"]]["average_precision"].to_numpy())
    d = np.abs(np.array(mine) - np.array(theirs)).max()
    print(f"simulator vs copairs, max abs AP diff over {reps} draws: {d:.3e}\n")


# ----------------------------------------------------------------------------------
# main experiment
# ----------------------------------------------------------------------------------

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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-sim", type=int, default=20_000)
    ap.add_argument("--n-null", type=int, default=400_000)
    ap.add_argument("--pool", type=int, default=2_000_000)
    ap.add_argument("--n-feat", type=int, default=50)
    ap.add_argument("--validate", action="store_true")
    args = ap.parse_args()

    if args.validate:
        validate_against_copairs()

    print(
        f"n_sim={args.n_sim:,} true-null simulations per config; "
        f"independent null = {args.n_null:,} draws resampled from a pool of "
        f"{args.pool:,} exact-law APs; n_feat={args.n_feat}\n"
    )

    pred_rows, cal_rows, diag_rows = [], [], []

    for n_rep, n_ctl in CONFIGS:
        t0 = time.time()
        M, L = n_rep - 1, n_rep - 1 + n_ctl
        n = n_rep

        # ---------- theory ----------
        v1 = float(var_ap(L, M))
        c1 = float(cov_ap(L, M, exact=False))
        rho_pred = c1 / v1
        de_pred = design_effect(L, M, n)
        mu = float(expected_ap(L, M))
        sd_ind_th = math.sqrt(v1 / n)
        sd_corr_th = map_null_sd([(L, M)] * n)  # = sqrt(v1 * de_pred / n)

        # ---------- true-null simulation ----------
        A = sim_gram_aps(n_rep, n_ctl, args.n_feat, args.n_sim, seed=1000 + n_rep)
        obs = A.mean(axis=1)
        v_meas_1 = A.var(ddof=1)  # marginal AP variance (sanity vs var_ap)
        var_meas = obs.var(ddof=1)
        de_meas = var_meas / (v1 / n)
        # se of a sample variance: Var(s2) ~ (mu4 - sigma^4)/n_sim
        d = obs - obs.mean()
        mu4 = (d**4).mean()
        se_var = math.sqrt(max(mu4 - var_meas**2, 0.0) / args.n_sim)
        se_de = se_var / (v1 / n)
        rho_meas = np.corrcoef(A.T)[np.triu_indices(n, 1)].mean()
        se_rho = (1.0 - rho_meas**2) / math.sqrt(args.n_sim)  # per-pair, optimistic

        # ---------- nulls ----------
        pool = sample_marginal_ap(L, M, args.pool, seed=2000 + n_rep)
        rng = np.random.default_rng(3000 + n_rep)
        Z = np.empty(args.n_null)
        step = max(1, 20_000_000 // n)
        done = 0
        while done < args.n_null:
            b = min(step, args.n_null - done)
            Z[done : done + b] = pool[rng.integers(0, pool.size, size=(b, n))].mean(1)
            done += b

        # heuristic "effective n" null: averaging k = n/DE independent APs reproduces the
        # corrected variance AND carries more skew than the n-fold average, since skew of
        # a k-fold mean scales as 1/sqrt(k).  Rescaled afterwards so the sd is exact.
        k_eff = max(1, int(round(n / de_pred)))
        Zk = np.empty(args.n_null)
        done = 0
        while done < args.n_null:
            b = min(step, args.n_null - done)
            Zk[done : done + b] = pool[
                rng.integers(0, pool.size, size=(b, k_eff))
            ].mean(1)
            done += b

        sd_meas = math.sqrt(var_meas)

        def rescaled(src, target_sd):
            return np.sort(mu + (src - src.mean()) * (target_sd / src.std(ddof=1)))

        Z_unc = np.sort(Z)
        Z_cor = rescaled(Z, sd_corr_th)
        Z_ora = rescaled(Z, sd_meas)
        Z_eff = rescaled(Zk, sd_corr_th)

        p_unc_mc = mc_pvalues(obs, Z_unc)
        p_cor_mc = mc_pvalues(obs, Z_cor)
        p_ora_mc = mc_pvalues(obs, Z_ora)
        p_eff_mc = mc_pvalues(obs, Z_eff)
        p_unc_nm = norm_sf((obs - mu) / sd_ind_th)
        p_cor_nm = norm_sf((obs - mu) / sd_corr_th)

        fpr = {}
        for name, p in [
            ("unc_mc", p_unc_mc),
            ("cor_mc", p_cor_mc),
            ("ora_mc", p_ora_mc),
            ("eff_mc", p_eff_mc),
            ("unc_nm", p_unc_nm),
            ("cor_nm", p_cor_nm),
        ]:
            for a in (0.05, 0.01):
                fpr[(name, a)] = float((p < a).mean())

        # tail inflation: how much wider than the independent null is the TRUE upper tail?
        # sqrt(DE) is what a pure variance rescale delivers; anything above it is shape.
        tail = {}
        for a in (0.05, 0.01):
            qt = float(np.quantile(obs, 1 - a))
            qn = float(np.quantile(Z, 1 - a))
            tail[a] = (qt - mu) / (qn - mu)

        pred_rows.append(
            dict(
                n_rep=n_rep,
                n_ctl=n_ctl,
                M=M,
                L=L,
                rho_pred=rho_pred,
                rho_meas=rho_meas,
                se_rho=se_rho,
                de_pred=de_pred,
                de_meas=de_meas,
                se_de=se_de,
                sdr_pred=math.sqrt(de_pred),
                sdr_meas=sd_meas / sd_ind_th,
            )
        )
        cal_rows.append(dict(n_rep=n_rep, n_ctl=n_ctl, fpr=fpr, k_eff=k_eff))
        diag_rows.append(
            dict(
                n_rep=n_rep,
                n_ctl=n_ctl,
                mu_th=mu,
                mu_meas=obs.mean(),
                se_mu=sd_meas / math.sqrt(args.n_sim),
                sd_ap_th=math.sqrt(v1),
                sd_ap_meas=math.sqrt(v_meas_1),
                skew_null=skew(Z),
                skew_obs=skew(obs),
                kurt_null=exkurt(Z),
                kurt_obs=exkurt(obs),
                sd_ratio=sd_meas / sd_ind_th,
                tail05=tail[0.05],
                tail01=tail[0.01],
                secs=time.time() - t0,
            )
        )
        print(f"  done ({n_rep},{n_ctl}) in {time.time() - t0:5.1f}s", flush=True)

    nsim = args.n_sim

    print("\n" + "=" * 100)
    print(
        "1. PREDICTION TEST -- theoretical design effect vs measured variance inflation"
    )
    print("=" * 100)
    print(
        f"{'n_rep':>5} {'n_ctl':>5} {'M':>4} {'L':>5} | "
        f"{'rho_pred':>9} {'rho_meas':>9} | {'DE_pred':>8} {'DE_meas':>16} "
        f"{'ratio':>7} | {'sd_pred':>7} {'sd_meas':>7}"
    )
    print("-" * 100)
    for r in pred_rows:
        print(
            f"{r['n_rep']:>5} {r['n_ctl']:>5} {r['M']:>4} {r['L']:>5} | "
            f"{r['rho_pred']:>+9.4f} {r['rho_meas']:>+9.4f} | "
            f"{r['de_pred']:>8.4f} {r['de_meas']:>10.4f} +-{r['se_de']:<5.4f} "
            f"{r['de_meas'] / r['de_pred']:>7.4f} | "
            f"{r['sdr_pred']:>7.4f} {r['sdr_meas']:>7.4f}"
        )
    print(
        "rho = Corr(AP_i, AP_j); DE = Var(mAP)/(Var(AP)/n); sd = sd ratio vs independent."
        "\nDE_meas +- is the Monte Carlo se of the sample variance."
    )

    print("\n" + "=" * 100)
    print("2. CALIBRATION TEST -- false-positive rate on true-null data")
    print("=" * 100)
    methods = ("unc_mc", "cor_mc", "eff_mc", "ora_mc", "unc_nm", "cor_nm")
    labels = ("MCuncorr", "MC corr", "MC neff", "MCoracle", "N uncorr", "N corr")
    for a in (0.05, 0.01):
        print(f"\n--- nominal alpha = {a} (MC se {se_prop(a, nsim):.4f}) ---")
        head = " ".join(f"{lab:>8}" for lab in labels)
        print(f"{'n_rep':>5} {'n_ctl':>5} {'k_eff':>5} | {head}")
        print("-" * (19 + 9 * len(labels)))
        for r in cal_rows:
            cells = " ".join(f"{r['fpr'][(k, a)]:>8.4f}" for k in methods)
            print(f"{r['n_rep']:>5} {r['n_ctl']:>5} {r['k_eff']:>5} | {cells}")
    print(
        f"\n{nsim:,} true-null sims per config.  "
        "MC uncorr = independent-convolution null (what copairs uses).\n"
        "MC corr   = that shape rescaled to the corrected sd (the correction under test).\n"
        "MC neff   = independent null of k_eff = round(n/DE) profiles, then rescaled to "
        "the corrected sd\n            (keeps more skew; heuristic).\n"
        "MC oracle = independent shape rescaled to the sd MEASURED in simulation "
        "(the ceiling for any\n            variance-only fix).\n"
        "N uncorr / N corr = Normal approximation with the independent / corrected sd."
    )

    print("\n" + "=" * 100)
    print("3. DIAGNOSTICS")
    print("=" * 100)
    print(
        f"{'n_rep':>5} {'n_ctl':>5} | {'E[AP] th':>9} {'E[AP] sim':>10} {'se':>8} | "
        f"{'sd(AP) th':>10} {'sd(AP) sim':>11} | {'skew null':>10} {'skew sim':>9} | "
        f"{'exk null':>9} {'exk sim':>8} | {'secs':>6}"
    )
    print("-" * 130)
    for r in diag_rows:
        print(
            f"{r['n_rep']:>5} {r['n_ctl']:>5} | {r['mu_th']:>9.5f} {r['mu_meas']:>10.5f} "
            f"{r['se_mu']:>8.5f} | {r['sd_ap_th']:>10.5f} {r['sd_ap_meas']:>11.5f} | "
            f"{r['skew_null']:>10.4f} {r['skew_obs']:>9.4f} | "
            f"{r['kurt_null']:>9.4f} {r['kurt_obs']:>8.4f} | {r['secs']:>6.1f}"
        )
    print(
        "E[AP] and sd(AP) check the marginal law: theory is the exact uniform-rank-set law,\n"
        "sim is the Gram simulation.  skew/exk compare the shape of the independent null\n"
        "against the shape of the true mAP distribution."
    )

    print(
        "\n--- tail inflation: how much wider the TRUE upper tail is than the "
        "independent null ---"
    )
    print(
        f"{'n_rep':>5} {'n_ctl':>5} | {'sd ratio':>9} {'sqrt(DE_pred)':>14} | "
        f"{'tail@.05':>9} {'tail@.01':>9}"
    )
    print("-" * 60)
    for r, p in zip(diag_rows, pred_rows):
        print(
            f"{r['n_rep']:>5} {r['n_ctl']:>5} | {r['sd_ratio']:>9.4f} "
            f"{p['sdr_pred']:>14.4f} | {r['tail05']:>9.4f} {r['tail01']:>9.4f}"
        )
    print(
        "tail@a = (q_true(1-a) - mu) / (q_indep(1-a) - mu).  A pure variance rescale can\n"
        "only deliver the sd ratio; whatever the tail needs beyond that is skewness."
    )

    # --- shared-positive-only cross-check on two configs -------------------------
    print("\n" + "=" * 100)
    print("4. WHERE THE COUPLING COMES FROM (Gram vs shared-pair-only)")
    print("=" * 100)
    print(
        f"{'n_rep':>5} {'n_ctl':>5} | {'rho gram':>9} {'rho shared':>11} "
        f"{'rho pred':>9} | {'DE gram':>8} {'DE shared':>10} {'DE pred':>8}"
    )
    print("-" * 80)
    for n_rep, n_ctl in [(4, 20), (10, 20), (20, 100)]:
        M, L = n_rep - 1, n_rep - 1 + n_ctl
        v1 = float(var_ap(L, M))
        de_pred = design_effect(L, M, n_rep)
        rho_pred = float(cov_ap(L, M, exact=False)) / v1
        Ag = sim_gram_aps(n_rep, n_ctl, args.n_feat, args.n_sim, seed=1000 + n_rep)
        As = sim_shared_only_aps(n_rep, n_ctl, args.n_sim, seed=4000 + n_rep)
        rg = np.corrcoef(Ag.T)[np.triu_indices(n_rep, 1)].mean()
        rs = np.corrcoef(As.T)[np.triu_indices(n_rep, 1)].mean()
        dg = Ag.mean(1).var(ddof=1) / (v1 / n_rep)
        ds = As.mean(1).var(ddof=1) / (v1 / n_rep)
        print(
            f"{n_rep:>5} {n_ctl:>5} | {rg:>+9.4f} {rs:>+11.4f} {rho_pred:>+9.4f} | "
            f"{dg:>8.4f} {ds:>10.4f} {de_pred:>8.4f}"
        )
    print(
        "shared = every similarity iid but pair (i,j) still shared between profiles i,j;\n"
        "this is exactly the model cov_ap assumes.  gram = the real cosine-similarity setup."
    )


if __name__ == "__main__":
    main()
