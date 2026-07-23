# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy"]
# ///
"""Shape of the mAP null under shared positives: third moment and skew correction.

Extends the tier-2 machinery of `ap_moments` from two moments to three.  The variance
work showed a variance-only design-effect correction fixes the false-positive rate at
alpha = 0.05 but not at 0.01, and located the residual in distribution shape.  This
module supplies the missing third moment and the resulting shape-corrected null.

Third central moment of mAP = (1/n) sum_i AP_i over n profiles pairwise sharing one
positive, by index-coincidence pattern (exact identity):

    m3(mAP) = (1/n^3) [ n*mu3 + 3n(n-1)*tau + n(n-1)(n-2)*psi ]

    mu3 = E[Y_i^3]      marginal third central moment - EXACT (from `eap3`)
    tau = E[Y_i^2 Y_j]  pair term - EXACT (double-Beta sum over the shared quantile)
    psi = E[Y_i Y_j Y_k] triple term - NUMERICAL (Gauss-Legendre; validated against
                        simulation, not exact rational; the three pairwise shared
                        quantiles are independent, and conditioning on them makes the
                        profiles independent)

with Y_i = AP_i - mu.  The same conditioning that gives `cov_ap` gives tau: given the
shared quantile p the two profiles are independent, so tau = E_p[C2(p) * d1(p)] with
d1(p) = E[AP | p] - mu and C2(p) = E[(AP - mu)^2 | p]; rank-level conditional moments
are exact (closed-form mean, DP second moment) and the p-average collapses to an exact
double-Beta sum.  The machinery reproduces `cov_ap` exactly as a by-product, which the
test suite checks.

`map_shape` assembles (mu, sd, skew) for the mAP null; `cf_sf` (Cornish-Fisher) and
`gamma3_null_sample` (shifted gamma / Pearson III) are moment-matched upper-tail nulls
on top of it.  Everything inherits the tier-2 modelling assumption of `cov_ap`; see
AP_MOMENTS.md for calibration results and the honest limitations (in particular, the
residual Gram coupling of realistic cosine data lies outside the model and shows up as
under-predicted skew at large n).

Run `python map_shape.py` for a table of sd/skew/design-effect across configs.
"""

from __future__ import annotations

import math
from fractions import Fraction
from math import comb, factorial, lgamma
from statistics import NormalDist

import numpy as np

from ap_moments import eap3, expected_ap, var_ap

__all__ = [
    "cf_crit",
    "cf_sf",
    "central_moments",
    "cov_and_tau",
    "gamma3_null_sample",
    "map_shape",
    "mc_sf",
    "norm_sf",
    "psi_quad",
    "sim_shared_only",
]

_N = NormalDist()


# ----------------------------------------------------------------------------------
# marginal central moments (exact)
# ----------------------------------------------------------------------------------


def central_moments(L: int, M: int) -> tuple[Fraction, Fraction, Fraction]:
    """(mu, mu2, mu3) = (E[AP], Var(AP), third central moment), exact Fractions."""
    mu = expected_ap(L, M)
    mu2 = var_ap(L, M)
    m2 = mu2 + mu * mu  # raw second moment
    mu3 = eap3(L, M) - 3 * mu * m2 + 2 * mu**3
    return mu, mu2, mu3


# ----------------------------------------------------------------------------------
# conditional moments given forced relevant ranks (exact)
# ----------------------------------------------------------------------------------


def _incl(L: int, M: int, f: int) -> tuple[Fraction, Fraction]:
    """P(one extra rank relevant | f forced), P(two extra), as Fractions."""
    p1 = Fraction(M - f, L - f)
    p2 = (
        Fraction(0)
        if (M - f) < 2
        else Fraction((M - f) * (M - f - 1), (L - f) * (L - f - 1))
    )
    return p1, p2


def ew_cond_closed(L: int, M: int, forced: tuple[int, ...]) -> Fraction:
    """E[W | ranks in `forced` all relevant], closed form, O(L)."""
    fset = set(forced)
    p1, p2 = _incl(L, M, len(fset))
    total = Fraction(0)
    below_forced = 0  # forced ranks strictly below current r
    for r in range(1, L + 1):
        inv = Fraction(1, r)
        in_f = r in fset
        total += inv * (1 if in_f else p1)  # diagonal term Z_r/r
        below_new = (r - 1) - below_forced
        if in_f:  # off-diagonal sum_{s<r} Z_s Z_r / r
            total += inv * (below_forced + below_new * p1)
            below_forced += 1
        else:
            total += inv * (below_forced * p1 + below_new * p2)
    return total


def dp_cond_moments(
    L: int, M: int, forced: tuple[int, ...]
) -> tuple[Fraction, Fraction]:
    """(E[W|F], E[W^2|F]) exactly, over M-subsets containing `forced`.  O(L*M) DP."""
    fset = set(forced)
    dp: list[tuple[int, Fraction, Fraction]] = [(0, Fraction(0), Fraction(0))] * (M + 1)
    dp[0] = (1, Fraction(0), Fraction(0))
    for r in range(1, L + 1):
        new = [[0, Fraction(0), Fraction(0)] for _ in range(M + 1)]
        forced_here = r in fset
        for c in range(M + 1):
            cnt, s1, s2 = dp[c]
            if cnt == 0:
                continue
            if not forced_here:  # rank r not relevant
                t = new[c]
                t[0] += cnt
                t[1] += s1
                t[2] += s2
            if c + 1 <= M:  # rank r is the (c+1)-th relevant
                w0 = Fraction(c + 1, r)
                t = new[c + 1]
                t[0] += cnt
                t[1] += s1 + w0 * cnt
                t[2] += s2 + 2 * w0 * s1 + w0 * w0 * cnt
        dp = [tuple(x) for x in new]
    cnt, s1, s2 = dp[M]
    if cnt == 0:
        raise ValueError("no configuration contains the forced set")
    return s1 / cnt, s2 / cnt


# ----------------------------------------------------------------------------------
# pair term tau (exact)
# ----------------------------------------------------------------------------------


def _kbeta(L: int, u: int, v: int) -> Fraction:
    """int_0^1 P(u|p) P(v|p) dp with P(u|p) = C(L-1,u-1) p^{L-u} (1-p)^{u-1}."""
    return Fraction(comb(L - 1, u - 1) * comb(L - 1, v - 1)) * Fraction(
        factorial(u + v - 2) * factorial(2 * L - u - v), factorial(2 * L - 1)
    )


def cov_and_tau(L: int, M: int) -> tuple[Fraction, Fraction]:
    """Exact (Cov(AP_i, AP_j), tau = E[Y_i^2 Y_j]) in the tier-2 model.

    d1(u) = E[W|{u}]/M - mu and C2(u) = E[(AP - mu)^2 | shared at rank u]; averaging
    the rank pair over the shared quantile gives the Beta kernel `_kbeta`.  The Cov
    output equals `cov_ap` exactly (checked in the test suite) - it exists here as a
    built-in consistency check on the tau machinery.
    """
    mu = expected_ap(L, M)
    d1 = [Fraction(0)] * (L + 1)
    c2 = [Fraction(0)] * (L + 1)
    for u in range(1, L + 1):
        ew, ew2 = dp_cond_moments(L, M, (u,))
        m1 = ew / M
        d1[u] = m1 - mu
        c2[u] = ew2 / (M * M) - 2 * mu * m1 + mu * mu
    kb = {(u, v): _kbeta(L, u, v) for u in range(1, L + 1) for v in range(u, L + 1)}

    def K(u: int, v: int) -> Fraction:
        return kb[(u, v)] if u <= v else kb[(v, u)]

    cov = Fraction(0)
    tau = Fraction(0)
    for u in range(1, L + 1):
        for v in range(1, L + 1):
            k = K(u, v)
            cov += d1[u] * d1[v] * k
            tau += c2[u] * d1[v] * k
    return cov, tau


# ----------------------------------------------------------------------------------
# triple term psi (Gauss-Legendre quadrature; float, validated against simulation)
# ----------------------------------------------------------------------------------


def _safelog(a: np.ndarray) -> np.ndarray:
    return np.log(np.where(a > 0, a, 1.0))


def _phi2_rank_table(L: int, M: int) -> np.ndarray:
    """Rk[u, w] = E[W | {u, w} relevant]/M - mu, float, symmetric.  Needs M >= 2."""
    mu = float(expected_ap(L, M))
    rk = np.zeros((L + 1, L + 1))
    for u in range(1, L + 1):
        for w in range(u + 1, L + 1):
            val = float(ew_cond_closed(L, M, (u, w))) / M - mu
            rk[u, w] = val
            rk[w, u] = val
    return rk


def phi2_matrix(L: int, M: int, Q: int = 64):
    """(Phi, nodes, wq): Phi[i, j] = phi2(node_i, node_j) on Gauss-Legendre nodes.

    phi2(x, y) = E[AP | two shared positives at quantiles x, y] - mu, computed by
    mixing the rank table over the trinomial law of the two shared items' ranks.
    """
    rk = _phi2_rank_table(L, M)
    x, wl = np.polynomial.legendre.leggauss(Q)
    nodes = 0.5 * (x + 1.0)
    wq = 0.5 * wl
    n2 = L - 2
    logfac = np.array([0.0] + [lgamma(k + 1) for k in range(1, n2 + 2)])
    bg, cg = np.meshgrid(np.arange(n2 + 1), np.arange(n2 + 1), indexing="ij")
    mask = (bg + cg) <= n2
    ag = n2 - bg - cg
    agi = np.clip(ag, 0, n2)
    logtri = logfac[n2] - logfac[agi] - logfac[bg] - logfac[cg]
    # rank indices: worse (lower-quantile) item = B+C+2, better item = C+1
    rx = np.clip(bg + cg + 2, 0, L)
    ry = np.clip(cg + 1, 0, L)
    rval = rk[rx, ry]
    phi = np.zeros((Q, Q))
    for i in range(Q):
        xi = nodes[i]
        for j in range(i, Q):
            yj = nodes[j]
            lo, hi = (xi, yj) if xi <= yj else (yj, xi)
            gap, top = hi - lo, 1.0 - hi
            # a positive exponent on a zero base contributes exactly 0 (safelog would
            # wrongly send 0^B to 1); exclude those cells (bites the diagonal xi == yj)
            bad = (
                ((ag > 0) & (lo <= 0))
                | ((bg > 0) & (gap <= 0))
                | ((cg > 0) & (top <= 0))
            )
            logw = logtri + ag * _safelog(lo) + bg * _safelog(gap) + cg * _safelog(top)
            logw = np.where(mask & ~bad, logw, -np.inf)
            val = float((np.exp(logw) * rval).sum())
            phi[i, j] = val
            phi[j, i] = val
    return phi, nodes, wq


def psi_quad(L: int, M: int, Q: int = 64) -> float:
    """psi = E[Y_i Y_j Y_k] via Gauss-Legendre on [0,1]^3, trace((Phi diag(w))^3)."""
    if M < 2:
        return 0.0
    phi, _, wq = phi2_matrix(L, M, Q)
    mmat = phi * wq[None, :]
    return float(np.trace(mmat @ mmat @ mmat))


# ----------------------------------------------------------------------------------
# assembled mAP moments and the moment-matched nulls
# ----------------------------------------------------------------------------------


def map_shape(L: int, M: int, n: int, Q: int = 128) -> dict:
    """Moments of mAP for n homogeneous (L, M) profiles pairwise sharing one positive.

    Returns mu, sd, skew (the inputs a shape-corrected null needs), the raw
    components, and the three additive contributions to m3 (diagnostics).
    """
    mu_f, mu2_f, mu3_f = central_moments(L, M)
    cov_f, tau_f = cov_and_tau(L, M)
    mu, mu2, mu3 = float(mu_f), float(mu2_f), float(mu3_f)
    cov, tau = float(cov_f), float(tau_f)
    psi = psi_quad(L, M, Q) if n >= 3 else 0.0

    var = (n * mu2 + n * (n - 1) * cov) / n**2
    m3 = (n * mu3 + 3 * n * (n - 1) * tau + n * (n - 1) * (n - 2) * psi) / n**3
    sd = math.sqrt(var)
    return dict(
        mu=mu,
        mu2=mu2,
        mu3=mu3,
        cov=cov,
        tau=tau,
        psi=psi,
        var=var,
        sd=sd,
        m3=m3,
        skew=m3 / sd**3 if sd > 0 else 0.0,
        de=1.0 + (n - 1) * cov / mu2 if mu2 > 0 else 1.0,
        c_mu3=(n * mu3) / n**3,
        c_tau=(3 * n * (n - 1) * tau) / n**3,
        c_psi=(n * (n - 1) * (n - 2) * psi) / n**3,
    )


def norm_sf(z):
    """P(Z >= z), vectorized via erfc."""
    return 0.5 * np.vectorize(math.erfc)(np.asarray(z, dtype=float) / math.sqrt(2.0))


def z_upper(alpha: float) -> float:
    return _N.inv_cdf(1.0 - alpha)


def cf_sf(obs, mu: float, sd: float, g1: float):
    """Cornish-Fisher upper-tail p-value P(X >= obs) matching (mu, sd, skew g1)."""
    w = (np.asarray(obs, dtype=float) - mu) / sd
    a = g1 / 6.0
    if abs(a) < 1e-12:
        z = w
    else:
        disc = np.maximum(1.0 + 4.0 * a * (w + a), 0.0)
        z = (-1.0 + np.sqrt(disc)) / (2.0 * a)
    return norm_sf(z)


def cf_crit(alpha: float, mu: float, sd: float, g1: float) -> float:
    """Upper-alpha critical value under the Cornish-Fisher expansion."""
    z = z_upper(alpha)
    return mu + sd * (z + (g1 / 6.0) * (z * z - 1.0))


def gamma3_null_sample(
    mu: float, sd: float, g1: float, n: int, seed: int
) -> np.ndarray:
    """Sorted Monte-Carlo sample from the shifted gamma matching (mu, sd, g1 > 0).

    Pearson-III robustness alternative to `cf_sf`: a proper monotone distribution
    matching the same three moments, so agreement between the two says the correction
    does not hinge on the Cornish-Fisher expansion's tail validity.
    """
    rng = np.random.default_rng(seed)
    if g1 <= 1e-9:
        return np.sort(rng.normal(mu, sd, n))
    k = 4.0 / (g1 * g1)
    theta = sd * g1 / 2.0
    return np.sort(mu - 2.0 * sd / g1 + rng.gamma(k, theta, n))


def mc_sf(obs, null_sorted: np.ndarray):
    """P(null >= obs), the +1 Monte-Carlo upper-tail p-value."""
    n = null_sorted.size
    ge = n - np.searchsorted(null_sorted, obs, side="left")
    return (1.0 + ge) / (1.0 + n)


# ----------------------------------------------------------------------------------
# tier-2 generative simulator (the model itself, end to end)
# ----------------------------------------------------------------------------------


def _ap_from_scores(scores: np.ndarray, n_pos: int) -> np.ndarray:
    """AP for each row of `scores` (..., L) whose first n_pos columns are positives."""
    L = scores.shape[-1]
    lab = np.zeros(L)
    lab[:n_pos] = 1.0
    order = np.argsort(-scores, axis=-1, kind="stable")
    rel = lab[order]
    tp = np.cumsum(rel, axis=-1)
    k = np.arange(1, L + 1, dtype=float)
    return ((tp / k) * rel).sum(axis=-1) / n_pos


def sim_shared_only(
    n_rep: int, n_ctl: int, n_sim: int, seed: int, max_elems: int = 8_000_000
) -> np.ndarray:
    """Tier-2 generative model, exactly: (n_sim, n_rep) AP array.

    Symmetric matrix P of iid N(0,1) shared values; profile i ranks the other
    n_rep - 1 replicates (positives P[i, *]) against n_ctl fresh iid negatives.  Every
    pair (i, j) shares exactly the single value P[i, j] and nothing else - this IS the
    model behind `cov_ap`, `cov_and_tau`, and `psi_quad`.
    """
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
        out[done : done + b] = _ap_from_scores(np.concatenate([pos, neg], axis=-1), M)
        done += b
    return out


if __name__ == "__main__":
    CONFIGS = [(3, 20), (4, 20), (6, 20), (10, 20), (4, 100), (10, 100), (20, 100)]
    hdr = (
        f"{'nrep':>4} {'nctl':>4} {'M':>3} {'L':>4} | {'sd(mAP)':>10} {'skew':>8} "
        f"{'DE':>7} | {'c_mu3':>10} {'c_tau':>10} {'c_psi':>10} {'psi%':>6}"
    )
    print(hdr)
    print("-" * len(hdr))
    for n_rep, n_ctl in CONFIGS:
        M, L = n_rep - 1, n_rep - 1 + n_ctl
        r = map_shape(L, M, n_rep)
        psipct = 100 * r["c_psi"] / r["m3"] if r["m3"] else 0.0
        print(
            f"{n_rep:>4} {n_ctl:>4} {M:>3} {L:>4} | {r['sd']:>10.3e} {r['skew']:>8.4f} "
            f"{r['de']:>7.4f} | {r['c_mu3']:>10.2e} {r['c_tau']:>10.2e} "
            f"{r['c_psi']:>10.2e} {psipct:>5.1f}%"
        )
    print(
        "\nc_* are the three additive contributions to m3(mAP); psi% is the triple "
        "term's share of m3."
    )
