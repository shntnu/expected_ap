# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy"]
# ///
"""Saddlepoint tail for the independent mAP null: the probe behind AP_MOMENTS.md.

The cumulant generating function of W = M*AP is computable by the same rank DP as
`_ap_coeffs`, with exp(t*c/r) weights instead of atom bookkeeping: O(L*M) floats, no
atom grid, no bignums.  A Lugannani-Rice tail evaluation then costs milliseconds at
any L, where the exact PMF convolution explodes on its lcm(1..L) grid.

Scope, stated plainly: demonstrated on the INDEPENDENT null only, where
`exact_map_pmf` supplies exact ground truth.  Accuracy under the shared-positive
model is untested; extending it means saddlepointing conditional on the shared
quantiles and integrating.

History, kept because it is instructive: the first version of this probe had the
sign of the Lugannani-Rice correction term flipped ((1/w - 1/u) for (1/u - 1/w)),
producing a systematic bias of up to ~20% at moderate deviations that was initially
misdiagnosed as a lattice effect.  It is not one: the mAP lattice spacing at the
test config is ~3e-6 sd, five orders of magnitude too small to matter, and the
continuity-corrected formula changes nothing past the fifth digit.  An adversarial
review caught both the sign error and the bad diagnosis; this file carries the
standard-sign formula and a self-check against the exact law.

Run: uv run --with numpy saddle_probe.py
"""

from __future__ import annotations

import math
import time

import numpy as np

from ap_moments import exact_map_pmf, expected_ap, var_ap
from map_shape import cf_sf, central_moments, norm_sf


def cgf_w(L: int, M: int, t: float) -> float:
    """log E[exp(t*W)], W = M*AP, by the rank DP with exponential weights.  O(L*M)."""
    neg = -np.inf
    dp = np.full(M + 1, neg)
    dp[0] = 0.0
    for r in range(1, L + 1):
        new = np.full(M + 1, neg)
        for c in range(min(r, M), -1, -1):
            if dp[c] == neg:
                continue
            if c <= r - 1:  # rank r not relevant
                new[c] = np.logaddexp(new[c], dp[c])
            if c + 1 <= M:  # rank r is the (c+1)-th relevant
                new[c + 1] = np.logaddexp(new[c + 1], dp[c] + t * (c + 1) / r)
        dp = new
    return float(dp[M]) - math.log(math.comb(L, M))


def saddle_tail(L: int, M: int, n: int, x: float) -> float:
    """Lugannani-Rice P(mAP >= x) for n independent (L, M) profiles.

    K_mAP(s) = n * K_AP(s/n) with K_AP(s) = cgf_w(L, M, s/M).  Standard-sign formula:
    P = 1 - Phi(w) + phi(w) * (1/u - 1/w).
    """

    def K(s: float) -> float:
        return n * cgf_w(L, M, s / (n * M))

    h = 1e-4

    def Kp(s: float) -> float:
        return (K(s + h) - K(s - h)) / (2 * h)

    def Kpp(s: float) -> float:
        return (K(s + h) - 2 * K(s) + K(s - h)) / h**2

    lo, hi = 0.0, 400.0 * n
    for _ in range(200):  # bisect on K'(s) = x
        mid = 0.5 * (lo + hi)
        if Kp(mid) < x:
            lo = mid
        else:
            hi = mid
    s = 0.5 * (lo + hi)
    if s <= 1e-9:
        return 0.5
    w = math.copysign(math.sqrt(max(2 * (s * x - K(s)), 0.0)), s)
    u = s * math.sqrt(max(Kpp(s), 1e-300))
    phi_w = math.exp(-w * w / 2) / math.sqrt(2 * math.pi)
    return float(norm_sf(w) + phi_w * (1 / u - 1 / w))


def _compare(L: int, M: int, n: int, ks) -> list[dict]:
    t0 = time.time()
    pmf = exact_map_pmf([(L, M)] * n)
    t_exact = time.time() - t0
    vals = np.array([float(v) for v in pmf])
    probs = np.array([float(p) for p in pmf.values()])
    order = np.argsort(vals)
    vals, probs = vals[order], probs[order]

    mu = float(expected_ap(L, M))
    sd = math.sqrt(float(var_ap(L, M)) / n)
    _, _, mu3 = central_moments(L, M)
    skew_ind = (float(mu3) / n**2) / sd**3  # independent null: m3(mAP) = mu3/n^2

    rows = []
    for k in ks:
        x = mu + k * sd
        exact = float(probs[vals >= x - 1e-15].sum())
        t0 = time.time()
        sp = saddle_tail(L, M, n, x)
        t_sp = time.time() - t0
        rows.append(
            dict(
                k=k,
                exact=exact,
                saddle=sp,
                cf=float(cf_sf(x, mu, sd, skew_ind)),
                normal=float(norm_sf(k)),
                t_exact=t_exact,
                t_saddle=t_sp,
            )
        )
    return rows


if __name__ == "__main__":
    KS = (1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5)
    for L, M, n in [(14, 3, 3), (10, 2, 3)]:
        rows = _compare(L, M, n, KS)
        print(
            f"\n{n} x (L={L}, M={M}) independent null "
            f"(exact PMF build {rows[0]['t_exact'] * 1e3:.0f} ms, "
            f"one saddlepoint eval {rows[0]['t_saddle'] * 1e3:.0f} ms)"
        )
        print(
            f"{'k (sd)':>7} {'exact':>10} {'saddle':>10} {'err%':>7} "
            f"{'CF':>10} {'err%':>7} {'Normal':>10} {'err%':>7}"
        )
        for r in rows:
            e = r["exact"]
            print(
                f"{r['k']:>7.1f} {e:>10.5f} "
                f"{r['saddle']:>10.5f} {100 * (r['saddle'] / e - 1):>+7.1f} "
                f"{r['cf']:>10.5f} {100 * (r['cf'] / e - 1):>+7.1f} "
                f"{r['normal']:>10.5f} {100 * (r['normal'] / e - 1):>+7.1f}"
            )
        if (L, M, n) == (14, 3, 3):
            worst = max(abs(r["saddle"] / r["exact"] - 1) for r in rows)
            assert worst < 0.025, f"saddlepoint drifted: max rel err {worst:.3f}"
            print(
                f"self-check passed: max |rel err| = {100 * worst:.1f}% over k in {KS}"
            )
