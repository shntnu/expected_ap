# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Exact moments of Average Precision under random ranking, and the mAP null.

Everything here is exact rational arithmetic on top of one ranking model, stated
once and used everywhere:

    A profile ranks L items, M of them relevant (1 <= M <= L).  Under the null the
    ranking is uniform, so the set of ranks holding the relevant items is uniform
    over the C(L, M) size-M subsets, and with sorted ranks R_1 < ... < R_M

        AP = (1/M) * sum_{j=1}^{M} j / R_j.

The results come in three tiers, in increasing order of what they assume.

Tier 1, the marginal law of one AP.  `expected_ap` is PROVEN: it is
`expected_ap_closed_form` in lean/expected_ap.lean, machine-checked with no `sorry`.
`var_ap` is the matching second moment of the same law.  It too is PROVEN:
`varianceAP_closed_form` in lean/ap_moments.lean, machine-checked with no `sorry`,
and additionally checked against exhaustive enumeration for all 1 <= M <= L <= 12.

Tier 2, two APs that share a positive.  `cov_ap` is a statement about a MODEL, not
about the ranking law alone, and the model has to be believed for the number to mean
anything: profiles i and j each rank L items with M relevant, exactly one relevant
item is shared - it is the pair (i, j) itself, carrying literally the same similarity
value in both lists - and every other value in both lists is an independent draw from
the same continuous distribution.  That is the standard replicate-retrieval setup, but
it is an assumption about the data, not a theorem.  Given the model, the covariance is
exact, including for lists of unequal shape (`cov_ap_hetero`).  `design_effect` and
the correction inside `map_null_sd` inherit that caveat.

Tier 3, the exact null PMF of mAP.  `exact_map_pmf` convolves the per-profile laws
under the assumption that the profiles are INDEPENDENT, which tier 2 says they are
not when they share positives.  It is the right null when the profiles genuinely do
not share relevant items, and it is the reference the moment formulas are checked
against; when positives are shared, widen it with `map_null_sd`.

Run `python ap_moments.py` for a small table of the numbers.
"""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction
from math import comb, gcd, lcm, prod, sqrt

__all__ = [
    "cov_ap",
    "cov_ap_hetero",
    "design_effect",
    "eap3",
    "exact_map_pmf",
    "exact_map_tail",
    "expected_ap",
    "expected_map",
    "harmonic",
    "map_null_sd",
    "var_ap",
]

Config = tuple[int, int]


def harmonic(L: int, power: int = 1) -> Fraction:
    """H_L = sum_{k=1}^{L} 1/k, or H^(2)_L = sum_{k=1}^{L} 1/k^2 for power=2."""
    return sum((Fraction(1, k**power) for k in range(1, L + 1)), Fraction(0))


# ----------------------------------------------------------------------------------
# tier 1: the marginal law of a single AP
# ----------------------------------------------------------------------------------


def expected_ap(L: int, M: int) -> Fraction:
    """E[AP] = (1/L) * ( (M-1)/(L-1) * (L - H_L) + H_L ), for 1 <= M <= L.

    PROVEN, not merely checked: `expected_ap_closed_form` in lean/expected_ap.lean.
    The Lean statement carries the same M >= 1 guard - at M = 0 the AP is 0 by
    convention while the harmonic expression is not.

    This is the correct null for "how good does random look", and it exceeds the naive
    prevalence M/L by an O(log L / L) term that does not vanish at practical L.
    """
    if not 1 <= M <= L:
        raise ValueError(f"require 1 <= M <= L, got L={L}, M={M}")
    if L == 1:
        return Fraction(1)
    H = harmonic(L)
    return Fraction(1, L) * (Fraction(M - 1, L - 1) * (L - H) + H)


def var_ap(L: int, M: int) -> Fraction:
    """Exact Var(AP) under uniform random ranking of L items, M of them relevant.

    Same law as `expected_ap`, second moment instead of first.  Writing the AP in
    indicator form, with Z_k = 1 when rank k holds a relevant item,

        AP = (1/M) * sum_{k=1}^{L} Z_k * (1/k) * sum_{i<=k} Z_i,

    every moment reduces to inclusion probabilities of up to four ranks at once.  Let
    H = H_L, H2 = H^(2)_L, and m_r = (M)_r / (L)_r = C(M,r) / C(L,r), with m_r = 0 for
    r > M.  With W = M * AP = sum_{1<=i<=k<=L} Z_i Z_k / k:

        E[W]   = m1*H + m2*(L - H)
        E[W^2] = m1*H2
               + m2*(2H^2 + 3H - 5H2)
               + m3*(2LH + 5L - 5H^2 - 9H + 7H2)
               + m4*(L^2 - 2LH - 5L + 3H^2 + 6H - 3H2)
        Var(AP) = (E[W^2] - E[W]^2) / M^2

    Exact in rational arithmetic, and E[W] here reproduces the Lean-proven mean.  The
    variance is PROVEN: `varianceAP_closed_form` in lean/ap_moments.lean establishes
    exactly this closed form with no `sorry`, and it also agrees with exhaustive
    enumeration of all C(L,M) rank subsets for every 1 <= M <= L <= 12.

    Requires 1 <= M <= L.  Returns exactly 0 when M == L (AP is then deterministically
    1), and H2_L/L - (H_L/L)^2 when M == 1.
    """
    if not (1 <= M <= L):
        raise ValueError("require 1 <= M <= L")

    H = harmonic(L)
    H2 = harmonic(L, 2)

    def m(r: int) -> Fraction:
        # falling-factorial ratio (M)_r / (L)_r; the r > M guard also keeps the
        # (L-1)(L-2)(L-3) denominator factors from ever being touched at small L
        if r > M:
            return Fraction(0)
        num = den = 1
        for t in range(r):
            num *= M - t
            den *= L - t
        return Fraction(num, den)

    m1, m2, m3, m4 = m(1), m(2), m(3), m(4)

    e_w = m1 * H + m2 * (L - H)
    e_w2 = (
        m1 * H2
        + m2 * (2 * H**2 + 3 * H - 5 * H2)
        + m3 * (2 * L * H + 5 * L - 5 * H**2 - 9 * H + 7 * H2)
        + m4 * (L**2 - 2 * L * H - 5 * L + 3 * H**2 + 6 * H - 3 * H2)
    )

    return (e_w2 - e_w * e_w) / Fraction(M * M)


def eap3(L: int, M: int) -> Fraction:
    """Exact E[AP^3] under uniform random ranking of L items, M of them relevant.

    Third raw moment of the same law as `expected_ap` and `var_ap`.  With m_r as in
    `var_ap`, H = H_L, H2 = H^(2)_L, H3 = H^(3)_L, and ONE extra weight-3 generator,
    the finite Euler sum G = sum_{k<=L} H_k / k^2:

        E[W^3] = m1*H3
               + m2*(7*H2 + 6*H*H2 - 19*H3 + 6*G)
               + m3*(30*H + 21*H^2 + 6*H^3 + (3L-66)*H2 - 51*H*H2 + 81*H3 - 24*G)
               + m4*(58*L + (24L-141)*H + (6L-195/2)*H^2 - 26*H^3
                     + (343/2-15L)*H2 + 129*H*H2 - 139*H3 + 30*G)
               + m5*(15L^2 - 132*L + (3L^2-57L+201)*H + (273/2-15L)*H^2 + 35*H^3
                     + (21L-345/2)*H2 - 129*H*H2 + 106*H3 - 12*G)
               + m6*(L^3 - 15L^2 + 74*L - (3L^2-33L+90)*H + (9L-60)*H^2 - 15*H^3
                     - (9L-60)*H2 + 45*H*H2 - 30*H3)
        E[AP^3] = E[W^3] / M^3

    The G term is not removable: the pure weight-3 basis {1, H, H^2, H^3, H2, H*H2, H3}
    with (L, M)-rational coefficients provably cannot express E[W^3] (the exact linear
    systems are inconsistent, confirmed by modular tests over two independent 61-bit
    primes).  Collected, coeff(G) = 6M(M-1)(L-M)(L-M-1)(L-2M) / (L(L-1)(L-2)(L-3)(L-4)),
    vanishing only at M in {1, L/2, L-1, L}.

    Two independent derivations (exact ansatz identification against a moment DP out to
    L = 120, and a mechanical 6-index coincidence-pattern expansion over 818 patterns)
    produced this identical formula; it matches exhaustive enumeration for all
    1 <= M <= L <= 13 (the test suite re-checks L <= 12) and the DP to L = 120.
    Anchors: M = 1 gives E[AP^3] = H3_L / L; M = L gives exactly 1.
    """
    if not (1 <= M <= L):
        raise ValueError("require 1 <= M <= L")

    H = harmonic(L)
    H2 = harmonic(L, 2)
    H3 = harmonic(L, 3)
    G = Fraction(0)
    Hk = Fraction(0)
    for k in range(1, L + 1):
        Hk += Fraction(1, k)
        G += Hk / (k * k)

    def m(r: int) -> Fraction:
        if r > M:
            return Fraction(0)
        num = den = 1
        for t in range(r):
            num *= M - t
            den *= L - t
        return Fraction(num, den)

    e_w3 = (
        m(1) * H3
        + m(2) * (7 * H2 + 6 * H * H2 - 19 * H3 + 6 * G)
        + m(3)
        * (
            30 * H
            + 21 * H**2
            + 6 * H**3
            + (3 * L - 66) * H2
            - 51 * H * H2
            + 81 * H3
            - 24 * G
        )
        + m(4)
        * (
            58 * L
            + (24 * L - 141) * H
            + (6 * L - Fraction(195, 2)) * H**2
            - 26 * H**3
            + (Fraction(343, 2) - 15 * L) * H2
            + 129 * H * H2
            - 139 * H3
            + 30 * G
        )
        + m(5)
        * (
            15 * L**2
            - 132 * L
            + (3 * L**2 - 57 * L + 201) * H
            + (Fraction(273, 2) - 15 * L) * H**2
            + 35 * H**3
            + (21 * L - Fraction(345, 2)) * H2
            - 129 * H * H2
            + 106 * H3
            - 12 * G
        )
        + m(6)
        * (
            L**3
            - 15 * L**2
            + 74 * L
            - (3 * L**2 - 33 * L + 90) * H
            + (9 * L - 60) * H**2
            - 15 * H**3
            - (9 * L - 60) * H2
            + 45 * H * H2
            - 30 * H3
        )
    )

    return e_w3 / Fraction(M**3)


# ----------------------------------------------------------------------------------
# tier 2: two APs that share a positive
# ----------------------------------------------------------------------------------


def cov_ap(L: int, M: int, exact: bool = True):
    """Exact Cov(AP_i, AP_j) in the two-list shared-positive model.  O(L) work.

    MODELLING ASSUMPTION, stated so it can be disagreed with.  Profiles i and j each
    rank L items with M relevant.  Exactly ONE relevant item is shared - it is the pair
    (i, j) and carries literally the same similarity value in both lists; every other
    value in both lists is an independent draw from the same continuous distribution.
    AP = (1/M) sum_j j/R_j as everywhere else.  Nothing in Lean covers this; what is
    exact is the arithmetic downstream of the model.

    Derivation: conditioning on the shared value's quantile p makes the two lists
    independent, so Cov = Var_{p~U(0,1)}( E[AP | p] ).  Given the shared item sits
    at rank u, the other M-1 positives are a uniform (M-1)-subset of the other L-1
    ranks, giving E[AP | U=u] = (a + b/u + c*H_u)/M with
        q  = (M-1)/(L-1),   q2 = (M-1)(M-2)/((L-1)(L-2))   (0 if M<3 or L<3),
        b  = 1 - 2q + q2,   c = q2 - q,   a = 2q*H_L + q + q2*(L-1-2H_L).
    Mixing over p ~ U(0,1) (rank = 1 + Binomial(L-1, 1-p)) turns E[AP|p] into
    (a + A*g(p) + c*(H_{L-1} - l(p)))/M with A = (b+c)/L, g(p) = sum_{k<L} p^k,
    l(p) = sum_{k<L} p^k/k.  The constant a drops out of the variance and the
    three remaining p-moments each reduce to a single harmonic sum.

    Returns an exact Fraction (exact=True) or a float (exact=False).
    Requires L >= 2 and 1 <= M <= L.  Returns exactly 0 when M == L.
    For M == 1 this equals [1 + 2L(H_{2L-1} - H_L) - H_L^2] / L^2, and for fixed M
    Cov ~ 2*ln(2) / (M^2 * L) as L -> infinity.
    """
    if L < 2 or not (1 <= M <= L):
        raise ValueError("need L >= 2 and 1 <= M <= L")

    if exact:
        R = Fraction
        H = [Fraction(0)]
        for k in range(1, 2 * L):
            H.append(H[-1] + Fraction(1, k))
    else:

        def R(a, b=1):
            return a / b

        H = [0.0]
        for k in range(1, 2 * L):
            H.append(H[-1] + 1.0 / k)

    # inclusion probabilities for the OTHER M-1 positives among the other L-1 ranks
    q = R(M - 1, L - 1)
    q2 = R(0) if (M <= 2 or L <= 2) else R((M - 1) * (M - 2), (L - 1) * (L - 2))

    b = 1 - 2 * q + q2
    c = q2 - q  # = -(M-1)(L-M)/((L-1)(L-2))    for L >= 3
    A = (b + c) / L  # = (L-M)(L-2M)/(L(L-1)(L-2))   for L >= 3

    var_g = 1 + 2 * L * (H[2 * L - 1] - H[L]) - H[L] ** 2
    cov_gl = sum(R(1, j) * (H[L + j] - H[j]) for j in range(1, L)) - R(L - 1, L) * H[L]
    var_l = (
        sum(R(1, j * (j + 1)) * (H[L - 1] + H[j + 1] - H[L + j]) for j in range(1, L))
        - R(L - 1, L) ** 2
    )

    return (A * A * var_g - 2 * A * c * cov_gl + c * c * var_l) / (M * M)


def cov_ap_hetero(L1: int, M1: int, L2: int, M2: int, exact: bool = True):
    """Exact Cov(AP_1, AP_2) for lists (L1, M1) and (L2, M2) sharing one positive.

    The tier-2 model of `cov_ap` without the matching-shape restriction: list r ranks
    L_r items with M_r relevant, the single shared positive carries the same similarity
    value in both lists, everything else is independent.  The conditioning argument goes
    through unchanged - given the shared quantile p the lists are independent, so
    Cov = Cov_p(f_1(p), f_2(p)) with each f_r built from its own (L_r, M_r) - except
    that the two cross terms no longer coincide:

        Cov = [ A1*A2*Cov(g1,g2) - A1*c2*Cov(g1,l2) - c1*A2*Cov(l1,g2)
                + c1*c2*Cov(l1,l2) ] / (M1*M2)

    with A_r, c_r as in `cov_ap` and each raw cross-moment a single harmonic sum, so
    O(L1 + L2) work.  Symmetric in the two lists; on the diagonal the two cross terms
    merge and this reduces exactly to `cov_ap(L, M)`.

    Verified: exact match with direct rational integration of the model (all
    L1, L2 <= 5 in the test suite); exact diagonal reduction to `cov_ap` for
    2 <= L <= 12; two independently derived implementations agreed exactly on all
    6084 configs with L1, L2 <= 12; Monte Carlo consistent on heterogeneous configs.

    Returns an exact Fraction (exact=True) or a float (exact=False).  Requires
    1 <= M_r <= L_r.  Returns exactly 0 when either list is deterministic
    (M_r == L_r, which includes L_r == 1).
    """
    if not (1 <= M1 <= L1 and 1 <= M2 <= L2):
        raise ValueError(
            f"require 1 <= M <= L per list, got (L1,M1)=({L1},{M1}), (L2,M2)=({L2},{M2})"
        )
    if M1 == L1 or M2 == L2:
        return Fraction(0) if exact else 0.0

    if exact:
        R = Fraction
        H = [Fraction(0)]
        for k in range(1, L1 + L2):
            H.append(H[-1] + Fraction(1, k))
    else:

        def R(a, b=1):
            return a / b

        H = [0.0]
        for k in range(1, L1 + L2):
            H.append(H[-1] + 1.0 / k)

    def params(L, M):
        # (A, c) exactly as in cov_ap; safe because 1 <= M < L here, so L >= 2
        q = R(M - 1, L - 1)
        q2 = R(0) if (M < 3 or L < 3) else R((M - 1) * (M - 2), (L - 1) * (L - 2))
        b = 1 - 2 * q + q2
        c = q2 - q
        return (b + c) / L, c

    A1, c1 = params(L1, M1)
    A2, c2 = params(L2, M2)

    e_g1, e_g2 = H[L1] - 1, H[L2] - 1
    e_l1, e_l2 = R(L1 - 1, L1), R(L2 - 1, L2)

    cov_gg = sum(H[k + L2] - H[k + 1] for k in range(1, L1)) - e_g1 * e_g2
    cov_gl = sum(R(1, m) * (H[m + L1] - H[m + 1]) for m in range(1, L2)) - e_g1 * e_l2
    cov_lg = sum(R(1, k) * (H[k + L2] - H[k + 1]) for k in range(1, L1)) - e_l1 * e_g2
    cov_ll = (
        sum(
            R(1, k * (k + 1)) * (H[L2 - 1] + H[k + 1] - H[L2 + k]) for k in range(1, L1)
        )
        - e_l1 * e_l2
    )

    return (
        A1 * A2 * cov_gg - A1 * c2 * cov_gl - c1 * A2 * cov_lg + c1 * c2 * cov_ll
    ) / (M1 * M2)


def design_effect(L: int, M: int, n: int) -> float:
    """Var(mAP) inflation from sharing positives: 1 + (n-1) * Cov(AP_i,AP_j) / Var(AP).

    Multiply the independent-profiles variance Var(AP)/n by this to get the variance of
    mAP over n exchangeable profiles that pairwise share one positive.  Inherits the
    tier-2 modelling assumption in `cov_ap`; the ratio is otherwise exact.

    For fixed M and L -> infinity, Cov/Var -> (12 ln 2 / pi^2) / M = 0.8428 / M, so in
    replicate retrieval (M = n - 1 positives for n replicates) the design effect tends to
    1 + 12 ln 2 / pi^2 = 1.8428 for every n.  On short lists it is smaller - 1.40 at
    L = 20, n = 12 - so do not treat 1.84 as universal.

    At M = L both moments are 0 (every AP is deterministically 1); by convention that
    degenerate case returns 1.0, i.e. no inflation.

    Uses the float covariance path, which tracks the exact one to ~1e-12 relative and
    keeps large L cheap (the exact path is O(L) bignum rational adds).
    """
    if n < 1:
        raise ValueError("need n >= 1")
    variance = float(var_ap(L, M))
    if variance == 0.0:
        return 1.0
    return 1.0 + (n - 1) * cov_ap(L, M, exact=False) / variance


# ----------------------------------------------------------------------------------
# mAP null: moments (with the tier-2 correction) and the exact tier-3 law
# ----------------------------------------------------------------------------------


def expected_map(configs: Sequence[Config]) -> Fraction:
    """E[mAP] = (1/n) * sum_i E[AP_i].  Linearity, so no independence needed."""
    configs = list(configs)
    if not configs:
        raise ValueError("need at least one (L, M) config")
    return sum((expected_ap(L, M) for L, M in configs), Fraction(0)) / len(configs)


def map_null_sd(configs: Sequence[Config], shared_positive: bool = True) -> float:
    """sd(mAP) under the null, with the shared-positive correction on by default.

    configs is [(L, M), ...], one per profile averaged into mAP = (1/n) sum_i AP_i.

        Var(mAP) = (1/n^2) * ( sum_i Var(AP_i) + sum_{i != j} Cov(AP_i, AP_j) ).

    With shared_positive=False the covariance term is dropped, which is the independent
    null that `exact_map_pmf` realises exactly - use it only when the profiles really do
    not share relevant items, otherwise it understates the spread by roughly the
    `design_effect` factor.  With shared_positive=True (default) each pair contributes
    the exact tier-2 covariance: `cov_ap` for a pair with matching (L, M), and its
    heterogeneous generalisation `cov_ap_hetero` for mismatched pairs, so heterogeneous
    configs are exactly as defensible as homogeneous ones (given the tier-2 model).
    """
    configs = [(int(L), int(M)) for L, M in configs]
    n = len(configs)
    if n == 0:
        raise ValueError("need at least one (L, M) config")

    total = sum(float(var_ap(L, M)) for L, M in configs)
    if shared_positive and n > 1:
        pair_cov: dict[tuple[Config, Config], float] = {}
        for i, ci in enumerate(configs):
            for cj in configs[i + 1 :]:
                key = (ci, cj) if ci <= cj else (cj, ci)
                if key not in pair_cov:
                    a, b = key
                    pair_cov[key] = (
                        cov_ap(*a, exact=False)
                        if a == b
                        else cov_ap_hetero(*a, *b, exact=False)
                    )
                # clamp: the float path can land a hair below 0 in the degenerate M == L
                total += 2.0 * max(pair_cov[key], 0.0)
    return sqrt(max(total, 0.0)) / n


def exact_map_pmf(configs: Sequence[Config]) -> dict[Fraction, Fraction]:
    """Exact null PMF of mAP = (1/n) * sum_i AP_i for INDEPENDENT AP_i.

    configs: list of (L, M), 1 <= M <= L, one per profile.  Each AP_i is the AP of a
    uniformly random ranking: relevant ranks uniform over the C(L, M) size-M subsets,
    AP = (1/M) sum_j j / R_j.
    Returns {Fraction mAP value: Fraction probability}; probabilities sum to exactly 1.

    Exactness note: each AP is put on the integer grid K / (M * lcm(1..L)) by a
    rank-inclusion DP, all profiles are rescaled to a common grid, and the laws are
    convolved as integer polynomials, so the output is the true finite law with no
    floating point anywhere.  Independence is the assumption - see the module docstring
    and `map_null_sd` for what to do when the profiles share positives.
    """
    configs = [(int(L), int(M)) for L, M in configs]
    if not configs:
        raise ValueError("need at least one (L, M) config")
    for L, M in configs:
        if not 1 <= M <= L:
            raise ValueError(f"require 1 <= M <= L, got L={L}, M={M}")
    n = len(configs)
    per = {c: _ap_coeffs(*c) for c in set(configs)}
    G = lcm(*(den for den, _ in per.values()))  # mAP = (sum_i V_i) / (n * G)
    scaled = {}
    for c, (den, counts) in per.items():
        rescale = G // den
        scaled[c] = {K * rescale: v for K, v in counts.items()}
    mins = {c: min(d) for c, d in scaled.items()}
    g = 0
    for c, d in scaled.items():
        for v in d:
            g = gcd(g, v - mins[c])
    g = g or 1  # exact grid reduction
    polys = {
        c: {(v - mins[c]) // g: cnt for v, cnt in d.items()} for c, d in scaled.items()
    }

    acc = {0: 1}
    for c in configs:  # integer convolution
        out: dict[int, int] = {}
        for ka, ca in acc.items():
            for kb, cb in polys[c].items():
                out[ka + kb] = out.get(ka + kb, 0) + ca * cb
        acc = out

    offset = sum(mins[c] for c in configs)
    den, total = n * G, prod(comb(L, M) for L, M in configs)
    return {
        Fraction(offset + g * t, den): Fraction(c, total)
        for t, c in sorted(acc.items())
    }


def exact_map_tail(configs: Sequence[Config], threshold) -> Fraction:
    """Exact P(mAP >= threshold) under the same independent null as `exact_map_pmf`."""
    thr = Fraction(threshold)
    return sum((p for v, p in exact_map_pmf(configs).items() if v >= thr), Fraction(0))


def _ap_coeffs(L: int, M: int) -> tuple[int, dict[int, int]]:
    """AP = K / (M * lcm(1..L)); returns that denominator and {K: number of rank sets}.

    Rank-inclusion DP over ranks 1..L: state is how many relevant items have been placed
    so far, so this never enumerates the C(L, M) subsets one by one.
    """
    D = lcm(*range(1, L + 1))
    dp: list[dict[int, int]] = [{} for _ in range(M + 1)]
    dp[0][0] = 1
    for r in range(1, L + 1):
        step = D // r
        new: list[dict[int, int]] = [{} for _ in range(M + 1)]
        for j in range(max(0, M - (L - r)), min(M, r) + 1):
            if j <= r - 1 and dp[j]:  # rank r not relevant
                new[j].update(dp[j])
            if j >= 1 and dp[j - 1]:  # rank r is the j-th relevant
                w, tgt = j * step, new[j]
                for K, c in dp[j - 1].items():
                    tgt[K + w] = tgt.get(K + w, 0) + c
        dp = new
    return M * D, dp[M]


if __name__ == "__main__":
    ROW = "{:>5} {:>4} {:>8} {:>8} {:>10} {:>8} {:>8}"
    print(ROW.format("L", "M", "E[AP]", "sd(AP)", "cov", "cov/var", "DE(n=4)"))
    for L, M in [(10, 1), (10, 2), (50, 2), (50, 4), (100, 4), (384, 4), (384, 8)]:
        variance = float(var_ap(L, M))
        covariance = cov_ap(L, M, exact=False)
        print(
            "{:5d} {:4d} {:8.5f} {:8.5f} {:10.3e} {:8.4f} {:8.4f}".format(
                L,
                M,
                float(expected_ap(L, M)),
                sqrt(variance),
                covariance,
                covariance / variance,
                design_effect(L, M, 4),
            )
        )

    configs = [(10, 2)] * 4
    independent = map_null_sd(configs, shared_positive=False)
    pmf = exact_map_pmf(configs)
    tail = float(exact_map_tail(configs, Fraction(1, 2)))
    print(f"\nmAP null for {configs}")
    print(f"  E[mAP]                     = {float(expected_map(configs)):.6f}")
    print(f"  sd, independent  (tier 3)  = {independent:.6f}")
    print(f"  sd, shared positive        = {map_null_sd(configs):.6f}")
    print(f"  exact PMF atoms            = {len(pmf):,}, mass {sum(pmf.values())}")
    print(f"  P(mAP >= 0.5), independent = {tail:.6f}")
