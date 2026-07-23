"""Decisive checks for ap_moments: closed forms against exact enumeration.

Every closed form is compared to a reference built from the model definition alone -
exhaustive enumeration of rank subsets, or exact rational integration over the shared
value's quantile - so a wrong coefficient anywhere fails a test rather than a tolerance.
The one Monte Carlo test exists because it is the only thing that exercises the tier-2
generative story (one shared similarity value, everything else independent) end to end.

Run: uv run --with pytest --with numpy python -m pytest test_ap_moments.py -q
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb, log, pi, sqrt

import numpy as np
import pytest

from ap_moments import (
    cov_ap,
    cov_ap_hetero,
    design_effect,
    exact_map_pmf,
    exact_map_tail,
    expected_ap,
    expected_map,
    harmonic,
    map_null_sd,
    var_ap,
)


def ap_of(ranks) -> Fraction:
    """AP = (1/M) sum_j j / R_j for sorted relevant ranks."""
    total = sum((Fraction(j, r) for j, r in enumerate(ranks, 1)), Fraction(0))
    return total / len(ranks)


def brute_ap(L: int, M: int) -> list[Fraction]:
    """The AP of every one of the C(L, M) equally likely rank subsets."""
    return [ap_of(ranks) for ranks in combinations(range(1, L + 1), M)]


# ----------------------------------------------------------------------------------
# tier 1: marginal moments against exhaustive enumeration
# ----------------------------------------------------------------------------------


def test_expected_ap_matches_enumeration():
    for L in range(1, 13):
        for M in range(1, L + 1):
            values = brute_ap(L, M)
            assert sum(values, Fraction(0)) / len(values) == expected_ap(L, M)


def test_var_ap_matches_enumeration():
    for L in range(1, 13):
        for M in range(1, L + 1):
            values = brute_ap(L, M)
            mean = sum(values, Fraction(0)) / len(values)
            second = sum((v * v for v in values), Fraction(0)) / len(values)
            assert second - mean * mean == var_ap(L, M), (L, M)


def test_var_ap_edge_cases():
    for L in range(1, 30):
        assert var_ap(L, L) == 0  # AP is deterministically 1
        assert var_ap(L, 1) == harmonic(L, 2) / L - (harmonic(L) / L) ** 2
    with pytest.raises(ValueError):
        var_ap(5, 0)
    with pytest.raises(ValueError):
        var_ap(5, 6)


# ----------------------------------------------------------------------------------
# tier 2: covariance against exact integration over the shared value's quantile
# ----------------------------------------------------------------------------------


def conditional_mean_ap(L: int, M: int, u: int) -> Fraction:
    """E[AP | shared positive at rank u], by enumerating the other positives."""
    others = [r for r in range(1, L + 1) if r != u]
    subsets = list(combinations(others, M - 1))
    return sum((ap_of(sorted(s + (u,))) for s in subsets), Fraction(0)) / len(subsets)


def cov_by_integration(L: int, M: int) -> tuple[Fraction, Fraction]:
    """Cov and E[AP] from the model directly: rank = 1 + Binomial(L-1, 1-p), p ~ U(0,1).

    Given p the two lists are independent, so Cov = Var_p(E[AP | p]).  E[AP | p] is a
    degree-(L-1) polynomial in p with exact rational coefficients, so both moments are
    exact integrals of polynomials.  No closed form from ap_moments is used here.
    """
    g = [Fraction(0)] * L
    for u in range(1, L + 1):
        weight = conditional_mean_ap(L, M, u) * comb(L - 1, u - 1)
        for t in range(u):  # (1-p)^(u-1) = sum_t C(u-1, t) (-1)^t p^t
            g[L - u + t] += weight * comb(u - 1, t) * (-1) ** t

    square = [Fraction(0)] * (2 * L - 1)
    for i, x in enumerate(g):
        for j, y in enumerate(g):
            square[i + j] += x * y

    def integrate(poly):
        return sum((c / (k + 1) for k, c in enumerate(poly)), Fraction(0))

    return integrate(square) - integrate(g) ** 2, integrate(g)


def test_cov_ap_matches_exact_quantile_integration():
    for L in range(2, 8):
        for M in range(1, L + 1):
            covariance, mean = cov_by_integration(L, M)
            assert covariance == cov_ap(L, M), (L, M)
            assert mean == expected_ap(L, M), (L, M)  # the mixing is the right one


def _conditional_mean_poly(L: int, M: int) -> list[Fraction]:
    """E[AP | p] as a degree-(L-1) polynomial in the shared quantile p, exact."""
    g = [Fraction(0)] * L
    for u in range(1, L + 1):
        weight = conditional_mean_ap(L, M, u) * comb(L - 1, u - 1)
        for t in range(u):  # (1-p)^(u-1) = sum_t C(u-1, t) (-1)^t p^t
            g[L - u + t] += weight * comb(u - 1, t) * (-1) ** t
    return g


def cov_hetero_by_integration(L1: int, M1: int, L2: int, M2: int) -> Fraction:
    """Heterogeneous Cov from the model directly: Cov_p(E[AP_1|p], E[AP_2|p]), exact."""
    g1, g2 = _conditional_mean_poly(L1, M1), _conditional_mean_poly(L2, M2)
    product = [Fraction(0)] * (len(g1) + len(g2) - 1)
    for i, x in enumerate(g1):
        for j, y in enumerate(g2):
            product[i + j] += x * y

    def integrate(poly):
        return sum((c / (k + 1) for k, c in enumerate(poly)), Fraction(0))

    return integrate(product) - integrate(g1) * integrate(g2)


def test_cov_ap_hetero_matches_exact_quantile_integration():
    for L1 in range(2, 6):
        for L2 in range(2, 6):
            for M1 in range(1, L1 + 1):
                for M2 in range(1, L2 + 1):
                    exact = cov_hetero_by_integration(L1, M1, L2, M2)
                    assert cov_ap_hetero(L1, M1, L2, M2) == exact, (L1, M1, L2, M2)


def test_cov_ap_hetero_reduction_symmetry_and_float_path():
    for L in range(2, 13):
        for M in range(1, L + 1):
            assert cov_ap_hetero(L, M, L, M) == cov_ap(L, M), (L, M)
    for L1, M1, L2, M2 in [(5, 2, 9, 3), (4, 1, 11, 5), (20, 4, 50, 2)]:
        exact = cov_ap_hetero(L1, M1, L2, M2)
        assert exact == cov_ap_hetero(L2, M2, L1, M1)
        assert exact > 0
        assert abs(cov_ap_hetero(L1, M1, L2, M2, exact=False) - float(exact)) < 1e-14
    assert cov_ap_hetero(7, 7, 9, 3) == 0  # deterministic list has zero covariance
    assert cov_ap_hetero(9, 3, 1, 1) == 0


def test_map_null_sd_heterogeneous_uses_exact_covariance():
    configs = [(10, 2), (14, 3), (10, 2)]
    n = len(configs)
    total = sum(float(var_ap(L, M)) for L, M in configs)
    total += 2.0 * cov_ap(10, 2, exact=False)  # the matching pair
    total += 2.0 * 2.0 * cov_ap_hetero(10, 2, 14, 3, exact=False)  # two mixed pairs
    assert abs(map_null_sd(configs) - sqrt(total) / n) < 1e-15


def test_cov_ap_edge_cases_and_float_path():
    for L in range(2, 30):
        assert cov_ap(L, L) == 0  # both lists are deterministic
        one = 1 + 2 * L * (harmonic(2 * L - 1) - harmonic(L)) - harmonic(L) ** 2
        assert cov_ap(L, 1) == one / L**2
        for M in range(1, L + 1):
            exact = cov_ap(L, M)
            assert exact >= 0  # a shared positive can only help both lists
            assert cov_ap(L, M, exact=False) == pytest.approx(float(exact), rel=1e-9)
    # design_effect and map_null_sd take the float path; pin it at real list lengths
    for L, M in [(100, 3), (1000, 5), (1000, 500)]:
        exact = float(cov_ap(L, M))
        assert cov_ap(L, M, exact=False) == pytest.approx(exact, rel=1e-10)


@pytest.mark.parametrize(("L", "M"), [(6, 2), (8, 3)])
def test_cov_ap_matches_simulation_of_the_shared_positive_model(L, M):
    """Simulate the model literally: one similarity value shared, all others fresh."""
    reps = 200_000
    rng = np.random.default_rng(0)
    shared = rng.random(reps)
    lists = []
    for _ in range(2):
        values = np.concatenate([shared[:, None], rng.random((reps, L - 1))], axis=1)
        ranks = 1 + (values[:, None, :] > values[:, :, None]).sum(axis=2)
        relevant = np.sort(ranks[:, :M], axis=1)  # column 0 is the shared item
        lists.append((np.arange(1, M + 1) / relevant).sum(axis=1) / M)
    a, b = lists

    # the simulator itself must reproduce the tier-1 moments, or the covariance is moot
    tolerance = 4 * a.std() / sqrt(reps)
    assert a.mean() == pytest.approx(float(expected_ap(L, M)), abs=tolerance)
    assert a.var() == pytest.approx(float(var_ap(L, M)), rel=0.02)

    products = (a - a.mean()) * (b - b.mean())
    standard_error = products.std() / sqrt(reps)
    assert products.mean() == pytest.approx(float(cov_ap(L, M)), abs=5 * standard_error)


def test_design_effect_lands_in_the_measured_band():
    """Replicate retrieval: n profiles per group, each with its n-1 replicates relevant.

    Every pair in the group shares exactly one positive - the pair itself - which is
    precisely the tier-2 model.  With M = n - 1 held fixed the design effect tends to
    1 + 12*ln(2)/pi^2 = 1.8428 as L grows, for every n, which is why this whole family
    lands in the 1.7-1.9 band that calibration_check.py measures.  It is NOT 1.84
    everywhere: on short lists with many replicates it decays well below that band, so
    the band is asserted only where it actually holds.
    """
    for L in (50, 100, 384, 1000, 4000):
        for n in (2, 3, 4, 5, 6, 8):
            assert 1.7 <= design_effect(L, n - 1, n) <= 1.9, (L, n)
    limit = 1.0 + 12.0 * log(2.0) / pi**2
    for n in (2, 5, 9):
        assert design_effect(20_000, n - 1, n) == pytest.approx(limit, abs=0.002), n
    assert design_effect(20, 11, 12) == pytest.approx(1.404, abs=0.005)  # short list
    assert design_effect(10, 10, 4) == 1.0  # degenerate: every AP is 1
    assert design_effect(10, 3, 1) == 1.0  # a single profile cannot be inflated


def test_map_null_sd_is_the_design_effect_applied_to_the_independent_sd():
    for L, M, n in [(20, 3, 4), (50, 5, 6), (100, 2, 3)]:
        configs = [(L, M)] * n
        independent = map_null_sd(configs, shared_positive=False)
        assert independent == pytest.approx(sqrt(float(var_ap(L, M)) / n))
        corrected = map_null_sd(configs)
        assert (corrected / independent) ** 2 == pytest.approx(design_effect(L, M, n))
        assert corrected > independent


# ----------------------------------------------------------------------------------
# tier 3: exact convolution
# ----------------------------------------------------------------------------------


def test_exact_map_pmf_single_profile_matches_enumeration():
    for L, M in [(1, 1), (5, 1), (6, 2), (7, 3), (7, 7)]:
        counts = Counter(brute_ap(L, M))  # collisions are the whole point
        reference = {v: Fraction(c, comb(L, M)) for v, c in counts.items()}
        assert exact_map_pmf([(L, M)]) == reference


def test_exact_map_pmf_is_a_law_with_the_closed_form_mean_and_variance():
    for configs in [[(4, 2), (5, 2), (6, 3)], [(8, 3)] * 3, [(6, 1), (6, 5)]]:
        pmf = exact_map_pmf(configs)
        n = len(configs)
        assert sum(pmf.values(), Fraction(0)) == 1
        mean = sum((v * p for v, p in pmf.items()), Fraction(0))
        assert mean == expected_map(configs)
        variance = sum((v * v * p for v, p in pmf.items()), Fraction(0)) - mean * mean
        # independent profiles: the convolution variance IS sum of var_ap over n^2
        assert variance == sum((var_ap(L, M) for L, M in configs), Fraction(0)) / n**2
        independent = map_null_sd(configs, shared_positive=False)
        assert independent == pytest.approx(sqrt(float(variance)))


def test_exact_map_tail_agrees_with_the_pmf():
    configs = [(6, 2), (7, 2)]
    pmf = exact_map_pmf(configs)
    for threshold in (Fraction(k, 10) for k in (0, 3, 5, 9, 20)):
        mass = sum((p for v, p in pmf.items() if v >= threshold), Fraction(0))
        assert exact_map_tail(configs, threshold) == mass
    assert exact_map_tail(configs, 0) == 1
