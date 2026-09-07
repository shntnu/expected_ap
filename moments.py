"""Exact mean and variance of full-list AP under uniform random ranking."""

from fractions import Fraction
from operator import index


def _validate_counts(L: int, M: int) -> tuple[int, int]:
    L, M = index(L), index(M)
    if L < 1 or not 0 <= M <= L:
        raise ValueError(f"require L >= 1 and 0 <= M <= L, got L={L}, M={M}")
    return L, M


def harmonic(L: int, power: int = 1) -> Fraction:
    """Return the exact generalized harmonic number."""
    return sum((Fraction(1, k**power) for k in range(1, L + 1)), Fraction(0))


def expected_ap(L: int, M: int) -> Fraction:
    """Return E[AP] for integer L >= 1 and 0 <= M <= L; Proposition 1."""
    L, M = _validate_counts(L, M)
    if M == 0:
        return Fraction(0)
    if L == 1:
        return Fraction(1)
    H = harmonic(L)
    return Fraction(1, L) * (Fraction(M - 1, L - 1) * (L - H) + H)


def var_ap(L: int, M: int) -> Fraction:
    """Return Var(AP) for integer L >= 1 and 0 <= M <= L; Proposition 2."""
    L, M = _validate_counts(L, M)
    if M == 0:
        return Fraction(0)
    H = harmonic(L)
    H2 = harmonic(L, 2)

    def m(r: int) -> Fraction:
        if r > M:
            return Fraction(0)
        num = den = 1
        for t in range(r):
            num *= M - t
            den *= L - t
        return Fraction(num, den)

    m1, m2, m3, m4 = (m(1), m(2), m(3), m(4))
    e_w = m1 * H + m2 * (L - H)
    e_w2 = (
        m1 * H2
        + m2 * (2 * H**2 + 3 * H - 5 * H2)
        + m3 * (2 * L * H + 5 * L - 5 * H**2 - 9 * H + 7 * H2)
        + m4 * (L**2 - 2 * L * H - 5 * L + 3 * H**2 + 6 * H - 3 * H2)
    )
    return (e_w2 - e_w * e_w) / Fraction(M * M)
